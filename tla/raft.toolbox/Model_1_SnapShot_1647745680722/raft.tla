--------------------------------- MODULE raft ---------------------------------
\* This is the formal specification for the Raft consensus algorithm.
\*
\* Copyright 2014 Diego Ongaro.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* The set of requests that can go into the log
CONSTANTS Value

\* Server states.
CONSTANTS Follower, Candidate, Leader

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse

----
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another. TLAPS doesn't support the Bags module, so this is a function
\* mapping Message to Nat.
\* Set of messages. Simulates network channel. Message have uniq seq numbers.
\* Type: { [ type: {RequestVoteRequest, ...}, from: Server, to: Server,
\*           seq: Nat, body: [ ... ] ] }
\* Body RequestVoteRequest: 
\*      [ term: Nat, candidate: Server, lastLogIdx: Nat, LastLogTerm: Nat ]
\* Body RequestVoteResponse:
\*      [ term: Nat, voteGranted: {TRUE, FALSE} ]
\* Body AppendEntriesRequest:
\*      [ term: Nat, prevLogIdx: Nat, prevLogTerm: Nat, leaderCommit: Nat,
\*        entries: <<[...]>> ]
\* Body AppendEntriesResponse:
\*      [ term: Nat, success: {TRUE, FALSE}, curIdx: Nat ]
\*      (curIdx helps Leader decrease the corresponding node's nextIdx quickly.)
\* Body SnapshotRequest:
\*      [ term: Nat, lastIdx: Nat, lastTerm: Nat ]
VARIABLE messages

\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Keeps track of successful elections, including the initial logs of the
\* leader and voters' logs. Set of functions containing various things about
\* successful elections (see BecomeLeader).
VARIABLE elections

\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Keeps track of every log ever in the system (set of logs).
VARIABLE allLogs

----
\* The following variables are all per server (functions with domain Server).

\* The server's term number.
VARIABLE currentTerm
\* The server's state (Follower, Candidate, or Leader).
VARIABLE state
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor
serverVars == <<currentTerm, state, votedFor>>

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
\* Log entries. Head index is 1.
\* Type: [ s: << [ term |-> xx, value |-> xx ], .. >> ]
VARIABLE log
\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex
logVars == <<log, commitIndex>>

\* The following variables are used only on candidates:
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE votesResponded
\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE votesGranted
\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Function from each server that voted for this candidate in its currentTerm
\* to that voter's log.
VARIABLE voterLog
candidateVars == <<votesResponded, votesGranted, voterLog>>

\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE nextIndex
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE matchIndex
leaderVars == <<nextIndex, matchIndex, elections>>

VARIABLE pc1

\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, allLogs, serverVars, candidateVars, leaderVars, logVars, pc1>>


\* State constraint recorder.
\* Type: [ nSent: Nat, nRecv: Nat, nWire: Nat, nDrop: Nat, nDup: Nat,
\*         nUnorder: Nat, nTimeout: Nat, nRestart: Nat, nOp: Nat, nLog, Nat,
\*         maxTerm: Nat, nCont: Nat, nCure: Nat, lock: [...], pc: ACTION_NAME,
\*         partNodes: SUBSET Server, nSnapshot: Nat, noInv: {1,2,..} ]
\* nSent/nRecv/nWire: network message count of sent/recv/on-the-wire.
\* nDrop/nDup/nUnorder: network failures count.
\* nTimeout/nRestart: node failures count.
\* nOp: client requests count.
\* nLog/maxTerm: current max log length and max term.
\* nCont: continuous normal actions count.
\* pc: action name and args
\* inv: invariants to evaluate
\* nCure: network partion recovered times
\* partNodes: nodes in the set cannot communicate with nodes not in the set
\* noInv: not to exit TLC even if those inv evaluated as FALSE
\* lock:
\* Loop a broadcast action (e.g. send AppendEntriesRequest).
\*  [ type: { RequestVoteRequest, AppendEntriesRequest, SnapshotRequest},
\*    args: [ from: Server, to: Server ] ]
\* VARIABLES scr


\* first to test, we need a variable to note how system changes

----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] + 1]
    ELSE
        msgs @@ (m :> 1)

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] - 1]
    ELSE
        msgs

\* Add a message to the bag of messages.
Send(m) == messages' = WithMessage(m, messages)

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) == messages' = WithoutMessage(m, messages)

\* Combination of Send and Discard
Reply(response, request) ==
    messages' = WithoutMessage(request, WithMessage(response, messages))

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* Check server state.
IsLeader   (s)  == state[s] = Leader
IsFollower (s)  == state[s] = Follower
IsCandidate(s)  == state[s] = Candidate

\* Check if entry ety is null.
IsNullEntry(ety) == ety = Nil

UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
       \* messages is unchanged so m can be processed further.
    \* /\ pc1 = <<"UpdateTerm", i, j, m.mterm>>
    \* /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars>>

----
\* Define initial values for all variables

\* InitScr ==
\*     scr = [ nSent |-> 0,   nRecv    |-> 0,   nWire     |-> 0, nDrop    |-> 0,
\*             nDup  |-> 0,   nUnorder |-> 0,   nTimeout  |-> 0, nRestart |-> 0,
\*             nOp   |-> 0,   nLog     |-> 0,   maxTerm   |-> 0, inv      |-> <<>>,
\*             nCure |-> 0,   lock     |-> Nil,  partNodes|-> {},
\*             noInv |-> GetParameterSet("IgnoreInvNumbers"),    nAe      |-> 0 , 
\*             nCont |-> GetParameter("MinContNormalActions"),   pc |-> <<"Init">>]

InitPc == pc1 = <<"Init">>

InitHistoryVars == /\ elections = {}
                   /\ allLogs   = {}
                   /\ voterLog  = [i \in Server |-> [j \in {} |-> <<>>]]
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
InitLogVars == /\ log          = [i \in Server |-> << >>]
               /\ commitIndex  = [i \in Server |-> 0]
InitNetwokVars == messages = [m \in {} |-> 0]
Init == /\ InitNetwokVars
        /\ InitHistoryVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars
        /\ InitPc
----
\* Define state transitions

\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
Restart(i) ==
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    /\ pc1 = <<"Restart", i>>
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, elections>>
    

\* Server i times out and starts a new election.
Timeout(i) == /\ state[i] \in {Follower, Candidate}
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              \* Most implementations would probably just set the local vote
              \* atomically, but messaging localhost for it is weaker.
              /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
              /\ pc1 = <<"Timeout", i>>
              /\ UNCHANGED <<messages, leaderVars, logVars>>
              

\* Candidate i sends j a RequestVote request.
RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ j \notin votesResponded[i]
    /\ Send([mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i],
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j])
    /\ pc1 = <<"RequestVote", i, j>>
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex].term
                          ELSE
                              0
           \* Send up to 1 entry, constrained by the end of the log.
           lastEntry == Min({Len(log[i]), nextIndex[i][j]})
           entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
       IN Send([mtype          |-> AppendEntriesRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries,
                \* mlog is used as a history variable for the proof.
                \* It would not exist in a real implementation.
                mlog           |-> log[i],
                mcommitIndex   |-> Min({commitIndex[i], lastEntry}),
                msource        |-> i,
                mdest          |-> j])
    /\ pc1 = <<"AppendEntriese", i, j>>
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* Candidate i transitions to leader.
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    /\ elections'  = elections \cup
                         {[eterm     |-> currentTerm[i],
                           eleader   |-> i,
                           elog      |-> log[i],
                           evotes    |-> votesGranted[i],
                           evoterLog |-> voterLog[i]]}
    /\ pc1 = <<"BecomLeader", i>>
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars>>

\* Leader i receives a client request to add v to the log.
ClientRequest(i, v) ==
    /\ state[i] = Leader
    /\ LET entry == [term  |-> currentTerm[i],
                     value |-> v]
           newLog == Append(log[i], entry)
       IN  log' = [log EXCEPT ![i] = newLog]
    /\ pc1 = <<"ClientRequest", i, v>>
    /\ UNCHANGED <<messages, serverVars, candidateVars,
                   leaderVars, commitIndex>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Server :
                                         matchIndex[i][k] >= index}
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(log[i]) :
                                Agree(index) \in Quorum}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
       IN commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
    /\ pc1 = <<"AdvanceCommitIndex", i, commitIndex>>
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log>>

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
HandleRequestVoteRequest(i, j, m) ==
    LET body == m.body
        logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ ~IsLeader(i)
                 /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
        rb          == [ mterm |-> currentTerm'[i], mvoteGranted |-> grant ]
        msg         == [ type |-> RequestVoteResponse,
                         from |-> i,
                         to   |-> j,
                         body |-> rb ]
    IN /\ IF IsLeader(i)
            THEN /\ Reply(msg, m)
                 /\ pc1 = <<"HandleRequestVoteRequest: leader not granted",
                              i, j, m.seq, FALSE>>
             ELSE /\ m.mterm <= currentTerm[i]
                  /\ UpdateTerm(i, j, m)
                  /\ Reply(msg, m)
                  /\ IF  grant  
                     THEN  /\ votedFor' = [votedFor EXCEPT ![i] = j]
                           /\ pc1 = <<"HandleRequestVoteRequest: granted",
                                  i, j, m.seq, TRUE>>
                     ELSE   /\ pc1 = <<"HandleRequestVoteRequest: not granted",
                                  i, j, m.seq, FALSE>>
       /\ UNCHANGED <<candidateVars, leaderVars, logVars>>

\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ Discard(m)
    /\ LET b == m.body
           notCandidate == ~IsCandidate(i)
           staleMsg     == currentTerm[i] > b.term
           notGranted   == currentTerm[i] = b.term /\ ~b.voteGranted
       IN IF notCandidate \/ staleMsg \/ notGranted
          THEN  /\ pc1 = <<CASE notCandidate -> "HandleRequestVoteResponse: not candidate"
                        [] staleMsg     -> "HandleRequestVoteResponse: stale msg"
                        [] notGranted   -> "HandleRequestVoteResponse: not granted"
                        [] OTHER        -> Assert(FALSE,
                           "HandleRequestVoteResponse unhandled CASE"),
                      i, j, m.seq, FALSE>>
                /\ UNCHANGED <<votesGranted, voterLog>>
          ELSE IF currentTerm[i] < b.term
               THEN /\ UpdateTerm(i, j, m) \* return to follower state
                    /\ m.mterm = currentTerm[i]
                    /\ state[i] = Candidate
                    /\ state' = [state EXCEPT ![i] = Follower]
                    /\ pc1 = <<"HandleRequestVoteResponse: demote",
                                  i, j, m.seq, FALSE>>
                ELSE /\ votesGranted' = [votesGranted EXCEPT ![i] = votesGranted[i] \cup {j}]
                     /\ IF /\ votesGranted'[i] \in Quorum
                        THEN /\ BecomeLeader(i)
                             /\ pc1 = <<"HandleRequestVoteResponse: promote",
                                        i, j, m.seq, TRUE>>
                        ELSE pc1 = <<"HandleRequestVoteResponse: get vote",
                                          i, j, m.seq, TRUE>>   
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars>>
    \* /\ m.mterm = currentTerm[i]
    \* /\ votesResponded' = [votesResponded EXCEPT ![i] =
    \*                           votesResponded[i] \cup {j}]
    \* /\ \/ /\ m.mvoteGranted
    \*       /\ votesGranted' = [votesGranted EXCEPT ![i] =
    \*                               votesGranted[i] \cup {j}]
    \*       /\ voterLog' = [voterLog EXCEPT ![i] =
    \*                           voterLog[i] @@ (j :> m.mlog)]
    \*    \/ /\ ~m.mvoteGranted
    \*       /\ UNCHANGED <<votesGranted, voterLog>>

    \* /\ pc1 = <<"HandleRequestVoteResponse", i, j, m>>
    \* /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars>>

\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ /\ \* reject request
                \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ \lnot logOk
             /\ Reply([mtype           |-> AppendEntriesResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> FALSE,
                       mmatchIndex     |-> 0,
                       msource         |-> i,
                       mdest           |-> j],
                       m)
             /\ pc1 = <<"HandleAppendEntriesRequest : reply false">>
             /\ UNCHANGED <<serverVars, logVars>>
          \/ \* return to follower state
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages>>
          \/ \* accept request
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk
             /\ LET index == m.mprevLogIndex + 1
                IN \/ \* already done with request
                       /\ \/ m.mentries = << >>
                          \/ /\ m.mentries /= << >>
                             /\ Len(log[i]) >= index
                             /\ log[i][index].term = m.mentries[1].term
                          \* This could make our commitIndex decrease (for
                          \* example if we process an old, duplicated request),
                          \* but that doesn't really affect anything.
                       /\ commitIndex' = [commitIndex EXCEPT ![i] =
                                              m.mcommitIndex]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 mmatchIndex     |-> m.mprevLogIndex +
                                                     Len(m.mentries),
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars, log>>
                   \/ \* conflict: remove 1 entry
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) >= index
                       /\ log[i][index].term /= m.mentries[1].term
                       /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |->
                                          log[i][index2]]
                          IN log' = [log EXCEPT ![i] = new]
                       /\ UNCHANGED <<serverVars, commitIndex, messages>>
                   \/ \* no conflict: append entry
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) = m.mprevLogIndex
                       /\ log' = [log EXCEPT ![i] =
                                      Append(log[i], m.mentries[1])]
                       /\ UNCHANGED <<serverVars, commitIndex, messages>>
              /\ UNCHANGED <<pc1>>
       /\ UNCHANGED <<candidateVars, leaderVars>>

\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
          /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
       \/ /\ \lnot m.msuccess \* not successful
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                               Max({nextIndex[i][j] - 1, 1})]
          /\ UNCHANGED <<matchIndex>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars, elections, pc1>>

\* Any RPC with a newer term causes the recipient to advance its term first.


\* Responses with stale terms are ignored.
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, pc1>>

\* Receive a message.
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
       \/ /\ m.mtype = RequestVoteRequest
          /\ HandleRequestVoteRequest(i, j, m)
       \/ /\ m.mtype = RequestVoteResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleRequestVoteResponse(i, j, m)
       \/ /\ m.mtype = AppendEntriesRequest
          /\ HandleAppendEntriesRequest(i, j, m)
       \/ /\ m.mtype = AppendEntriesResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleAppendEntriesResponse(i, j, m)

\* End of message handlers.
----
\* Network state transitions

\* The network duplicates a message
DuplicateMessage(m) ==
    /\ Send(m)
    /\ pc1 = <<"Duplicate", m.seq>>
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ pc1 = <<"Drop", m.seq>>
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

----
\* Defines how the variables may transition.
Next == /\ \/ \E i \in Server : Restart(i)
           \/ \E i \in Server : Timeout(i)
           \/ \E i,j \in Server : RequestVote(i, j)
           \/ \E i \in Server, v \in Value : ClientRequest(i, v)
           \/ \E i \in Server : AdvanceCommitIndex(i)
           \/ \E i,j \in Server : AppendEntries(i, j)
           \/ \E m \in DOMAIN messages : Receive(m)
           \/ \E m \in DOMAIN messages : DuplicateMessage(m)
           \/ \E m \in DOMAIN messages : DropMessage(m)
           \* History variable that tracks every log ever:
        /\ allLogs' = allLogs \cup {log[i] : i \in Server}

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars


\* Inv 1: at most one leader per term
AtMostOneLeaderPerTerm ==
    LET TwoLeader == \E i, j \in Server:
                        /\ i /= j
                        /\ currentTerm'[i] = currentTerm'[j]
                        /\ state'[i] = Leader
                        /\ state'[j] = Leader
    IN ~TwoLeader

===============================================================================

\* Changelog:
\*
\* 2014-12-02:
\* - Fix AppendEntries to only send one entry at a time, as originally
\*   intended. Since SubSeq is inclusive, the upper bound of the range should
\*   have been nextIndex, not nextIndex + 1. Thanks to Igor Kovalenko for
\*   reporting the issue.
\* - Change matchIndex' to matchIndex (without the apostrophe) in
\*   AdvanceCommitIndex. This apostrophe was not intentional and perhaps
\*   confusing, though it makes no practical difference (matchIndex' equals
\*   matchIndex). Thanks to Hugues Evrard for reporting the issue.
\*
\* 2014-07-06:
\* - Version from PhD dissertation
