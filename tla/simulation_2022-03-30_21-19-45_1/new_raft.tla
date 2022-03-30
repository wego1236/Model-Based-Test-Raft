--------------------------------- MODULE new_raft ---------------------------------
\* This is the formal specification for the Raft consensus algorithm.

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
VARIABLE log
\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex
logVars == <<log, commitIndex>>

\* The following variables are used only on candidates:
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE votesGranted
\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Function from each server that voted for this candidate in its currentTerm
\* to that voter's log.
candidateVars == <<votesGranted>>

\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE nextIndex
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE matchIndex
leaderVars == <<nextIndex, matchIndex, elections>>

\* End of per server variables.
----

\* watch over the transition, now i have only figured out pc'
VARIABLE pc


\* State constraint recorder.
\* Type: [  lock: [...]]
VARIABLE scr

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, serverVars, candidateVars, leaderVars, logVars, pc, scr>>

----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* Check if servers set (ss) is quorum.
IsQuorum(ss) == Cardinality(ss) * 2 > Cardinality(Server)

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
WithMessage(m, msgs) == LET msgSeq == scr.nSent + 1
                        m_ == IF "seq" \in DOMAIN m
                              THEN {[ m EXCEPT !["seq"] = msgSeq ]}
                              ELSE {m @@ ( "seq" :> msgSeq )}
                        IN msgs \union m_

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
WithoutMessage(m, msgs) ==
    IF m \in msgs THEN msgs \ {m} ELSE msgs

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

\* scr change
ScrSetLock(l)           == ("lock"  :> l)
ScrUnsetLock            == ("lock"  :> Nil)
ScrIsLocked             == scr.lock /= Nil
ScrNotLocked            == scr.lock  = Nil
ScrGetLockType          == IF ScrIsLocked THEN scr.lock.type ELSE Nil
ScrDeleteLockArg(a)     == IF ScrNotLocked
                           THEN ScrUnsetLock
                           ELSE LET s == scr.lock.args \ {a}
                                IN IF Cardinality(s) = 0
                                   THEN ScrUnsetLock
                                   ELSE ("lock" :> [scr.lock EXCEPT !.args = s]) 


ScrGetHelper(member)    == (member :> scr[member])
ScrIncHelper(member)    == (member :> scr[member] + 1)
\* ScrIncSent              == LET num1 == Cardinality(messages')
\*                                num2 == Cardinality(messages)
\*                            IN IF \/ num1 > num2
\*                                  \/ num1 = num2 /\ messages' /= messages
\*                               THEN ScrIncHelper("nSent")
\*                               ELSE ScrGetHelper("nSent")
ScrIncSent    == ScrIncHelper("nSent")


\* Get lock args: all servers except me, and in set s and parted nodes.
LockArgs(i, s, type) ==
    LET e == {i} \union s
    IN IF e /= Server
       THEN ScrSetLock([ type |-> type, args |-> [ from: {i}, to: Server \ e ]])
       ELSE ScrUnsetLock


ScrSet(r) ==
    scr' = r @@ scr



----
\* Invariants

\* Inv 1: at most one leader per term
AtMostOneLeaderPerTerm ==
    LET TwoLeader == \E i, j \in Server:
                        /\ i /= j
                        /\ currentTerm[i] = currentTerm[j]
                        /\ state[i] = Leader
                        /\ state[j] = Leader
    IN /\ ~TwoLeader
        

\* Inv 2: committed log should be replicated to majority nodes
CommittedLogReplicatedMajority ==
     \A i \in Server:
        IF state[i] /= Leader \/ commitIndex[i] = 0
        THEN TRUE
        ELSE LET entries == SubSeq(log[i], 1, commitIndex[i])
                 len     == Len(entries)
                 nServer == Cardinality(Server)
                 F[j \in 0..nServer] ==
                    IF j = 0
                    THEN <<{}, {}>>
                    ELSE LET k == CHOOSE k \in Server: k \notin F[j-1][1]
                             logLenOk == Len(log[k]) >= commitIndex[i]
                             kEntries == SubSeq(log[k], 1, commitIndex[i])
                             minLen == Min({len, Len(kEntries)})
                         IN IF /\ logLenOk
                               /\ \/ minLen = 0
                                  \/ SubSeq(entries, Len(entries) + 1 - minLen,
                                            Len(entries)) = 
                                     SubSeq(kEntries, Len(kEntries)+1 - minLen,
                                            Len(kEntries))
                             THEN /\ <<F[j-1][1] \union {k}, F[j-1][2] \union {k}>>
                                \*   /\ Print(F[j-1], TRUE)
                             ELSE /\ <<F[j-1][1] \union {k}, F[j-1][2]>>
                                \*   /\ Print(F[j-1], TRUE)
             IN IsQuorum(F[nServer][2])

NextIdxGtMatchIdx ==
    \A i \in Server:
        IF state[i] = Leader
        THEN \A j \in Server: nextIndex[i][j] > matchIndex[i][j]
        ELSE TRUE

\* Inv 10: next index is greater than 0
NextIdxGtZero ==
    \A i \in Server:
        IF state[i] = Leader
        THEN \A j \in Server: nextIndex[i][j] > 0
        ELSE TRUE


Inv == /\ AtMostOneLeaderPerTerm
       /\ CommittedLogReplicatedMajority



----
\* Define initial values for all variables

InitHistoryVars == /\ elections = {}
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == /\ votesGranted   = [i \in Server |-> {}]
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
InitLogVars == /\ log          = [i \in Server |-> << >>]
               /\ commitIndex  = [i \in Server |-> 0]
Initpc == pc = <<"Init">>
InitLock ==  scr = [lock |-> Nil, nSent |-> 0]
Init == /\ messages = {}
        /\ InitHistoryVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ Initpc
        /\ InitLogVars
        /\ InitLock

----
\* Define state transitions

\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
Restart(i) ==
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    /\ pc' = <<"Restart", i>>
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, elections, scr>>


BecomeFollower(i, term) == 
    /\ state'       = [ state       EXCEPT ![i] = IF term > currentTerm[i]
                                                  THEN Follower ELSE @ ]
    /\ currentTerm' = [ currentTerm EXCEPT ![i] = IF term > currentTerm[i]
                                                  THEN term     ELSE @ ]
    /\ votedFor' = [ votedFor  EXCEPT ![i] = IF term > currentTerm[i]
                                                  THEN Nil      ELSE @ ]


BecomeLeader(i) ==
    /\ state'    = [ state    EXCEPT ![i] = Leader ]
    /\ nextIndex'  = [ nextIndex  EXCEPT ![i] =
                       [ j \in Server |-> IF i = j THEN 1 ELSE Len(log[i]) + 1 ]]
    /\ matchIndex' = [ matchIndex EXCEPT ![i] = [ j \in Server |-> 0 ]]


\* Server i times out and start a new election.


\* Leader i sends j an AppendEntries/Snapshot request
\* The append entries contain logs from next index to log info back or end.
AppendEntriesHelper(i, j) ==
    LET    prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex].term
                          ELSE
                              0
           \* Send up to 1 entry, constrained by the end of the log.
           lastEntry == Min({Len(log[i]), nextIndex[i][j]})
           entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
           body == [    term          |-> currentTerm[i],
                        prevLogIndex  |-> prevLogIndex,
                        prevLogTerm   |-> prevLogTerm,
                        entries       |-> entries,
                        \* mlog is used as a history variable for the proof.
                        \* It would not exist in a real implementation.
                        log           |-> log[i],
                        commitIndex   |-> Min({commitIndex[i], lastEntry})]
           msg     == [ type          |-> AppendEntriesRequest,
                        from        |-> i,
                        to          |-> j,
                        body           |-> body ]
      IN msg


AppendEntries(i, j) == i /= j /\ Send(AppendEntriesHelper(i, j))

AppendEntriesAll(i) ==
    /\ UNCHANGED <<messages, candidateVars, logVars, leaderVars, serverVars>>
    /\ IsLeader(i)
    /\ LET s == LockArgs(i, {}, AppendEntriesRequest)
       IN /\ s.lock /= Nil
          /\ ScrSet(s)
          /\ pc' = <<"AppendEntriesAll", i>>

\* Server i receives an AppendEntries request from server j 
\*  This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
HandleAppendEntriesRequest(i, j, m) ==
    LET b   == m.body
        rb1 == [ term       |-> currentTerm'[i],
                 success    |-> FALSE,
                 curIdx     |-> Len(log[i])]
        rb2 == [ term       |-> currentTerm'[i],
                 success    |-> TRUE,
                 curIdx     |-> b.prevLogIndex + Len(b.entries)]
        msg == [ type       |-> AppendEntriesResponse,
                 from       |-> i,
                 to         |-> j ]  \* Body is not included here.
    IN  /\  IF b.term < currentTerm[i] \* Term is smaller, reply false.
            THEN /\ UNCHANGED <<serverVars, logVars>>
                 /\ Reply(msg @@ ("body" :> rb1), m)
                 /\ pc' = <<"HandleAppendEntriesRequest: stale msg",
                          i, j, m.seq>>
                 /\ ScrSet(ScrIncSent)
            ELSE /\ BecomeFollower(i ,b.term) \* here serverVars has changed
                 /\ IF b.prevLogIndex > Len(log[i])
                    THEN /\ UNCHANGED <<logVars>>
                         /\ Reply(msg @@ ("body" :> rb1), m)
                         /\ ScrSet(ScrIncSent)
                         /\ pc' = <<"HandleAppendEntriesRequest: would leave gap",
                          i, j, m.seq>>
                    ELSE IF /\ b.prevLogIndex > 0
                            /\ b.prevLogIndex <= Len(log[i])
                            /\ ~log[i][b.prevLogIndex].term = b.prevLogTerm
                         THEN \* log mismatch  
                                /\ UNCHANGED <<logVars>>
                                /\ LET rb3 == [ term       |-> currentTerm'[i],
                                                success    |-> FALSE,
                                                curIdx     |-> b.prevLogIndex - 1]  \* todo may have bugs
                                   IN Reply(msg @@("body") :> rb3, m)
                                /\ pc' = <<"HandleAppendEntriesRequest: log mismatch",
                                        i, j, m.seq>>
                                /\ ScrSet(ScrIncSent)
                         ELSE /\ IF Len(b.entries) = 0
                                 THEN UNCHANGED <<log>> \* if entries is null ,log doesn't change
                                 ELSE LET new == [index2 \in 1..b.prevLogIndex |-> \*todo may have bugs
                                                        log[i][index2]]  \* prevlogIndex -> end change to b.entries
                                          new1 == new \o b.entries
                
                                      IN /\ log' = [log EXCEPT ![i] = new1]
                                        \*  /\ Print(b.entries, TRUE)
                                        \*  /\ Print(new, TRUE)
                                        \*  /\ Print(new1, TRUE)

                              /\ commitIndex' = [ commitIndex EXCEPT ![i] =
                                           IF commitIndex[i] >= b.commitIndex
                                           THEN @  \* Not updated.
                                           ELSE Min({b.commitIndex} \union
                                                    {Max({Len(log'[i]), 1})})]
                              /\ Reply(msg @@ ("body" :> rb2), m)
                              /\ pc' = <<"HandleAppendEntriesRequest: success",
                                       i, j, m.seq>>
                              /\ ScrSet(ScrIncSent)
        /\ UNCHANGED <<candidateVars, leaderVars>>

\* Advance commmitIdx.
AdvanceCommitIdx(s, idx) ==
    LET c1 == /\ commitIndex[s] < idx 
              /\ /\ Len(log[s]) >= idx
                 /\ log[s][idx].term = currentTerm[s]
        c2 == IsQuorum({i \in Server \ {s}: matchIndex'[s][i] >= idx} \union {s})
    IN commitIndex' = [ commitIndex EXCEPT ![s] = IF c1 /\ c2 THEN idx ELSE @ ]


\* Server i receives an AppendEntries response from server j.
HandleAppendEntriesResponse(i, j, m) == 
    LET b          == m.body
        not_leader == ~IsLeader(i)
        demote     == currentTerm[i] < b.term
        \* stale_msg  == \/ currentTerm[i] > b.term
        \*               \/ /\ ~b.success
        \*                  /\ matchIdx[i][j] = nextIdx[i][j] - 1 \*not success, 更新就好 为什么这个也算stale
        \*               \/ /\ b.success
        \*                  /\ b.curIdx <= matchIdx[i][j]
        stale_msg == currentTerm[i] > b.term
        retry      == /\ ~b.success
                      /\ b.curIdx >= matchIndex[i][j] \* not success, why use match, not netxIdx????
    IN IF not_leader
       THEN /\ UNCHANGED <<serverVars, candidateVars, logVars, leaderVars, scr>>
            /\ Discard(m)
            /\ pc' = <<"HandleAppendEntriesResponse: not leader", i , j, m.seq>>
       ELSE IF demote
            THEN /\ UNCHANGED <<candidateVars, leaderVars, logVars, scr>>
                 /\ Discard(m)
                 /\ BecomeFollower(i, b.term)
                 /\ pc' = <<"HandleAppendEntriesResponse: demote",
                          i, j, m.seq>>
            ELSE IF stale_msg
                 THEN /\ Discard(m)
                      /\ pc' = <<"HandleAppendEntriesResponse: stale msg",
                                i, j, m.seq>>
                      /\ UNCHANGED <<candidateVars, leaderVars, logVars, serverVars>>
                 ELSE IF retry
                      THEN /\ UNCHANGED <<serverVars, candidateVars, matchIndex,
                                          elections, logVars>>
                           /\ nextIndex' = [nextIndex EXCEPT ![i][j] = b.curIdx + 1]
                           /\ Reply(AppendEntriesHelper(i, j), m)
                           /\ ScrSet(ScrIncSent)
                           /\ pc' = <<"HandleAppendEntriesResponse: mismatch and retry", i, j, m.seq>>
                      ELSE /\ UNCHANGED <<serverVars, candidateVars,
                                          elections, logVars, messages, scr>>
                           /\ nextIndex' = [ nextIndex EXCEPT ![i][j] = b.curIdx+1 ]
                           /\ matchIndex' = [ matchIndex EXCEPT ![i][j] = b.curIdx ]
                           /\ AdvanceCommitIdx(i, b.curIdx)
                           /\ pc' = <<"HandleAppendEntriesResponse: success",
                                          i, j, m.seq>>

\* Leader i receives a client request to add v to the log.
ClientRequest(i, v) ==
    /\ IsLeader(i)
    /\ LET entry == [term  |-> currentTerm[i],
                     value |-> v]
           newLog == Append(log[i], entry)
       IN  log' = [log EXCEPT ![i] = newLog]
    /\ pc' = <<"ClientRequest", i, v>>
    /\ UNCHANGED <<messages, serverVars, candidateVars,
                   leaderVars, commitIndex, scr>>
\* Candidate i sends j a RequestVote request.
RequestVote(i, j) ==
    LET body == [ term          |-> currentTerm'[i],
                  candidate     |-> i,
                  lastLogIdx    |-> Len(log[i]),
                  lastLogTerm   |-> LastTerm(log[i]) ]
        msg  == [ type |-> RequestVoteRequest,
                  from |-> i,
                  to   |-> j,
                  body |-> body ]
    IN Send(msg)

\* Send RequestVoteRequest to all servers except me and servers in set s.
RequestVoteAll(i) ==
    LET s == LockArgs(i, {}, RequestVoteRequest)
    IN /\ ScrSet(s) \* only use in lock
       /\ pc' = <<"Timeout: election", i>>

BecomeCandidate(i) ==
    /\ state'           = [ state           EXCEPT ![i] = Candidate ]
    /\ currentTerm'     = [ currentTerm     EXCEPT ![i] = @ + 1 ]
    \* Set the local vote atomically.
    /\ votedFor'        = [ votedFor        EXCEPT ![i] = i ]
    /\ votesGranted'    = [ votesGranted    EXCEPT ![i] = {i} ]
    /\ RequestVoteAll(i)

\* Server i receives a RequestVote request from server j.
\* Note: WRAFT code checks if timeElapsed >= electionTimeout * 1. TLA+ doesn't
\*       model timeout and servers are always votable.

HandleRequestVoteRequest(i, j, m) ==
    LET body        == m.body
        logOk       ==  \/ body.lastLogTerm > LastTerm(log[i])
                        \/ /\ body.lastLogTerm = LastTerm(log[i])
                           /\ body.lastLogIdx >= Len(log[i])
        voteNil     == \/ votedFor[i] = Nil
                       \/ body.term > currentTerm[i]
        canGrant    == /\ ~IsLeader(i)
                       /\ logOk
                       /\ votedFor[i] \in {body.candidate, Nil}
        rb          == [ term |-> currentTerm'[i], voteGranted |-> canGrant ]
        stale_msg   == body.term < currentTerm[i]
        demote      == body.term > currentTerm[i]
        msg         == [ type |-> RequestVoteResponse,
                         from |-> i,
                         to   |-> j,
                         body |-> rb ]
    IN IF IsLeader(i)
       THEN /\ UNCHANGED <<serverVars, leaderVars, logVars, candidateVars>>
            /\ Print("1", TRUE)
            /\ Reply(msg, m)
            /\ ScrSet(ScrIncSent)
            /\ pc' = <<"HandleRequestVoteRequest: leader not granted",
                              i, j, m.seq>>
       ELSE IF stale_msg
            THEN /\ UNCHANGED <<candidateVars, leaderVars, logVars, serverVars, scr>>
                 /\ Discard(m)
                 /\ Print("2", TRUE)
                 /\ pc' = <<"HandleRequestVoteRequest: stale msg",
                                i, j, m.seq>>
            ELSE IF demote
                 THEN   /\ UNCHANGED <<leaderVars, logVars, candidateVars, scr>>
                        /\ state'       = [ state       EXCEPT ![i] = Follower ]
                        /\ currentTerm' = [ currentTerm EXCEPT ![i] = body.term ]
                        /\ votedFor' = [ votedFor  EXCEPT ![i] = IF canGrant
                                                  THEN Nil      ELSE j ]
                        /\ Reply(msg, m)
                        /\ ScrSet(ScrIncSent)
                        /\ pc' = <<"HandleRequestVoteRequest: granted",
                                   i, j, m.seq>>
                        /\ Print("3", TRUE)
                 ELSE IF canGrant
                      THEN  /\ UNCHANGED <<state, currentTerm, leaderVars, logVars, candidateVars, scr>>
                            /\ votedFor' = [ votedFor  EXCEPT ![i] = IF canGrant
                                                  THEN Nil      ELSE j ]
                            /\ Reply(msg, m)
                            /\ ScrSet(ScrIncSent)
                            /\ pc' = <<"HandleRequestVoteRequest: granted",
                                   i, j, m.seq>>
                            /\ Print("4", TRUE)
                      ELSE /\ UNCHANGED <<vars>>
                            /\ pc' = <<"HandleRequestVoteRequest: all fail",
                                   i, j, m.seq>>
                            /\ Print(votedFor[i], {body.candidate, Nil})
                            


HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ Discard(m)
    /\ UNCHANGED <<scr>>
    /\ LET b == m.body
           notCandidate == ~IsCandidate(i)
           staleMsg     == currentTerm[i] > b.term
           notGranted   == currentTerm[i] = b.term /\ ~b.voteGranted
       IN IF notCandidate \/ staleMsg \/ notGranted
          THEN /\ UNCHANGED <<serverVars, leaderVars,logVars, candidateVars, scr>>
               /\ pc' = <<CASE notCandidate -> "HandleRequestVoteResponse: not candidate"
                        [] staleMsg     -> "HandleRequestVoteResponse: stale msg"
                        [] notGranted   -> "HandleRequestVoteResponse: not granted"
                        [] OTHER        -> Assert(FALSE,
                           "HandleRequestVoteResponse unhandled CASE"),
                      i, j, m.seq>>
          ELSE IF currentTerm[i] < b.term
               THEN /\ UNCHANGED <<candidateVars, leaderVars, logVars>>
                    /\ BecomeFollower(i, b.term)
                    /\ pc' = <<"HandleRequestVoteResponse: demote",
                                  i, j, m.seq>>
               ELSE /\ votesGranted' = [ votesGranted EXCEPT ![i] =
                                            @ \union {j}]
                    /\ IF IsQuorum(votesGranted'[i])
                       THEN /\ UNCHANGED <<elections, currentTerm, votedFor, logVars>>
                            /\ BecomeLeader(i)
                            \* Note: sends append entries immediately
                            /\ pc' = <<"HandleRequestVoteResponse: promote",
                                        i, j, m.seq>>
                       ELSE /\ UNCHANGED <<serverVars, leaderVars, logVars>>
                            /\ pc' = <<"HandleRequestVoteResponse: get vote",
                                          i, j, m.seq>>


\* Election timeout, become candidate and send request vote
Timeout(i) == /\ ~IsLeader(i)
              /\ UNCHANGED <<messages, leaderVars, logVars>>
              /\ BecomeCandidate(i)

Receive(m) ==
    LET t == m.type
        i == m.to
        j == m.from
    IN  /\ CASE t = AppendEntriesRequest  -> HandleAppendEntriesRequest (i, j, m)
            [] t = AppendEntriesResponse -> HandleAppendEntriesResponse(i, j, m)
            [] t = RequestVoteRequest    -> HandleRequestVoteRequest   (i, j, m)
            [] t = RequestVoteResponse   -> HandleRequestVoteResponse  (i, j, m)
            [] OTHER -> Assert(FALSE, "Receive unhandled CASE")
        /\ Assert(i /= j, "Receive i = j")
       

DuplicateMessage(m) ==
    /\ Send(m)
    /\ pc' = <<"Duplicate", Nil, Nil, m.seq>>
    /\ ScrSet(ScrIncSent)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ pc' = <<"Drop", Nil, Nil, m.seq>>
    /\ ScrSet(ScrIncSent)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>


DoHandleAppendEntriesRequest    == ScrNotLocked /\ \E m \in messages:
                                    m.type = AppendEntriesRequest  /\ Receive(m)
DoHandleAppendEntriesResponse   == ScrNotLocked /\ \E m \in messages:
                                    m.type = AppendEntriesResponse /\ Receive(m)
DoHandleRequestVoteRequest      == ScrNotLocked /\ \E m \in messages:
                                    m.type = RequestVoteRequest    /\ Receive(m)
DoHandleRequestVoteResponse     == ScrNotLocked /\ \E m \in messages:
                                    m.type = RequestVoteResponse   /\ Receive(m)
DoAppendEntriesAll              == ScrNotLocked /\ \E i \in Server:
                                    AppendEntriesAll(i)
DoClientRequest                 == ScrNotLocked /\ \E i \in Server, v \in Value:
                                    ClientRequest(i, v)
DoTimeout                       == ScrNotLocked /\ \E i \in Server:
                                    Timeout(i)
DoRestart                       == ScrNotLocked /\ \E i \in Server:
                                    Restart(i)
DoDrop                          == ScrNotLocked /\ \E m \in messages :
                                    DropMessage(m)
DoDuplicate                     == ScrNotLocked /\ \E m \in messages :
                                    DuplicateMessage(m)

DoLoop == /\ UNCHANGED <<serverVars, leaderVars, logVars, candidateVars>>
          /\ ScrIsLocked
          /\ Cardinality(scr.lock.args) /= 0
          /\ LET a  == CHOOSE x \in scr.lock.args: TRUE
                 t  == ScrGetLockType
                 s  == ScrDeleteLockArg(a) @@ ScrIncSent
                 i  == a.from
                 j  == a.to
             IN CASE t = AppendEntriesRequest ->
                    /\ AppendEntries(i, j)
                    /\ ScrSet(s)
                    /\ pc' =  <<"DoLoop: AppendEntries",
                                   i, j, scr.nSent + 1>>
                [] t = RequestVoteRequest   ->
                    /\ RequestVote(i, j)
                    /\ ScrSet(s)
                    /\ pc' = <<"DoLoop: RequestVote",
                                   i, j, scr.nSent + 1>>


Next == 
       \/ DoHandleAppendEntriesRequest
       \/ DoHandleAppendEntriesResponse
       \/ DoHandleRequestVoteRequest
       \/ DoHandleRequestVoteResponse
       \/ DoAppendEntriesAll
       \/ DoClientRequest
        \/ DoTimeout
        \/ DoRestart
       \/ DoDrop
       \/ DoDuplicate
        \/ DoLoop




\* question : 对于嵌套函数，variable'怎么变化
Spec == Init /\ [][Next]_vars
===============================================================================
