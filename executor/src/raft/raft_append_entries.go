package raft

// import (
// 	"time"
// )

type AppendEntriesArgs struct {
	Term         int        //leader's term
	LeaderId     int        //so follower can redirect clients
	PrevLogIndex int        //index of log entry immediatly preceding new ones
	PrevLogTerm  int        //term of prevLogIndex term
	Entries      []LogEntry // log entries to store
	LeaderCommit int        //leader's commitIndex
}

type AppendEntriesReply struct {
	Term    int  // currentTerm, for leader to update ieself
	Success bool //true if follower contained entry matching prevLogIndex and PrevLogTerm
	// ConflictIndex int  //use in reply, smallest index which log is conflict

	XTerm  int // term of conflict entry
	XIndex int // index of first entry of Xterm
	XLen   int // length of logs
}

func (rf *Raft) replicate() {
	rf.lock("replicate")
	defer rf.unLock("replicate")
	DPrintf("%d, replicate log entries", rf.me)
	for i := 0; i < len(rf.peers); i++ {
		if i != rf.me {
			go rf.sendLogEntry(i)
		}
	}
}

//make append entries call to follower and handle reply
func (rf *Raft) sendLogEntry(server int) {
	rf.lock("sendLogEntry1")
	DPrintf("%d, sendLogEntry", rf.me)
	// defer rf.unLock("sendLogEntry1")

	if rf.role != Leader {
		rf.unLock("sendLogEntry1")
		return
	}
	DPrintf("%d, server %d, nextIndex: %v", rf.me, server, rf.nextIndex)
	prevLogIndex := rf.nextIndex[server] - 1
	// println("prevLogIndex %d", prevLogIndex)

	PrevLogTerm := rf.logs[prevLogIndex].Term
	args := AppendEntriesArgs{Term: rf.currentTerm, LeaderId: rf.me,
		PrevLogIndex: prevLogIndex, PrevLogTerm: PrevLogTerm,
		LeaderCommit: rf.commitIndex, Entries: nil}
	if rf.nextIndex[server] < len(rf.logs) {
		args.Entries = rf.logs[rf.nextIndex[server]:]
	}
	// DPrintf("%d, logs %v", rf.me, args.Entries)
	rf.unLock("sendLogEntry1")
	reply := AppendEntriesReply{}
	// 切忌 此处不可以加锁，因为使用到了rpc 否则会进入死锁
	ok := rf.sendLogEntryToFollower(server, &args, &reply)
	if ok {
		rf.lock("handle")
		DPrintf("%d, sendLogEntry succeed,reply :%v", rf.me, reply)
		rf.handleAppendEntry(server, args, reply)
		rf.unLock("handle")
	} else {
		DPrintf("%d, sendLogEntry fail", rf.me)
		// time.Sleep(time.Millisecond * 10)
	}

}

func (rf *Raft) sendLogEntryToFollower(server int, args *AppendEntriesArgs, reply *AppendEntriesReply) bool {
	DPrintf("%d send AppendEntries to %d", rf.me, server)
	ok := rf.peers[server].Call("Raft.AppendEntries", args, reply)
	return ok
}

func (rf *Raft) handleAppendEntry(server int, args AppendEntriesArgs, reply AppendEntriesReply) {
	// rf.lock("handleAppendEntry")
	DPrintf("%d, reply is %v handleAppendEntry", rf.me, reply)
	// defer rf.unLock("handleAppendEntry")
	if rf.role != Leader {
		DPrintf("%d is not leader, but receive a reply", rf.me)
		return
	}

	if reply.Success {
		prevLogIndex, logEntryLen := args.PrevLogIndex, len(args.Entries)
		if prevLogIndex+logEntryLen >= rf.nextIndex[server] { // need update

			rf.nextIndex[server] = prevLogIndex + logEntryLen + 1
			rf.matchIndex[server] = prevLogIndex + logEntryLen
			DPrintf("%d, update nextindex[%d] -> %d, matchIndex[%d] -> %d", rf.me, server, rf.nextIndex[server], server, rf.matchIndex[server])
		}
		// todo need commit ?????????
		toCommitIndex := rf.matchIndex[server]
		if rf.canCommit(toCommitIndex) {
			rf.commitIndex = toCommitIndex
			go rf.commitLogs()
		}
	} else {
		if reply.Term > rf.currentTerm { // me fall behind
			rf.changeRole(Follower)
			rf.currentTerm = args.Term
			rf.votedFor = -1
			rf.persist()
		} else { // follower is inconsistent with leader
			//may have bugs
			// rf.nextIndex[Follower] = reply.XIndex
			if reply.XTerm != -1 && rf.logs[reply.XIndex].Term != reply.XTerm {
				rf.nextIndex[server] = reply.XIndex
				DPrintf("%d .nextindex[%d] -> reply.XIndex: %d", rf.me, server, reply.XIndex)
			} else if reply.XTerm != -1 && rf.logs[reply.XIndex].Term == reply.XTerm {
				rf.nextIndex[server] = reply.XIndex + 1
				DPrintf("%d .nextindex[%d] -> reply.XIndex + 1: %d", rf.me, server, rf.nextIndex[server])
			} else if reply.XTerm == -1 {
				DPrintf("%d .nextindex[%d] -> rf.nextIndex[%d]: %d- reply.XLen: %d", rf.me, server, server, rf.nextIndex[server], reply.XLen)
				rf.nextIndex[server] = rf.nextIndex[server] - reply.XLen
			} else {
				panic("append entries occur unknown circumstances")
			}
			if rf.nextIndex[server] > len(rf.logs) { // ?????? may happen?????
				DPrintf("%d .nextindex[%d] is longer than its logs", rf.me, server)
				rf.nextIndex[server] = len(rf.logs)
			}
		}
	}
}

func (rf *Raft) AppendEntries(args *AppendEntriesArgs, reply *AppendEntriesReply) {
	rf.lock("AppendEntries")
	DPrintf("leader %d append Entries to %d, me is %d", args.LeaderId, rf.me, rf.me)
	// DPrintf("leader %d append Entries %v to %d, me is %d", args.LeaderId, *args, rf.me, rf.me)
	defer rf.unLock("AppendEntries")
	if args.Term < rf.currentTerm {
		DPrintf("%d, args.Term < rf.currentTerm, throw the append entries", rf.me)
		reply.Success = false
		reply.Term = rf.currentTerm
		return
	} else {
		// DPrintf("%d, args.Term >= rf.currentTerm, handle %v", rf.me, *args)
		rf.currentTerm = args.Term
		rf.votedFor = -1
		rf.changeRole(Follower)
		rf.resetElectionTimer()
		reply.Term = rf.currentTerm
		rf.persist()
		// defer DPrintf("%d, reply %v", rf.me, *reply)
		if args.PrevLogIndex >= 0 && args.PrevLogIndex >= len(rf.logs) {
			DPrintf("%d, leader's log longer than the follower, args:%v, ", rf.me, *args)
			reply.XTerm = -1
			reply.XLen = args.PrevLogIndex - len(rf.logs) + 1
			reply.Success = false
			DPrintf("%d, reply %v", rf.me, *reply)
		} else if args.PrevLogIndex >= 0 && // first need leader has logs
			rf.logs[args.PrevLogIndex].Term != args.PrevLogTerm { // leaders log term doesn't match followers
			DPrintf("%d, leader's log  doesn't match followers, args:%v, conflict log: %v", rf.me, *args, rf.logs[args.PrevLogIndex])
			reply.XTerm = rf.logs[args.PrevLogIndex].Term
			reply.XIndex = args.PrevLogIndex
			for reply.XIndex >= 0 {
				if rf.logs[reply.XIndex].Term == reply.XTerm {
					reply.XIndex--
				} else {
					break
				}
			}
			reply.XIndex++
			reply.Success = false
			DPrintf("%d, reply %v", rf.me, *reply)
		} else if args.Entries == nil { //heartbeat packet
			if args.LeaderCommit > rf.lastApplied { // apply log[lastApplied] to state machines
				DPrintf("%d, get heartbeat packet, args:%v ", rf.me, *args)
				rf.commitIndex = args.LeaderCommit
				go rf.commitLogs()
			}
			reply.Success = true
			DPrintf("%d, reply %v", rf.me, *reply)
		} else if args.PrevLogIndex >= 0 && // first need leader has logs
			(args.PrevLogIndex <= len(rf.logs)-1) &&
			rf.logs[args.PrevLogIndex].Term == args.PrevLogTerm { // match, append
			DPrintf("%d, match need append, args:%v", rf.me, *args)
			rf.logs = rf.logs[:args.PrevLogIndex+1]
			rf.logs = append(rf.logs, args.Entries...)
			if args.LeaderCommit > rf.lastApplied { // apply log[lastApplied] to state machines
				rf.commitIndex = args.LeaderCommit
				go rf.commitLogs()
			}
			reply.Success = true
			DPrintf("%d, reply %v", rf.me, *reply)
		}

	}
}

func (rf *Raft) commitLogs() {
	rf.lock("commitLogs")
	defer rf.unLock("commitLogs")
	DPrintf("%d, commit logs", rf.me)

	if rf.commitIndex > len(rf.logs)-1 {
		panic("rf.commitIndex > len(rf.logs) - 1, out of range")
	} else {
		for i := rf.lastApplied + 1; i <= rf.commitIndex; i++ {
			rf.applyCh <- ApplyMsg{CommandValid: true, CommandIndex: i, Command: rf.logs[i].Command}
			DPrintf("%d, send applych %v", rf.me, ApplyMsg{CommandValid: true, CommandIndex: i, Command: rf.logs[i].Command})
		}

	}
	// go rf.showAllLogs()
	rf.lastApplied = rf.commitIndex
}

func (rf *Raft) canCommit(toCommitIndex int) bool {
	if toCommitIndex > rf.commitIndex && rf.getLog(toCommitIndex).Term == rf.currentTerm {
		count, majority := 1, len(rf.peers)/2+1
		for i := 0; i < len(rf.peers); i++ {
			if i == rf.me {
				continue
			}
			if rf.matchIndex[i] >= toCommitIndex {
				count++
			}
		}
		return count >= majority

	} else {
		return false
	}

}
