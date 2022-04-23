package raft

func (rf *Raft) RequestVote(args *RequestVoteArgs, reply *RequestVoteReply) {
	// Your code here (2A, 2B).
	rf.lock("RequestVote")
	defer rf.unLock("RequestVote")
	DPrintf("%d ask Request vote %v from %d, me is %d", args.CandidateID, *args, rf.me, rf.me)
	lastLogTerm, lastLogIndex := rf.getLastLogTermIndex()
	reply.Term = rf.currentTerm
	reply.VoteGranted = false
	reply.From = rf.me
	reply.To = args.From

	defer rf.persist()
	//raft 5.4 have given what's new
	if args.Term < rf.currentTerm { // 若发送来的包是旧的直接丢弃
		DPrintf("%d : args.Term < rf.currentTerm", rf.me)
		return
	} else if args.Term == rf.currentTerm { //发来的包 和现在属于同一term， 会出现吗？  有点质疑 （或许 会有两个 分区同时选拔leader 然后互相发送的情况
		DPrintf("%d : args.Term == rf.currentTerm", rf.me)
		if rf.role == Leader { // leader don't votes
			return
		} else if rf.votedFor != -1 && rf.votedFor != args.CandidateID { // have send votes to another peer
			// 若出现已经给别人投票的情况则不再投票
			return
		} else if rf.votedFor == args.CandidateID { // have sent to canditate, incase of repeating
			DPrintf("%d, have sent, incase of repeating remeber don't add count, candidate ID: %d", rf.me, args.CandidateID)
			reply.VoteGranted = true
			return
		}
	} else if args.Term > rf.currentTerm {
		//需要更新现有term
		DPrintf("%d : args.Term > rf.currentTerm", rf.me)
		rf.currentTerm = args.Term
		reply.Term = args.Term
		rf.votedFor = -1
		reply.VoteGranted = false
		// rf.changeRole(Follower)
	}

	if lastLogTerm > args.LastLogTerm || (lastLogTerm == args.LastLogTerm && args.LastLogIndex < lastLogIndex) {
		// leader election 的限制 ，我们仅能选取含有较新log的节点
		DPrintf("%d, %v args not up-to-date", rf.me, *args)
		return
	}
	//若到达此处 说明需要给candidate 投票 更新所需要的reply ，并转换为 follower 更新electiontimer
	rf.currentTerm = args.Term
	rf.votedFor = args.CandidateID
	reply.VoteGranted = true
	reply.Term = rf.currentTerm
	rf.changeRole(Follower)
	rf.resetElectionTimer() // when vote reset election timer
	DPrintf("%d : %d vote for %d", rf.me, rf.me, rf.votedFor)

}

//
// example code to send a RequestVote RPC to a server.
// server is the index of the target server in rf.peers[].
// expects RPC arguments in args.
// fills in *reply with RPC reply, so caller should
// pass &reply.
// the types of the args and reply passed to Call() must be
// the same as the types of the arguments declared in the
// handler function (including whether they are pointers).
//
// The labrpc package simulates a lossy network, in which servers
// may be unreachable, and in which requests and replies may be lost.
// Call() sends a request and waits for a reply. If a reply arrives
// within a timeout interval, Call() returns true; otherwise
// Call() returns false. Thus Call() may not return for a while.
// A false return can be caused by a dead server, a live server that
// can't be reached, a lost request, or a lost reply.
//
// Call() is guaranteed to return (perhaps after a delay) *except* if the
// handler function on the server side does not return.  Thus there
// is no need to implement your own timeouts around Call().
//
// look at the comments in ../labrpc/labrpc.go for more details.
//
// if you're having trouble getting RPC to work, check that you've
// capitalized all field names in structs passed over RPC, and
// that the caller passes the address of the reply struct with &, not
// the struct itself.
//
func (rf *Raft) sendRequestVote(server int, args *RequestVoteArgs, reply *RequestVoteReply) bool {
	DPrintf("%d send RequestVote %v to %d", rf.me, *args, server)
	ok := rf.peers[server].Call("Raft.RequestVote", args, reply)
	return ok
}

//对于rpc调用后返回的信息进行处理，来更新 调用者信息
func (rf *Raft) handleVoteResult(reply RequestVoteReply) {
	rf.lock("handleVoteResult")
	DPrintf("%d, handleVoteResult", rf.me)
	defer rf.unLock("handleVoteResult")
	// defer rf.persist()

	//回复包是过期的丢掉
	if reply.Term < rf.currentTerm { // reply term is less than rf.term , drop it
		DPrintf("%d, reply.Term < rf.currentTerm, drop it. reply: %v, %v", rf.me, reply, rf.currentTerm)
		return
	} else if reply.Term > rf.currentTerm {
		//若是 回复的包是超过me的，则说明me 已经落后（因为掉线或者。。。） ，需要重新变为follower ，记住恢复follower所需的信息，投票信息也需要重置
		DPrintf("%d, reply.Term > rf.currentTerm, me change to follower", rf.me)
		rf.currentTerm = reply.Term
		rf.votedFor = -1
		rf.persist()
		return
	} else if rf.role == Candidate && reply.VoteGranted {
		// me是竞选者 并且获得选票 +1
		DPrintf("%d gets a vote", rf.me)
		rf.getVotes += 1
		if rf.getVotes >= len(rf.peers)/2+1 {
			//超过半数 成为leader
			// log.Printf("%d get votes %d", rf.me, rf.getVotes)
			rf.changeRole(Leader)
			// go rf.leaderAnounce()
			//开始可以将自己的log复制给其他人
			//go rf.tick()  //todo need turn back
			go rf.Replicate()
		}

	} else if rf.role == Leader && reply.VoteGranted {
		DPrintf("%d, is leader already", rf.me)
		return
	} else {
		DPrintf("%d, reply: %v, %v", rf.me, reply, rf.currentTerm)
	}
}
