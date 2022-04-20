package raft

//
// this is an outline of the API that raft must expose to
// the service (or tester). see comments below for
// each of these functions for more details.
//
// rf = Make(...)
//   create a new Raft server.
// rf.Start(command interface{}) (index, term, isleader)
//   start agreement on a new log entry
// rf.GetState() (term, isLeader)
//   ask a Raft for its current term, and whether it thinks it is leader
// ApplyMsg
//   each time a new entry is committed to the log, each Raft peer
//   should send an ApplyMsg to the service (or tester)
//   in the same server.
//

import (
	//	"bytes"
	"bytes"
	"crypto/rand"
	"math/big"
	"sync"
	"sync/atomic"

	//	"6.824/labgob"
	"time"

	"executor/labgob"
	"executor/labrpc"
)

type Role int

const (
	Leader    Role = 1
	Follower  Role = 2
	Candidate Role = 3
)

const BigInt = 9999999

const (
	ElectionTimeout      = time.Millisecond * 300 // election timeout
	HeartbeatTimeout     = time.Millisecond * 100
	AppendEntriesTimeout = time.Millisecond * 100 // 100ms 通关 ，200ms 未试
	MaxDurationTime      = time.Millisecond * 10  // ?????
)

//
// as each Raft peer becomes aware that successive log entries are
// committed, the peer should send an ApplyMsg to the service (or
// tester) on the same server, via the applyCh passed to Make(). set
// CommandValid to true to indicate that the ApplyMsg contains a newly
// committed log entry.
//
// in part 2D you'll want to send other kinds of messages (e.g.,
// snapshots) on the applyCh, but set CommandValid to false for these
// other uses.
//
type ApplyMsg struct {
	CommandValid bool
	Command      interface{}
	CommandIndex int

	// For 2D:
	SnapshotValid bool
	Snapshot      []byte
	SnapshotTerm  int
	SnapshotIndex int
}

//
// A Go object implementing a single Raft peer.
//
type Raft struct {
	mu        sync.Mutex          // Lock to protect shared access to this peer's state
	peers     []*labrpc.ClientEnd // RPC end points of all peers
	persister *Persister          // Object to hold this peer's persisted state
	me        int                 // this peer's index into peers[]
	dead      int32               // set by Kill()

	// Your data here (2A, 2B, 2C).

	role Role // 角色 follower， candidate， leader

	//2A
	//persistent state
	currentTerm int        // latest term server has been
	votedFor    int        // candidateId that received vote in current Term
	logs        []LogEntry // logs

	//violate state
	commitIndex int // index of highest log entry known to be commited
	lastApplied int // index of highest log entry applied to state machine

	//violate state for leader
	nextIndex  []int
	matchIndex []int

	//other staff
	elecitonTimer      *time.Timer // election timer, when timeout turn to  candidate
	getVotes           int         // the number this peer gets votes ，统计得到了多少票
	numSendRequestVote int         // the number me sends Requests

	lockName  string    //for debug  锁的名称，想借助上锁时上锁名称来防止锁重复，但好像没什么用
	lockStart time.Time //for debug
	lockEnd   time.Time //for debug
	// Look at the paper's Figure 2 for a description of what
	// state a Raft server must maintain.

	test bool // or controller, not to tick timer

	stopCh  chan struct{} // 监听信道，通过调用 close 来关闭 来获取信息，从而推出函数循环（用来模拟election timer 计数）
	applyCh chan ApplyMsg
}
type LogEntry struct {
	Command interface{}
	Term    int
	Idx     int // only for debug
}

// return currentTerm and whether this server
// believes it is the leader.
func (rf *Raft) GetState() (int, bool) {
	rf.lock("GetState")
	defer rf.unLock("GetState")
	term := rf.currentTerm
	isleader := (rf.role == Leader)
	// Your code here (2A).
	return term, isleader
}

//
// save Raft's persistent state to stable storage,
// where it can later be retrieved after a crash and restart.
// see paper's Figure 2 for a description of what should be persistent.
//
func (rf *Raft) persist() {
	// Your code here (2C).
	// Example:

	w := new(bytes.Buffer)
	e := labgob.NewEncoder(w)
	e.Encode(rf.currentTerm)
	e.Encode(rf.votedFor)
	e.Encode(rf.logs)
	// e.Encode(rf.commitIndex)
	// e.Encode(rf.xxx)
	// e.Encode(rf.yyy)
	data := w.Bytes()
	rf.persister.SaveRaftState(data)
}

//
// restore previously persisted state.
//
func (rf *Raft) readPersist(data []byte) {
	if data == nil || len(data) < 1 { // bootstrap without any state?
		return
	}
	// Your code here (2C).
	// Example:
	r := bytes.NewBuffer(data)
	d := labgob.NewDecoder(r)
	var currentTerm int
	var votedFor int
	var logs []LogEntry
	// var commitIndex int
	if d.Decode(&currentTerm) != nil ||
		d.Decode(&votedFor) != nil ||
		d.Decode(&logs) != nil {
		DPrintf("rf read persist err")
	} else {
		rf.currentTerm = currentTerm
		rf.votedFor = votedFor
		rf.logs = logs
		// rf.commitIndex = commitIndex
	}
	// if d.Decode(&xxx) != nil ||
	//    d.Decode(&yyy) != nil {
	//   error...
	// } else {
	//   rf.xxx = xxx
	//   rf.yyy = yyy
	// }
}

//
// A service wants to switch to snapshot.  Only do so if Raft hasn't
// have more recent info since it communicate the snapshot on applyCh.
//
func (rf *Raft) CondInstallSnapshot(lastIncludedTerm int, lastIncludedIndex int, snapshot []byte) bool {

	// Your code here (2D).

	return true
}

// the service says it has created a snapshot that has
// all info up to and including index. this means the
// service no longer needs the log through (and including)
// that index. Raft should now trim its log as much as possible.
func (rf *Raft) Snapshot(index int, snapshot []byte) {
	// Your code here (2D).

}

//
// example RequestVote RPC arguments structure.
// field names must start with capital letters!
//
type RequestVoteArgs struct {
	// Your data here (2A, 2B).
	Term         int //candidate term
	CandidateID  int //candidate requesting vote
	LastLogIndex int //index of candidate's last log entry
	LastLogTerm  int //term of candidate's last log entry
	From         int
	To           int
}

//
// example RequestVote RPC reply structure.
// field names must start with capital letters!
//
type RequestVoteReply struct {
	// Your data here (2A).
	Term        int  // currentTerm, for candidate to update itself
	VoteGranted bool // true means candidate received vote
	From        int
	To          int
}

//
// example RequestVote RPC handler.
//

//
// the service using Raft (e.g. a k/v server) wants to start
// agreement on the next command to be appended to Raft's log. if this
// server isn't the leader, returns false. otherwise start the
// agreement and return immediately. there is no guarantee that this
// command will ever be committed to the Raft log, since the leader
// may fail or lose an election. even if the Raft instance has been killed,
// this function should return gracefully.
//
// the first return value is the index that the command will appear at
// if it's ever committed. the second return value is the current
// term. the third return value is true if this server believes it is
// the leader.
//
func (rf *Raft) Start(command interface{}) (int, int, bool) {
	rf.lock("start")
	defer rf.unLock("start")
	DPrintf("%d, start a agreement, ", rf.me)
	index := len(rf.logs) - 1
	term := rf.currentTerm
	isLeader := (rf.role == Leader)
	if rf.killed() {
		DPrintf("%d, is killed", rf.me)
		return index, term, isLeader
	} else if rf.role != Leader { // 由于test 调用中会随机抽取，所以不保证每次发给集群中都可以精确访问到leader 所以需要判断
		DPrintf("%d, not leader, return immediately", rf.me)
		return index, term, isLeader
	}
	newLog := LogEntry{Command: command, Term: rf.currentTerm, Idx: len(rf.logs)}
	rf.logs = append(rf.logs, newLog) // 在 本地logs 后直接append
	index = len(rf.logs) - 1
	term = rf.currentTerm
	DPrintf("%d, append logs index at %v", rf.me, newLog.Idx)
	// Your code here (2B).

	return index, term, isLeader
}

//展示所有logs  debug用
func (rf *Raft) showAllLogs() {
	rf.lock("showAllLogs")
	DPrintf("%d, show all logs", rf.me)
	defer rf.unLock("showAllLogs")
	for i := 0; i < len(rf.logs); i++ {
		DPrintf("%v", rf.logs[i])
	}
}

//
// the tester doesn't halt goroutines created by Raft after each test,
// but it does call the Kill() method. your code can use killed() to
// check whether Kill() has been called. the use of atomic avoids the
// need for a lock.
//
// the issue is that long-running goroutines use memory and may chew
// up CPU time, perhaps causing later tests to fail and generating
// confusing debug output. any goroutine with a long-running loop
// should call killed() to check whether it should stop.
//

func (rf *Raft) Kill() {

	rf.lock("Kill")
	defer rf.unLock("Kill")
	atomic.StoreInt32(&rf.dead, 1)
	// Your code here, if desired.
	close(rf.stopCh)
	DPrintf("Kill raft %d at %d , lastApplied: %d ", rf.me, rf.currentTerm, rf.lastApplied)
}

func (rf *Raft) killed() bool {
	z := atomic.LoadInt32(&rf.dead)
	return z == 1
}

// The ticker go routine starts a new election if this peer hasn't received
// heartsbeats recently.
func (rf *Raft) ticker() {
	for rf.killed() == false {

		// Your code here to check if a leader election should
		// be started and to randomize sleeping time using
		// time.Sleep().

	}
}

func (rf *Raft) lock(s string) {
	rf.mu.Lock()
	rf.lockName = s
	rf.lockStart = time.Now()
}

//解锁，如果解锁名 出现了和 上锁名不一致，必然逻辑错误,若解锁时间过长 也判定错误， debug用
func (rf *Raft) unLock(s string) {
	defer rf.mu.Unlock()
	rf.lockEnd = time.Now()
	if rf.lockName != "" && s != rf.lockName {
		DPrintf("Lock Name differs, lock start %s, lock end %s", rf.lockName, s)
		panic("lock wrong")
	}
	if Debug {
		duratioin := rf.lockEnd.Sub(rf.lockStart)
		if duratioin > MaxDurationTime {
			DPrintf("Lock too long, lock %s:%v  %v is killed", s, duratioin, rf.killed())
		}
	}
}

func (rf *Raft) resetElectionTimer() {
	rf.elecitonTimer.Stop()
	rf.elecitonTimer.Reset(randElectionTimeout())
}

func (rf *Raft) getLog(index int) LogEntry {
	return rf.logs[index]
}

//role change, need change term
// 转变角色 ， 不用上锁，因为转变角色必在已经上锁的进程中完成转变
func (rf *Raft) changeRole(role Role) { // because every step into this function, it has already add lock
	// rf.lock("changeRole")
	DPrintf("%d: changeRole", rf.me)
	// defer rf.unLock("changeRole")
	rf.role = role
	switch role {
	case Follower:
		DPrintf("%d, change to follower", rf.me)
		// rf.getVotes = 1
	case Candidate:
		//进入candidate 需要 增加自己的term 并且 将 votedfor 以及 getvotes 设为初始值，否则会出现后续投票错误的情况
		DPrintf("%d, change to Candidate", rf.me)
		rf.currentTerm += 1
		rf.votedFor = rf.me
		rf.getVotes = 1
		rf.persist()
	case Leader: //leader add what's need most
		//变为leader 需要增加 leader 所需要专属保存的 matchindex 以及 nextindex
		DPrintf("%d, change to Leader", rf.me)
		_, lastIndex := rf.getLastLogTermIndex()
		rf.nextIndex = make([]int, len(rf.peers))
		for i := 0; i < len(rf.peers); i++ {
			rf.nextIndex[i] = lastIndex + 1
		}
		rf.matchIndex = make([]int, len(rf.peers))
		for i := 0; i < len(rf.peers); i++ {
			rf.matchIndex[i] = 0
		}
		// rf.getVotes = 1
	default:
		panic("undefined role")
	}

}

func (rf *Raft) getLastLogTermIndex() (int, int) {
	if len(rf.logs) == 0 {
		return -1, -1
	}
	term := rf.logs[len(rf.logs)-1].Term // the last term
	index := len(rf.logs) - 1

	return term, index
}

// func (rf *Raft) leaderAnounce

//tick to replicate (empty)log to follower
// 设计 appendentries 计时器 通过计时来触发 appendentries 事件，这样可以不断的判断从而发送心跳包以及 logs
func (rf *Raft) tick() {
	DPrintf("%d, tick to send logs", rf.me)
	timer := time.NewTimer(AppendEntriesTimeout)
	for {
		select {
		case <-rf.stopCh:
			// DPrintf("kill??? %v", rf.killed())
			return
		case <-timer.C: //send appendEntries
			if !rf.test {
				if _, isLeader := rf.GetState(); !isLeader {
					DPrintf("%d, is not leader, don't send entries", rf.me)
					return
				}
				rf.Replicate()
				timer.Reset(AppendEntriesTimeout)
			}

		}
	}
}

func (rf *Raft) Get_Id() int {
	return rf.me
}

func (rf *Raft) Get_Term() int {
	return rf.currentTerm
}

func (rf *Raft) Get_Log() []LogEntry {
	return rf.logs
}

func (rf *Raft) Get_Role() string {
	switch rf.role {
	case Leader:
		return "L"
	case Follower:
		return "F"
	case Candidate:
		return "C"
	}
	return ""
}

func (rf *Raft) GetAllLog() []string {
	var allLog []string
	//allLog = make([]string, 0)
	for _, v := range rf.logs {
		if v.Command != nil {
			allLog = append(allLog, v.Command.(string))
		}

	}
	return allLog
}

// electiontimer 到时 会触发的函数， 进行选举
func (rf *Raft) StartElection() {
	rf.lock("startElection1")
	DPrintf("%d, startElection1", rf.me)
	rf.resetElectionTimer() // 选举开始 会重置 计时器
	if rf.role == Leader {  // 若本身就为leader 则不变化仍为leader
		DPrintf("%d, is leader", rf.me)
		rf.unLock("startElection1")
		return
	}
	rf.changeRole(Candidate) // 若原来为follower 则变为 candidate
	rf.unLock("startElection1")
	// Follower, Candidate -> Canditate

	rf.lock("startElection2") // 进行requestvote 的参数准备
	DPrintf("%d, startElection2", rf.me)
	LastTerm, lastIndex := rf.getLastLogTermIndex()
	args := RequestVoteArgs{
		Term:         rf.currentTerm,
		CandidateID:  rf.me,
		LastLogIndex: lastIndex,
		LastLogTerm:  LastTerm,
		From:         rf.me,
	}
	rf.unLock("startElection2")

	// voteCount := 1 //make sure votes send to all peers
	// voteForMe := 1 //get votes number

	for i := 0; i < len(rf.peers); i++ {
		if i == rf.me {
			continue
		}
		args.To = i
		// change go fund to func ,can not
		// because channel wait
		go func(index int, args RequestVoteArgs) { //
			reply := RequestVoteReply{}
			//may have problems
			ok := rf.sendRequestVote(index, &args, &reply)
			//time.Sleep(5 * time.Millisecond)
			if ok { // send success
				// if reply.Term != rf.currentTerm {
				// 	panic("reply term is not same as the sender")
				// }
				rf.handleVoteResult(reply)
			}
		}(i, args)
	}
}

//随机 生成election 时间
func randElectionTimeout() time.Duration {
	r, err := rand.Int(rand.Reader, big.NewInt(BigInt))

	if err != nil {
		DPrintf("election time out rand wrong, err : %v", err)
	}
	res := ElectionTimeout + time.Duration(r.Int64()*100)%ElectionTimeout
	//DPrintf("rand election timeout : %v", res)
	return res
}

//
// the service or tester wants to create a Raft server. the ports
// of all the Raft servers (including this one) are in peers[]. this
// server's port is peers[me]. all the servers' peers[] arrays
// have the same order. persister is a place for this server to
// save its persistent state, and also initially holds the most
// recent saved state, if any. applyCh is a channel on which the
// tester or service expects Raft to send ApplyMsg messages.
// Make() must return quickly, so it should start goroutines
// for any long-running work.
//
func Make(peers []*labrpc.ClientEnd, me int,
	persister *Persister, applyCh chan ApplyMsg, test bool) *Raft {
	rf := &Raft{}
	rf.peers = peers
	rf.persister = persister
	rf.me = me
	rf.applyCh = applyCh
	rf.test = test
	//DPrintf("%d make", rf.me)
	// Your initialization code here (2A, 2B, 2C).

	rf.role = Follower
	rf.votedFor = -1 // -1 for null
	// paper say log starts from 1, we use array begins from 0
	rf.currentTerm = 0
	rf.commitIndex = 0

	rf.lastApplied = 0

	rf.logs = make([]LogEntry, 1)
	rf.elecitonTimer = time.NewTimer(randElectionTimeout())

	rf.stopCh = make(chan struct{})

	// initialize from state persisted before a crash
	rf.readPersist(persister.ReadRaftState())

	//sleep for a while
	go func() {
		for {
			select {
			case <-rf.stopCh: // stop
				return
			case <-rf.elecitonTimer.C:
				DPrintf("%d, election timeout", rf.me)
				if !rf.test {
					rf.StartElection()
				}

			}
		}
	}()

	return rf
}
