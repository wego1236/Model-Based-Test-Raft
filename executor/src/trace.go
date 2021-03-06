package main

import (
	"fmt"
	"strconv"
	"strings"
)

const (
	TRACE_NIL = iota
	TRACE_INIT_SERVER
	TRACE_ELECTION_TIMEOUT
	TRACE_HEARTBEAT
	TRACE_RESTART
	TRACE_DROP_MSG
	TRACE_DUPLICATE_MSG
	TRACE_NETWORK_PARTITION
	TRACE_NETWORK_RECOVER
	TRACE_SEND_REQUESTVOTE   // election send
	TRACE_SEND_APPENDENTRIES // heartbeat send
	TRACE_HANDLE_REQUESTVOTE
	TRACE_HANDLE_REQUESTVOTE_RESPONSE
	TRACE_HANDLE_APPENDENTRIES
	TRACE_HANDLE_APPENDENTRIES_RESPONSE
	TRACE_CLIENT_OPERATION
)

// var countryCapitalMap map[string]string

type Raft_state struct {
	state     string // L/C/F for leader/candidate/follower
	term      int    // current term
	vote      int    // voted for
	commit    int    // commit index
	next_idx  []int  // next index
	match_idx []int  // match index
	log       []string
}

func (state *Raft_state) GetState() string {
	return state.state
}

func (state *Raft_state) GetTerm() int {
	return state.term
}

func (state *Raft_state) GetCommit() int {
	return state.commit
}

func (state *Raft_state) GetLog() []string {
	return state.log
}

//func (state *Raft_state) GetTerm() int{
//	return state.term
//}
//
//func (state *Raft_state) GetTerm() int{
//	return state.term
//}

type Trace struct {
	Type   int
	States []*Raft_state
	Server int
	Peer   int
	MsgSeq string
	Data   string
}

//func (trace *Trace) getStateRole{
//	return trace.States.
//}

// read token load Trace.state
func (trace *Trace) loadState(token string) {
	server_states := strings.Split(token, ";")
	n_server := len(server_states)
	for _, server_state := range server_states {
		values := strings.Split(server_state, " ")
		var tmpState Raft_state
		tmpState.state = values[0]
		tmpState.term, _ = strconv.Atoi(values[1])
		tmpState.vote, _ = strconv.Atoi(values[2])
		tmpState.commit, _ = strconv.Atoi(values[3])
		i := 3
		if tmpState.state == "L" {
			var n int
			for j := 1; j <= n_server; j++ {
				i++
				n, _ = strconv.Atoi(values[i])
				tmpState.next_idx = append(tmpState.next_idx, n)
			}
			for j := 1; j <= n_server; j++ {
				i++
				n, _ = strconv.Atoi(values[i])
				tmpState.match_idx = append(tmpState.match_idx, n)
			}
		}
		i++
		for ; i < len(values); i++ { // because last word is space , so
			if values[i] == "" || values[i] == " " {
				// fmt.Println("find wrong")
				continue
			}
			tmpState.log = append(tmpState.log, values[i])
			// fmt.Printf("%+v\n", tmpState.log)
		}
		trace.States = append(trace.States, &tmpState)
	}
}

func (trace *Trace) loadMsgData(token string) {
	//fmt.Printf("%v\n", token)
	msgData := strings.Split(token, " ")
	var hashInfo string
	if msgData[0] == "RequestVoteRequest" {
		hashInfo += "Raft.RequestVote"
	} else if msgData[0] == "RequestVoteResponse" {
		hashInfo += "Raft.RequestVoteResponse"
	} else if msgData[0] == "AppendEntriesRequest" {
		hashInfo += "Raft.AppendEntries"
	} else if msgData[0] == "AppendEntriesResponse" {
		hashInfo += "Raft.AppendEntriesResponse"
	}
	hashInfo += msgData[1]
	hashInfo += msgData[2]
	hashInfo += msgData[3]
	trace.MsgSeq = hashInfo
}

// show Trace.state
func (state *Raft_state) show() {
	fmt.Printf("%+v\n", *state)
}

func (trace *Trace) show() {
	fmt.Println("type", Trace_type[trace.Type], "server", trace.Server, "peer", trace.Peer)
	for _, state := range trace.States {
		state.show()
	}
	//fmt.Println("type", Trace_type[trace.Type])
}
