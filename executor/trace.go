package main

import (
	"bufio"
	"flag"
	"fmt"
	"io"
	"os"
	"strconv"
	"strings"
)

var trace_file = flag.String("s", "stdin", "need string type")
var o = flag.String("o", "stdin", "need string type")

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

var countryCapitalMap map[string]string

type Raft_state struct {
	state     string // L/C/F for leader/candidate/follower
	term      int    // current term
	vote      int    // voted for
	commit    int    // commit index
	next_idx  []int  // next index
	match_idx []int  // match index
	log       []string
}

type Trace struct {
	_type   int
	_states []*Raft_state
	_server int
	_peer   int
	_msgSeq int
}

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
				n, _ = strconv.Atoi(values[i])
				tmpState.match_idx = append(tmpState.match_idx, n)
			}
		}
		for ; i < len(values); i++ {
			tmpState.log = append(tmpState.log, values[i])
		}
		trace._states = append(trace._states, &tmpState)
	}
}

// show Trace.state
func (state *Raft_state) show() {
	fmt.Printf("%+v\n", *state)
}

func (trace Trace) show() {
	for _, state := range trace._states {
		state.show()
	}
}

func trace_reader(filename string) {

	fi, err := os.Open(filename)
	if err != nil {
		fmt.Printf("Error: %s\n", err)
		return
	}
	defer fi.Close()

	br := bufio.NewReader(fi)
	for {
		line, _, c := br.ReadLine()
		if c == io.EOF {
			break
		}
		var trace Trace
		tokens := strings.Split(string(line), "\t")
		for key, value := range tokens {
			switch key {
			case 0:
				{
					if value[0] != 'T' {
						panic("token not right")
					}
				}
			case 1:
				{
					trace.loadState(value)
				}
			}
		}
		trace.show()
	}
}

func main() {
	flag.Parse()
	fmt.Println("-s:", *trace_file)
	trace_reader(*trace_file)
	fmt.Println("-o:", *o)
}
