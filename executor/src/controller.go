package main

import (
	"bufio"
	"fmt"
	"io"
	"os"
	"strconv"
	"strings"
)

// var act_dict map[string]int

type Controller struct {
	traces     []Trace
	trace_dict map[string]int
	cfg        *config
}

var Trace_type = [...]string{
	"TRACE_NIL",
	"TRACE_INIT_SERVER",
	"TRACE_ELECTION_TIMEOUT",
	"TRACE_HEARTBEAT",
	"TRACE_RESTART",
	"TRACE_DROP_MSG",
	"TRACE_DUPLICATE_MSG",
	"TRACE_NETWORK_PARTITION",
	"TRACE_NETWORK_RECOVER",
	"TRACE_SEND_REQUESTVOTE",   // election send
	"TRACE_SEND_APPENDENTRIES", // heartbeat send
	"TRACE_HANDLE_REQUESTVOTE",
	"TRACE_HANDLE_REQUESTVOTE_RESPONSE",
	"TRACE_HANDLE_APPENDENTRIES",
	"TRACE_HANDLE_APPENDENTRIES_RESPONSE",
	"TRACE_CLIENT_OPERATION",
}

func (controller *Controller) init() {
	controller.trace_dict = make(map[string]int)
	for k, v := range Trace_type {
		controller.trace_dict[v] = k
	}
}

func (controller *Controller) Trace_reader(filename string) {
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
			case 0: // type
				{
					if value[0] != 'T' {
						panic("token type not right")
					}

					_type, ok := controller.trace_dict[value]
					if ok {
						trace.Type = _type
					} else {
						panic("token type not right")
					}
				}
			case 1: //state
				{
					trace.loadState(value)
				}
			case 2: // server
				{
					if value != "None" {
						_server, err := strconv.Atoi(value)
						if err == nil {
							trace.Server = _server
						} else {
							panic("token server not right")
						}
					} else {
						trace.Server = -1
					}

				}
			case 3: // peer
				{
					if value != "None" {
						_peer, err := strconv.Atoi(value)
						if err == nil {
							trace.Server = _peer
						} else {
							panic("token peer not right")
						}
					} else {
						trace.Peer = -1
					}
				}
			}
		}
		trace.show()
		controller.traces = append(controller.traces, trace)
	}
}

func (controller *Controller) Trace_executor() {
	for _, trace := range controller.traces {
		switch trace.Type {
		case TRACE_NIL:
			{
				//do nothing
			}
		case TRACE_INIT_SERVER:
			{
				controller.cfg = Make_config(trace.Server, false, false)
			}
		case TRACE_ELECTION_TIMEOUT:
			{
				controller.cfg.rafts[trace.Server].StartElection() // start election, become leader, and send Call
			}
		case TRACE_HEARTBEAT:
			{
				controller.cfg.appendAll(trace.Server)
			}
		case TRACE_HANDLE_REQUESTVOTE:
			{
				controller.cfg.net.Handle(trace.MsgSeq)
			}
		case TRACE_HANDLE_APPENDENTRIES:
			{
				controller.cfg.net.Handle(trace.MsgSeq)
			}
		case TRACE_HANDLE_APPENDENTRIES_RESPONSE:
			{
				controller.cfg.net.Handleresponse(trace.MsgSeq)
			}
		case TRACE_HANDLE_REQUESTVOTE_RESPONSE:
			{
				controller.cfg.net.Handleresponse(trace.MsgSeq)
			}
		}
	}
}
