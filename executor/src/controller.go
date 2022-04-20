package main

import (
	"bufio"
	"fmt"
	"io"
	"log"
	"os"
	"strconv"
	"strings"
	"time"
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

func (controller *Controller) Trace_reader(fi *os.File) {

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
							trace.Peer = _peer
						} else {
							panic("token peer not right")
						}
					} else {
						trace.Peer = -1
					}
				}
			case 4: //msgSeq
				{
					if value != "None" {
						trace.loadMsgData(value)
					} else {
						trace.MsgSeq = ""
					}
				}
			case 5:
				{
					if value != "None" {
						trace.Data = value
					}
				}
			}
		}
		//trace.show()
		controller.traces = append(controller.traces, trace)
	}
}

func (controller *Controller) show_states() {
	for _, v := range controller.cfg.rafts {
		fmt.Printf("id %d, role %s, term %d \n", v.Get_Id(), v.Get_Role(), v.Get_Term())
	}
	//msgs := controller.cfg.net.GetMsgs()
	//for k, v := range msgs {
	//	fmt.Printf("%d, %+v\n", k, v)
	//}
	//fmt.Printf("%+v", controller.cfg.net.GetMsgs())
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
				DPrintf("init, num of server: %d\n", trace.Server)
				controller.cfg = Make_config(trace.Server, false, false)
				time.Sleep(time.Millisecond * 10)
			}
		case TRACE_ELECTION_TIMEOUT:
			{
				DPrintf("election_timeout, server_number: %d, server_term %d\n", trace.Server, controller.cfg.rafts[trace.Server].Get_Term())
				controller.cfg.rafts[trace.Server].StartElection() // start election, become leader, and send Call
				time.Sleep(time.Millisecond * 10)
			}
		case TRACE_HEARTBEAT:
			{
				DPrintf("heart_beat, server_number: %d\n", trace.Server)
				controller.cfg.appendAll(trace.Server)
				time.Sleep(time.Millisecond * 10)
			}
		case TRACE_HANDLE_REQUESTVOTE, TRACE_HANDLE_APPENDENTRIES:
			{
				DPrintf("handle, msgs: %v\n", trace.MsgSeq)
				controller.cfg.net.Handle(trace.MsgSeq)
				time.Sleep(time.Millisecond * 10)

			}
		case TRACE_HANDLE_APPENDENTRIES_RESPONSE, TRACE_HANDLE_REQUESTVOTE_RESPONSE:
			{
				DPrintf("handleresponse, msgs: %v\n", trace.MsgSeq)
				controller.cfg.net.Handleresponse(trace.MsgSeq)
				time.Sleep(time.Millisecond * 10)
			}
		case TRACE_CLIENT_OPERATION:
			{
				DPrintf("clientOperation, data: %v, server_number: %d\n", trace.Data, trace.Server)
				controller.cfg.rafts[trace.Server].Start(trace.Data)
			}
		case TRACE_SEND_APPENDENTRIES, TRACE_SEND_REQUESTVOTE:
			{
				// do nothing
			}
		case TRACE_RESTART:
			{
				DPrintf("restart, server: %v\n", trace.Server)
				controller.cfg.start1(trace.Server, controller.cfg.applier)
				time.Sleep(time.Millisecond * 10)
			}

		}
		controller.stateCompare(trace)
	}

}

func (controller *Controller) stateCompare(trace Trace) {
	for k, v := range trace.States {
		term := controller.cfg.rafts[k].Get_Term()
		if term != v.term {
			log.Panicf("term not right, wrong server: %d\n", k)
		}
		state := controller.cfg.rafts[k].Get_Role()
		if state != v.state {
			log.Panicf("role not right, wrong server: %d\n", k)
		}
		traceLog := controller.cfg.rafts[k].GetAllLog()
		if len(traceLog) != len(v.log) {
			log.Panicf("log not right, wrong server: %d\n", k)
		} else {
			for k1, v1 := range traceLog {
				if v1 != v.log[k1] {
					log.Panicf("log not right, wrong server: %d, wrong log %v\n", k, v1)
				}
			}
		}
	}
}
