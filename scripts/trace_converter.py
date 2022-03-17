#!/usr/bin/python3

# usage: python3 trace_converter.py -h

from io import StringIO
from trace_reader import trace_reader, set_user_dict, set_kv_handler
from mc_log_converter import get_converted_string


def _kv_outside_handler(k, v):
    if k != 'messages':
        return k, v
    d = dict()
    for i in v:
        d[i['seq']] = i
    return k, d


_node_id_dict = {'s1': 0, 's2': 1, 's3': 2, 's4': 3, 's5': 4, 's6': 5, 's7': 6}


def _kv_inside_handler(k, v):

    def get_id(i):
        if type(i) == str and i in _node_id_dict:
            return _node_id_dict[i]
        return i
    return get_id(k), get_id(v)


def init_trace_reader():
    set_user_dict({'Nil': None})
    set_kv_handler(_kv_outside_handler, inside=False)
    set_kv_handler(_kv_inside_handler, inside=True)


def _pc_field(s, i, default_none=False):
    p = _pc(s)
    if len(p) <= i:
        if default_none:
            return None
        assert False
    return p[i]


def _action(s):
    p = _pc_field(s, 0)
    return _action_dict[p] if p in _action_dict else _action_dict[p.split(':')[0]]


def _partition(s):
    return ' '.join(map(lambda i: str(_node_id_dict[i]), s['scr']['partNodes']))


def _states(s):
    l = []
    for i in range(_n_server(s)):
        is_leader = s['state'][i] == 'Leader'
        role = s['state'][i][0]
        cur_term = s['currentTerm'][i]
        vote = s['votedFor'][i]
        vote = -1 if vote is None else vote
        commit_idx = s['commitIdx'][i]
        if is_leader:
            next_idx = ' '.join(str(j) for j in s['nextIdx'][i].values())
            match_idx = ' '.join(str(j) for j in s['matchIdx'][i].values())
        else:
            next_idx, match_idx = None, None
        last_idx = s['snapshotLastIdx'][i]
        last_term = s['snapshotLastTerm'][i]
        log = ' '.join('{}:{}'.format(j['term'], j['value'])
                       for j in s['log'][i])
        to_append = [role, cur_term, vote, commit_idx, next_idx, match_idx,
                     last_idx, last_term, log]
        l.append(j for j in to_append if j is not None)
    return ';'.join(' '.join(map(str, i)) for i in l)


def _pc(s): return s['scr']['pc']
def _nil(s): return None
def _server(s): return _node_id_dict[_pc_field(s, 1)]
def _state_n(s): return _pc_field(s, 1)
def _server_info(state, var_name): return state[var_name][_server(state)]
def _peer(s): return _node_id_dict[_pc_field(s, 2)]
def _msg_seq(s): return _pc_field(s, 3)
def _msg_response(s): return _pc_field(s, 4)
def _send_ok(s): return _pc_field(s, 4)
def _cont_file(s): return _pc_field(s, 4)
def _log(s): return _server_info(s, 'log')
def _n_server(s): return len(s['log'])
def _msg(s): return _server_info(s, 'messages')[_msg_seq(s)]
def _client_cmd(s): return _log(s)[-1]['value']


_action_dict = {
    'Continue':                    'TRACE_NIL',
    'Init':                        'TRACE_INIT_SERVER',
    'Timeout':                     'TRACE_ELECTION_TIMEOUT',
    'AppendEntriesAll':            'TRACE_HEARTBEAT',
    'Restart':                     'TRACE_RESTART',
    'FinishLoop':                  'TRACE_NIL',
    'DoLoop: AppendEntries':       'TRACE_SEND_APPENDENTRIES',
    'DoLoop: RequestVote':         'TRACE_SEND_REQUESTVOTE',
    'DoLoop: SendSnapshot':        'TRACE_SEND_SNAPSHOT',
    'HandleRequestVoteRequest':    'TRACE_HANDLE_REQUESTVOTE',
    'HandleRequestVoteResponse':   'TRACE_HANDLE_REQUESTVOTE_RESPONSE',
    'HandleAppendEntriesRequest':  'TRACE_HANDLE_APPENDENTRIES',
    'HandleAppendEntriesResponse': 'TRACE_HANDLE_APPENDENTRIES_RESPONSE',
    'HandleSnapshotRequest':       'TRACE_HANDLE_SNAPSHOT',
    'ExecSnapshot':                'TRACE_EXEC_SNAPSHOT',
    'ClientRequest':               'TRACE_CLIENT_OPERATION',
    'Drop':                        'TRACE_DROP_MSG',
    'Duplicate':                   'TRACE_DUPLICATE_MSG',
    'NetworkPartition':            'TRACE_NETWORK_PARTITION',
    'NetworkRecover':              'TRACE_NETWORK_RECOVER'
}

_callback_dict = {
    # FIELDS:                       type     states   server   peer   msg_seq   data
    'Continue':                    (_action, _states, _state_n, _nil, _nil,     _cont_file),
    'Init':                        (_action, _states, _n_server),
    'Timeout':                     (_action, _states, _server, ),
    'AppendEntriesAll':            (_action, _states, _server, ),
    'Restart':                     (_action, _states, _server, ),
    'FinishLoop':                  (_action, _states, ),
    'DoLoop':                      (_action, _states, _server, _peer, _msg_seq, _send_ok),
    'HandleRequestVoteRequest':    (_action, _states, _server, _peer, _msg_seq, _msg_response),
    'HandleRequestVoteResponse':   (_action, _states, _server, _peer, _msg_seq),
    'HandleAppendEntriesRequest':  (_action, _states, _server, _peer, _msg_seq, _msg_response),
    'HandleAppendEntriesResponse': (_action, _states, _server, _peer, _msg_seq, _msg_response),
    'HandleSnapshotRequest':       (_action, _states, _server, _peer, _msg_seq, _msg_response),
    'ExecSnapshot':                (_action, _states, _server, ),
    'ClientRequest':               (_action, _states, _server, _nil,  _nil,     _client_cmd),
    'Drop':                        (_action, _states, _nil,    _nil,  _msg_seq),
    'Duplicate':                   (_action, _states, _nil,    _nil,  _msg_seq, _msg_response),
    'NetworkPartition':            (_action, _states, _nil,    _nil,  _nil,     _partition),
    'NetworkRecover':              (_action, _states, )
}


def get_cont_string(file, state_n):
    if file.endswith('MC.out'):
        file = StringIO(''.join(get_converted_string(file)))
    return '\n'.join(get_state_string(state) for i, state in enumerate(trace_reader(file)) if i < state_n)


def get_state_string(state):
    name = _pc_field(state, 0).split(':')[0]
    if name == 'Continue':
        filename = _cont_file(state)
        state_n = _state_n(state)
        cont_string = get_cont_string(filename, state_n) + '\n'
    else:
        cont_string = ''
    if name not in _callback_dict:
        raise ValueError("Unhandled trace type: " + name)
    return cont_string + '\t'.join(
        map(str, [func(state) for func in _callback_dict[name]]))


def trace_generator(file):
    if file.endswith('MC.out'):
        file = StringIO(''.join(get_converted_string(file)))
    for state in trace_reader(file):
        yield get_state_string(state)


def trace_convert(in_filename, out_file):
    for string in trace_generator(in_filename):
        print(string, file=out_file)


init_trace_reader()

if __name__ == '__main__':
    import argparse
    import sys

    # arg parser
    parser = argparse.ArgumentParser(
        description="Read TLA traces and convert to controller readable format")
    parser.add_argument(dest='trace_file', action='store',
                        help='TLA trace file')
    parser.add_argument('-o', dest='out_file', action='store', required=False,
                        help="output file")
    args = parser.parse_args()

    if args.out_file:
        with open(args.out_file, 'w') as f:
            trace_convert(args.trace_file, f)
    else:
        trace_convert(args.trace_file, sys.stdout)
