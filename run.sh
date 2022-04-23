#!/bin/bash

# script dir
DIR=$(realpath $(dirname ${BASH_SOURCE[0]}))

# default config file
DEFAULT_CFG_FILE="${DIR}/experiments/simulation.ini"

# default tla file
TLA_FILE="${DIR}/tla/new-raft.tla"

# default out file 
TLA_FILE="${DIR}/tla/simulation"

TLCWRAPPER_DIR=$(realpath ${DIR}/tlc-cmd)
TLC_JAR="${TLCWRAPPER_DIR}/tla2tools.jar"
TLCWRAPPER_PY="${TLCWRAPPER_DIR}/tlcwrapper.py"

# set_output_dir

function set_output_dir() {
    OUTPUT_DIR=${DIR}/build/batch/$(date +"%F_%H-%M-%S")
    mkdir -p ${OUTPUT_DIR}
    OUTPUT_DIR=$(realpath ${OUTPUT_DIR})
    cp $(dirname ${TLA_FILE})/*.tla ${OUTPUT_DIR}
    TLA_FILE=${OUTPUT_DIR}/$(basename ${TLA_FILE})
    # MC_OUT_FILE=${MC_OUT_FILE:-MC.out}
}

function tlc_handle() {
    rm -r tla/simulation_2022*
    cat "$DEFAULT_CFG_FILE" | python3 "$TLCWRAPPER_PY"
    mv MC_summary_* ${OUTPUT_DIR}
    cnt=1
    mkdir ${OUTPUT_DIR}/traces
    find tla -name trace_* | while read trace_file; do
        python3 scripts/trace_converter.py -o ${OUTPUT_DIR}/traces/trace_${cnt}  ${trace_file}
        cnt=`expr ${cnt} + 1`
    done
    # python3 tlc-cmd/tlcwrapper.py $DEFAULT_CFG_FILE | 
    # python3 scripts/trace_converter.py -o 
}

function test() {
    cd executor/src
    make check CHECK_DIR=${OUTPUT_DIR}/traces
}

echo $DEFAULT_CFG_FILE

set_output_dir
tlc_handle
test


# python3 ../../tlcwrapper.py TPaxos-simulate.ini
# python3 trace_converter.py -o b ../tla/simulation_2022-03-27_16-15-05_1/trace_0_0