#!/bin/bash

# script dir
DIR=$(realpath $(dirname ${BASH_SOURCE[0]}))

# default config file
DEFAULT_CFG_FILE="${DIR}/../experiments/simulation.ini"

DEFAULT_CFG_FILE="${DIR}/../experiments/simulation.ini"

echo $DEFAULT_CFG_FILE

python3 ../tlc-cmd/tlcwrapper.py $DEFAULT_CFG_FILE


# python3 ../../tlcwrapper.py TPaxos-simulate.ini
# python3 trace_converter.py -o b ../tla/simulation_2022-03-27_16-15-05_1/trace_0_0