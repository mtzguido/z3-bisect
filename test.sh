#!/bin/bash

set -eux

if [ $# -ne 1 ]; then
	echo usage
	exit 125
fi

FILE=$(realpath $1)

# Move to the directory where this script lives.
cd $(dirname $0)

N=1 # Number of different seeds

oom=0
unknown=0
unsat=0
sat=0
seed=0

for seed in $(seq 0 $((N-1))); do
	o=$(ramon ./z3/build/z3 smt.random_seed=$seed "${FILE}" 2>errout)
	if grep SIGKILL errout; then oom=$((oom+1));
	elif [ "$o" == "unknown" ]; then unknown=$((unknown+1));
	elif [ "$o" == "unsat" ]; then unsat=$((unsat+1));
	elif [ "$o" == "sat" ]; then sat=$((sat+1)); fi
done

if [ "$unknown" == "$N" ]; then echo BAD; exit 1; fi # bad
if [ "$unsat" == "$N" ]; then echo GOOD; exit 0; fi # good

echo INCONCLUSIVE $unknown $unsat

read

exit 125
