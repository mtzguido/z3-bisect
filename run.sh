#!/bin/bash

set -ue

if [ $# -ne 3 ]; then
	exec >&2
	echo "Usage: $0 <bad_ref> <good_ref> <file.smt2>"
	echo
	echo "Example: ./run.sh origin/master Z3-4.8.5 K256.smt2"
	echo
	echo "The bisection will try to find when checking file.smt2 goes from 'unsat' to 'unknown'"
	echo "You can bisect other behaviors by editing test.sh (IOU: options to do so without editing :^) )"
	echo ""
	echo "The script will do a fresh clone of Z3's repo. Feel free to clone from a local repo"
	echo "instead, but DO NOT put anything of value in there, as it will be constantly reset"
	echo
	echo "NOTE: installing ccache is probably a smart choice, it may make rebuilds much faster"
	exit 1;
fi

if ! [ -d z3 ]; then
	git clone https://github.com/Z3Prover/z3 z3
fi

BAD=$1
GOOD=$2
FILE=$3

git -C z3/ bisect reset
git -C z3/ clean -dffx
git -C z3/ bisect start ${BAD} ${GOOD}
git -C z3/ bisect run $(realpath build-and-test.sh) $(realpath ${FILE}) 2>&1 | tee BISECT.log
echo
echo
