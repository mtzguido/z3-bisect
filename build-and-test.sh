#!/bin/bash

set -eux

if [ $# -ne 1 ]; then
	exit 125
fi

FILE=$1

cd $(dirname $0)

pushd z3
git clean -dffx &>/dev/null
./configure &>>BUILDLOG
if ! make -C build -j$(nproc) &>>BUILDLOG; then
	exit 125
fi
popd

./test.sh ${FILE}
