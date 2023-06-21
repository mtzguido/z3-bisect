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

# Try to disable optimizations for a faster build. It's likely
# that building Z3 takes longer than actually running the test.
sed -i 's/-O3/-O0/' build/config.mk || true

if ! make -C build -j$(nproc) &>>BUILDLOG; then
	exit 125
fi
popd

./test.sh ${FILE}
