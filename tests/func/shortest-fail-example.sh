#!/bin/bash
# example how to find a good SEED for a FAIL with a short path.
# here max 1000 lines of debug output, instead of 10000s.
# e.g. a memory leak, without the need to debug through too many steps.

trap "echo best SEED=$BEST; exit 1;" SIGINT

l=10000
while [ $l -gt 1000 ]
do
    SEED=$((SEED + 1))
    make SEED=$SEED DEBUG=1 SANITIZE=1 tests/func/test_unordered_set && \
        tests/func/test_unordered_set >xx 2>&1
    if [ $? -gt 0 ]
    then
        l=$(wc -l <xx)
        echo "$l" lines with FAIL
        if [ -z "$BEST" ] || [ $SEED -lt $BEST ]
        then
            BEST=$SEED; echo best SEED=$BEST
        fi
    fi
done
