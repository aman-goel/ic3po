#!/bin/bash
# Make sure we exit if there is a failure
# set -e

RETURN=0
chmod +x .travis/travis_bm.sh
chmod +x .travis/ic3po_bm.sh

SEED=1
if [[ -z "${ENVSEED}" ]]; then
	SEED=1
else
	SEED=$ENVSEED
fi

TIMEOUT=300
if [[ -z "${ENVTIMEOUT}" ]]; then
	TIMEOUT=300
else
	TIMEOUT=$ENVTIMEOUT
fi

args=$@

pushd .
./.travis/travis_bm.sh $SEED $TIMEOUT $args
code=$?
if [ $code -eq 1 ]
then
	echo "Run for $1-$2 failed."
	RETURN=1
fi
popd

echo -e "====================== END ======================="

if [ "${RETURN}" == "0" ]; then
	echo -e "ALL PASSED"
    exit 0
else
	echo -e "SOME FAILED"
    exit 1
fi
