#!/bin/bash
# set -e

SEED="$1"
shift
timeMax="$1"
shift
args=$@

echo -e "===================== (seed: $SEED, timeout: $timeMax) ======================="
pushd .
./.travis/ic3po_bm.sh $SEED $timeMax $args
python3 .travis/compile_results.py --seed $SEED --tool ic3po
popd

csvFile="xtras/ic3po-seed$SEED.csv"
table=$(column -t $csvFile)
echo -e "=================== RESULTS (seed$SEED) ================="
echo -e "$table"

resultSuccess=$(echo -e "$table" | grep -w "success" | wc -l)
resultFailure=$(echo -e "$table" | grep -w "failure" | wc -l)
echo -e "$resultSuccess tests passed, $resultFailure tests failed."

if [ "${resultFailure}" == "0" ]; then
	echo -e "\nPASS"
    exit 0
else
	echo -e "=================== FAILURES (seed$SEED) ================="
	FAILLOG="xtras/fail-seed$SEED.log"
	fail=$(column -t $FAILLOG)
	echo -e "$fail"
	echo -e "$fail" >> xtras/fail.log
	
	echo -e "\nFAIL"
    exit 1
fi
