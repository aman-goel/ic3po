#!/bin/bash

SEED="$1"
shift
timeMax="$1"
shift
suite="$1"
shift
benchmark="$1"
shift
args="$@"

#memMax="8000000"

outPrefix="output/seed$SEED"
#rm -rf $outPrefix
mkdir -p $outPrefix

BMPATH="ivybench"
TOOL="ic3po"
FAILLOG="fail-seed$SEED.log"

ARGMIN="2"
ARGRANDOM="0"
GLOBAL_ARGS="--min $ARGMIN --seed $SEED -r $ARGRANDOM"

COUNT=0

rm -f $FAILLOG

find_key() {
	result=$(awk -v key="$2" '{
				for(i=1;i<=NF;i++)        # process every word
					if($i==key)      # if word is sample
						print $(i+1)      # print the next
				}' $1)
	echo "$result"
}
find_after_match() {
	result=$(awk -v key="$2" 'x==1 {print $1} /key/ {x=1}' $1)
	echo "$result"
}
count_key() {
	result=$(awk -v key="$2" '/^key/{a++}END{print a}' $1)
	echo "$result"
}
run() {
	COUNT=$((COUNT+1))
	suite="$1"
	benchmark="$2"
	args="$3"
	echo "-----------------------------------------------------"
	echo "[Test $COUNT] Running $TOOL on $benchmark in suite $suite"
	echo "args $args"

	OUT_PATH="$outPrefix/${suite}_$benchmark"
	rm -rf $OUT_PATH
	mkdir $OUT_PATH
	cp $BMPATH/$suite/vmt/${benchmark}.vmt $OUT_PATH
	
	fname="$OUT_PATH/${benchmark}.vmt"
	logFile="$OUT_PATH/log.txt"
	statFile="$OUT_PATH/stats.txt"
	
	echo -e "tool:\t$TOOL" > $statFile
	echo -e "suite:\t$suite" >> $statFile
	echo -e "benchmark:\t$suite-$benchmark" >> $statFile
	echo -e "seed:\t$SEED" >> $statFile
	echo -e "timeout:\t$timeMax" >> $statFile
#	echo -e "memout:\t$memMax" >> $statFile
	
	cmd="timeout $timeMax python ic3po.py -o $OUT_PATH -n $benchmark $args $GLOBAL_ARGS $fname"
	echo -e "$cmd"
	start=$(date +%s.%N)
	$cmd > $logFile
	tool_exit=$?
	end=$(date +%s.%N)
	tool_runtime=$(bc <<< "scale = 3; $end - $start")
	
	echo -e "time:\t$tool_runtime" >> $statFile
	echo -e "time:\t$tool_runtime"
	echo -e "exit-status:\t$tool_exit" >> $statFile
	
	result="failure"
	if [[ "$tool_exit" -eq 0 ]]
	then
		sF="$OUT_PATH/$benchmark/$benchmark.results"
		val=$(find_key $sF "memory-mb:")
		echo -e "memory-mb:\t$val" >> $statFile
		val=$(find_key $sF "sz-invariant:")
		if [[ $val =~ ^[0-9]+$ ]]; then
			result="success"
		else
			echo -e "(seed: $SEED, timeout: $timeMax) $suite-$benchmark" >> $FAILLOG
		fi
		echo -e "status:\t$result" >> $statFile
		echo -e "sz-invariant:\t$val" >> $statFile
		echo -e "sz-invariant:\t$val"
		val=$(find_key $sF "scalls:")
		echo -e "scalls:\t$val" >> $statFile
		echo -e "scalls:\t$val"
		val=$(find_key $sF "scalls-finite:")
		echo -e "scalls-finite:\t$val" >> $statFile
		val=$(find_key $sF "scalls-infinite:")
		echo -e "scalls-infinite:\t$val" >> $statFile
		val=$(find_key $sF "scalls-finite-full:")
		echo -e "scalls-finite-full:\t$val" >> $statFile
		val=$(find_key $sF "sz-invariant-forall:")
		echo -e "sz-invariant-forall:\t$val" >> $statFile
		val=$(find_key $sF "sz-invariant-exists:")
		echo -e "sz-invariant-exists:\t$val" >> $statFile
		val=$(find_key $sF "sz-invariant-atoms:")
		echo -e "sz-invariant-atoms:\t$val" >> $statFile
		val=$(find_key $sF "cti:")
		echo -e "cti:\t$val" >> $statFile
		val=$(find_key $sF "finite-size-init:")
		echo -e "finite-size-init:\t$val" >> $statFile
		val=$(find_key $sF "finite-size-final:")
		echo -e "finite-size-final:\t$val" >> $statFile
	else
		echo -e "(seed: $SEED, timeout: $timeMax) $suite-$benchmark" >> $FAILLOG
		echo -e "memory-mb:\t-1" >> $statFile
		echo -e "status:\t$result" >> $statFile
		echo -e "sz-invariant:\t-1" >> $statFile
		echo -e "scalls:\t-1" >> $statFile
		echo -e "scalls-finite:\t-1" >> $statFile
		echo -e "scalls-infinite:\t-1" >> $statFile
		echo -e "scalls-finite-full:\t-1" >> $statFile
		echo -e "sz-invariant-forall:\t-1" >> $statFile
		echo -e "sz-invariant-exists:\t-1" >> $statFile
		echo -e "sz-invariant-atoms:\t-1" >> $statFile
		echo -e "cti:\t-1" >> $statFile
		echo -e "finite-size-init:\t-1" >> $statFile
		echo -e "finite-size-final:\t-1" >> $statFile
	fi
	
	echo -e "$benchmark done!"
	echo ''
}

run $suite $benchmark "$args"

exit
