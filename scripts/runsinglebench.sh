#!/bin/bash

POSITIONAL_ARGS=()
SKIP_N_TIMES=0
RUN_N_TIMES=1

while [[ $# -gt 0 ]]; do
    case $1 in
    -t | --term)
        TERM_COUNT=YES
        shift
        ;;
    -s | --skip)
        SKIP_N_TIMES=$2
        if [[ $SKIP_N_TIMES =~ ^(0|[1-9][0-9]*)$ ]]; then
            echo "Will skip $SKIP_N_TIMES"
        else
            echo "Bad argument to -s, expect a number, but got $SKIP_N_TIMES"
            exit 1
        fi
        shift
        shift
        ;;
    -n | --ntimes)
        RUN_N_TIMES=$2
        if [[ $RUN_N_TIMES =~ ^[1-9][0-9]*$ ]]; then
            echo "Will run $RUN_N_TIMES and calculate the average"
        else
            echo "Bad argument to -n, expect a number, but got $RUN_N_TIMES"
            exit 1
        fi
        shift
        shift
        ;;
    -* | --*)
        echo "Unknown option $1"
        exit 1
        ;;
    *)
        POSITIONAL_ARGS+=("$1")
        shift
        ;;
    esac
done

set -- "${POSITIONAL_ARGS[@]}" # restore positional parameters

PARENT_PATH=$(
    cd "$(dirname "${BASH_SOURCE[0]}")"
    pwd -P
)
BASE_PATH="$PARENT_PATH/.."
cd "$BASE_PATH" 

if [[ $TERM_COUNT == YES ]]; then
    PROJECT=$1
    echo "COUNTING TERM ON ${PROJECT}"
    TMPFILE=$(mktemp /tmp/${PROJECT}.XXXX) || exit 1
    GRISETTE_SOLVER_OUTPUT=$TMPFILE PATH="$BASE_PATH/scripts/solverwrappers:$PATH" stack run $PROJECT >/dev/null 2>/dev/null
    TERM_NUM=$(grep -e "\(declare-fun\|define-fun\)" $TMPFILE | wc -l)
    echo "Term count $TERM_NUM"
else
    PROJECT=$1
    echo "RUNNING ${PROJECT}"
    MONO_TIME_AVG=0.0
    CPU_TIME_AVG=0.0
    LOWERING_TIME_AVG=0.0
    LOWERING_DETECTED_NUM=0
    for ((i=1;i<=SKIP_N_TIMES;i++)); do
        PATH="$BASE_PATH/scripts/solvers:$PATH" stack run $PROJECT >/dev/null 2>/dev/null || exit 1
    done
    for ((i=1;i<=RUN_N_TIMES;i++)); do
        RESULT=$(PATH="$BASE_PATH/scripts/solvers:$PATH" stack run $PROJECT) || exit 1
        MONO_TIME=$(echo "${RESULT}" | sed -nE 's/.*Overall -- Mono clock: ([[:digit:]]+\.?[[:digit:]]*) s.*/\1/p')
        CPU_TIME=$(echo "${RESULT}" | sed -nE 's/.*Overall -- CPU clock: ([[:digit:]]+\.?[[:digit:]]*) s.*/\1/p')
        MONO_TIME_AVG=$(echo "$MONO_TIME_AVG + $MONO_TIME" | bc)
        CPU_TIME_AVG=$(echo "$CPU_TIME_AVG + $CPU_TIME" | bc)

        LOWERING_TIME=$(echo "${RESULT}" | sed -nE 's/.*Lowering\/Solving -- CPU clock: ([[:digit:]]+\.?[[:digit:]]*) s.*/\1/p' | awk '{total += $1} END { print total }')
        if [ -n "$LOWERING_TIME" ]; then
            LOWERING_DETECTED_NUM=$(echo "$LOWERING_DETECTED_NUM + 1" | bc)
            LOWERING_TIME_AVG=$(echo "$LOWERING_TIME + $LOWERING_TIME_AVG" | bc)
        fi
    done
    MONO_TIME_AVG=$(echo "$MONO_TIME_AVG / $RUN_N_TIMES" | bc -l)
    CPU_TIME_AVG=$(echo "$CPU_TIME_AVG / $RUN_N_TIMES" | bc -l)
    SOLVING_TIME_AVG=$(echo "$MONO_TIME_AVG - $CPU_TIME_AVG" | bc -l)
    echo "Overall mono time $MONO_TIME_AVG"
    echo "Overall CPU time $CPU_TIME_AVG"
    echo "Overall solving time $SOLVING_TIME_AVG"
    if [ "$RUN_N_TIMES" = "$LOWERING_DETECTED_NUM" ]; then
        LOWERING_TIME_AVG=$(echo "$LOWERING_TIME_AVG / $RUN_N_TIMES" | bc -l)
        EVALUATION_TIME_AVG=$(echo "$CPU_TIME_AVG - $LOWERING_TIME_AVG" | bc -l)
        echo "Overall lowering time $LOWERING_TIME_AVG"
        echo "Overall pure sym evalution time $EVALUATION_TIME_AVG"
    elif [ ! "$LOWERING_DETECTED_NUM" = "0" ]; then
        echo "Bad lowering time detected num"
    fi
fi
