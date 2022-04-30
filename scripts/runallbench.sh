#!/bin/bash

SKIP_N_TIMES=0
RUN_N_TIMES=1

declare -A STACK_KEYS
STACK_KEYS[regex-nomemo]=regex-nomemo
STACK_KEYS[regex]=regex
STACK_KEYS[letpoly-nomemo]=bonsai-letpoly-nomemo
STACK_KEYS[nanoscala-nomemo]=bonsai-nanoscala-nomemo
STACK_KEYS[cosette-1]=cosette-optimized-merge
STACK_KEYS[letpoly]=bonsai-letpoly
STACK_KEYS[nanoscala]=bonsai-nanoscala
STACK_KEYS[cosette]=cosette
STACK_KEYS[fluidics]=fluidics
STACK_KEYS[ifcl]=ifcl
STACK_KEYS[ferrite]=ferrite
TO_RUN=()
RUN_ALL=NO

exists(){
  if [ "$2" != in ]; then
    echo "Incorrect usage."
    echo "Correct usage: exists {key} in {array}"
    return
  fi   
  eval '[ ${'$3'[$1]+muahaha} ]'  
}

while [[ $# -gt 0 ]]; do
    case $1 in
    -s | --skip)
        SKIP_N_TIMES=$2
        if [[ ! $SKIP_N_TIMES =~ ^(0|[1-9][0-9]*)$ ]]; then
            echo "Bad argument to -s, expect a number, but got $SKIP_N_TIMES"
            exit 1
        fi
        shift
        shift
        ;;
    -n | --ntimes)
        RUN_N_TIMES=$2
        if [[ ! $RUN_N_TIMES =~ ^[1-9][0-9]*$ ]]; then
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
    all)
        RUN_ALL=YES
        shift
        ;;
    *)
        if ! exists "$1" in STACK_KEYS; then
            echo "Unknown subject $1"
            echo "Supported subjects: all ${!STACK_KEYS[@]}"
            exit 1
        else
            TO_RUN+=("$1")
        fi
        shift
        ;;
    esac
done

set -- "${POSITIONAL_ARGS[@]}" # restore positional parameters

COLUMNS="subject,total,eval,solv,lower,pureeval,term"
PARENT_PATH=$(
    cd "$(dirname "${BASH_SOURCE[0]}")"
    pwd -P
)

if [[ "$RUN_ALL" = "YES" ]]; then
    TO_RUN=()
    for i in ${!STACK_KEYS[@]}; do
        TO_RUN+=("$i")
    done
fi

TO_RUN_NUM=${#TO_RUN[@]}

if [[ "$TO_RUN_NUM" = "0" ]]; then
    echo "Supported subjects: all ${!STACK_KEYS[@]}"
    exit 1
fi

echo $COLUMNS

for ((i=0;i<TO_RUN_NUM;i++)); do
    SUBJECT=${TO_RUN[$i]}
    STACK_KEY=${STACK_KEYS[$SUBJECT]}
    TERM_RESULT=$("$PARENT_PATH/runsinglebench.sh" -t $STACK_KEY 2>/dev/null)
    TERM_COUNT=$(echo "$TERM_RESULT" | sed -nE 's/.*Term count ([[:digit:]]+)$/\1/p')
    TIME_RESULT=$("$PARENT_PATH/runsinglebench.sh" -s ${SKIP_N_TIMES} -n ${RUN_N_TIMES} $STACK_KEY 2>/dev/null)
    TOTAL_TIME=$(echo "$TIME_RESULT" | sed -nE 's/.*Overall mono time ([[:digit:]]*\.?[[:digit:]]*)$/\1/p')
    EVAL_TIME=$(echo "$TIME_RESULT" | sed -nE 's/.*Overall CPU time ([[:digit:]]*\.?[[:digit:]]*)$/\1/p')
    SOLV_TIME=$(echo "$TIME_RESULT" | sed -nE 's/.*Overall solving time ([[:digit:]]*\.?[[:digit:]]*)$/\1/p')
    LOWER_TIME=$(echo "$TIME_RESULT" | sed -nE 's/.*Overall lowering time ([[:digit:]]*\.?[[:digit:]]*)$/\1/p')
    PUREEVAL_TIME=$(echo "$TIME_RESULT" | sed -nE 's/.*Overall pure sym evalution time ([[:digit:]]*\.?[[:digit:]]*)$/\1/p')
    echo "${SUBJECT},$TOTAL_TIME,$EVAL_TIME,$SOLV_TIME,$LOWER_TIME,$PUREEVAL_TIME,$TERM_COUNT"
done

