#!/bin/bash
# Clean rebuild of one token (kit build left in place), then its axioms check.
export PATH=$HOME/.elan/bin:$PATH
t=$1; L=/home/user/logs/verify1; mkdir -p $L; rm -f $L/$t.*
echo $$ > $L/$t.pid
K=/home/user/token-kit
rm -rf $K/tokens/$t/.lake/build
T0=$(date +%s)
if [ "$t" = uni ]; then export LEAN_NUM_THREADS=2; fi  # 8 workers run out of memory on UNI
( cd $K/tokens/$t && lake build > $L/$t.log 2>&1; echo "EXIT=$?" >> $L/$t.log )
R=$(ls -d $K/tokens/$t/*Verify | head -1)
bash $K/scripts/check_axioms.sh $L/$t.log $R/Test/Axioms.lean > $L/$t.axioms 2>&1; echo "AXRC=$?" >> $L/$t.axioms
echo "DONE $(( $(date +%s) - T0 ))s" > $L/$t.done
