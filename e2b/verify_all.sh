#!/bin/bash
# Clean rebuild of the shared kit and all 15 tokens on the box, then the axioms check per token.
# UNI takes about 40 minutes, ONDO about 25; the other 13 take a few minutes each.
TOKENS="shib qnt bnb weth pepe wbt usdd dai usde ena sky link wbtc uni ondo"
# ONDO: the five biggest path modules peak near 3.5 GB each, so they are built alone first.
ONDO_SEQ="OndoVerify.Ondo.Gen.PGetVestedBalance OndoVerify.Ondo.Gen.PGetFreedBalance OndoVerify.Ondo.Gen.PVest0 OndoVerify.Ondo.Gen.PVest1 OndoVerify.Ondo.Gen.PVest2"
export PATH=$HOME/.elan/bin:$PATH
L=/home/user/logs/verify; mkdir -p $L; rm -f $L/*
echo $$ > $L/pid
K=/home/user/token-kit
rm -rf $K/.lake/build; for t in $TOKENS; do rm -rf $K/tokens/$t/.lake/build; done
T0=$(date +%s)
( cd $K && lake build > $L/kit.log 2>&1; echo "EXIT=$?" >> $L/kit.log )
for t in $TOKENS; do
  # UNI's big generated files need about 3 GB each: 8 workers run out of memory on an 8 GB box.
  if [ "$t" = uni ]; then export LEAN_NUM_THREADS=2; elif [ "$t" = ondo ]; then export LEAN_NUM_THREADS=3; else unset LEAN_NUM_THREADS; fi
  : > $L/$t.log
  if [ "$t" = ondo ]; then for m in $ONDO_SEQ; do ( cd $K/tokens/$t && lake build $m >> $L/$t.log 2>&1 ) || true; done; fi
  ( cd $K/tokens/$t && lake build >> $L/$t.log 2>&1; echo "EXIT=$?" >> $L/$t.log )
  R=$(ls -d $K/tokens/$t/*Verify | head -1)
  bash $K/scripts/check_axioms.sh $L/$t.log $R/Test/Axioms.lean > $L/$t.axioms 2>&1; echo "AXRC=$?" >> $L/$t.axioms
done
echo "ALLDONE $(( $(date +%s) - T0 ))s" > $L/done
