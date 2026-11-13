import TokenKit.Evm.Prune

/-!
# Paths with named terms

A long path through code with many reads and writes (UNI: a transfer moves two balances and
writes two checkpoints) has a state whose term doubles with every write, because the value
written is itself a term over the state before. The generator (`scripts/gen_paths.py`, option
`paths.named_terms`) then gives a name (an `abbrev` of the path file) to every state, substate,
memory and large word of a path, and states the path with the names.

- `decidedN h [n1, n2]`: the tactic `decided h` of Evm/Prune.lean after the names `n1`, `n2` are
  unfolded in `h` and in the goal.

Nothing here is about one token.
-/

namespace TokenKit

open UsdtVerify
open EthLib.Execution.Evm

/-- `decided h` with the listed names unfolded first. -/
macro "decidedN " h:ident " [" ns:ident,* "]" : tactic => `(tactic| (
  have hdec := $h
  simp only [$[$ns:ident],*, storageAt_readSlot, isZero_eq_zero_iff, gt_swap, ne_eq,
    Classical.not_not] at hdec ⊢
  exact hdec))

end TokenKit
