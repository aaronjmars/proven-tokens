import LinkVerify.Link.SeqLocal
import LinkVerify.Link.Sanity.Addr
import LinkVerify.Link.Sanity.TacLib

/-!
# A base case: a state that is good

Written by hand (not generated). Fix of audit 4, LINK-3. The sequence theorems (`inv_runL`,
`good_runL`) say that a good state stays good. They do not say that any state is good. Here one
is built.

`baseState`: one account, at `LINK_ADDRESS`, that holds the code of LINK; one storage word: the
balance slot of the address `Witness.CALLER1` holds `10^27`; every other slot is 0.

- `holdsCode_baseState`: the account holds the code of LINK (`Reenter.HoldsCode`).
- `inv_baseState`: the sum of the balances of the 2^160 addresses is `10^27` (`Inv`).
- `good_baseState`: so the state is good (`GoodLink`), and `inv_runL_baseState`: the sum is
  `10^27` after every sequence `RunL` from it.

Hypotheses that stay (both in the statements, NOT proved):
- `hu : Supply.UniqBal 1 Witness.CALLER1W`: no other address word has the balance slot of
  `CALLER1`. It is a fact about keccak for ONE address against all others (the `uniq` part of
  `Sep [CALLER1W]`); it cannot be computed (2^160 hashes). Without it another address would read
  the same word and the sum would be a multiple of `10^27`. So the base case is an implication,
  not a closed instance.
- `hH : hashOf CODE ≠ EMPTY_CODE_HASH`: the keccak hash of the code of LINK is not the hash of
  the empty code. It is true (Test/Hash.lean computes the hash, 77c633ba...8785, with `#eval`),
  but it is not proved in the kernel here.

Not covered: that the state of LINK on mainnet is good. The constructor (creation code) is not
in the proof, the history from the deployment in 2017 to Berlin is outside the fork range of
the theorems, and nothing here reads the chain. `Inv` at the first block the theorems apply to
is an assumption.
-/

set_option autoImplicit false

namespace LinkVerify.Sanity

open UsdtVerify
open TokenKit
open LinkVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.State.TransactionState
open EthLib.Execution.Evm

/-- `10^27` as a word. -/
abbrev TOTALW : U256 := 1000000000000000000000000000

/-- One account, at `LINK_ADDRESS`, with the code of LINK; the balance of `Witness.CALLER1` is
`10^27`, every other storage word is 0. -/
abbrev baseState : State.TransactionState :=
  codeState LINK_ADDRESS [(mapSlot Witness.CALLER1W 1, TOTALW)] LINK_ADDRESS CODE

/-- A sum of zeros is zero. -/
theorem sumTo_zero : ∀ n : Nat, Supply.sumTo (fun _ => (0 : Int)) n = 0
  | 0 => rfl
  | n + 1 => by rw [Supply.sumTo, sumTo_zero n]; rfl

/-- The code hash of the account of `codeState` that holds the code, when it is the contract. -/
theorem codeHash_codeState_self (C : Address) (kvs : List (U256 × U256)) (code : ByteArray) :
    ((codeState C kvs C code).getAccount C).codeHash = hashOf code := by
  have e : (codeState C kvs C code).getAccountOptional C = some ⟨1, 0, hashOf code⟩ :=
    getAccountOptional_setAccount_self (sState C kvs) C (some ⟨1, 0, hashOf code⟩)
  unfold State.TransactionState.getAccount
  rw [e] <;> rfl

/-- The account at `LINK_ADDRESS` of `baseState` holds the code of LINK. `hH`: the hash of the
code is not the hash of the empty code. -/
theorem holdsCode_baseState (hH : hashOf CODE ≠ EMPTY_CODE_HASH) :
    Reenter.HoldsCode LINK_ADDRESS CODE baseState :=
  ⟨getCode_codeState _ _ _ hH, by rw [codeHash_codeState_self]; exact hH,
    codeHash_codeState_self _ _ _⟩

/-- The sum of the balances of `baseState` is `10^27`. `hu`: no other address word has the
balance slot of `CALLER1` (keccak, not proved). -/
theorem inv_baseState (hu : Supply.UniqBal 1 Witness.CALLER1W) : Inv LINK_ADDRESS baseState := by
  have ha : Witness.CALLER1W.toNat < 2 ^ 160 := by decide
  have hfg : ∀ i : Nat, i < 2 ^ 160 → i ≠ Witness.CALLER1W.toNat →
      Supply.bal 1 LINK_ADDRESS baseState i = (fun _ => (0 : Int)) i := by
    intro i hi hne
    have hi' : i < 2 ^ 256 := Nat.lt_trans hi (by decide)
    have ht : (BitVec.ofNat 256 i).toNat = i := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hi'
    have hk : ¬ mapSlot Witness.CALLER1W 1 = mapSlot (BitVec.ofNat 256 i) 1 := by
      intro e
      have h1 := hu (BitVec.ofNat 256 i) (by rw [ht]; exact hi) e.symm
      exact hne (by rw [← ht, h1])
    show ((storageAt baseState LINK_ADDRESS (mapSlot (BitVec.ofNat 256 i) 1)).toNat : Int) = 0
    rw [storageAt_codeState, storageAt_sState_cons, if_neg hk, storageAt_sState_nil]
    rfl
  unfold Inv Supply.sumBal
  rw [Supply.sumTo_update (f := fun _ => (0 : Int)) (a := Witness.CALLER1W.toNat) (2 ^ 160) ha
    hfg, sumTo_zero]
  show (0 : Int) - 0 +
    ((storageAt baseState LINK_ADDRESS
      (mapSlot (BitVec.ofNat 256 Witness.CALLER1W.toNat) 1)).toNat : Int) = TOTAL
  rw [Supply.ofNat_toNat, storageAt_codeState, storageAt_sState_cons, if_pos rfl]
  decide

/-- A GOOD STATE EXISTS (under `hu` and `hH`): `baseState` holds the code of LINK at
`LINK_ADDRESS` and the sum of its balances is `10^27`. -/
theorem good_baseState (hH : hashOf CODE ≠ EMPTY_CODE_HASH)
    (hu : Supply.UniqBal 1 Witness.CALLER1W) : GoodLink LINK_ADDRESS baseState :=
  ⟨holdsCode_baseState hH, inv_baseState hu⟩

/-- The sequence theorem from the base state: after every finite sequence of clean top-level
messages and creations and of `Other` steps from `baseState`, the sum of the balances is
`10^27`. -/
theorem inv_runL_baseState (hH : hashOf CODE ≠ EMPTY_CODE_HASH)
    (hu : Supply.UniqBal 1 Witness.CALLER1W) {S' : State.TransactionState}
    (h : RunL LINK_ADDRESS baseState S') : Inv LINK_ADDRESS S' :=
  inv_runL h (holdsCode_baseState hH) (inv_baseState hu)

end LinkVerify.Sanity
