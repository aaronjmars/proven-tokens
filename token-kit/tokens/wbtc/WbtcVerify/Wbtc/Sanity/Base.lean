import WbtcVerify.Wbtc.SeqLocal
import WbtcVerify.Wbtc.Sanity.Addr
import WbtcVerify.Wbtc.Sanity.ReclaimLib

/-!
# A base case: a state that is good

Written by hand (not generated). Fix of audit 4, WBTC-2. The sequence theorems (`inv_runL`,
`good_runL`) say that a good state stays good. They did not say that any state is good. Here one
is built, with no hypothesis on the slots of keccak.

`emptyState`: one account, at `WBTC_ADDRESS`, that holds the code of WBTC; every storage word is
0 (no balance, `totalSupply_` = 0, no owner).

- `holdsCode_emptyState`: the account holds the code of WBTC (`Reenter.HoldsCode`).
- `inv_emptyState`: the sum of the balances of the 2^160 addresses is 0, the word of slot 1
  (`Inv`). No hypothesis.
- `good_emptyState`: so the state is good (`GoodWbtc`), and `inv_runL_emptyState`: `Inv` holds
  after every sequence `RunL` from it.

The hypothesis that stays (in the statements, NOT proved):
- `hH : hashOf CODE ≠ EMPTY_CODE_HASH`: the keccak hash of the code of WBTC is not the hash of
  the empty code. It is true (Test/Hash.lean computes the hash with `#eval`), but the kernel
  cannot compute the keccak of 4,582 bytes within the memory of the build box.

Not covered: this is the non-keccak part only. `Sep A` is proved for no list `A` (keccak facts
over 2^160 keys cannot be computed), so no theorem with a `Sep` or `CleanW` hypothesis has a
closed instance with a message that writes a balance. And nothing here says that the state of
WBTC on mainnet is good: the constructor (creation code) is not in the proof, and nothing reads
the chain.
-/

set_option autoImplicit false

namespace WbtcVerify.Sanity

open UsdtVerify
open TokenKit
open WbtcVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.State.TransactionState
open EthLib.Execution.Evm

/-- One account, at `WBTC_ADDRESS`, with the code of WBTC; every storage word is 0. -/
abbrev emptyState : State.TransactionState := codeState WBTC_ADDRESS [] WBTC_ADDRESS CODE

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

/-- The account at `WBTC_ADDRESS` of `emptyState` holds the code of WBTC. `hH`: the hash of the
code is not the hash of the empty code. -/
theorem holdsCode_emptyState (hH : hashOf CODE ≠ EMPTY_CODE_HASH) :
    Reenter.HoldsCode WBTC_ADDRESS CODE emptyState :=
  ⟨getCode_codeState _ _ _ hH, by rw [codeHash_codeState_self]; exact hH,
    codeHash_codeState_self _ _ _⟩

/-- The sum of the balances of `emptyState` is 0, the word of slot 1. No hypothesis. -/
theorem inv_emptyState : Inv WBTC_ADDRESS emptyState := by
  have hz : ∀ n : U256, storageAt emptyState WBTC_ADDRESS n = 0 := fun n => by
    rw [storageAt_codeState, storageAt_sState_nil]
  show Supply.sumBal 0 WBTC_ADDRESS emptyState -
    ((storageAt emptyState WBTC_ADDRESS 1).toNat : Int) = 0
  unfold Supply.sumBal
  rw [Supply.sumTo_congr (g := fun _ => (0 : Int)) (2 ^ 160) (fun i _ => by
    show ((storageAt emptyState WBTC_ADDRESS _).toNat : Int) = 0
    rw [hz]
    rfl), sumTo_zero, hz]
  rfl

/-- A GOOD STATE EXISTS (under `hH` only): `emptyState` holds the code of WBTC at `WBTC_ADDRESS`
and the sum of its balances is its `totalSupply_`. -/
theorem good_emptyState (hH : hashOf CODE ≠ EMPTY_CODE_HASH) :
    GoodWbtc WBTC_ADDRESS emptyState :=
  ⟨holdsCode_emptyState hH, inv_emptyState⟩

/-- The sequence theorem from the base state: after every finite sequence of clean top-level
messages and creations and of `Other` steps from `emptyState`, the sum of the balances is the
word of slot 1. -/
theorem inv_runL_emptyState (hH : hashOf CODE ≠ EMPTY_CODE_HASH)
    {S' : State.TransactionState} (h : RunL WBTC_ADDRESS emptyState S') :
    Inv WBTC_ADDRESS S' :=
  inv_runL h (holdsCode_emptyState hH) inv_emptyState

end WbtcVerify.Sanity
