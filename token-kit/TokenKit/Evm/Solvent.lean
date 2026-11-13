import TokenKit.Evm.Safe
import TokenKit.Evm.Call

/-!
# The sum of the balances of a token against the ether that its contract holds

For a token that keeps `balances[a]` in slot `mapSlot a b` and is backed by the ether balance of
its contract (a wrapped ether token):

- `Solvent b C S`: in the state `S`, the sum of the balance words of the 2^160 addresses of the
  contract `C` (`sumBal`, Evm/Supply.lean) is at most the ether balance of `C`.
- `Backed b v C S`: the same with `v` wei to spare: the sum plus `v` is at most the ether balance.
  It is the form at the start of the frame of a message that carries `v` wei: the message layer
  has already credited `v` to `C`, and the code has not yet counted it.
- how storage reads and writes and account reads change the two sides.
- `add_toNat`: an addition that is not checked, as an integer modulo 2^256.
- `sub_fact_lt`: after `require(a >= v)` as compiled (three ISZERO over LT), the difference does
  not wrap.
- `solvent_of_ro`: a run that only reads keeps `Solvent`.

The base slot `b` is a parameter: nothing here is about one token.
-/

namespace TokenKit.Supply

open UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- The sum of the balances is at most the ether of the contract. -/
def Solvent (b : U256) (C : Address) (S : State.TransactionState) : Prop :=
  sumBal b C S ≤ ((etherOf S C).toNat : Int)

/-- The sum of the balances plus `v` is at most the ether of the contract. -/
def Backed (b v : U256) (C : Address) (S : State.TransactionState) : Prop :=
  sumBal b C S + (v.toNat : Int) ≤ ((etherOf S C).toNat : Int)

variable {b v : U256} {C : Address} {S S' : State.TransactionState}

theorem Backed.solvent (h : Backed b v C S) : Solvent b C S := by
  unfold Backed at h
  unfold Solvent
  omega

theorem Solvent.backed_zero (h : Solvent b C S) : Backed b 0 C S := by
  unfold Solvent at h
  unfold Backed
  simpa using h

/-- The sum reads the storage words of `C` only. -/
theorem sumBal_congr (h : ∀ n, storageAt S' C n = storageAt S C n) :
    sumBal b C S' = sumBal b C S := by
  unfold sumBal
  exact sumTo_congr _ (fun i _ => by simp only [bal, h])

/-- A recorded account read changes no storage word. -/
theorem sumBal_recordAccountRead (x : Address) :
    sumBal b C (S.recordAccountRead x) = sumBal b C S :=
  sumBal_congr (fun _ => rfl)

/-- `Solvent` reads the storage words of `C` and its ether only. -/
theorem solvent_congr (h : ∀ n, storageAt S' C n = storageAt S C n)
    (he : (etherOf S C).toNat ≤ (etherOf S' C).toNat) (hs : Solvent b C S) : Solvent b C S' := by
  unfold Solvent at hs ⊢
  rw [sumBal_congr h]
  omega

/-- An addition that is not checked, as an integer modulo 2^256. -/
theorem add_toNat (a v : U256) : (add a v).toNat = (a.toNat + v.toNat) % 2 ^ 256 := by
  simp only [add, BitVec.toNat_add]

/-- After `require(a >= v)` as compiled, the difference does not wrap. -/
theorem sub_fact_lt {a v : U256} (h : isZero (isZero (isZero (lessThan a v))) ≠ 0) :
    ((sub a v).toNat : Int) = a.toNat - v.toNat := by
  have hle := le_of_cond_lt h
  have ha := a.isLt
  have hv := v.isLt
  have e : (sub a v).toNat = a.toNat - v.toNat := by
    simp only [sub, BitVec.toNat_sub]
    omega
  omega

/-- A run that only reads keeps `Solvent`. -/
theorem solvent_of_ro {ss ss' : Substate} (h : Ro C S ss S' ss') (hs : Solvent b C S) :
    Solvent b C S' :=
  solvent_congr (fun n => h.storage C n) (by unfold etherOf; rw [h.accounts]; exact Nat.le_refl _)
    hs

end TokenKit.Supply
