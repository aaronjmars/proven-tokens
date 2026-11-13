import LinkVerify.Link.Tac.Rules

/-!
# transferAndCall: the decoded arguments

The words that the entry block of `transferAndCall(address,uint256,bytes)` reads from the call
data, as terms of the call data, and the natural numbers of the offsets built from them.
-/

set_option autoImplicit false

namespace LinkVerify.Tac

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm

variable {fork : Fork}

/-- The recipient: the first argument, cut to 160 bits. -/
def tacTo (message : Message fork) : U256 :=
  bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
    (loadWord message.data 4 32)

/-- The amount: the second argument. -/
def tacValue (message : Message fork) : U256 := loadWord message.data 36 32

/-- The offset of the `bytes` argument inside the arguments: the third head word. -/
def tacOff (message : Message fork) : U256 := loadWord message.data 68 32

/-- The length of the `bytes` argument, as the contract reads it. -/
def tacLen (message : Message fork) : U256 :=
  loadWord message.data (add (4 : U256) (tacOff message)).toNat 32

/-- The bytes of the `bytes` argument (zero padded when the call data is short). -/
def tacData (message : Message fork) : ByteArray :=
  copied message.data (add (tacOff message) (36 : U256)).toNat (tacLen message).toNat

/-- The free memory pointer after the copy of a `bytes` argument of length `L`, as the contract
computes it: `96 + (32 * ((L + 31) / 32) + 32)`. -/
def tacFpw (L : U256) : U256 :=
  add (96 : U256) (add (mul (32 : U256) (div (add L (31 : U256)) (32 : U256))) (32 : U256))

/-- The free memory pointer as a number, for a length below `2 ^ 64`. -/
theorem tacFpw_toNat {L : U256} {N : Nat} (hL : L.toNat = N) (hN : N < 2 ^ 64) :
    (tacFpw L).toNat = (N + 31) / 32 * 32 + 128 := by
  have h31 : (add L (31 : U256)).toNat = N + 31 :=
    toNat_add' hL (by decide) (by omega)
  have hd : (div (add L (31 : U256)) (32 : U256)).toNat = (N + 31) / 32 := by
    unfold div
    rw [if_neg (by decide), h31]
    show (BitVec.ofNat 256 ((N + 31) / 32)).toNat = (N + 31) / 32
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hm : (mul (32 : U256) (div (add L (31 : U256)) (32 : U256))).toNat =
      (N + 31) / 32 * 32 := by
    unfold mul
    rw [BitVec.toNat_mul, hd]
    show 32 * ((N + 31) / 32) % 2 ^ 256 = (N + 31) / 32 * 32
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have h1 : (add (mul (32 : U256) (div (add L (31 : U256)) (32 : U256))) (32 : U256)).toNat =
      (N + 31) / 32 * 32 + 32 := toNat_add' hm (by decide) (by omega)
  have h2 := toNat_add' (a := (96 : U256)) (x := 96) (by decide) h1 (by omega)
  unfold tacFpw
  rw [h2]
  omega

/-- The low five bits of a word, as a number. -/
theorem and31_toNat {L : U256} {N : Nat} (hL : L.toNat = N) :
    (bitwiseAnd (31 : U256) L).toNat = N % 32 := by
  unfold bitwiseAnd
  rw [BitVec.toNat_and, hL]
  show 31 &&& N = N % 32
  rw [Nat.and_comm]
  exact Nat.and_two_pow_sub_one_eq_mod N 5

/-- The loop test `i < n` holds. -/
theorem lt_cond_go {a b : U256} {x y : Nat} (ha : a.toNat = x) (hb : b.toNat = y) (h : x < y) :
    isZero (lessThan a b) = 0 := by
  unfold lessThan
  rw [ha, hb, if_pos h]
  decide

/-- The loop test `i < n` fails. -/
theorem lt_cond_stop {a b : U256} {x y : Nat} (ha : a.toNat = x) (hb : b.toNat = y)
    (h : y ≤ x) : isZero (lessThan a b) ≠ 0 := by
  unfold lessThan
  rw [ha, hb, if_neg (by omega)]
  decide

/-- A word whose number is zero passes the test `ISZERO`. -/
theorem isZero_of_toNat {a : U256} (h : a.toNat = 0) : isZero a ≠ 0 := by
  have e : a = 0 := BitVec.eq_of_toNat_eq h
  rw [e]
  decide

/-- A word whose number is not zero fails the test `ISZERO`. -/
theorem isZero_of_toNat_pos {a : U256} {x : Nat} (h : a.toNat = x) (hx : 0 < x) :
    isZero a = 0 := by
  unfold isZero
  rw [if_neg]
  intro e
  rw [e] at h
  have : (0 : U256).toNat = 0 := rfl
  omega

/-- A word is the word of its number. -/
theorem ofNat_of_toNat {a : U256} {n : Nat} (h : a.toNat = n) : a = BitVec.ofNat 256 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, ← h]
  exact (Nat.mod_eq_of_lt a.isLt).symm

/-- The length of the `bytes` argument, as a number. -/
def tacN (message : Message fork) : Nat := (tacLen message).toNat

/-- The length of the `bytes` argument, rounded up to a multiple of 32. -/
def tacW (message : Message fork) : Nat := (tacN message + 31) / 32 * 32

/-- The free memory pointer after the copy of the `bytes` argument, as a number: the head of
128 bytes and the padded bytes. -/
def tacF (message : Message fork) : Nat := tacW message + 128

/-- An address read from a word that was cut to 160 bits on the other side. -/
theorem toAddressMasked_mask' (w : U256) :
    toAddressMasked (bitwiseAnd w (1461501637330902918203684832716283019655932542975 : U256)) =
      toAddressMasked w := by
  rw [show bitwiseAnd w (1461501637330902918203684832716283019655932542975 : U256) =
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w from
      BitVec.and_comm _ _]
  exact toAddressMasked_mask w

/-- A storage read keeps the code of every code hash. -/
theorem getCode_readSlot (S : State.TransactionState) (t : Address) (n : U256)
    (h : EthLib.Base.Hash32) : (readSlot S t n).getCode h = S.getCode h := rfl

/-- A code size that passed the test `size > 0` passes the test `size != 0`. -/
theorem code_twice {x : U256} (h : isZero (greaterThan x (0 : U256)) = 0) :
    isZero (isZero x) ≠ 0 := by
  have hx : x ≠ 0 := by
    intro e
    rw [e] at h
    revert h
    decide
  have h0 : isZero x = 0 := by
    unfold isZero
    rw [if_neg hx]
  rw [h0]
  decide

/-- A record of an account read keeps the code of every code hash. -/
theorem getCode_rar (S : State.TransactionState) (a : Address) (h : EthLib.Base.Hash32) :
    (S.recordAccountRead a).getCode h = S.getCode h := rfl

/-- A record of an account read keeps every account. -/
theorem getAccount_rar (S : State.TransactionState) (a b : Address) :
    (S.recordAccountRead a).getAccount b = S.getAccount b := rfl

end LinkVerify.Tac
