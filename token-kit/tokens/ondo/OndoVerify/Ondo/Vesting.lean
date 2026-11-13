import OndoVerify.Ondo.Gen
import OndoVerify.Ondo.Arith
import TokenKit.Evm.Readable

/-!
# The vesting rule of ONDO in plain words (audit 5, fix ONDO-4)

Written by hand. The generated path theorems state the vesting check of `_transferTokens` as
8 cases (`vest0_ends`, `vest1_ends`, `vest2_ends`: one segment for `transfer` and two for
`transferFrom`), each a list of conditions on words. This file states the rule that the 8
cases together say, on natural numbers, and proves it from them.

The rule (`VestRule B t c now bal a`): let `B` be the initial balance of the source
(`investorBalances[src] >> 8`, low 96 bits), `t` its tranche type (low byte), `c` the cliff
(slot 1), `now` the time stamp of the block, `bal` the balance of the source before the call
(low 96 bits) and `a` the amount. Then either `B = 0` (no vesting check), or `c + 60566400 <
2^256`, `t <= 2` unless `now > c + 60566400`, and `lockedAt B t c now <= bal` and
`a <= bal - lockedAt B t c now`, where `lockedAt` is:

- `B` when `now <= c` (before the cliff),
- `0` when `now > c + 60566400` (every period has passed),
- for `t = 0`: `B - floor(B * min(e, 15811200) / 15811200)` with `e = now - c`,
- for `t = 1`: `B - floor(B * min(e, 47433600) / 47433600)`,
- for `t = 2` (seed): `B - (floor(B / 3) + floor(2 * floor(B * e / 60566400) / 3))`.

- `vcase0` to `vcase7`: each case of the generated definitions, as conditions on five words,
  implies `VestRule`. No hypothesis beyond the conditions of the case.
- `vest0_rule`, `vest1_rule`, `vest2_rule`: each of the three generated definitions implies
  `VestRule` for the holder of the check.
- `transfer_vesting`: THE HEADLINE. A successful `transfer(to, amount)` satisfies `VestRule`
  for the caller, read in the state before the call, with the exact amount.
- `transferFrom_vesting`: the same for `transferFrom(src, dst, amount)` and `src`, with three
  keccak separation hypotheses (the allowance slot is none of the three slots of the check).

Every message runner, from Berlin (the path layer; per call, one-counter meter).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace OndoVerify

open UsdtVerify
open TokenKit
open OndoVerify.Paths

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- The locked amount of the source (natural numbers): `B` initial balance, `t` tranche type,
`c` cliff, `now` time stamp. -/
def lockedAt (B t c now : Nat) : Nat :=
  if now ≤ c then B
  else if c + 60566400 < now then 0
  else if t = 0 then B - B * min (now - c) 15811200 / 15811200
  else if t = 1 then B - B * min (now - c) 47433600 / 47433600
  else B - (B / 3 + 2 * (B * (now - c) / 60566400) / 3)

/-- The vesting rule for a transfer of `a` out of a holder with balance `bal`. -/
def VestRule (B t c now bal a : Nat) : Prop :=
  B = 0 ∨ (c + 60566400 < 2 ^ 256 ∧ (now ≤ c + 60566400 → t ≤ 2) ∧
    lockedAt B t c now ≤ bal ∧ a ≤ bal - lockedAt B t c now)

/-! ## The 8 cases, as conditions on words -/

/-- Case 0 of the vesting check (every period has passed). -/
theorem vcase0 (x cl nw bl a0 : U256)
    (h1 : (isZero (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256)))) = 0)
    (h2 : (isZero (greaterThan cl (115792089237316195423570985008687907853269984665640564039457584007913069073535 : U256))) ≠ 0)
    (h3 : (isZero (greaterThan nw (add cl (60566400 : U256)))) = 0)
    (h4 : (isZero (greaterThan (bitwiseAnd (79228162514264337593543950335 : U256) a0) (bitwiseAnd (79228162514264337593543950335 : U256) (bitwiseAnd (79228162514264337593543950335 : U256) bl)))) ≠ 0) :
    VestRule (x.toNat / 256 % 2 ^ 96) (x.toNat % 2 ^ 8) cl.toNat nw.toNat (bl.toNat % 2 ^ 96)
      (a0.toNat % 2 ^ 96) := by
  simp only [TokenKit.and_m96_comm, TokenKit.and_m32_comm, TokenKit.and_mask_comm, OndoVerify.and_m8_comm,
    OndoVerify.c_isZero_ne, OndoVerify.c_isZero_eq, OndoVerify.c_andb_ne, OndoVerify.c_andb_eq,
    OndoVerify.c_and1_ne, OndoVerify.c_and1_eq, OndoVerify.c_lt_ne, OndoVerify.c_lt_eq,
    OndoVerify.c_gt_ne, OndoVerify.c_gt_eq, OndoVerify.c_eq_ne, OndoVerify.c_eq_eq] at *
  simp only [ne_eq, OndoVerify.w_eq0, TokenKit.toNat_m96, OndoVerify.toNat_m8,
    OndoVerify.toNat_m32, OndoVerify.toNat_m160, TokenKit.toNat_addW, TokenKit.toNat_subW,
    OndoVerify.toNat_mulW, OndoVerify.toNat_divW, BitVec.reduceToNat, Nat.mod_mod, Nat.div_one] at *
  have hcl := cl.isLt
  have hnl := nw.isLt
  have hBl : x.toNat / 256 % 2 ^ 96 < 2 ^ 96 := Nat.mod_lt _ (by decide)
  have hbl : bl.toNat % 2 ^ 96 < 2 ^ 96 := Nat.mod_lt _ (by decide)
  unfold VestRule lockedAt
  generalize x.toNat / 256 % 2 ^ 96 = B at *
  generalize x.toNat % 2 ^ 8 = t at *
  generalize cl.toNat = c at *
  generalize nw.toNat = n at *
  generalize bl.toNat % 2 ^ 96 = b at *
  generalize a0.toNat % 2 ^ 96 = a at *
  have hc3 : (c + 60566400) % 2 ^ 256 = c + 60566400 := Nat.mod_eq_of_lt (by omega)
  rw [hc3] at h3
  right
  rw [if_neg (by omega), if_pos h3]
  refine ⟨by omega, fun _ => by omega, by omega, by omega⟩

/-- Case 1 of the vesting check (type 0, within its period). -/
theorem vcase1 (x cl nw bl a0 : U256)
    (h1 : (isZero (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256)))) = 0)
    (h2 : (isZero (greaterThan cl (115792089237316195423570985008687907853269984665640564039457584007913069073535 : U256))) ≠ 0)
    (h3 : (isZero (greaterThan nw (add cl (60566400 : U256)))) ≠ 0)
    (h4 : (isZero (greaterThan (bitwiseAnd x (255 : U256)) (2 : U256))) ≠ 0)
    (h5 : (isZero (greaterThan nw cl)) = 0)
    (h6 : (isZero (equal (bitwiseAnd x (255 : U256)) (0 : U256))) = 0)
    (h7 : (greaterThan (sub nw cl) (15811200 : U256)) = 0)
    (h8 : (isZero (greaterThan (bitwiseAnd (79228162514264337593543950335 : U256) (sub (bitwiseAnd (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256))) (79228162514264337593543950335 : U256)) (bitwiseAnd (79228162514264337593543950335 : U256) (div (mul (bitwiseAnd (79228162514264337593543950335 : U256) (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256)))) (sub nw cl)) (15811200 : U256))))) (bitwiseAnd (79228162514264337593543950335 : U256) (bitwiseAnd (79228162514264337593543950335 : U256) (div bl (1 : U256)))))) ≠ 0)
    (h9 : (isZero (greaterThan (bitwiseAnd (79228162514264337593543950335 : U256) a0) (bitwiseAnd (79228162514264337593543950335 : U256) (sub (bitwiseAnd (bitwiseAnd (79228162514264337593543950335 : U256) (div bl (1 : U256))) (79228162514264337593543950335 : U256)) (bitwiseAnd (79228162514264337593543950335 : U256) (sub (bitwiseAnd (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256))) (79228162514264337593543950335 : U256)) (bitwiseAnd (79228162514264337593543950335 : U256) (div (mul (bitwiseAnd (79228162514264337593543950335 : U256) (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256)))) (sub nw cl)) (15811200 : U256))))))))) ≠ 0) :
    VestRule (x.toNat / 256 % 2 ^ 96) (x.toNat % 2 ^ 8) cl.toNat nw.toNat (bl.toNat % 2 ^ 96)
      (a0.toNat % 2 ^ 96) := by
  simp only [TokenKit.and_m96_comm, TokenKit.and_m32_comm, TokenKit.and_mask_comm, OndoVerify.and_m8_comm,
    OndoVerify.c_isZero_ne, OndoVerify.c_isZero_eq, OndoVerify.c_andb_ne, OndoVerify.c_andb_eq,
    OndoVerify.c_and1_ne, OndoVerify.c_and1_eq, OndoVerify.c_lt_ne, OndoVerify.c_lt_eq,
    OndoVerify.c_gt_ne, OndoVerify.c_gt_eq, OndoVerify.c_eq_ne, OndoVerify.c_eq_eq] at *
  simp only [ne_eq, OndoVerify.w_eq0, TokenKit.toNat_m96, OndoVerify.toNat_m8,
    OndoVerify.toNat_m32, OndoVerify.toNat_m160, TokenKit.toNat_addW, TokenKit.toNat_subW,
    OndoVerify.toNat_mulW, OndoVerify.toNat_divW, BitVec.reduceToNat, Nat.mod_mod, Nat.div_one] at *
  have hcl := cl.isLt
  have hnl := nw.isLt
  have hBl : x.toNat / 256 % 2 ^ 96 < 2 ^ 96 := Nat.mod_lt _ (by decide)
  have hbl : bl.toNat % 2 ^ 96 < 2 ^ 96 := Nat.mod_lt _ (by decide)
  unfold VestRule lockedAt
  generalize x.toNat / 256 % 2 ^ 96 = B at *
  generalize x.toNat % 2 ^ 8 = t at *
  generalize cl.toNat = c at *
  generalize nw.toNat = n at *
  generalize bl.toNat % 2 ^ 96 = b at *
  generalize a0.toNat % 2 ^ 96 = a at *
  have hc3 : (c + 60566400) % 2 ^ 256 = c + 60566400 := Nat.mod_eq_of_lt (by omega)
  rw [hc3] at h3
  have he : (2 ^ 256 - c + n) % 2 ^ 256 = n - c := by omega
  try simp only [he] at *
  right
  rw [if_neg (by omega), if_neg (by omega), if_pos h6, Nat.min_eq_left h7]
  have hV : B * (n - c) ≤ B * 15811200 := Nat.mul_le_mul_left _ h7
  generalize B * (n - c) = V at *
  have hVl : V % 2 ^ 256 = V := Nat.mod_eq_of_lt (by omega)
  try simp only [hVl] at *
  have hq : V / 15811200 ≤ B := by omega
  try simp (disch := omega) only [Nat.mod_eq_of_lt, OndoVerify.sub_mod_of_le] at *
  try simp (disch := omega) only [Nat.mod_eq_of_lt, OndoVerify.sub_mod_of_le] at *
  try simp (disch := omega) only [Nat.mod_eq_of_lt, OndoVerify.sub_mod_of_le] at *
  refine ⟨by omega, fun _ => by omega, by omega, by omega⟩

/-- Case 2 of the vesting check (type 0, past its period). -/
theorem vcase2 (x cl nw bl a0 : U256)
    (h1 : (isZero (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256)))) = 0)
    (h2 : (isZero (greaterThan cl (115792089237316195423570985008687907853269984665640564039457584007913069073535 : U256))) ≠ 0)
    (h3 : (isZero (greaterThan nw (add cl (60566400 : U256)))) ≠ 0)
    (h4 : (isZero (greaterThan (bitwiseAnd x (255 : U256)) (2 : U256))) ≠ 0)
    (h5 : (isZero (greaterThan nw cl)) = 0)
    (h6 : (isZero (equal (bitwiseAnd x (255 : U256)) (0 : U256))) = 0)
    (h7 : (greaterThan (sub nw cl) (15811200 : U256)) ≠ 0)
    (h8 : (isZero (greaterThan (bitwiseAnd (79228162514264337593543950335 : U256) a0) (bitwiseAnd (79228162514264337593543950335 : U256) (sub (bitwiseAnd (bitwiseAnd (79228162514264337593543950335 : U256) (div bl (1 : U256))) (79228162514264337593543950335 : U256)) (bitwiseAnd (79228162514264337593543950335 : U256) (sub (bitwiseAnd (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256))) (79228162514264337593543950335 : U256)) (bitwiseAnd (79228162514264337593543950335 : U256) (div (mul (bitwiseAnd (79228162514264337593543950335 : U256) (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256)))) (15811200 : U256)) (15811200 : U256))))))))) ≠ 0) :
    VestRule (x.toNat / 256 % 2 ^ 96) (x.toNat % 2 ^ 8) cl.toNat nw.toNat (bl.toNat % 2 ^ 96)
      (a0.toNat % 2 ^ 96) := by
  simp only [TokenKit.and_m96_comm, TokenKit.and_m32_comm, TokenKit.and_mask_comm, OndoVerify.and_m8_comm,
    OndoVerify.c_isZero_ne, OndoVerify.c_isZero_eq, OndoVerify.c_andb_ne, OndoVerify.c_andb_eq,
    OndoVerify.c_and1_ne, OndoVerify.c_and1_eq, OndoVerify.c_lt_ne, OndoVerify.c_lt_eq,
    OndoVerify.c_gt_ne, OndoVerify.c_gt_eq, OndoVerify.c_eq_ne, OndoVerify.c_eq_eq] at *
  simp only [ne_eq, OndoVerify.w_eq0, TokenKit.toNat_m96, OndoVerify.toNat_m8,
    OndoVerify.toNat_m32, OndoVerify.toNat_m160, TokenKit.toNat_addW, TokenKit.toNat_subW,
    OndoVerify.toNat_mulW, OndoVerify.toNat_divW, BitVec.reduceToNat, Nat.mod_mod, Nat.div_one] at *
  have hcl := cl.isLt
  have hnl := nw.isLt
  have hBl : x.toNat / 256 % 2 ^ 96 < 2 ^ 96 := Nat.mod_lt _ (by decide)
  have hbl : bl.toNat % 2 ^ 96 < 2 ^ 96 := Nat.mod_lt _ (by decide)
  unfold VestRule lockedAt
  generalize x.toNat / 256 % 2 ^ 96 = B at *
  generalize x.toNat % 2 ^ 8 = t at *
  generalize cl.toNat = c at *
  generalize nw.toNat = n at *
  generalize bl.toNat % 2 ^ 96 = b at *
  generalize a0.toNat % 2 ^ 96 = a at *
  have hc3 : (c + 60566400) % 2 ^ 256 = c + 60566400 := Nat.mod_eq_of_lt (by omega)
  rw [hc3] at h3
  have he : (2 ^ 256 - c + n) % 2 ^ 256 = n - c := by omega
  try simp only [he] at *
  right
  rw [if_neg (by omega), if_neg (by omega), if_pos h6, Nat.min_eq_right (Nat.le_of_lt h7), Nat.mul_div_cancel _ (by decide)]
  have hq : B * 15811200 % 2 ^ 256 / 15811200 = B := by
    rw [Nat.mod_eq_of_lt (by omega), Nat.mul_div_cancel _ (by decide)]
  try simp only [hq, Nat.mod_eq_of_lt hBl, Nat.sub_self] at *
  try simp (disch := omega) only [Nat.mod_eq_of_lt, OndoVerify.sub_mod_of_le] at *
  try simp (disch := omega) only [Nat.mod_eq_of_lt, OndoVerify.sub_mod_of_le] at *
  try simp (disch := omega) only [Nat.mod_eq_of_lt, OndoVerify.sub_mod_of_le] at *
  refine ⟨by omega, fun _ => by omega, by omega, by omega⟩

/-- Case 3 of the vesting check (type 1, within its period). -/
theorem vcase3 (x cl nw bl a0 : U256)
    (h1 : (isZero (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256)))) = 0)
    (h2 : (isZero (greaterThan cl (115792089237316195423570985008687907853269984665640564039457584007913069073535 : U256))) ≠ 0)
    (h3 : (isZero (greaterThan nw (add cl (60566400 : U256)))) ≠ 0)
    (h4 : (isZero (greaterThan (bitwiseAnd x (255 : U256)) (2 : U256))) ≠ 0)
    (h5 : (isZero (greaterThan nw cl)) = 0)
    (h6 : (isZero (equal (bitwiseAnd x (255 : U256)) (0 : U256))) ≠ 0)
    (h7 : (isZero (equal (bitwiseAnd x (255 : U256)) (1 : U256))) = 0)
    (h8 : (greaterThan (sub nw cl) (47433600 : U256)) = 0)
    (h9 : (isZero (greaterThan (bitwiseAnd (79228162514264337593543950335 : U256) (sub (bitwiseAnd (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256))) (79228162514264337593543950335 : U256)) (bitwiseAnd (79228162514264337593543950335 : U256) (div (mul (bitwiseAnd (79228162514264337593543950335 : U256) (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256)))) (sub nw cl)) (47433600 : U256))))) (bitwiseAnd (79228162514264337593543950335 : U256) (bitwiseAnd (79228162514264337593543950335 : U256) (div bl (1 : U256)))))) ≠ 0)
    (h10 : (isZero (greaterThan (bitwiseAnd (79228162514264337593543950335 : U256) a0) (bitwiseAnd (79228162514264337593543950335 : U256) (sub (bitwiseAnd (bitwiseAnd (79228162514264337593543950335 : U256) (div bl (1 : U256))) (79228162514264337593543950335 : U256)) (bitwiseAnd (79228162514264337593543950335 : U256) (sub (bitwiseAnd (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256))) (79228162514264337593543950335 : U256)) (bitwiseAnd (79228162514264337593543950335 : U256) (div (mul (bitwiseAnd (79228162514264337593543950335 : U256) (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256)))) (sub nw cl)) (47433600 : U256))))))))) ≠ 0) :
    VestRule (x.toNat / 256 % 2 ^ 96) (x.toNat % 2 ^ 8) cl.toNat nw.toNat (bl.toNat % 2 ^ 96)
      (a0.toNat % 2 ^ 96) := by
  simp only [TokenKit.and_m96_comm, TokenKit.and_m32_comm, TokenKit.and_mask_comm, OndoVerify.and_m8_comm,
    OndoVerify.c_isZero_ne, OndoVerify.c_isZero_eq, OndoVerify.c_andb_ne, OndoVerify.c_andb_eq,
    OndoVerify.c_and1_ne, OndoVerify.c_and1_eq, OndoVerify.c_lt_ne, OndoVerify.c_lt_eq,
    OndoVerify.c_gt_ne, OndoVerify.c_gt_eq, OndoVerify.c_eq_ne, OndoVerify.c_eq_eq] at *
  simp only [ne_eq, OndoVerify.w_eq0, TokenKit.toNat_m96, OndoVerify.toNat_m8,
    OndoVerify.toNat_m32, OndoVerify.toNat_m160, TokenKit.toNat_addW, TokenKit.toNat_subW,
    OndoVerify.toNat_mulW, OndoVerify.toNat_divW, BitVec.reduceToNat, Nat.mod_mod, Nat.div_one] at *
  have hcl := cl.isLt
  have hnl := nw.isLt
  have hBl : x.toNat / 256 % 2 ^ 96 < 2 ^ 96 := Nat.mod_lt _ (by decide)
  have hbl : bl.toNat % 2 ^ 96 < 2 ^ 96 := Nat.mod_lt _ (by decide)
  unfold VestRule lockedAt
  generalize x.toNat / 256 % 2 ^ 96 = B at *
  generalize x.toNat % 2 ^ 8 = t at *
  generalize cl.toNat = c at *
  generalize nw.toNat = n at *
  generalize bl.toNat % 2 ^ 96 = b at *
  generalize a0.toNat % 2 ^ 96 = a at *
  have hc3 : (c + 60566400) % 2 ^ 256 = c + 60566400 := Nat.mod_eq_of_lt (by omega)
  rw [hc3] at h3
  have he : (2 ^ 256 - c + n) % 2 ^ 256 = n - c := by omega
  try simp only [he] at *
  right
  rw [if_neg (by omega), if_neg (by omega), if_neg h6, if_pos h7, Nat.min_eq_left h8]
  have hV : B * (n - c) ≤ B * 47433600 := Nat.mul_le_mul_left _ h8
  generalize B * (n - c) = V at *
  have hVl : V % 2 ^ 256 = V := Nat.mod_eq_of_lt (by omega)
  try simp only [hVl] at *
  have hq : V / 47433600 ≤ B := by omega
  try simp (disch := omega) only [Nat.mod_eq_of_lt, OndoVerify.sub_mod_of_le] at *
  try simp (disch := omega) only [Nat.mod_eq_of_lt, OndoVerify.sub_mod_of_le] at *
  try simp (disch := omega) only [Nat.mod_eq_of_lt, OndoVerify.sub_mod_of_le] at *
  refine ⟨by omega, fun _ => by omega, by omega, by omega⟩

/-- Case 4 of the vesting check (type 1, past its period). -/
theorem vcase4 (x cl nw bl a0 : U256)
    (h1 : (isZero (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256)))) = 0)
    (h2 : (isZero (greaterThan cl (115792089237316195423570985008687907853269984665640564039457584007913069073535 : U256))) ≠ 0)
    (h3 : (isZero (greaterThan nw (add cl (60566400 : U256)))) ≠ 0)
    (h4 : (isZero (greaterThan (bitwiseAnd x (255 : U256)) (2 : U256))) ≠ 0)
    (h5 : (isZero (greaterThan nw cl)) = 0)
    (h6 : (isZero (equal (bitwiseAnd x (255 : U256)) (0 : U256))) ≠ 0)
    (h7 : (isZero (equal (bitwiseAnd x (255 : U256)) (1 : U256))) = 0)
    (h8 : (greaterThan (sub nw cl) (47433600 : U256)) ≠ 0)
    (h9 : (isZero (greaterThan (bitwiseAnd (79228162514264337593543950335 : U256) a0) (bitwiseAnd (79228162514264337593543950335 : U256) (sub (bitwiseAnd (bitwiseAnd (79228162514264337593543950335 : U256) (div bl (1 : U256))) (79228162514264337593543950335 : U256)) (bitwiseAnd (79228162514264337593543950335 : U256) (sub (bitwiseAnd (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256))) (79228162514264337593543950335 : U256)) (bitwiseAnd (79228162514264337593543950335 : U256) (div (mul (bitwiseAnd (79228162514264337593543950335 : U256) (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256)))) (47433600 : U256)) (47433600 : U256))))))))) ≠ 0) :
    VestRule (x.toNat / 256 % 2 ^ 96) (x.toNat % 2 ^ 8) cl.toNat nw.toNat (bl.toNat % 2 ^ 96)
      (a0.toNat % 2 ^ 96) := by
  simp only [TokenKit.and_m96_comm, TokenKit.and_m32_comm, TokenKit.and_mask_comm, OndoVerify.and_m8_comm,
    OndoVerify.c_isZero_ne, OndoVerify.c_isZero_eq, OndoVerify.c_andb_ne, OndoVerify.c_andb_eq,
    OndoVerify.c_and1_ne, OndoVerify.c_and1_eq, OndoVerify.c_lt_ne, OndoVerify.c_lt_eq,
    OndoVerify.c_gt_ne, OndoVerify.c_gt_eq, OndoVerify.c_eq_ne, OndoVerify.c_eq_eq] at *
  simp only [ne_eq, OndoVerify.w_eq0, TokenKit.toNat_m96, OndoVerify.toNat_m8,
    OndoVerify.toNat_m32, OndoVerify.toNat_m160, TokenKit.toNat_addW, TokenKit.toNat_subW,
    OndoVerify.toNat_mulW, OndoVerify.toNat_divW, BitVec.reduceToNat, Nat.mod_mod, Nat.div_one] at *
  have hcl := cl.isLt
  have hnl := nw.isLt
  have hBl : x.toNat / 256 % 2 ^ 96 < 2 ^ 96 := Nat.mod_lt _ (by decide)
  have hbl : bl.toNat % 2 ^ 96 < 2 ^ 96 := Nat.mod_lt _ (by decide)
  unfold VestRule lockedAt
  generalize x.toNat / 256 % 2 ^ 96 = B at *
  generalize x.toNat % 2 ^ 8 = t at *
  generalize cl.toNat = c at *
  generalize nw.toNat = n at *
  generalize bl.toNat % 2 ^ 96 = b at *
  generalize a0.toNat % 2 ^ 96 = a at *
  have hc3 : (c + 60566400) % 2 ^ 256 = c + 60566400 := Nat.mod_eq_of_lt (by omega)
  rw [hc3] at h3
  have he : (2 ^ 256 - c + n) % 2 ^ 256 = n - c := by omega
  try simp only [he] at *
  right
  rw [if_neg (by omega), if_neg (by omega), if_neg h6, if_pos h7, Nat.min_eq_right (Nat.le_of_lt h8), Nat.mul_div_cancel _ (by decide)]
  have hq : B * 47433600 % 2 ^ 256 / 47433600 = B := by
    rw [Nat.mod_eq_of_lt (by omega), Nat.mul_div_cancel _ (by decide)]
  try simp only [hq, Nat.mod_eq_of_lt hBl, Nat.sub_self] at *
  try simp (disch := omega) only [Nat.mod_eq_of_lt, OndoVerify.sub_mod_of_le] at *
  try simp (disch := omega) only [Nat.mod_eq_of_lt, OndoVerify.sub_mod_of_le] at *
  try simp (disch := omega) only [Nat.mod_eq_of_lt, OndoVerify.sub_mod_of_le] at *
  refine ⟨by omega, fun _ => by omega, by omega, by omega⟩

/-- Case 5 of the vesting check (seed (type 2)). -/
theorem vcase5 (x cl nw bl a0 : U256)
    (h1 : (isZero (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256)))) = 0)
    (h2 : (isZero (greaterThan cl (115792089237316195423570985008687907853269984665640564039457584007913069073535 : U256))) ≠ 0)
    (h3 : (isZero (greaterThan nw (add cl (60566400 : U256)))) ≠ 0)
    (h4 : (isZero (greaterThan (bitwiseAnd x (255 : U256)) (2 : U256))) ≠ 0)
    (h5 : (isZero (greaterThan nw cl)) = 0)
    (h6 : (isZero (equal (bitwiseAnd x (255 : U256)) (0 : U256))) ≠ 0)
    (h7 : (isZero (equal (bitwiseAnd x (255 : U256)) (1 : U256))) ≠ 0)
    (h8 : (isZero (greaterThan (bitwiseAnd (79228162514264337593543950335 : U256) (sub (bitwiseAnd (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256))) (79228162514264337593543950335 : U256)) (bitwiseAnd (79228162514264337593543950335 : U256) (add (bitwiseAnd (div (bitwiseAnd (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256))) (79228162514264337593543950335 : U256)) (3 : U256)) (79228162514264337593543950335 : U256)) (bitwiseAnd (div (mul (2 : U256) (div (mul (bitwiseAnd (79228162514264337593543950335 : U256) (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256)))) (sub nw cl)) (60566400 : U256))) (3 : U256)) (79228162514264337593543950335 : U256)))))) (bitwiseAnd (79228162514264337593543950335 : U256) (bitwiseAnd (79228162514264337593543950335 : U256) (div bl (1 : U256)))))) ≠ 0)
    (h9 : (isZero (greaterThan (bitwiseAnd (79228162514264337593543950335 : U256) a0) (bitwiseAnd (79228162514264337593543950335 : U256) (sub (bitwiseAnd (bitwiseAnd (79228162514264337593543950335 : U256) (div bl (1 : U256))) (79228162514264337593543950335 : U256)) (bitwiseAnd (79228162514264337593543950335 : U256) (sub (bitwiseAnd (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256))) (79228162514264337593543950335 : U256)) (bitwiseAnd (79228162514264337593543950335 : U256) (add (bitwiseAnd (div (bitwiseAnd (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256))) (79228162514264337593543950335 : U256)) (3 : U256)) (79228162514264337593543950335 : U256)) (bitwiseAnd (div (mul (2 : U256) (div (mul (bitwiseAnd (79228162514264337593543950335 : U256) (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256)))) (sub nw cl)) (60566400 : U256))) (3 : U256)) (79228162514264337593543950335 : U256)))))))))) ≠ 0) :
    VestRule (x.toNat / 256 % 2 ^ 96) (x.toNat % 2 ^ 8) cl.toNat nw.toNat (bl.toNat % 2 ^ 96)
      (a0.toNat % 2 ^ 96) := by
  simp only [TokenKit.and_m96_comm, TokenKit.and_m32_comm, TokenKit.and_mask_comm, OndoVerify.and_m8_comm,
    OndoVerify.c_isZero_ne, OndoVerify.c_isZero_eq, OndoVerify.c_andb_ne, OndoVerify.c_andb_eq,
    OndoVerify.c_and1_ne, OndoVerify.c_and1_eq, OndoVerify.c_lt_ne, OndoVerify.c_lt_eq,
    OndoVerify.c_gt_ne, OndoVerify.c_gt_eq, OndoVerify.c_eq_ne, OndoVerify.c_eq_eq] at *
  simp only [ne_eq, OndoVerify.w_eq0, TokenKit.toNat_m96, OndoVerify.toNat_m8,
    OndoVerify.toNat_m32, OndoVerify.toNat_m160, TokenKit.toNat_addW, TokenKit.toNat_subW,
    OndoVerify.toNat_mulW, OndoVerify.toNat_divW, BitVec.reduceToNat, Nat.mod_mod, Nat.div_one] at *
  have hcl := cl.isLt
  have hnl := nw.isLt
  have hBl : x.toNat / 256 % 2 ^ 96 < 2 ^ 96 := Nat.mod_lt _ (by decide)
  have hbl : bl.toNat % 2 ^ 96 < 2 ^ 96 := Nat.mod_lt _ (by decide)
  unfold VestRule lockedAt
  generalize x.toNat / 256 % 2 ^ 96 = B at *
  generalize x.toNat % 2 ^ 8 = t at *
  generalize cl.toNat = c at *
  generalize nw.toNat = n at *
  generalize bl.toNat % 2 ^ 96 = b at *
  generalize a0.toNat % 2 ^ 96 = a at *
  have hc3 : (c + 60566400) % 2 ^ 256 = c + 60566400 := Nat.mod_eq_of_lt (by omega)
  rw [hc3] at h3
  have he : (2 ^ 256 - c + n) % 2 ^ 256 = n - c := by omega
  try simp only [he] at *
  right
  rw [if_neg (by omega), if_neg (by omega), if_neg h6, if_neg h7]
  have hle : n - c ≤ 60566400 := by omega
  have hV : B * (n - c) ≤ B * 60566400 := Nat.mul_le_mul_left _ hle
  generalize B * (n - c) = V at *
  have hVl : V % 2 ^ 256 = V := Nat.mod_eq_of_lt (by omega)
  try simp only [hVl] at *
  have hq : V / 60566400 ≤ B := by omega
  generalize V / 60566400 = Q at *
  have hq2 : 2 * Q % 2 ^ 256 = 2 * Q := Nat.mod_eq_of_lt (by omega)
  try simp only [hq2] at *
  have hR : 2 * Q / 3 * 3 ≤ 2 * Q := Nat.div_mul_le_self _ _
  generalize 2 * Q / 3 = R at *
  have h13 : B / 3 * 3 ≤ B := Nat.div_mul_le_self _ _
  generalize B / 3 = q at *
  have e1 : q % 2 ^ 96 = q := Nat.mod_eq_of_lt (by omega)
  have e3 : R % 2 ^ 96 = R := Nat.mod_eq_of_lt (by omega)
  simp only [e1, e3] at h8 h9
  have e4 : (q + R) % 2 ^ 256 = q + R := Nat.mod_eq_of_lt (by omega)
  simp only [e4] at h8 h9
  have e5 : (q + R) % 2 ^ 96 = q + R := Nat.mod_eq_of_lt (by omega)
  simp only [e5] at h8 h9
  have e6 : (2 ^ 256 - (q + R) + B) % 2 ^ 256 = B - (q + R) :=
    OndoVerify.sub_mod_of_le (by omega) (by omega)
  simp only [e6] at h8 h9
  have e7 : (B - (q + R)) % 2 ^ 96 = B - (q + R) := Nat.mod_eq_of_lt (by omega)
  simp only [e7] at h8 h9
  have e8 : (2 ^ 256 - (B - (q + R)) + b) % 2 ^ 256 = b - (B - (q + R)) :=
    OndoVerify.sub_mod_of_le h8 (by omega)
  simp only [e8] at h9
  have e9 : (b - (B - (q + R))) % 2 ^ 96 = b - (B - (q + R)) := Nat.mod_eq_of_lt (by omega)
  simp only [e9] at h9
  refine ⟨by omega, fun _ => by omega, by omega, by omega⟩

/-- Case 6 of the vesting check (before the cliff). -/
theorem vcase6 (x cl nw bl a0 : U256)
    (h1 : (isZero (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256)))) = 0)
    (h2 : (isZero (greaterThan cl (115792089237316195423570985008687907853269984665640564039457584007913069073535 : U256))) ≠ 0)
    (h3 : (isZero (greaterThan nw (add cl (60566400 : U256)))) ≠ 0)
    (h4 : (isZero (greaterThan (bitwiseAnd x (255 : U256)) (2 : U256))) ≠ 0)
    (h5 : (isZero (greaterThan nw cl)) ≠ 0)
    (h6 : (isZero (greaterThan (bitwiseAnd (79228162514264337593543950335 : U256) (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256)))) (bitwiseAnd (79228162514264337593543950335 : U256) (bitwiseAnd bl (79228162514264337593543950335 : U256))))) ≠ 0)
    (h7 : (isZero (greaterThan (bitwiseAnd (79228162514264337593543950335 : U256) a0) (bitwiseAnd (79228162514264337593543950335 : U256) (sub (bitwiseAnd (bitwiseAnd bl (79228162514264337593543950335 : U256)) (79228162514264337593543950335 : U256)) (bitwiseAnd (79228162514264337593543950335 : U256) (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256)))))))) ≠ 0) :
    VestRule (x.toNat / 256 % 2 ^ 96) (x.toNat % 2 ^ 8) cl.toNat nw.toNat (bl.toNat % 2 ^ 96)
      (a0.toNat % 2 ^ 96) := by
  simp only [TokenKit.and_m96_comm, TokenKit.and_m32_comm, TokenKit.and_mask_comm, OndoVerify.and_m8_comm,
    OndoVerify.c_isZero_ne, OndoVerify.c_isZero_eq, OndoVerify.c_andb_ne, OndoVerify.c_andb_eq,
    OndoVerify.c_and1_ne, OndoVerify.c_and1_eq, OndoVerify.c_lt_ne, OndoVerify.c_lt_eq,
    OndoVerify.c_gt_ne, OndoVerify.c_gt_eq, OndoVerify.c_eq_ne, OndoVerify.c_eq_eq] at *
  simp only [ne_eq, OndoVerify.w_eq0, TokenKit.toNat_m96, OndoVerify.toNat_m8,
    OndoVerify.toNat_m32, OndoVerify.toNat_m160, TokenKit.toNat_addW, TokenKit.toNat_subW,
    OndoVerify.toNat_mulW, OndoVerify.toNat_divW, BitVec.reduceToNat, Nat.mod_mod, Nat.div_one] at *
  have hcl := cl.isLt
  have hnl := nw.isLt
  have hBl : x.toNat / 256 % 2 ^ 96 < 2 ^ 96 := Nat.mod_lt _ (by decide)
  have hbl : bl.toNat % 2 ^ 96 < 2 ^ 96 := Nat.mod_lt _ (by decide)
  unfold VestRule lockedAt
  generalize x.toNat / 256 % 2 ^ 96 = B at *
  generalize x.toNat % 2 ^ 8 = t at *
  generalize cl.toNat = c at *
  generalize nw.toNat = n at *
  generalize bl.toNat % 2 ^ 96 = b at *
  generalize a0.toNat % 2 ^ 96 = a at *
  have hc3 : (c + 60566400) % 2 ^ 256 = c + 60566400 := Nat.mod_eq_of_lt (by omega)
  rw [hc3] at h3
  right
  rw [if_pos h5]
  try simp (disch := omega) only [Nat.mod_eq_of_lt, OndoVerify.sub_mod_of_le] at *
  try simp (disch := omega) only [Nat.mod_eq_of_lt, OndoVerify.sub_mod_of_le] at *
  try simp (disch := omega) only [Nat.mod_eq_of_lt, OndoVerify.sub_mod_of_le] at *
  refine ⟨by omega, fun _ => by omega, by omega, by omega⟩

/-- Case 7 of the vesting check (no initial balance). -/
theorem vcase7 (x cl nw bl a0 : U256)
    (h1 : (isZero (bitwiseAnd (79228162514264337593543950335 : U256) (div x (256 : U256)))) ≠ 0) :
    VestRule (x.toNat / 256 % 2 ^ 96) (x.toNat % 2 ^ 8) cl.toNat nw.toNat (bl.toNat % 2 ^ 96)
      (a0.toNat % 2 ^ 96) := by
  simp only [TokenKit.and_m96_comm, TokenKit.and_m32_comm, TokenKit.and_mask_comm, OndoVerify.and_m8_comm,
    OndoVerify.c_isZero_ne, OndoVerify.c_isZero_eq, OndoVerify.c_andb_ne, OndoVerify.c_andb_eq,
    OndoVerify.c_and1_ne, OndoVerify.c_and1_eq, OndoVerify.c_lt_ne, OndoVerify.c_lt_eq,
    OndoVerify.c_gt_ne, OndoVerify.c_gt_eq, OndoVerify.c_eq_ne, OndoVerify.c_eq_eq] at *
  simp only [ne_eq, OndoVerify.w_eq0, TokenKit.toNat_m96, OndoVerify.toNat_m8,
    OndoVerify.toNat_m32, OndoVerify.toNat_m160, TokenKit.toNat_addW, TokenKit.toNat_subW,
    OndoVerify.toNat_mulW, OndoVerify.toNat_divW, BitVec.reduceToNat, Nat.mod_mod, Nat.div_one] at *
  unfold VestRule
  exact Or.inl h1

/-! ## The rule for one segment of the vesting check -/

/-- `bitwiseAnd M160 (bitwiseAnd M160 w) = bitwiseAnd w M160`: the two ways the code writes the
address word of the holder. -/
theorem m160_m160 (w : U256) :
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w) =
    bitwiseAnd w (1461501637330902918203684832716283019655932542975 : U256) := by
  unfold bitwiseAnd
  rw [← BitVec.and_assoc, BitVec.and_self, BitVec.and_comm]

/-- The words of the rule, read in a state: the initial balance, the tranche type, the cliff,
the balance of the holder (address word `h`). -/
abbrev initialOf (S : State.TransactionState) (C : Address) (h : U256) : Nat :=
  (storageAt S C (mapSlot h 2)).toNat / 256 % 2 ^ 96
abbrev trancheOf (S : State.TransactionState) (C : Address) (h : U256) : Nat :=
  (storageAt S C (mapSlot h 2)).toNat % 2 ^ 8
abbrev cliffOf (S : State.TransactionState) (C : Address) : Nat := (storageAt S C 1).toNat
abbrev balanceOf96 (S : State.TransactionState) (C : Address) (h : U256) : Nat :=
  (storageAt S C (mapSlot h 6)).toNat % 2 ^ 96

/-- The holder of the vesting check (`a2`) has the address word `bitwiseAnd a2 M160`. -/
abbrev holderOf (a2 : U256) : U256 :=
  bitwiseAnd a2 (1461501637330902918203684832716283019655932542975 : U256)

/-- THE RULE, for the check of `transfer` (`vest0_ends`): the 8 cases of the generated
path theorem together imply `VestRule`. -/
theorem vest0_rule {fork : Fork} {message : Message fork} {state : State.TransactionState}
    {substate : Substate} {gas : Nat} {s : Evm fork Nat} {a0 a1 a2 a3 : U256} {mem : ByteArray}
    (h : vest0_ends fork message state substate gas s a0 a1 a2 a3 mem) :
    VestRule (initialOf state message.currentTarget (holderOf a2))
      (trancheOf state message.currentTarget (holderOf a2)) (cliffOf state message.currentTarget)
      message.blockEnv.timestamp.toNat
      (balanceOf96 state message.currentTarget (holderOf a2)) (a0.toNat % 2 ^ 96) := by
  unfold vest0_ends at h
  rcases h with ⟨h1, h2, h3, h4, -, -⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, -, -⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -, -⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7, -, -⟩ |
      ⟨h1, -, -⟩
  · try simp only [storageAt_readSlot, m160_m160] at h1 h2 h3 h4
    exact vcase0 _ _ _ _ _ h1 h2 h3 h4
  · try simp only [storageAt_readSlot, m160_m160] at h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact vcase1 _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9
  · try simp only [storageAt_readSlot, m160_m160] at h1 h2 h3 h4 h5 h6 h7 h8
    exact vcase2 _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8
  · try simp only [storageAt_readSlot, m160_m160] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact vcase3 _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  · try simp only [storageAt_readSlot, m160_m160] at h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact vcase4 _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9
  · try simp only [storageAt_readSlot, m160_m160] at h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact vcase5 _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9
  · try simp only [storageAt_readSlot, m160_m160] at h1 h2 h3 h4 h5 h6 h7
    exact vcase6 _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7
  · try simp only [storageAt_readSlot, m160_m160] at h1
    exact vcase7 _ _ _ _ _ h1

/-- THE RULE, for the check of `transferFrom` with an allowance (`vest1_ends`). -/
theorem vest1_rule {fork : Fork} {message : Message fork} {state : State.TransactionState}
    {substate : Substate} {gas : Nat} {s : Evm fork Nat} {a0 a1 a2 a3 a4 a5 : U256}
    {mem : ByteArray}
    (h : vest1_ends fork message state substate gas s a0 a1 a2 a3 a4 a5 mem) :
    VestRule (initialOf state message.currentTarget (holderOf a2))
      (trancheOf state message.currentTarget (holderOf a2)) (cliffOf state message.currentTarget)
      message.blockEnv.timestamp.toNat
      (balanceOf96 state message.currentTarget (holderOf a2)) (a0.toNat % 2 ^ 96) := by
  unfold vest1_ends at h
  rcases h with ⟨h1, h2, h3, h4, -, -⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, -, -⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -, -⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7, -, -⟩ |
      ⟨h1, -, -⟩
  · try simp only [storageAt_readSlot, m160_m160] at h1 h2 h3 h4
    exact vcase0 _ _ _ _ _ h1 h2 h3 h4
  · try simp only [storageAt_readSlot, m160_m160] at h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact vcase1 _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9
  · try simp only [storageAt_readSlot, m160_m160] at h1 h2 h3 h4 h5 h6 h7 h8
    exact vcase2 _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8
  · try simp only [storageAt_readSlot, m160_m160] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact vcase3 _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  · try simp only [storageAt_readSlot, m160_m160] at h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact vcase4 _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9
  · try simp only [storageAt_readSlot, m160_m160] at h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact vcase5 _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9
  · try simp only [storageAt_readSlot, m160_m160] at h1 h2 h3 h4 h5 h6 h7
    exact vcase6 _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7
  · try simp only [storageAt_readSlot, m160_m160] at h1
    exact vcase7 _ _ _ _ _ h1

/-- THE RULE, for the check of `transferFrom` from the caller itself (`vest2_ends`). -/
theorem vest2_rule {fork : Fork} {message : Message fork} {state : State.TransactionState}
    {substate : Substate} {gas : Nat} {s : Evm fork Nat} {a0 a1 a2 a3 a4 a5 : U256}
    {mem : ByteArray}
    (h : vest2_ends fork message state substate gas s a0 a1 a2 a3 a4 a5 mem) :
    VestRule (initialOf state message.currentTarget (holderOf a2))
      (trancheOf state message.currentTarget (holderOf a2)) (cliffOf state message.currentTarget)
      message.blockEnv.timestamp.toNat
      (balanceOf96 state message.currentTarget (holderOf a2)) (a0.toNat % 2 ^ 96) := by
  unfold vest2_ends at h
  rcases h with ⟨h1, h2, h3, h4, -, -⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, -, -⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -, -⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -⟩ |
      ⟨h1, h2, h3, h4, h5, h6, h7, -, -⟩ |
      ⟨h1, -, -⟩
  · try simp only [storageAt_readSlot, m160_m160] at h1 h2 h3 h4
    exact vcase0 _ _ _ _ _ h1 h2 h3 h4
  · try simp only [storageAt_readSlot, m160_m160] at h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact vcase1 _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9
  · try simp only [storageAt_readSlot, m160_m160] at h1 h2 h3 h4 h5 h6 h7 h8
    exact vcase2 _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8
  · try simp only [storageAt_readSlot, m160_m160] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact vcase3 _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  · try simp only [storageAt_readSlot, m160_m160] at h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact vcase4 _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9
  · try simp only [storageAt_readSlot, m160_m160] at h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact vcase5 _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9
  · try simp only [storageAt_readSlot, m160_m160] at h1 h2 h3 h4 h5 h6 h7
    exact vcase6 _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7
  · try simp only [storageAt_readSlot, m160_m160] at h1
    exact vcase7 _ _ _ _ _ h1

variable {fork : Fork} {message : Message fork}
variable {state : State.TransactionState} {substate : Substate}
variable {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- THE HEADLINE OF ONDO-4: a successful `transfer(to, amount)` from `caller` satisfies the
vesting rule `VestRule` of the source, read in the state before the call: with
`B = initialOf`, `t = trancheOf`, `c = cliffOf`, `now` the time stamp of the block, `bal` the
balance of `caller`: either `B = 0`, or `c + 60566400 < 2^256` and
`amount <= bal - lockedAt B t c now` (and `lockedAt B t c now <= bal`). Every message runner,
from Berlin. -/
theorem transfer_vesting (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    VestRule (initialOf state message.currentTarget (holderOf message.caller.toU256))
      (trancheOf state message.currentTarget (holderOf message.caller.toU256))
      (cliffOf state message.currentTarget) message.blockEnv.timestamp.toNat
      (balanceOf96 state message.currentTarget (holderOf message.caller.toU256))
      (loadWord message.data 36 32).toNat := by
  obtain ⟨-, -, -, h4, -, htt⟩ := ok_transfer hfork hsize' hsel start hrun hok
  have ha : (loadWord message.data 36 32).toNat < 2 ^ 96 := by
    simp only [c_lt_ne, BitVec.reduceToNat] at h4
    omega
  rw [← Nat.mod_eq_of_lt ha]
  unfold tt0_ends at htt
  rcases htt with ⟨-, -, -, -, -, hv⟩ | ⟨-, -, -, -, hv⟩
  · simpa only [initialOf, trancheOf, cliffOf, balanceOf96, storageAt_readSlot] using vest0_rule hv
  · simpa only [initialOf, trancheOf, cliffOf, balanceOf96, storageAt_readSlot] using vest0_rule hv

/-- The same for a successful `transferFrom(src, dst, amount)`, for the source `src`, read in the
state before the call. When the spender is not `src`, the code writes the allowance slot
`allowances[src][spender]` before the check; `hne1`, `hne2`, `hne3` say that this slot is none
of the three slots that the check reads (keccak separation, NOT proved; the same kind of
hypothesis as `Sep`). -/
theorem transferFrom_vesting (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd)
    (hne1 : mapSlot (holderOf (loadWord message.data 4 32)) 2 ≠
      mapSlot (bitwiseAnd message.caller.toU256 (1461501637330902918203684832716283019655932542975 : U256))
        (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)) 5))
    (hne2 : (1 : U256) ≠
      mapSlot (bitwiseAnd message.caller.toU256 (1461501637330902918203684832716283019655932542975 : U256))
        (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)) 5))
    (hne3 : mapSlot (holderOf (loadWord message.data 4 32)) 6 ≠
      mapSlot (bitwiseAnd message.caller.toU256 (1461501637330902918203684832716283019655932542975 : U256))
        (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)) 5))
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    VestRule (initialOf state message.currentTarget (holderOf (loadWord message.data 4 32)))
      (trancheOf state message.currentTarget (holderOf (loadWord message.data 4 32)))
      (cliffOf state message.currentTarget) message.blockEnv.timestamp.toNat
      (balanceOf96 state message.currentTarget (holderOf (loadWord message.data 4 32)))
      (loadWord message.data 68 32).toNat := by
  have h := ok_transferFrom hfork hsize' hsel start hrun hok
  rcases h with ⟨-, -, -, -, h5, -, -, -, -, hacc, -, htt⟩ | ⟨-, -, -, -, h5, -, -, -, htt⟩ |
      ⟨-, -, -, -, h5, -, -, htt⟩
  · have ha : (loadWord message.data 68 32).toNat < 2 ^ 96 := by
      simp only [c_lt_ne, BitVec.reduceToNat] at h5
      omega
    rw [← Nat.mod_eq_of_lt ha]
    simp only [holderOf] at hne1 hne2 hne3 ⊢
    unfold tt1_ends at htt
    rcases htt with ⟨-, -, -, -, -, hv⟩ | ⟨-, -, -, -, hv⟩
    · have := vest1_rule hv
      simp (disch := repeat' first | assumption | apply UsdtVerify.hasAccount_readSlot) only
        [initialOf, trancheOf, cliffOf, balanceOf96, holderOf, storageAt_readSlot,
        TokenKit.Readable.storageAt_writeSlot_ite, hne1, hne2, hne3, ↓reduceIte] at this
      simpa only [initialOf, trancheOf, cliffOf, balanceOf96] using this
    · have := vest1_rule hv
      simp (disch := repeat' first | assumption | apply UsdtVerify.hasAccount_readSlot) only
        [initialOf, trancheOf, cliffOf, balanceOf96, holderOf, storageAt_readSlot,
        TokenKit.Readable.storageAt_writeSlot_ite, hne1, hne2, hne3, ↓reduceIte] at this
      simpa only [initialOf, trancheOf, cliffOf, balanceOf96] using this
  · have ha : (loadWord message.data 68 32).toNat < 2 ^ 96 := by
      simp only [c_lt_ne, BitVec.reduceToNat] at h5
      omega
    rw [← Nat.mod_eq_of_lt ha]
    unfold tt2_ends at htt
    rcases htt with ⟨-, -, -, -, -, hv⟩ | ⟨-, -, -, -, hv⟩
    · simpa only [initialOf, trancheOf, cliffOf, balanceOf96, storageAt_readSlot] using vest2_rule hv
    · simpa only [initialOf, trancheOf, cliffOf, balanceOf96, storageAt_readSlot] using vest2_rule hv
  · have ha : (loadWord message.data 68 32).toNat < 2 ^ 96 := by
      simp only [c_lt_ne, BitVec.reduceToNat] at h5
      omega
    rw [← Nat.mod_eq_of_lt ha]
    unfold tt2_ends at htt
    rcases htt with ⟨-, -, -, -, -, hv⟩ | ⟨-, -, -, -, hv⟩
    · simpa only [initialOf, trancheOf, cliffOf, balanceOf96, storageAt_readSlot] using vest2_rule hv
    · simpa only [initialOf, trancheOf, cliffOf, balanceOf96, storageAt_readSlot] using vest2_rule hv

end OndoVerify
