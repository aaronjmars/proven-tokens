import DaiVerify.Dai.Gen
import TokenKit.Evm.Precompile

/-!
# `permit` under EthLib's real runner

`permit(holder, spender, nonce, expiry, allowed, v, r, s)` (selector `0x8fcbaf0c`) builds an
EIP-712 digest in memory, calls the precompile at address 1 (ECRECOVER) with STATICCALL, and
compares the address it gets with `holder`. The generated paths stop at the frame before
`GAS STATICCALL` (pc 5335, `Paths.ok_permit`) and start again after it (pc 5337,
`Paths.ok_permitTail`). This file joins the two across the call, for `processRunner`, with no
assumption on what the precompile returns: the output is EthLib's own
`Precompiles.Ecrecover.compute` (through `TokenKit.recoveredWord`).

- `permitStruct`, `permitDigest`, `permitInput`: the struct hash, the digest and the 128 bytes
  given to ECRECOVER, as the code builds them.
- `digest_bytes`: the 66 bytes that the code hashes are `0x19 0x01`, the domain separator of
  storage slot 5, and the struct hash.
- `permit_call`: from the frame at pc 5335 with a memory that holds the four input words, a run
  of the real runner that ends with no error made the call with at least 3000 gas and ended as
  `Paths.permitTail_ends` says, with the recovered word `recoveredWord (permitInput ...)`.
- `ok_permit_real`: completeness for `permit`. A run of a fresh frame of `CODE` on a `permit`
  message that ends with no error: no value, at least 260 bytes of call data, a nonzero holder,
  and the end of `Paths.permitTail_ends` (the recovered word equals the holder, the expiry and
  the nonce checks, the two exact storage writes, the Approval log and the exact gas).

Scope: from Paris and before Glamsterdam (EthLib's rules of STATICCALL; from Paris a message
does not touch its target). `hdel`: the account at address 1 holds no EIP-7702 delegation code
(a fact of the state, true on chain: precompile accounts hold no code).
-/

set_option maxRecDepth 4096

namespace DaiVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open DaiVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

/-- `PERMIT_TYPEHASH` of the contract. -/
def PERMIT_TYPEHASH : U256 :=
  105916522785188513640362517802612480037966763957092682311465172263008277174987

/-- The struct hash: keccak of the type hash and the five arguments, one word each. -/
def permitStruct (holder spender nonce expiry allowed : U256) : U256 :=
  keccak (memW [PERMIT_TYPEHASH, holder, spender, nonce, expiry, allowed])

/-- The digest: keccak of `0x19 0x01`, the domain separator and the struct hash. -/
def permitDigest (domain structHash : U256) : U256 :=
  keccak (⟨#[0x19, 0x01]⟩ ++ wordBytes domain ++ wordBytes structHash)

/-- The 128 bytes given to ECRECOVER: the digest, `v`, `r` and `s`. -/
def permitInput (digest v r s : U256) : ByteArray :=
  wordBytes digest ++ wordBytes v ++ wordBytes r ++ wordBytes s

/-- The word `0x1901` shifted to the top of a word, as the code writes it at 0x180. -/
def P1901 : U256 :=
  11309588061646438093662687302255421419811724423900836950936401294474059186176

/-- The first two bytes of a memory of words whose word 12 is `P1901`, from 0x180. -/
theorem prefix1901 {ws : List U256} (hlen : 32 * ws.length = 416)
    (hP : loadWord (memoryReadBytes (memW ws) 384 32) 0 32 = P1901) :
    memoryReadBytes (memW ws) 384 2 = ⟨#[0x19, 0x01]⟩ := by
  have hsz : (memW ws).size = 416 := size_memWn ws hlen
  have hw : memoryReadBytes (memW ws) 384 32 = wordBytes P1901 :=
    readWord_raw hP hsz (by decide)
  have f2 : 384 + 2 ≤ (memW ws).size := by rw [hsz]; decide
  have f32 : 384 + 32 ≤ (memW ws).size := by rw [hsz]; decide
  apply EthLib.Base.eq_of_byteAt
  · rw [size_memoryReadBytes f2]
    rfl
  · intro i
    rw [byteAt_memoryReadBytes f2]
    by_cases h : i < 2
    · rw [if_pos h]
      have hb : EthLib.Base.byteAt (memW ws) (384 + i) =
          EthLib.Base.byteAt (wordBytes P1901) i := by
        rw [← hw, byteAt_memoryReadBytes f32, if_pos (by omega)]
      rw [hb]
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hi with rfl | rfl <;> decide +kernel
    · rw [if_neg h]
      exact (EthLib.Base.byteAt_of_size_le (by show 2 ≤ i; omega)).symm

/-- The 66 bytes that `permit` hashes for the digest: `0x19 0x01`, the domain separator and the
struct hash. The memory is the one the code has built at that point: 13 words, then the writes
of the domain separator at 0x182, of the struct hash at 0x1a2, of the length at 0x160 and of the
free memory pointer. -/
theorem digest_bytes {ws : List U256} {DS SH a b : U256} (hlen : 32 * ws.length = 416)
    (hP : loadWord (memoryReadBytes (memW ws) 384 32) 0 32 = P1901) :
    memoryReadBytes (memoryWrite (memoryExtend (memoryWrite (memoryExtend (memoryWrite
      (memoryExtend (memoryWrite (memoryExtend (memW ws) 32) 386 (wordBytes DS)) 32) 418
      (wordBytes SH)) 0) 352 (wordBytes a)) 0) 64 (wordBytes b)) 384 66 =
      ⟨#[0x19, 0x01]⟩ ++ wordBytes DS ++ wordBytes SH := by
  have s0 : (memW ws).size = 416 := size_memWn ws hlen
  have s1 := size_rawW (v := DS) (n := 32) (o := 386) s0 (by decide)
  have s2 := size_rawW (v := SH) (n := 32) (o := 418) s1 (by decide)
  have s3 := size_rawW (v := a) (n := 0) (o := 352) s2 (by decide)
  rw [read_rawW s3 (by decide) (by decide) (by decide),
    read_rawW s2 (by decide) (by decide) (by decide)]
  refine (memoryReadBytes_add (j := 34) (k := 32) (by rw [s2]; decide) (by decide)
    (by decide)).trans ?_
  have hSH := readWord_raw (load_rawW_self (v := SH) (n := 32) (o := 418) s1 (by decide)) s2
    (by decide)
  have hDS := readWord_raw (load_rawW_self (v := DS) (n := 32) (o := 386) s0 (by decide)) s1
    (by decide)
  have h34 : memoryReadBytes (memoryWrite (memoryExtend (memoryWrite (memoryExtend (memW ws) 32)
      386 (wordBytes DS)) 32) 418 (wordBytes SH)) 384 34 =
      ⟨#[0x19, 0x01]⟩ ++ wordBytes DS := by
    rw [read_rawW s1 (by decide) (by decide) (by decide)]
    refine (memoryReadBytes_add (j := 2) (k := 32) (by rw [s1]; decide) (by decide)
      (by decide)).trans ?_
    rw [read_rawW s0 (by decide) (by decide) (by decide), prefix1901 hlen hP]
    exact congrArg (⟨#[0x19, 0x01]⟩ ++ ·) hDS
  rw [h34]
  exact congrArg ((⟨#[0x19, 0x01]⟩ : ByteArray) ++ wordBytes DS ++ ·) hSH

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The gas of the call of ECRECOVER from a frame with `gas` at GAS, and what the caller pays:
EthLib's `messageCallGas` for the gas that GAS pushed, no memory growth, and the access of
address 1. -/
abbrev permitCall (fork : Fork) (substate : Substate) (gas : Nat) :=
  messageCallGas fork 0 (BitVec.ofNat 256 (gas - 2)).toNat (gas - 2) 0
    (callBaseCost fork (decide (toAddressMasked 1 ∉ substate.accessedAddresses)) +
      routeCost fork (substate.accessedAddresses.insert (toAddressMasked 1)) none)

/-- From Paris and before Glamsterdam, under the real runner: a run from the frame of `permit`
before `GAS STATICCALL` (pc 5335), with a memory of 640 bytes that holds the digest, `v`, `r`
and `s` at 482 and 0 at the output word 450, that ends with no error.

The call of ECRECOVER got at least 3000 gas, and the run ended as `Paths.permitTail_ends` says
from the frame after the call: the state with the reads of the call recorded, the substate with
address 1 accessed, the gas left after the call, and the recovered word
`recoveredWord (permitInput digest v r s)`. -/
theorem permit_call (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    {dg sS sR sV allowed expiry nonce spender holder sel v : U256} {M : ByteArray} {gas : Nat}
    (hsz : M.size = 640) (hfp : loadWord (memoryReadBytes M 64 32) 0 32 = (482 : U256))
    (h450 : loadWord (memoryReadBytes M 450 32) 0 32 = (0 : U256))
    (h482 : loadWord (memoryReadBytes M 482 32) 0 32 = dg)
    (h514 : loadWord (memoryReadBytes M 514 32) 0 32 = v)
    (h546 : loadWord (memoryReadBytes M 546 32) 0 32 = sR)
    (h578 : loadWord (memoryReadBytes M 578 32) 0 32 = sS)
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    {bound : Nat} {z s : Evm fork Nat}
    (start : At CODE message 5335 [(1 : U256), (482 : U256), (128 : U256), (450 : U256),
      (32 : U256), (610 : U256), (1 : U256), dg, sS, sR, sV, allowed, expiry, nonce, spender,
      holder, (1437 : U256), sel] M gas state substate z)
    (within : GasMeter.gasHeld z.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) z
      within = .ok s)
    (hok : s.error = none) :
    3000 ≤ (permitCall fork substate gas).subCall ∧
    Paths.permitTail_ends fork message
      ((state.recordAccountRead (toAddressMasked 1)).recordAccountRead message.currentTarget)
      { substate with
        accessedAddresses := substate.accessedAddresses.insert (toAddressMasked 1) }
      (gas - 2 - ((permitCall fork substate gas).cost + 0) +
        ((permitCall fork substate gas).subCall - 3000))
      s dg sS sR sV allowed expiry nonce spender holder sel
      (recoveredWord (permitInput dg v sR sS)) := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have t482 : (482 : U256).toNat = 482 := by decide
  have t128 : (128 : U256).toNat = 128 := by decide
  have t450 : (450 : U256).toNat = 450 := by decide
  have t32 : (32 : U256).toNat = 32 := by decide
  have hE : extendMemory M.size [((482 : U256), (128 : U256)), ((450 : U256), (32 : U256))] =
      ⟨0, 0⟩ := extendMemory_two (by rw [hsz]; decide) (by rw [hsz]; decide)
  obtain ⟨hg, after, hat, w, hr⟩ := ecrecover_call_ok hparis hglam (q := 5337) rfl
    (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by simp [STACK_LIMIT]) hdel start within hrun hok
  rw [hE] at hg hat
  simp only [memoryExtend_zero, t482, t128, t450, t32] at hat
  have hdata : memoryReadBytes M 482 128 = permitInput dg v sR sS :=
    read4_raw h482 h514 h546 h578 hsz (by decide)
  rw [hdata] at hat
  have hfit : 450 + 32 ≤ M.size := by rw [hsz]; decide
  refine ⟨hg, ?_⟩
  exact Paths.ok_permitTail_ends hberlin
    ((size_ecrecover_write _ hfit).trans hsz)
    ((congrArg (loadWord · 0 32) (read_ecrecover_other _ hfit (.inl (by decide)))).trans hfp)
    (load_ecrecover _ hfit h450) hat ⟨w, hr⟩ hok

/-- Completeness for `permit`, under EthLib's real runner, from Paris and before Glamsterdam.

A run of a fresh frame of `CODE` on a message with the selector of `permit` that ends with no
error: the message carries no value, its call data holds the eight arguments, the holder is not
zero, the gas covered the code before the call and 3000 for ECRECOVER, and the run ended as
`Paths.permitTail_ends` says. That predicate (generated, `Gen/PPermitTail.lean`) has the checks
after the call (the recovered word equals the holder, the expiry against the time stamp of the
block, the nonce against storage), the two exact storage writes (nonce and allowance), the
Approval log and the exact gas, for each of the four ways to succeed.

The recovered word is `recoveredWord` of the 128 bytes `permitInput digest v r s`, where the
digest is `permitDigest` of the domain separator in storage slot 5 and of `permitStruct` of the
arguments. `recoveredWord` is EthLib's `Precompiles.Ecrecover.compute` read as a word: nothing
is assumed about it. -/
theorem ok_permit_real (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x8fcbaf0c)
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    isZero message.value ≠ 0 ∧
    isZero (lessThan (sub (BitVec.ofNat 256 message.data.size) (4 : U256)) (256 : U256)) ≠ 0 ∧
    isZero (equal (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (loadWord message.data 4 32))) (0 : U256)) ≠ 0 ∧
    1219 + slotCost (coldIn substate message.currentTarget (5 : U256)) ≤ gas ∧
    3000 ≤ (permitCall fork (accessSlot substate message.currentTarget (5 : U256))
      (gas - (1219 + slotCost (coldIn substate message.currentTarget (5 : U256))))).subCall ∧
    Paths.permitTail_ends fork message
      (((readSlot state message.currentTarget (5 : U256)).recordAccountRead
        (toAddressMasked 1)).recordAccountRead message.currentTarget)
      { accessSlot substate message.currentTarget (5 : U256) with
        accessedAddresses := (accessSlot substate message.currentTarget
          (5 : U256)).accessedAddresses.insert (toAddressMasked 1) }
      (gas - (1219 + slotCost (coldIn substate message.currentTarget (5 : U256))) - 2 -
        ((permitCall fork (accessSlot substate message.currentTarget (5 : U256))
          (gas - (1219 + slotCost (coldIn substate message.currentTarget (5 : U256))))).cost + 0) +
        ((permitCall fork (accessSlot substate message.currentTarget (5 : U256))
          (gas - (1219 + slotCost (coldIn substate message.currentTarget (5 : U256))))).subCall - 3000))
      s
      (permitDigest (storageAt state message.currentTarget (5 : U256))
        (permitStruct
          (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
            (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
              (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
                (loadWord message.data 4 32))))
          (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
            (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
              (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
                (loadWord message.data 36 32))))
          (loadWord message.data 68 32) (loadWord message.data 100 32)
          (isZero (isZero (isZero (isZero (isZero (isZero (loadWord message.data 132 32)))))))))
      (loadWord message.data 228 32) (loadWord message.data 196 32)
      (bitwiseAnd (255 : U256) (loadWord message.data 164 32))
      (isZero (isZero (loadWord message.data 132 32)))
      (loadWord message.data 100 32) (loadWord message.data 68 32)
      (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (loadWord message.data 36 32))
      (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (loadWord message.data 4 32))
      (BitVec.ofNat 256 (selector message.data))
      (recoveredWord (permitInput
        (permitDigest (storageAt state message.currentTarget (5 : U256))
        (permitStruct
          (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
            (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
              (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
                (loadWord message.data 4 32))))
          (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
            (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
              (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
                (loadWord message.data 36 32))))
          (loadWord message.data 68 32) (loadWord message.data 100 32)
          (isZero (isZero (isZero (isZero (isZero (isZero (loadWord message.data 132 32)))))))))
        (bitwiseAnd (255 : U256) (bitwiseAnd (255 : U256) (bitwiseAnd (255 : U256)
          (loadWord message.data 164 32))))
        (loadWord message.data 196 32) (loadWord message.data 228 32))) := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  obtain ⟨hc1, hc2, hc3, hcg, z, hz, w, hzr⟩ :=
    Paths.ok_permit hberlin hsize' hsel start ⟨within, hrun⟩ hok
  obtain ⟨m0, m64, -, -, -, -, -, -, -, -, -, -, -, -, -, m450, m482, m514, m546, m578⟩ :=
    Paths.permit_p3_mem (message := message) (state := state)
  have core := permit_call hparis hglam m0 m64 m450 m482 m514 m546 m578
    (state := readSlot state message.currentTarget (5 : U256)) (fun c h => hdel c h) hz w hzr hok
  rw [digest_bytes (ws := _) (by rfl) (memW_load 12 (by rfl) (by rfl) (by rfl))] at core
  exact ⟨hc1, hc2, hc3, hcg, core.1, core.2⟩

end DaiVerify
