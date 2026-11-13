import SkyVerify.Sky.PermitBytes1271
import TokenKit.Evm.Note

/-!
# `permit(owner, spender, value, deadline, bytes signature)` with a signature of 65 bytes

The function with the signature as `bytes` (selector `0x9fd5a6cf`) decodes its last argument to
memory and then runs the code of `permit(owner, spender, value, deadline, v, r, s)` (pc 2287):
the checks, the nonce, the digest, ECRECOVER when the signature has 65 bytes, and the ERC-1271
call to the owner when the recovered address is not the owner.

The run is joined from these parts:

- `Paths.ok_permitBytes` (generated): pc 0 to the CALLDATALOAD of the length word (pc 4202);
- one CALLDATALOAD, at the offset `sigPtr m` that the call data gives (no fixed offset);
- `Paths.ok_permitDecode` (generated): the allocation, up to the CALLDATACOPY (pc 4293);
- `bytes_copy` (here): the CALLDATACOPY of 65 bytes, the zero word after them, the return to
  pc 761 and the jump to pc 2287, with exact gas;
- `Paths.ok_permitBody` (generated): pc 2287 to the call of ECRECOVER (pc 3501);
- `permit_ec` (Sky/Permit.lean): the call of ECRECOVER over the real runner;
- `Paths.ok_permitRecC_ends`, `Paths.ok_permitRecD_ends` (generated) and `permit_contract_C`,
  `permit_contract_D` (Sky/PermitBytes1271.lean): what follows.

The one fact of the call data that is assumed: the length word of the signature is 65
(`hlen`). Nothing is assumed on the offset word: the code reads the length at
`sigPtr m = 4 + offset` and the bytes from `sigPtr m + 32`, wherever that is.

Scope: from Paris and before Glamsterdam; `hdel` as in Sky/Permit.lean. This file is the case
of a length word of 65. For another length the code skips ECRECOVER and asks the owner contract:
that route is proved in Sky/PermitBytesAny.lean (`ok_permitBytes_other`, and
`ok_permitBytes_full` for every length), from `ok_permitBytes_decoded` below, which gives, for
any length, the checks of the decoder and the frame at the CALLDATACOPY.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace SkyVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open SkyVerify.Blocks SkyVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked byteAt)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork}

/-! ## Words of copied call data -/

/-- A word read from bytes that are those of `data` from `s` is the word of `data` at `s`. -/
theorem loadWord_of_bytes {X data : ByteArray} {a s : Nat}
    (h : ∀ i, i < 32 → byteAt X (a + i) = byteAt data (s + i)) :
    loadWord X a 32 = loadWord data s 32 := by
  have e : (List.range 32).map (fun i => byteAt X (a + i)) =
      (List.range 32).map (fun i => byteAt data (s + i)) :=
    List.map_congr_left (fun i hi => h i (List.mem_range.mp hi))
  unfold loadWord bufferRead
  rw [e]

/-- A byte of copied call data. -/
theorem byteAt_copied (data : ByteArray) (f k j : Nat) :
    byteAt (copied data f k) j = if j < k then byteAt data (f + j) else 0 :=
  byteAt_bufferRead data f k j

theorem size_copied_data (data : ByteArray) (f k : Nat) : (copied data f k).size = k := by
  simp [ByteArray.size, bufferRead_length]

/-- The 32 bytes of the word of `data` at `s` are the 32 bytes of `data` from `s`. -/
theorem wordBytes_loadWord_at (data : ByteArray) (s : Nat) :
    wordBytes (loadWord data s 32) = copied data s 32 := by
  have h : loadWord (copied data s 32) 0 32 = loadWord data s 32 :=
    loadWord_of_bytes (fun i hi => by rw [Nat.zero_add, byteAt_copied, if_pos hi])
  rw [← h]
  exact wordBytes_loadWord (size_copied_data data s 32)

/-- A write of copied call data leaves a word that it does not cover. -/
theorem load_rawC {m data : ByteArray} {sz n o f k a : Nat} {w : U256}
    (h : loadWord (memoryReadBytes m a 32) 0 32 = w) (hs : m.size = sz)
    (hfit : o + k ≤ sz + n) (ha : a + 32 ≤ sz) (hd : a + 32 ≤ o ∨ o + k ≤ a) :
    loadWord (memoryReadBytes (memoryWrite (memoryExtend m n) o (copied data f k)) a 32) 0 32 =
      w := by
  rw [memoryReadBytes_memoryWrite_of_disjoint
      (by rw [size_memoryExtend, size_copied_data, hs]; exact hfit)
      (by rw [size_copied_data]; exact hd),
    memoryReadBytes_memoryExtend (by omega)]
  exact h

/-- A word inside copied call data is the word of the call data there. -/
theorem load_copyC {m data : ByteArray} {sz n o f k a j : Nat} (hs : m.size = sz)
    (hfit : o + k ≤ sz + n) (ha : a = o + j) (hj : j + 32 ≤ k) :
    loadWord (memoryReadBytes (memoryWrite (memoryExtend m n) o (copied data f k)) a 32) 0 32 =
      loadWord data (f + j) 32 := by
  subst ha
  have hsz := size_rawC (data := data) (f := f) hs hfit
  apply loadWord_of_bytes
  intro i hi
  rw [Nat.zero_add, byteAt_memoryReadBytes (by rw [hsz]; omega) i, if_pos hi,
    byteAt_memoryWrite (by rw [size_memoryExtend, size_copied_data, hs]; exact hfit),
    if_pos ⟨by omega, by rw [size_copied_data]; omega⟩, byteAt_copied, if_pos (by omega)]
  congr 1
  omega

/-! ## The signature in the call data and in memory -/

/-- Where the call data holds the length word of the signature: 4 and the offset word (the fifth
argument word, at 132). -/
abbrev sigPtr {fork : Fork} (m : Message fork) : U256 :=
  add (4 : U256) (loadWord m.data 132 32)

/-- Where the call data holds the bytes of the signature: 32 after the length word. -/
abbrev sigSrc {fork : Fork} (m : Message fork) : Nat :=
  (add (sigPtr m) (32 : U256)).toNat

/-- `r`: the first word of the signature. -/
abbrev sigR {fork : Fork} (m : Message fork) : U256 := loadWord m.data (sigSrc m) 32

/-- `s`: the second word of the signature. -/
abbrev sigS {fork : Fork} (m : Message fork) : U256 := loadWord m.data (sigSrc m + 32) 32

/-- The third word of the signature: its first byte is `v` (`getByte 0 (sigVw m)`). -/
abbrev sigVw {fork : Fork} (m : Message fork) : U256 := loadWord m.data (sigSrc m + 64) 32

/-- The memory at pc 2287 for a signature of 65 bytes read from `f` of the call data: the free
memory pointer 256, the length 65 at 128, the 65 bytes from 160, and a zero word at 225. -/
abbrev bytesMem (data : ByteArray) (f : Nat) : ByteArray :=
  memoryWrite (memoryExtend
    (memoryWrite (memoryExtend
      (memW [(0 : U256), (0 : U256), (256 : U256), (0 : U256), (65 : U256)]) 96) 160
      (copied data f 65)) 32) 225 (wordBytes (0 : U256))

theorem bytesMem_size (data : ByteArray) (f : Nat) : (bytesMem data f).size = 288 :=
  size_rawW (size_rawC (size_memW5 _ _ _ _ _) (by decide)) (by decide)

theorem bytesMem_word {data : ByteArray} {f i : Nat} {a : Nat} {w : U256} (ha : a = 32 * i)
    (hi : decide (i < 5) = true)
    (hv : wordAt [(0 : U256), (0 : U256), (256 : U256), (0 : U256), (65 : U256)] i = w) :
    loadWord (memoryReadBytes (bytesMem data f) a 32) 0 32 = w := by
  have hi' : i < 5 := of_decide_eq_true hi
  exact load_rawW (load_rawC (memW_load i ha hi hv) (size_memW5 _ _ _ _ _) (by decide)
    (by omega) (.inl (by omega))) (size_rawC (size_memW5 _ _ _ _ _) (by decide)) (by decide)
    (by omega) (.inl (by omega))

theorem bytesMem_sig {data : ByteArray} {f a j : Nat} (ha : a = 160 + j) (hj : j + 32 ≤ 65) :
    loadWord (memoryReadBytes (bytesMem data f) a 32) 0 32 = loadWord data (f + j) 32 :=
  load_rawW (load_copyC (size_memW5 _ _ _ _ _) (by decide) ha hj)
    (size_rawC (size_memW5 _ _ _ _ _) (by decide)) (by decide) (by omega) (.inl (by omega))

theorem bytesMem_top (data : ByteArray) (f : Nat) :
    TopBytes (bytesMem data f) 224 1 (loadWord data (f + 64) 32) := by
  refine top_rawW ?_ (size_rawC (size_memW5 _ _ _ _ _) (by decide)) (by decide) (by decide)
    (.inl (by decide))
  intro i hi
  have h0 : i = 0 := by omega
  subst h0
  rw [byteAt_memoryWrite (by
      rw [size_memoryExtend, size_copied_data, size_memW5]; decide),
    if_pos ⟨by omega, by rw [size_copied_data]; omega⟩, byteAt_copied, if_pos (by omega),
    wordBytes_loadWord_at, byteAt_copied, if_pos (by omega)]

/-! ## From the CALLDATACOPY to the code of `permit` -/

/-- The CALLDATACOPY of the 65 bytes of the signature, the zero word after them, the return of
the decoder to pc 761 and the jump to pc 2287. -/
theorem bytes_copy {p deadline value spender owner size sel nf : U256} {gas : Nat}
    {state : State.TransactionState} {substate : Substate} (hnf : nf = (256 : U256))
    (hg : 105 ≤ gas) :
    Logic.HoareG fork (At CODE message 4293 [(160 : U256), add p (32 : U256), (65 : U256),
        (128 : U256), nf, (65 : U256), (18446744073709551615 : U256), p, (0 : U256), deadline,
        value, spender, owner, (4 : U256), size, (761 : U256), (558 : U256), sel]
        (memW [(0 : U256), (0 : U256), nf, (0 : U256), (65 : U256)]) gas state substate)
      (At CODE message 2287 [(128 : U256), deadline, value, spender, owner, (558 : U256), sel]
        (bytesMem message.data (add p (32 : U256)).toNat) (gas - 105) state substate) := by
  subst hnf
  step calldatacopyK (by code_fact) (by code_fact) (size_memW5 _ _ _ _ _) (c := 9) (n := 96) (by decide +kernel) (o := 160) (by decide +kernel) (f := (add p (32 : U256)).toNat) rfl (k := 65) (by decide +kernel) (w := 3) (by decide +kernel) rfl (by gas_ok)
  step pushR 1 (0 : U256)
  at_pc 4296
  step pushR 1 (32 : U256)
  at_pc 4298
  step dupR 4
  step dupR 3
  step binR 0x01 instruction_add
  step binR 0x01 instruction_add
  step foldK (y := (225 : U256)) (by decide +kernel)
  step mstoreK (by code_fact) (by code_fact) (size_rawC (size_memW5 _ _ _ _ _) (by decide)) (c := 3) (n := 32) (by decide +kernel) (o := 225) (by decide +kernel) rfl (by gas_ok)
  step dupR 0
  step swap6K (by code_fact) (by code_fact) (by gas_ok)
  step popR
  step popR
  step popR
  step popR
  step popR
  step popR
  step swap3K (by code_fact) (by code_fact) (by gas_ok)
  step swap6K (by code_fact) (by code_fact) (by gas_ok)
  step popR
  step swap3K (by code_fact) (by code_fact) (by gas_ok)
  step swap6K (by code_fact) (by code_fact) (by gas_ok)
  step swap1K (by code_fact) (by code_fact) (by gas_ok)
  step swap4K (by code_fact) (by code_fact) (by gas_ok)
  step popR
  step jumpR
  at_pc 761
  step jumpdestR
  step pushR 2 (2287 : U256)
  at_pc 765
  step jumpR
  exact hoareL (restate (by decide) rfl rfl (by gas_ok) rfl rfl)

/-! ## Any length: the decoder -/

/-- The length word of the signature, as the code reads it. -/
abbrev sigLen {fork : Fork} (m : Message fork) : U256 := loadWord m.data (sigPtr m).toNat 32

/-- The free memory pointer after the allocation of a `bytes` of length `len` at 128:
`128 + ((63 + ((len + 31) & ~31)) & ~31)`. -/
abbrev sigFree (len : U256) : U256 :=
  add (128 : U256) (bitwiseAnd (add (63 : U256) (bitwiseAnd
    (115792089237316195423570985008687907853269984665640564039457584007913129639904 : U256)
    (add len (31 : U256))))
    (115792089237316195423570985008687907853269984665640564039457584007913129639904 : U256))

/-- For a signature of any length, under any runner of calls: a run of `permit` with a signature
as bytes that ends with no error passed the checks of the decoder (no value, 164 bytes of call
data or more, clean address words, an offset word and a length word of at most 2^64 - 1, the
length word and the bytes inside the call data), 711 gas was there, and the run went on from
the CALLDATACOPY of the signature (pc 4293) with the stack and the memory below. What follows
for a length that is not 65 (the copy, then the ERC-1271 call with the bytes as given) is in
Sky/PermitBytesAny.lean (`ok_permitBytes_other`). -/
theorem ok_permitBytes_decoded {state : State.TransactionState} {substate : Substate}
    {bound : Nat} {runChild : MessageRunner fork Nat bound}
    (hberlin : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x9fd5a6cf)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    isZero message.value ≠ 0 ∧
    isZero (signedLessThan (sub (BitVec.ofNat 256 message.data.size) (4 : U256))
      (160 : U256)) ≠ 0 ∧
    equal (loadWord message.data 4 32) (bitwiseAnd (loadWord message.data 4 32) ADDR_MASK) ≠ 0 ∧
    equal (loadWord message.data 36 32)
      (bitwiseAnd (loadWord message.data 36 32) ADDR_MASK) ≠ 0 ∧
    isZero (greaterThan (loadWord message.data 132 32) (18446744073709551615 : U256)) ≠ 0 ∧
    signedLessThan (add (sigPtr message) (31 : U256))
      (BitVec.ofNat 256 message.data.size) ≠ 0 ∧
    isZero (greaterThan (sigLen message) (18446744073709551615 : U256)) ≠ 0 ∧
    isZero (greaterThan (add (add (sigPtr message) (sigLen message)) (32 : U256))
      (BitVec.ofNat 256 message.data.size)) ≠ 0 ∧
    711 ≤ gas ∧
    ∃ z : Evm fork Nat,
      At CODE message 4293 [(160 : U256), add (sigPtr message) (32 : U256), sigLen message,
        (128 : U256), sigFree (sigLen message), sigLen message, (18446744073709551615 : U256),
        sigPtr message, (0 : U256), loadWord message.data 100 32, loadWord message.data 68 32,
        loadWord message.data 36 32, loadWord message.data 4 32, (4 : U256),
        BitVec.ofNat 256 message.data.size, (761 : U256), (558 : U256),
        BitVec.ofNat 256 (selector message.data)]
        (memW [(0 : U256), (0 : U256), sigFree (sigLen message), (0 : U256), sigLen message])
        (gas - 711) state substate z ∧
      EndsL runChild z s := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hg0, z0, hz0, hend0⟩ :=
    Paths.ok_permitBytes hberlin hsize' hsel start hrun hok
  obtain ⟨hg1, z1, hz1, hend1⟩ := ok_splitLE (B := 3) (c := 3) (Nat.le_refl _)
    (fun g hg => hoareL (Gas.calldataloadG (by code_fact) (by code_fact) hg)) hz0 hend0 hok
  obtain ⟨hc7, -, hc8, hg2, z2, hz2, hend2⟩ := Paths.ok_permitDecode hberlin hz1 hend1 hok
  have eg : gas - 513 - 3 - 195 = gas - 711 := by omega
  rw [eg] at hz2
  exact ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, by omega, z2, hz2, hend2⟩

/-! ## The whole function -/

/-- The checks of `permit` with a signature as bytes, before the nonce is written: no value, 164
bytes of call data or more, clean address words for owner and spender, an offset word of at
most 2^64 - 1, the length word inside the call data, the 65 bytes inside the call data, the
deadline not passed, a nonzero owner. -/
structure PermitBytes65Checks {fork : Fork} (m : Message fork) : Prop where
  value : isZero m.value ≠ 0
  size : isZero (signedLessThan (sub (BitVec.ofNat 256 m.data.size) (4 : U256))
    (160 : U256)) ≠ 0
  owner : equal (loadWord m.data 4 32) (bitwiseAnd (loadWord m.data 4 32) ADDR_MASK) ≠ 0
  spender : equal (loadWord m.data 36 32) (bitwiseAnd (loadWord m.data 36 32) ADDR_MASK) ≠ 0
  offset : isZero (greaterThan (loadWord m.data 132 32) (18446744073709551615 : U256)) ≠ 0
  lengthIn : signedLessThan (add (sigPtr m) (31 : U256)) (BitVec.ofNat 256 m.data.size) ≠ 0
  bytesIn : isZero (greaterThan (add (add (sigPtr m) (65 : U256)) (32 : U256))
    (BitVec.ofNat 256 m.data.size)) ≠ 0
  deadline : isZero (greaterThan m.blockEnv.timestamp (loadWord m.data 100 32)) ≠ 0
  nonzero : permitOwner m ≠ 0

theorem gas_shift {G : Nat} (h : 128 ≤ G) : G - 128 + 23 ≤ G + 23 - 128 := by omega

/-- `PermitKept` from more gas: its gas is an inequality. (Before audit 4 this was
`permitByContract_mono`; `PermitByContract` now gives the gas at the STATICCALL exactly, so it
is not monotone, and `ok_permitBytes65_full` uses the equality `gas_shift_eq`.) -/
theorem permitKept_mono {st : State.TransactionState} {ss : Substate} {g g' : Nat}
    {s : Evm fork Nat} {owner spender value : U256} (hle : g ≤ g')
    (h : PermitKept fork message st ss g s owner spender value) :
    PermitKept fork message st ss g' s owner spender value := by
  unfold PermitKept at h ⊢
  obtain ⟨c, out, st', ss', g0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨c, out, st', ss', g0, h1, h2, h3, h4, h5, h6, h7, h8, h9, by omega, h11⟩

theorem gas_shift_eq {G : Nat} (h : 128 ≤ G) : G - 128 + 23 = G + 23 - 128 := by omega

/-- The code of `permit` with a signature of 65 bytes, from the call of ECRECOVER on. 816 gas
pays the decoder up to pc 2287; then the gas `permitCost1 c` of the code before the call was
there (`c` is 958 when the chain id is 1 and 1354 else), the call had 3000 gas, and the run ended
as `PermitEnd` says from the state and the substate after the call, with the recovered word
`recoveredWord (permitInput digest v r s)` for `r`, `s` and `v` read from the signature.

The gas given to `PermitEnd` is the gas after the call and 23: `PermitEnd` counts 2190 gas for
the last part of `permit(v, r, s)`, and this entry uses 23 less there (2167). The gas at the end
of the signature path is so exact: `ecGas .. - (2167 + the write)`. For the same reason the `k`
of `PermitEnd` is 1315 here (1292 and 23): on the ERC-1271 path the gas left at the STATICCALL
to the owner is the gas at the EXTCODESIZE less the access cost and 1292. The call data of that
call is `erc1271Input` of the digest and of `r`, `s` and the first byte of the third word, read
from the signature. -/
def PermitBytes65AfterEc (fork : Fork) (bound : Nat) (m : Message fork)
    (state : State.TransactionState) (substate : Substate) (gas : Nat) (s : Evm fork Nat)
    (c : Nat) (domain : U256) : Prop :=
  816 ≤ gas ∧
  permitCost1 c fork m state substate ≤ gas - 816 ∧
  3000 ≤ (permitCall fork (permitSub1 fork m state substate)
    (gas - 816 - permitCost1 c fork m state substate)).subCall ∧
  PermitEnd fork bound m (ecState m (permitState1 m state))
    (ecSub (permitSub1 fork m state substate))
    (ecGas fork (permitSub1 fork m state substate)
      (gas - 816 - permitCost1 c fork m state substate) + 23)
    s 1315 (permitDigest domain (permitStruct m state)) (sigR m) (sigS m) (sigVw m)
    (loadWord m.data 4 32) (loadWord m.data 36 32) (loadWord m.data 68 32)
    (recoveredWord (permitInput (permitDigest domain (permitStruct m state))
      (getByte (0 : U256) (sigVw m)) (sigR m) (sigS m)))

/-- Completeness for `permit(owner, spender, value, deadline, bytes signature)` (selector
`0x9fd5a6cf`) with a signature of 65 bytes, over the real runner (`processRunner`), from Paris
and before Glamsterdam, with no assumption on ECRECOVER and none on the code of the owner.

A run of a fresh frame of the code, on a message whose signature length word is 65 (`hlen`),
that ends with no error passed the checks (`PermitBytes65Checks`), was not static, the token
account exists, and it ended as `PermitEnd` says after the call of ECRECOVER
(`PermitBytes65AfterEc`): by the signature path with exact gas, or by the ERC-1271 path with a gas
inequality. -/
theorem ok_permitBytes65_full {state : State.TransactionState} {substate : Substate}
    (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x9fd5a6cf)
    (hlen : loadWord message.data (sigPtr message).toNat 32 = (65 : U256))
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    PermitBytes65Checks message ∧ message.isStatic = false ∧
    hasAccount state message.currentTarget ∧
    ((equal (1 : U256) (BitVec.ofNat 256 message.blockEnv.chainId.toNat) = 0 ∧
        PermitBytes65AfterEc fork bound message state substate gas s 1354
          (permitDomain message)) ∨
      (equal (1 : U256) (BitVec.ofNat 256 message.blockEnv.chainId.toNat) ≠ 0 ∧
        PermitBytes65AfterEc fork bound message state substate gas s 958 DOMAIN_MAINNET)) := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hd1 := hdel_state1 (message := message) hdel
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hg0, z0, hz0, hend0⟩ :=
    Paths.ok_permitBytes hberlin hsize' hsel start ⟨within, hrun⟩ hok
  obtain ⟨hg1, z1, hz1, hend1⟩ := ok_splitLE (B := 3) (c := 3) (Nat.le_refl _)
    (fun g hg => hoareL (Gas.calldataloadG (by code_fact) (by code_fact) hg)) hz0 hend0 hok
  rw [hlen] at hz1
  obtain ⟨-, -, hc7, hg2, z2, hz2, hend2⟩ := Paths.ok_permitDecode hberlin hz1 hend1 hok
  obtain ⟨hg3, z3, hz3, hend3⟩ := ok_splitLE (B := 105) (c := 105) (Nat.le_refl _)
    (fun g hg => bytes_copy (by decide +kernel) hg) hz2 hend2 hok
  have eg : gas - 513 - 3 - 195 - 105 = gas - 816 := by omega
  rw [eg] at hz3
  have hG : 816 ≤ gas := by omega
  have b0 := bytesMem_size message.data (sigSrc message)
  have b64 : loadWord (memoryReadBytes (bytesMem message.data (sigSrc message)) 64 32) 0 32 =
      (256 : U256) := bytesMem_word (i := 2) rfl rfl rfl
  have b96 : loadWord (memoryReadBytes (bytesMem message.data (sigSrc message)) 96 32) 0 32 =
      (0 : U256) := bytesMem_word (i := 3) rfl rfl rfl
  have b128 : loadWord (memoryReadBytes (bytesMem message.data (sigSrc message)) 128 32) 0 32 =
      (65 : U256) := bytesMem_word (i := 4) rfl rfl rfl
  have b160 : loadWord (memoryReadBytes (bytesMem message.data (sigSrc message)) 160 32) 0 32 =
      sigR message := bytesMem_sig (j := 0) rfl (by decide)
  have b192 : loadWord (memoryReadBytes (bytesMem message.data (sigSrc message)) 192 32) 0 32 =
      sigS message := bytesMem_sig (j := 32) rfl (by decide)
  have btop := bytesMem_top message.data (sigSrc message)
  rcases Paths.ok_permitBody hberlin b0 b64 b96 b128 b160 b192 btop hz3 hend3 hok with
    ⟨hc8, hc9, hchain, hst, hacc, hcg, z, hz, w, hzr⟩ |
    ⟨hc8, hc9, hchain, hst, hacc, hcg, z, hz, w, hzr⟩
  · refine ⟨⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9⟩, hst, hacc, .inl ⟨hchain, hG, hcg, ?_⟩⟩
    obtain ⟨m0, m64, -, -, w96, w128, w160, w192, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, w898, w930, w962, w994, w1026, t224, -⟩ :=
      Paths.permitBody_p3_mem (message := message) (state := state)
        (deadline := loadWord message.data 100 32) (value := loadWord message.data 68 32)
        (spender := loadWord message.data 36 32) (owner := loadWord message.data 4 32)
        (sel := BitVec.ofNat 256 (selector message.data)) b0 b64 b96 b128 b160 b192 btop
    obtain ⟨hg, M', after, hsz', hsame, hrec, hat, hend⟩ :=
      permit_ec hparis hglam (f := 930) (o := 898) rfl (by rw [m0]; decide) (by decide) w898
        (by simp [STACK_LIMIT]) hd1 hz w hzr hok
    have hdata := read4_raw w930 w962 w994 w1026 m0 (by decide)
    rw [hdata] at hrec
    have L : ∀ {a : Nat} {x : U256}, (a + 32 ≤ 898 ∨ 898 + 32 ≤ a) →
        loadWord (memoryReadBytes _ a 32) 0 32 = x →
        loadWord (memoryReadBytes M' a 32) 0 32 = x :=
      fun hd h => (congrArg (loadWord · 0 32) (hsame _ 32 hd)).trans h
    have t' := top_same hsame hsz' t224 (.inl (by decide)) (by rw [m0]; decide)
    have pm : PermitMem M' 1088 (930 : U256) _ _ _ :=
      ⟨hsz'.trans m0, L (.inl (by decide)) m64, L (.inl (by decide)) w96,
        L (.inl (by decide)) w128, L (.inl (by decide)) w160, L (.inl (by decide)) w192, t'⟩
    refine ⟨hg, ?_⟩
    rcases Paths.ok_permitRecD_ends hberlin pm.size pm.fp pm.w96 pm.w128 pm.w160
        pm.w192 hrec pm.top hat hend hok with ⟨hsub, r⟩ | ⟨hsub, hg', zc, hzc, hendc⟩
    · exact .inl ⟨hsub, permitWrites_shift (c := 2167) (by omega) r⟩
    · exact .inr ⟨hsub, Nat.le_trans hg' (Nat.le_add_right _ _),
        gas_shift_eq hg' ▸ permit_contract_D hparis hglam pm hzc hendc hok⟩
  · refine ⟨⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9⟩, hst, hacc, .inr ⟨hchain, hG, hcg, ?_⟩⟩
    obtain ⟨m0, m64, -, -, w96, w128, w160, w192, -, -, -, -, -, -, -, -, -, -, w578, w610,
      w642, w674, w706, t224, -⟩ :=
      Paths.permitBody_p5_mem (message := message) (state := state)
        (deadline := loadWord message.data 100 32) (value := loadWord message.data 68 32)
        (spender := loadWord message.data 36 32) (owner := loadWord message.data 4 32)
        (sel := BitVec.ofNat 256 (selector message.data)) b0 b64 b96 b128 b160 b192 btop
    obtain ⟨hg, M', after, hsz', hsame, hrec, hat, hend⟩ :=
      permit_ec hparis hglam (f := 610) (o := 578) rfl (by rw [m0]; decide) (by decide) w578
        (by simp [STACK_LIMIT]) hd1 hz w hzr hok
    have hdata := read4_raw w610 w642 w674 w706 m0 (by decide)
    rw [hdata] at hrec
    have L : ∀ {a : Nat} {x : U256}, (a + 32 ≤ 578 ∨ 578 + 32 ≤ a) →
        loadWord (memoryReadBytes _ a 32) 0 32 = x →
        loadWord (memoryReadBytes M' a 32) 0 32 = x :=
      fun hd h => (congrArg (loadWord · 0 32) (hsame _ 32 hd)).trans h
    have t' := top_same hsame hsz' t224 (.inl (by decide)) (by rw [m0]; decide)
    have pm : PermitMem M' 768 (610 : U256) _ _ _ :=
      ⟨hsz'.trans m0, L (.inl (by decide)) m64, L (.inl (by decide)) w96,
        L (.inl (by decide)) w128, L (.inl (by decide)) w160, L (.inl (by decide)) w192, t'⟩
    refine ⟨hg, ?_⟩
    rcases Paths.ok_permitRecC_ends hberlin pm.size pm.fp pm.w96 pm.w128 pm.w160
        pm.w192 hrec pm.top hat hend hok with ⟨hsub, r⟩ | ⟨hsub, hg', zc, hzc, hendc⟩
    · exact .inl ⟨hsub, permitWrites_shift (c := 2167) (by omega) r⟩
    · exact .inr ⟨hsub, Nat.le_trans hg' (Nat.le_add_right _ _),
        gas_shift_eq hg' ▸ permit_contract_C hparis hglam pm hzc hendc hok⟩

/-- The `permit` with a signature of 65 bytes, when the recovered address is not the owner (for
the domain separator of either layout) and the owner holds no code in the state after the call
of ECRECOVER, never ends with no error: the ERC-1271 path needs code at the owner. This is
`permit_no_code_fails` for the selector `0x9fd5a6cf` and a signature length word of 65
(`hlen`); for another length see `permitBytes_other_no_code_fails` (Sky/PermitBytesAny.lean). -/
theorem permitBytes65_no_code_fails {state : State.TransactionState} {substate : Substate}
    (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x9fd5a6cf)
    (hlen : loadWord message.data (sigPtr message).toNat 32 = (65 : U256))
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    (hrec : ∀ domain : U256,
      sub (bitwiseAnd ADDR_MASK (loadWord message.data 4 32))
        (bitwiseAnd ADDR_MASK (recoveredWord (permitInput
          (permitDigest domain (permitStruct message state)) (getByte (0 : U256) (sigVw message))
          (sigR message) (sigS message)))) ≠ 0)
    (hcode : ∀ c, (ecState message (permitState1 message state)).getCode
      ((ecState message (permitState1 message state)).getAccount
        (toAddressMasked (bitwiseAnd (loadWord message.data 4 32) ADDR_MASK))).codeHash = .ok c →
      c.size = 0)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s) :
    s.error ≠ none := by
  intro hok
  obtain ⟨-, -, -, hlay⟩ :=
    ok_permitBytes65_full hparis hglam hsize' hsel hlen hdel start within hrun hok
  rcases hlay with ⟨-, hA⟩ | ⟨-, hA⟩
  · unfold PermitBytes65AfterEc at hA
    obtain ⟨-, -, -, hend⟩ := hA
    exact permitEnd_no_code (hrec _) hcode hend
  · unfold PermitBytes65AfterEc at hA
    obtain ⟨-, -, -, hend⟩ := hA
    exact permitEnd_no_code (hrec _) hcode hend

end SkyVerify
