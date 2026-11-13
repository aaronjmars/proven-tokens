import SkyVerify.Sky.Gen
import TokenKit.Evm.Precompile
import TokenKit.Evm.Call

/-!
# `permit(owner, spender, value, deadline, v, r, s)`: up to the answer of ECRECOVER

`permit` (selector `0xd505accf`) checks the deadline and the owner, adds 1 to `nonces[owner]`,
builds the EIP-712 digest in memory, packs `r ++ s ++ v` as 65 bytes and calls the precompile at
address 1 (ECRECOVER) with STATICCALL. When the recovered address is the owner it writes the
allowance and logs `Approval`. Else it asks the owner contract (ERC-1271), `Sky/Permit1271.lean`.

The generated paths stop at the frame before `GAS STATICCALL` (pc 3501, `Paths.ok_permit`) and
start again after the call (pc 3503, `Paths.ok_permitRecA`, `Paths.ok_permitRecB`). This file
joins them across the call, for `processRunner`, with no assumption on what the precompile
returns: the output is EthLib's own `Precompiles.Ecrecover.compute` (`TokenKit.recoveredWord`).

The memory has two layouts. When the chain id is 1 the domain separator is a constant of the
code (layout A, free memory pointer 579 at the call). Else the code builds it from the chain id
and its own address (layout B, free memory pointer 899).

- `permitStruct`, `permitDomain`, `permitDigest`, `permitV`, `permitInput`: the struct hash, the
  domain separator, the digest, the byte `v` and the 128 bytes given to ECRECOVER.
- `permitState1`, `permitSub1`, `permitCost1`: the state, the substate and the gas used at the
  call (the nonce is written before the call).
- `permit_ec`: the call of ECRECOVER from the frame at pc 3501, for both layouts.
- `ok_permit_ec`: completeness for `permit` up to the code after the call (`PermitAfterEc`).

Scope: from Paris and before Glamsterdam. `hdel`: the account at address 1 holds no EIP-7702
delegation code (a fact of the state, true on chain: precompile accounts hold no code).
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace SkyVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open SkyVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked byteAt)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

/-- The mask of an address word: 2^160 - 1. -/
abbrev ADDR_MASK : U256 := (1461501637330902918203684832716283019655932542975 : U256)

/-- `PERMIT_TYPEHASH` of the contract. -/
abbrev PERMIT_TYPEHASH_W : U256 :=
  (49955707469362902507454157297736832118868343942642399513960811609542965143241 : U256)

/-- The word `0x1901` shifted to the top of a word: its first two bytes start the digest. -/
abbrev P1901 : U256 :=
  (11309588061646438093662687302255421419811724423900836950936401294474059186176 : U256)

/-- The owner argument, as the code uses it: the first argument, masked to an address. -/
abbrev permitOwner {fork : Fork} (m : Message fork) : U256 :=
  bitwiseAnd (loadWord m.data 4 32) ADDR_MASK

/-- The storage key of `nonces[owner]`. -/
abbrev permitNonceKey {fork : Fork} (m : Message fork) : U256 :=
  mapSlot (permitOwner m) (4 : U256)

/-- The struct hash: keccak of the type hash, owner, spender, value, the nonce in the state
before the call and the deadline, one word each. -/
abbrev permitStruct {fork : Fork} (m : Message fork) (state : State.TransactionState) : U256 :=
  keccak (memW [PERMIT_TYPEHASH_W, permitOwner m,
    bitwiseAnd (loadWord m.data 36 32) ADDR_MASK, loadWord m.data 68 32,
    storageAt state m.currentTarget (permitNonceKey m), loadWord m.data 100 32])

/-- The domain separator that the code holds as a constant and uses when the chain id is 1. -/
abbrev DOMAIN_MAINNET : U256 :=
  (88021402408547776102591478376141464261910208107393209539845231887077057693780 : U256)

/-- The domain separator that the code computes when the chain id is not 1: the keccak of the
EIP-712 domain type hash, the hash of the name, the hash of the version, the chain id and the
address of the contract. -/
abbrev permitDomain {fork : Fork} (m : Message fork) : U256 :=
  keccak (memW [(63076024560530113402979550242307453568063438748328787417531900361828837441551 : U256),
    (42607552171995751425823498296870486043198744678280595602348571221231826827713 : U256),
    (90743482286830539503240959006302832933333810038750515972785732718729991261126 : U256),
    (BitVec.ofNat 256 m.blockEnv.chainId.toNat), m.currentTarget.toU256])

/-- The digest: keccak of the two bytes `0x19 0x01`, the domain separator and the struct hash
(`topBytes 2 P1901 d` is the first two bytes of the word `P1901`, then `d`). -/
abbrev permitDigest (domain structHash : U256) : U256 :=
  keccak (topBytes 2 P1901 (memW [domain, structHash]))

/-- The byte `v` as the code reads it back from the packed signature: the first byte of the
word `v << 248`. For `v < 256` it is `v` (`permitV_eq`). -/
abbrev permitV {fork : Fork} (m : Message fork) : U256 :=
  getByte (0 : U256) (bitwiseAnd
    (115339776388732929035197660848497720713218148788040405586178452820382218977280 : U256)
    (bitwiseShl (248 : U256) (loadWord m.data 132 32)))

/-- The 128 bytes given to ECRECOVER: the digest, `v`, `r` and `s`. -/
def permitInput (digest v r s : U256) : ByteArray :=
  wordBytes digest ++ wordBytes v ++ wordBytes r ++ wordBytes s

/-- The state at the call of ECRECOVER: the nonce of the owner is read and written. -/
abbrev permitState1 {fork : Fork} (m : Message fork) (state : State.TransactionState) :
    State.TransactionState :=
  writeSlot (readSlot state m.currentTarget (permitNonceKey m)) m.currentTarget
    (permitNonceKey m)
    (add (storageAt state m.currentTarget (permitNonceKey m)) (1 : U256))

/-- The substate at the call of ECRECOVER. -/
abbrev permitSub1 (fork : Fork) (m : Message fork) (state : State.TransactionState)
    (substate : Substate) : Substate :=
  storeSub fork (accessSlot substate m.currentTarget (permitNonceKey m)) m.currentTarget
    (permitNonceKey m)
    (originalAt (readSlot state m.currentTarget (permitNonceKey m)) m.currentTarget
      (permitNonceKey m))
    (storageAt (readSlot state m.currentTarget (permitNonceKey m)) m.currentTarget
      (permitNonceKey m))
    (add (storageAt state m.currentTarget (permitNonceKey m)) (1 : U256))

/-- The gas used up to the call of ECRECOVER: `c` for the opcodes (2207 when the code builds the
domain separator, 1811 when the chain id is 1), the read and the write of the nonce. -/
abbrev permitCost1 (c : Nat) (fork : Fork) (m : Message fork) (state : State.TransactionState)
    (substate : Substate) : Nat :=
  c + slotCost (coldIn substate m.currentTarget (permitNonceKey m)) +
    Gas.writeCost fork
      (originalAt (readSlot state m.currentTarget (permitNonceKey m)) m.currentTarget
        (permitNonceKey m))
      (storageAt (readSlot state m.currentTarget (permitNonceKey m)) m.currentTarget
        (permitNonceKey m))
      (add (storageAt state m.currentTarget (permitNonceKey m)) (1 : U256))
      (coldIn (accessSlot substate m.currentTarget (permitNonceKey m)) m.currentTarget
        (permitNonceKey m))

/-- The gas of the call of ECRECOVER from a frame with `gas` at GAS, and what the caller pays:
EthLib's `messageCallGas` for the gas that GAS pushed, no memory growth, and the access of
address 1. -/
abbrev permitCall (fork : Fork) (substate : Substate) (gas : Nat) :=
  messageCallGas fork 0 (BitVec.ofNat 256 (gas - 2)).toNat (gas - 2) 0
    (callBaseCost fork (decide (toAddressMasked 1 ∉ substate.accessedAddresses)) +
      routeCost fork (substate.accessedAddresses.insert (toAddressMasked 1)) none)

/-- The state after the call of ECRECOVER: the two reads of the call are recorded. -/
abbrev ecState {fork : Fork} (m : Message fork) (st : State.TransactionState) :
    State.TransactionState :=
  (st.recordAccountRead (toAddressMasked 1)).recordAccountRead m.currentTarget

/-- The substate after the call of ECRECOVER: address 1 is accessed. -/
abbrev ecSub (ss : Substate) : Substate :=
  { ss with accessedAddresses := ss.accessedAddresses.insert (toAddressMasked 1) }

/-- The gas after the call of ECRECOVER from a frame with `gas` at GAS. -/
abbrev ecGas (fork : Fork) (ss : Substate) (gas : Nat) : Nat :=
  gas - 2 - ((permitCall fork ss gas).cost + 0) + ((permitCall fork ss gas).subCall - 3000)

/-- What the code after the call of ECRECOVER knows of its memory `M`: its size `sz`, the free
memory pointer `fpw`, the zero word at 96, the packed signature at 128 (length 65, `r`, `s`, and
the byte at 224 that is the first byte of the word `vw`). -/
structure PermitMem (M : ByteArray) (sz : Nat) (fpw sR sS vw : U256) : Prop where
  size : M.size = sz
  fp : loadWord (memoryReadBytes M 64 32) 0 32 = fpw
  w96 : loadWord (memoryReadBytes M 96 32) 0 32 = (0 : U256)
  w128 : loadWord (memoryReadBytes M 128 32) 0 32 = (65 : U256)
  w160 : loadWord (memoryReadBytes M 160 32) 0 32 = sR
  w192 : loadWord (memoryReadBytes M 192 32) 0 32 = sS
  top : TopBytes M 224 1 vw

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- Bytes that two memories of one size share stay known first bytes. -/
theorem top_same {M M' : ByteArray} {o a n : Nat} {w : U256}
    (hsame : ∀ a k, a + k ≤ o ∨ o + 32 ≤ a → memoryReadBytes M' a k = memoryReadBytes M a k)
    (hsz : M'.size = M.size) (h : TopBytes M a n w) (hd : a + n ≤ o ∨ o + 32 ≤ a)
    (ha : a + n ≤ M.size) : TopBytes M' a n w := by
  intro i hi
  have e : byteAt (memoryReadBytes M' a n) i = byteAt (memoryReadBytes M a n) i := by
    rw [hsame a n hd]
  rw [byteAt_memoryReadBytes (by rw [hsz]; exact ha), byteAt_memoryReadBytes ha, if_pos hi,
    if_pos hi] at e
  rw [e]
  exact h i hi

/-- From Paris and before Glamsterdam, under the real runner: a run from the frame of `permit`
before `GAS STATICCALL` (pc 3501) with the input range of 128 bytes at `f`, the output word at
`o = f - 32` (it holds 0) and both inside the memory, that ends with no error.

The call of ECRECOVER got at least 3000 gas and the run went on from pc 3503 with 1 pushed, in
a memory `M'` of the same size that differs from `M` only in the output word, which holds
`recoveredWord` of the input bytes. The state has the two reads of the call recorded, the
substate has address 1 accessed, and the gas is exact. -/
theorem permit_ec (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    {f o : Nat} {rest : List U256} {M : ByteArray} {gas : Nat}
    (hfo : o + 32 = f) (hsz : f + 128 ≤ M.size) (hf : f < 2 ^ 256)
    (h0 : loadWord (memoryReadBytes M o 32) 0 32 = (0 : U256))
    (hrest : rest.length + 6 < STACK_LIMIT)
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    {bound : Nat} {z s : Evm fork Nat}
    (start : At CODE message 3501 ((1 : U256) :: BitVec.ofNat 256 f :: (128 : U256) ::
      BitVec.ofNat 256 o :: (32 : U256) :: rest) M gas state substate z)
    (within : GasMeter.gasHeld z.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) z
      within = .ok s)
    (hok : s.error = none) :
    3000 ≤ (permitCall fork substate gas).subCall ∧
    ∃ (M' : ByteArray) (after : Evm fork Nat), M'.size = M.size ∧
      (∀ a k, a + k ≤ o ∨ o + 32 ≤ a → memoryReadBytes M' a k = memoryReadBytes M a k) ∧
      loadWord (memoryReadBytes M' o 32) 0 32 = recoveredWord (memoryReadBytes M f 128) ∧
      At CODE message 3503 ((1 : U256) :: rest) M' (ecGas fork substate gas)
        (ecState message state) (ecSub substate) after ∧
      EndsL (processRunner fork bound) after s := by
  have tf : (BitVec.ofNat 256 f : U256).toNat = f := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hf
  have to_ : (BitVec.ofNat 256 o : U256).toNat = o := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have t128 : (128 : U256).toNat = 128 := by decide
  have t32 : (32 : U256).toNat = 32 := by decide
  have hE : extendMemory M.size [((BitVec.ofNat 256 f : U256), (128 : U256)),
      ((BitVec.ofNat 256 o : U256), (32 : U256))] = ⟨0, 0⟩ :=
    extendMemory_two (by rw [tf, t128]; omega) (by rw [to_, t32]; omega)
  obtain ⟨hg, after, hat, w, hr⟩ := ecrecover_call_ok hparis hglam (q := 3503) rfl
    (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    hrest hdel start within hrun hok
  rw [hE] at hg hat
  simp only [memoryExtend_zero, tf, t128, to_, t32] at hat
  have hfit : o + 32 ≤ M.size := by omega
  exact ⟨hg, _, after, size_ecrecover_write _ hfit,
    fun a k hd => read_ecrecover_other _ hfit hd, load_ecrecover _ hfit h0, hat, ⟨w, hr⟩⟩

/-- The checks of `permit` before the nonce is written: no value, 228 bytes of call data, clean
address words for owner and spender, `v` below 256, the deadline not passed, a nonzero owner. -/
structure PermitChecks {fork : Fork} (m : Message fork) : Prop where
  value : isZero m.value ≠ 0
  size : isZero (signedLessThan (sub (BitVec.ofNat 256 m.data.size) (4 : U256))
    (224 : U256)) ≠ 0
  owner : equal (loadWord m.data 4 32) (bitwiseAnd (loadWord m.data 4 32) ADDR_MASK) ≠ 0
  spender : equal (loadWord m.data 36 32) (bitwiseAnd (loadWord m.data 36 32) ADDR_MASK) ≠ 0
  v : equal (loadWord m.data 132 32) (bitwiseAnd (loadWord m.data 132 32) (255 : U256)) ≠ 0
  deadline : isZero (greaterThan m.blockEnv.timestamp (loadWord m.data 100 32)) ≠ 0
  nonzero : permitOwner m ≠ 0

/-- The code of `permit` after the answer of ECRECOVER, for the layout whose generated segment
ends as `ends` says (`Paths.permitRecA_ends` or `Paths.permitRecB_ends`): the gas `c` of the
opcodes before the call was there, the call had 3000 gas, and the run ended as `ends` says from
the state, the substate and the gas after the call, in a memory `M` (`PermitMem`), with the
recovered word `recoveredWord (permitInput digest v r s)`. -/
def PermitAfterEc (fork : Fork) (m : Message fork) (state : State.TransactionState)
    (substate : Substate) (gas : Nat) (s : Evm fork Nat) (bound : Nat) (c sz : Nat)
    (fpw domain : U256)
    (ends : (state : State.TransactionState) → (substate : Substate) → (gas : Nat) →
      (s : Evm fork Nat) → (vb sS sR dg owner nonce deadline value spender sv sel rec vw : U256) →
      (mem : ByteArray) → {bound : Nat} → (runChild : MessageRunner fork Nat bound) → Prop) :
    Prop :=
  permitCost1 c fork m state substate ≤ gas ∧
  3000 ≤ (permitCall fork (permitSub1 fork m state substate)
    (gas - permitCost1 c fork m state substate)).subCall ∧
  ∃ M : ByteArray,
    PermitMem M sz fpw (loadWord m.data 164 32) (loadWord m.data 196 32)
      (bitwiseAnd
        (115339776388732929035197660848497720713218148788040405586178452820382218977280 : U256)
        (bitwiseShl (248 : U256) (loadWord m.data 132 32))) ∧
    ends (ecState m (permitState1 m state)) (ecSub (permitSub1 fork m state substate))
      (ecGas fork (permitSub1 fork m state substate)
        (gas - permitCost1 c fork m state substate))
      s (permitV m) (loadWord m.data 196 32) (loadWord m.data 164 32)
      (permitDigest domain (permitStruct m state)) (loadWord m.data 4 32)
      (storageAt state m.currentTarget (permitNonceKey m)) (loadWord m.data 100 32)
      (loadWord m.data 68 32) (loadWord m.data 36 32) (loadWord m.data 132 32)
      (BitVec.ofNat 256 (selector m.data))
      (recoveredWord (permitInput (permitDigest domain (permitStruct m state)) (permitV m)
        (loadWord m.data 164 32) (loadWord m.data 196 32)))
      (bitwiseAnd
        (115339776388732929035197660848497720713218148788040405586178452820382218977280 : U256)
        (bitwiseShl (248 : U256) (loadWord m.data 132 32)))
      M (processRunner fork bound)

/-- The account at address 1 holds no delegation code in the state at the call, when it holds
none in the state at the start: a read and a write of a slot keep accounts and codes. -/
theorem hdel_state1
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none) :
    ∀ c, (permitState1 message state).getCode
        ((permitState1 message state).getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none := by
  intro c h
  rw [getAccount_writeSlot, getCode_writeSlot, getAccount_readSlot] at h
  exact hdel c h

/-- Completeness for `permit` up to the code after the call of ECRECOVER, under EthLib's real
runner, from Paris and before Glamsterdam.

A run of a fresh frame of `CODE` on a message with the selector of `permit` that ends with no
error passed the checks `PermitChecks`, ran in a frame that may write on an account that
exists, and went on after the call of ECRECOVER as `PermitAfterEc` says: for the layout B when
the chain id is not 1 (the code builds the domain separator), for the layout A when it is 1. -/
theorem ok_permit_ec (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xd505accf)
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    PermitChecks message ∧ message.isStatic = false ∧
    hasAccount state message.currentTarget ∧
    ((equal (1 : U256) (BitVec.ofNat 256 message.blockEnv.chainId.toNat) = 0 ∧
        PermitAfterEc fork message state substate gas s bound 2207 1056 (899 : U256)
          (permitDomain message) (Paths.permitRecB_ends fork message)) ∨
      (equal (1 : U256) (BitVec.ofNat 256 message.blockEnv.chainId.toNat) ≠ 0 ∧
        PermitAfterEc fork message state substate gas s bound 1811 736 (579 : U256)
          DOMAIN_MAINNET (Paths.permitRecA_ends fork message))) := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hd1 := hdel_state1 (message := message) hdel
  rcases Paths.ok_permit hberlin hsize' hsel start ⟨within, hrun⟩ hok with
    ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hst, hacc, hcg, z, hz, w, hzr⟩ |
    ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hst, hacc, hcg, z, hz, w, hzr⟩
  · refine ⟨⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩, hst, hacc, .inl ⟨hc8, hcg, ?_⟩⟩
    obtain ⟨m0, m64, -, -, w96, w128, w160, w192, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, w867, w899, w931, w963, w995, t224, -⟩ :=
      Paths.permit_p8_mem (message := message) (state := state)
    obtain ⟨hg, M', after, hsz', hsame, hrec, hat, hend⟩ :=
      permit_ec hparis hglam (f := 899) (o := 867) rfl (by rw [m0]; decide) (by decide) w867
        (by simp [STACK_LIMIT]) hd1 hz w hzr hok
    have hdata := read4_raw w899 w931 w963 w995 m0 (by decide)
    rw [hdata] at hrec
    have L : ∀ {a : Nat} {x : U256}, (a + 32 ≤ 867 ∨ 867 + 32 ≤ a) →
        loadWord (memoryReadBytes _ a 32) 0 32 = x →
        loadWord (memoryReadBytes M' a 32) 0 32 = x :=
      fun hd h => (congrArg (loadWord · 0 32) (hsame _ 32 hd)).trans h
    have t' := top_same hsame hsz' t224 (.inl (by decide)) (by rw [m0]; decide)
    have pm : PermitMem M' 1056 (899 : U256) _ _ _ :=
      ⟨hsz'.trans m0, L (.inl (by decide)) m64, L (.inl (by decide)) w96,
        L (.inl (by decide)) w128, L (.inl (by decide)) w160, L (.inl (by decide)) w192, t'⟩
    exact ⟨hg, M', pm, Paths.ok_permitRecB_ends hberlin pm.size pm.fp pm.w96 pm.w128 pm.w160
      pm.w192 hrec pm.top hat hend hok⟩
  · refine ⟨⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩, hst, hacc, .inr ⟨hc8, hcg, ?_⟩⟩
    obtain ⟨m0, m64, -, -, w96, w128, w160, w192, -, -, -, -, -, -, -, -, -, -, w547, w579,
      w611, w643, w675, t224, -⟩ :=
      Paths.permit_p9_mem (message := message) (state := state)
    obtain ⟨hg, M', after, hsz', hsame, hrec, hat, hend⟩ :=
      permit_ec hparis hglam (f := 579) (o := 547) rfl (by rw [m0]; decide) (by decide) w547
        (by simp [STACK_LIMIT]) hd1 hz w hzr hok
    have hdata := read4_raw w579 w611 w643 w675 m0 (by decide)
    rw [hdata] at hrec
    have L : ∀ {a : Nat} {x : U256}, (a + 32 ≤ 547 ∨ 547 + 32 ≤ a) →
        loadWord (memoryReadBytes _ a 32) 0 32 = x →
        loadWord (memoryReadBytes M' a 32) 0 32 = x :=
      fun hd h => (congrArg (loadWord · 0 32) (hsame _ 32 hd)).trans h
    have t' := top_same hsame hsz' t224 (.inl (by decide)) (by rw [m0]; decide)
    have pm : PermitMem M' 736 (579 : U256) _ _ _ :=
      ⟨hsz'.trans m0, L (.inl (by decide)) m64, L (.inl (by decide)) w96,
        L (.inl (by decide)) w128, L (.inl (by decide)) w160, L (.inl (by decide)) w192, t'⟩
    exact ⟨hg, M', pm, Paths.ok_permitRecA_ends hberlin pm.size pm.fp pm.w96 pm.w128 pm.w160
      pm.w192 hrec pm.top hat hend hok⟩

end SkyVerify
