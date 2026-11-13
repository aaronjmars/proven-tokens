import SkyVerify.Sky.BytesCall

/-!
# `permit(owner, spender, value, deadline, bytes signature)` for a signature of any length

The code reads the length word of the signature and takes the ECRECOVER path only when it is 65.
For every other length (0, less than 65, more than 65, up to the 2^64 - 1 that the decoder
lets through) it skips ECRECOVER and asks the owner: `isValidSignature(digest, signature)` by
STATICCALL, with the bytes of the signature as the call data gives them.

This file joins the run for a length that is not 65:

- `ok_permitBytes_decoded` (Sky/PermitBytes.lean): pc 0 to the CALLDATACOPY (pc 4293), any length;
- `bytes_copy_any` (Sky/BytesWord.lean): the copy of the signature to memory, to pc 2287;
- the blocks of the checks (deadline, owner), the nonce (`sb2430_*`), the domain separator
  (`sb3191`), the struct hash and the digest (`sb2551`, `sb2704`), with memory offsets that
  depend on the rounded length `c` (Sky/BytesGen.lean, generated);
- `permit_contract_any` (Sky/BytesCall.lean): the encoder, the STATICCALL to the owner over the
  real runner, the check of the answer, the write of the allowance and the log.

`ok_permitBytes_other` is the completeness statement for a length that is not 65, and
`ok_permitBytes_full` the one with no hypothesis on the length (65: `ok_permitBytes65_full`).

Gas: `c = ceilLen L` is the length rounded up to 32. The decoder uses 711, the copy
`copyCost c`, the two checks 60, the body up to the EXTCODESIZE of the owner
`permitCost1 (bodyCostC c)` (chain id 1) or `permitCost1 (bodyCostD c)` (another chain id), and
the encoder `encCost F c` for the free memory pointer `F` (`freeC c`, `freeD c`). All of these
are exact; only the gas that the code of the owner uses is not known.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

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

/-! ## The memory after the nonce -/

/-- The memory after the read and the write of the nonce: the owner and the slot number 4 in the
first two words. -/
abbrev nonceM (M : ByteArray) (owner : U256) : ByteArray :=
  memoryWrite (memoryExtend (memoryWrite (memoryExtend M 0) 0
    (wordBytes (bitwiseAnd owner ADDR_MASK))) 0) 32 (wordBytes (4 : U256))

theorem nonceM_spec {M : ByteArray} {sz : Nat} (owner : U256) (hs : M.size = sz)
    (h64 : 64 ≤ sz) :
    (nonceM M owner).size = sz ∧ ∀ i, 64 ≤ i → byteAt (nonceM M owner) i = byteAt M i :=
  ⟨(size_rawW (size_rawW hs (by omega)) (by omega)).trans (by omega), fun i hi => by
    rw [byteAt_rawW_miss (size_rawW hs (by omega)) (by omega) (.inr (by omega)),
      byteAt_rawW_miss hs (by omega) (.inr (by omega))]⟩

/-! ## The struct hash and the digest -/

/-- The struct hash of `permit` from the words on the stack. -/
abbrev structW (nonce deadline value spender owner : U256) : U256 :=
  keccak (memW [PERMIT_TYPEHASH_W, bitwiseAnd owner ADDR_MASK, bitwiseAnd spender ADDR_MASK,
    value, nonce, deadline])

/-- The memory at the EXTCODESIZE of the owner (pc 3580), from the memory `M` at pc 2551 with the
free memory pointer `P`. -/
abbrev digM (M : ByteArray) (P sz L : Nat) (dom nonce deadline value spender owner : U256) :
    ByteArray :=
  sb2704_M (sb2551_M M P sz dom nonce deadline value spender owner) (P + 224) L nonce deadline
    value spender owner dom (structW nonce deadline value spender owner)

/-- The memory after the struct hash and the digest: what `sb2704` needs of the memory after
`sb2551`, and what the encoder needs of the memory after `sb2704`. -/
theorem digest_chain {M data : ByteArray} {f L c P sz : Nat} (hL : LenC L c) (hP : P % 32 = 0)
    (hP0 : c + 160 ≤ P) (hPb : P < 2 ^ 90) (hsz1 : P ≤ sz) (hsz2 : sz ≤ P + 32)
    (hszm : sz % 32 = 0) (hms : M.size = sz) (hfp : mw M 64 = W P)
    (hw96 : mw M 96 = (0 : U256)) (hw128 : mw M 128 = W L)
    (hsig : ∀ j, j < L → byteAt M (160 + j) = byteAt data (f + j))
    (dom nonce deadline value spender owner : U256) :
    ∃ M2 M3 : ByteArray,
      sb2551_M M P sz dom nonce deadline value spender owner = M2 ∧
      sb2704_M M2 (P + 224) L nonce deadline value spender owner dom
        (structW nonce deadline value spender owner) = M3 ∧
      digM M P sz L dom nonce deadline value spender owner = M3 ∧
      M2.size = P + 224 + 128 ∧ mw M2 64 = W (P + 224) ∧ mw M2 128 = W L ∧
      mw M2 (P + 224 + 34) = dom ∧
      mw M2 (P + 224 + 66) = structW nonce deadline value spender owner ∧
      TopBytes M2 (P + 224 + 32) 2 P1901 ∧
      EncMem M3 data f (P + 224 + 98) L c := by
  have hLs := hL.small
  have hLm := hL.mod
  have hLle := hL.le
  have hLlt := hL.lt
  obtain ⟨M2, e2⟩ : ∃ M2, sb2551_M M P sz dom nonce deadline value spender owner = M2 :=
    ⟨_, rfl⟩
  have k := sb2551_mem (rest := []) (x0 := dom) (x2 := nonce) (x4 := deadline) (x5 := value)
    (x6 := spender) (x7 := owner) hP (by omega) (by omega) hsz1 hsz2 hszm hms hfp
  rw [e2] at k
  obtain ⟨s2, -, -, -, -, -, -, -, a64, adom, ash, atop, fr2⟩ := k
  have a96 : mw M2 96 = (0 : U256) :=
    (mw_congr (M := M) (by omega) (by omega)
      (fun j hj => fr2 (96 + j) (by omega) (by omega))).trans hw96
  have a128 : mw M2 128 = W L :=
    (mw_congr (M := M) (by omega) (by omega)
      (fun j hj => fr2 (128 + j) (by omega) (by omega))).trans hw128
  have adom' : mw M2 (P + 224 + 34) = dom := by
    rw [show P + 224 + 34 = P + 258 from by omega]
    exact adom
  have ash' : mw M2 (P + 224 + 66) = structW nonce deadline value spender owner := by
    rw [show P + 224 + 66 = P + 290 from by omega]
    exact ash
  have atop' : TopBytes M2 (P + 224 + 32) 2 P1901 := by
    rw [show P + 224 + 32 = P + 256 from by omega]
    exact atop
  have s2' : M2.size = P + 224 + 128 := by omega
  obtain ⟨M3, e3⟩ : ∃ M3, sb2704_M M2 (P + 224) L nonce deadline value spender owner dom
      (structW nonce deadline value spender owner) = M3 := ⟨_, rfl⟩
  have k3 := sb2704_mem (rest := []) (x2 := nonce) (x4 := deadline) (x5 := value)
    (x6 := spender) (x7 := owner) (L := L) (Q := P + 224) (by omega) (by omega) (by omega) hLs
    s2' a64 a128 adom' ash' atop'
  rw [e3] at k3
  obtain ⟨s3, b128, -, -, -, b64, -, fr3⟩ := k3
  have b96 : mw M3 96 = (0 : U256) :=
    (mw_congr (M := M2) (by omega) (by omega)
      (fun j hj => fr3 (96 + j) (by omega) (by omega))).trans a96
  refine ⟨M2, M3, e2, e3, ?_, s2', a64, a128, adom', ash', atop',
    { size := by omega
      fp := b64
      w96 := b96
      w128 := b128
      sig := fun j hj => by
        rw [fr3 _ (by omega) (by omega), fr2 _ (by omega) (by omega)]
        exact hsig j hj
      hF := by omega
      hFc := by omega
      hFb := by omega }⟩
  show sb2704_M (sb2551_M M P sz dom nonce deadline value spender owner) (P + 224) L nonce
    deadline value spender owner dom (structW nonce deadline value spender owner) = M3
  rw [e2, e3]

/-- The struct hash and the digest, from pc 2551 to the EXTCODESIZE of the owner (pc 3580), for
a signature whose length is not 65: no ECRECOVER. -/
theorem digest_part (hfork : .berlin ≤ fork) {M data : ByteArray} {f L c P sz : Nat}
    (hL : LenC L c) (hP : P % 32 = 0) (hP0 : c + 160 ≤ P) (hPb : P < 2 ^ 90) (hsz1 : P ≤ sz)
    (hsz2 : sz ≤ P + 32) (hszm : sz % 32 = 0) (hms : M.size = sz) (hfp : mw M 64 = W P)
    (hw96 : mw M 96 = (0 : U256)) (hw128 : mw M 128 = W L)
    (hsig : ∀ j, j < L → byteAt M (160 + j) = byteAt data (f + j))
    (hlen : sub (65 : U256) (W L) ≠ 0)
    {dom nonce deadline value spender owner sel : U256} {gas : Nat}
    {state : State.TransactionState} {substate : Substate}
    (hg : 536 + (memoryGasCost (P + 352) - memoryGasCost sz) ≤ gas) :
    Logic.HoareG fork
      (At CODE message 2551 [dom, (0 : U256), nonce, (128 : U256), deadline, value, spender,
        owner, (558 : U256), sel] M gas state substate)
      (At CODE message 3580 [bitwiseAnd owner ADDR_MASK, (0 : U256), (128 : U256),
        permitDigest dom (structW nonce deadline value spender owner), owner, (2739 : U256),
        permitDigest dom (structW nonce deadline value spender owner), nonce, (128 : U256),
        deadline, value, spender, owner, (558 : U256), sel]
        (digM M P sz L dom nonce deadline value spender owner)
        (gas - (536 + (memoryGasCost (P + 352) - memoryGasCost sz))) state substate) := by
  have hLs := hL.small
  have hLle := hL.le
  have hLlt := hL.lt
  obtain ⟨M2, M3, e2, e3, e4, s2, a64, a128, adom, ash, atop, -⟩ :=
    digest_chain hL hP hP0 hPb hsz1 hsz2 hszm hms hfp hw96 hw128 hsig dom nonce deadline value
      spender owner
  rw [e4]
  refine Logic.Triple.seq (sb2551 (rest := [(558 : U256), sel]) hfork hP (by omega) (by omega)
    hsz1 hsz2 hszm hms hfp (by simp) (by omega)) ?_
  rw [e2, show P + 322 = P + 224 + 98 from by omega]
  refine Logic.Triple.seq (sb2704 (rest := [(558 : U256), sel]) (L := L) hfork (by omega)
    (by omega) (by omega) hLs s2 a64 a128 adom ash atop hlen (by simp) (by omega)) ?_
  rw [e3]
  exact hoareL (restate rfl rfl rfl (by omega) rfl rfl)

/-! ## From the nonce to the EXTCODESIZE of the owner -/

/-- The fixed gas from pc 2430 to the EXTCODESIZE of the owner (pc 3580) when the chain id is 1,
without the read and the write of the nonce: 673 and the growth of the memory from `c + 192` to
`c + 512` bytes. -/
def bodyCostC (c : Nat) : Nat :=
  673 + (memoryGasCost (c + 160 + 352) - memoryGasCost (c + 192))

/-- The same when the chain id is not 1 (the domain separator is computed): 1038 and the growth
of the memory from `c + 192` to `c + 832` bytes. -/
def bodyCostD (c : Nat) : Nat :=
  1038 + (memoryGasCost (c + 160 + 320) - memoryGasCost (c + 160 + 32)) +
    (memoryGasCost (c + 160 + 320 + 352) - memoryGasCost (c + 160 + 320))

/-- The free memory pointer at the encoder when the chain id is 1: `c + 482`. -/
abbrev freeC (c : Nat) : Nat := c + 160 + 224 + 98

/-- The free memory pointer at the encoder when the chain id is not 1: `c + 802`. -/
abbrev freeD (c : Nat) : Nat := c + 160 + 320 + 224 + 98

/-- The memory at the EXTCODESIZE of the owner, chain id 1. -/
abbrev bodyMemC {fork : Fork} (m : Message fork) (state : State.TransactionState)
    (M : ByteArray) (L c : Nat) : ByteArray :=
  digM (nonceM M (loadWord m.data 4 32)) (c + 160) (c + 192) L DOMAIN_MAINNET
    (storageAt state m.currentTarget (permitNonceKey m)) (loadWord m.data 100 32)
    (loadWord m.data 68 32) (loadWord m.data 36 32) (loadWord m.data 4 32)

/-- The memory at the EXTCODESIZE of the owner, chain id not 1. -/
abbrev bodyMemD {fork : Fork} (m : Message fork) (state : State.TransactionState)
    (M : ByteArray) (L c : Nat) : ByteArray :=
  digM (sb3191_M m (nonceM M (loadWord m.data 4 32)) (c + 160)
      (BitVec.ofNat 256 m.blockEnv.chainId.toNat)) (c + 160 + 320) (c + 160 + 320) L
    (permitDomain m)
    (storageAt state m.currentTarget (permitNonceKey m)) (loadWord m.data 100 32)
    (loadWord m.data 68 32) (loadWord m.data 36 32) (loadWord m.data 4 32)

theorem bodyMemC_enc {M data : ByteArray} {f L c : Nat} (state : State.TransactionState)
    (hL : LenC L c) (sm : SigMem M data f L c) :
    EncMem (bodyMemC message state M L c) data f (freeC c) L c := by
  have hLs := hL.small
  have hLm := hL.mod
  have hLle := hL.le
  have hLlt := hL.lt
  have hMs := sm.size
  obtain ⟨n1, n2⟩ := nonceM_spec (loadWord message.data 4 32) hMs (by omega)
  obtain ⟨M2, M3, -, -, e4, -, -, -, -, -, -, em⟩ :=
    digest_chain (M := nonceM M (loadWord message.data 4 32)) (data := data) (f := f)
      (P := c + 160) (sz := c + 192) hL (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) n1
      ((mw_congr (M := M) (by omega) (by omega) (fun j hj => n2 (64 + j) (by omega))).trans
        sm.fp)
      ((mw_congr (M := M) (by omega) (by omega) (fun j hj => n2 (96 + j) (by omega))).trans
        sm.w96)
      ((mw_congr (M := M) (by omega) (by omega) (fun j hj => n2 (128 + j) (by omega))).trans
        sm.w128)
      (fun j hj => (n2 _ (by omega)).trans (sm.sig j hj))
      DOMAIN_MAINNET (storageAt state message.currentTarget (permitNonceKey message))
      (loadWord message.data 100 32) (loadWord message.data 68 32)
      (loadWord message.data 36 32) (loadWord message.data 4 32)
  show EncMem (digM _ _ _ _ _ _ _ _ _ _) data f (c + 160 + 224 + 98) L c
  rw [e4]
  exact em

/-- What the domain separator code (`sb3191`) keeps of the memory after the nonce. -/
theorem domM_spec {M data : ByteArray} {f L c : Nat} (hL : LenC L c) (sm : SigMem M data f L c)
    (owner x0 : U256) :
    (nonceM M owner).size = c + 160 + 32 ∧
    mw (nonceM M owner) 64 = W (c + 160) ∧
    (sb3191_M message (nonceM M owner) (c + 160) x0).size = c + 160 + 320 ∧
    mw (sb3191_M message (nonceM M owner) (c + 160) x0) 64 = W (c + 160 + 320) ∧
    mw (sb3191_M message (nonceM M owner) (c + 160) x0) 96 = (0 : U256) ∧
    mw (sb3191_M message (nonceM M owner) (c + 160) x0) 128 = W L ∧
    (∀ j, j < L → byteAt (sb3191_M message (nonceM M owner) (c + 160) x0) (160 + j) =
      byteAt data (f + j)) := by
  have hLs := hL.small
  have hLm := hL.mod
  have hLle := hL.le
  have hLlt := hL.lt
  have hMs := sm.size
  obtain ⟨n1, n2⟩ := nonceM_spec owner hMs (by omega)
  obtain ⟨N, eN⟩ : ∃ N, nonceM M owner = N := ⟨_, rfl⟩
  rw [eN] at n1 n2 ⊢
  have nfp : mw N 64 = W (c + 160) :=
    (mw_congr (M := M) (by omega) (by omega) (fun j hj => n2 (64 + j) (by omega))).trans sm.fp
  have n96 : mw N 96 = (0 : U256) :=
    (mw_congr (M := M) (by omega) (by omega) (fun j hj => n2 (96 + j) (by omega))).trans sm.w96
  have n128 : mw N 128 = W L :=
    (mw_congr (M := M) (by omega) (by omega) (fun j hj => n2 (128 + j) (by omega))).trans
      sm.w128
  have n1' : N.size = c + 160 + 32 := by omega
  obtain ⟨D, eD⟩ : ∃ D, sb3191_M message N (c + 160) x0 = D := ⟨_, rfl⟩
  have k := sb3191_mem (message := message) (rest := []) (x0 := x0) (P := c + 160) (by omega)
    (by omega) (by omega) n1' nfp
  rw [eD] at k ⊢
  obtain ⟨s1, -, -, -, -, -, -, -, -, -, -, d64, fr⟩ := k
  exact ⟨n1', nfp, s1, d64,
    (mw_congr (M := N) (by omega) (by omega)
      (fun j hj => fr (96 + j) (by omega) (by omega))).trans n96,
    (mw_congr (M := N) (by omega) (by omega)
      (fun j hj => fr (128 + j) (by omega) (by omega))).trans n128,
    fun j hj => (fr _ (by omega) (by omega)).trans ((n2 _ (by omega)).trans (sm.sig j hj))⟩

theorem bodyMemD_enc {M data : ByteArray} {f L c : Nat} (state : State.TransactionState)
    (hL : LenC L c) (sm : SigMem M data f L c) :
    EncMem (bodyMemD message state M L c) data f (freeD c) L c := by
  have hLs := hL.small
  have hLm := hL.mod
  have hLle := hL.le
  have hLlt := hL.lt
  obtain ⟨-, -, d0, d64, d96, d128, dsig⟩ := domM_spec (message := message) hL sm
    (loadWord message.data 4 32) (BitVec.ofNat 256 message.blockEnv.chainId.toNat)
  obtain ⟨M2, M3, -, -, e4, -, -, -, -, -, -, em⟩ :=
    digest_chain (data := data) (f := f) (P := c + 160 + 320) (sz := c + 160 + 320) hL
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) d0 d64 d96 d128 dsig
      (permitDomain message) (storageAt state message.currentTarget (permitNonceKey message))
      (loadWord message.data 100 32) (loadWord message.data 68 32)
      (loadWord message.data 36 32) (loadWord message.data 4 32)
  show EncMem (digM _ _ _ _ _ _ _ _ _ _) data f (c + 160 + 320 + 224 + 98) L c
  rw [e4]
  exact em

/-- From the read of the nonce (pc 2430) to the EXTCODESIZE of the owner (pc 3580), chain id 1,
for a signature whose length is not 65, with exact gas. -/
theorem body_C (hfork : .berlin ≤ fork) {M data : ByteArray} {f L c : Nat} (hL : LenC L c)
    (sm : SigMem M data f L c) {state : State.TransactionState} {substate : Substate}
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hc : equal (1 : U256) (BitVec.ofNat 256 message.blockEnv.chainId.toNat) ≠ 0)
    (hlen : sub (65 : U256) (W L) ≠ 0) {sel : U256} {gas : Nat}
    (hg : permitCost1 (bodyCostC c) fork message state substate + 2300 < gas) :
    Logic.HoareG fork
      (At CODE message 2430 [(128 : U256), loadWord message.data 100 32,
        loadWord message.data 68 32, loadWord message.data 36 32, loadWord message.data 4 32,
        (558 : U256), sel] M gas state substate)
      (At CODE message 3580 [permitOwner message, (0 : U256), (128 : U256),
        permitDigest DOMAIN_MAINNET (permitStruct message state), loadWord message.data 4 32,
        (2739 : U256), permitDigest DOMAIN_MAINNET (permitStruct message state),
        storageAt state message.currentTarget (permitNonceKey message), (128 : U256),
        loadWord message.data 100 32, loadWord message.data 68 32, loadWord message.data 36 32,
        loadWord message.data 4 32, (558 : U256), sel]
        (bodyMemC message state M L c)
        (gas - permitCost1 (bodyCostC c) fork message state substate)
        (permitState1 message state) (permitSub1 fork message state substate)) := by
  have hLs := hL.small
  have hLm := hL.mod
  have hLle := hL.le
  have hLlt := hL.lt
  have hMs := sm.size
  obtain ⟨n1, n2⟩ := nonceM_spec (loadWord message.data 4 32) hMs (by omega)
  simp only [permitCost1, bodyCostC, permitNonceKey, permitOwner, ADDR_MASK] at hg ⊢
  refine Logic.Triple.seq (sb2430_1 (rest := [(558 : U256), sel]) (msz := c + 192) hfork hMs
    (by omega) hstatic hacc hc (by simp) (by omega)) ?_
  refine Logic.Triple.seq (b2517_0 (by simp) (by omega)) ?_
  refine Logic.Triple.seq (digest_part (M := nonceM M (loadWord message.data 4 32))
    (data := data) (f := f) (P := c + 160) (sz := c + 192) hfork hL (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) n1
    ((mw_congr (M := M) (by omega) (by omega) (fun j hj => n2 (64 + j) (by omega))).trans
      sm.fp)
    ((mw_congr (M := M) (by omega) (by omega) (fun j hj => n2 (96 + j) (by omega))).trans
      sm.w96)
    ((mw_congr (M := M) (by omega) (by omega) (fun j hj => n2 (128 + j) (by omega))).trans
      sm.w128)
    (fun j hj => (n2 _ (by omega)).trans (sm.sig j hj)) hlen (by omega)) ?_
  exact hoareL (restate rfl rfl rfl (by omega) rfl rfl)

/-- From the read of the nonce (pc 2430) to the EXTCODESIZE of the owner (pc 3580), chain id not
1 (the domain separator is computed), for a signature whose length is not 65, with exact gas. -/
theorem body_D (hfork : .berlin ≤ fork) {M data : ByteArray} {f L c : Nat} (hL : LenC L c)
    (sm : SigMem M data f L c) {state : State.TransactionState} {substate : Substate}
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hc : equal (1 : U256) (BitVec.ofNat 256 message.blockEnv.chainId.toNat) = 0)
    (hlen : sub (65 : U256) (W L) ≠ 0) {sel : U256} {gas : Nat}
    (hg : permitCost1 (bodyCostD c) fork message state substate + 2300 < gas) :
    Logic.HoareG fork
      (At CODE message 2430 [(128 : U256), loadWord message.data 100 32,
        loadWord message.data 68 32, loadWord message.data 36 32, loadWord message.data 4 32,
        (558 : U256), sel] M gas state substate)
      (At CODE message 3580 [permitOwner message, (0 : U256), (128 : U256),
        permitDigest (permitDomain message) (permitStruct message state),
        loadWord message.data 4 32, (2739 : U256),
        permitDigest (permitDomain message) (permitStruct message state),
        storageAt state message.currentTarget (permitNonceKey message), (128 : U256),
        loadWord message.data 100 32, loadWord message.data 68 32, loadWord message.data 36 32,
        loadWord message.data 4 32, (558 : U256), sel]
        (bodyMemD message state M L c)
        (gas - permitCost1 (bodyCostD c) fork message state substate)
        (permitState1 message state) (permitSub1 fork message state substate)) := by
  have hLs := hL.small
  have hLm := hL.mod
  have hLle := hL.le
  have hLlt := hL.lt
  have hMs := sm.size
  obtain ⟨n1, nfp, d0, d64, d96, d128, dsig⟩ := domM_spec (message := message) hL sm
    (loadWord message.data 4 32) (BitVec.ofNat 256 message.blockEnv.chainId.toNat)
  have g1 := memoryGasCost_mono (show c + 160 + 32 ≤ c + 160 + 320 by omega)
  have g2 := memoryGasCost_mono (show c + 160 + 320 ≤ c + 160 + 320 + 352 by omega)
  simp only [permitCost1, bodyCostD, permitNonceKey, permitOwner, ADDR_MASK] at hg ⊢
  refine Logic.Triple.seq (sb2430_0 (rest := [(558 : U256), sel]) (msz := c + 192) hfork hMs
    (by omega) hstatic hacc hc (by simp) (by omega)) ?_
  refine Logic.Triple.seq (b2504_0 hfork (by simp) (by omega)) ?_
  refine Logic.Triple.seq (sb3191 (P := c + 160) hfork (by omega) (by omega) (by omega) n1 nfp
    (by simp) (by omega)) ?_
  refine Logic.Triple.seq (b2512_0 (by simp) (by omega)) ?_
  refine Logic.Triple.seq (digest_part (data := data) (f := f) (P := c + 160 + 320)
    (sz := c + 160 + 320) hfork hL (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) d0 d64 d96 d128 dsig hlen (by omega)) ?_
  exact hoareL (restate rfl rfl rfl (by omega) rfl rfl)

/-! ## The whole function, for a length that is not 65 -/

/-- The checks of `permit` with a signature as bytes of any length, before the nonce is written:
no value, 164 bytes of call data or more, clean address words for owner and spender, an offset
word and a length word of at most 2^64 - 1, the length word and the bytes of the signature
inside the call data, the deadline not passed, a nonzero owner. -/
structure PermitBytesChecks {fork : Fork} (m : Message fork) : Prop where
  value : isZero m.value ≠ 0
  size : isZero (signedLessThan (sub (BitVec.ofNat 256 m.data.size) (4 : U256))
    (160 : U256)) ≠ 0
  owner : equal (loadWord m.data 4 32) (bitwiseAnd (loadWord m.data 4 32) ADDR_MASK) ≠ 0
  spender : equal (loadWord m.data 36 32) (bitwiseAnd (loadWord m.data 36 32) ADDR_MASK) ≠ 0
  offset : isZero (greaterThan (loadWord m.data 132 32) (18446744073709551615 : U256)) ≠ 0
  lengthIn : signedLessThan (add (sigPtr m) (31 : U256)) (BitVec.ofNat 256 m.data.size) ≠ 0
  length : isZero (greaterThan (sigLen m) (18446744073709551615 : U256)) ≠ 0
  bytesIn : isZero (greaterThan (add (add (sigPtr m) (sigLen m)) (32 : U256))
    (BitVec.ofNat 256 m.data.size)) ≠ 0
  deadline : isZero (greaterThan m.blockEnv.timestamp (loadWord m.data 100 32)) ≠ 0
  nonzero : permitOwner m ≠ 0

/-- The checks for a signature of 65 bytes are the checks for any length. -/
theorem PermitBytes65Checks.any {m : Message fork} (hlen : sigLen m = (65 : U256))
    (h : PermitBytes65Checks m) : PermitBytesChecks m :=
  { value := h.value
    size := h.size
    owner := h.owner
    spender := h.spender
    offset := h.offset
    lengthIn := h.lengthIn
    length := by
      rw [hlen]
      decide
    bytesIn := by
      rw [hlen]
      exact h.bytesIn
    deadline := h.deadline
    nonzero := h.nonzero }

/-- The signature of the message as the code copies it: `L` bytes of the call data from
`sigSrc m` (zeros past the end of the call data, which the check `bytesIn` excludes). -/
abbrev sigBytes {fork : Fork} (m : Message fork) : ByteArray :=
  copied m.data (sigSrc m) (sigLen m).toNat

/-- The code of `permit` with a signature whose length `L` is not 65, after the checks, for the
gas `b` of the body (`bodyCostC c` or `bodyCostD c`), the free memory pointer `F` at the encoder
(`freeC c` or `freeD c`) and the domain separator `domain`; `c` is `L` rounded up to 32.

`771 + copyCost c` gas pays the decoder (711), the copy of the signature and the two checks (25
and 35); then the gas `permitCost1 b` of the code up to the EXTCODESIZE of the owner was there,
and the run ended as `PermitByContractAny` says from the state and the substate after the write
of the nonce: the owner has code, the STATICCALL that `OwnerCall` describes was made with the
call data `erc1271Bytes digest (sigBytes m)`, the answer was the magic value, and the allowance
was written. The gas at the STATICCALL is exact; the gas at the end is an inequality. -/
def PermitBytesByContract (fork : Fork) (bound : Nat) (m : Message fork)
    (state : State.TransactionState) (substate : Substate) (gas : Nat) (s : Evm fork Nat)
    (b F : Nat) (domain : U256) : Prop :=
  771 + copyCost (ceilLen (sigLen m).toNat) ≤ gas ∧
  permitCost1 b fork m state substate ≤ gas - (771 + copyCost (ceilLen (sigLen m).toNat)) ∧
  PermitByContractAny fork bound m (permitState1 m state) (permitSub1 fork m state substate)
    (gas - (771 + copyCost (ceilLen (sigLen m).toNat)) - permitCost1 b fork m state substate)
    s (16 + encCost F (ceilLen (sigLen m).toNat))
    (permitDigest domain (permitStruct m state)) (sigBytes m)
    (loadWord m.data 4 32) (loadWord m.data 36 32) (loadWord m.data 68 32)

theorem sub65_ne {x : U256} (h : x ≠ (65 : U256)) : sub (65 : U256) x ≠ 0 := by
  intro h0
  apply h
  have h1 : (65 : BitVec 256) - x = 0 := h0
  bv_omega

/-- Completeness for `permit(owner, spender, value, deadline, bytes signature)` (selector
`0x9fd5a6cf`) with a signature whose length word is not 65, over the real runner
(`processRunner`), from Paris and before Glamsterdam, with no assumption on the code of the
owner and none on the call data.

A run of a fresh frame of the code that ends with no error passed the checks
(`PermitBytesChecks`), was not static, the token account exists, and it ended as
`PermitBytesByContract` says: no ECRECOVER, the ERC-1271 call to the owner with the digest and
the bytes of the signature as given, the magic value as the answer, then the allowance and the
log. The length is any word that the decoder lets through: 0, less than 65, more than 65, up to
2^64 - 1. -/
theorem ok_permitBytes_other {state : State.TransactionState} {substate : Substate}
    (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x9fd5a6cf)
    (hlen : sigLen message ≠ (65 : U256))
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    PermitBytesChecks message ∧ message.isStatic = false ∧
    hasAccount state message.currentTarget ∧
    ((equal (1 : U256) (BitVec.ofNat 256 message.blockEnv.chainId.toNat) = 0 ∧
        PermitBytesByContract fork bound message state substate gas s
          (bodyCostD (ceilLen (sigLen message).toNat)) (freeD (ceilLen (sigLen message).toNat))
          (permitDomain message)) ∨
      (equal (1 : U256) (BitVec.ofNat 256 message.blockEnv.chainId.toNat) ≠ 0 ∧
        PermitBytesByContract fork bound message state substate gas s
          (bodyCostC (ceilLen (sigLen message).toNat)) (freeC (ceilLen (sigLen message).toNat))
          DOMAIN_MAINNET)) := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hg0, z0, hz0, hend0⟩ :=
    ok_permitBytes_decoded hberlin hsize' hsel start ⟨within, hrun⟩ hok
  have hLs := len_small hc7
  have hLC : LenC (sigLen message).toNat (ceilLen (sigLen message).toNat) := lenC_ceil hLs
  have e1 : W (sigLen message).toNat = sigLen message := W_self _
  have e2 : W (ceilLen (sigLen message).toNat + 160) = sigFree (sigLen message) := by
    have h := sigFree_W hLC
    rw [e1] at h
    exact h.symm
  have hlenW : sub (65 : U256) (W (sigLen message).toNat) ≠ 0 := by
    rw [e1]
    exact sub65_ne hlen
  unfold PermitBytesByContract
  -- from here on the length and its rounding are two numbers
  revert hLC e1 e2 hlenW
  generalize ceilLen (sigLen message).toNat = c
  unfold sigBytes
  generalize (sigLen message).toNat = L at hLs ⊢
  intro hLC e1 e2 hlenW
  have hz0' : At CODE message 4293 [(160 : U256), add (sigPtr message) (32 : U256), W L,
      (128 : U256), W (c + 160), W L, (18446744073709551615 : U256),
      sigPtr message, (0 : U256), loadWord message.data 100 32, loadWord message.data 68 32,
      loadWord message.data 36 32, loadWord message.data 4 32, (4 : U256),
      BitVec.ofNat 256 message.data.size, (761 : U256), (558 : U256),
      BitVec.ofNat 256 (selector message.data)]
      (memW [(0 : U256), (0 : U256), W (c + 160), (0 : U256), W L])
      (gas - 711) state substate z0 := by
    rw [e2, e1]
    exact hz0
  obtain ⟨hg1, z1, hz1, hend1⟩ := ok_splitLE (B := copyCost c) (c := copyCost c)
    (Nat.le_refl _) (fun g hg => bytes_copy_any hLC hg) hz0' hend0 hok
  have sm := bytesMemAny_sigMem message.data (sigSrc message) hLC
  have hMs := sm.size
  have hd : isZero (greaterThan message.blockEnv.timestamp (loadWord message.data 100 32)) ≠
      0 := by
    intro hd
    obtain ⟨-, z2, hz2, hend2⟩ := ok_splitLE (B := 25) (c := 25) (Nat.le_refl _)
      (fun g hg => b2287_0 hd (by simp) hg) hz1 hend1 hok
    exact tail_deadline hberlin (by simp) (RunsTo.of_at hz2 hend2) hok
  obtain ⟨hg2, z2, hz2, hend2⟩ := ok_splitLE (B := 25) (c := 25) (Nat.le_refl _)
    (fun g hg => b2287_1 hd (by simp) hg) hz1 hend1 hok
  have ho : permitOwner message ≠ 0 := by
    intro ho
    obtain ⟨-, z3, hz3, hend3⟩ := ok_splitLE (B := 35) (c := 35) (Nat.le_refl _)
      (fun g hg => b2356_0 hberlin ho (by simp) hg) hz2 hend2 hok
    exact tail_owner hberlin (by simp) (RunsTo.of_at hz3 hend3) hok
  obtain ⟨hg3, z3, hz3, hend3⟩ := ok_splitLE (B := 35) (c := 35) (Nat.le_refl _)
    (fun g hg => b2356_1 hberlin ho (by simp) hg) hz2 hend2 hok
  have hgood : message.isStatic = false ∧ hasAccount state message.currentTarget := by
    apply Classical.byContradiction
    intro hgood
    exact no_ok_stuckLE
      (B := 109 + slotCost (coldIn substate message.currentTarget (permitNonceKey message)))
      (fun g hg => sb2430_2 (rest := [(558 : U256), BitVec.ofNat 256 (selector message.data)])
        (msz := c + 192) hberlin hMs (by omega) (Gas.bad_of_not hgood) (by simp) hg)
      hz3 hend3 hok
  have hchecks : PermitBytesChecks message := by
    refine ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hd, ho⟩
  refine ⟨hchecks, hgood.1, hgood.2, ?_⟩
  by_cases hch : equal (1 : U256) (BitVec.ofNat 256 message.blockEnv.chainId.toNat) = 0
  · refine .inl ⟨hch, ?_⟩
    obtain ⟨hg4, z4, hz4, hend4⟩ := ok_splitLE
      (B := permitCost1 (bodyCostD c) fork message state substate + 2301)
      (c := permitCost1 (bodyCostD c) fork message state substate) (by omega)
      (fun g hg => body_D hberlin hLC sm hgood.1 hgood.2 hch hlenW (by omega)) hz3 hend3 hok
    have eg : gas - 711 - copyCost c - 25 - 35 -
        permitCost1 (bodyCostD c) fork message state substate =
        gas - (771 + copyCost c) - permitCost1 (bodyCostD c) fork message state substate := by
      omega
    rw [eg] at hz4
    exact ⟨by omega, by omega,
      permit_contract_any hparis hglam hLC (bodyMemD_enc state hLC sm) hz4 hend4 hok⟩
  · refine .inr ⟨hch, ?_⟩
    obtain ⟨hg4, z4, hz4, hend4⟩ := ok_splitLE
      (B := permitCost1 (bodyCostC c) fork message state substate + 2301)
      (c := permitCost1 (bodyCostC c) fork message state substate) (by omega)
      (fun g hg => body_C hberlin hLC sm hgood.1 hgood.2 hch hlenW (by omega)) hz3 hend3 hok
    have eg : gas - 711 - copyCost c - 25 - 35 -
        permitCost1 (bodyCostC c) fork message state substate =
        gas - (771 + copyCost c) - permitCost1 (bodyCostC c) fork message state substate := by
      omega
    rw [eg] at hz4
    exact ⟨by omega, by omega,
      permit_contract_any hparis hglam hLC (bodyMemC_enc state hLC sm) hz4 hend4 hok⟩

/-! ## Every length -/

/-- Completeness for `permit(owner, spender, value, deadline, bytes signature)` (selector
`0x9fd5a6cf`) with no hypothesis on the signature, over the real runner (`processRunner`), from
Paris and before Glamsterdam, with no assumption on ECRECOVER and none on the code of the owner.

A run of a fresh frame of the code that ends with no error passed the checks
(`PermitBytesChecks`), was not static, the token account exists, and:

- the length word of the signature is 65 and the run ended as `PermitBytes65AfterEc` says (the
  signature path with exact gas, or the ERC-1271 path with `r`, `s`, `v` as the call data), or
- the length word is not 65 and the run ended as `PermitBytesByContract` says (the ERC-1271
  path with the bytes of the signature as given).

`hdel` (the address 1 holds no delegation, as in Sky/Permit.lean) is used by the 65 case only. -/
theorem ok_permitBytes_full {state : State.TransactionState} {substate : Substate}
    (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x9fd5a6cf)
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    PermitBytesChecks message ∧ message.isStatic = false ∧
    hasAccount state message.currentTarget ∧
    ((sigLen message = (65 : U256) ∧
      ((equal (1 : U256) (BitVec.ofNat 256 message.blockEnv.chainId.toNat) = 0 ∧
          PermitBytes65AfterEc fork bound message state substate gas s 1354
            (permitDomain message)) ∨
        (equal (1 : U256) (BitVec.ofNat 256 message.blockEnv.chainId.toNat) ≠ 0 ∧
          PermitBytes65AfterEc fork bound message state substate gas s 958 DOMAIN_MAINNET))) ∨
    (sigLen message ≠ (65 : U256) ∧
      ((equal (1 : U256) (BitVec.ofNat 256 message.blockEnv.chainId.toNat) = 0 ∧
          PermitBytesByContract fork bound message state substate gas s
            (bodyCostD (ceilLen (sigLen message).toNat))
            (freeD (ceilLen (sigLen message).toNat)) (permitDomain message)) ∨
        (equal (1 : U256) (BitVec.ofNat 256 message.blockEnv.chainId.toNat) ≠ 0 ∧
          PermitBytesByContract fork bound message state substate gas s
            (bodyCostC (ceilLen (sigLen message).toNat))
            (freeC (ceilLen (sigLen message).toNat)) DOMAIN_MAINNET)))) := by
  by_cases hlen : sigLen message = (65 : U256)
  · obtain ⟨hch, hst, hacc, h⟩ :=
      ok_permitBytes65_full hparis hglam hsize' hsel hlen hdel start within hrun hok
    exact ⟨hch.any hlen, hst, hacc, .inl ⟨hlen, h⟩⟩
  · obtain ⟨hch, hst, hacc, h⟩ :=
      ok_permitBytes_other hparis hglam hsize' hsel hlen start within hrun hok
    exact ⟨hch, hst, hacc, .inr ⟨hlen, h⟩⟩

/-- `permit` with a signature whose length is not 65, when the owner holds no code in the state
after the write of the nonce, never ends with no error: the ERC-1271 path needs code at the
owner. -/
theorem permitBytes_other_no_code_fails {state : State.TransactionState} {substate : Substate}
    (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x9fd5a6cf)
    (hlen : sigLen message ≠ (65 : U256))
    (hcode : ∀ c, (permitState1 message state).getCode
      ((permitState1 message state).getAccount
        (toAddressMasked (bitwiseAnd (loadWord message.data 4 32) ADDR_MASK))).codeHash = .ok c →
      c.size = 0)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s) :
    s.error ≠ none := by
  intro hok
  obtain ⟨-, -, -, h⟩ := ok_permitBytes_other hparis hglam hsize' hsel hlen start within hrun hok
  have key : ∀ {b F : Nat} {domain : U256},
      PermitBytesByContract fork bound message state substate gas s b F domain → False := by
    intro b F domain h
    obtain ⟨-, -, cd, out, st, ss, g, hcd, hne, -⟩ := h
    apply hne
    rw [hcode cd hcd]
    rfl
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · exact key h
  · exact key h

end SkyVerify
