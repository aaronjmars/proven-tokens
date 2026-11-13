import OndoVerify.Ondo.Sig
import OndoVerify.Ondo.Invariant

/-!
# The supply invariant of ONDO under EthLib's real runner, for every selector

`Invariant.lean` (generated) proves that a successful call keeps `Dsum` (the sum of the `uint96`
balances of all addresses minus `totalSupply`) for every selector but that of `delegateBySig`,
whose code calls the precompile ECRECOVER. This file adds it, for `processRunner` (EthLib's real
runner), from `ok_delegateBySig_real`, and closes the case split.

- `sigSigner`: the address word that `delegateBySig` reads from the output of ECRECOVER.
- `realKeys`, `realCk`, `RealSep`: the keys of a call with that word added, and the hypothesis
  on keccak for them. It is a statement about the one message and its start state: finite lists
  of words, no statement over every address.
- `delta_delegateBySigTail_ends`: the code after the call keeps `Dsum`.
- `delta_delegateBySig_real`, `supply_delegateBySig_real`: a successful call of the function
  keeps `Dsum`, and so `Inv`.
- `delta_step_real`, `supply_preserved_real`: a successful call of `CODE` with any call data
  keeps `Dsum`, and so `Inv`.

Scope: from Paris and before Glamsterdam. `hdel`: the account at address 1 holds no EIP-7702
delegation code. Nothing is assumed about what ECRECOVER returns.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096

namespace OndoVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open OndoVerify.Paths OndoVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {message : Message fork}
variable {state : State.TransactionState} {substate : Substate}

/-- The address word that `delegateBySig` takes as the signer: the low 160 bits of the word that
ECRECOVER returns for the digest and the `v`, `r`, `s` of the call data. -/
def sigSigner (m : Message fork) : U256 :=
  bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
    (recoveredWord (sigInput (delegDigest m) (bitwiseAnd (loadWord m.data 100 32) (255 : U256))
      (loadWord m.data 132 32) (loadWord m.data 164 32)))

/-- The address words a call can use as keys of the mappings, the signer of `delegateBySig`
included. -/
def realKeys (m : Message fork) : List U256 := sigSigner m :: callKeys m

/-- The delegates whose checkpoints a call can write, the delegate of the signer of
`delegateBySig` included. -/
def realCk (m : Message fork) (S : State.TransactionState) : List U256 :=
  delegOf m.currentTarget S (sigSigner m) :: ckKeys m S

/-- The hypothesis on keccak for one message from the state `S` (see `Sep`). -/
abbrev RealSep (m : Message fork) (S : State.TransactionState) : Prop :=
  Sep (realKeys m) (realCk m S) (loadWord m.data 4 32)

/-- `RealSep` gives the hypothesis of the generated theorems. -/
theorem RealSep.call (h : RealSep message state) :
    Sep (callKeys message) (ckKeys message state) (loadWord message.data 4 32) :=
  Sep.mono h (fun x hx => List.mem_cons_of_mem _ hx) (fun x hx => List.mem_cons_of_mem _ hx)

/-- The two account reads that a call records change no storage word. -/
theorem Dsum_recorded {A D : List U256} {R : U256} (hsep : Sep A D R) (C : Address)
    (S : State.TransactionState) (a b : Address) :
    Dsum C ((S.recordAccountRead a).recordAccountRead b) = Dsum C S :=
  Dsum_frame hsep (fun _ _ => rfl)

/-- The code of `delegateBySig` after the call of ECRECOVER keeps `Dsum`: it writes the nonce
and the delegate of the recovered address, and checkpoints of the old and the new delegate. -/
theorem delta_delegateBySigTail_ends {A D : List U256} {R : U256} (hsep : Sep A D R) {gas : Nat}
    {s : Evm fork Nat} {dg sh ds sigS sigR sigV expiry nonce delegatee sel rec : U256}
    (hs : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) rec ∈ A)
    (hd1 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) delegatee ∈ D)
    (hd2 : delegOf message.currentTarget state (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) rec) ∈ D)
    (h : delegateBySigTail_ends fork message state substate gas s dg sh ds sigS sigR sigV expiry
      nonce delegatee sel rec) :
    Dsum message.currentTarget s.state = Dsum message.currentTarget state := by
  unfold delegateBySigTail_ends at h
  obtain ⟨h1, h2, h3, h4, hstat, hacc, hgas, hch⟩ := h
  rw [Dsum_frame hsep (mvSrc1_frame hch hd1 (by
    have h' := hd2
    simp (disch := slot_side) only [delegOf, and_mask_comm, mask_idem, storageAt_readSlot,
      st_deleg_nonce hsep hs hs] at h' ⊢
    exact h'))]
  clear hgas hch h1 h2 h3 h4
  simp (disch := slot_side) only
    [and_mask_comm, mask_idem, storageAt_readSlot, D_rd, D_nonce hsep hs, D_deleg hsep hs]

/-- A successful call of `delegateBySig` under the real runner leaves `Dsum` as it was. -/
theorem delta_delegateBySig_real (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xc3cda520)
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    (hsep : RealSep message state)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    Dsum message.currentTarget s.state = Dsum message.currentTarget state := by
  obtain ⟨-, -, -, -, -, -, hend⟩ :=
    ok_delegateBySig_real hparis hglam hsize' hsel hdel start within hrun hok
  rw [delta_delegateBySigTail_ends hsep (by simp [realKeys, sigSigner])
    (by simp [realCk, ckKeys, callKeys]) (by
      show delegOf message.currentTarget state _ ∈ _
      simp [realCk, sigSigner]) hend]
  exact Dsum_recorded hsep _ _ _ _

/-- A successful call of `delegateBySig` under the real runner keeps the invariant. -/
theorem supply_delegateBySig_real (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xc3cda520)
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    (hsep : RealSep message state)
    (hinv : Inv message.currentTarget state)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    Inv message.currentTarget s.state := by
  have h := delta_delegateBySig_real hparis hglam hsize' hsel hdel hsep start within hrun hok
  unfold Inv SupplyMask.Inv at hinv ⊢
  unfold Dsum at h
  rw [h]
  exact hinv

/-- From Paris and before Glamsterdam, under the real runner: a run of `CODE` from pc 0 that
ends with no error, with any call data, leaves `Dsum` as it was. -/
theorem delta_step_real (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256)
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    (hsep : RealSep message state)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    Dsum message.currentTarget s.state = Dsum message.currentTarget state := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  by_cases h5 : selector message.data = 0xc3cda520
  · exact delta_delegateBySig_real hparis hglam hsize' h5 hdel hsep start within hrun hok
  · exact delta_step hberlin hsize' h5 hsep.call start ⟨within, hrun⟩ hok

/-- From Paris and before Glamsterdam, under the real runner: a run of `CODE` from pc 0 that
ends with no error, with any call data, keeps the invariant (the sum of the `uint96` balances
of all addresses is `totalSupply`). -/
theorem supply_preserved_real (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256)
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    (hsep : RealSep message state)
    (hinv : Inv message.currentTarget state)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    Inv message.currentTarget s.state := by
  have h := delta_step_real hparis hglam hsize' hdel hsep start within hrun hok
  unfold Inv SupplyMask.Inv at hinv ⊢
  unfold Dsum at h
  rw [h]
  exact hinv

end OndoVerify
