import UniVerify.Uni.Sig
import UniVerify.Uni.Invariant

/-!
# The supply invariant of UNI under EthLib's real runner, for every selector

`Invariant.lean` (generated) proves that a successful call keeps `Dsum` (the sum of the `uint96`
balances of all addresses minus `totalSupply`) for every selector but those of `delegateBySig`
and `permit`, whose code calls the precompile ECRECOVER. This file adds the two, for
`processRunner` (EthLib's real runner), from `ok_delegateBySig_real` and `ok_permit_real`, and
closes the case split.

- `delta_delegateBySigTail_ends`, `delta_permitMaxTail_ends`, `delta_permitTail_ends`: the code
  after the call keeps `Dsum`.
- `delta_delegateBySig_real`, `delta_permit_real`, `supply_delegateBySig_real`,
  `supply_permit_real`: a successful call of the function keeps `Dsum`, and so `Inv`.
- `delta_step_real`, `supply_preserved_real`: a successful call of `CODE` with any call data
  keeps `Dsum`, and so `Inv`.

- `sigSigner`, `sigKeys`, `realKeys`, `realCk`, `RealSep`: the keys of a call, with the address
  word that `delegateBySig` reads from the output of ECRECOVER added when the selector is that
  of `delegateBySig`, and the hypothesis on keccak for them. It is a statement about the one
  message and its start state: finite lists of words, no statement over every address word
  (audit 4, UNI-2).
- `SepAllMsg`, `supply_preserved_real_sepAll`: the OLD, weaker form of the headline (hypothesis
  over every address word, most likely false for keccak; see Sep.lean), kept as a corollary.

Scope: from Paris and before Glamsterdam. `hdel`: the account at address 1 holds no EIP-7702
delegation code. `RealSep message state` is the hypothesis on keccak of Sep.lean for the keys
of this message (not proved). Nothing is assumed about what ECRECOVER returns.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096

namespace UniVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open UniVerify.Paths UniVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

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
    (recoveredWord (sigInput (delegDigest m) (bitwiseAnd (255 : U256) (loadWord m.data 100 32))
      (loadWord m.data 132 32) (loadWord m.data 164 32)))

/-- The signer as a key: only for a call with the selector of `delegateBySig`. -/
def sigKeys (m : Message fork) : List U256 :=
  if selector m.data = 0xc3cda520 then [sigSigner m] else []

/-- The address words a call can use as keys of the mappings, the signer of `delegateBySig`
included. -/
def realKeys (m : Message fork) : List U256 := sigKeys m ++ callKeys m

/-- The delegates whose checkpoints a call can write, the delegate of the signer of
`delegateBySig` included. -/
def realCk (m : Message fork) (S : State.TransactionState) : List U256 :=
  (sigKeys m).map (delegOf m.currentTarget S) ++ ckKeys m S

/-- The hypothesis on keccak for one message from the state `S` (see `Sep`): finitely many
slots, those of the keys of this message and of their delegates in `S`. -/
abbrev RealSep (m : Message fork) (S : State.TransactionState) : Prop :=
  Sep (realKeys m) (realCk m S)

/-- `RealSep` gives the hypothesis of the generated theorems. -/
theorem RealSep.call (h : RealSep message state) :
    Sep (callKeys message) (ckKeys message state) :=
  Sep.mono h (fun x hx => List.mem_append_right _ hx) (fun x hx => List.mem_append_right _ hx)

/-- The two account reads that a call records change no storage word. -/
theorem Dsum_recorded {A D : List U256} (hsep : Sep A D) (C : Address)
    (S : State.TransactionState) (a b : Address) :
    Dsum C ((S.recordAccountRead a).recordAccountRead b) = Dsum C S :=
  Dsum_frame hsep (fun _ _ => rfl)

/-- The code of `delegateBySig` after the call of ECRECOVER keeps `Dsum`: it writes the nonce
and the delegate of the recovered address, and checkpoints of the old and the new delegate. -/
theorem delta_delegateBySigTail_ends {A D : List U256} (hsep : Sep A D) {gas : Nat}
    {s : Evm fork Nat} {dg sh ds sigS sigR sigV expiry nonce delegatee sel rec : U256}
    (hs : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) rec ∈ A)
    (hd1 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) delegatee ∈ D)
    (hd2 : delegOf message.currentTarget state (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) rec) ∈ D)
    (h : delegateBySigTail_ends fork message state substate gas s dg sh ds sigS sigR sigV expiry
      nonce delegatee sel rec) :
    Dsum message.currentTarget s.state = Dsum message.currentTarget state := by
  unfold delegateBySigTail_ends at h
  obtain ⟨h1, h2, h3, hstat, hacc, hgas, hch⟩ := h
  rw [Dsum_frame hsep (mvSrc5_frame hch hd1 (by
    have h' := hd2
    simp (disch := slot_side) only [delegOf, and_mask_comm, mask_idem, storageAt_readSlot,
      st_deleg_nonce hsep hs hs] at h' ⊢
    exact h'))]
  clear hgas hch h1 h2 h3
  simp (disch := slot_side) only
    [and_mask_comm, mask_idem, storageAt_readSlot, D_rd, D_nonce hsep hs, D_deleg hsep hs]

/-- The code of `permit` (largest amount) after the call of ECRECOVER keeps `Dsum`: it writes
one allowance. -/
theorem delta_permitMaxTail_ends {D : List U256} (hsep : Sep (callKeys message) D) {gas : Nat}
    {s : Evm fork Nat} {dg sh ds sigS sigR sigV deadline rawAmount sel rec : U256}
    (h : permitMaxTail_ends fork message state substate gas s dg sh ds sigS sigR sigV deadline
      rawAmount (loadWord message.data 36 32) (loadWord message.data 4 32) sel rec) :
    Dsum message.currentTarget s.state = Dsum message.currentTarget state := by
  unfold permitMaxTail_ends at h
  obtain ⟨h1, h2, h3, hstat, hacc, hgas, hout, hg, hst, hsub⟩ := h
  rw [hst]
  clear hgas hout hg hst hsub h1 h2 h3
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
  have hm3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 36 32) ∈ callKeys message := by simp [callKeys]
  simp (disch := slot_side) only
    [and_mask_comm, mask_idem, storageAt_readSlot, D_rd, D_allow hsep]

/-- The code of `permit` (other amounts) after the call of ECRECOVER keeps `Dsum`. -/
theorem delta_permitTail_ends {D : List U256} (hsep : Sep (callKeys message) D) {gas : Nat}
    {s : Evm fork Nat} {dg sh ds amount sigS sigR sigV deadline rawAmount sel rec : U256}
    (h : permitTail_ends fork message state substate gas s dg sh ds amount sigS sigR sigV
      deadline rawAmount (loadWord message.data 36 32) (loadWord message.data 4 32) sel rec) :
    Dsum message.currentTarget s.state = Dsum message.currentTarget state := by
  unfold permitTail_ends at h
  obtain ⟨h1, h2, h3, hstat, hacc, hgas, hout, hg, hst, hsub⟩ := h
  rw [hst]
  clear hgas hout hg hst hsub h1 h2 h3
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
  have hm3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 36 32) ∈ callKeys message := by simp [callKeys]
  simp (disch := slot_side) only
    [and_mask_comm, mask_idem, storageAt_readSlot, D_rd, D_allow hsep]

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
  rw [delta_delegateBySigTail_ends hsep (by simp [realKeys, sigKeys, hsel, sigSigner])
    (by simp [realCk, ckKeys, callKeys]) (by
      show delegOf message.currentTarget state _ ∈ _
      simp [realCk, sigKeys, hsel, sigSigner]) hend]
  exact Dsum_recorded hsep _ _ _ _

/-- A successful call of `permit` under the real runner leaves `Dsum` as it was. -/
theorem delta_permit_real (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xd505accf)
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
  rcases ok_permit_real hparis hglam hsize' hsel hdel start within hrun hok with
    ⟨-, -, -, -, -, -, hstat, hacc, -, -, hend⟩ |
    ⟨-, -, -, -, -, -, -, hstat, hacc, -, -, hend⟩
  · have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
    rw [delta_permitMaxTail_ends hsep.call hend, Dsum_recorded hsep]
    simp (disch := slot_side) only [permitS1, and_mask_comm, D_rd, D_nonce hsep.call]
  · have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
    rw [delta_permitTail_ends hsep.call hend, Dsum_recorded hsep]
    simp (disch := slot_side) only [permitS1, and_mask_comm, D_rd, D_nonce hsep.call]

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

/-- A successful call of `permit` under the real runner keeps the invariant. -/
theorem supply_permit_real (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xd505accf)
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
  have h := delta_permit_real hparis hglam hsize' hsel hdel hsep start within hrun hok
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
  · by_cases h6 : selector message.data = 0xd505accf
    · exact delta_permit_real hparis hglam hsize' h6 hdel hsep start within hrun hok
    · exact delta_step hberlin hsize' h5 h6 hsep.call start ⟨within, hrun⟩ hok

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

/-! ## The old, weaker form (hypothesis over every address word) -/

/-- The OLD hypothesis on keccak of one message (before audit 4, UNI-2): `SepAll` of its call
keys (facts for EVERY address word, most likely false for keccak, see Sep.lean) and the three
facts between given slots that the finite form adds, for the keys of the message. -/
structure SepAllMsg (m : Message fork) : Prop where
  all : SepAll (realKeys m)
  cross : SepCross (realKeys m)

/-- The old form gives the finite form `RealSep`, in every state. -/
theorem SepAllMsg.real (h : SepAllMsg message) (S : State.TransactionState) :
    RealSep message S := by
  refine SepAll.sep h.all h.cross ?_ ?_
  · intro x hx
    simp only [realKeys, sigKeys, callKeys, List.mem_append, List.mem_cons, List.mem_nil_iff,
      or_false] at hx
    rcases hx with hx | rfl | rfl | rfl
    · split at hx
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        subst hx
        exact mask_lt _
      · cases hx
    · exact toNat_toU256_lt _
    · exact mask_lt _
    · exact mask_lt _
  · intro d hd
    simp only [realCk, sigKeys, ckKeys, callKeys, delegKeys, List.mem_append, List.mem_cons,
      List.mem_nil_iff, or_false, List.mem_map] at hd
    rcases hd with ⟨x, -, rfl⟩ | (rfl | rfl | rfl) | (rfl | rfl | rfl)
    · exact mask_lt _
    · exact toNat_toU256_lt _
    · exact mask_lt _
    · exact mask_lt _
    · exact mask_lt _
    · exact mask_lt _
    · exact mask_lt _

/-- THE OLD, WEAKER FORM of `supply_preserved_real` (the headline before audit 4): the same
conclusion under `SepAllMsg`, whose facts over every address word are most likely false for
keccak. It follows from `supply_preserved_real`; it is kept so the old statement can be named,
and is no headline. -/
theorem supply_preserved_real_sepAll (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256)
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    (hsep : SepAllMsg message)
    (hinv : Inv message.currentTarget state)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    Inv message.currentTarget s.state :=
  supply_preserved_real hparis hglam hsize' hdel (hsep.real state) hinv start within hrun hok

end UniVerify
