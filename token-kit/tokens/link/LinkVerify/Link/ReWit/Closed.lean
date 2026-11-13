import LinkVerify.Link.ReWit.Run

/-!
# The run-local theorems applied to a run where the receiver calls back

Written by hand (not generated). Fix of audit 4, LINK-4. `ReWit/Run.lean` builds a real run of
`transferAndCall` whose receiver calls back into LINK. Here the run-local theorems of
`AnyLocal.lean` and `SeqLocal.lean` are applied to that run, and the start state is built.

- `callKeys_m_re`: the mapping keys of the outer call are the words `CALLER1W`, 0x1000 and 1.
- `supply_tac_re_frame`: the frame level. The run of `tac_re_core` meets `CleanFrameL`, and
  `supply_all_real_local` is applied to it: the sum of the balances is kept.
- `process_tac_re`: the message level. EthLib's `processMessage` ends the message with no error,
  the run meets `CleanL`, and `process_good_local` is applied to it: the end state is good.
- `msgL_tac_re`: so the run is one step `MsgL` of the sequences of `SeqLocal.lean`.
- `reState`: a start state. `baseState` (LINK at `LINK_ADDRESS`, the caller has `10^27`) with one
  more account, at the address of the word 0x1000, that holds the code `RE`.
- `reenter_closed`: THE CLOSED WITNESS. From `reState`, `processMessage` ends the message
  `transferAndCall(0x1000, 1, "")`; the end balances show the inner call; the run is a step
  `MsgL` (so `RunL`), and the sum of the balances at the end is `10^27`, by `inv_runL`.

Hypotheses that stay (in the statements, NOT proved):
- `hA : Sep RE_KEYS`, with `RE_KEYS = [CALLER1W, 0x1000, 0x2000, 1]`: the separation of the
  slots for these FOUR address words (a fact about keccak: the balance slot of each is the
  balance slot of no other address, and no allowance slot keyed by two of them is a balance
  slot). It cannot be computed (each part is over 2^160 addresses). It is a hypothesis on four
  named words, not on the messages of the runner.
- `hH : hashOf CODE ≠ EMPTY_CODE_HASH` and `hRE : hashOf RE ≠ hashOf CODE` (closed state only):
  two facts on the keccak hash of the code of LINK. Both are true (Test/Hash.lean computes the
  hash with `#eval`), but the kernel cannot compute the keccak of the 3 kB of code here. The
  state keeps codes under their hashes, so without `hRE` the two codes could share one entry.
- Paris ≤ fork < Glamsterdam.

Not covered: another receiver, another amount, a receiver that calls back more than once or
that calls `transferAndCall` again; that this state is a state of mainnet.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192

namespace LinkVerify.Sanity

open UsdtVerify
open TokenKit
open LinkVerify LinkVerify.Tac LinkVerify.Paths UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.State.TransactionState
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork}

/-! ## The mapping keys -/

/-- The four address words of the run: the caller, the receiver, the address that the receiver
sends the token on to, and the word 1 (the amount, that `callKeys` lists as a possible key). -/
abbrev RE_KEYS : List U256 := [Witness.CALLER1W, 0x1000, 0x2000, 1]

/-- The mapping keys of the outer call. -/
theorem callKeys_m_re (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C : Address) : callKeys (m_re b t C) = [Witness.CALLER1W, 0x1000, 1] := by
  have h1 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (m_re b t C).caller.toU256 = Witness.CALLER1W := by
    rw [re_m_caller]
    exact g3
  have h2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord (m_re b t C).data 4 32) = 0x1000 := re_m_to b t C
  have h3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord (m_re b t C).data 36 32) = 1 := by
    have h := re_m_value b t C
    unfold tacValue at h
    rw [h]
    exact q3
  unfold callKeys
  rw [h1, h2, h3]

/-- The keys of the outer call are among the four words. -/
theorem sep_outer (hA : Sep RE_KEYS) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C : Address) : Sep (callKeys (m_re b t C)) := by
  rw [callKeys_m_re]
  refine hA.restrict (fun x hx => ?_)
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
  rcases hx with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))

/-- The keys of the inner call are among the four words. -/
theorem sep_inner (hA : Sep RE_KEYS) {m : Message fork}
    (hk : callKeys m = [(0x1000 : U256), (0x2000 : U256), (1 : U256)]) : SepMsg m := by
  unfold SepMsg
  rw [hk]
  refine hA.restrict (fun x hx => ?_)
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
  rcases hx with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-! ## The frame level -/

/-- `supply_all_real_local` APPLIED TO THE RUN WITH A RECEIVER THAT CALLS BACK. In any state `S`
where `C` holds the code of LINK, 0x1000 holds `RE`, the caller has `10^27` tokens, 0x1000 and
0x2000 have none, and the sum of the balances is `10^27`: the frame of
`transferAndCall(0x1000, 1, "")` run by the loop of the interpreter with `processRunner` ends
with no error, the end balances show the inner call, the run meets `CleanFrameL` (the run-local
condition of `AnyLocal.lean`), and so, by `supply_all_real_local`, the sum of the balances at
the end is `10^27`. The only hypothesis on keccak is `Sep` of the four words of the run. -/
theorem supply_tac_re_frame (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (hC : C.toU256 = (0x514910771af9ca656af840dff83e8264ecf986ca : U256))
    (S : State.TransactionState) (ss : Substate)
    (hold : Reenter.HoldsCode C CODE S)
    (hre : S.getCode (S.getAccount (toAddressMasked (0x1000 : U256))).codeHash = .ok RE)
    (hbal : storageAt S C (mapSlot Witness.CALLER1W 1) = TOTALW)
    (hto : storageAt S C (mapSlot (0x1000 : U256) 1) = 0)
    (hto2 : storageAt S C (mapSlot (0x2000 : U256) 1) = 0)
    (hinv : Inv C S) (hA : Sep RE_KEYS)
    {B : Nat} (hB : reMeter fork b t C S ss ≤ B) (hcap : B ≤ GAS_CAP) {evm : Evm fork Nat}
    (start : At CODE (m_re b t C) 0 [] .empty (reMeter fork b t C S ss) S ss evm)
    (within : GasMeter.gasHeld evm.gas ≤ B) :
    ∃ s, Evm.runFrame (step fork) (step_decreases fork) B (processRunner fork B) evm within =
        .ok s ∧
      s.error = none ∧ s.output = wordBytes (1 : U256) ∧
      storageAt s.state C (mapSlot Witness.CALLER1W 1) = 999999999999999999999999999 ∧
      storageAt s.state C (mapSlot (0x1000 : U256) 1) = 0 ∧
      storageAt s.state C (mapSlot (0x2000 : U256) 1) = 1 ∧
      CleanFrameL C B evm ∧ Inv C s.state := by
  have hfork : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  obtain ⟨s, hrun, hok, hout, b1, b2, b3, hclean⟩ :=
    tac_re_core hparis hglam b t C hC S ss hold hre hbal hto hto2 hB start within
  have clean : CleanFrameL C B evm :=
    hclean (fun m => SepMsg m) (fun m hk => sep_inner hA hk)
  refine ⟨s, hrun, hok, hout, b1, b2, b3, clean, ?_⟩
  exact supply_all_real_local (message := m_re b t C) hfork hglam
    (by rw [re_m_size]; decide) (sep_outer hA b t C) hold hinv hcap clean start within hrun hok

/-! ## The message level -/

/-- `process_good_local` APPLIED TO THE RUN WITH A RECEIVER THAT CALLS BACK. In a state `S` as
above: EthLib's `processMessage` ends the message `transferAndCall(0x1000, 1, "")` (gas limit
`RE_GAS`) with no error and the output `true`; the end balances show the inner call; the run of
the message meets `CleanL` (the run-local condition of `SeqLocal.lean`: the outer call and the
inner call are the only two messages that enter `C`, and no code is deposited); and so, by
`process_good_local`, the end state is good: `C` holds the code of LINK and the sum of the
balances is `10^27`. -/
theorem process_tac_re (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (hC : C.toU256 = (0x514910771af9ca656af840dff83e8264ecf986ca : U256))
    (S : State.TransactionState) (ss : Substate)
    (hold : Reenter.HoldsCode C CODE S)
    (hre : S.getCode (S.getAccount (toAddressMasked (0x1000 : U256))).codeHash = .ok RE)
    (hbal : storageAt S C (mapSlot Witness.CALLER1W 1) = TOTALW)
    (hto : storageAt S C (mapSlot (0x1000 : U256) 1) = 0)
    (hto2 : storageAt S C (mapSlot (0x2000 : U256) 1) = 0)
    (hinv : Inv C S) (hA : Sep RE_KEYS) :
    ∃ (held : GasMeter.gasHeld (reMeter fork b t C S ss) ≤ (m_re b t C).gas)
      (ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ (m_re b t C).gas }),
      processMessage fork (m_re b t C) S ss (reMeter fork b t C S ss) held = .ok ended ∧
      ended.val.error = none ∧ ended.val.output = wordBytes (1 : U256) ∧
      storageAt ended.val.state C (mapSlot Witness.CALLER1W 1) = 999999999999999999999999999 ∧
      storageAt ended.val.state C (mapSlot (0x1000 : U256) 1) = 0 ∧
      storageAt ended.val.state C (mapSlot (0x2000 : U256) 1) = 1 ∧
      CleanL C (m_re b t C) S ss (reMeter fork b t C S ss) ∧
      GoodLink C ended.val.state := by
  have hfork : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hv : (m_re b t C).value = 0 := rfl
  have ht : ¬((m_re b t C).shouldTransferValue = true ∧ (m_re b t C).value ≠ 0) :=
    fun h => h.2 hv
  have noPre : precompileAddress fork (m_re b t C) = none :=
    noPre_of (a := C) rfl (notPrecompile_link hC)
  have hst : startState fork (m_re b t C) S = S := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have held : GasMeter.gasHeld (reMeter fork b t C S ss) ≤ (m_re b t C).gas :=
    reMeter_le hfork hglam b t C S ss
  have start : At CODE (m_re b t C) 0 [] .empty (reMeter fork b t C S ss) S ss
      (startFrame (m_re b t C) S ss (reMeter fork b t C S ss)) := at_startFrame rfl _
  obtain ⟨s, hrun, hok, hout, b1, b2, b3, hclean⟩ :=
    tac_re_core hparis hglam b t C hC S ss hold hre hbal hto hto2
      (B := (m_re b t C).gas) held start held
  have hrun' : Evm.runFrame (step fork) (step_decreases fork) (m_re b t C).gas
      (processRunner fork (m_re b t C).gas)
      (startFrame (m_re b t C) (startState fork (m_re b t C) S) ss (reMeter fork b t C S ss))
      held = .ok s := by
    rw [hst]
    exact hrun
  have hmap := processMessage_map_val ht noPre hrun'
  have clean : CleanL C (m_re b t C) S ss (reMeter fork b t C S ss) := by
    intro e he
    cases he with
    | self => exact fun _ => sep_outer hA b t C
    | sub fo hs ho =>
      rw [frameOf_noValue hparis hv fo] at hs
      exact hclean (fun m => SepMsg m) (fun m hk => sep_inner hA hk) _ _ hs e ho
  cases hpm : processMessage (Meter := Nat) fork (m_re b t C) S ss (reMeter fork b t C S ss)
      held with
  | error e =>
    rw [hpm] at hmap
    simp [Except.map] at hmap
  | ok ended =>
    rw [hpm] at hmap
    have hc : ended.1 = s := by
      simp only [Except.map, Except.ok.injEq] at hmap
      rw [hmap, rollbackOnError_of_error_eq_none hok]
    refine ⟨held, ended, hpm, by rw [hc]; exact hok, by rw [hc]; exact hout,
      by rw [hc]; exact b1, by rw [hc]; exact b2, by rw [hc]; exact b3, clean, ?_⟩
    exact process_good_local hfork hglam (L := C) (message := m_re b t C)
      (show (1000000 : Nat) ≤ GAS_CAP by decide)
      (fun _ => ⟨rfl, rfl, by rw [re_m_size]; decide⟩) ⟨hold, hinv⟩ clean hpm

/-- The run is one step `MsgL` of the sequences of `SeqLocal.lean`, to a state with the end
balances of the inner call. -/
theorem msgL_tac_re (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (hC : C.toU256 = (0x514910771af9ca656af840dff83e8264ecf986ca : U256))
    (S : State.TransactionState) (ss : Substate)
    (hold : Reenter.HoldsCode C CODE S)
    (hre : S.getCode (S.getAccount (toAddressMasked (0x1000 : U256))).codeHash = .ok RE)
    (hbal : storageAt S C (mapSlot Witness.CALLER1W 1) = TOTALW)
    (hto : storageAt S C (mapSlot (0x1000 : U256) 1) = 0)
    (hto2 : storageAt S C (mapSlot (0x2000 : U256) 1) = 0)
    (hinv : Inv C S) (hA : Sep RE_KEYS) :
    ∃ S' : State.TransactionState, MsgL C S S' ∧
      storageAt S' C (mapSlot Witness.CALLER1W 1) = 999999999999999999999999999 ∧
      storageAt S' C (mapSlot (0x1000 : U256) 1) = 0 ∧
      storageAt S' C (mapSlot (0x2000 : U256) 1) = 1 := by
  have hfork : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  obtain ⟨held, ended, hpm, -, -, b1, b2, b3, clean, -⟩ :=
    process_tac_re hparis hglam b t C hC S ss hold hre hbal hto hto2 hinv hA
  exact ⟨ended.val.state,
    ⟨fork, m_re b t C, ss, reMeter fork b t C S ss, held, ended, hfork, hglam,
      show (1000000 : Nat) ≤ GAS_CAP by decide,
      fun _ => ⟨rfl, rfl, by rw [re_m_size]; decide⟩, clean, hpm, rfl⟩, b1, b2, b3⟩

/-! ## A closed start state -/

/-- A state with one more account, at `a`, that holds `code` (nonce 1, no ether), kept under its
keccak hash as EthLib's `setCode` keeps it. -/
def addCode (S : State.TransactionState) (a : Address) (code : ByteArray) :
    State.TransactionState :=
  { S.setAccount a (some ⟨1, 0, hashOf code⟩) with
    codeWrites := (S.setAccount a (some ⟨1, 0, hashOf code⟩)).codeWrites.insert
      (hashOf code) code }

/-- `addCode` keeps every storage word. -/
theorem storageAt_addCode (S : State.TransactionState) (a : Address) (code : ByteArray)
    (C : Address) (n : U256) : storageAt (addCode S a code) C n = storageAt S C n := rfl

/-- `addCode` keeps what `getStorage` reads. -/
theorem getStorage_addCode (S : State.TransactionState) (a : Address) (code : ByteArray)
    (C : Address) (k : EthLib.Base.Bytes32) :
    (addCode S a code).getStorage C k = S.getStorage C k := rfl

/-- The code hash of the new account. -/
theorem codeHash_addCode_self (S : State.TransactionState) (a : Address) (code : ByteArray) :
    ((addCode S a code).getAccount a).codeHash = hashOf code := by
  have e : (addCode S a code).getAccountOptional a = some ⟨1, 0, hashOf code⟩ :=
    getAccountOptional_setAccount_self S a (some ⟨1, 0, hashOf code⟩)
  unfold State.TransactionState.getAccount
  rw [e] <;> rfl

/-- The code hash of another account is kept. -/
theorem codeHash_addCode_other (S : State.TransactionState) {a o : Address}
    (code : ByteArray) (h : o ≠ a) :
    ((addCode S a code).getAccount o).codeHash = (S.getAccount o).codeHash := by
  have e : (addCode S a code).getAccountOptional o = S.getAccountOptional o :=
    getAccountOptional_setAccount_of_ne S (some ⟨1, 0, hashOf code⟩) h
  unfold State.TransactionState.getAccount
  rw [e]

/-- `addCode` gives the new code under its hash, when it is not the hash of the empty code. -/
theorem getCode_addCode_self (S : State.TransactionState) (a : Address) {code : ByteArray}
    (hH : hashOf code ≠ EMPTY_CODE_HASH) :
    (addCode S a code).getCode (hashOf code) = .ok code := by
  have e2 : (addCode S a code).codeWrites[hashOf code]? = some code := by
    show ((S.setAccount a (some ⟨1, 0, hashOf code⟩)).codeWrites.insert
      (hashOf code) code)[hashOf code]? = some code
    simp
  unfold State.TransactionState.getCode
  rw [if_neg hH, e2]

/-- `addCode` keeps the code under every other hash. -/
theorem getCode_addCode_other (S : State.TransactionState) (a : Address) {code : ByteArray}
    {h : EthLib.Base.Hash32} (hne : hashOf code ≠ h) :
    (addCode S a code).getCode h = S.getCode h := by
  have e2 : (addCode S a code).codeWrites[h]? = S.codeWrites[h]? := by
    show ((S.setAccount a (some ⟨1, 0, hashOf code⟩)).codeWrites.insert
      (hashOf code) code)[h]? = S.codeWrites[h]?
    simp [Std.ExtTreeMap.getElem?_insert, hne]
    rfl
  unfold State.TransactionState.getCode
  rw [e2]
  rfl

/-- The hash of `RE` is not the hash of the empty code (computed in the kernel). -/
theorem re_hash_ne : hashOf RE ≠ EMPTY_CODE_HASH := by decide +kernel

/-- The balance slot of the caller is not the one of 0x2000 (computed in the kernel). -/
theorem key_ne2 : mapSlot Witness.CALLER1W 1 ≠ mapSlot (0x2000 : U256) 1 := by decide +kernel

/-- THE START STATE: `baseState` (the code of LINK at `LINK_ADDRESS`; the caller `CALLER1` has
`10^27` tokens, every other storage word is 0) with one more account, at the address of the word
0x1000, that holds the code `RE`. -/
abbrev reState : State.TransactionState :=
  addCode baseState (toAddressMasked (0x1000 : U256)) RE

/-- `LINK_ADDRESS` holds the code of LINK in `reState`. -/
theorem holdsCode_reState (hH : hashOf CODE ≠ EMPTY_CODE_HASH)
    (hRE : hashOf RE ≠ hashOf CODE) : Reenter.HoldsCode LINK_ADDRESS CODE reState := by
  obtain ⟨h1, h2, h3⟩ := holdsCode_baseState hH
  have e : (reState.getAccount LINK_ADDRESS).codeHash =
      (baseState.getAccount LINK_ADDRESS).codeHash :=
    codeHash_addCode_other baseState RE link_ne_rcpt
  have e0 : (baseState.getAccount LINK_ADDRESS).codeHash = hashOf CODE :=
    codeHash_codeState_self _ _ _
  refine ⟨?_, by rw [e]; exact h2, by rw [e]; exact h3⟩
  rw [e, e0, getCode_addCode_other baseState _ hRE, ← e0]
  exact h1

/-- The address of the word 0x1000 holds the code `RE` in `reState`. -/
theorem getCode_reState :
    reState.getCode (reState.getAccount (toAddressMasked (0x1000 : U256))).codeHash =
      .ok RE := by
  rw [codeHash_addCode_self]
  exact getCode_addCode_self _ _ re_hash_ne

/-- The sum of the balances of `reState` is `10^27`. -/
theorem inv_reState (hu : Supply.UniqBal 1 Witness.CALLER1W) : Inv LINK_ADDRESS reState :=
  storageOnly_inv LINK_ADDRESS baseState reState (fun k => getStorage_addCode _ _ _ _ k)
    (inv_baseState hu)

/-- The caller has `10^27` tokens in `reState`. -/
theorem bal_reState :
    storageAt reState LINK_ADDRESS (mapSlot Witness.CALLER1W 1) = TOTALW := by
  rw [storageAt_addCode, storageAt_codeState, storageAt_sState_cons, if_pos rfl]

/-- The receiver has no token in `reState`. -/
theorem to_reState : storageAt reState LINK_ADDRESS (mapSlot (0x1000 : U256) 1) = 0 := by
  rw [storageAt_addCode, storageAt_codeState, storageAt_sState_cons, if_neg key_ne,
    storageAt_sState_nil]

/-- The address 0x2000 has no token in `reState`. -/
theorem to2_reState : storageAt reState LINK_ADDRESS (mapSlot (0x2000 : U256) 1) = 0 := by
  rw [storageAt_addCode, storageAt_codeState, storageAt_sState_cons, if_neg key_ne2,
    storageAt_sState_nil]

/-- THE CLOSED WITNESS OF A RECEIVER THAT CALLS BACK. From the state `reState`, at every fork
from Paris and before Glamsterdam, in every block and transaction environment: EthLib's
`processMessage` ends the message `transferAndCall(0x1000, 1, "")` from `CALLER1` to LINK with no
error and the output `true`. The receiver, whose code is `RE`, called `transfer(0x2000, 1)` on
LINK from inside `onTokenTransfer`: at the end the caller has `10^27 - 1` tokens, the receiver
has 0 and the address 0x2000 has 1. The run meets the run-local condition `CleanL`, the end
state is good by `process_good_local`, the run is a sequence `RunL` from `reState`, and the sum
of the balances at the end is `10^27` by `inv_runL`.

Hypotheses (keccak, not proved): `hA` on the four words of the run, `hH` and `hRE` on the hash of
the code of LINK. -/
theorem reenter_closed (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate)
    (hH : hashOf CODE ≠ EMPTY_CODE_HASH) (hRE : hashOf RE ≠ hashOf CODE)
    (hA : Sep RE_KEYS) :
    ∃ (held : GasMeter.gasHeld (reMeter fork b t LINK_ADDRESS reState ss) ≤
        (m_re b t LINK_ADDRESS).gas)
      (ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ (m_re b t LINK_ADDRESS).gas }),
      processMessage fork (m_re b t LINK_ADDRESS) reState ss
        (reMeter fork b t LINK_ADDRESS reState ss) held = .ok ended ∧
      ended.val.error = none ∧ ended.val.output = wordBytes (1 : U256) ∧
      storageAt ended.val.state LINK_ADDRESS (mapSlot Witness.CALLER1W 1) =
        999999999999999999999999999 ∧
      storageAt ended.val.state LINK_ADDRESS (mapSlot (0x1000 : U256) 1) = 0 ∧
      storageAt ended.val.state LINK_ADDRESS (mapSlot (0x2000 : U256) 1) = 1 ∧
      CleanL LINK_ADDRESS (m_re b t LINK_ADDRESS) reState ss
        (reMeter fork b t LINK_ADDRESS reState ss) ∧
      GoodLink LINK_ADDRESS ended.val.state ∧
      RunL LINK_ADDRESS reState ended.val.state ∧
      Inv LINK_ADDRESS ended.val.state := by
  have hfork : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hu : Supply.UniqBal 1 Witness.CALLER1W := hA.uniq _ (by simp)
  have hold := holdsCode_reState hH hRE
  have hinv := inv_reState hu
  obtain ⟨held, ended, hpm, hok, hout, b1, b2, b3, clean, good⟩ :=
    process_tac_re hparis hglam b t LINK_ADDRESS link_address_word reState ss hold
      getCode_reState bal_reState to_reState to2_reState hinv hA
  have hmsg : MsgL LINK_ADDRESS reState ended.val.state :=
    ⟨fork, m_re b t LINK_ADDRESS, ss, reMeter fork b t LINK_ADDRESS reState ss, held, ended,
      hfork, hglam, show (1000000 : Nat) ≤ GAS_CAP by decide,
      fun _ => ⟨rfl, rfl, by rw [re_m_size]; decide⟩, clean, hpm, rfl⟩
  have hrunL : RunL LINK_ADDRESS reState ended.val.state := RunL.msg hmsg (RunL.nil _)
  exact ⟨held, ended, hpm, hok, hout, b1, b2, b3, clean, good, hrunL,
    inv_runL hrunL hold hinv⟩

end LinkVerify.Sanity
