import TokenKit.Evm.StaticCall
import TokenKit.Evm.SafeL

/-!
# Runs that go on after a nested call: steps that keep the return data

After a STATICCALL the code reads the return data (RETURNDATASIZE, RETURNDATACOPY), which the
`At` of usdt-verify does not hold. The steps after the call are stated over EthLib's `Logic.At`
(with the return data), as facts about one run of the interpreter loop.

- `RunsTo runChild s code message B pc stack memory state substate rd`: the run that ends at the
  frame `s` goes through a frame at `pc` with this stack, memory, state, substate and return
  data, and with at most `B` gas.
- `RunsTo.step`: a rule over `Logic.StepG` moves a run that ends with no error.
- `RunsTo.reverts`: a rule to a REVERT: no such run ends with no error.
- `extcodesize_outcome`: EXTCODESIZE, with no assumption on the account: the run fails or it
  goes on with the size of the code of the account.

Nothing here is about one token.
-/

namespace TokenKit

open UsdtVerify

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Base
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}
  {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- The run that ends at `s` goes through a frame at `pc` with at most `B` gas. -/
def RunsTo (runChild : MessageRunner fork Nat bound) (s : Evm fork Nat)
    (code : ByteArray) (message : Message fork) (B pc : Nat) (stack : List U256)
    (memory : ByteArray) (state : State.TransactionState) (substate : Substate)
    (rd : ByteArray) : Prop :=
  ∃ (g : Nat) (l : Evm fork Nat), g ≤ B ∧
    Logic.At code message pc stack memory g state substate rd l ∧ EndsL runChild l s

namespace RunsTo

variable {s : Evm fork Nat} {B : Nat} {stack : List U256} {rd : ByteArray}

/-- A frame of usdt-verify's `At` that runs to `s`. -/
theorem of_at {l : Evm fork Nat} (h : At code message pc stack memory gas state substate l)
    (e : EndsL runChild l s) :
    RunsTo runChild s code message gas pc stack memory state substate l.returnData :=
  ⟨gas, l, Nat.le_refl _, h.toLogic, e⟩

/-- A frame of EthLib's `At` that runs to `s`. -/
theorem of_logic {l : Evm fork Nat}
    (h : Logic.At code message pc stack memory gas state substate rd l)
    (e : EndsL runChild l s) :
    RunsTo runChild s code message gas pc stack memory state substate rd :=
  ⟨gas, l, Nat.le_refl _, h, e⟩

/-- Back to a frame of usdt-verify's `At`. -/
theorem to_at (h : RunsTo runChild s code message B pc stack memory state substate rd) :
    ∃ (g : Nat) (l : Evm fork Nat), g ≤ B ∧
      At code message pc stack memory g state substate l ∧ EndsL runChild l s := by
  obtain ⟨g, l, hB, h0, e⟩ := h
  exact ⟨g, l, hB, At.ofLogic h0, e⟩

/-- A rule over `Logic.StepG`, held for every gas from `c` on, moves a run that ends with no
error. -/
theorem step {c pcr pc' : Nat} {stack' : List U256} {memory' : ByteArray}
    {state' : State.TransactionState} {substate' : Substate} {rd' : ByteArray}
    (h : RunsTo runChild s code message B pc stack memory state substate rd)
    (hok : s.error = none)
    (rule : ∀ G, c ≤ G →
      Logic.HoareG fork (Logic.At code message pc stack memory G state substate rd)
        (Logic.At code message pcr stack' memory' (G - c) state' substate' rd'))
    (hpc : pcr = pc') :
    RunsTo runChild s code message B pc' stack' memory' state' substate' rd' := by
  subst hpc
  obtain ⟨g, l, hB, h0, within, hr⟩ := h
  obtain ⟨z, hreach, hz⟩ := rule (g + c) (by omega) _ (h0.addGas c)
  obtain ⟨l', w, rfl, e'⟩ := reaches_low hreach c l rfl within hr hok
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hz
  have h7' : l'.gas + c = g + c - c := h7
  exact ⟨l'.gas, l', by omega, ⟨h1, h2, h3, h4, h5, h6, rfl, h8, h9, h10, h11, h12, h13⟩, w, e'⟩

/-- A rule to a REVERT, held for every gas from `c` on: no run through the frame ends with no
error. -/
theorem reverts {c : Nat} {out : ByteArray} {state' : State.TransactionState}
    {substate' : Substate}
    (h : RunsTo runChild s code message B pc stack memory state substate rd)
    (rule : ∀ G, c ≤ G →
      Logic.SpecG fork (Logic.At code message pc stack memory G state substate rd)
        (Halted true out (G - c) state' substate')) :
    s.error ≠ none := by
  obtain ⟨g, l, -, h0, within, hr⟩ := h
  exact Logic.SpecG.not_ok (rule (g + c) (by omega)) (fun evm hq => by rw [hq.2.1]; simp)
    (h0.addGas c) within hr

end RunsTo

/-- EXTCODESIZE, with no assumption on the account: the run fails (the state cannot give the
code, or the gas is short), or it goes on with the size of the code. -/
theorem extcodesize_outcome (hfork : .berlin ≤ fork) {U : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x3b) {evm s : Evm fork Nat}
    (start : At code message pc (U :: rest) memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    s.error ≠ none ∨
    ∃ (c : ByteArray) (after : Evm fork Nat),
      state.getCode (state.getAccount (toAddressMasked U)).codeHash = .ok c ∧
      externalBaseCost fork (decide (toAddressMasked U ∉ substate.accessedAddresses)) ≤ gas ∧
      At code message (pc + 1) (BitVec.ofNat 256 c.size :: rest) memory
        (gas - externalBaseCost fork (decide (toAddressMasked U ∉ substate.accessedAddresses)))
        (state.recordAccountRead (toAddressMasked U))
        { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked U) } after ∧
      ∃ within' : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound runChild after within' = .ok s := by
  have running := start.2.2.2.2.2.2.2.1
  cases hcode : state.getCode (state.getAccount (toAddressMasked U)).codeHash with
  | error e =>
    left
    obtain ⟨hc, -, -, hpc, hst, -, hgas, -, -, -, hs, hss⟩ := start
    subst hc hpc hgas hs hss
    have missing : accountCode evm (toAddressMasked U) = .error (.state e) := by
      simp [accountCode, hcode, Except.mapError]
    obtain ⟨e', he'⟩ := UsdtVerify.Complete.extcodesizeStep_notFound hst missing
    refine error_ne_none_of_stepFails running (.inl ⟨e', ?_⟩) hrun
    rw [step_of_instruction hlt
      (by rw [hbyte]; exact ofByte_of_decode (op := .extcodesize) rfl (Fork.frontier_le _))
      UsdtVerify.Complete.instruction_extcodesize', he']
    rfl
  | ok c =>
    by_cases hg :
        externalBaseCost fork (decide (toAddressMasked U ∉ substate.accessedAddresses)) ≤ gas
    · right
      obtain ⟨after, hat, w⟩ := Hoare.runFrame_of_ok
        (Logic.extcodesize_of_berlin_le hfork hlt hbyte hcode rfl hg) start.toLogic within hrun
      exact ⟨c, after, rfl, hg, At.ofLogic hat, w⟩
    · exact .inl (error_ne_none_of_stepFails running
        (.inl ⟨_, UsdtVerify.Complete.extcodesize_low hfork hlt hbyte hcode
          (Nat.lt_of_not_le hg) start⟩) hrun)

/-! ## Memory reads and writes inside the memory, over `Logic.At` -/

variable {rd : ByteArray}

/-- MLOAD of a word inside the memory: 3 gas, the memory stays. -/
theorem mloadInG {sz : Nat} {start : U256} {rest : List U256} (hs : memory.size = sz)
    (hfit : start.toNat + 32 ≤ sz) (hlt : pc < code.size) (hbyte : code[pc] = 0x51)
    (hgas : 3 ≤ gas) :
    Logic.HoareG fork (Logic.At code message pc (start :: rest) memory gas state substate rd)
      (Logic.At code message (pc + 1)
        (loadWord (memoryReadBytes memory start.toNat 32) 0 32 :: rest) memory (gas - 3)
        state substate rd) := by
  have e : extendMemory memory.size [(start, (32 : U256))] = ⟨0, 0⟩ :=
    extendMemory_of_le (by rw [hs]; exact hfit)
  have r := Logic.mloadG (fork := fork) (message := message) (state := state)
    (substate := substate) (returnData := rd) (rest := rest) (start := start)
    (memory := memory) (gas := gas) hlt hbyte (by rw [e]; exact hgas)
  rw [e] at r
  simp only [memoryExtend_zero] at r
  exact r

/-- MSTORE of a word inside the memory: 3 gas. -/
theorem mstoreInG {sz : Nat} {start value : U256} {rest : List U256} (hs : memory.size = sz)
    (hfit : start.toNat + 32 ≤ sz) (hlt : pc < code.size) (hbyte : code[pc] = 0x52)
    (hgas : 3 ≤ gas) :
    Logic.HoareG fork
      (Logic.At code message pc (start :: value :: rest) memory gas state substate rd)
      (Logic.At code message (pc + 1) rest
        (memoryWrite (memoryExtend memory 0) start.toNat (wordBytes value)) (gas - 3)
        state substate rd) := by
  have e : extendMemory memory.size [(start, (32 : U256))] = ⟨0, 0⟩ :=
    extendMemory_of_le (by rw [hs]; exact hfit)
  have r := Logic.mstoreG (fork := fork) (message := message) (state := state)
    (substate := substate) (returnData := rd) (rest := rest) (start := start) (value := value)
    (memory := memory) (gas := gas) hlt hbyte (by rw [e]; exact hgas)
  rw [e] at r
  exact r

/-! ## The memory after a copy of the return data (RETURNDATACOPY from offset 0) -/

/-- The copy leaves a word that ends before it. -/
theorem load_copied {m out : ByteArray} {sz a : Nat} {ow n w : U256}
    (h : loadWord (memoryReadBytes m a 32) 0 32 = w) (hs : m.size = sz) (hmod : sz % 32 = 0)
    (ha : a + 32 ≤ sz) (hd : a + 32 ≤ ow.toNat) (hn : n ≠ 0) (hout : n.toNat ≤ out.size) :
    loadWord (memoryReadBytes (memoryWrite
      (memoryExtend m (extendMemory m.size [(ow, n)]).expandBy) ow.toNat
      (memoryReadBytes out (0 : U256).toNat n.toNat)) a 32) 0 32 = w := by
  have hsz : (memoryExtend m (extendMemory m.size [(ow, n)]).expandBy).size =
      max m.size (ceil32 (ow.toNat + n.toNat)) :=
    size_memoryExtend_extendMemory (by rw [hs]; exact hmod) hn
  have hle := le_ceil32 (ow.toNat + n.toNat)
  have hr : (memoryReadBytes out (0 : U256).toNat n.toNat).size = n.toNat :=
    size_memoryReadBytes (by show 0 + n.toNat ≤ out.size; omega)
  have hsz' : m.size ≤ (memoryExtend m (extendMemory m.size [(ow, n)]).expandBy).size := by
    rw [size_memoryExtend]; omega
  rw [memoryReadBytes_memoryWrite_of_disjoint (by rw [hr, hsz]; omega) (.inl hd),
    memoryReadBytes_memoryExtend (by omega)]
  exact h

/-- The copy does not shrink the memory. -/
theorem size_copied_ge {m out : ByteArray} {sz : Nat} {ow n : U256} (hs : m.size = sz)
    (hmod : sz % 32 = 0) (hn : n ≠ 0) (hout : n.toNat ≤ out.size) :
    sz ≤ (memoryWrite (memoryExtend m (extendMemory m.size [(ow, n)]).expandBy) ow.toNat
      (memoryReadBytes out (0 : U256).toNat n.toNat)).size := by
  have hsz : (memoryExtend m (extendMemory m.size [(ow, n)]).expandBy).size =
      max m.size (ceil32 (ow.toNat + n.toNat)) :=
    size_memoryExtend_extendMemory (by rw [hs]; exact hmod) hn
  have hle := le_ceil32 (ow.toNat + n.toNat)
  have hr : (memoryReadBytes out (0 : U256).toNat n.toNat).size = n.toNat :=
    size_memoryReadBytes (by show 0 + n.toNat ≤ out.size; omega)
  rw [size_memoryWrite (by rw [hr, hsz]; omega), hsz]
  omega

/-- A copy inside the memory keeps its size. -/
theorem size_copied {m out : ByteArray} {sz : Nat} {ow n : U256} (hs : m.size = sz)
    (hfit : ow.toNat + n.toNat ≤ sz) (hout : n.toNat ≤ out.size) :
    (memoryWrite (memoryExtend m (extendMemory m.size [(ow, n)]).expandBy) ow.toNat
      (memoryReadBytes out (0 : U256).toNat n.toNat)).size = sz := by
  have hr : (memoryReadBytes out (0 : U256).toNat n.toNat).size = n.toNat :=
    size_memoryReadBytes (by show 0 + n.toNat ≤ out.size; omega)
  rw [size_memoryWrite (by rw [hr, size_memoryExtend]; omega), size_memoryExtend,
    extendMemory_of_le (by rw [hs]; exact hfit)]
  exact hs

/-- A copy of 32 bytes inside the memory: the word there is the first word of the return
data. -/
theorem load_copied_word {m out : ByteArray} {sz : Nat} {ow : U256} (hs : m.size = sz)
    (hfit : ow.toNat + 32 ≤ sz) (hout : 32 ≤ out.size) :
    loadWord (memoryReadBytes (memoryWrite
      (memoryExtend m (extendMemory m.size [(ow, (32 : U256))]).expandBy) ow.toNat
      (memoryReadBytes out (0 : U256).toNat (32 : U256).toNat)) ow.toNat 32) 0 32 =
      loadWord (memoryReadBytes out 0 32) 0 32 := by
  have e : memoryReadBytes out (0 : U256).toNat (32 : U256).toNat =
      wordBytes (loadWord (memoryReadBytes out 0 32) 0 32) :=
    (wordBytes_loadWord (size_memoryReadBytes (by show 0 + 32 ≤ out.size; omega))).symm
  rw [e]
  exact load_rawW_self hs (by omega)

/-- A STATICCALL whose input is inside the memory and whose output range is empty leaves the
memory as it was. -/
theorem staticcall_mem_same {m : ByteArray} (out : ByteArray) {i isz o : U256}
    (hfit : i.toNat + isz.toNat ≤ m.size) :
    memoryWrite (memoryExtend m (extendMemory m.size [(i, isz), (o, (0 : U256))]).expandBy)
      o.toNat (out.extract 0 (min (0 : U256).toNat out.size)) = m := by
  have e : extendMemory m.size [(i, isz), (o, (0 : U256))] = ⟨0, 0⟩ :=
    extendMemory_eq_zero _ _ fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact .inr (ceil32_le (ceil32_mod m.size) (Nat.le_trans hfit (le_ceil32 m.size)))
      · rw [List.mem_singleton.mp hp]
        exact .inl rfl
  have h0 : min (0 : U256).toNat out.size = 0 := Nat.zero_min _
  rw [e, h0]
  simp [memoryWrite, memoryExtend_zero]

end TokenKit
