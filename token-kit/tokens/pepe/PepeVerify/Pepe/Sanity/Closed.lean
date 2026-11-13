import PepeVerify.Pepe.Tx
import PepeVerify.Pepe.Sanity.Zero

/-!
# A closed instance: a good start state, a real call, and the transaction-level theorem on it

Written by hand (not generated; the argument block of `transfer_closed` follows the generated witness
`transfer_p10_runs` of `Sanity/Zero.lean`). Fix of audit 4, PEPE: the supply theorems take the
hypothesis on keccak `Sep` and the invariant `Inv` at the start, and no file showed that these
hypotheses can hold together for one concrete state and call, nor that EthLib's `processMessage`
ends a call to PEPE with no error. Here one instance is built.

- `PEPE_ADDRESS`: the address of PEPE on mainnet. `wState`: one account, at `PEPE_ADDRESS`,
  that HOLDS THE CODE of PEPE; the owner (slot 0) is the address 2, the balance of `Witness.CALLER1` is 5, `_totalSupply` (slot 3) is 5, every other slot is 0.
- `m_w`: the call `transfer(2, 1)` from `Witness.CALLER1`, no value, gas limit 1000000.
- `holdsCode_wState`, `inv_wState`, `good_wState`: the start state is good (`Seq.Good`): the
  account holds the code and the sum of the balances of the 2^160 addresses is `_totalSupply`.
- `spec_process`, `clean_of_spec`: two lemmas that are about no token. From Paris, a message with
  no value whose frame has a specification to a normal halt (the form of the path theorems) is
  ended by `processMessage` with no error, and its run is `Seq.Clean` as soon as the hypothesis
  of its own message holds (the frame sends no message, so the run has one event).
- `transfer_closed`: THE CLOSED INSTANCE. From `wState`, EthLib's `processMessage` ends `m_w` with no
  error; one token moves from the caller to the address 2: the caller has 4, the address 2 has 1, `_totalSupply` is still 5; the run meets the run-local hypothesis `Seq.Clean` of
  `supply_message_any_depth`; and so, by that theorem, the end state is good.

Hypotheses that stay (in the statements, NOT proved, and they cannot be proved in this model):
- `hA : Sep W_KEYS`, with `W_KEYS = [Witness.CALLER1W, 2, 1]`: the separation of the slots for
  THREE named address words (the caller, the receiver 2 and the amount word 1). It unfolds to 33 (1 for slot 3, 3 for the balance slots of the three words, 18 for the 9 allowance slots, 6 for the 3 blacklist slots, 5 for the slots 0, 6, 7, 8, 9) facts
  about keccak, each of the form "this one slot is the balance slot of no address word" or "no
  other address word has this balance slot". Each is over all 2^160 address words, so the
  kernel cannot compute it, and keccak is a function with no proved property in the model. This
  is the smallest list the frame theorem `supply_preserved` lets through: it asks `Sep` of the
  three words of `callKeys`, whatever the function.
- `hH : hashOf CODE ≠ EMPTY_CODE_HASH`: the keccak hash of the code of PEPE is not the hash of
  the empty code. It is true (Test/Hash.lean computes the hash with `#eval`), but it is not
  proved in the kernel here (the keccak of the whole code is too large a kernel computation).
- Paris ≤ fork < Glamsterdam. The proof uses Paris only; the upper bound is stated because the
  one-counter gas meter of these theorems is the one EthLib's transactions run before
  Glamsterdam.

Not covered: `Seq.TxClean` and `Seq.Chain` (the hypotheses of `supply_transaction` and
`supply_any_transactions`) have no closed instance: that needs a signed transaction that
EthLib's `processTransaction` accepts (signature recovery in the kernel). The instance here is
at the level of the message, the level `Seq.Clean` speaks of. That `wState` is a state of
mainnet is not claimed.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192

namespace PepeVerify.Sanity

open UsdtVerify
open TokenKit
open PepeVerify PepeVerify.Paths UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.State.TransactionState
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork}

/-! ## Lemmas about no token (candidates for the kit) -/

/-- The keccak hash under which the state keeps a code. -/
abbrev hashOf (code : ByteArray) : EthLib.Base.Hash32 :=
  EthLib.Cryptography.Hash.Keccak.keccak256 code

/-- `sState C kvs` where the account at `C` holds the code `code` (nonce 1, no ether), kept
under its keccak hash as EthLib's `setCode` keeps it. -/
def codeState (C : Address) (kvs : List (U256 × U256)) (code : ByteArray) :
    State.TransactionState :=
  { (sState C kvs).setAccount C (some ⟨1, 0, hashOf code⟩) with
    codeWrites := ((sState C kvs).setAccount C (some ⟨1, 0, hashOf code⟩)).codeWrites.insert
      (hashOf code) code }

/-- The storage of `codeState` is that of `sState`. -/
theorem storageAt_codeState (C : Address) (kvs : List (U256 × U256)) (code : ByteArray)
    (C' : Address) (n : U256) :
    storageAt (codeState C kvs code) C' n = storageAt (sState C kvs) C' n := rfl

/-- The code hash of the account of `codeState`. -/
theorem codeHash_codeState (C : Address) (kvs : List (U256 × U256)) (code : ByteArray) :
    ((codeState C kvs code).getAccount C).codeHash = hashOf code := by
  have e : (codeState C kvs code).getAccountOptional C = some ⟨1, 0, hashOf code⟩ :=
    getAccountOptional_setAccount_self (sState C kvs) C (some ⟨1, 0, hashOf code⟩)
  unfold State.TransactionState.getAccount
  rw [e] <;> rfl

/-- `codeState` gives the code for its account, when the hash of the code is not the hash of the
empty code. -/
theorem getCode_codeState (C : Address) (kvs : List (U256 × U256)) {code : ByteArray}
    (hH : hashOf code ≠ EMPTY_CODE_HASH) :
    (codeState C kvs code).getCode ((codeState C kvs code).getAccount C).codeHash = .ok code := by
  have e2 : (codeState C kvs code).codeWrites[hashOf code]? = some code := by
    show (((sState C kvs).setAccount C (some ⟨1, 0, hashOf code⟩)).codeWrites.insert
      (hashOf code) code)[hashOf code]? = some code
    simp
  rw [codeHash_codeState]
  unfold State.TransactionState.getCode
  rw [if_neg hH, e2]

/-- The account of `codeState` holds its code (`Seq.HoldsCode`). -/
theorem holdsCode_codeState (C : Address) (kvs : List (U256 × U256)) {code : ByteArray}
    (hH : hashOf code ≠ EMPTY_CODE_HASH) : Seq.HoldsCode C code (codeState C kvs code) :=
  ⟨getCode_codeState C kvs hH, by rw [codeHash_codeState]; exact hH, codeHash_codeState C kvs code⟩

/-- A message whose code address is no precompile runs no precompile. -/
theorem noPre_of {msg : Message fork} {a : Address} (h : msg.codeAddress = some a)
    (hnp : Precompiles.isPrecompile fork a.toU256.toNat = false) :
    precompileAddress fork msg = none := by
  simp [precompileAddress, h, hnp]

/-- From Berlin, an SSTORE of the one-counter meter costs at most 110020, at every fork. -/
theorem writeCost_le_all (hfork : .berlin ≤ fork) (o c w : U256) (cold : Bool) :
    UsdtVerify.Gas.writeCost fork o c w cold ≤ 110020 := by
  have h := UsdtVerify.Gas.writeCost_le hfork o c w cold
  have h2 : UsdtVerify.Gas.writeMax fork ≤ 110020 := by
    unfold UsdtVerify.Gas.writeMax
    split <;> decide
  exact Nat.le_trans h h2

/-- A bound through a middle number. -/
theorem lt_of_le_bound {a B g : Nat} (h1 : a ≤ B) (h2 : B < g) : a < g :=
  Nat.lt_of_le_of_lt h1 h2

/-- From Paris, EthLib's `processMessage` ends a message with no value, to a target that is no
precompile, whose frame has a specification to a normal halt (`Logic.SpecG`, the form of the path
theorems): with no error, in the state and with the output of the specification. -/
theorem spec_process (hparis : .paris ≤ fork) {msg : Message fork}
    {S : State.TransactionState} {ss : Substate} {code out : ByteArray} {g' : Nat}
    {st' : State.TransactionState} {ss' : Substate}
    (hcode : msg.code = code) (noPre : precompileAddress fork msg = none) (hv : msg.value = 0)
    (spec : Logic.SpecG fork (At code msg 0 [] .empty msg.gas S ss)
      (Halted false out g' st' ss')) :
    ∃ ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ msg.gas },
      processMessage fork msg S ss = .ok ended ∧ ended.val.error = none ∧
        ended.val.state = st' ∧ ended.val.output = out := by
  have ht : ¬(msg.shouldTransferValue = true ∧ msg.value ≠ 0) := fun h => h.2 hv
  have hst : startState fork msg S = S := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have spec' : Logic.SpecG fork
      (At code msg 0 [] .empty msg.gas (startState fork msg S) ss)
      (Halted false out g' st' ss') := by
    rw [hst]
    exact spec
  obtain ⟨stopped, hrf, hq⟩ := spec'.runFrame
    (bound := msg.gas) (runChild := processRunner fork msg.gas)
    (At.startFrame hcode (startState fork msg S) ss)
    (Nat.le_refl _)
  have hmap := processMessage_map_val ht noPre hrf
  obtain ⟨-, he, ho, -, hs, -⟩ := hq
  have he' : stopped.error = none := by simpa using he
  cases hpm : processMessage (Meter := Nat) fork msg S ss with
  | error e =>
    rw [hpm] at hmap
    simp [Except.map] at hmap
  | ok ended =>
    rw [hpm] at hmap
    have hc : ended.1 = stopped := by
      simp only [Except.map, Except.ok.injEq] at hmap
      rw [hmap, rollbackOnError_of_error_eq_none he']
    exact ⟨ended, rfl, by rw [hc]; exact he', by rw [hc, hs], by rw [hc, ho]⟩

/-- From Paris, the run that `processMessage` makes of a message with no value whose frame has a
specification `Logic.SpecG` (so the frame sends no message) is `Seq.Clean` for a contract at
`L` as soon as the message itself meets `Q` when it runs at `L`: the run has that one event. -/
theorem clean_of_spec (hparis : .paris ≤ fork) {L : Address} {CODE' : ByteArray}
    {Q : Message fork → State.TransactionState → Prop} {msg : Message fork}
    {S : State.TransactionState} {ss : Substate} {code : ByteArray}
    {Post : Evm fork Nat → Prop}
    (hcode : msg.code = code) (hv : msg.value = 0)
    (spec : Logic.SpecG fork (At code msg 0 [] .empty msg.gas S ss) Post)
    (hq : msg.currentTarget = L → Q msg S) :
    Seq.Clean L CODE' Q msg S ss (GasMeter.start msg.gas msg.reservoir) := by
  have ht : ¬(msg.shouldTransferValue = true ∧ msg.value ≠ 0) := fun h => h.2 hv
  have h2 : startState fork msg S = S := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hs1 : ∀ state1, Seq.startSt msg S = .ok state1 → state1 = S := by
    intro state1 hst
    unfold Seq.startSt at hst
    rw [if_neg ht] at hst
    exact (Except.ok.inj hst).symm.trans h2
  have hsub : Seq.startSub msg ss = ss := by
    unfold Seq.startSub
    rw [if_neg ht]
  refine Seq.clean_of_no_sent ?_ (fun state1 hst hL => by rw [hs1 state1 hst]; exact hq hL)
  intro evm0 fo c m
  obtain ⟨-, state1, hst, rfl⟩ := fo
  rw [hsub, hs1 state1 hst]
  exact Seq.not_sent_of_specG spec (At.startFrame hcode S ss) _ c m

end PepeVerify.Sanity

/-- Closes a bound `cost < gas` of a path theorem for the gas 1000000: the cost is a sum of
numbers, of prices of a slot read (at most 2100 each) and of prices of a write (at most 110020
each). -/
macro "gas_below" hfork:term : tactic =>
  `(tactic| (
    show _ < 1000000
    apply PepeVerify.Sanity.lt_of_le_bound
    · repeat' first
        | exact _root_.UsdtVerify.slotCost_le _
        | exact PepeVerify.Sanity.writeCost_le_all $hfork _ _ _ _
        | apply Nat.add_le_add
        | exact Nat.le_refl _
    · decide))

namespace PepeVerify.Sanity

open UsdtVerify
open TokenKit
open PepeVerify PepeVerify.Paths UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.State.TransactionState
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork}

/-! ## The state and the call -/

/-- The address of the PEPE token on Ethereum mainnet. -/
def PEPE_ADDRESS : Address :=
  #v[0x69, 0x82, 0x50, 0x81, 0x45, 0x45, 0x4c, 0xe3, 0x25, 0xdd, 0xbe, 0x47, 0xa2, 0x5d, 0x4e,
    0xc3, 0xd2, 0x31, 0x19, 0x33]

/-- The address word of `PEPE_ADDRESS`. -/
theorem pepe_address_word :
    PEPE_ADDRESS.toU256 = (0x6982508145454ce325ddbe47a25d4ec3d2311933 : U256) := by decide

/-- The address of PEPE is no precompile, at any fork. -/
theorem notPrecompile_pepe :
    Precompiles.isPrecompile fork PEPE_ADDRESS.toU256.toNat = false := by
  have h : (0x6982508145454ce325ddbe47a25d4ec3d2311933 : U256).toNat =
      0x6982508145454ce325ddbe47a25d4ec3d2311933 := by decide
  rw [pepe_address_word, h]
  rfl

/-- The start state: one account, at `PEPE_ADDRESS`, that holds the code of PEPE;
the owner (slot 0) is the address 2, the balance of `Witness.CALLER1` is 5, `_totalSupply` (slot 3) is 5, every other slot is 0. -/
abbrev wState : State.TransactionState :=
  codeState PEPE_ADDRESS [(0, 2), (mapSlot Witness.CALLER1W 1, 5), (3, 5)] CODE

/-- The call `transfer(2, 1)` from `Witness.CALLER1` to `PEPE_ADDRESS`: no value, gas limit
1000000. -/
def m_w (b : BlockEnvironment fork) (t : TransactionEnvironment fork) : Message fork :=
  { sMsg b t PEPE_ADDRESS Witness.CALLER1 CODE (data2 SEL_transfer 2 1) with gas := 1000000 }

/-- The three address words of the call: the caller, the receiver 2 and the amount word 1. -/
abbrev W_KEYS : List U256 := [Witness.CALLER1W, 2, 1]

/-- The account at `PEPE_ADDRESS` of `wState` holds the code of PEPE. `hH`: the hash of the code
is not the hash of the empty code. -/
theorem holdsCode_wState (hH : hashOf CODE ≠ EMPTY_CODE_HASH) :
    Seq.HoldsCode PEPE_ADDRESS CODE wState :=
  holdsCode_codeState _ _ hH

/-- THE START INVARIANT HOLDS in `wState` (under `Sep W_KEYS`): the sum of the balances of the
2^160 addresses is `_totalSupply`. Of `hA` it uses three facts: no other address word has the
balance slot of the caller, and the slots 0 and 3 are balance slots of no address. -/
theorem inv_wState (hA : Sep W_KEYS) : Inv PEPE_ADDRESS wState := by
  have hu : Supply.UniqBal 1 Witness.CALLER1W := hA.uniq _ (by simp)
  have ha : Witness.CALLER1W.toNat < 2 ^ 160 := by decide
  have hfg : ∀ i : Nat, i < 2 ^ 160 → i ≠ Witness.CALLER1W.toNat →
      Supply.bal 1 PEPE_ADDRESS wState i = (fun _ => (0 : Int)) i := by
    intro i hi hne
    have hi' : i < 2 ^ 256 := Nat.lt_trans hi (by decide)
    have ht : (BitVec.ofNat 256 i).toNat = i := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hi'
    have hx : (BitVec.ofNat 256 i).toNat < 2 ^ 160 := by rw [ht]; exact hi
    have hk0 : ¬ (0 : U256) = mapSlot (BitVec.ofNat 256 i) 1 := hA.fixed.1 _ hx
    have hk1 : ¬ mapSlot Witness.CALLER1W 1 = mapSlot (BitVec.ofNat 256 i) 1 := by
      intro e
      have h1 := hu (BitVec.ofNat 256 i) hx e.symm
      exact hne (by rw [← ht, h1])
    have hk2 : ¬ (3 : U256) = mapSlot (BitVec.ofNat 256 i) 1 := hA.total _ hx
    show ((storageAt wState PEPE_ADDRESS (mapSlot (BitVec.ofNat 256 i) 1)).toNat : Int) = 0
    rw [storageAt_codeState, storageAt_sState_cons, if_neg hk0, storageAt_sState_cons, if_neg hk1, storageAt_sState_cons, if_neg hk2, storageAt_sState_nil]
    rfl
  have hb : storageAt wState PEPE_ADDRESS (mapSlot Witness.CALLER1W 1) = 5 := by
    rw [storageAt_codeState]
    simp only [storageAt_sState_cons, storageAt_sState_nil]
    decide +kernel
  have h3 : storageAt wState PEPE_ADDRESS (3 : U256) = 5 := by
    rw [storageAt_codeState]
    simp only [storageAt_sState_cons, storageAt_sState_nil]
    decide +kernel
  show Supply.D 1 3 PEPE_ADDRESS wState = 0
  unfold Supply.D Supply.sumBal
  rw [Supply.sumTo_update (f := fun _ => (0 : Int)) (a := Witness.CALLER1W.toNat) (2 ^ 160) ha
    hfg, Seq.sumTo_zero _ _ (fun _ _ => rfl)]
  show (0 : Int) - 0 +
    ((storageAt wState PEPE_ADDRESS
      (mapSlot (BitVec.ofNat 256 Witness.CALLER1W.toNat) 1)).toNat : Int) -
    ((storageAt wState PEPE_ADDRESS (3 : U256)).toNat : Int) = 0
  rw [Supply.ofNat_toNat, hb, h3]
  decide

/-- A GOOD STATE EXISTS (under `hH` and `hA`): `wState` holds the code of PEPE at
`PEPE_ADDRESS` and the invariant holds. -/
theorem good_wState (hH : hashOf CODE ≠ EMPTY_CODE_HASH) (hA : Sep W_KEYS) :
    Seq.Good PEPE_ADDRESS CODE (Inv PEPE_ADDRESS) wState :=
  ⟨holdsCode_wState hH, inv_wState hA⟩

/-! ## The closed instance -/

set_option maxHeartbeats 1000000 in
/-- THE CLOSED INSTANCE. From Paris and before Glamsterdam, in the state `wState` (good, by
`good_wState`): EthLib's `processMessage` ends the message `transfer(2, 1)` with no error;
one token moves from the caller to the address 2: the caller has 4, the address 2 has 1, `_totalSupply` is still 5; the run meets `Seq.Clean`, the
run-local hypothesis of `supply_message_any_depth`; and so, by that theorem, the end state is
good: `PEPE_ADDRESS` holds the code of PEPE and the sum of the balances is `_totalSupply`.

Hypotheses (keccak, not proved): `hA` on the three words of the call, `hH` on the hash of the
code of PEPE. -/
theorem transfer_closed (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate)
    (hH : hashOf CODE ≠ EMPTY_CODE_HASH) (hA : Sep W_KEYS) :
    Seq.Good PEPE_ADDRESS CODE (Inv PEPE_ADDRESS) wState ∧
    ∃ ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ (m_w b t).gas },
      processMessage fork (m_w b t) wState ss = .ok ended ∧
      ended.val.error = none ∧ ended.val.output = wordBytes (1 : U256) ∧
      storageAt ended.val.state PEPE_ADDRESS (mapSlot Witness.CALLER1W 1) = 4 ∧
      storageAt ended.val.state PEPE_ADDRESS (mapSlot (2 : U256) 1) = 1 ∧
      storageAt ended.val.state PEPE_ADDRESS ((3 : U256)) = 5 ∧
      Seq.Clean PEPE_ADDRESS CODE (SepMsg fork) (m_w b t) wState ss
        (GasMeter.start (m_w b t).gas (m_w b t).reservoir) ∧
      Seq.Good PEPE_ADDRESS CODE (Inv PEPE_ADDRESS) ended.val.state := by
  have hfork : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hdata : (m_w b t).data = data2 SEL_transfer 2 1 := rfl
  have hsz : (m_w b t).data.size = 68 := by
    rw [hdata]; exact size_data2 size_SEL_transfer _ _
  have hsl : selector (m_w b t).data = selector SEL_transfer := by
    rw [hdata]; exact selector_data2 size_SEL_transfer _ _
  have hA1 : loadWord (m_w b t).data 4 32 = 2 := by
    rw [hdata]; exact Witness.arg1_data2 size_SEL_transfer _ _
  have hA2 : loadWord (m_w b t).data 36 32 = 1 := by
    rw [hdata]; exact Witness.arg2_data2 size_SEL_transfer _ _
  have hval : (m_w b t).value = 0 := rfl
  have hcw : (m_w b t).caller.toU256 = Witness.CALLER1W := Witness.caller1_toU256
  have hct : (m_w b t).currentTarget = PEPE_ADDRESS := rfl
  have hacc : hasAccount wState PEPE_ADDRESS := (holdsCode_wState hH).hasAccount
  have hspec := transfer_p10 (fork := fork) (message := (m_w b t))
    (state := wState) (substate := ss) (gas := (m_w b t).gas)
    hfork
    (by rw [hsz]; decide)
    (by rw [hsz]; decide)
    (by rw [hsl]; decide)
    rfl
    hacc
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_codeState, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_codeState, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_codeState, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_codeState, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_codeState, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_codeState, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_codeState, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_codeState, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_codeState, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_codeState, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_codeState, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_codeState, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by gas_below hfork)
  have hkeys : callKeys (m_w b t) = W_KEYS := by
    unfold callKeys
    rw [hcw, hA1, hA2]
    decide
  have noPre : precompileAddress fork (m_w b t) = none :=
    noPre_of (a := PEPE_ADDRESS) rfl notPrecompile_pepe
  have good0 := good_wState hH hA
  have clean : Seq.Clean PEPE_ADDRESS CODE (SepMsg fork) (m_w b t) wState ss
      (GasMeter.start (m_w b t).gas (m_w b t).reservoir) :=
    clean_of_spec hparis rfl hval hspec (fun _ => by
      show Sep (callKeys (m_w b t))
      rw [hkeys]
      exact hA)
  obtain ⟨ended, hpm, hok, hst, hout⟩ := spec_process hparis rfl noPre hval hspec
  have sane : Seq.Sane PEPE_ADDRESS CODE (m_w b t) :=
    fun _ => ⟨rfl, rfl, by rw [hsz]; decide⟩
  refine ⟨good0, ended, hpm, hok, hout, ?_, ?_, ?_, clean,
    supply_message_any_depth hfork sane good0 clean hpm⟩
  · rw [hst]
    simp (disch := supply_side) only
      [hcw, hA1, hA2, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_codeState, storageAt_sState_cons, storageAt_sState_nil]
    <;> decide +kernel
  · rw [hst]
    simp (disch := supply_side) only
      [hcw, hA1, hA2, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_codeState, storageAt_sState_cons, storageAt_sState_nil]
    <;> decide +kernel
  · rw [hst]
    simp (disch := supply_side) only
      [hcw, hA1, hA2, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_codeState, storageAt_sState_cons, storageAt_sState_nil]
    <;> decide +kernel

end PepeVerify.Sanity
