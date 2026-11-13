import WbtcVerify.Wbtc.Reclaim.Whole
import WbtcVerify.Wbtc.Sep
import WbtcVerify.Wbtc.Reenter

/-!
# `reclaimToken`: the invariant across its two outside calls

`reclaimToken(address token)` sends two messages to a token that the owner chooses, which may be
any contract, WBTC itself included. WBTC's own opcodes only read (slot 5 and the code size of
the token), so what a successful run does to the state is what the two children do.

What is proved:

- `reclaim_two_calls`: the decomposition. A run that ends with no error sent exactly two
  messages; each is described by EthLib's `SentVia` (from a frame whose state reads as the state
  before the call, to the token, value 0, running the code that the state holds for the address
  the call resolves to), with data of at most 36 and 68 bytes; the second is sent from the state
  that the first child left; the end state is the state that the second child left.
- `sane_of_sentVia`: such a message is `Reenter.Sane`: when it goes to `L`, an account that
  holds `CODE`, it runs `CODE` (the self call `reclaimToken(WBTC)` included), since `CODE` is no
  EIP-7702 delegation (`hdel`).
- `reclaim_good`: the form the reentrancy induction needs, for any invariant `P` that reads the
  storage of WBTC only: a successful `reclaimToken` from a good state ends in a good state, when
  every sane message that the runner ends with no error keeps a good state good.
- `ReclaimCalleeKeeps`: the LOCAL assumption on the two messages (exact target, exact data, the
  second sent from the state the first child left, with the owner read after the first call and
  the returned balance in its data): each keeps `Inv` when its run ends with no error.
- `supply_reclaimToken`: under `ReclaimCalleeKeeps`, a successful `reclaimToken` keeps `Inv`.
  NO hypothesis on keccak (`Sep` is not needed: the function reads slot 5 only and writes
  nothing), and no assumption that the token is not WBTC.
- `reclaimCalleeKeeps_of_keepsOn`: the local assumption follows from the assumption on the
  runner of `reclaim_good` when the account holds the code.

Assumed: Berlin ≤ fork < Glamsterdam, one counter of gas, call data below 2^256 bytes;
`hdel : delegatedAddress CODE = none` (a fact about the bytes of WBTC, proved in the reentrancy
stream as `code_not_delegated`); `so : Reenter.StorageOnly L P` where stated.
Not covered: runs that end with an error; that the runner assumption holds for the real runner
(the reentrancy stream proves it from `reclaim_good`).
-/

set_option autoImplicit false

namespace WbtcVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open WbtcVerify.Paths WbtcVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-! ## The state at each call reads as the state before -/

/-- The state of the frame at a CALL of `reclaimToken` reads as the state before: only two
reads were recorded. -/
theorem readsAs_rcSt (message : Message fork) (S : State.TransactionState) (tok : Address) :
    ReadsAs (rcSt message S tok) S :=
  ((ReadsAs.refl S).recordStorageRead _ _).recordAccountRead _

/-- The data of a message read from memory has at most the size asked for. -/
theorem size_read_lt (m : ByteArray) (a k : Nat) (hk : k < 2 ^ 256) :
    (memoryReadBytes m a k).size < 2 ^ 256 :=
  Nat.lt_of_le_of_lt (Reenter.size_memoryReadBytes_le m a k) hk

/-! ## The decomposition -/

/-- THE DECOMPOSITION of a successful `reclaimToken`. A run that ends with no error sent exactly
two messages, both to the token `rcToken message`:

- `msg1` from `caller1`, whose state reads as the state before; its child `child1` ended with
  no error;
- `msg2` from `caller2`, whose state reads as the state that `child1` left; its child `child2`
  ended with no error;
- the state at the end is the state that `child2` left.

`SentVia` gives, for each message: the address it goes to, its caller (WBTC), value 0, and the
code it runs (the code that the state holds for the address the call resolves to). The data are
exact (`rcMem1`, `rcMem2`: see `ok_reclaim` for all the facts, with the gas). -/
theorem reclaim_two_calls (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x17ffc320)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    ∃ (caller1 : Evm fork Nat) (msg1 : Message fork) (child1 : Evm fork Nat)
      (caller2 : Evm fork Nat) (msg2 : Message fork) (child2 : Evm fork Nat),
      SentVia message (rcSt message state (rcToken message)) (rcToken message) caller1 msg1 ∧
      ReadsAs caller1.state state ∧
      msg1.data = memoryReadBytes (rcMem1 message) 128 36 ∧
      Ran runChild caller1 msg1 child1 ∧ child1.error = none ∧
      SentVia message (rcSt message child1.state (rcToken message)) (rcToken message) caller2
        msg2 ∧
      ReadsAs caller2.state child1.state ∧
      msg2.data = memoryReadBytes (rcMem2 message child1.state
        (rcOut (rcMem1 message) child1.output)
        (loadWord (memoryReadBytes child1.output 0 32) 0 32)) 128 68 ∧
      Ran runChild caller2 msg2 child2 ∧ child2.error = none ∧
      s.state = child2.state := by
  obtain ⟨-, -, c1, route1, caller1, msg1, child1, c2, route2, caller2, msg2, child2, -, -,
    hvia1, -, md1, -, hran1, herr1, -, -, -, hvia2, -, md2, -, hran2, herr2, -, -, hst, -⟩ :=
    ok_reclaim hfork hglam hsize' hsel start hrun hok
  have r1 : ReadsAs caller1.state state := by
    obtain ⟨_, _, -, -, hr, -⟩ := hvia1
    exact hr.trans (readsAs_rcSt _ _ _)
  have r2 : ReadsAs caller2.state child1.state := by
    obtain ⟨_, _, -, -, hr, -⟩ := hvia2
    exact hr.trans (readsAs_rcSt _ _ _)
  exact ⟨caller1, msg1, child1, caller2, msg2, child2, hvia1, r1, md1, hran1, herr1, hvia2, r2,
    md2, hran2, herr2, hst⟩

/-! ## The messages are sane, the self call included -/

/-- A message sent by a CALL with no value from a state `S` in which `L` holds `CODE`: when it
goes to `L` it runs `CODE` (it is no delegation, `hdel`), it has a target, and its data are
below 2^256 bytes. This covers the direct self call. -/
theorem sane_of_sentVia {L : Address} {CODE : ByteArray} (hdel : delegatedAddress CODE = none)
    {S : State.TransactionState} {tok : Address} {caller : Evm fork Nat} {msg : Message fork}
    (hold : Reenter.HoldsCode L CODE S) (hvia : SentVia message S tok caller msg)
    (hsize : msg.data.size < 2 ^ 256) : Reenter.Sane L CODE msg := by
  intro hL
  obtain ⟨c, route, hcode, hroute, -, -, hcur, htar, -, hmc, -⟩ := hvia
  have htok : tok = L := hcur.symm.trans hL
  subst htok
  have hc : c = CODE := Except.ok.inj (hcode.symm.trans hold.1)
  subst hc
  refine ⟨?_, by rw [htar]; rfl, hsize⟩
  rcases route with _ | ⟨d, c'⟩
  · exact hmc
  · exact absurd (hdel.symm.trans hroute.2.1) (by simp)

/-- One outside call of `reclaimToken` keeps a good state good, under the assumption on the
runner. -/
theorem good_through_call {P : State.TransactionState → Prop}
    (so : Reenter.StorageOnly message.currentTarget P) (hdel : delegatedAddress CODE = none)
    (keeps : Logic.KeepsOn runChild (fun _ msg => Reenter.Sane message.currentTarget CODE msg)
      (Reenter.GoodKept message.currentTarget CODE P))
    {S : State.TransactionState} {tok : Address} {caller : Evm fork Nat} {msg : Message fork}
    {child : Evm fork Nat}
    (good : Reenter.Good message.currentTarget CODE P S)
    (hvia : SentVia message (rcSt message S tok) tok caller msg)
    (hsize : msg.data.size < 2 ^ 256)
    (hran : Ran runChild caller msg child) (herr : child.error = none) :
    Reenter.Good message.currentTarget CODE P child.state := by
  have r0 : ReadsAs (rcSt message S tok) S := readsAs_rcSt _ _ _
  have gS : Reenter.Good message.currentTarget CODE P (rcSt message S tok) :=
    Reenter.Good.of_readsAs so r0 good
  have sane : Reenter.Sane message.currentTarget CODE msg := sane_of_sentVia hdel gS.1 hvia hsize
  have rc : ReadsAs caller.state (rcSt message S tok) := by
    obtain ⟨_, _, -, -, hr, -⟩ := hvia
    exact hr
  obtain ⟨lt, child', hrc, rfl⟩ := hran
  exact keeps caller msg lt child' hrc sane herr (Reenter.Good.of_readsAs so rc gS)

/-! ## The form for the reentrancy induction -/

/-- A successful `reclaimToken` frame keeps a good state good (`L` holds the code of WBTC and
`P` holds), for any `P` that reads the storage of WBTC only, when every sane message that its
runner ends with no error keeps a good state good. The token is any address, WBTC included. -/
theorem reclaim_good {P : State.TransactionState → Prop} (hfork : .berlin ≤ fork)
    (hglam : fork < .glamsterdam)
    (so : Reenter.StorageOnly message.currentTarget P) (hdel : delegatedAddress CODE = none)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x17ffc320)
    (keeps : Logic.KeepsOn runChild (fun _ msg => Reenter.Sane message.currentTarget CODE msg)
      (Reenter.GoodKept message.currentTarget CODE P))
    (good : Reenter.Good message.currentTarget CODE P state)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    Reenter.Good message.currentTarget CODE P s.state := by
  obtain ⟨caller1, msg1, child1, caller2, msg2, child2, hvia1, -, md1, hran1, herr1, hvia2, -,
    md2, hran2, herr2, hst⟩ := reclaim_two_calls hfork hglam hsize' hsel start hrun hok
  have g1 := good_through_call so hdel keeps good hvia1
    (by rw [md1]; exact size_read_lt _ _ _ (by decide)) hran1 herr1
  have g2 := good_through_call so hdel keeps g1 hvia2
    (by rw [md2]; exact size_read_lt _ _ _ (by decide)) hran2 herr2
  rw [hst]
  exact g2

/-! ## The supply invariant under a local assumption on the two messages -/

/-- The sum of the balances depends on the storage words of `C` only. -/
theorem rc_sumBal_congr {C : Address} {S S' : State.TransactionState}
    (h : ∀ k : U256, storageAt S' C k = storageAt S C k) :
    Supply.sumBal 0 C S' = Supply.sumBal 0 C S := by
  unfold Supply.sumBal
  exact Supply.sumTo_congr _ (fun i _ => by
    show ((storageAt S' C _).toNat : Int) = ((storageAt S C _).toNat : Int)
    rw [h])

/-- The invariant holds in a state that reads as a state where it holds. -/
theorem inv_of_readsAs {L : Address} {tx S : State.TransactionState} (r : ReadsAs tx S)
    (h : Inv L S) : Inv L tx := by
  have hk : ∀ k : U256, storageAt tx L k = storageAt S L k :=
    fun k => (r.1 L (by simp)).2.1 _
  unfold Inv Supply.Inv Supply.D at h ⊢
  rw [rc_sumBal_congr hk, hk]
  exact h

/-- The LOCAL assumption of `reclaimToken` on the two messages that its CALLs send.

The first message goes to the token from a frame whose state is the state before with two reads
recorded (`SentVia` with `rcSt message state`), with the data `balanceOf(address(this))`. When
its run by `runChild` ends with no error it keeps the invariant, and then the second message,
which goes to the token from the state that the first child left (with two reads recorded),
with the data `transfer(owner read from that state, first word returned by the first child)`,
keeps the invariant when its run ends with no error.

Nothing is asked about any other message, and the token may be WBTC itself. -/
def ReclaimCalleeKeeps (runChild : MessageRunner fork Nat bound) (message : Message fork)
    (state : State.TransactionState) : Prop :=
  ∀ (caller1 : Evm fork Nat) (msg1 : Message fork) (child1 : Evm fork Nat),
    Ran runChild caller1 msg1 child1 →
    SentVia message (rcSt message state (rcToken message)) (rcToken message) caller1 msg1 →
    msg1.data = memoryReadBytes (rcMem1 message) 128 36 →
    child1.error = none →
    Inv message.currentTarget caller1.state →
    Inv message.currentTarget child1.state ∧
    ∀ (caller2 : Evm fork Nat) (msg2 : Message fork) (child2 : Evm fork Nat),
      Ran runChild caller2 msg2 child2 →
      SentVia message (rcSt message child1.state (rcToken message)) (rcToken message) caller2
        msg2 →
      msg2.data = memoryReadBytes (rcMem2 message child1.state
        (rcOut (rcMem1 message) child1.output)
        (loadWord (memoryReadBytes child1.output 0 32) 0 32)) 128 68 →
      child2.error = none →
      Inv message.currentTarget caller2.state →
      Inv message.currentTarget child2.state

/-- A successful `reclaimToken` keeps the invariant (the sum of the balances is `totalSupply_`)
under the local assumption on its two messages. No hypothesis on keccak, none on the code at
the address of WBTC, and the token may be WBTC itself. -/
theorem supply_reclaimToken (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x17ffc320)
    (keeps : ReclaimCalleeKeeps runChild message state)
    (hinv : Inv message.currentTarget state)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    Inv message.currentTarget s.state := by
  obtain ⟨caller1, msg1, child1, caller2, msg2, child2, hvia1, r1, md1, hran1, herr1, hvia2, r2,
    md2, hran2, herr2, hst⟩ := reclaim_two_calls hfork hglam hsize' hsel start hrun hok
  obtain ⟨i1, k2⟩ := keeps caller1 msg1 child1 hran1 hvia1 md1 herr1 (inv_of_readsAs r1 hinv)
  rw [hst]
  exact k2 caller2 msg2 child2 hran2 hvia2 md2 herr2 (inv_of_readsAs r2 i1)

/-- The local assumption follows from the assumption on the runner of `reclaim_good` (each sane
message that the runner ends with no error keeps a good state good), when the account holds the
code. `so` is proved in the reentrancy stream (`storageOnly_inv`). -/
theorem reclaimCalleeKeeps_of_keepsOn
    (so : Reenter.StorageOnly message.currentTarget (Inv message.currentTarget))
    (hdel : delegatedAddress CODE = none)
    (keeps : Logic.KeepsOn runChild (fun _ msg => Reenter.Sane message.currentTarget CODE msg)
      (Reenter.GoodKept message.currentTarget CODE (Inv message.currentTarget)))
    (hold : Reenter.HoldsCode message.currentTarget CODE state) :
    ReclaimCalleeKeeps runChild message state := by
  intro caller1 msg1 child1 hran1 hvia1 md1 herr1 hinv1
  have r1 : ReadsAs caller1.state state := by
    obtain ⟨_, _, -, -, hr, -⟩ := hvia1
    exact hr.trans (readsAs_rcSt _ _ _)
  have g0 : Reenter.Good message.currentTarget CODE (Inv message.currentTarget) state :=
    Reenter.Good.to_readsAs so r1 ⟨Reenter.HoldsCode.of_readsAs r1 hold, hinv1⟩
  have g1 := good_through_call so hdel keeps g0 hvia1
    (by rw [md1]; exact size_read_lt _ _ _ (by decide)) hran1 herr1
  refine ⟨g1.2, ?_⟩
  intro caller2 msg2 child2 hran2 hvia2 md2 herr2 _
  exact (good_through_call so hdel keeps g1 hvia2
    (by rw [md2]; exact size_read_lt _ _ _ (by decide)) hran2 herr2).2

end WbtcVerify
