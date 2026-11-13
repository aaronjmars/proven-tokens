import TokenKit.Seq.Run

/-!
# A frame rule for a frame that makes a read-only outside call (audit 4, SKY-3)

Hand-written, token-neutral (to merge into the kit, TokenKit/Seq/Run.lean).

The interface `Seq.FrameKeepsR` of the kit offers a frame of the token two facts about the
messages that the frame sends: what the real runner keeps on them (`KeepsOn ... GoodKept`).
A frame whose only outside calls are

- a call to a precompile (ECRECOVER at address 1), and
- a read-only STATICCALL to an account with ANY code (the owner contract of ERC-1271),

needs neither fact: the theorem for its frame is about EthLib's real runner
`processRunner fork bound` and bounds the outside call itself (for the STATICCALL:
`TokenKit.staticcall_kept` of TokenKit/Evm/StaticCall.lean, which shows from the real runner
that the run of a static message changes no storage word of any account, whatever code it runs
and whatever it sends at any depth). `RealFrameKeeps` is that form; `frameKeepsR_of_real` says
it meets the interface. Nothing is assumed about the runner or about the code that is called.

What the kit then adds on top (`Seq.processMessage_good_local`, `Seq.processTransaction_good`):
the outside run itself is a message of the transaction like any other, so if the owner contract
calls back into the token (a STATICCALL keeps the callee static, so only read-only re-entry is
possible), that entry is one more event of the run, covered by the induction of the kit with
its own run-local hypothesis `Q`.
-/

set_option autoImplicit false

namespace SkyVerify


open TokenKit
open EthLib.Base (Fork Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- A frame theorem about EthLib's REAL runner that uses no fact about the messages the frame
sends: from `Q` of the message and its start state and `P` of the start state, a frame of
`CODE` at `L` (cap `G` on the gas bound) that ends with no error ends in a state with `P`.
This is the form of `supply_permit` and `supply_permitBytes` (each makes a STATICCALL to the
owner with any code). -/
def RealFrameKeeps (fork : Fork) (G : Nat) (L : Address) (CODE : ByteArray)
    (P : State.TransactionState → Prop) (Q : Message fork → State.TransactionState → Prop) :
    Prop :=
  ∀ {bound : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {gas : Nat} {evm s : Evm fork Nat}
    (within : GasMeter.gasHeld evm.gas ≤ bound), bound ≤ G →
    message.currentTarget = L → message.code = CODE → message.data.size < 2 ^ 256 →
    Q message state → P state →
    UsdtVerify.At CODE message 0 [] .empty gas state substate evm →
    Evm.runFrame (step fork) (step_decreases fork) bound
      (Logic.processRunner fork (Meter := Nat) bound) evm within = .ok s →
    s.error = none → P s.state

/-- THE FRAME RULE: a frame theorem of the form `RealFrameKeeps` (for a frame whose outside
calls are a precompile call and a read-only STATICCALL to any code, bounded by the real runner)
meets the interface `Seq.FrameKeepsR` of the kit. The facts on the runner that the interface
offers are not used. -/
theorem frameKeepsR_of_real {fork : Fork} {G : Nat} {L : Address} {CODE : ByteArray}
    {P : State.TransactionState → Prop} {Q : Message fork → State.TransactionState → Prop}
    (h : RealFrameKeeps fork G L CODE P Q) : Seq.FrameKeepsR fork G L CODE P Q := by
  intro bound message state substate gas evm s within hG ht hcode hsize hq good _ hat hrun herr
  exact h within hG ht hcode hsize hq good.2 hat hrun herr

end SkyVerify
