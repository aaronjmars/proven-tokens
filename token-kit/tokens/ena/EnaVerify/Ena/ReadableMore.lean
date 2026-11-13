import EnaVerify.Ena.Readable
import EnaVerify.Ena.Permit
import EnaVerify.Ena.Gen.Loops

/-!
# Readable corollaries written by hand

The functions that `scripts/gen_readable.py` does not describe:

- `domainSeparator_readable`: DOMAIN_SEPARATOR() returns `domainSep message` (the cached
  constant at the deployed address on chain 1, else the rebuilt hash), with no slot change and
  no log.
- `renounceOwnership_never`: renounceOwnership() never ends with no error (the contract
  overrides it to revert).
- `name_readable`, `symbol_readable`, `eip712Domain_readable`: the three functions that return
  dynamic data change no storage word of any account and add no log. Their exact return data is
  not stated.

`permit` is in `Ena/PermitSeq.lean` (`permit_readable`); it needs the real runner.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace EnaVerify.Readable

open UsdtVerify
open TokenKit TokenKit.Complete TokenKit.Readable
open EnaVerify EnaVerify.Paths EnaVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {message : Message fork}
variable {state : State.TransactionState} {substate : Substate}
variable {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- DOMAIN_SEPARATOR(). Success needs no value. Then: returns `domainSep message` (the constant
cached at deployment when the contract is at the deployed address and the chain id is 1, else
the hash rebuilt from the chain id and the address); the state and the substate are unchanged
(no slot changes, no log). -/
theorem domainSeparator_readable (hfork : .shapella ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x3644e515)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    message.value = 0 ∧
    (s.output = wordBytes (domainSep message) ∧
      (∀ k, storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) ∧
      s.substate.logs = substate.logs) := by
  rcases ok_domainSeparator hfork hsize' hsel start hrun hok with
    ⟨hc1, hc2, hc3, -, hout, -, hst, hsub⟩ |
    ⟨hc1, hc2, hc3, -, hout, -, hst, hsub⟩ |
    ⟨hc1, hc2, -, hout, -, hst, hsub⟩
  · have e7 : ENA_ADDRESS = message.currentTarget.toU256 := eq_of_isZero_equal hc2
    have e8 := eq_of_isZero_equal hc3
    have hD : domainSep message = CACHED_DOMAIN := by
      unfold domainSep
      exact if_pos ⟨e7, e8⟩
    refine ⟨value_of_cond hc1, ?_, fun k => by rw [hst], by rw [hsub]⟩
    rw [hout, hD, CACHED_DOMAIN]
  · have n8 := ne_of_isZero_equal hc3
    have hD : domainSep message = domainRebuilt message := by
      unfold domainSep
      exact if_neg (fun h => n8 h.2)
    refine ⟨value_of_cond hc1, ?_, fun k => by rw [hst], by rw [hsub]⟩
    rw [hout, hD, domainRebuilt]
  · have n7 : ENA_ADDRESS ≠ message.currentTarget.toU256 := ne_of_isZero_equal hc2
    have hD : domainSep message = domainRebuilt message := by
      unfold domainSep
      exact if_neg (fun h => n7 h.1)
    refine ⟨value_of_cond hc1, ?_, fun k => by rw [hst], by rw [hsub]⟩
    rw [hout, hD, domainRebuilt]

/-- renounceOwnership() never ends with no error: every run of it ends with an error. -/
theorem renounceOwnership_never (hfork : .shapella ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x715018a6)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) : s.error ≠ none :=
  fun hok => ok_renounceOwnership hfork hsize' hsel start hrun hok

/-- name(). A run that ends with no error changes no storage word of any account and adds no
log. -/
theorem name_readable (hfork : .shapella ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x06fdde03)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    (∀ (c : Address) (k : U256), storageAt s.state c k = storageAt state c k) ∧
      s.substate.logs = substate.logs :=
  have h := Loops.ro_name hfork hsize' hsel start hrun hok
  ⟨h.storage, h.logs⟩

/-- symbol(). A run that ends with no error changes no storage word of any account and adds no
log. -/
theorem symbol_readable (hfork : .shapella ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x95d89b41)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    (∀ (c : Address) (k : U256), storageAt s.state c k = storageAt state c k) ∧
      s.substate.logs = substate.logs :=
  have h := Loops.ro_symbol hfork hsize' hsel start hrun hok
  ⟨h.storage, h.logs⟩

/-- eip712Domain(). A run that ends with no error changes no storage word of any account and
adds no log. -/
theorem eip712Domain_readable (hfork : .shapella ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x84b0196e)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    (∀ (c : Address) (k : U256), storageAt s.state c k = storageAt state c k) ∧
      s.substate.logs = substate.logs :=
  have h := Loops.ro_eip712Domain hfork hsize' hsel start hrun hok
  ⟨h.storage, h.logs⟩

end EnaVerify.Readable
