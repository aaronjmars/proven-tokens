import TokenKit.Evm.Ether

/-!
# A move of ether keeps the storage of a contract with code

EthLib's `moveEther` debits the sender and credits the recipient. From Paris a change of an
account deletes it, and its storage, when it is left empty. An account with code is never empty.

- `moveEther_keeps_storage`: a successful move of ether between ANY two addresses (the contract
  may be the sender, the recipient, both or neither) keeps every storage word of a contract that
  holds code. It joins EthLib's `getStorage_moveEther_of_ne` (the contract is neither party) and
  `sameOutside_moveEther_self` (a move to itself) with `moveEther_into` and `moveEther_outOf`.

This is what the message layer does to the storage of a contract when it moves the value of a
message, so no theorem needs it as a hypothesis. Nothing here is about one token.
-/

namespace TokenKit

open UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.State.TransactionState

variable {fork : Fork} {tx tx' : State.TransactionState} {C a b : Address} {v : U256}

/-- A move of ether between any two addresses keeps every storage word of a contract with
code. -/
theorem moveEther_keeps_storage (hcode : (tx.getAccount C).codeHash ≠ EMPTY_CODE_HASH)
    (h : tx.moveEther fork a b v = .ok tx') (n : U256) :
    storageAt tx' C n = storageAt tx C n := by
  by_cases hab : a = b
  · subst hab
    by_cases hC : C = a
    · subst hC
      unfold storageAt
      rw [(sameOutside_moveEther_self hcode h C List.not_mem_nil).2.1]
    · unfold storageAt
      rw [getStorage_moveEther_of_ne h hC hC]
  · by_cases hCa : C = a
    · subst hCa
      exact (moveEther_outOf hab hcode h).1 n
    · by_cases hCb : C = b
      · subst hCb
        exact (moveEther_into hab hcode h).1 n
      · unfold storageAt
        rw [getStorage_moveEther_of_ne h hCa hCb]

end TokenKit
