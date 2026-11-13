import UsdeVerify.Usde.Gen
import TokenKit.Evm.Precompile
import TokenKit.Evm.Call
import TokenKit.Evm.ReadableOpt

/-!
# `permit` under EthLib's real runner

`permit(owner, spender, value, deadline, v, r, s)` (selector `0xd505accf`, OpenZeppelin
ERC20Permit 4.9) checks the deadline, reads and increments `_nonces[owner]`, builds an EIP-712
digest in memory, checks that `s` is in the lower half of the curve order, calls the precompile
at address 1 (ECRECOVER) with STATICCALL, and compares the address it gets with `owner`. The
generated paths stop at the frame before `GAS STATICCALL` (pc 6035, `Paths.ok_permit`) and start
again after it (pc 6037, `Paths.ok_permitTailC` and `Paths.ok_permitTailR`). This file joins the
two across the call, for `processRunner`, with no assumption on what the precompile returns: the
output is EthLib's own `Precompiles.Ecrecover.compute` (through `TokenKit.recoveredWord`).

The domain separator has two branches in the bytecode (`_domainSeparatorV4`): the constant
cached at deployment when the address of the contract is the deployed address and the chain id
is 1, else the hash rebuilt from the chain id and the address (three paths: cached; same
address, other chain; other address). `domainSep` is that word; both branches are covered.

- `permitStruct`, `permitDigest`, `permitInput`: the struct hash, the digest and the 128 bytes
  given to ECRECOVER, as the code builds them.
- `domainRebuilt`, `domainSep`, `permitBase`: the domain separator and the fixed gas of the code
  before the call, by branch.
- `digest_bytes_at`: the 66 bytes that the code hashes are `0x19 0x01`, the domain separator and
  the struct hash.
- `permit_callC`, `permit_callR`: from the frame at pc 6035 with a memory that holds the four
  input words (the two memory layouts: cached and rebuilt separator), a run of the real runner
  that ends with no error made the call with at least 3000 gas and ended as
  `Paths.permitTailC_ends` says, with the recovered word `recoveredWord (permitInput ...)`.
- `ok_permit_real`: completeness for `permit`. A run of a fresh frame of `CODE` on a `permit`
  message that ends with no error: the checks before the call and `PermitDone` (the gas, and
  the end of `Paths.permitTailC_ends`: the recovered word is not 0 and equals the owner, the
  exact allowance write, the Approval log and the exact gas), from the state where the nonce is
  already incremented.

Scope: from Paris and before Glamsterdam (EthLib's rules of STATICCALL; from Paris a message
does not touch its target). `hdel`: the account at address 1 holds no EIP-7702 delegation code
(a fact of the state, true on chain: precompile accounts hold no code).
-/

set_option maxRecDepth 4096

namespace UsdeVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open UsdeVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

/-- `_PERMIT_TYPEHASH` of the contract:
keccak of `Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)`. -/
def PERMIT_TYPEHASH : U256 :=
  49955707469362902507454157297736832118868343942642399513960811609542965143241

/-- The struct hash: keccak of the type hash and the five words. -/
def permitStruct (owner spender value nonce deadline : U256) : U256 :=
  keccak (memW [PERMIT_TYPEHASH, owner, spender, value, nonce, deadline])

/-- The digest: keccak of `0x19 0x01`, the domain separator and the struct hash. -/
def permitDigest (domain structHash : U256) : U256 :=
  keccak (⟨#[0x19, 0x01]⟩ ++ wordBytes domain ++ wordBytes structHash)

/-- The 128 bytes given to ECRECOVER: the digest, `v`, `r` and `s`. -/
def permitInput (digest v r s : U256) : ByteArray :=
  wordBytes digest ++ wordBytes v ++ wordBytes r ++ wordBytes s

/-- The word `0x1901` shifted to the top of a word, as the code writes it before the domain
separator. -/
def P1901 : U256 :=
  11309588061646438093662687302255421419811724423900836950936401294474059186176

/-- The domain separator cached in the code at deployment (chain id 1, the deployed address). -/
def CACHED_DOMAIN : U256 :=
  52913264502934295635151425816809534945870579946550263777912616301551047572659

/-- The address of the deployed contract, as the code holds it (`_cachedThis`):
`0x4c9edd5852cd905f086c759e8383e09bff1e68b3`. -/
def USDE_ADDRESS : U256 := 437426098194082895061803372304124391670360729779

/-- The first two bytes of a memory of words whose last word, at `o`, is `P1901`. -/
theorem prefix1901_at {ws : List U256} (o : Nat) (hlen : 32 * ws.length = o + 32)
    (hP : loadWord (memoryReadBytes (memW ws) o 32) 0 32 = P1901) :
    memoryReadBytes (memW ws) o 2 = ⟨#[0x19, 0x01]⟩ := by
  have hsz : (memW ws).size = o + 32 := size_memWn ws hlen
  have hw : memoryReadBytes (memW ws) o 32 = wordBytes P1901 :=
    readWord_raw hP hsz (Nat.le_refl _)
  have f2 : o + 2 ≤ (memW ws).size := by rw [hsz]; omega
  have f32 : o + 32 ≤ (memW ws).size := by rw [hsz]; omega
  apply EthLib.Base.eq_of_byteAt
  · rw [size_memoryReadBytes f2]
    rfl
  · intro i
    rw [byteAt_memoryReadBytes f2]
    by_cases h : i < 2
    · rw [if_pos h]
      have hb : EthLib.Base.byteAt (memW ws) (o + i) =
          EthLib.Base.byteAt (wordBytes P1901) i := by
        rw [← hw, byteAt_memoryReadBytes f32, if_pos (by omega)]
      rw [hb]
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hi with rfl | rfl <;> decide +kernel
    · rw [if_neg h]
      exact (EthLib.Base.byteAt_of_size_le (by show 2 ≤ i; omega)).symm

/-- The 66 bytes that `permit` hashes for the digest: `0x19 0x01`, the domain separator and the
struct hash. The memory is the one the code has built at that point: words up to `o + 32` with
`P1901` in the last one, then the writes of the domain separator at `o + 2` and of the struct
hash at `o + 34`. -/
theorem digest_bytes_at {ws : List U256} {DS SH : U256} (o : Nat)
    (hlen : 32 * ws.length = o + 32)
    (hP : loadWord (memoryReadBytes (memW ws) o 32) 0 32 = P1901) :
    memoryReadBytes (memoryWrite (memoryExtend (memoryWrite (memoryExtend (memW ws) 32) (o + 2)
      (wordBytes DS)) 32) (o + 34) (wordBytes SH)) o 66 =
      ⟨#[0x19, 0x01]⟩ ++ wordBytes DS ++ wordBytes SH := by
  have s0 : (memW ws).size = o + 32 := size_memWn ws hlen
  have s1 := size_rawW (v := DS) (n := 32) (o := o + 2) s0 (by omega)
  have s2 := size_rawW (v := SH) (n := 32) (o := o + 34) s1 (by omega)
  refine (memoryReadBytes_add (j := 34) (k := 32) (by rw [s2]; omega) (by decide)
    (by decide)).trans ?_
  have hSH := readWord_raw (load_rawW_self (v := SH) (n := 32) (o := o + 34) s1 (by omega)) s2
    (by omega)
  have hDS := readWord_raw (load_rawW_self (v := DS) (n := 32) (o := o + 2) s0 (by omega)) s1
    (by omega)
  have h34 : memoryReadBytes (memoryWrite (memoryExtend (memoryWrite (memoryExtend (memW ws) 32)
      (o + 2) (wordBytes DS)) 32) (o + 34) (wordBytes SH)) o 34 =
      ⟨#[0x19, 0x01]⟩ ++ wordBytes DS := by
    rw [read_rawW s1 (by omega) (by omega) (by omega)]
    refine (memoryReadBytes_add (j := 2) (k := 32) (by rw [s1]; omega) (by decide)
      (by decide)).trans ?_
    rw [read_rawW s0 (by omega) (by omega) (by omega), prefix1901_at o hlen hP]
    exact congrArg (⟨#[0x19, 0x01]⟩ ++ ·) hDS
  rw [h34]
  exact congrArg ((⟨#[0x19, 0x01]⟩ : ByteArray) ++ wordBytes DS ++ ·) hSH

/-- `digest_bytes_at` for the memory of the branch with the cached domain separator. -/
theorem digest_bytes_352 {ws : List U256} {DS SH : U256} (hlen : 32 * ws.length = 384)
    (hP : loadWord (memoryReadBytes (memW ws) 352 32) 0 32 = P1901) :
    memoryReadBytes (memoryWrite (memoryExtend (memoryWrite (memoryExtend (memW ws) 32) 354
      (wordBytes DS)) 32) 386 (wordBytes SH)) 352 66 =
      ⟨#[0x19, 0x01]⟩ ++ wordBytes DS ++ wordBytes SH :=
  digest_bytes_at 352 hlen hP

/-- `digest_bytes_at` for the memory of the branches that rebuild the domain separator. -/
theorem digest_bytes_544 {ws : List U256} {DS SH : U256} (hlen : 32 * ws.length = 576)
    (hP : loadWord (memoryReadBytes (memW ws) 544 32) 0 32 = P1901) :
    memoryReadBytes (memoryWrite (memoryExtend (memoryWrite (memoryExtend (memW ws) 32) 546
      (wordBytes DS)) 32) 578 (wordBytes SH)) 544 66 =
      ⟨#[0x19, 0x01]⟩ ++ wordBytes DS ++ wordBytes SH :=
  digest_bytes_at 544 hlen hP

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The domain separator as the code rebuilds it: keccak of the EIP-712 domain type hash, the
hash of the name, the hash of the version, the chain id and the address of the contract. -/
def domainRebuilt (m : Message fork) : U256 :=
  keccak (memW [(63076024560530113402979550242307453568063438748328787417531900361828837441551 : U256),
    (800430381884319963266448255313171563733839282559604318839735355180845479980 : U256),
    (90743482286830539503240959006302832933333810038750515972785732718729991261126 : U256),
    BitVec.ofNat 256 m.blockEnv.chainId.toNat, m.currentTarget.toU256])

/-- The domain separator of a call: the cached constant when the contract is at the deployed
address and the chain id is 1, else the rebuilt hash. -/
def domainSep (m : Message fork) : U256 :=
  if USDE_ADDRESS = m.currentTarget.toU256 ∧
      BitVec.ofNat 256 m.blockEnv.chainId.toNat = (1 : U256) then CACHED_DOMAIN
  else domainRebuilt m

/-- The fixed part of the gas of `permit` before the call of ECRECOVER, by branch of the domain
separator. -/
def permitBase (m : Message fork) : Nat :=
  if USDE_ADDRESS = m.currentTarget.toU256 then
    if BitVec.ofNat 256 m.blockEnv.chainId.toNat = (1 : U256) then 1592 else 1845
  else 1835

/-- The slot of `_nonces[owner]` of a `permit` message. -/
abbrev nonceSlot (m : Message fork) : U256 :=
  mapSlot (bitwiseAnd (loadWord m.data 4 32)
    (1461501637330902918203684832716283019655932542975 : U256)) (9 : U256)

/-- The state at the call of ECRECOVER: the nonce of the owner is already incremented. -/
abbrev permitS1 (m : Message fork) (S : State.TransactionState) : State.TransactionState :=
  writeSlot (readSlot S m.currentTarget (nonceSlot m)) m.currentTarget (nonceSlot m)
    (add (storageAt S m.currentTarget (nonceSlot m)) (1 : U256))

/-- The substate at the call of ECRECOVER. -/
abbrev permitSS1 (m : Message fork) (S : State.TransactionState) (ss : Substate) : Substate :=
  storeSub fork (accessSlot ss m.currentTarget (nonceSlot m)) m.currentTarget (nonceSlot m)
    (originalAt (readSlot S m.currentTarget (nonceSlot m)) m.currentTarget (nonceSlot m))
    (storageAt (readSlot S m.currentTarget (nonceSlot m)) m.currentTarget (nonceSlot m))
    (add (storageAt S m.currentTarget (nonceSlot m)) (1 : U256))

/-- The gas of the code before the call: the fixed part `c`, the read and the write of the
nonce slot. -/
abbrev permitPre (m : Message fork) (S : State.TransactionState) (ss : Substate) (c : Nat) :
    Nat :=
  c + (slotCost (coldIn ss m.currentTarget (nonceSlot m))) +
    (Gas.writeCost fork
      (originalAt (readSlot S m.currentTarget (nonceSlot m)) m.currentTarget (nonceSlot m))
      (storageAt (readSlot S m.currentTarget (nonceSlot m)) m.currentTarget (nonceSlot m))
      (add (storageAt S m.currentTarget (nonceSlot m)) (1 : U256))
      (coldIn (accessSlot ss m.currentTarget (nonceSlot m)) m.currentTarget (nonceSlot m)))

/-- The struct hash of a `permit` message in the state `S`: owner, spender, value, the nonce
of the owner in `S`, and the deadline. -/
abbrev permitStructOf (m : Message fork) (S : State.TransactionState) : U256 :=
  permitStruct
    (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord m.data 4 32))
    (bitwiseAnd (loadWord m.data 36 32) (1461501637330902918203684832716283019655932542975 : U256))
    (loadWord m.data 68 32) (storageAt S m.currentTarget (nonceSlot m)) (loadWord m.data 100 32)

/-- The word that ECRECOVER gives for a `permit` message in the state `S` with the domain
separator `D`: EthLib's `Precompiles.Ecrecover.compute` (through `recoveredWord`) on the digest,
`v` (its low byte; the decoder has checked that `v` is one byte), `r` and `s`. -/
def permitRec (m : Message fork) (S : State.TransactionState) (D : U256) : U256 :=
  recoveredWord (permitInput (permitDigest D (permitStructOf m S))
    (bitwiseAnd (loadWord m.data 132 32) (255 : U256))
    (loadWord m.data 164 32) (loadWord m.data 196 32))

/-- The gas of the call of ECRECOVER from a frame with `gas` at GAS, and what the caller pays:
EthLib's `messageCallGas` for the gas that GAS pushed, no memory growth, and the access of
address 1. -/
abbrev permitCall (fork : Fork) (substate : Substate) (gas : Nat) :=
  messageCallGas fork 0 (BitVec.ofNat 256 (gas - 2)).toNat (gas - 2) 0
    (callBaseCost fork (decide (toAddressMasked 1 ∉ substate.accessedAddresses)) +
      routeCost fork (substate.accessedAddresses.insert (toAddressMasked 1)) none)

/-- From Paris and before Glamsterdam, under the real runner: a run from the frame of `permit`
before `GAS STATICCALL` (pc 6035), in the branch of the cached domain separator (a memory of
512 bytes that holds the digest, `v`, `r` and `s` at 384 and 0 at the output word 352), that
ends with no error.

The call of ECRECOVER got at least 3000 gas, and the run ended as `Paths.permitTailC_ends` says
from the frame after the call: the state with the reads of the call recorded, the substate with
address 1 accessed, the gas left after the call, and the recovered word
`recoveredWord (permitInput digest v r s)`. -/
theorem permit_callC (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    {dg sS sR sV sh deadline value spender owner sel v : U256} {M : ByteArray} {gas : Nat}
    (hsz : M.size = 512) (hfp : loadWord (memoryReadBytes M 64 32) 0 32 = (384 : U256))
    (h352 : loadWord (memoryReadBytes M 352 32) 0 32 = (0 : U256))
    (h384 : loadWord (memoryReadBytes M 384 32) 0 32 = dg)
    (h416 : loadWord (memoryReadBytes M 416 32) 0 32 = v)
    (h448 : loadWord (memoryReadBytes M 448 32) 0 32 = sR)
    (h480 : loadWord (memoryReadBytes M 480 32) 0 32 = sS)
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    {bound : Nat} {z s : Evm fork Nat}
    (start : At CODE message 6035 [(1 : U256), (384 : U256), (128 : U256), (352 : U256),
      (32 : U256), (512 : U256), (1 : U256), (0 : U256), (0 : U256), (0 : U256), sS, sR, sV, dg,
      (5711 : U256), (0 : U256), (0 : U256), (0 : U256), sS, sR, sV, dg, (2433 : U256),
      (0 : U256), dg, sh, sS, sR, sV, deadline, value, spender, owner, (656 : U256), sel]
      M gas state substate z)
    (within : GasMeter.gasHeld z.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) z
      within = .ok s)
    (hok : s.error = none) :
    3000 ≤ (permitCall fork substate gas).subCall ∧
    Paths.permitTailC_ends fork message
      ((state.recordAccountRead (toAddressMasked 1)).recordAccountRead message.currentTarget)
      { substate with
        accessedAddresses := substate.accessedAddresses.insert (toAddressMasked 1) }
      (gas - 2 - ((permitCall fork substate gas).cost + 0) +
        ((permitCall fork substate gas).subCall - 3000))
      s sS sR sV dg sh deadline value spender owner sel
      (recoveredWord (permitInput dg v sR sS)) := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have t384 : (384 : U256).toNat = 384 := by decide
  have t128 : (128 : U256).toNat = 128 := by decide
  have t352 : (352 : U256).toNat = 352 := by decide
  have t32 : (32 : U256).toNat = 32 := by decide
  have hE : extendMemory M.size [((384 : U256), (128 : U256)), ((352 : U256), (32 : U256))] =
      ⟨0, 0⟩ := extendMemory_two (by rw [hsz]; decide) (by rw [hsz]; decide)
  obtain ⟨hg, after, hat, w, hr⟩ := ecrecover_call_ok hparis hglam (q := 6037) rfl
    (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by simp [STACK_LIMIT]) hdel start within hrun hok
  rw [hE] at hg hat
  simp only [memoryExtend_zero, t384, t128, t352, t32] at hat
  have hdata : memoryReadBytes M 384 128 = permitInput dg v sR sS :=
    read4_raw h384 h416 h448 h480 hsz (by decide)
  rw [hdata] at hat
  have hfit : 352 + 32 ≤ M.size := by rw [hsz]; decide
  refine ⟨hg, ?_⟩
  exact Paths.ok_permitTailC_ends hberlin
    ((size_ecrecover_write _ hfit).trans hsz)
    ((congrArg (loadWord · 0 32) (read_ecrecover_other _ hfit (.inl (by decide)))).trans hfp)
    (load_ecrecover _ hfit h352) hat ⟨w, hr⟩ hok

/-- The same in the branches that rebuild the domain separator: a memory of 704 bytes that holds
the digest, `v`, `r` and `s` at 576 and 0 at the output word 544. The end is stated with
`Paths.permitTailC_ends` (the two generated predicates of the tail say the same). -/
theorem permit_callR (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    {dg sS sR sV sh deadline value spender owner sel v : U256} {M : ByteArray} {gas : Nat}
    (hsz : M.size = 704) (hfp : loadWord (memoryReadBytes M 64 32) 0 32 = (576 : U256))
    (h544 : loadWord (memoryReadBytes M 544 32) 0 32 = (0 : U256))
    (h576 : loadWord (memoryReadBytes M 576 32) 0 32 = dg)
    (h608 : loadWord (memoryReadBytes M 608 32) 0 32 = v)
    (h640 : loadWord (memoryReadBytes M 640 32) 0 32 = sR)
    (h672 : loadWord (memoryReadBytes M 672 32) 0 32 = sS)
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    {bound : Nat} {z s : Evm fork Nat}
    (start : At CODE message 6035 [(1 : U256), (576 : U256), (128 : U256), (544 : U256),
      (32 : U256), (704 : U256), (1 : U256), (0 : U256), (0 : U256), (0 : U256), sS, sR, sV, dg,
      (5711 : U256), (0 : U256), (0 : U256), (0 : U256), sS, sR, sV, dg, (2433 : U256),
      (0 : U256), dg, sh, sS, sR, sV, deadline, value, spender, owner, (656 : U256), sel]
      M gas state substate z)
    (within : GasMeter.gasHeld z.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) z
      within = .ok s)
    (hok : s.error = none) :
    3000 ≤ (permitCall fork substate gas).subCall ∧
    Paths.permitTailC_ends fork message
      ((state.recordAccountRead (toAddressMasked 1)).recordAccountRead message.currentTarget)
      { substate with
        accessedAddresses := substate.accessedAddresses.insert (toAddressMasked 1) }
      (gas - 2 - ((permitCall fork substate gas).cost + 0) +
        ((permitCall fork substate gas).subCall - 3000))
      s sS sR sV dg sh deadline value spender owner sel
      (recoveredWord (permitInput dg v sR sS)) := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have t576 : (576 : U256).toNat = 576 := by decide
  have t128 : (128 : U256).toNat = 128 := by decide
  have t544 : (544 : U256).toNat = 544 := by decide
  have t32 : (32 : U256).toNat = 32 := by decide
  have hE : extendMemory M.size [((576 : U256), (128 : U256)), ((544 : U256), (32 : U256))] =
      ⟨0, 0⟩ := extendMemory_two (by rw [hsz]; decide) (by rw [hsz]; decide)
  obtain ⟨hg, after, hat, w, hr⟩ := ecrecover_call_ok hparis hglam (q := 6037) rfl
    (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by simp [STACK_LIMIT]) hdel start within hrun hok
  rw [hE] at hg hat
  simp only [memoryExtend_zero, t576, t128, t544, t32] at hat
  have hdata : memoryReadBytes M 576 128 = permitInput dg v sR sS :=
    read4_raw h576 h608 h640 h672 hsz (by decide)
  rw [hdata] at hat
  have hfit : 544 + 32 ≤ M.size := by rw [hsz]; decide
  refine ⟨hg, ?_⟩
  have htail := Paths.ok_permitTailR_ends hberlin
    ((size_ecrecover_write _ hfit).trans hsz)
    ((congrArg (loadWord · 0 32) (read_ecrecover_other _ hfit (.inl (by decide)))).trans hfp)
    (load_ecrecover _ hfit h544) hat ⟨w, hr⟩ hok
  exact htail

/-- What a run of `permit` that ends with no error did from the call of ECRECOVER on, for the
domain separator `D` and the fixed gas `c` of the code before the call: the gas covered the
code before the call and 3000 for ECRECOVER, and the run ended as `Paths.permitTailC_ends`
says (generated, `Gen/PPermitTailC.lean`) from the state `permitS1` (nonce incremented) with the
reads of the call recorded. That predicate has the checks after the call (the recovered word
`permitRec` is not 0 as an address and equals the owner, the owner and the spender are not 0),
the exact write of the allowance, the Approval log and the exact gas. -/
def PermitDone (fork : Fork) (message : Message fork) (state : State.TransactionState)
    (substate : Substate) (gas : Nat) (s : Evm fork Nat) (D : U256) (c : Nat) : Prop :=
  permitPre message state substate c ≤ gas ∧
  3000 ≤ (permitCall fork (permitSS1 message state substate)
    (gas - permitPre message state substate c)).subCall ∧
  Paths.permitTailC_ends fork message
    (((permitS1 message state).recordAccountRead (toAddressMasked 1)).recordAccountRead
      message.currentTarget)
    { permitSS1 message state substate with
      accessedAddresses :=
        (permitSS1 message state substate).accessedAddresses.insert (toAddressMasked 1) }
    (gas - permitPre message state substate c - 2 -
      ((permitCall fork (permitSS1 message state substate)
        (gas - permitPre message state substate c)).cost + 0) +
      ((permitCall fork (permitSS1 message state substate)
        (gas - permitPre message state substate c)).subCall - 3000))
    s
    (loadWord message.data 196 32) (loadWord message.data 164 32) (loadWord message.data 132 32)
    (permitDigest D (permitStructOf message state)) (permitStructOf message state)
    (loadWord message.data 100 32) (loadWord message.data 68 32) (loadWord message.data 36 32)
    (loadWord message.data 4 32) (BitVec.ofNat 256 (selector message.data))
    (permitRec message state D)

/-- Completeness for `permit`, under EthLib's real runner, from Paris and before Glamsterdam.

A run of a fresh frame of `CODE` on a message with the selector of `permit` that ends with no
error: the message carries no value, its call data holds the seven arguments, `owner` and
`spender` are clean address words and `v` is one byte, the time stamp of the block is not after
the deadline, `s` is at most half the order of secp256k1, the frame may write, the contract has
its account, and `PermitDone` holds for the domain separator `domainSep message` (cached or
rebuilt) and the gas `permitBase message` of that branch.

The recovered word is `permitRec`: `recoveredWord` of the 128 bytes `permitInput digest v r s`,
where the digest is `permitDigest` of the domain separator and of `permitStruct` of the
arguments and of the nonce in storage. `recoveredWord` is EthLib's
`Precompiles.Ecrecover.compute` read as a word: nothing is assumed about it. -/
theorem ok_permit_real (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xd505accf)
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    isZero message.value ≠ 0 ∧
    isZero (signedLessThan (sub (BitVec.ofNat 256 message.data.size) (4 : U256)) (224 : U256))
      ≠ 0 ∧
    equal (loadWord message.data 4 32) (bitwiseAnd (loadWord message.data 4 32)
      (1461501637330902918203684832716283019655932542975 : U256)) ≠ 0 ∧
    equal (loadWord message.data 36 32) (bitwiseAnd (loadWord message.data 36 32)
      (1461501637330902918203684832716283019655932542975 : U256)) ≠ 0 ∧
    equal (loadWord message.data 132 32) (bitwiseAnd (loadWord message.data 132 32) (255 : U256))
      ≠ 0 ∧
    isZero (greaterThan message.blockEnv.timestamp (loadWord message.data 100 32)) ≠ 0 ∧
    isZero (greaterThan (loadWord message.data 196 32)
      (57896044618658097711785492504343953926418782139537452191302581570759080747168 : U256))
      ≠ 0 ∧
    message.isStatic = false ∧
    hasAccount state message.currentTarget ∧
    PermitDone fork message state substate gas s (domainSep message) (permitBase message) := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hdel' : ∀ c, (permitS1 message state).getCode
      ((permitS1 message state).getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none := by
    intro c h
    rw [getCode_writeSlot, getAccount_writeSlot] at h
    exact hdel c h
  unfold PermitDone
  rcases Paths.ok_permit hberlin hsize' hsel start ⟨within, hrun⟩ hok with
    ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hstat, hacc, hcg, z, hz, w, hzr⟩ |
    ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hstat, hacc, hcg, z, hz, w, hzr⟩ |
    ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hstat, hacc, hcg, z, hz, w, hzr⟩
  · have e7 : USDE_ADDRESS = message.currentTarget.toU256 := Readable.eq_of_isZero_equal hc7
    have e8 := Readable.eq_of_isZero_equal hc8
    have hD : domainSep message = CACHED_DOMAIN := by
      unfold domainSep
      exact if_pos ⟨e7, e8⟩
    have hB : permitBase message = 1592 := by
      unfold permitBase
      rw [if_pos e7, if_pos e8]
    obtain ⟨msz, m64, -, -, -, -, -, -, -, -, -, -, m352, m384, m416, m448, m480⟩ :=
      Paths.permit_p8_mem (message := message) (state := state)
    have core := permit_callC hparis hglam msz m64 m352 m384 m416 m448 m480 hdel' hz w hzr hok
    rw [digest_bytes_352 (ws := _) (by rfl) (memW_load 11 (by rfl) (by rfl) (by rfl))] at core
    rw [hD, hB]
    exact ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc9, hstat, hacc, hcg, core.1, core.2⟩
  · have e7 : USDE_ADDRESS = message.currentTarget.toU256 := Readable.eq_of_isZero_equal hc7
    have n8 := Readable.ne_of_isZero_equal hc8
    have hD : domainSep message = domainRebuilt message := by
      unfold domainSep
      exact if_neg (fun h => n8 h.2)
    have hB : permitBase message = 1845 := by
      unfold permitBase
      rw [if_pos e7, if_neg n8]
    obtain ⟨msz, m64, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, m544, m576, m608, m640,
      m672⟩ := Paths.permit_p10_mem (message := message) (state := state)
    have core := permit_callR hparis hglam msz m64 m544 m576 m608 m640 m672 hdel' hz w hzr hok
    rw [digest_bytes_544 (ws := _) (by rfl) (memW_load 17 (by rfl) (by rfl) (by rfl))] at core
    rw [hD, hB]
    exact ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc9, hstat, hacc, hcg, core.1, core.2⟩
  · have n7 : USDE_ADDRESS ≠ message.currentTarget.toU256 := Readable.ne_of_isZero_equal hc7
    have hD : domainSep message = domainRebuilt message := by
      unfold domainSep
      exact if_neg (fun h => n7 h.1)
    have hB : permitBase message = 1835 := by
      unfold permitBase
      rw [if_neg n7]
    obtain ⟨msz, m64, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, m544, m576, m608, m640,
      m672⟩ := Paths.permit_p12_mem (message := message) (state := state)
    have core := permit_callR hparis hglam msz m64 m544 m576 m608 m640 m672 hdel' hz w hzr hok
    rw [digest_bytes_544 (ws := _) (by rfl) (memW_load 17 (by rfl) (by rfl) (by rfl))] at core
    rw [hD, hB]
    exact ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc8, hstat, hacc, hcg, core.1, core.2⟩

end UsdeVerify
