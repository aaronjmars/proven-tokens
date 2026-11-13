import UsdeVerify.Usde.Gen
import TokenKit.Evm.Witness
import TokenKit.Evm.WitnessOpt

/-!
# Sanity: the three success paths of `DOMAIN_SEPARATOR()` have a concrete run

Written by hand (the generator of `Sanity/Zero.lean` has one contract address and one block for
all its witnesses, and these paths need their own): the path of the cached separator needs the
deployed address and chain id 1, the second one the deployed address and another chain id, the
third one another address.

- `domainSeparator_cached_runs`: the contract at the deployed address `USDE`, chain id 1.
- `domainSeparator_chain_runs`: the contract at `USDE`, chain id 5.
- `domainSeparator_address_runs`: the contract at `Witness.CALLER1` (not the deployed address),
  any block.

Each: the call meets every hypothesis of its success path theorem, so the loop of the
interpreter runs it from pc 0 to the end with no error, for every message runner and every gas
bound that holds its gas, with the stated output and an unchanged state.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 4096

namespace UsdeVerify.Sanity

open UsdtVerify
open TokenKit
open UsdeVerify UsdeVerify.Paths UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork}

/-- The four bytes of the selector of `DOMAIN_SEPARATOR()`. -/
def SEL_domainSeparator : ByteArray := ⟨#[0x36, 0x44, 0xe5, 0x15]⟩

theorem size_SEL_domainSeparator : SEL_domainSeparator.size = 4 := by decide

/-- The deployed address of USDe: `0x4c9edd5852cd905f086c759e8383e09bff1e68b3`. -/
def USDE : Address := toAddressMasked (437426098194082895061803372304124391670360729779 : U256)

/-- The word of the deployed address. -/
theorem usde_toU256 : USDE.toU256 = (437426098194082895061803372304124391670360729779 : U256) := by decide +kernel

/-- The block `b` with the chain id `c`. -/
abbrev onChain (b : BlockEnvironment fork) (c : UInt64) : BlockEnvironment fork :=
  { b with chainId := c }

/-- The call `DOMAIN_SEPARATOR()` from `Witness.CALLER1` to `C`. -/
abbrev m_domainSeparator (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C : Address) : Message fork :=
  sMsg b t C Witness.CALLER1 CODE SEL_domainSeparator

set_option maxHeartbeats 1000000 in
/-- The success path `domainSeparator_p1` (the cached separator) is not empty: at the deployed address with chain id 1, this call runs to the end with no error and returns the cached constant. -/
theorem domainSeparator_cached_runs (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (ss : Substate) :
    ∃ (gas : Nat) (evm s : Evm fork Nat),
      At CODE (m_domainSeparator (onChain b 1) t USDE) 0 [] .empty gas (sState USDE []) ss evm ∧
      (∀ {bound : Nat} (runChild : MessageRunner fork Nat bound),
        GasMeter.gasHeld evm.gas ≤ bound → EndsL runChild evm s) ∧ s.error = none ∧
      s.output = (wordBytes (52913264502934295635151425816809534945870579946550263777912616301551047572659 : U256)) ∧
      s.state = sState USDE [] := by
  have hsz : (m_domainSeparator (onChain b 1) t USDE).data.size = 4 := size_SEL_domainSeparator
  have hsl : selector (m_domainSeparator (onChain b 1) t USDE).data = selector SEL_domainSeparator := rfl
  have hval : (m_domainSeparator (onChain b 1) t USDE).value = 0 := rfl
  have hct : (m_domainSeparator (onChain b 1) t USDE).currentTarget.toU256 = (437426098194082895061803372304124391670360729779 : U256) := usde_toU256
  have hcw : (m_domainSeparator (onChain b 1) t USDE).caller.toU256 = Witness.CALLER1W := Witness.caller1_toU256
  have hch : (m_domainSeparator (onChain b 1) t USDE).blockEnv.chainId.toNat = 1 := rfl
  have hspec := domainSeparator_p1 (fork := fork) (message := (m_domainSeparator (onChain b 1) t USDE))
    (state := sState USDE []) (substate := ss)
    hfork
    (by rw [hsz]; decide)
    (by rw [hsz]; decide)
    (by rw [hsl]; decide)
    (by
      simp only [hval, hct, hcw, hch]
      decide +kernel)
    (by
      simp only [hval, hct, hcw, hch]
      decide +kernel)
    (by
      simp only [hval, hct, hcw, hch]
      decide +kernel)
    (Nat.le_refl _)
  obtain ⟨s, hr, hrun, hH⟩ := hspec (sFrame (m_domainSeparator (onChain b 1) t USDE) (sState USDE []) ss _)
    (at_sFrame _ rfl _ _ _)
  refine ⟨_, _, s, at_sFrame _ rfl _ _ _, fun rc within => Witness.endsL_of_reaches hr hrun rc within, ?_,
    hH.2.2.1, hH.2.2.2.2.1⟩
  obtain ⟨-, he, -⟩ := hH
  simpa using he

set_option maxHeartbeats 1000000 in
/-- The success path `domainSeparator_p2` (the deployed address, another chain) is not empty: at the deployed address with chain id 5, this call runs to the end with no error and returns the rebuilt hash. -/
theorem domainSeparator_chain_runs (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (ss : Substate) :
    ∃ (gas : Nat) (evm s : Evm fork Nat),
      At CODE (m_domainSeparator (onChain b 5) t USDE) 0 [] .empty gas (sState USDE []) ss evm ∧
      (∀ {bound : Nat} (runChild : MessageRunner fork Nat bound),
        GasMeter.gasHeld evm.gas ≤ bound → EndsL runChild evm s) ∧ s.error = none ∧
      s.output = (wordBytes (keccak (memW [(63076024560530113402979550242307453568063438748328787417531900361828837441551 : U256), (800430381884319963266448255313171563733839282559604318839735355180845479980 : U256), (90743482286830539503240959006302832933333810038750515972785732718729991261126 : U256), (BitVec.ofNat 256 (m_domainSeparator (onChain b 5) t USDE).blockEnv.chainId.toNat), (m_domainSeparator (onChain b 5) t USDE).currentTarget.toU256]))) ∧
      s.state = sState USDE [] := by
  have hsz : (m_domainSeparator (onChain b 5) t USDE).data.size = 4 := size_SEL_domainSeparator
  have hsl : selector (m_domainSeparator (onChain b 5) t USDE).data = selector SEL_domainSeparator := rfl
  have hval : (m_domainSeparator (onChain b 5) t USDE).value = 0 := rfl
  have hct : (m_domainSeparator (onChain b 5) t USDE).currentTarget.toU256 = (437426098194082895061803372304124391670360729779 : U256) := usde_toU256
  have hcw : (m_domainSeparator (onChain b 5) t USDE).caller.toU256 = Witness.CALLER1W := Witness.caller1_toU256
  have hch : (m_domainSeparator (onChain b 5) t USDE).blockEnv.chainId.toNat = 5 := rfl
  have hspec := domainSeparator_p2 (fork := fork) (message := (m_domainSeparator (onChain b 5) t USDE))
    (state := sState USDE []) (substate := ss)
    hfork
    (by rw [hsz]; decide)
    (by rw [hsz]; decide)
    (by rw [hsl]; decide)
    (by
      simp only [hval, hct, hcw, hch]
      decide +kernel)
    (by
      simp only [hval, hct, hcw, hch]
      decide +kernel)
    (by
      simp only [hval, hct, hcw, hch]
      decide +kernel)
    (Nat.le_refl _)
  obtain ⟨s, hr, hrun, hH⟩ := hspec (sFrame (m_domainSeparator (onChain b 5) t USDE) (sState USDE []) ss _)
    (at_sFrame _ rfl _ _ _)
  refine ⟨_, _, s, at_sFrame _ rfl _ _ _, fun rc within => Witness.endsL_of_reaches hr hrun rc within, ?_,
    hH.2.2.1, hH.2.2.2.2.1⟩
  obtain ⟨-, he, -⟩ := hH
  simpa using he

set_option maxHeartbeats 1000000 in
/-- The success path `domainSeparator_p3` (another address) is not empty: at the address `Witness.CALLER1`, in any block, this call runs to the end with no error and returns the rebuilt hash. -/
theorem domainSeparator_address_runs (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (ss : Substate) :
    ∃ (gas : Nat) (evm s : Evm fork Nat),
      At CODE (m_domainSeparator b t Witness.CALLER1) 0 [] .empty gas (sState Witness.CALLER1 []) ss evm ∧
      (∀ {bound : Nat} (runChild : MessageRunner fork Nat bound),
        GasMeter.gasHeld evm.gas ≤ bound → EndsL runChild evm s) ∧ s.error = none ∧
      s.output = (wordBytes (keccak (memW [(63076024560530113402979550242307453568063438748328787417531900361828837441551 : U256), (800430381884319963266448255313171563733839282559604318839735355180845479980 : U256), (90743482286830539503240959006302832933333810038750515972785732718729991261126 : U256), (BitVec.ofNat 256 (m_domainSeparator b t Witness.CALLER1).blockEnv.chainId.toNat), (m_domainSeparator b t Witness.CALLER1).currentTarget.toU256]))) ∧
      s.state = sState Witness.CALLER1 [] := by
  have hsz : (m_domainSeparator b t Witness.CALLER1).data.size = 4 := size_SEL_domainSeparator
  have hsl : selector (m_domainSeparator b t Witness.CALLER1).data = selector SEL_domainSeparator := rfl
  have hval : (m_domainSeparator b t Witness.CALLER1).value = 0 := rfl
  have hct : (m_domainSeparator b t Witness.CALLER1).currentTarget.toU256 = Witness.CALLER1W := Witness.caller1_toU256
  have hcw : (m_domainSeparator b t Witness.CALLER1).caller.toU256 = Witness.CALLER1W := Witness.caller1_toU256
  have hch : (m_domainSeparator b t Witness.CALLER1).value = 0 := rfl
  have hspec := domainSeparator_p3 (fork := fork) (message := (m_domainSeparator b t Witness.CALLER1))
    (state := sState Witness.CALLER1 []) (substate := ss)
    hfork
    (by rw [hsz]; decide)
    (by rw [hsz]; decide)
    (by rw [hsl]; decide)
    (by
      simp only [hval, hct, hcw, hch]
      decide +kernel)
    (by
      simp only [hval, hct, hcw, hch]
      decide +kernel)
    (Nat.le_refl _)
  obtain ⟨s, hr, hrun, hH⟩ := hspec (sFrame (m_domainSeparator b t Witness.CALLER1) (sState Witness.CALLER1 []) ss _)
    (at_sFrame _ rfl _ _ _)
  refine ⟨_, _, s, at_sFrame _ rfl _ _ _, fun rc within => Witness.endsL_of_reaches hr hrun rc within, ?_,
    hH.2.2.1, hH.2.2.2.2.1⟩
  obtain ⟨-, he, -⟩ := hH
  simpa using he

end UsdeVerify.Sanity
