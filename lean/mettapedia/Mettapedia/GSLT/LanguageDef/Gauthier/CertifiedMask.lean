/-
# Certified pruning for the Gauthier postfix root

The completed-program certificates in `GauthierOEISCertifiedMask` are lifted
through actual postfix-search completions.  The lift is the only new semantic
step: sign/parity and mod-k soundness remain delegated to the sealed theorems.
-/

import Mathlib.Tactic
import Mettapedia.GSLT.LanguageDef.CertifiedMask
import Mettapedia.GSLT.LanguageDef.Gauthier.AtomicRefinement
import Mettapedia.OSLF.Framework.GauthierOEISCertifiedMask

namespace Mettapedia.GSLT.LanguageDef.GauthierCertifiedMask

open Mettapedia.GSLT.LanguageDef.CertifiedMask
open Mettapedia.GSLT.LanguageDef.RefinementInterface
open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierRefinement
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton
open Mettapedia.GSLT.LanguageDef.GauthierSkeletonMask
open Mettapedia.OSLF.Framework.GauthierOEISPruningSoundness
open Mettapedia.OSLF.Framework.GauthierOEISModKPruning
open Mettapedia.OSLF.Framework.GauthierOEISCertifiedMask

/-! ## Sealed program certificates, lifted without reproving them -/

/-- The sealed sign/parity incompatibility theorem as a program rejector. -/
def signParityRejector (target : List ObservedTerm) :
    CertifiedProgramRejector (fun program : Prog => Reproduces program target) where
  rejects := fun program => AnalysisIncompatible program target
  sound := fun _ hbad => certified_property_pruning_via_mask hbad

/-- The sealed mod-k incompatibility theorem as a program rejector. -/
def modKRejector (k : Nat) (target : List ObservedTerm) :
    CertifiedProgramRejector (fun program : Prog => Reproduces program target) where
  rejects := fun program => ModKIncompatible k program target
  sound := fun _ hbad => certified_modk_pruning_via_mask hbad

/-- State predicate obtained by quantifying the sealed sign/parity test over completions. -/
def signParityStatePrune (target : List ObservedTerm)
    (node : SearchNode orgMemoRoot) : Prop :=
  liftProgramRejector (signParityRejector target) node

/-- State predicate obtained by quantifying the sealed mod-k test over completions. -/
def modKStatePrune (k : Nat) (target : List ObservedTerm)
    (node : SearchNode orgMemoRoot) : Prop :=
  liftProgramRejector (modKRejector k target) node

/-- On-the-nose recovery: the lifted sign/parity predicate mentions exactly the sealed test. -/
theorem signParityStatePrune_iff {target : List ObservedTerm}
    {node : SearchNode orgMemoRoot} :
    signParityStatePrune target node ↔
      ∀ program, node.Completes program → AnalysisIncompatible program target :=
  Iff.rfl

/-- On-the-nose recovery: the lifted residue predicate mentions exactly the sealed test. -/
theorem modKStatePrune_iff {k : Nat} {target : List ObservedTerm}
    {node : SearchNode orgMemoRoot} :
    modKStatePrune k target node ↔
      ∀ program, node.Completes program → ModKIncompatible k program target :=
  Iff.rfl

/-- T2 sign/parity instance of the root-parametric program-to-state lift. -/
theorem signParityStatePrune_certified {target : List ObservedTerm} :
    CertifiedHardMask (fun program : Prog => Reproduces program target)
      (signParityStatePrune target) := by
  intro node hlifted
  change liftProgramRejector (signParityRejector target) node at hlifted
  exact liftProgramRejector_semanticallyPrunable
    (signParityRejector target) hlifted

/-- T2 mod-k instance of the root-parametric program-to-state lift. -/
theorem modKStatePrune_certified (k : Nat) (target : List ObservedTerm) :
    CertifiedHardMask (fun program : Prog => Reproduces program target)
      (modKStatePrune k target) := by
  intro node hlifted
  change liftProgramRejector (modKRejector k target) node at hlifted
  exact liftProgramRejector_semanticallyPrunable
    (modKRejector k target) hlifted

/-! ## An honest executable sufficient test for postfix states -/

/-- Executable evidence for a program rejector; reflection is one-way on purpose. -/
structure DecidableProgramRejector {property : Prog → Prop}
    (certificate : CertifiedProgramRejector property) where
  rejects? : Prog → Bool
  reflects : ∀ program, rejects? program = true → certificate.rejects program

/-- At an exhausted operator budget, any successful next token must be EOS. -/
theorem exhausted_step_implies_eos {state next : MaskState} {token : PyToken}
    (hexhausted : state.tokensEmitted = state.maxLen)
    (hstep : orgMemoRoot.apply? state token = some next) :
    token = eos := by
  have hmem : token ∈ legalTokens orgMemoSignature state :=
    mem_legalTokens_of_step?_some hstep
  unfold legalTokens at hmem
  simp [opLegal, hexhausted] at hmem
  exact hmem.2

/-- EOS in a trace is rejected by the sealed nonnegative operator decoder. -/
theorem decode_append_eos_cons_none (before after : List PyToken) :
    orgMemoRoot.decode (before ++ eos :: after) = none := by
  simp [orgMemoRoot, decodeOperatorTrace, nonnegativeTokens, eos]

/-- Reaching an exhausted state forces every accepted completion suffix to be empty. -/
theorem exhausted_accepted_suffix_nil {node : SearchNode orgMemoRoot}
    {suffix : List PyToken} {program : Prog}
    (hreached : node.Reached)
    (hexhausted : node.state.tokensEmitted = node.state.maxLen)
    (haccepts : orgMemoRoot.Accepts node.budget
      (node.actions ++ suffix) program) :
    suffix = [] := by
  rcases haccepts with ⟨finalState, hrun, _hterminal, hdecode⟩
  rw [orgMemoRoot.run_append, hreached] at hrun
  cases suffix with
  | nil => rfl
  | cons token rest =>
      simp only [RefinementInterface.run] at hrun
      cases hstep : orgMemoRoot.apply? node.state token with
      | none =>
          change step? orgMemoSignature node.state token = none at hstep
          rw [hstep] at hrun
          contradiction
      | some next =>
          have heos := exhausted_step_implies_eos hexhausted hstep
          subst token
          rw [decode_append_eos_cons_none] at hdecode
          contradiction

/--
Executable sufficient test used by the ranking harness: it fires only when the
operator budget is exhausted and the already decoded program has a reflected
certificate.  Earlier partial stacks remain `false` (unknown), so this test is
sound but intentionally not claimed complete.
-/
def exhaustedStateTest {property : Prog → Prop}
    (certificate : CertifiedProgramRejector property)
    (decision : DecidableProgramRejector certificate) :
    CertifiedStateTest (root := orgMemoRoot) property where
  test := fun node =>
    (node.state.tokensEmitted == node.state.maxLen) &&
      match orgMemoRoot.decode node.actions with
      | none => false
      | some program => decision.rejects? program
  sound := by
    intro node htest program hcompletes hproperty
    simp only [Bool.and_eq_true, beq_iff_eq] at htest
    rcases htest with ⟨hexhausted, hrejects⟩
    cases hdecode : decodeOperatorTrace node.actions with
    | none => simp [hdecode] at hrejects
    | some decoded =>
        have hcertified : certificate.rejects decoded :=
          decision.reflects decoded (by simpa [hdecode] using hrejects)
        rcases hcompletes with ⟨hreached, suffix, haccepts⟩
        have hsuffix := exhausted_accepted_suffix_nil hreached hexhausted haccepts
        subst suffix
        rcases haccepts with ⟨finalState, _hrun, _hterminal, hprogram⟩
        simp only [List.append_nil] at hprogram
        change decodeOperatorTrace node.actions = some program at hprogram
        rw [hdecode] at hprogram
        have heq : decoded = program := Option.some.inj hprogram
        subst program
        exact certificate.sound decoded hcertified hproperty

/-- A tiny executable classifier whose only positive answer is the sealed zero canary. -/
def zeroForOneTargetDecision : DecidableProgramRejector
    (signParityRejector oneTarget) where
  rejects? := fun program =>
    match program with
    | .node 0 [] => true
    | _ => false
  reflects := by
    intro program hzero
    cases program with
    | node id children =>
        cases id with
        | zero =>
            cases children with
            | nil =>
                refine ⟨observedOneAt0, by simp [oneTarget], ?_⟩
                exact Or.inr zero_incompatible_with_one_observation
            | cons child rest => simp at hzero
        | succ id => simp at hzero

/-- Concrete executable sign/parity state test used by the postfix fixtures. -/
def zeroForOneTargetStateTest :
    CertifiedStateTest (root := orgMemoRoot)
      (fun program : Prog => Reproduces program oneTarget) :=
  exhaustedStateTest (signParityRejector oneTarget) zeroForOneTargetDecision

/-- Exhausted, decoded constant-zero is positively pruned by the executable test. -/
def zeroSolutionNode : SearchNode orgMemoRoot where
  budget := 1
  actions := orgMemoRoot.encode zeroProg
  state := { depth := 1, tokensEmitted := 1, maxLen := 1 }

theorem zeroProg_wellFormed : WellFormed orgMemoSignature zeroProg := by
  apply WellFormed.node (sig := orgMemoSignature)
  · rfl
  · rfl
  · simp

theorem zeroForOneTargetStateTest_positive :
    zeroForOneTargetStateTest.test zeroSolutionNode = true := by
  change
    (true &&
      match decodeOperatorTrace ((rpnTokens zeroProg).map Int.ofNat) with
      | none => false
      | some program => zeroForOneTargetDecision.rejects? program) = true
  rw [decodeOperatorTrace_encode zeroProg_wellFormed]
  rfl

/-! ## Trust-boundary negative: an attractive but false hard rule -/

/-- A plausible heuristic: retain only programs whose root operator id is even. -/
def EvenRoot : Prog → Prop
  | .node id _ => id % 2 = 0

/-- Hard-prune a completed prefix when its decoded root violates `EvenRoot`. -/
def oddRootHardMask (node : SearchNode orgMemoRoot) : Prop :=
  ∃ program, orgMemoRoot.decode node.actions = some program ∧ ¬ EvenRoot program

/-- Concrete terminal node reached by the genuine constant-one solution. -/
def oneSolutionNode : SearchNode orgMemoRoot where
  budget := 1
  actions := orgMemoRoot.encode oneProg
  state := { depth := 1, tokensEmitted := 1, maxLen := 1 }

theorem oneProg_reproduces_oneTarget : Reproduces oneProg oneTarget := by
  intro obs hmem
  simp [oneTarget] at hmem
  subst obs
  refine ⟨1, Store.zero, ?_⟩
  simp [oneProg, observedOneAt0, ObservedTerm.seedValue, eval, orgE1Signature,
    entryAt, listGet?, entry, seed]

theorem oneProg_wellFormed : WellFormed orgMemoSignature oneProg := by
  apply WellFormed.node (sig := orgMemoSignature)
  · rfl
  · rfl
  · simp

theorem oneProg_cost : orgMemoRoot.programCost oneProg ≤ 1 := by
  simp [oneProg, rpnTokens]

theorem oneSolutionNode_reached : oneSolutionNode.Reached := by
  change
    orgMemoRoot.run (orgMemoRoot.encode oneProg) (orgMemoRoot.initial 1) =
      some { depth := 1, tokensEmitted := 1, maxLen := 1 }
  simp [orgMemoRoot, oneProg, rpnTokens, RefinementInterface.run,
    GauthierSkeletonMask.step?, legalTokens, opLegal, initial, operatorIds,
    nextDepth?, canComplete, orgMemoSignature,
    Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature,
    Mettapedia.GSLT.LanguageDef.GauthierE2.orgSignature,
    Mettapedia.GSLT.LanguageDef.GauthierE2.listOps, maskStep?, entryAt,
    listGet?, entry, eos, popN]

/-- The genuine constant-one path is retained, exhibiting the negative test fixture. -/
theorem zeroForOneTargetStateTest_negative :
    zeroForOneTargetStateTest.test oneSolutionNode = false := by
  change
    (true &&
      match decodeOperatorTrace ((rpnTokens oneProg).map Int.ofNat) with
      | none => false
      | some program => zeroForOneTargetDecision.rejects? program) = false
  rw [decodeOperatorTrace_encode oneProg_wellFormed]
  rfl

theorem oneSolutionNode_completes : oneSolutionNode.Completes oneProg := by
  refine ⟨oneSolutionNode_reached, [], ?_⟩
  change orgMemoRoot.Accepts 1 (orgMemoRoot.encode oneProg ++ []) oneProg
  simpa using orgMemoLaws.complete (budget := 1) (program := oneProg)
    (by simp) oneProg_wellFormed oneProg_cost

theorem oddRootHardMask_prunes_oneSolution : oddRootHardMask oneSolutionNode := by
  refine ⟨oneProg, ?_, ?_⟩
  · change orgMemoRoot.decode (orgMemoRoot.encode oneProg) = some oneProg
    exact decodeOperatorTrace_encode oneProg_wellFormed
  · simp [EvenRoot, oneProg]

/-- Mandatory T3 counterexample: the plausible parity-of-root rule loses a real solve. -/
theorem oddRootHardMask_not_recallSafe :
    ¬ RecallSafe (fun program : Prog => Reproduces program oneTarget)
      oddRootHardMask := by
  intro hsafe
  exact hsafe oneSolutionNode oneProg oneSolutionNode_completes
    oneProg_reproduces_oneTarget oddRootHardMask_prunes_oneSolution

/-- Therefore the bad rule cannot inhabit the hard-mask certification boundary. -/
theorem oddRootHardMask_not_certified :
    ¬ CertifiedHardMask (fun program : Prog => Reproduces program oneTarget)
      oddRootHardMask := by
  rw [← hardMask_recallSafe_iff_certified]
  exact oddRootHardMask_not_recallSafe

/-! ## Soft ranking remains safe on the same concrete root -/

/-- Concrete Gauthier restatement of the generic soft-ranking boundary. -/
theorem gauthierSoftRanking_always_safe
    (ranking : orgMemoRoot.State → List orgMemoRoot.Action)
    (hcoverage : orgMemoRoot.ListsAllLegalActions ranking)
    {budget : Nat} {trace : List orgMemoRoot.Action} {program : Prog} :
    orgMemoRoot.RankedAccepts ranking budget trace program ↔
      orgMemoRoot.Accepts budget trace program :=
  softRanking_always_safe orgMemoLaws ranking hcoverage

#print axioms signParityStatePrune_certified
#print axioms modKStatePrune_certified
#print axioms oddRootHardMask_not_recallSafe
#print axioms oddRootHardMask_not_certified
#print axioms gauthierSoftRanking_always_safe

end Mettapedia.GSLT.LanguageDef.GauthierCertifiedMask
