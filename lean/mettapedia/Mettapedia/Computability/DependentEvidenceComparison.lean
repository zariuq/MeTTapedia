import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Types.Basic
import Mettapedia.Computability.ComputationalTrinity
import Mettapedia.GSLT.Core.NonFactorization
import Mettapedia.GSLT.Dynamics.EvidenceIndexedBranchingRealization

/-!
# Dependent evidence as a computational-trinity comparison

Every dependent evidence family has a canonical three-face comparison:

```
total evidence  Sigma E  -->  state  -->  observed view.
```

The first interpretation forgets evidence and the second applies the selected
observer.  The direct interpretation does both, so the triangle commutes.
The direct map is injective exactly when the observer is injective and every
evidence fibre is subsingleton, provided every state has evidence.  Without
those conditions, proof relevance or observational collapse is necessarily
lost on the spatial face.

This theorem does not prescribe which face is a language, proof calculus, or
space semantics.  It identifies the exact information boundary for any such
interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.DependentEvidenceComparison

open _root_.CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.GSLT.Core.NonFactorization

universe u

abbrev Context := _root_.CategoryTheory.Discrete PUnit

variable {State View : Type u}

/-- The total space of a dependent evidence family. -/
abbrev TotalEvidence (evidence : State → Type u) := Sigma evidence

/-- Proof-relevant total evidence as the operational face. -/
def evidenceFace (evidence : State → Type u) : Face.{0, 0, u} Context :=
  (_root_.CategoryTheory.Functor.const Contextᵒᵖ).obj
    (TotalEvidence evidence)

/-- The underlying state carrier as the logical/intermediate face. -/
def stateFace : Face.{0, 0, u} Context :=
  (_root_.CategoryTheory.Functor.const Contextᵒᵖ).obj State

/-- A selected extensional observation carrier. -/
def viewFace : Face.{0, 0, u} Context :=
  (_root_.CategoryTheory.Functor.const Contextᵒᵖ).obj View

/-- Forget dependent evidence while retaining its state index. -/
def evidenceToState (evidence : State → Type u) :
    evidenceFace evidence ⟶ stateFace (State := State) :=
  (_root_.CategoryTheory.Functor.const Contextᵒᵖ).map
    (↾(Sigma.fst : TotalEvidence evidence → State))

/-- Apply the selected observer to a state. -/
def stateToView (observe : State → View) :
    stateFace (State := State) ⟶ viewFace (View := View) :=
  (_root_.CategoryTheory.Functor.const Contextᵒᵖ).map (↾observe)

/-- Forget evidence and observe the retained state. -/
def evidenceToView (evidence : State → Type u) (observe : State → View) :
    evidenceFace evidence ⟶ viewFace (View := View) :=
  (_root_.CategoryTheory.Functor.const Contextᵒᵖ).map
    (↾(fun total : TotalEvidence evidence => observe total.1))

/-- The canonical dependent-evidence comparison triangle. -/
def comparison (evidence : State → Type u) (observe : State → View) :
    Comparison.{0, 0, u} Context where
  program := evidenceFace evidence
  logic := stateFace
  space := viewFace
  programToLogic := evidenceToState evidence
  logicToSpace := stateToView observe
  programToSpace := evidenceToView evidence observe
  coherence := by
    ext context total
    rfl

/-! ## Exact information criteria -/

/-- Forgetting evidence is injective exactly when every evidence fibre is a
subsingleton. -/
theorem sigmaFst_injective_iff_subsingleton
    (evidence : State → Type u) :
    Function.Injective (Sigma.fst : TotalEvidence evidence → State) ↔
      ∀ state, Subsingleton (evidence state) := by
  constructor
  · intro injective state
    refine ⟨fun left right => ?_⟩
    have equalTotals :
        (⟨state, left⟩ : TotalEvidence evidence) = ⟨state, right⟩ :=
      injective rfl
    exact eq_of_heq (Sigma.mk.inj_iff.mp equalTotals).2
  · intro subsingleton left right equalStates
    rcases left with ⟨leftState, leftEvidence⟩
    rcases right with ⟨rightState, rightEvidence⟩
    change leftState = rightState at equalStates
    subst rightState
    exact Sigma.ext rfl
      (heq_of_eq (Subsingleton.elim leftEvidence rightEvidence))

/-- Faithful state observation plus proof-irrelevant evidence makes the direct
total-evidence observation faithful. -/
theorem evidenceToView_injective_of
    (evidence : State → Type u) (observe : State → View)
    (observeInjective : Function.Injective observe)
    (evidenceSubsingleton : ∀ state, Subsingleton (evidence state)) :
    Function.Injective
      (fun total : TotalEvidence evidence => observe total.1) := by
  intro left right sameView
  apply (sigmaFst_injective_iff_subsingleton evidence).2
    evidenceSubsingleton
  exact observeInjective sameView

/-- Faithfulness of the direct observation always forces every evidence fibre
to be subsingleton. -/
theorem subsingleton_of_evidenceToView_injective
    (evidence : State → Type u) (observe : State → View)
    (directInjective : Function.Injective
      (fun total : TotalEvidence evidence => observe total.1)) :
    ∀ state, Subsingleton (evidence state) := by
  intro state
  refine ⟨fun left right => ?_⟩
  have equalTotals :
      (⟨state, left⟩ : TotalEvidence evidence) = ⟨state, right⟩ :=
    directInjective rfl
  exact eq_of_heq (Sigma.mk.inj_iff.mp equalTotals).2

/-- If every state has evidence, direct faithfulness also forces the selected
state observer to be faithful. -/
theorem observer_injective_of_evidenceToView_injective
    (evidence : State → Type u) (observe : State → View)
    (inhabited : ∀ state, Nonempty (evidence state))
    (directInjective : Function.Injective
      (fun total : TotalEvidence evidence => observe total.1)) :
    Function.Injective observe := by
  intro left right sameView
  obtain ⟨leftEvidence⟩ := inhabited left
  obtain ⟨rightEvidence⟩ := inhabited right
  have equalTotals :
      (⟨left, leftEvidence⟩ : TotalEvidence evidence) =
        ⟨right, rightEvidence⟩ :=
    directInjective sameView
  exact congrArg Sigma.fst equalTotals

/-- With inhabited fibres, direct observation is faithful exactly when state
observation is faithful and evidence is proof-irrelevant. -/
theorem evidenceToView_injective_iff
    (evidence : State → Type u) (observe : State → View)
    (inhabited : ∀ state, Nonempty (evidence state)) :
    Function.Injective
        (fun total : TotalEvidence evidence => observe total.1) ↔
      Function.Injective observe ∧
        ∀ state, Subsingleton (evidence state) := by
  constructor
  · intro directInjective
    exact ⟨observer_injective_of_evidenceToView_injective
        evidence observe inhabited directInjective,
      subsingleton_of_evidenceToView_injective
        evidence observe directInjective⟩
  · rintro ⟨observeInjective, evidenceSubsingleton⟩
    exact evidenceToView_injective_of evidence observe
      observeInjective evidenceSubsingleton

/-! ## Invariance under fibrewise equivalence -/

/-- Fibrewise equivalence induces an equivalence of total evidence while
retaining the state index exactly. -/
def totalEvidenceEquiv
    {first second : State → Type u}
    (equivalence : ∀ state, first state ≃ second state) :
    TotalEvidence first ≃ TotalEvidence second where
  toFun total := ⟨total.1, equivalence total.1 total.2⟩
  invFun total := ⟨total.1, (equivalence total.1).symm total.2⟩
  left_inv := by
    rintro ⟨state, evidence⟩
    exact Sigma.ext rfl
      (heq_of_eq ((equivalence state).left_inv evidence))
  right_inv := by
    rintro ⟨state, evidence⟩
    exact Sigma.ext rfl
      (heq_of_eq ((equivalence state).right_inv evidence))

@[simp] theorem totalEvidenceEquiv_fst
    {first second : State → Type u}
    (equivalence : ∀ state, first state ≃ second state)
    (total : TotalEvidence first) :
    (totalEvidenceEquiv equivalence total).1 = total.1 :=
  rfl

/-- Loss of program information in the dependent-evidence triangle is
invariant under a fibrewise equivalence.  Thus replacing evidence by an exact
representation neither creates nor repairs observational collapse. -/
theorem comparison_loses_congr_fibreEquiv
    {first second : State → Type u} (observe : State → View)
    (equivalence : ∀ state, first state ≃ second state) :
    (comparison first observe).LosesProgramInformation ↔
      (comparison second observe).LosesProgramInformation := by
  let totalEquivalence := totalEvidenceEquiv equivalence
  constructor
  · rintro ⟨context, left, right, distinct, sameView⟩
    refine ⟨context, totalEquivalence left, totalEquivalence right, ?_, ?_⟩
    · exact fun equal => distinct (totalEquivalence.injective equal)
    · exact sameView
  · rintro ⟨context, left, right, distinct, sameView⟩
    refine ⟨context, totalEquivalence.symm left,
      totalEquivalence.symm right, ?_, ?_⟩
    · exact fun equal => distinct (totalEquivalence.symm.injective equal)
    · exact sameView

/-! ## Information loss in the comparison -/

private def here : Contextᵒᵖ :=
  _root_.Opposite.op
    (_root_.CategoryTheory.Discrete.mk PUnit.unit)

/-- Any explicit pair of distinct total-evidence points with one view proves
that the comparison loses program information. -/
theorem comparison_loses_of_witness
    (evidence : State → Type u) (observe : State → View)
    {left right : TotalEvidence evidence}
    (distinct : left ≠ right)
    (sameView : observe left.1 = observe right.1) :
    (comparison evidence observe).LosesProgramInformation :=
  ⟨here, left, right, distinct, sameView⟩

/-! ## Branching operational canary -/

namespace Canary

open Mettapedia.Algebra
open Mettapedia.GSLT.Dynamics.EvidenceIndexedBranchingRealization

abbrev BranchTotal := TotalEvidence exactFamily.Exact

def rightFalse : BranchTotal := ⟨.rightDone, false⟩
def rightTrue : BranchTotal := ⟨.rightDone, true⟩
def leftUnit : BranchTotal := ⟨.leftDone, PUnit.unit⟩

def branchingComparison : Comparison.{0, 0, 0} Context :=
  comparison exactFamily.Exact sourceCompletion.observe

/-- Proof relevance is already lost at the state face: two evidence values at
one endpoint become one state. -/
theorem evidence_values_lost_at_state :
    (evidenceToState exactFamily.Exact).app here rightFalse =
        (evidenceToState exactFamily.Exact).app here rightTrue ∧
      rightFalse ≠ rightTrue := by
  refine ⟨rfl, ?_⟩
  intro equalTotals
  exact Bool.false_ne_true
    (eq_of_heq (Sigma.mk.inj_iff.mp equalTotals).2)

/-- The completion observer also identifies the two distinct completed
states. -/
theorem completed_states_lost_at_view :
    sourceCompletion.observe leftUnit.1 =
        sourceCompletion.observe rightFalse.1 ∧
      leftUnit.1 ≠ rightFalse.1 := by
  exact ⟨rfl, by intro equalStates; cases equalStates⟩

/-- Therefore the dependent-evidence comparison is necessarily non-exact on
its program-to-space leg. -/
theorem branching_comparison_loses_program_information :
    branchingComparison.LosesProgramInformation :=
  comparison_loses_of_witness exactFamily.Exact sourceCompletion.observe
    (left := rightFalse) (right := rightTrue) (by
      intro equalTotals
      exact Bool.false_ne_true
        (eq_of_heq (Sigma.mk.inj_iff.mp equalTotals).2)) rfl

/-- Work/span read from the authentic operational realization, indexed by the
retained endpoint. -/
def totalEvidenceWorkSpan : BranchTotal → WorkSpan
  | ⟨.entry, evidence⟩ => nomatch evidence
  | ⟨.leftDone, _⟩ => realizedEventCost leftEvent
  | ⟨.rightDone, _⟩ => realizedEventCost rightEvent

@[simp] theorem left_totalEvidenceWorkSpan :
    totalEvidenceWorkSpan leftUnit = ⟨2, 2⟩ :=
  rfl

@[simp] theorem right_totalEvidenceWorkSpan :
    totalEvidenceWorkSpan rightFalse = ⟨1, 1⟩ :=
  rfl

/-- The extensional completion view cannot reconstruct authentic operational
cost, even though cost is well-defined on total evidence. -/
theorem workSpan_does_not_factor_through_completion :
    ¬ Factors
      (fun total : BranchTotal => sourceCompletion.observe total.1)
      totalEvidenceWorkSpan := by
  let fibre : NonTrivialFiber
      (fun total : BranchTotal => sourceCompletion.observe total.1)
      totalEvidenceWorkSpan :=
    { left := leftUnit
      right := rightFalse
      sameShadow := rfl
      differentValue := by decide }
  exact fibre.not_factors

/-- Paired boundary: the comparison is coherent, yet it loses both evidence
and endpoint distinctions, and its spatial face does not determine cost. -/
theorem dependent_evidence_trinity_boundary :
    branchingComparison.LosesProgramInformation ∧
      ¬ Factors
        (fun total : BranchTotal => sourceCompletion.observe total.1)
        totalEvidenceWorkSpan :=
  ⟨branching_comparison_loses_program_information,
    workSpan_does_not_factor_through_completion⟩

end Canary

#print axioms sigmaFst_injective_iff_subsingleton
#print axioms evidenceToView_injective_iff
#print axioms totalEvidenceEquiv
#print axioms comparison_loses_congr_fibreEquiv
#print axioms comparison_loses_of_witness
#print axioms Canary.evidence_values_lost_at_state
#print axioms Canary.completed_states_lost_at_view
#print axioms Canary.branching_comparison_loses_program_information
#print axioms Canary.workSpan_does_not_factor_through_completion
#print axioms Canary.dependent_evidence_trinity_boundary

end Mettapedia.Computability.DependentEvidenceComparison
