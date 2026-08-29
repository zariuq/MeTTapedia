import Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedService

/-!
# Semantic composition for status-indexed TSTP derivations

Checking the local relation named by every TSTP status does not by itself
choose a meaning for an entire derivation.  In particular, theoremhood,
counter-theoremhood, and equisatisfiability do not compose by one implicit
rule.  This module makes the missing calculus-specific composition law an
explicit interface and proves that the single-pass derivation machine
preserves every supplied law.

The common all-theorem profile is derived as a reusable specialization.  A
mixed-status calculus must supply its own `CompositionPolicy`; unsupported
mixtures cannot acquire theorem meaning through this module.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedComposition

open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedService
open Mettapedia.Languages.TPTP.StatusSemantics

universe uModel

variable {Formula Rule Evidence Provenance Obligation : Type}
  {service : Service Formula Rule Evidence}
  {boundary : MachineBoundary Formula Provenance Obligation}

/-! ## Explicit composition boundary -/

/-- A calculus-specific law for composing checked local edges into one
meaning of formula occurrences.  The inference field receives the exact
status-indexed `StepSound` witness, so a mixed-status calculus must explain
the semantic use of every status it admits. -/
structure CompositionPolicy
    (service : Service Formula Rule Evidence)
    (boundary : MachineBoundary Formula Provenance Obligation) where
  Meaning : SemanticNode Formula -> Prop
  input_sound : forall state provenance formula,
    InputConditions service boundary state provenance formula -> Meaning formula
  infer_sound : forall state next rule parents evidence conclusion,
    (forall parent, parent ∈ parents -> Meaning parent) ->
    StepSound service state next rule parents evidence conclusion ->
      Meaning conclusion

/-- Every checked derivation has the meaning supplied by its explicit
composition policy. -/
theorem derivation_meaning
    (policy : CompositionPolicy service boundary)
    {formula : SemanticNode Formula}
    (derivation : StatusDerivation service boundary formula) :
    policy.Meaning formula := by
  induction derivation with
  | input state provenance formula conditions =>
      exact policy.input_sound state provenance formula conditions
  | infer state next rule parents evidence conclusion parentsChecked
      stepSound inductionHypotheses =>
      exact policy.infer_sound state next rule parents evidence conclusion
        inductionHypotheses stepSound

/-- A root policy connects one formula-occurrence meaning to a named
whole-problem objective.  Closed assumptions and the problem-specific root
authorization remain separate premises. -/
structure ObjectivePolicy
    {service : Service Formula Rule Evidence}
    {boundary : MachineBoundary Formula Provenance Obligation}
    (composition : CompositionPolicy service boundary) where
  Objective : Obligation -> Prop
  root_sound : forall state formula obligation,
    composition.Meaning formula ->
    formula.openAssumptions = ∅ ->
    boundary.rootAuthorized state formula obligation = true ->
      Objective obligation

/-- A structurally accepted root projects to a semantic objective only
through an explicit root policy. -/
theorem checkedObjective_meaning
    (composition : CompositionPolicy service boundary)
    (objective : ObjectivePolicy composition)
    {obligation : Obligation}
    (checked : StatusCheckedObjective service boundary obligation) :
    objective.Objective obligation := by
  cases checked with
  | verified state formula derivation assumptionsClosed rootAuthorized =>
      exact objective.root_sound state formula obligation
        (derivation_meaning composition derivation)
        assumptionsClosed rootAuthorized

/-- The explicit policies instantiate the one continuous invariant used by
all branches of the generic derivation-check machine. -/
def soundServices
    (composition : CompositionPolicy service boundary)
    (objective : ObjectivePolicy composition) :
    SoundServices (machineServices service boundary) where
  Valid := composition.Meaning
  Objective := objective.Objective
  StateValid := fun _ => True
  initial_sound := trivial
  input_sound := by
    intro state provenance formula next accepted _stateValid
    have exactInput := machineServices_input_exact
      service boundary state next provenance formula accepted
    exact ⟨composition.input_sound state provenance formula exactInput.1,
      trivial⟩
  infer_sound := by
    intro state rule parents evidence conclusion next accepted
      _stateValid parentsValid
    have exactStep := machineServices_infer_sound
      service boundary state next rule parents evidence conclusion accepted
    exact ⟨composition.infer_sound state next rule parents evidence conclusion
      parentsValid exactStep, trivial⟩
  root_sound := by
    intro state formula obligation accepted _stateValid valid
    have exactRoot := machineServices_root_exact
      service boundary state formula obligation accepted
    exact objective.root_sound state formula obligation valid
      exactRoot.1 exactRoot.2

/-! ## Common all-theorem specialization -/

/-- A formula occurrence is a theorem relative to one fixed submitted
premise collection. -/
def RelativeTheorem
    (semantics : ClassicalModelSemantics.{0, uModel} Formula)
    (premises : List Formula) (formula : SemanticNode Formula) : Prop :=
  semantics.TheoremRelation {
    parents := premises
    inferred := formula.body
  }

/-- Exact obligations needed to compose a status-indexed service whose
accepted edges are all ordinary theorem-preserving edges.  The status premise
is load-bearing: no `.cth` or `.esa` edge is coerced into `.thm`. -/
structure AllTheoremProfile
    (semantics : ClassicalModelSemantics.{0, uModel} Formula)
    (premises : List Formula)
    (service : Service Formula Rule Evidence)
    (boundary : MachineBoundary Formula Provenance Obligation) where
  meaning_eq : service.calculus.meaning = semantics.commonStatusMeaning
  input_sound : forall state provenance formula,
    InputConditions service boundary state provenance formula ->
      RelativeTheorem semantics premises formula
  accepted_status : forall rule status parents evidence conclusion,
    service.calculus.check rule status parents evidence conclusion = true ->
      status = .thm

/-- The common theorem-only relation composes through arbitrary checked DAG
shape, parent order, and parent multiplicity. -/
def AllTheoremProfile.compositionPolicy
    {semantics : ClassicalModelSemantics.{0, uModel} Formula}
    {premises : List Formula}
    {service : Service Formula Rule Evidence}
    {boundary : MachineBoundary Formula Provenance Obligation}
    (profile : AllTheoremProfile semantics premises service boundary) :
    CompositionPolicy service boundary where
  Meaning := RelativeTheorem semantics premises
  input_sound := profile.input_sound
  infer_sound := by
    intro state next rule parents evidence conclusion parentsMeaning stepSound
    rcases stepSound with
      ⟨normalized, _normalizedEq, _parentSignatures, _conclusionSignature,
        _metadataAccepted, _nextEq,
        _parentOriginsAccepted, _ruleMetadataAccepted,
        calculusAccepted, semanticMeaning⟩
    have statusEq : normalized.status = .thm :=
      profile.accepted_status rule normalized.status
        (parents.map SemanticNode.body) evidence.calculus conclusion.body
        calculusAccepted
    have localTheorem : semantics.TheoremRelation {
        parents := parents.map SemanticNode.body
        inferred := conclusion.body
      } := by
      rw [profile.meaning_eq] at semanticMeaning
      simpa [ClassicalModelSemantics.commonStatusMeaning, statusEq] using
        semanticMeaning
    intro model premisesSatisfied
    apply localTheorem model
    intro parentBody member
    obtain ⟨parent, parentMember, rfl⟩ := List.mem_map.mp member
    exact parentsMeaning parent parentMember model premisesSatisfied

/-! ## Signed theorem/countertheorem specialization -/

/-- A formula occurrence is a counter-theorem relative to one fixed submitted
premise collection. -/
def RelativeCounterTheorem
    (semantics : ClassicalModelSemantics.{0, uModel} Formula)
    (premises : List Formula) (formula : SemanticNode Formula) : Prop :=
  semantics.CounterTheoremRelation {
    parents := premises
    inferred := formula.body
  }

/-- Origins which provide a formula positively to an ordinary inference.
Counter-theorems are signed negative judgments, not reusable positive
formulae.  Equisatisfiability is a theory-state relation and is excluded too. -/
def PositivePremiseOrigin : NodeOrigin -> Prop
  | .input => True
  | .inferred .thm => True
  | _ => False

/-- The global meaning of the first explicitly signed composition profile.
Input occurrences and theorem conclusions are positive judgments;
counter-theorem conclusions are negative judgments.  Other statuses acquire
no formula-level meaning through this profile. -/
def SignedRelativeMeaning
    (semantics : ClassicalModelSemantics.{0, uModel} Formula)
    (premises : List Formula) (formula : SemanticNode Formula) : Prop :=
  match formula.origin with
  | .input => RelativeTheorem semantics premises formula
  | .inferred .thm => RelativeTheorem semantics premises formula
  | .inferred .cth => RelativeCounterTheorem semantics premises formula
  | _ => False

theorem signedRelativeMeaning_of_positiveOrigin
    {semantics : ClassicalModelSemantics.{0, uModel} Formula}
    {premises : List Formula} {formula : SemanticNode Formula}
    (meaning : SignedRelativeMeaning semantics premises formula)
    (positive : PositivePremiseOrigin formula.origin) :
    RelativeTheorem semantics premises formula := by
  cases originEq : formula.origin with
  | input => simpa [SignedRelativeMeaning, originEq] using meaning
  | inferred status =>
      rw [originEq] at positive
      cases status <;> simp [PositivePremiseOrigin] at positive
      case thm =>
        simpa [SignedRelativeMeaning, originEq] using meaning

/-- Exact obligations for a calculus which admits ordinary theorem and
counter-theorem conclusions while consuming only positive formula premises.
The parent-origin field prevents a negative or theory-state judgment from
silently entering an ordinary parent list. -/
structure TheoremCounterProfile
    (semantics : ClassicalModelSemantics.{0, uModel} Formula)
    (premises : List Formula)
    (service : Service Formula Rule Evidence)
    (boundary : MachineBoundary Formula Provenance Obligation) where
  meaning_eq : service.calculus.meaning = semantics.commonStatusMeaning
  input_sound : forall state provenance formula,
    InputConditions service boundary state provenance formula ->
      RelativeTheorem semantics premises formula
  accepted_status : forall rule status parents evidence conclusion,
    service.calculus.check rule status parents evidence conclusion = true ->
      status = .thm \/ status = .cth
  parents_positive : forall rule status origins,
    service.calculus.parentOriginsAccepted rule status origins = true ->
      forall origin, origin ∈ origins -> PositivePremiseOrigin origin

/-- The signed theorem/counter-theorem profile composes through a checked DAG
without treating a negative conclusion as a positive premise. -/
def TheoremCounterProfile.compositionPolicy
    {semantics : ClassicalModelSemantics.{0, uModel} Formula}
    {premises : List Formula}
    {service : Service Formula Rule Evidence}
    {boundary : MachineBoundary Formula Provenance Obligation}
    (profile : TheoremCounterProfile semantics premises service boundary) :
    CompositionPolicy service boundary where
  Meaning := SignedRelativeMeaning semantics premises
  input_sound := by
    intro state provenance formula conditions
    have originEq := conditions.1
    simp only [SignedRelativeMeaning, originEq]
    exact profile.input_sound state provenance formula conditions
  infer_sound := by
    intro state next rule parents evidence conclusion parentsMeaning stepSound
    rcases stepSound with
      ⟨normalized, _normalizedEq, _parentSignatures, _conclusionSignature,
        metadataAccepted, _nextEq,
        parentOriginsAccepted, _ruleMetadataAccepted,
        calculusAccepted, semanticMeaning⟩
    have originEq : conclusion.origin = .inferred normalized.status :=
      (metadataAccepted_iff_conditions state parents conclusion normalized).mp
        metadataAccepted |>.1
    have parentTheorems : forall parent, parent ∈ parents ->
        RelativeTheorem semantics premises parent := by
      intro parent parentMember
      apply signedRelativeMeaning_of_positiveOrigin
        (parentsMeaning parent parentMember)
      apply profile.parents_positive rule normalized.status
        (parents.map SemanticNode.origin) parentOriginsAccepted
        parent.origin
      exact List.mem_map.mpr ⟨parent, parentMember, rfl⟩
    have localMeaning : semantics.commonStatusMeaning.Meaning normalized.status {
        parents := parents.map SemanticNode.body
        inferred := conclusion.body
      } := by
      rw [← profile.meaning_eq]
      exact semanticMeaning
    rcases profile.accepted_status rule normalized.status
        (parents.map SemanticNode.body) evidence.calculus conclusion.body
        calculusAccepted with statusEq | statusEq
    · rw [statusEq] at originEq localMeaning
      simp only [SignedRelativeMeaning, originEq]
      have localTheorem : semantics.TheoremRelation {
          parents := parents.map SemanticNode.body
          inferred := conclusion.body
        } := by
        simpa [ClassicalModelSemantics.commonStatusMeaning] using localMeaning
      intro model premisesSatisfied
      apply localTheorem model
      intro parentBody member
      obtain ⟨parent, parentMember, rfl⟩ := List.mem_map.mp member
      exact parentTheorems parent parentMember model premisesSatisfied
    · rw [statusEq] at originEq localMeaning
      simp only [SignedRelativeMeaning, originEq]
      have localCounter : semantics.CounterTheoremRelation {
          parents := parents.map SemanticNode.body
          inferred := conclusion.body
        } := by
        simpa [ClassicalModelSemantics.commonStatusMeaning] using localMeaning
      intro model premisesSatisfied
      apply localCounter model
      intro parentBody member
      obtain ⟨parent, parentMember, rfl⟩ := List.mem_map.mp member
      exact parentTheorems parent parentMember model premisesSatisfied

/-! ## Non-collapse canary -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.TptpOfficialUsefulInfo

/-- Two models make equisatisfiability visibly weaker than entailment. -/
def twoModelSemantics : ClassicalModelSemantics Bool where
  Model := Bool
  satisfies := fun model formula => model = formula
  negate := not
  satisfies_negate := by
    intro model formula
    cases model <;> cases formula <;> simp

def equisatisfiableButNotTheoremClaim : RelationClaim Bool := {
  parents := [true]
  inferred := false
}

inductive SignedRule where
  | counter
  deriving DecidableEq, Repr

def positiveOriginB : NodeOrigin -> Bool
  | .input => true
  | .inferred .thm => true
  | _ => false

/-- A tiny status-indexed calculus used to exercise the signed composition
profile.  It proves the negative judgment for `false` from the positive input
`true`; it does not reinterpret that negative judgment as a positive fact. -/
def signedCalculus : Calculus Bool SignedRule Unit where
  meaning := twoModelSemantics.commonStatusMeaning
  parentOriginsAccepted := fun _ _ origins => origins.all positiveOriginB
  ruleMetadataAccepted := fun _ _ _ => true
  check := fun _ status parents _ conclusion =>
    decide (status = .cth /\ parents = [true] /\ conclusion = false)
  check_sound := by
    intro rule status parents evidence conclusion accepted
    have conditions := of_decide_eq_true accepted
    rcases conditions with ⟨rfl, rfl, rfl⟩
    change twoModelSemantics.CounterTheoremRelation {
      parents := [true]
      inferred := false
    }
    intro model parentsSatisfied
    have modelTrue : model = true := parentsSatisfied true (by simp)
    simpa [twoModelSemantics] using modelTrue

def signedService : Service Bool SignedRule Unit where
  formulaSignature := { principalSymbols? := fun _ => some ∅ }
  calculus := signedCalculus

def signedBoundary : MachineBoundary Bool Unit Unit where
  initialMetadata := { knownSymbols := ∅ }
  inputAuthorized := fun _ formula => decide (formula.body = true)
  rootAuthorized := fun _ _ _ => false

def positiveInput : SemanticNode Bool := {
  name := "positive-input"
  role := .axiom
  origin := .input
  body := true
  principalSymbols := ∅
  openAssumptions := ∅
}

def negativeConclusion : SemanticNode Bool := {
  name := "negative-conclusion"
  role := .plain
  origin := .inferred .cth
  body := false
  principalSymbols := ∅
  openAssumptions := ∅
}

def counterMetadata : RuleMetadata := {
  status := .cth
  assumptions := []
  newSymbols := []
  rawItems := []
  ruleInfo := []
}

def counterEvidence : OfficialEvidence Unit := {
  metadata := counterMetadata
  calculus := ()
}

theorem positiveInput_conditions :
    InputConditions signedService signedBoundary signedBoundary.initialMetadata ()
      positiveInput := by
  simp [InputConditions, signedBoundary, positiveInput,
    NodeSignatureExact, signedService,
    expectedInputAssumptions,
    Mettapedia.GSLT.LanguageDef.TptpOfficialRoleSemantics.FormulaRole.semanticSupported,
    Mettapedia.GSLT.LanguageDef.TptpOfficialRoleSemantics.FormulaRole.requiresDischarge]

theorem counterStep_sound :
    StepSound signedService signedBoundary.initialMetadata
      signedBoundary.initialMetadata .counter [positiveInput]
      counterEvidence negativeConclusion := by
  refine ⟨{
      status := .cth
      declaredAssumptions := ∅
      dischargedAssumptions := ∅
      introducedSymbols := []
    }, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · intro parent parentMember
    simp only [List.mem_singleton] at parentMember
    subst parent
    rfl
  · rfl
  · exact signedCalculus.check_sound .counter .cth [true] () false rfl

def signedProfile : TheoremCounterProfile twoModelSemantics [true]
    signedService signedBoundary where
  meaning_eq := rfl
  input_sound := by
    intro state provenance formula conditions
    have bodyEq : formula.body = true := of_decide_eq_true conditions.2.2.1
    intro model premisesSatisfied
    rw [bodyEq]
    exact premisesSatisfied true (by simp)
  accepted_status := by
    intro rule status parents evidence conclusion accepted
    have conditions := of_decide_eq_true accepted
    exact Or.inr conditions.1
  parents_positive := by
    intro rule status origins accepted origin member
    have acceptedOrigin := List.all_eq_true.mp accepted origin member
    cases origin with
    | input => trivial
    | inferred originStatus =>
        cases originStatus <;>
          simp [positiveOriginB, PositivePremiseOrigin] at acceptedOrigin ⊢

def positiveInputDerivation :
    StatusDerivation signedService signedBoundary positiveInput :=
  .input signedBoundary.initialMetadata () positiveInput positiveInput_conditions

def negativeConclusionDerivation :
    StatusDerivation signedService signedBoundary negativeConclusion :=
  .infer signedBoundary.initialMetadata signedBoundary.initialMetadata
    .counter [positiveInput] counterEvidence negativeConclusion
    (by
      intro parent member
      simp only [List.mem_singleton] at member
      subst parent
      exact positiveInputDerivation)
    counterStep_sound

/-- The signed profile yields the negative relation named by `.cth`; the same
derivation does not manufacture an ordinary positive theorem. -/
theorem counterDerivation_has_negative_meaning :
    RelativeCounterTheorem twoModelSemantics [true] negativeConclusion := by
  have meaning := derivation_meaning signedProfile.compositionPolicy
    negativeConclusionDerivation
  change SignedRelativeMeaning twoModelSemantics [true] negativeConclusion at meaning
  simpa [SignedRelativeMeaning, negativeConclusion] using meaning

theorem counterDerivation_does_not_become_positive :
    Not (RelativeTheorem twoModelSemantics [true] negativeConclusion) := by
  intro theoremRelation
  have falseHolds := theoremRelation true (by
    intro formula member
    simp only [List.mem_singleton] at member
    subst formula
    rfl)
  change true = false at falseHolds
  cases falseHolds

/-- Equisatisfiability remains outside the signed formula-premise profile. -/
theorem esa_origin_has_no_signed_formula_meaning :
    Not (SignedRelativeMeaning twoModelSemantics [true] {
      name := "equisatisfiable-state"
      role := .plain
      origin := .inferred .esa
      body := true
      principalSymbols := ∅
      openAssumptions := ∅
    }) := by
  simp [SignedRelativeMeaning]

/-- A valid `.esa` edge cannot be silently used as a `.thm` edge. -/
theorem equisatisfiable_does_not_collapse_to_theorem :
    twoModelSemantics.EquiSatisfiableRelation
      equisatisfiableButNotTheoremClaim /\
    Not (twoModelSemantics.TheoremRelation
      equisatisfiableButNotTheoremClaim) := by
  constructor
  · constructor
    · rintro ⟨model, satisfied⟩
      exact ⟨false, by
        intro formula member
        simp only [equisatisfiableButNotTheoremClaim, List.mem_singleton]
          at member
        subst formula
        rfl⟩
    · rintro ⟨model, satisfied⟩
      exact ⟨true, by
        intro formula member
        simp only [equisatisfiableButNotTheoremClaim, List.mem_singleton]
          at member
        subst formula
        rfl⟩
  · intro theoremRelation
    have falseHolds := theoremRelation true (by
      intro formula member
      simp only [equisatisfiableButNotTheoremClaim, List.mem_singleton]
        at member
      subst formula
      rfl)
    change true = false at falseHolds
    cases falseHolds

end Canary

#print axioms derivation_meaning
#print axioms checkedObjective_meaning
#print axioms soundServices
#print axioms AllTheoremProfile.compositionPolicy
#print axioms signedRelativeMeaning_of_positiveOrigin
#print axioms TheoremCounterProfile.compositionPolicy
#print axioms Canary.counterStep_sound
#print axioms Canary.counterDerivation_has_negative_meaning
#print axioms Canary.counterDerivation_does_not_become_positive
#print axioms Canary.esa_origin_has_no_signed_formula_meaning
#print axioms Canary.equisatisfiable_does_not_collapse_to_theorem

end Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedComposition
