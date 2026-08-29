import Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedComposition

/-!
# Theory-state composition for official TSTP equisatisfiability edges

An equisatisfiability status is not a positive formula judgment.  In a fixed
model universe it licenses replacement of one theory fragment by another only
when the calculus proves that the replacement remains equisatisfiable in every
surrounding theory context.  This module states that stronger same-model law,
connects accepted `.esa` edges to it, and proves preservation along arbitrary
finite replacement traces.  Signature-extending transformations require an
indexed model-extension profile rather than this one.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialTheoryStateComposition

open Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedService
open Mettapedia.Languages.TPTP.StatusSemantics

universe uModel

variable {Formula Rule Evidence Provenance Obligation : Type}

/-! ## Contextual theory replacement -/

/-- Replacing `parents` by `inferred` preserves satisfiability between any
left and right theory contexts.  Plain equisatisfiability of the isolated
fragments is not strong enough for this operation. -/
def ContextualEquiSatisfiable
    (semantics : ClassicalModelSemantics.{0, uModel} Formula)
    (parents : List Formula) (inferred : Formula) : Prop :=
  forall left right,
    semantics.Satisfiable (left ++ parents ++ right) <->
      semantics.Satisfiable (left ++ [inferred] ++ right)

/-- One exact replacement inside a theory list.  Both contexts and both
fragment boundaries are retained, so the theorem does not silently identify
lists up to permutation or duplicate erasure. -/
structure TheoryStateReplacement
    (semantics : ClassicalModelSemantics.{0, uModel} Formula)
    (source target : List Formula) : Type where
  left : List Formula
  right : List Formula
  parents : List Formula
  inferred : Formula
  source_eq : source = left ++ parents ++ right
  target_eq : target = left ++ [inferred] ++ right
  contextual : ContextualEquiSatisfiable semantics parents inferred

theorem TheoryStateReplacement.satisfiable_iff
    {semantics : ClassicalModelSemantics.{0, uModel} Formula}
    {source target : List Formula}
    (replacement : TheoryStateReplacement semantics source target) :
    semantics.Satisfiable source <-> semantics.Satisfiable target := by
  rcases replacement with
    ⟨left, right, parents, inferred, rfl, rfl, contextual⟩
  exact contextual left right

/-- Finite theory transformation built only from exact contextual
replacements. -/
inductive TheoryStateTrace
    (semantics : ClassicalModelSemantics.{0, uModel} Formula) :
    List Formula -> List Formula -> Prop where
  | refl (state : List Formula) : TheoryStateTrace semantics state state
  | step {source middle target : List Formula}
      (replacement : TheoryStateReplacement semantics source middle)
      (rest : TheoryStateTrace semantics middle target) :
      TheoryStateTrace semantics source target

theorem TheoryStateTrace.satisfiable_iff
    {semantics : ClassicalModelSemantics.{0, uModel} Formula}
    {source target : List Formula}
    (trace : TheoryStateTrace semantics source target) :
    semantics.Satisfiable source <-> semantics.Satisfiable target := by
  induction trace with
  | refl => exact Iff.rfl
  | step replacement rest inductionHypothesis =>
      exact replacement.satisfiable_iff.trans inductionHypothesis

/-! ## Exact connection to accepted official edges -/

/-- Origins which may occur as entries of a theory being transformed.
Counter-theorems are negative judgments and cannot become positive theory
entries. -/
def TheoryEntryOrigin : NodeOrigin -> Prop
  | .input => True
  | .inferred .thm => True
  | .inferred .esa => True
  | _ => False

/-- Semantic content extracted from one accepted `.esa` edge. -/
structure CheckedEquisatisfiableEdge
    (semantics : ClassicalModelSemantics.{0, uModel} Formula)
    (parents : List (SemanticNode Formula))
    (conclusion : SemanticNode Formula) : Prop where
  parents_are_theory_entries : forall parent, parent ∈ parents ->
    TheoryEntryOrigin parent.origin
  conclusion_origin : conclusion.origin = .inferred .esa
  isolated_relation : semantics.EquiSatisfiableRelation {
    parents := parents.map SemanticNode.body
    inferred := conclusion.body
  }
  contextual : ContextualEquiSatisfiable semantics
    (parents.map SemanticNode.body) conclusion.body

def CheckedEquisatisfiableEdge.replacement
    {semantics : ClassicalModelSemantics.{0, uModel} Formula}
    {parents : List (SemanticNode Formula)}
    {conclusion : SemanticNode Formula}
    (edge : CheckedEquisatisfiableEdge semantics parents conclusion)
    (left right : List Formula) :
    TheoryStateReplacement semantics
      (left ++ parents.map SemanticNode.body ++ right)
      (left ++ [conclusion.body] ++ right) where
  left := left
  right := right
  parents := parents.map SemanticNode.body
  inferred := conclusion.body
  source_eq := rfl
  target_eq := rfl
  contextual := edge.contextual

/-- In one fixed model universe, a calculus may use `.esa` as a theory
transformation only by supplying the stronger context-stable theorem.  Its
ordinary TSTP status meaning remains the common local equisatisfiability
relation, so both claims stay visible.  Fresh-symbol extensions need a
separate indexed profile relating source and target model signatures. -/
structure ContextualEquisatisfiableProfile
    (semantics : ClassicalModelSemantics.{0, uModel} Formula)
    (service : Service Formula Rule Evidence) where
  meaning_eq : service.calculus.meaning = semantics.commonStatusMeaning
  accepted_status : forall rule status parents evidence conclusion,
    service.calculus.check rule status parents evidence conclusion = true ->
      status = .esa
  parents_are_theory_entries : forall rule status origins,
    service.calculus.parentOriginsAccepted rule status origins = true ->
      forall origin, origin ∈ origins -> TheoryEntryOrigin origin
  contextual_sound : forall rule parents evidence conclusion,
    service.calculus.check rule .esa parents evidence conclusion = true ->
      ContextualEquiSatisfiable semantics parents conclusion

theorem ContextualEquisatisfiableProfile.checkedEdge
    {semantics : ClassicalModelSemantics.{0, uModel} Formula}
    {service : Service Formula Rule Evidence}
    (profile : ContextualEquisatisfiableProfile semantics service)
    {state next : MetadataState} {rule : Rule}
    {parents : List (SemanticNode Formula)}
    {evidence : OfficialEvidence Evidence}
    {conclusion : SemanticNode Formula}
    (stepSound : StepSound service state next rule parents evidence conclusion) :
    CheckedEquisatisfiableEdge semantics parents conclusion := by
  rcases stepSound with
    ⟨normalized, _normalizedEq, _parentSignatures, _conclusionSignature,
      metadataAccepted, _nextEq,
      parentOriginsAccepted, _ruleMetadataAccepted,
      calculusAccepted, semanticMeaning⟩
  have statusEq : normalized.status = .esa :=
    profile.accepted_status rule normalized.status
      (parents.map SemanticNode.body) evidence.calculus conclusion.body
      calculusAccepted
  have originEq : conclusion.origin = .inferred normalized.status :=
    (metadataAccepted_iff_conditions state parents conclusion normalized).mp
      metadataAccepted |>.1
  refine ⟨?_, originEq.trans (congrArg NodeOrigin.inferred statusEq), ?_, ?_⟩
  · intro parent parentMember
    apply profile.parents_are_theory_entries rule normalized.status
      (parents.map SemanticNode.origin) parentOriginsAccepted parent.origin
    exact List.mem_map.mpr ⟨parent, parentMember, rfl⟩
  · rw [profile.meaning_eq] at semanticMeaning
    rw [statusEq] at semanticMeaning
    simpa [ClassicalModelSemantics.commonStatusMeaning] using semanticMeaning
  · rw [statusEq] at calculusAccepted
    exact profile.contextual_sound rule (parents.map SemanticNode.body)
      evidence.calculus conclusion.body calculusAccepted

/-! ## Contextual-strength canaries -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedComposition
open Mettapedia.GSLT.LanguageDef.TptpOfficialUsefulInfo

def semantics : ClassicalModelSemantics Bool :=
  TptpOfficialStatusIndexedComposition.Canary.twoModelSemantics

/-- Duplicate elimination is a genuine context-stable replacement. -/
theorem duplicate_true_is_contextual :
    ContextualEquiSatisfiable semantics [true, true] true := by
  intro left right
  constructor
  · rintro ⟨model, satisfied⟩
    refine ⟨model, ?_⟩
    intro formula member
    apply satisfied formula
    simpa using member
  · rintro ⟨model, satisfied⟩
    refine ⟨model, ?_⟩
    intro formula member
    apply satisfied formula
    simpa using member

/-- Isolated equisatisfiability does not license replacement under arbitrary
surrounding axioms. -/
theorem isolated_equisatisfiability_is_not_contextual :
    semantics.EquiSatisfiableRelation {
      parents := [true]
      inferred := false
    } /\
    Not (ContextualEquiSatisfiable semantics [true] false) := by
  constructor
  · exact Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedComposition.Canary.equisatisfiable_does_not_collapse_to_theorem.1
  · intro contextual
    have sourceSatisfiable : semantics.Satisfiable [true, true] := by
      refine ⟨true, ?_⟩
      intro formula member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl
    have targetSatisfiable : semantics.Satisfiable [true, false] := by
      simpa using (contextual [true] []).mp sourceSatisfiable
    rcases targetSatisfiable with ⟨model, satisfied⟩
    have trueSatisfied := satisfied true (by simp)
    have falseSatisfied := satisfied false (by simp)
    change model = true at trueSatisfied
    change model = false at falseSatisfied
    have impossible : true = false := trueSatisfied.symm.trans falseSatisfied
    cases impossible

inductive EsaRule where
  | deduplicateTrue
  deriving DecidableEq, Repr

def theoryEntryOriginB : NodeOrigin -> Bool
  | .input => true
  | .inferred .thm => true
  | .inferred .esa => true
  | _ => false

def esaCalculus : Calculus Bool EsaRule Unit where
  meaning := semantics.commonStatusMeaning
  parentOriginsAccepted := fun _ _ origins => origins.all theoryEntryOriginB
  ruleMetadataAccepted := fun _ _ _ => true
  check := fun _ status parents _ conclusion =>
    decide (status = .esa /\ parents = [true, true] /\ conclusion = true)
  check_sound := by
    intro rule status parents evidence conclusion accepted
    have conditions := of_decide_eq_true accepted
    rcases conditions with ⟨rfl, rfl, rfl⟩
    change semantics.Satisfiable [true, true] <-> semantics.Satisfiable [true]
    exact duplicate_true_is_contextual [] []

def esaService : Service Bool EsaRule Unit where
  formulaSignature := { principalSymbols? := fun _ => some ∅ }
  calculus := esaCalculus

def firstInput : SemanticNode Bool := {
  name := "first-input"
  role := .axiom
  origin := .input
  body := true
  principalSymbols := ∅
  openAssumptions := ∅
}

def secondInput : SemanticNode Bool := {
  name := "second-input"
  role := .axiom
  origin := .input
  body := true
  principalSymbols := ∅
  openAssumptions := ∅
}

def deduplicatedConclusion : SemanticNode Bool := {
  name := "deduplicated"
  role := .plain
  origin := .inferred .esa
  body := true
  principalSymbols := ∅
  openAssumptions := ∅
}

def emptyState : MetadataState := { knownSymbols := ∅ }

def esaMetadata : RuleMetadata := {
  status := .esa
  assumptions := []
  newSymbols := []
  rawItems := []
  ruleInfo := []
}

def esaEvidence : OfficialEvidence Unit := {
  metadata := esaMetadata
  calculus := ()
}

theorem esaStep_sound :
    StepSound esaService emptyState emptyState .deduplicateTrue
      [firstInput, secondInput] esaEvidence deduplicatedConclusion := by
  refine ⟨{
      status := .esa
      declaredAssumptions := ∅
      dischargedAssumptions := ∅
      introducedSymbols := []
    }, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · intro parent parentMember
    have parentEq : parent = firstInput \/ parent = secondInput := by
      simpa using parentMember
    rcases parentEq with rfl | rfl <;> rfl
  · rfl
  · exact esaCalculus.check_sound .deduplicateTrue .esa
      [true, true] () true rfl

def esaProfile : ContextualEquisatisfiableProfile semantics esaService where
  meaning_eq := rfl
  accepted_status := by
    intro rule status parents evidence conclusion accepted
    exact (of_decide_eq_true accepted).1
  parents_are_theory_entries := by
    intro rule status origins accepted origin member
    have originAccepted := List.all_eq_true.mp accepted origin member
    cases origin with
    | input => trivial
    | inferred originStatus =>
        cases originStatus <;>
          simp [theoryEntryOriginB, TheoryEntryOrigin] at originAccepted ⊢
  contextual_sound := by
    intro rule parents evidence conclusion accepted
    have conditions := of_decide_eq_true accepted
    rcases conditions with ⟨_, rfl, rfl⟩
    exact duplicate_true_is_contextual

def checkedEsaEdge :
    CheckedEquisatisfiableEdge semantics [firstInput, secondInput]
      deduplicatedConclusion :=
  esaProfile.checkedEdge esaStep_sound

theorem checked_edge_retains_exact_esa_origin :
    deduplicatedConclusion.origin = .inferred .esa :=
  checkedEsaEdge.conclusion_origin

theorem checked_edge_retains_local_esa_relation :
    semantics.EquiSatisfiableRelation {
      parents := [true, true]
      inferred := true
    } := by
  simpa [firstInput, secondInput, deduplicatedConclusion] using
    checkedEsaEdge.isolated_relation

def firstReplacement : TheoryStateReplacement semantics
    [true, true, true, true] [true, true, true] := by
  simpa [firstInput, secondInput, deduplicatedConclusion] using
    checkedEsaEdge.replacement [] [true, true]

def secondReplacement : TheoryStateReplacement semantics
    [true, true, true] [true, true] := by
  simpa [firstInput, secondInput, deduplicatedConclusion] using
    checkedEsaEdge.replacement [] [true]

def duplicateEliminationTrace : TheoryStateTrace semantics
    [true, true, true, true] [true, true] :=
  .step firstReplacement (.step secondReplacement (.refl [true, true]))

theorem duplicate_elimination_trace_preserves_satisfiability :
    semantics.Satisfiable [true, true, true, true] <->
      semantics.Satisfiable [true, true] :=
  duplicateEliminationTrace.satisfiable_iff

end Canary

#print axioms TheoryStateReplacement.satisfiable_iff
#print axioms TheoryStateTrace.satisfiable_iff
#print axioms ContextualEquisatisfiableProfile.checkedEdge
#print axioms Canary.duplicate_true_is_contextual
#print axioms Canary.isolated_equisatisfiability_is_not_contextual
#print axioms Canary.esaStep_sound
#print axioms Canary.checked_edge_retains_exact_esa_origin
#print axioms Canary.checked_edge_retains_local_esa_relation
#print axioms Canary.duplicate_elimination_trace_preserves_satisfiability

end Mettapedia.GSLT.LanguageDef.TptpOfficialTheoryStateComposition
