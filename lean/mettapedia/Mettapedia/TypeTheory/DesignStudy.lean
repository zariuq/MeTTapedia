import Mettapedia.TypeTheory.DesignDetermination
import Mettapedia.Enactive.Razor

/-!
# Evidence for an evolving specification

A specification names requirements independently of their implementations.
Evidence is indexed by one candidate: independent existence results for
different components cannot be combined into evidence for an assembly.
Incomplete evidence computes an outstanding-requirement list without
turning that list into proof obligations that have silently been discharged.

Necessity and preference are separate. `Determined` quantifies over the
entire stated admissible class. A `Criterion` compares that class without
asserting that a preferred candidate is logically forced. Uniform expression,
substitution, proof transport and representation cost can be requirements or
comparison axes; preservation of individual answers is not a complete design
criterion. Neither the candidate type nor its requirements are fixed here.
-/

namespace Mettapedia.TypeTheory.DesignStudy

open Mettapedia.TypeTheory.DesignDetermination
open Mettapedia.Enactive.Razor

universe u v

/-- A named family of semantic requirements and the subset currently demanded.
`holds` must state the actual property, including any observer or assumptions;
names and evidence provenance belong to its application-specific ledger. -/
structure Specification (Candidate : Type u) (Requirement : Type v) where
  holds : Requirement → Candidate → Prop
  required : List Requirement

namespace Specification

variable {Candidate : Type u} {Requirement : Type v}

def Satisfies (spec : Specification Candidate Requirement) (candidate : Candidate) : Prop :=
  ∀ requirement ∈ spec.required, spec.holds requirement candidate

/-- The same candidate index is shared by every supported requirement. -/
structure Evidence (spec : Specification Candidate Requirement) (candidate : Candidate) where
  supported : List Requirement
  verifies : ∀ requirement ∈ supported, spec.holds requirement candidate

def Evidence.remaining [DecidableEq Requirement]
    {spec : Specification Candidate Requirement} {candidate : Candidate}
    (evidence : spec.Evidence candidate) : List Requirement :=
  spec.required.filter (fun requirement => requirement ∉ evidence.supported)

/-- Completing the evidence list establishes the conjunction for this actual
candidate, not for a collection of independently chosen witnesses. -/
theorem Evidence.complete [DecidableEq Requirement]
    {spec : Specification Candidate Requirement} {candidate : Candidate}
    (evidence : spec.Evidence candidate) (complete : evidence.remaining = []) :
    spec.Satisfies candidate := by
  intro requirement required
  apply evidence.verifies requirement
  by_contra unsupported
  have member : requirement ∈ evidence.remaining := by
    simp only [Evidence.remaining, List.mem_filter, decide_eq_true_eq]
    exact ⟨required, unsupported⟩
  rw [complete] at member
  exact List.not_mem_nil member

/-- Requiring more properties narrows the candidate class, not the meaning
of the properties that were already present. -/
def extend (spec : Specification Candidate Requirement) (additional : List Requirement) :
    Specification Candidate Requirement :=
  { spec with required := spec.required ++ additional }

theorem satisfies_extend_iff (spec : Specification Candidate Requirement)
    (additional : List Requirement) (candidate : Candidate) :
    (spec.extend additional).Satisfies candidate ↔
      spec.Satisfies candidate ∧
        ∀ requirement ∈ additional, spec.holds requirement candidate := by
  constructor
  · intro satisfies
    exact ⟨fun requirement member => satisfies requirement (List.mem_append.mpr (.inl member)),
      fun requirement member => satisfies requirement (List.mem_append.mpr (.inr member))⟩
  · rintro ⟨original, added⟩ requirement member
    rcases List.mem_append.mp member with before | after
    · exact original requirement before
    · exact added requirement after

/-- A preference relation is restricted to independently stated requirements.
The preference alone does not supply a satisfaction proof or a selection. -/
def compare (spec : Specification Candidate Requirement) (preference : Criterion Candidate) :
    Criterion Candidate :=
  { preference with admissible := fun candidate =>
      spec.Satisfies candidate ∧ preference.admissible candidate }

theorem optimal_satisfies (spec : Specification Candidate Requirement)
    (preference : Criterion Candidate) {candidate : Candidate}
    (optimal : (spec.compare preference).IsOptimal candidate) : spec.Satisfies candidate :=
  optimal.1.1

/-- Necessity survives adding consistent requirements. The inhabitance premise
cannot be dropped: inconsistent extensions do not determine a design. -/
theorem determination_of_extension (spec : Specification Candidate Requirement)
    (additional : List Requirement) {property : Candidate → Prop}
    (determination : Determined spec.Satisfies property)
    (consistent : ∃ candidate, (spec.extend additional).Satisfies candidate) :
    Determined (spec.extend additional).Satisfies property := by
  refine ⟨consistent, ?_⟩
  intro candidate satisfies
  exact determination.entails candidate
    ((spec.satisfies_extend_iff additional candidate).mp satisfies).1

end Specification

/-! ## Specifications on parts of one assembly

Projection brings a component's requirements to the actual assembly which
contains it. Conjunction then keeps that same assembly index throughout.
These operations do not assert that arbitrary components are compatible:
interface agreement is a further requirement on the assembly, and must be
proved before it can appear in completed evidence.
-/

namespace Specification

universe u' v'

variable {Candidate : Type u} {Requirement : Type v}
  {Whole : Type u'} {OtherRequirement : Type v'}

/-- Read component requirements on the component actually selected by an
assembly. No independent existential witness is substituted for this part. -/
def pullback (spec : Specification Candidate Requirement)
    (project : Whole → Candidate) : Specification Whole Requirement where
  holds requirement whole := spec.holds requirement (project whole)
  required := spec.required

@[simp] theorem satisfies_pullback_iff
    (spec : Specification Candidate Requirement) (project : Whole → Candidate)
    (whole : Whole) :
    (spec.pullback project).Satisfies whole ↔ spec.Satisfies (project whole) := Iff.rfl

/-- Component evidence can be used only at its actual projected index. -/
def Evidence.pullback {spec : Specification Candidate Requirement}
    (project : Whole → Candidate) (whole : Whole)
    (evidence : spec.Evidence (project whole)) :
    (spec.pullback project).Evidence whole where
  supported := evidence.supported
  verifies := evidence.verifies

/-- Combine two requirement namespaces without merging their identities. -/
def conjoin (left : Specification Candidate Requirement)
    (right : Specification Candidate OtherRequirement) :
    Specification Candidate (Requirement ⊕ OtherRequirement) where
  holds
    | .inl requirement => left.holds requirement
    | .inr requirement => right.holds requirement
  required := left.required.map Sum.inl ++ right.required.map Sum.inr

theorem satisfies_conjoin_iff (left : Specification Candidate Requirement)
    (right : Specification Candidate OtherRequirement) (candidate : Candidate) :
    (left.conjoin right).Satisfies candidate ↔
      left.Satisfies candidate ∧ right.Satisfies candidate := by
  constructor
  · intro satisfies
    constructor
    · intro requirement required
      exact satisfies (.inl requirement) (by simp [conjoin, required])
    · intro requirement required
      exact satisfies (.inr requirement) (by simp [conjoin, required])
  · rintro ⟨leftHolds, rightHolds⟩ requirement required
    cases requirement with
    | inl requirement =>
        exact leftHolds requirement (by simpa [conjoin] using required)
    | inr requirement =>
        exact rightHolds requirement (by simpa [conjoin] using required)

/-- Both proofs concern the same candidate. This constructor cannot assemble
evidence for different candidates merely because both exist. -/
def Evidence.conjoin {left : Specification Candidate Requirement}
    {right : Specification Candidate OtherRequirement} {candidate : Candidate}
    (leftEvidence : left.Evidence candidate)
    (rightEvidence : right.Evidence candidate) :
    (left.conjoin right).Evidence candidate where
  supported := leftEvidence.supported.map Sum.inl ++ rightEvidence.supported.map Sum.inr
  verifies := by
    intro requirement supported
    cases requirement with
    | inl requirement =>
        exact leftEvidence.verifies requirement (by simpa using supported)
    | inr requirement =>
        exact rightEvidence.verifies requirement (by simpa using supported)

/-- Evidence growth does not change old predicates or the candidate. The
new requirement is added only with a proof at that very index. -/
def Evidence.add {spec : Specification Candidate Requirement} {candidate : Candidate}
    (evidence : spec.Evidence candidate) (requirement : Requirement)
    (proof : spec.holds requirement candidate) : spec.Evidence candidate where
  supported := requirement :: evidence.supported
  verifies := by
    intro claimed membership
    rcases List.mem_cons.mp membership with rfl | previous
    · exact proof
    · exact evidence.verifies claimed previous

theorem Evidence.remaining_add_subset [DecidableEq Requirement]
    {spec : Specification Candidate Requirement} {candidate : Candidate}
    (evidence : spec.Evidence candidate) (requirement : Requirement)
    (proof : spec.holds requirement candidate) :
    (evidence.add requirement proof).remaining ⊆ evidence.remaining := by
  intro claimed remaining
  simp only [Evidence.remaining, Evidence.add, List.mem_filter,
    decide_eq_true_eq, List.mem_cons, not_or] at remaining ⊢
  exact ⟨remaining.1, remaining.2.2⟩

end Specification

/-! ## Executable study: quotation, unused work, and incompatible requirements

These are two strategies of the finite countermodel, not competing complete
languages. The experiment isolates the inference that quotation forces a
particular evaluation strategy; it is not a global recommendation of by-name.
-/

namespace EvaluationStudy

open QuotationCountermodel

inductive Requirement where
  | quotation
  | skipUnused
  | executeUnused
  deriving DecidableEq, Repr

def holds : Requirement → Strategy → Prop
  | .quotation => QuotesWithoutExecution
  | .skipUnused => SkipsDiscardedTick
  | .executeUnused => fun strategy =>
      evaluate strategy (.discard .tick (.literal 7)) = (.number 7, 1)

def quotationSpec : Specification Strategy Requirement :=
  ⟨holds, [.quotation]⟩

def demandSpec : Specification Strategy Requirement :=
  quotationSpec.extend [.skipUnused]

def conflictingSpec : Specification Strategy Requirement :=
  demandSpec.extend [.executeUnused]

def eagerQuotationEvidence : quotationSpec.Evidence .eager where
  supported := [.quotation]
  verifies := by
    intro requirement membership
    have equal : requirement = .quotation := by simpa using membership
    subst requirement
    exact eager_quotes_without_execution

def demandEvidence : demandSpec.Evidence .byName where
  supported := [.quotation, .skipUnused]
  verifies := by
    intro requirement membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl
    · exact byName_quotes_without_execution
    · exact byName_skips_discarded_tick

theorem demandEvidence_complete : demandSpec.Satisfies .byName :=
  demandEvidence.complete (by decide)

theorem quotation_admits_both :
    quotationSpec.Satisfies .eager ∧ quotationSpec.Satisfies .byName := by
  refine ⟨eagerQuotationEvidence.complete (by decide), ?_⟩
  exact ((quotationSpec.satisfies_extend_iff [.skipUnused] .byName).mp
    demandEvidence_complete).1

/-- The new observation, not the old quotation requirement, excludes eagerness. -/
theorem extra_requirement_excludes_eager : ¬ demandSpec.Satisfies .eager := by
  intro satisfies
  have skip := satisfies .skipUnused (by simp [demandSpec, quotationSpec, Specification.extend])
  change SkipsDiscardedTick .eager at skip
  simp [SkipsDiscardedTick, evaluate] at skip

theorem demand_determines_byName_in_this_class :
    Determined demandSpec.Satisfies (fun strategy => strategy = .byName) := by
  refine ⟨⟨.byName, demandEvidence_complete⟩, ?_⟩
  intro strategy satisfies
  cases strategy with
  | eager => exact (extra_requirement_excludes_eager satisfies).elim
  | byName => rfl

theorem each_requirement_has_a_witness :
    ∀ requirement ∈ conflictingSpec.required, ∃ strategy, holds requirement strategy := by
  intro requirement _
  cases requirement with
  | quotation => exact ⟨.eager, eager_quotes_without_execution⟩
  | skipUnused => exact ⟨.byName, byName_skips_discarded_tick⟩
  | executeUnused => exact ⟨.eager, eager_executes_discarded_tick⟩

/-- Componentwise existence does not assemble a model: the last two demands
disagree on the effect count of the very same closed workload. -/
theorem no_joint_witness : ¬ ∃ strategy, conflictingSpec.Satisfies strategy := by
  rintro ⟨strategy, satisfies⟩
  have skip := satisfies .skipUnused
    (by simp [conflictingSpec, demandSpec, quotationSpec, Specification.extend])
  have execute := satisfies .executeUnused
    (by simp [conflictingSpec, demandSpec, quotationSpec, Specification.extend])
  have impossible : (Value.number 7, 0) = (.number 7, 1) := skip.symm.trans execute
  cases impossible

theorem incompatible_extension_is_not_determined :
    ¬ Determined conflictingSpec.Satisfies (fun strategy => strategy = .byName) :=
  incompatible_requirements_determine_nothing no_joint_witness

/-- Conjunction retains the reusable quotation requirement and the demand
requirement on the same concrete evaluator. -/
def quotationAndDemandEvidence :
    (quotationSpec.conjoin demandSpec).Evidence .byName :=
  (show quotationSpec.Evidence .byName from
    { supported := [.quotation]
      verifies := by
        intro requirement membership
        have equal : requirement = .quotation := by simpa using membership
        subst requirement
        exact byName_quotes_without_execution }).conjoin demandEvidence

theorem quotationAndDemand_complete :
    (quotationSpec.conjoin demandSpec).Satisfies .byName :=
  quotationAndDemandEvidence.complete (by decide)

/-- The componentwise-witness fallacy is still impossible after introducing
assembly conjunction. A good quotation component cannot repair contradictory
effect requirements on the same evaluator. -/
theorem conjoining_does_not_repair_incompatibility :
    ¬ ∃ strategy, (quotationSpec.conjoin conflictingSpec).Satisfies strategy := by
  rintro ⟨strategy, satisfies⟩
  exact no_joint_witness ⟨strategy,
    ((quotationSpec.satisfies_conjoin_iff conflictingSpec strategy).mp satisfies).2⟩

end EvaluationStudy

#print axioms Specification.Evidence.complete
#print axioms Specification.satisfies_conjoin_iff
#print axioms Specification.Evidence.remaining_add_subset
#print axioms EvaluationStudy.quotationAndDemand_complete
#print axioms EvaluationStudy.conjoining_does_not_repair_incompatibility
#print axioms EvaluationStudy.demand_determines_byName_in_this_class
#print axioms EvaluationStudy.no_joint_witness

end Mettapedia.TypeTheory.DesignStudy
