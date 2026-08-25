import Mettapedia.Cybernetics.ObservedVariety

/-!
# Constraint, static variety, and dynamic variation

A system is represented first by its admissible fibre, not by a scalar count.
Dynamic variation is a proof-relevant relation, so distinct histories between
the same endpoints remain distinct.  Cardinality and entropy can therefore be
added downstream as readouts without becoming the definition of variety.

The final section formalizes the three independent yes/no axes used in Francis
Heylighen's 1995 classification: constraint, static variety, and dynamic
variation.  The eight cases carry the judgments that justify them, and the
classification theorem proves that exactly one case applies.  Names such as
`metasystem` and `supersystem` require the additional second-order structure in
`MetasystemTransition`; they are not inferred from a bit pattern alone.

Reference:

- F. Heylighen, *(Meta)Systems as Constraints on Variation* (1995).
- V. Turchin, *The Phenomenon of Science* (1977), for the metasystem-transition
  programme distinguished and refined by Heylighen.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics

universe uState uView uSource uTarget uWitness uPart uConfiguration

/-! ## Constraint fibres -/

/-- A constraint selects the admissible states of a system. -/
abbrev Constraint (State : Type uState) := Set State

namespace Constraint

variable {State : Type uState}

/-- The informative variety admitted by a constraint. -/
abbrev Fibre (constraint : Constraint State) : Type uState := ↥constraint

/-- `stronger` refines `weaker` when every strongly admissible state is also
weakly admissible. -/
def Refines (stronger weaker : Constraint State) : Prop :=
  stronger ⊆ weaker

/-- Refinement embeds the stronger admissible fibre into the weaker one. -/
def fibreEmbedding {stronger weaker : Constraint State}
    (refines : Refines stronger weaker) :
    Fibre stronger ↪ Fibre weaker where
  toFun state := ⟨state.1, refines state.2⟩
  inj' := by
    intro left right equal
    exact Subtype.ext
      (congrArg (fun state : Fibre weaker => state.1) equal)

/-- Restrict an observer to the states admitted by a constraint. -/
def restrictObserver {View : Type uView} (constraint : Constraint State)
    (observer : Observer State View) : Observer (Fibre constraint) View where
  observe state := observer.observe state.1

/-- Exact equality of constraints preserves their informative fibres. -/
def fibreEquivOfEq {left right : Constraint State} (equal : left = right) :
    Fibre left ≃ Fibre right := by
  subst equal
  exact Equiv.refl _

end Constraint

/-! ## Proof-relevant dynamic variation -/

namespace Variation

variable {Source : Type uSource} {Target : Type uTarget}

/-- Every source has at least one witnessed successor. -/
def Total (relation : Source → Target → Type uWitness) : Prop :=
  ∀ source, Nonempty (Σ target, relation source target)

/-- All witnessed successors of a source have the same endpoint.  This does
not erase the potentially different witnesses reaching that endpoint. -/
def EndpointDeterministic
    (relation : Source → Target → Type uWitness) : Prop :=
  ∀ source first second,
    Nonempty (relation source first) →
    Nonempty (relation source second) →
    first = second

/-- The four exhaustive totality/endpoint-determinism regimes of a
proof-relevant relation. -/
inductive Regime (relation : Source → Target → Type uWitness) : Type where
  | totalDeterministic : Total relation → EndpointDeterministic relation →
      Regime relation
  | totalBranching : Total relation → ¬ EndpointDeterministic relation →
      Regime relation
  | partialDeterministic : ¬ Total relation → EndpointDeterministic relation →
      Regime relation
  | partialBranching : ¬ Total relation → ¬ EndpointDeterministic relation →
      Regime relation

/-- Every proof-relevant relation inhabits exactly one operational regime. -/
noncomputable def classify
    (relation : Source → Target → Type uWitness) : Regime relation := by
  classical
  by_cases total : Total relation
  · by_cases deterministic : EndpointDeterministic relation
    · exact .totalDeterministic total deterministic
    · exact .totalBranching total deterministic
  · by_cases deterministic : EndpointDeterministic relation
    · exact .partialDeterministic total deterministic
    · exact .partialBranching total deterministic

/-- The total/partial axis cannot classify one relation both ways. -/
theorem not_total_and_partial
    (relation : Source → Target → Type uWitness) :
    ¬ (Total relation ∧ ¬ Total relation) := by
  tauto

/-- The deterministic/branching axis cannot classify one relation both ways. -/
theorem not_deterministic_and_branching
    (relation : Source → Target → Type uWitness) :
    ¬ (EndpointDeterministic relation ∧
      ¬ EndpointDeterministic relation) := by
  tauto

end Variation

/-! ## The three Heylighen axes -/

/-- A selected domain for the 1995 three-axis classification.  `admissible`
constrains part/configuration pairs; `Change` retains witnessed transitions
between configurations. -/
structure Organization
    (Part : Type uPart) (Configuration : Type uConfiguration) where
  admissible : Set (Part × Configuration)
  Change : Configuration → Configuration → Type uWitness

namespace Organization

variable {Part : Type uPart} {Configuration : Type uConfiguration}
  (organization : Organization Part Configuration)

/-- Some candidate part/configuration is excluded. -/
def HasConstraint : Prop :=
  ∃ part configuration, (part, configuration) ∉ organization.admissible

/-- Two distinct parts are jointly admissible in one configuration. -/
def HasStaticVariety : Prop :=
  ∃ first second configuration,
    first ≠ second ∧
    (first, configuration) ∈ organization.admissible ∧
    (second, configuration) ∈ organization.admissible

/-- A witnessed transition reaches a distinct configuration. -/
def HasDynamicVariation : Prop :=
  ∃ first second,
    first ≠ second ∧ Nonempty (organization.Change first second)

/-- The eight exhaustive, proof-bearing cases of the constraint × static
variety × dynamic variation classification. -/
inductive Classification : Type (max uPart uConfiguration uWitness) where
  | constrainedDynamicStatic :
      organization.HasConstraint →
      organization.HasDynamicVariation →
      organization.HasStaticVariety → Classification
  | unconstrainedDynamicStatic :
      ¬ organization.HasConstraint →
      organization.HasDynamicVariation →
      organization.HasStaticVariety → Classification
  | constrainedDynamicUnitary :
      organization.HasConstraint →
      organization.HasDynamicVariation →
      ¬ organization.HasStaticVariety → Classification
  | unconstrainedDynamicUnitary :
      ¬ organization.HasConstraint →
      organization.HasDynamicVariation →
      ¬ organization.HasStaticVariety → Classification
  | constrainedRigidStatic :
      organization.HasConstraint →
      ¬ organization.HasDynamicVariation →
      organization.HasStaticVariety → Classification
  | unconstrainedRigidStatic :
      ¬ organization.HasConstraint →
      ¬ organization.HasDynamicVariation →
      organization.HasStaticVariety → Classification
  | constrainedRigidUnitary :
      organization.HasConstraint →
      ¬ organization.HasDynamicVariation →
      ¬ organization.HasStaticVariety → Classification
  | null :
      ¬ organization.HasConstraint →
      ¬ organization.HasDynamicVariation →
      ¬ organization.HasStaticVariety → Classification

/-- Every organization in the selected domain has one of the eight profiles. -/
noncomputable def classify : organization.Classification := by
  classical
  by_cases constraint : organization.HasConstraint
  · by_cases dynamic : organization.HasDynamicVariation
    · by_cases static : organization.HasStaticVariety
      · exact .constrainedDynamicStatic constraint dynamic static
      · exact .constrainedDynamicUnitary constraint dynamic static
    · by_cases static : organization.HasStaticVariety
      · exact .constrainedRigidStatic constraint dynamic static
      · exact .constrainedRigidUnitary constraint dynamic static
  · by_cases dynamic : organization.HasDynamicVariation
    · by_cases static : organization.HasStaticVariety
      · exact .unconstrainedDynamicStatic constraint dynamic static
      · exact .unconstrainedDynamicUnitary constraint dynamic static
    · by_cases static : organization.HasStaticVariety
      · exact .unconstrainedRigidStatic constraint dynamic static
      · exact .null constraint dynamic static

/-- The constraint axis is non-confusing. -/
theorem not_constrained_and_unconstrained :
    ¬ (organization.HasConstraint ∧ ¬ organization.HasConstraint) := by
  tauto

/-- The static-variety axis is non-confusing. -/
theorem not_static_and_unitary :
    ¬ (organization.HasStaticVariety ∧
      ¬ organization.HasStaticVariety) := by
  tauto

/-- The dynamic-variation axis is non-confusing. -/
theorem not_dynamic_and_rigid :
    ¬ (organization.HasDynamicVariation ∧
      ¬ organization.HasDynamicVariation) := by
  tauto

end Organization

/-! ## Positive and negative controls -/

namespace ConstrainedVarietyCanary

inductive Toggle : Bool → Bool → Type where
  | advance : Toggle false true

/-- A genuinely constrained organization with static parts and a witnessed
configuration change. -/
def candidate : Organization Bool Bool where
  admissible := {(part, configuration) | ¬ (part = true ∧ configuration = false)}
  Change := Toggle

theorem candidate_hasConstraint : candidate.HasConstraint := by
  exact ⟨true, false, by simp [candidate]⟩

theorem candidate_hasStaticVariety : candidate.HasStaticVariety := by
  exact ⟨false, true, true, by decide, by simp [candidate], by simp [candidate]⟩

theorem candidate_hasDynamicVariation : candidate.HasDynamicVariation := by
  exact ⟨false, true, by decide, ⟨Toggle.advance⟩⟩

def candidateClassification : candidate.Classification :=
  .constrainedDynamicStatic candidate_hasConstraint
    candidate_hasDynamicVariation candidate_hasStaticVariety

/-- A one-state, one-part unconstrained organization with no transitions. -/
def nullOrganization : Organization Unit Unit where
  admissible := Set.univ
  Change := fun _ _ => Empty

theorem null_hasNoConstraint : ¬ nullOrganization.HasConstraint := by
  simp [Organization.HasConstraint, nullOrganization]

theorem null_hasNoStaticVariety : ¬ nullOrganization.HasStaticVariety := by
  simp [Organization.HasStaticVariety]

theorem null_hasNoDynamicVariation :
    ¬ nullOrganization.HasDynamicVariation := by
  simp [Organization.HasDynamicVariation, nullOrganization]

def nullClassification : nullOrganization.Classification :=
  .null null_hasNoConstraint null_hasNoDynamicVariation
    null_hasNoStaticVariety

end ConstrainedVarietyCanary

end Mettapedia.Cybernetics

#print axioms Mettapedia.Cybernetics.Variation.not_total_and_partial
#print axioms Mettapedia.Cybernetics.Organization.not_constrained_and_unconstrained
#print axioms Mettapedia.Cybernetics.ConstrainedVarietyCanary.candidateClassification
