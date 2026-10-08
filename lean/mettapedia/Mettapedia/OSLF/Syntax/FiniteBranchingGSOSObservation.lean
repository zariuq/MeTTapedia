import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSPresentation

/-!
# The finite observation bound of an authored GSOS presentation

For one operator and output action, the finite union of all positive and
negative premise addresses determines its complete target set. Original
argument values are retained separately. This theorem permits arbitrary
action carriers; it is the boundary needed to distinguish finite-premise
presentations from natural laws that test infinitely many input actions.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.Premises

open _root_.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)
open Classical

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u}

def Pattern.observed {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator) : Finset (Address (Actions := Actions) operator) :=
  Finset.univ.image pattern.address ∪ pattern.negative

theorem Pattern.positive_observed {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator) (occurrence : pattern.Occurrence) :
    pattern.address occurrence ∈ pattern.observed :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨occurrence, Finset.mem_univ _, rfl⟩)

theorem Pattern.negative_observed {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator) {address : Address (Actions := Actions) operator}
    (member : address ∈ pattern.negative) : address ∈ pattern.observed :=
  Finset.mem_union_right _ member

theorem matches_of_observation {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator) {X : S.Families}
    (first second : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (sources : ∀ position, (first position).1 = (second position).1)
    (observations : ∀ address ∈ pattern.observed,
      (first address.1).2 address.2 = (second address.1).2 address.2)
    (input : Input pattern X) : Matches pattern first input ↔ Matches pattern second input := by
  have sameSources : (∀ position, input.originals position = (first position).1) ↔
      ∀ position, input.originals position = (second position).1 := by
    constructor <;> intro held position
    · exact (held position).trans (sources position)
    · exact (held position).trans (sources position).symm
  have samePositive :
      (∀ occurrence, input.derivatives occurrence ∈ (first (pattern.address occurrence).1).2
        (pattern.address occurrence).2) ↔
      ∀ occurrence, input.derivatives occurrence ∈ (second (pattern.address occurrence).1).2
        (pattern.address occurrence).2 := by
    constructor <;> intro held occurrence
    · rw [← observations _ (pattern.positive_observed occurrence)]
      exact held occurrence
    · rw [observations _ (pattern.positive_observed occurrence)]
      exact held occurrence
  have sameNegative :
      (∀ address ∈ pattern.negative, (first address.1).2 address.2 = ∅) ↔
      ∀ address ∈ pattern.negative, (second address.1).2 address.2 = ∅ := by
    constructor <;> intro held address member
    · rw [← observations _ (pattern.negative_observed member)]
      exact held address member
    · rw [observations _ (pattern.negative_observed member)]
      exact held address member
  exact and_congr sameSources (and_congr samePositive sameNegative)

def Presentation.observed (presentation : Presentation S Actions) {sort : S.Srt}
    (operator : S.Operator sort) (action : Actions sort) : Finset (Address (Actions := Actions) operator) :=
  (presentation sort operator action).biUnion (fun rule => rule.pattern.observed)

theorem Presentation.targets_of_observation (presentation : Presentation S Actions)
    {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort) {X : S.Families}
    (first second : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (sources : ∀ position, (first position).1 = (second position).1)
    (observations : ∀ address ∈ presentation.observed operator action,
      (first address.1).2 address.2 = (second address.1).2 address.2) :
    Presentation.targets presentation operator first action =
      Presentation.targets presentation operator second action := by
  apply Finset.ext
  intro target
  rw [Presentation.mem_targets, Presentation.mem_targets]
  constructor <;> rintro ⟨rule, member, input, matching, same⟩
  · refine ⟨rule, member, input, ?_, same⟩
    apply (matches_of_observation rule.pattern first second sources ?_ input).mp matching
    intro address held
    exact observations address (Finset.mem_biUnion.mpr ⟨rule, member, held⟩)
  · refine ⟨rule, member, input, ?_, same⟩
    apply (matches_of_observation rule.pattern first second sources ?_ input).mpr matching
    intro address held
    exact observations address (Finset.mem_biUnion.mpr ⟨rule, member, held⟩)

/-- Uniform finite observation is a semantic locality condition on actual
input behaviors, not a supplied presentation or reconstruction witness. -/
def UniformFiniteObservation (law : Law S Actions) : Prop :=
  ∀ sort (operator : S.Operator sort) action,
    ∃ observed : Finset (Address (Actions := Actions) operator),
      ∀ (X : S.Families) (first second : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator),
        (∀ position, (first position).1 = (second position).1) →
        (∀ address ∈ observed, (first address.1).2 address.2 = (second address.1).2 address.2) →
        law.app X PUnit.unit sort ⟨operator, first⟩ action =
          law.app X PUnit.unit sort ⟨operator, second⟩ action

theorem Presentation.toLaw_uniform (presentation : Presentation S Actions) :
    UniformFiniteObservation (Presentation.toLaw presentation) := by
  intro sort operator action
  refine ⟨presentation.observed operator action, ?_⟩
  intro X first second sources observations
  exact presentation.targets_of_observation operator action first second sources observations

theorem Presentation.uniform_of_denotes (presentation : Presentation S Actions) (law : Law S Actions)
    (denotes : Presentation.Denotes presentation law) : UniformFiniteObservation law := by
  rw [presentation.law_unique law denotes]
  exact presentation.toLaw_uniform

end Mettapedia.OSLF.FiniteBranching.Premises
