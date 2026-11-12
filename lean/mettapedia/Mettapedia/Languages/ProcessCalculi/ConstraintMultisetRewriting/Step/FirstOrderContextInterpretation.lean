import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderNativeRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderIndependence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ContextualTensorInterpretation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceFootprints

/-!
# The first-order consumer of shared contextual execution

The canonical one-frame placement uses the existing configuration tensor.
Its exact permission test asks freshness, joint consistency and the actual
guards and census queries. A separate consumption condition is precisely the
frame law needed to leave the other component unchanged. No guard blindness
or disjointness of shared reads is imposed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.FirstOrderNativeRuns

open AnnotatedRuns (Firing firstOrder firstOrderTransport)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

def ContextChecks (left right : Configuration T O) (f : Firing T S O) : Prop :=
  Disjoint f.selection.made.toFinset right.present ∧
    A.Consistent (f.selection.problem label f.rule (AnnotatedRuns.tensor left right)) ∧
    (∀ check ∈ f.rule.checks, ∀ σ : S,
      A.Models σ (f.selection.problem label f.rule (AnnotatedRuns.tensor left right)) →
        check.Holds A σ label (left.present ∪ right.present)) ∧
    ∀ query ∈ f.queries, ∀ σ : S,
      A.Models σ (f.selection.problem label f.rule (AnnotatedRuns.tensor left right)) →
        (query.atSolution σ).Holds label (left.present ∪ right.present)

theorem valid_tensor_iff {left right : Configuration T O} (f : Firing T S O)
    (allowed : f.Valid A label left) :
    f.Valid A label (AnnotatedRuns.tensor left right) ↔ ContextChecks A label left right f := by
  constructor
  · intro native
    exact ⟨Finset.disjoint_of_subset_right Finset.subset_union_right native.firing.occurrences.fresh,
      native.firing.consistent, native.firing.checks, native.observations⟩
  · rintro ⟨fresh, consistent, guards, queries⟩
    exact ⟨⟨allowed.firing.take_distinct, allowed.firing.output_distinct, allowed.firing.take_length,
      allowed.firing.read_length, allowed.firing.outputs,
      allowed.firing.occurrences.frame_of_positive rfl fresh, consistent, guards⟩, queries⟩

abbrev contextualRunInterpretation : ContextualRunInterpretation (firstOrderTransport A label) where
  Place _ _ := PUnit.{1}
  pair := fun {left right} _ => nativePair A label left right
  candidate _ f := f
  advance _ _ _ := PUnit.unit
  domain := fun {_ right} _ f => Disjoint f.selection.taken.toFinset right.present
  check := fun {left right} _ f => ContextChecks A label left right f
  admission := fun _ f allowed => valid_tensor_iff A label f allowed
  resultIso := fun _ _ _ framed _ => ⟨AnnotatedRuns.tensor_result_left A label framed⟩

theorem framing_domain_iff_result_resources {left right : Configuration T O} (f : Firing T S O)
    (allowed : f.Valid A label left) :
    (contextualRunInterpretation A label).domain (left := left) (right := right) PUnit.unit f ↔
      (f.result label (AnnotatedRuns.tensor left right)).present =
        (AnnotatedRuns.tensor (f.result label left) right).present := by
  change Disjoint f.selection.taken.toFinset right.present ↔
    MeTTaCalculus.OccurrenceCommits.fire (left.present ∪ right.present) (f.selection.commit (T := T)) =
      MeTTaCalculus.OccurrenceCommits.fire left.present (f.selection.commit (T := T)) ∪ right.present
  exact (Coexistence.Footprints.fire_preserves_context_iff label left.present right.present
    (f.selection.commit (T := T)) allowed.firing.occurrences).symm

theorem framing_domain_iff_native_iso {left right : Configuration T O} (f : Firing T S O)
    (allowed : f.Valid A label left) :
    (contextualRunInterpretation A label).domain (left := left) (right := right) PUnit.unit f ↔
      (firstOrderTransport A label).Same (f.result label (AnnotatedRuns.tensor left right))
        (AnnotatedRuns.tensor (f.result label left) right) := by
  constructor
  · intro framed
    exact ⟨⟨AnnotatedRuns.tensor_result_left A label framed⟩⟩
  · rintro ⟨iso⟩
    exact (framing_domain_iff_result_resources A label f allowed).mpr iso.down.2

abbrev contextualFlip : (contextualRunInterpretation A label).Flip where
  swap _ := PUnit.unit
  stateIso := fun {left right} _ => ⟨AnnotatedRuns.tensor_comm A right left⟩

theorem contextualFlip_lawful : (contextualFlip A label).Lawful where
  swap_swap place := Subsingleton.elim _ place
  left_natural _ := by
    intro term
    change (Frames.ofSubstitution A).E
      ((Frames.ofSubstitution A).act
        ((Frames.ofSubstitution A).comp ((Frames.ofSubstitution A).id PUnit.unit) A.identity) term)
      ((Frames.ofSubstitution A).act A.identity term)
    rw [(Frames.ofSubstitution A).act_comp, (Frames.ofSubstitution A).act_id]
    exact ((Frames.ofSubstitution A).equivalence _).refl _
  right_natural _ := by
    intro term
    change (Frames.ofSubstitution A).E
      ((Frames.ofSubstitution A).act
        ((Frames.ofSubstitution A).comp ((Frames.ofSubstitution A).id PUnit.unit) A.identity) term)
      ((Frames.ofSubstitution A).act A.identity term)
    rw [(Frames.ofSubstitution A).act_comp, (Frames.ofSubstitution A).act_id]
    exact ((Frames.ofSubstitution A).equivalence _).refl _

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.FirstOrderNativeRuns
