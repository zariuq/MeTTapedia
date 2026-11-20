import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.TaggedAssignments
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeResidualExample

/-!
# Contextual assignments that change frames and preserve distinct captures

The first inclusion adds an optional fresh name. The second adds another name
and retains both original captures. Their composite is the actual contextual
composite, at the second target frame, rather than a common collapsed value.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.TaggedAssignmentsControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open NativeResidualExample (tiny)
open TaggedAssignments

def source : Object tiny := (0,⟨Bool,fun _ => ([],())⟩)
def middle : Object tiny := (1,⟨Option Bool,fun _ => ([],())⟩)
def target : Object tiny := (2,⟨Unit ⊕ Bool,fun _ => ([],())⟩)

def firstInclusion : Assignment source.2.arity middle.2.arity :=
  fun name => generator middle.2.arity (some name)

def secondInclusion : Assignment middle.2.arity target.2.arity
  | none => generator target.2.arity (.inl ())
  | some name => generator target.2.arity (.inr name)

noncomputable def first : Substitution tiny := single source middle firstInclusion
noncomputable def second : Substitution tiny := single middle target secondInclusion

theorem composite_target : (compose tiny second first source).1 = target := by
  change (second (first source).1).1 = target
  rw [show first source = ⟨middle,firstInclusion⟩ from single_at source middle firstInclusion]
  exact congrArg Sigma.fst (single_at middle target secondInclusion)

theorem composite_observation (name : Bool) :
    apply tiny (compose tiny second first) (pack source (observe (generator source.2.arity name))) =
      pack target (observe (generator target.2.arity (.inr name))) := by
  rw [apply_compose]
  change apply tiny second
    (pack (first source).1 (instantiateObservation (first source).2 (observe (generator source.2.arity name)))) = _
  rw [show first source = ⟨middle,firstInclusion⟩ from single_at source middle firstInclusion]
  change pack (second middle).1
    (observe (instantiate (second middle).2 (instantiate firstInclusion (generator source.2.arity name)))) = _
  rw [show instantiate firstInclusion (generator source.2.arity name) =
    generator middle.2.arity (some name) from instantiate_generator firstInclusion name]
  rw [show second middle = ⟨target,secondInclusion⟩ from single_at middle target secondInclusion]
  change pack target (observe (instantiate secondInclusion (generator middle.2.arity (some name)))) = _
  rw [show instantiate secondInclusion (generator middle.2.arity (some name)) =
    generator target.2.arity (.inr name) from instantiate_generator secondInclusion (some name)]
  rfl

theorem captures_remain_distinct :
    apply tiny (compose tiny second first) (pack source (observe (generator source.2.arity false))) ≠
      apply tiny (compose tiny second first) (pack source (observe (generator source.2.arity true))) := by
  rw [composite_observation,composite_observation]
  intro equal
  have same := observe_injective (pack_injective target equal)
  cases same

theorem source_captures_already_distinct :
    pack source (observe (generator source.2.arity false)) ≠
      pack source (observe (generator source.2.arity true)) := by
  intro equal
  have same := observe_injective (pack_injective source equal)
  cases same

theorem distinct_source_tags : source ≠ middle := by
  intro equal
  have tags := congrArg Prod.fst equal
  cases tags

theorem first_keeps_other_source : first middle = identity tiny middle :=
  single_other source middle middle firstInclusion distinct_source_tags.symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.TaggedAssignmentsControls
