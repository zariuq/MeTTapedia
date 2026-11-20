import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.SharedProjection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.StepSpan

/-!
# Conservative executions from the shared-row image

The exact firing correspondence induces the existing functional-bisimulation
contract. Consequently every finite path starting at an embedded shared state
lifts back to the original construction. No transition escapes that image.
This is not a predecessor-observation theorem for arbitrary schematic states
outside the image, nor an identification of schematic and shared variables.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Shared

open Interface (Frames)
open LogicOverTheStep.StepSpan (Succ)
open FragmentsOfTheStep.TransitionMaps

universe uO uT uH uE uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom} {P : RuleSyntax.Program Tm}

theorem functionalBisimulation (X : Frames Tm Hom) :
    FunctionalBisimulation (Succ (RuleSyntax.step X O E P).toStep)
      (Succ (singleFiring X O E (program P)).toStep) (State.ofShared (Tm := Tm) (O := O)) := by
  constructor
  ·
    rintro s _ ⟨f, admitted, rfl⟩
    exact ⟨lift s f, (admits_iff X s f).mpr admitted, result_eq X s f⟩
  ·
    rintro s _ ⟨f, admitted, rfl⟩
    exact ⟨(forget s f).result X s,
      ⟨forget s f, (forget_admits_iff X s f).mpr admitted, rfl⟩, forget_result X s f⟩

theorem reachable_iff (X : Frames Tm Hom) (s : RuleSyntax.State Tm O) (after : State Tm O) :
    Relation.ReflTransGen (Succ (singleFiring X O E (program P)).toStep) (State.ofShared s) after ↔
      ∃ original : RuleSyntax.State Tm O,
        Relation.ReflTransGen (Succ (RuleSyntax.step X O E P).toStep) s original ∧
          State.ofShared original = after := by
  constructor
  · intro path
    exact Zag.path (functionalBisimulation X).zag path s rfl
  · rintro ⟨original, path, same⟩
    rw [← same]
    exact Zig.path (functionalBisimulation X).zig path

theorem reachable_images_iff (X : Frames Tm Hom) (s after : RuleSyntax.State Tm O) :
    Relation.ReflTransGen (Succ (singleFiring X O E (program P)).toStep)
        (State.ofShared s) (State.ofShared after) ↔
      Relation.ReflTransGen (Succ (RuleSyntax.step X O E P).toStep) s after := by
  rw [reachable_iff]
  constructor
  · rintro ⟨original, path, same⟩
    exact state_injective same ▸ path
  · intro path
    exact ⟨after, path, rfl⟩

theorem terminal_iff (X : Frames Tm Hom) (s : RuleSyntax.State Tm O) :
    (∀ after, ¬ Succ (singleFiring X O E (program P)).toStep (State.ofShared s) after) ↔
      ∀ after, ¬ Succ (RuleSyntax.step X O E P).toStep s after := by
  constructor
  · intro terminal after step
    exact terminal _ ((functionalBisimulation X).zig step)
  · intro terminal after step
    obtain ⟨original, lifted, _⟩ := (functionalBisimulation X).zag step
    exact terminal original lifted

theorem future_observation_iff (X : Frames Tm Hom) (s : RuleSyntax.State Tm O)
    (observes : State Tm O → Prop) :
    (∃ after, Succ (singleFiring X O E (program P)).toStep (State.ofShared s) after ∧ observes after) ↔
      ∃ original, Succ (RuleSyntax.step X O E P).toStep s original ∧ observes (State.ofShared original) := by
  constructor
  · rintro ⟨after, step, seen⟩
    obtain ⟨original, lifted, same⟩ := (functionalBisimulation X).zag step
    exact ⟨original, lifted, same ▸ seen⟩
  · rintro ⟨original, step, seen⟩
    exact ⟨State.ofShared original, (functionalBisimulation X).zig step, seen⟩

#print axioms functionalBisimulation
#print axioms reachable_iff
#print axioms reachable_images_iff
#print axioms terminal_iff
#print axioms future_observation_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Shared
