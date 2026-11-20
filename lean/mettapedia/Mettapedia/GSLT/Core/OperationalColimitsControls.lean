import Mettapedia.GSLT.Core.OperationalColimits
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# An operational coequalizer inherits a step at an identified inert term

Two arrows send a unit term to a ready state and an inert state. Their
coequalizer identifies those images, which then share the ready state's
reduction. The target stage's inert state is terminal before this quotient.

This is a nonfiltered control of the constructed forward colimit. It also
shows why reflection of normality, covered translations and behavioral
colimits cannot be inferred from the forward construction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational.OperationalColimits.Controls

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

inductive State where
  | ready
  | inert
  | done
  deriving DecidableEq

def source : OperationalTheory :=
  ⟨equalityGSLT Unit (fun _ _ => False)⟩

def target : OperationalTheory :=
  ⟨equalityGSLT State (fun left right => left = .ready ∧ right = .done)⟩

def readyMap : source ⟶ target where
  mapTerm := fun _ => .ready
  mapEquiv := by intro left right equivalent; rfl
  mapStep := by intro left right impossible; cases impossible

def inertMap : source ⟶ target where
  mapTerm := fun _ => .inert
  mapEquiv := by intro left right equivalent; rfl
  mapStep := by intro left right impossible; cases impossible

def diagram : WalkingParallelPair ⥤ OperationalTheory := parallelPair readyMap inertMap

/-- Both images of the unit term are identified by the actual transport
quotient, even though they were distinct target-stage terms. -/
theorem ready_and_inert_identified :
    inject diagram .one State.inert = inject diagram .one State.ready := by
  have first := inject_along diagram WalkingParallelPairHom.left ()
  have second := inject_along diagram WalkingParallelPairHom.right ()
  exact second.symm.trans first

/-- The stage's ready step survives and is shared by the identified inert
image; the equational saturation is essential to its operational meaning. -/
theorem inert_image_steps :
    (theory diagram).Step (inject diagram .one State.inert)
      (inject diagram .one State.done) := by
  have stageStep : target.theory.Step State.ready State.done := ⟨rfl, rfl⟩
  have image := (inclusion diagram .one).mapStep stageStep
  change (theory diagram).Step (inject diagram .one State.ready)
    (inject diagram .one State.done) at image
  rw [← ready_and_inert_identified] at image
  exact image

/-- The source of that ambient step had no reduction in the target stage. -/
theorem inert_stage_is_normal : target.theory.IsNormalForm State.inert := by
  rintro ⟨next, step⟩
  cases step.1

theorem inert_image_is_not_normal :
    ¬ (theory diagram).IsNormalForm (inject diagram .one State.inert) := by
  intro normal
  exact normal ⟨inject diagram .one State.done, inert_image_steps⟩

#print axioms ready_and_inert_identified
#print axioms inert_image_steps
#print axioms inert_stage_is_normal
#print axioms inert_image_is_not_normal

end Mettapedia.GSLT.IndexedOperational.OperationalColimits.Controls
