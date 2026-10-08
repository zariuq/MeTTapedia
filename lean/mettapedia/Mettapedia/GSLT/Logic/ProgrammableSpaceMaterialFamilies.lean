import Mettapedia.GSLT.Logic.ProgrammableSpaceMaterial
import Mettapedia.GSLT.Logic.ConstructiveObservedMaterialFamilies

/-!
# Actual dependent continuation families for programmable spaces

The already constructed native/material family machinery is instantiated on
the real growing execution coalgebra. An actual source action constructs an
element of its continuation fibre, with a material member and inverse decoder.
Conversely every such fibre element has a matching source action up to the
declared observed class. No source occurrence is selected from that existence
claim. Empty unrequested spaces have an empty continuation fibre.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProgrammableSpaceMaterialFamilies

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ProgrammableSpace
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open PowerClassPresheafDescent.Controls
open ProgrammableSpaceMaterial

variable {Atom Tag Reading : Type} (languages : Tag → Language Atom)
  (policies : (tag : Tag) → Policy (languages tag))
  (read : Reading → Space languages policies → Prop) (coding : ArgumentCoding Reading)

abbrev classes := ConstructiveObservedMaterialInterpretation.observedClasses
  worlds arrows (dynamics languages policies) (observes languages policies read) coding

abbrev classOf := ConstructiveObservedMaterialInterpretation.observedProjection
  worlds arrows (dynamics languages policies) (observes languages policies read) coding

abbrev parameters := ConstructiveObservedMaterialFamilies.parameters worlds arrows
  (dynamics languages policies) (observes languages policies read) coding

abbrev continuations := ConstructiveObservedMaterialFamilies.continuations worlds arrows
  (dynamics languages policies) (observes languages policies read) coding

def parameter (point : Stagesᵒᵖ) (state : (states languages policies).obj point) :
    (parameters languages policies read coding).Elements :=
  ⟨⟨point⟩, (interpretation languages policies read coding).app point state⟩

theorem continuation_iff (point : Stagesᵒᵖ)
    (parent : (states languages policies).obj point)
    (child : (classes languages policies read coding).obj point) :
    (ConstructiveObservedMaterialFamilies.childPredicate worlds arrows
        (dynamics languages policies) (observes languages policies read) coding).holds
      (parameter languages policies read coding point parent) ⟨child⟩ ↔
      ∃ original : (states languages policies).obj point,
        (classOf languages policies read coding).app point original = child ∧
          Action languages policies parent.val original.val :=
  ConstructiveObservedMaterialFamilies.source_class_continuation_iff worlds arrows
    (dynamics languages policies) (observes languages policies read) coding point parent child

/-- The witness is built from the actual after-state, at the next available
context. It is not a constant-family inhabitant supplied as an assumption. -/
def actionContinuation (point : Stagesᵒᵖ)
    (parent : (states languages policies).obj point) (after : Space languages policies)
    (action : Action languages policies parent.val after) :
    (continuations languages policies read coding).native.obj
      (parameter languages policies read coding (world (stageIndex point + 1))
        ((states languages policies).map (extend point) parent)) :=
  ⟨⟨(classOf languages policies read coding).app (world (stageIndex point + 1))
    (nextState languages policies point parent after action)⟩,
    (continuation_iff languages policies read coding _ _ _).mpr
      ⟨nextState languages policies point parent after action, rfl, action⟩⟩

def materialContinuation (point : Stagesᵒᵖ)
    (parent : (states languages policies).obj point) (after : Space languages policies)
    (action : Action languages policies parent.val after) : HSet.{1} :=
  ((continuations languages policies read coding).models _).value
    (actionContinuation languages policies read coding point parent after action)

theorem action_is_material_member (point : Stagesᵒᵖ)
    (parent : (states languages policies).obj point) (after : Space languages policies)
    (action : Action languages policies parent.val after) :
    materialContinuation languages policies read coding point parent after action ∈
      ((continuations languages policies read coding).models
        (parameter languages policies read coding (world (stageIndex point + 1))
          ((states languages policies).map (extend point) parent))).carrier :=
  ((continuations languages policies read coding).models _).value_mem _

theorem decode_action_continuation (point : Stagesᵒᵖ)
    (parent : (states languages policies).obj point) (after : Space languages policies)
    (action : Action languages policies parent.val after) :
    ((continuations languages policies read coding).models _).decode
      ⟨materialContinuation languages policies read coding point parent after action,
        action_is_material_member languages policies read coding point parent after action⟩ =
      actionContinuation languages policies read coding point parent after action :=
  ((continuations languages policies read coding).models _).decode_value _

def emptyState (point : Stagesᵒᵖ) : (states languages policies).obj point :=
  ⟨⟨[], [], []⟩, initial_started languages policies [], Nat.zero_le _⟩

theorem empty_space_has_no_continuation (point : Stagesᵒᵖ)
    (child : (continuations languages policies read coding).native.obj
      (parameter languages policies read coding point (emptyState languages policies point))) : False := by
  obtain ⟨original, _, action⟩ :=
    (continuation_iff languages policies read coding point
      (emptyState languages policies point) child.val.down).mp child.property
  rcases action_needs_atom_or_session languages policies action with atoms | sessions
  · exact atoms rfl
  · exact sessions rfl

end Mettapedia.GSLT.ProgrammableSpaceMaterialFamilies
