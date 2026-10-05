import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualMaterialLogic
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetCollectionControls

/-!
# Formula controls in the actual infinite hyperset model

The self-member atom is inhabited at the actual cyclic set and excluded at
empty. The quantified extensionality premise distinguishes late membership
from an empty set, although all present membership predicates agree. These
controls use the same logical interpretation and the constructed set model.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualMaterialLogicControls

open _root_.CategoryTheory ContextualMaterialLogic HostChoiceContextualMaterialLogic
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality
open HostChoiceContextualSetInterpretationControls
open PowerClassPresheafDescent.Controls

universe u
variable {D : Type u} [Category.{u} D]

def pairEnvironment (point : D) (child parent : (sets (D := D)).obj point) :
    Environment sets 2 point := Fin.cases child (fun _ => parent)

theorem cyclic_atom (point : D) :
    force sets HostChoiceContextualMaterialLogic.model (.member 0 1)
      point (pairEnvironment point (loopSet.val point) (loopSet.val point)) :=
  loop_self_member point

theorem empty_atom_false (point : D) (child : (sets (D := D)).obj point) :
    ¬ force sets HostChoiceContextualMaterialLogic.model (.member 0 1)
      point (pairEnvironment point child (emptySet.val point)) :=
  member_empty point child

theorem empty_atom_negated (point : D) (child : (sets (D := D)).obj point) :
    force sets HostChoiceContextualMaterialLogic.model (.imply (.member 0 1) .bottom)
      point (pairEnvironment point child (emptySet.val point)) := by
  intro target arrow belongs
  change Member target (sets.map arrow child) (sets.map arrow (emptySet.val point)) at belongs
  rw [emptySet.property arrow] at belongs
  exact member_empty target _ belongs

namespace Infinite

abbrev values := sets (D := Stagesᵒᵖ)

def allMembersAgree : Formula 2 := .all (equivalent (.member 0 1) (.member 0 2))

noncomputable def lateEmptyEnvironment : Environment values 2 (world 0) :=
  pairEnvironment (world 0)
    (HostChoiceContextualSetInterpretationControls.Infinite.lateSet.val (world 0))
    (emptySet.val (world 0))

theorem present_members_agree : ∀ child : values.obj (world 0),
    Member (world 0) child (lateEmptyEnvironment 0) ↔ Member (world 0) child (lateEmptyEnvironment 1) :=
  HostChoiceContextualSetInterpretationControls.Infinite.present_members_equal

theorem full_quantified_agreement_fails :
    ¬ force values HostChoiceContextualMaterialLogic.model allMembersAgree (world 0) lateEmptyEnvironment := by
  intro agreement
  have future := agreement (world 1) ContextualMaterialCoalgebraControls.firstAdvance (emptySet.val (world 1))
  have forward := future.1 (world 1) (𝟙 _)
  rw [ContextualMaterialLogic.transport_id] at forward
  have belongs := (futureMember_iff ContextualMaterialCoalgebraControls.firstAdvance _ _).mp
    HostChoiceContextualSetInterpretationControls.Infinite.late_has_later_member
  have inferred := forward belongs
  change Member (world 1) (emptySet.val (world 1))
    (values.map ContextualMaterialCoalgebraControls.firstAdvance (emptySet.val (world 0))) at inferred
  rw [emptySet.property ContextualMaterialCoalgebraControls.firstAdvance] at inferred
  exact member_empty (world 1) _ inferred

theorem extensionality_still_valid :
    force values HostChoiceContextualMaterialLogic.model extensionality (world 0) lateEmptyEnvironment :=
  extensionality_valid (world 0) lateEmptyEnvironment

theorem actual_values_unequal : lateEmptyEnvironment 0 ≠ lateEmptyEnvironment 1 :=
  HostChoiceContextualSetInterpretationControls.Infinite.late_ne_empty

/-- Substitution into an actual larger assignment still gives the same
interpreted formula; it does not repair a missing future premise. -/
theorem extensionality_substitution {n : Nat} (indices : Fin 2 → Fin n)
    (point : Stagesᵒᵖ) (assignment : Environment values n point) :
    force values HostChoiceContextualMaterialLogic.model (substitute indices extensionality) point assignment :=
  (force_substitute HostChoiceContextualMaterialLogic.model indices extensionality point assignment).mpr
    (extensionality_valid point (fun index => assignment (indices index)))

end Infinite

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualMaterialLogicControls
