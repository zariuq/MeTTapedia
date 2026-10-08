import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableSchemaSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableSchemaSelection
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.ExecutableTowerSchemaNumbers

/-!
# Positive and negative controls for source-derived equation execution

Shared slots, capture-avoiding right sides and first-match priority are
observable independently. A failed match can become successful after context
substitution. A missing right-side slot gives no contraction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Normalization.ExecutableSchemaControls

open AlgebraicSchema ExecutableSchemaMatching ExecutableSchemaSelection

def repeated : Tm Unit 1 := .app (.var 0) (.var 0)

theorem shared_slot_matches :
    (run repeated (.app (.const `a) (.const `a) : Tm Unit 0) (fun _ => none)).isSome = true := by
  decide +kernel

theorem differing_slot_refuses :
    run repeated (.app (.const `a) (.const `b) : Tm Unit 0) (fun _ => none) = none := by
  decide +kernel

theorem previous_binding_is_preserved :
    run (.var 0 : Tm Unit 1) (.const `b : Tm Unit 0) (fun _ => some (.const `a)) = none := by
  decide +kernel

def openSubject : Tm Unit 2 := .app (.var 0) (.var 1)

def connectSlots : Sub Unit 2 0 := fun _ => .const `a

theorem open_match_waits : run repeated openSubject (fun _ => none) = none := by
  decide +kernel

theorem substitution_enables_matching :
    (run repeated (Presentation.subst connectSlots openSubject) (fun _ => none)).isSome = true := by
  decide +kernel

def capturesUnderBinders : SchemaTable Unit :=
  [⟨1, (.app (.const `f) (.var 0)), (.lam (.lam (.var 2)))⟩]

theorem right_side_preserves_scope :
    (first capturesUnderBinders (.app (.const `f) (.var 0) : Tm Unit 1)).target? =
      some (.lam (.lam (.var 2))) := by
  decide +kernel

def missingRightSlot : SchemaTable Unit :=
  [⟨1, (.const `a), (.var 0)⟩]

theorem unassigned_right_side_is_not_a_value :
    (first missingRightSlot (.const `a : Tm Unit 0)).target? = none := by
  decide +kernel

theorem unassigned_right_side_retains_its_origin :
    (first missingRightSlot (.const `a : Tm Unit 0)).position? = some 0 := by
  decide +kernel

def overlapping : SchemaTable Unit :=
  [⟨0, (.const `a), (.const `b)⟩, ⟨0, (.const `a), (.const `c)⟩]

theorem first_source_occurrence_is_selected :
    (first overlapping (.const `a : Tm Unit 0)).target? = some (.const `b) := by
  decide +kernel

theorem source_position_is_retained :
    (first overlapping (.const `a : Tm Unit 0)).position? = some 0 := by
  decide +kernel

theorem later_equation_is_still_a_semantic_step :
    (SchemaFamily.computation overlapping.family).step (.const `a : Tm Unit 0) (.const `c) :=
  SchemaTable.step_of_mem overlapping (List.mem_cons_of_mem _ List.mem_cons_self) Fin.elim0

/-- A selected policy need not reflect the unprioritized semantic relation. -/
theorem arbitrary_priority_does_not_reflect_all_steps :
    ¬ ((first overlapping (.const `a : Tm Unit 0)).target? = some (.const `c)) := by
  rw [first_source_occurrence_is_selected]
  decide +kernel

end TypedEquality.Normalization.ExecutableSchemaControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
