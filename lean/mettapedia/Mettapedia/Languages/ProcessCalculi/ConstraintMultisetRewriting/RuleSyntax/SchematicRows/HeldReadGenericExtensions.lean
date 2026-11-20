import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadExtensionSum
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Step

/-!
# Held firings in an explicitly extended capability family

Old firings use the old-extension branch; internal identity firings use its
distinct identity branch. Their actual information, freshness, admission and
results are preserved. This is an embedding, not an unrestricted equivalence
of the extended candidate with the original one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadExtensionSum

open Interface (Frames)
open RuleOccurrences

universe uO uT uH uE uOcc uR uC uZ
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) (E : Extensions.{uO, uH, uE} Hom)
  {O : Type uOcc} {R : Type uR} {C : Type uC} {Z : Type uZ}
  {codes : Codes Tm C Z} {source : RState Tm O R C Z}

def liftHeld (firing : RFiring O R E codes source) :
    RFiring O R (withIdentity X E) codes source :=
  ⟨firing.use, .inl firing.ext, firing.opening, firing.selection, firing.seen,
    firing.madeRules, firing.installed, firing.removedRules, firing.published⟩

def liftInternal (firing : RFiring O R (Extensions.identity X : Extensions.{uO, uH, 0} Hom) codes source) :
    RFiring O R (withIdentity X E) codes source :=
  ⟨firing.use, .inr PUnit.unit, firing.opening, firing.selection, firing.seen,
    firing.madeRules, firing.installed, firing.removedRules, firing.published⟩

theorem liftHeld_information (firing : RFiring O R E codes source) :
    (liftHeld X E firing).information X = firing.information X := rfl

theorem liftHeld_fresh_iff (firing : RFiring O R E codes source) :
    (liftHeld X E firing).Fresh X ↔ firing.Fresh X := Iff.rfl

theorem liftInternal_information
    (firing : RFiring O R (Extensions.identity X : Extensions.{uO, uH, 0} Hom) codes source) :
    (liftInternal X E firing).information X = firing.information X := rfl

theorem liftInternal_fresh_iff
    (firing : RFiring O R (Extensions.identity X : Extensions.{uO, uH, 0} Hom) codes source) :
    (liftInternal X E firing).Fresh X ↔ firing.Fresh X := Iff.rfl

theorem liftHeld_ruleShapes_iff (ambient : Set C) (firing : RFiring O R E codes source) :
    (liftHeld X E firing).RuleShapes ambient ↔ firing.RuleShapes ambient := by
  constructor
  · intro shapes
    exact ⟨shapes.available, shapes.arguments, shapes.installed, shapes.madeNodup,
      shapes.madeLength, shapes.madeNew, shapes.removed, shapes.removedNodup,
      shapes.removedHeld, shapes.published⟩
  · intro shapes
    exact ⟨shapes.available, shapes.arguments, shapes.installed, shapes.madeNodup,
      shapes.madeLength, shapes.madeNew, shapes.removed, shapes.removedNodup,
      shapes.removedHeld, shapes.published⟩

theorem liftInternal_ruleShapes_iff (ambient : Set C)
    (firing : RFiring O R (Extensions.identity X : Extensions.{uO, uH, 0} Hom) codes source) :
    (liftInternal X E firing).RuleShapes ambient ↔ firing.RuleShapes ambient := by
  constructor
  · intro shapes
    exact ⟨shapes.available, shapes.arguments, shapes.installed, shapes.madeNodup,
      shapes.madeLength, shapes.madeNew, shapes.removed, shapes.removedNodup,
      shapes.removedHeld, shapes.published⟩
  · intro shapes
    exact ⟨shapes.available, shapes.arguments, shapes.installed, shapes.madeNodup,
      shapes.madeLength, shapes.madeNew, shapes.removed, shapes.removedNodup,
      shapes.removedHeld, shapes.published⟩

theorem liftHeld_shapes_iff (ambient : Set C) (firing : RFiring O R E codes source) :
    (liftHeld X E firing).Shapes X ambient ↔ firing.Shapes X ambient :=
  and_congr Iff.rfl (and_congr Iff.rfl (liftHeld_ruleShapes_iff X E ambient firing))

theorem liftInternal_shapes_iff (ambient : Set C)
    (firing : RFiring O R (Extensions.identity X : Extensions.{uO, uH, 0} Hom) codes source) :
    (liftInternal X E firing).Shapes X ambient ↔ firing.Shapes X ambient :=
  and_congr Iff.rfl (and_congr Iff.rfl (liftInternal_ruleShapes_iff X E ambient firing))

variable [DecidableEq O]

theorem liftHeld_admission_iff (ambient : Set C) (firing : RFiring O R E codes source) :
    (liftHeld X E firing).Admits X ambient ↔ firing.Admits X ambient := by
  unfold RFiring.Admits
  rw [liftHeld_shapes_iff]
  rfl

theorem liftInternal_admission_iff (ambient : Set C)
    (firing : RFiring O R (Extensions.identity X : Extensions.{uO, uH, 0} Hom) codes source) :
    (liftInternal X E firing).Admits X ambient ↔ firing.Admits X ambient := by
  unfold RFiring.Admits
  rw [liftInternal_shapes_iff]
  rfl

variable [DecidableEq R]

theorem liftHeld_result (firing : RFiring O R E codes source) :
    (liftHeld X E firing).result X = firing.result X := rfl

theorem liftInternal_result
    (firing : RFiring O R (Extensions.identity X : Extensions.{uO, uH, 0} Hom) codes source) :
    (liftInternal X E firing).result X = firing.result X := rfl

variable (O R codes) (ambient : Set C)

noncomputable def liftHeldRun : {source : RState Tm O R C Z} →
    (rstep X O R E codes ambient).toStep.Run source →
      (rstep X O R (withIdentity X E) codes ambient).toStep.Run source
  | _, .nil source => .nil source
  | _, .cons firing admitted rest => .cons (liftHeld X E firing)
      ((liftHeld_admission_iff X E ambient firing).mpr admitted) (liftHeldRun rest)

theorem liftHeldRun_last {source : RState Tm O R C Z}
    (run : (rstep X O R E codes ambient).toStep.Run source) :
    (liftHeldRun X E O R codes ambient run).last = run.last := by
  induction run with
  | nil _ => rfl
  | cons firing admitted rest ih => exact ih

#print axioms liftHeld_admission_iff
#print axioms liftInternal_admission_iff
#print axioms liftHeld_result
#print axioms liftInternal_result
#print axioms liftHeldRun_last

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadExtensionSum
