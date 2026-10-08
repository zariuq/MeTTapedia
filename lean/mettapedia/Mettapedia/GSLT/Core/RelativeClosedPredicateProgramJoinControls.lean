import Mettapedia.GSLT.Core.RelativeClosedProgramReductionExtensionControls
import Mettapedia.CategoryTheory.RelativeClosedPredicateLogicControls
import Mettapedia.CategoryTheory.RelativeClosedPositionedModalInterpretation

/-!
# Joint program and predicate interpretation controls

The complete source/reduct readings and the independently interpreted
quantifier answers coexist in one environment. The raw abstraction reading
uses the shared context-first constructor, while the established raw curry
continues to take its argument first.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedPredicateProgramJoinControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory

theorem complete_program_and_predicate_readings :
    (RelativeClosedProgramReductionExtensionControls.decodedSource (ULift.up false)).down = false ∧
    (RelativeClosedProgramReductionExtensionControls.decodedTarget (ULift.up false)).down = true ∧
    ¬ ElementaryTypePredicateReadout.Contains
      (HigherOrderInternalPredicateObject.family HigherOrderInternalPredicateControls.logic
        (HigherOrderInternalPredicateControls.suppliedName ≫
          RelativeClosedPredicateLogic.Controls.universalImage)) (PUnit.unit, 1) ∧
    ElementaryTypePredicateReadout.Contains
      (HigherOrderInternalPredicateObject.family HigherOrderInternalPredicateControls.logic
        (HigherOrderInternalPredicateControls.suppliedName ≫
          RelativeClosedPredicateLogic.Controls.existentialImage)) (PUnit.unit, 1) :=
  ⟨RelativeClosedProgramReductionExtensionControls.complete_supplied_endpoints.1,
    RelativeClosedProgramReductionExtensionControls.complete_supplied_endpoints.2.1,
    RelativeClosedPredicateLogic.Controls.the_actual_interpreted_operations_disagree.2,
    RelativeClosedPredicateLogic.Controls.the_actual_interpreted_operations_disagree.1⟩

universe k w z
variable {C : Type k} [Category.{k} C] {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (base : C ⥤ D) (meaning : RelativeClosedPredicateLogic.Interpretation.Meaning base)

theorem context_first_abstraction_reads_the_complete_first_input (context argument : C) :
    (RelativeClosedPredicateLogic.Interpretation.assignment base meaning).evaluateArrow
      (RawHom.abstract (RawHom.first
        (baseObject (RelativeClosedPredicateLogic.signature (C := C)) context)
        (baseObject (RelativeClosedPredicateLogic.signature (C := C)) argument))).code =
      some ⟨base.obj context, base.obj argument ⟶[D] base.obj context,
        Interpretation.abstraction (fst (base.obj context) (base.obj argument))⟩ :=
  RawInterpretation.abstract (RelativeClosedPredicateLogic.Interpretation.assignment base meaning)
    rfl
    rfl
    rfl
    (RawInterpretation.first (RelativeClosedPredicateLogic.Interpretation.assignment base meaning)
      rfl
      rfl)

end Mettapedia.GSLT.Core.RelativeClosedPredicateProgramJoinControls
