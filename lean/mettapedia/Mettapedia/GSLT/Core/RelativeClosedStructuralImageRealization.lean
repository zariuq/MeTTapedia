import Mettapedia.GSLT.Core.RelativeClosedStructuralImagePresentation
import Mettapedia.GSLT.Core.RelativeClosedPositionedModalRealization

/-!
# Exact admission of independently supplied constructor-image arrows

The old predicate and modal meanings are independent target data. Each new
structural value must agree with existential transport along its retained
constructor. The structural evaluator derives this complete body reading;
local equality then earns all new headers and equations. Conversely, the
authored defining equations force exactly that equality. Restriction keeps
the complete old interpretation, including every raw arrow readout.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedStructuralImageRealization

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory ProgramReductionTheory

universe k w z
variable (source : Theory.{k,k}) {Index Origins : Type k}
variable (selected : Index → RelativeClosedPositionedModalPresentation.Selection source)
variable (constructors : Origins → RelativeClosedStructuralImagePresentation.Constructor source)
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (base : source.closed.Obj ⥤ D)
variable (meaning : RelativeClosedPredicateLogic.Interpretation.Meaning base)
variable (modalValues : Option Index → RelativeClosedSyntax.Interpretation.ArrowValue D)

def oldAssignment := RelativeClosedPositionedModalRealization.assignment source base meaning modalValues

theorem logical_object_read (code : ObjectCode source.closed.Obj (RelativeClosedPredicateLogic.symbols source.closed.Obj)) :
    (oldAssignment source base meaning modalValues).evaluateObject
      (code.map (RelativeClosedStructuralImagePresentation.logicalInclusion source selected).base
        (RelativeClosedStructuralImagePresentation.logicalInclusion source selected).objects
        (RelativeClosedStructuralImagePresentation.logicalInclusion source selected).arrows) =
      (RelativeClosedPredicateLogic.Interpretation.assignment base meaning).evaluateObject code :=
  (RelativeClosedStructuralImagePresentation.logicalInclusion source selected).evaluateObject_precompose
    (oldAssignment source base meaning modalValues) code

theorem logical_arrow_read (code : ArrowCode source.closed.Obj (RelativeClosedPredicateLogic.symbols source.closed.Obj)) :
    (oldAssignment source base meaning modalValues).evaluateArrow
      (code.map (RelativeClosedStructuralImagePresentation.logicalInclusion source selected).base
        (RelativeClosedStructuralImagePresentation.logicalInclusion source selected).objects
        (RelativeClosedStructuralImagePresentation.logicalInclusion source selected).arrows) =
      (RelativeClosedPredicateLogic.Interpretation.assignment base meaning).evaluateArrow code :=
  (RelativeClosedStructuralImagePresentation.logicalInclusion source selected).evaluateArrow_precompose
    (oldAssignment source base meaning modalValues) code

def expectedValue (origin : Origins) : RelativeClosedSyntax.Interpretation.ArrowValue D :=
  ⟨RelativeClosedPredicateLogic.Interpretation.targetPower base meaning (constructors origin).arguments,
    RelativeClosedPredicateLogic.Interpretation.targetPower base meaning source.program,
    meaning.existential (constructors origin).term⟩

theorem body_read (origin : Origins) :
    (oldAssignment source base meaning modalValues).evaluateArrow
      (RelativeClosedStructuralImagePresentation.declaration source selected constructors origin).body.code =
        some (expectedValue source constructors base meaning origin) :=
  (logical_arrow_read source selected base meaning modalValues
    (RelativeClosedPredicateLogic.existentialRaw (constructors origin).term).code).trans rfl

variable (values : Origins → RelativeClosedSyntax.Interpretation.ArrowValue D)

def assignment := DefinitionExtension.assignment (oldAssignment source base meaning modalValues) values
def LocalAdmission : Prop := ∀ origin, values origin = expectedValue source constructors base meaning origin

variable (old : RelativeClosedPredicateLogic.Interpretation.Admission base meaning)
variable (modal : RelativeClosedPositionedModalRealization.LocalAdmission source selected base meaning modalValues)

include old modal

theorem oldRealization : RelativeClosedSyntax.Interpretation.Realization
    (RelativeClosedPositionedModalPresentation.signature source selected)
    (oldAssignment source base meaning modalValues) :=
  RelativeClosedPositionedModalRealization.realized source selected base meaning modalValues old modal

theorem expected_complete (origin : Origins) :
    DefinitionExtension.expected (RelativeClosedPositionedModalPresentation.signature source selected)
      (RelativeClosedStructuralImagePresentation.declaration source selected constructors)
      (oldAssignment source base meaning modalValues)
      (oldRealization source selected base meaning modalValues old modal) origin =
        expectedValue source constructors base meaning origin :=
  Option.some.inj ((DefinitionExtension.expected_read
    (RelativeClosedPositionedModalPresentation.signature source selected)
    (RelativeClosedStructuralImagePresentation.declaration source selected constructors)
    (oldAssignment source base meaning modalValues)
    (oldRealization source selected base meaning modalValues old modal) origin).symm.trans
      (body_read source selected constructors base meaning modalValues origin))

theorem definitions_admitted (admitted : LocalAdmission source constructors base meaning values) :
    DefinitionExtension.LocalAdmission (RelativeClosedPositionedModalPresentation.signature source selected)
      (RelativeClosedStructuralImagePresentation.declaration source selected constructors)
      (oldAssignment source base meaning modalValues) values
      (oldRealization source selected base meaning modalValues old modal) :=
  fun origin => (admitted origin).trans (expected_complete source selected constructors base meaning modalValues
    old modal origin).symm

theorem realized (admitted : LocalAdmission source constructors base meaning values) :
    RelativeClosedSyntax.Interpretation.Realization
      (RelativeClosedStructuralImagePresentation.signature source selected constructors)
      (assignment source base meaning modalValues values) :=
  DefinitionExtension.extended_realization (RelativeClosedPositionedModalPresentation.signature source selected)
    (RelativeClosedStructuralImagePresentation.declaration source selected constructors)
    (oldAssignment source base meaning modalValues) values
    (oldRealization source selected base meaning modalValues old modal)
    (definitions_admitted source selected constructors base meaning modalValues values old modal admitted)

theorem necessary_local
    (extended : RelativeClosedSyntax.Interpretation.Realization
      (RelativeClosedStructuralImagePresentation.signature source selected constructors)
      (assignment source base meaning modalValues values)) :
    LocalAdmission source constructors base meaning values := by
  have actual := DefinitionExtension.necessary_admission
    (RelativeClosedPositionedModalPresentation.signature source selected)
    (RelativeClosedStructuralImagePresentation.declaration source selected constructors)
    (oldAssignment source base meaning modalValues) values
    (oldRealization source selected base meaning modalValues old modal) extended
  exact fun origin => (actual origin).trans
    (expected_complete source selected constructors base meaning modalValues old modal origin)

omit old modal in
theorem necessary_previous
    (extended : RelativeClosedSyntax.Interpretation.Realization
      (RelativeClosedStructuralImagePresentation.signature source selected constructors)
      (assignment source base meaning modalValues values)) :
    RelativeClosedSyntax.Interpretation.Realization
      (RelativeClosedPositionedModalPresentation.signature source selected)
      (oldAssignment source base meaning modalValues) := by
  have actual := (RelativeClosedStructuralImagePresentation.inclusion source selected constructors).realization_precompose
    (assignment source base meaning modalValues values) extended
  exact (congrArg (RelativeClosedSyntax.Interpretation.Realization
    (RelativeClosedPositionedModalPresentation.signature source selected))
      (DefinitionExtension.restricted_assignment (RelativeClosedPositionedModalPresentation.signature source selected)
        (RelativeClosedStructuralImagePresentation.declaration source selected constructors)
        (oldAssignment source base meaning modalValues) values)).mp actual

omit old modal in
theorem realization_iff_local :
    RelativeClosedSyntax.Interpretation.Realization
      (RelativeClosedStructuralImagePresentation.signature source selected constructors)
      (assignment source base meaning modalValues values) ↔
        RelativeClosedPredicateLogic.Interpretation.Admission base meaning ∧
          RelativeClosedPositionedModalRealization.LocalAdmission source selected base meaning modalValues ∧
            LocalAdmission source constructors base meaning values := by
  constructor
  · intro extended
    have previous := necessary_previous source selected constructors base meaning modalValues values extended
    have admitted := (RelativeClosedPositionedModalRealization.realization_iff_local
      source selected base meaning modalValues).mp previous
    exact ⟨admitted.1, admitted.2, necessary_local source selected constructors base meaning modalValues values
      admitted.1 admitted.2 extended⟩
  · rintro ⟨previous, modal, admitted⟩
    exact realized source selected constructors base meaning modalValues values previous modal admitted

omit old modal in
theorem named_read (origin : Origins) :
    (assignment source base meaning modalValues values).evaluateArrow
      (RelativeClosedStructuralImagePresentation.namedRaw source selected constructors origin).code = some (values origin) :=
  DefinitionExtension.named_read (RelativeClosedPositionedModalPresentation.signature source selected)
    (RelativeClosedStructuralImagePresentation.declaration source selected constructors)
    (oldAssignment source base meaning modalValues) values origin

theorem complete_previous_diagram (admitted : LocalAdmission source constructors base meaning values) :
    (RelativeClosedStructuralImagePresentation.inclusion source selected constructors).functor ⋙
        RelativeClosedSyntax.Interpretation.functor (assignment source base meaning modalValues values)
          (realized source selected constructors base meaning modalValues values old modal admitted) =
      RelativeClosedSyntax.Interpretation.functor (oldAssignment source base meaning modalValues)
        (oldRealization source selected base meaning modalValues old modal) :=
  DefinitionExtension.complete_restriction (RelativeClosedPositionedModalPresentation.signature source selected)
    (RelativeClosedStructuralImagePresentation.declaration source selected constructors)
    (oldAssignment source base meaning modalValues) values
    (oldRealization source selected base meaning modalValues old modal)
    (definitions_admitted source selected constructors base meaning modalValues values old modal admitted)

end Mettapedia.GSLT.Core.RelativeClosedStructuralImageRealization
