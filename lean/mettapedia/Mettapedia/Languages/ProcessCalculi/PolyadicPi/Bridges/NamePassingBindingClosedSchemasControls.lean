import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemasInterpretation
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingConstructorControls
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.PublicOutputObservation

/-!
# Complete schema sections, scope and model-admission controls

The supplied reference body retains both bound name positions and an old
ambient position. Actual future substitutions can identify old names while
preserving the reference and return binders. Independent public output
observations separate the exchanged bound positions. A free process-tree
algebra rejects the scope schema, so the equation extension adds a genuine
model obligation to the constructor-only closed presentation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemas.Controls

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.OSLF.Binding CategoricalBindingModel
open IntrinsicScopedConditionalPresheaf MultiBinderPresheaf
open Mettapedia.Languages.LambdaCalculus
open NamePassingCategoricalCompiler NamePassingContinuationOperations NamePassingOpenInterpretation
open NamePassingBindingClosedOperations

attribute [local irreducible] Operations.application Operations.definition Operations.carrier

def context : Ctx sig := [.nm, .nm]
def argument : Name context := .var .zero
def result : Name context := .var (.succ .zero)
def value : Proc (.nm :: context) := out1 (.var (.succ .zero)) (.var .zero)
def payload : Proc (.nm :: .nm :: context) :=
  out2 (.var (.succ .zero)) (.var .zero) (.var (.succ (.succ (.succ .zero))))

def collision : Sub sig context context := fun sort position => match sort, position with
  | .nm, .zero => .var .zero
  | .nm, .succ .zero => .var .zero

def unitMeta : operations.boundBodyObject ⟶
    (ihom (operations.names ⊗ 𝟙_ Ambient)).obj operations.termObject :=
  (MonoidalClosed.pre (ρ_ operations.names).hom).app operations.termObject

theorem unitMeta_inverse : unitMeta ≫ boundValue operations = 𝟙 operations.boundBodyObject := by
  unfold unitMeta boundValue
  rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, Iso.inv_hom_id,
    MonoidalClosed.pre_id, NatTrans.id_app]

def schemaInput :
    ((NamePassingBindingClosedOperations.Native.operations.context [.tm, .nm]) ⊗
      NamePassingBindingClosedOperations.Native.operations.family NamePassing.AuthoredEquations.metas).obj
        (stage context) :=
  ((rawBody value, rawPoint argument, PUnit.unit), (unitMeta.app (stage context) (rawSchemaBody payload), PUnit.unit))

def leftFunction : operations.termObject.obj (stage context) :=
  (NamePassingBindingClosedOperations.Native.operations.model.generic NamePassing.AuthoredEquations.metas
    NamePassing.AuthoredEquations.appDefinition.lhs).app (stage context) schemaInput

def rightFunction : operations.termObject.obj (stage context) :=
  (NamePassingBindingClosedOperations.Native.operations.model.generic NamePassing.AuthoredEquations.metas
    NamePassing.AuthoredEquations.appDefinition.rhs).app (stage context) schemaInput

theorem actual_left_function :
    leftFunction = applySection (defineSection (rawBody value) (rawSchemaBody payload)) (rawPoint argument) := by
  unfold leftFunction Model.generic
  rw [definition_left_value]
  change applySection
    (defineSection (rawBody value) ((unitMeta ≫ boundValue operations).app (stage context) (rawSchemaBody payload)))
      (rawPoint argument) = _
  rw [unitMeta_inverse, NatTrans.id_app, types_id_apply]

theorem actual_right_function :
    rightFunction = defineSection (rawBody value)
      (applicationBody.app (stage context) (rawSchemaBody payload, rawPoint argument)) := by
  unfold rightFunction Model.generic
  rw [definition_right_value]
  rw [appliedBody_native]
  change defineSection (rawBody value)
    (applicationBody.app (stage context)
      ((unitMeta ≫ boundValue operations).app (stage context) (rawSchemaBody payload), rawPoint argument)) = _
  rw [unitMeta_inverse, NatTrans.id_app, types_id_apply]

theorem actual_complete_functions_agree : leftFunction = rightFunction := by
  rw [actual_left_function, actual_right_function]
  exact application_definition_section _ _ _

def sourceImage (term : Term NamePassing.AuthoredEquations.schemaSig [.tm, .nm] .tm) :
    Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.ArrowValue Ambient :=
  ⟨interpretation.functor.obj
      ((ClosedPresentation.AuthoredPresentation.inclusion NamePassing.AuthoredEquations.equations).functor.obj
        (ClosedPresentation.SchemaExpressions.genericStage NamePassing.Presentation.signature
          NamePassing.AuthoredEquations.metas [.tm, .nm])),
    interpretation.functor.obj
      ((ClosedPresentation.AuthoredPresentation.inclusion NamePassing.AuthoredEquations.equations).functor.obj
        (ClosedPresentation.sortObject NamePassing.Presentation.signature .tm)),
    interpretation.functor.map
      ((ClosedPresentation.AuthoredPresentation.inclusion NamePassing.AuthoredEquations.equations).functor.map
        (Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory.classOf
          (ClosedPresentation.SchemaExpressions.expression NamePassing.Presentation.signature term)))⟩

def readImage (term : Term NamePassing.AuthoredEquations.schemaSig [.tm, .nm] .tm) :
    Option (operations.termObject.obj (stage context)) :=
  (Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.ArrowValue.readAt (some (sourceImage term))
    (NamePassingBindingClosedOperations.Native.operations.context [.tm, .nm] ⊗
      NamePassingBindingClosedOperations.Native.operations.family NamePassing.AuthoredEquations.metas)
    operations.termObject).map (fun arrow => arrow.app (stage context) schemaInput)

theorem generated_image_readout (term : Term NamePassing.AuthoredEquations.schemaSig [.tm, .nm] .tm) :
    readImage term = some
      ((NamePassingBindingClosedOperations.Native.operations.model.generic NamePassing.AuthoredEquations.metas term).app
        (stage context) schemaInput) := by
  unfold readImage sourceImage
  rw [generated_schema_readout]
  erw [Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.ArrowValue.readAt_supplied]
  rfl

theorem actual_generated_left : readImage NamePassing.AuthoredEquations.appDefinition.lhs = some leftFunction :=
  generated_image_readout _

theorem actual_generated_right : readImage NamePassing.AuthoredEquations.appDefinition.rhs = some rightFunction :=
  generated_image_readout _

theorem actual_generated_equation :
    readImage NamePassing.AuthoredEquations.appDefinition.lhs =
      readImage NamePassing.AuthoredEquations.appDefinition.rhs := by
  rw [actual_generated_left, actual_generated_right, actual_complete_functions_agree]

theorem actual_two_binder_readout :
    bodyReadout (rawSchemaBody payload) = (Quotient.mk _ payload : TermQ equations (.nm :: .nm :: context) .pr) :=
  rawSchemaBody_readout payload

theorem actual_future_collision :
    programsAtEquiv algebra .pr (stage context)
      ((((rawSchemaBody payload).app (stage context) (rawChange collision)) (rawPoint argument)).app
        (stage context) (𝟙 _) (rawPoint result)) =
      (Quotient.mk _ (out2 argument result argument) : TermQ equations context .pr) := by
  rw [rawSchemaBody_future]
  rfl

theorem actual_future_retains_bound_positions :
    bodyReadout (operations.boundBodyObject.map (rawChange collision) (rawSchemaBody payload)) =
      (Quotient.mk _ (out2 (.var (.succ .zero)) (.var .zero) (.var (.succ (.succ .zero)))) :
        TermQ equations (.nm :: .nm :: context) .pr) := by
  rw [rawSchemaBody_substitution, rawSchemaBody_readout]
  rfl

theorem bound_reference_return_distinct :
    rawSchemaBody (out1 (.var (.succ .zero)) (.var .zero) : Proc (.nm :: .nm :: context)) ≠
      rawSchemaBody (out1 (.var .zero) (.var (.succ .zero)) : Proc (.nm :: .nm :: context)) := by
  intro same
  have read := congrArg bodyReadout same
  rw [rawSchemaBody_readout, rawSchemaBody_readout] at read
  have equation := (AuthoredEquations.eqClosure_iff_structuralEq _ _).mp (Quotient.exact read)
  have first : PublicOutputObservation.HasOutput (.succ .zero)
      (out1 (.var (.succ .zero)) (.var .zero) : Proc (.nm :: .nm :: context)) :=
    PublicOutputObservation.output_observed _ _
  have second := (PublicOutputObservation.structural_congr (.succ .zero) equation).mp first
  have active := (PublicOutputObservation.hasOutput_iff_active _ _).mp second
  cases active

def rejectedOperations := generated NamePassingConstructorControls.operations

def rejectedParameters : PUnit ⟶ rejectedOperations.model.family NamePassing.AuthoredEquations.metas :=
  ↾fun _ => (show rejectedOperations.power [.nm] .tm from
    ↾fun reference => NamePassingConstructorControls.body reference.1, PUnit.unit)

def rejectedEnvironment : rejectedOperations.model.Env PUnit [.tm, .nm] := fun sort position =>
  match sort, position with
  | .tm, .zero => ↾fun _ => NamePassingConstructorControls.value
  | .nm, .succ .zero => ↾fun _ => (19 : Nat)

theorem free_tree_rejects_scope_schema :
    rejectedOperations.model.interp NamePassing.AuthoredEquations.metas NamePassing.AuthoredEquations.appDefinition.lhs ≠
      rejectedOperations.model.interp NamePassing.AuthoredEquations.metas NamePassing.AuthoredEquations.appDefinition.rhs := by
  intro same
  have values := congrArg (fun reading => reading.value PUnit rejectedParameters rejectedEnvironment) same
  erw [definition_left_value, definition_right_value] at values
  have current := congrArg (fun arrow : PUnit ⟶ NamePassingConstructorControls.operations.termObject =>
    (show NamePassingConstructorControls.Program from arrow PUnit.unit) 11) values
  unfold Operations.application Operations.definition at current
  have opened := congrArg (fun body => body 5) (NamePassingConstructorControls.ProcessTree.fresh.inj current)
  have impossible := (NamePassingConstructorControls.ProcessTree.parallel.inj opened).2
  cases impossible

theorem constructor_only_category_does_not_identify_scope_schema :
    Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory.classOf
        (ClosedPresentation.SchemaExpressions.expression.{0} NamePassing.Presentation.signature
          NamePassing.AuthoredEquations.appDefinition.lhs) ≠
      Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory.classOf
        (ClosedPresentation.SchemaExpressions.expression.{0} NamePassing.Presentation.signature
          NamePassing.AuthoredEquations.appDefinition.rhs) := by
  intro same
  exact free_tree_rejects_scope_schema
    ((rejectedOperations.schema_arrow_eq_iff _ _).mp (congrArg rejectedOperations.interpretation.functor.map same))

theorem free_tree_not_admitted :
    ¬ Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.Realization
      (ClosedPresentation.AuthoredPresentation.signature.{0} NamePassing.AuthoredEquations.equations)
      (ClosedPresentation.SchemaEquations.assignment
        (Index := ULift.{0} (Fin NamePassing.AuthoredEquations.equations.length)) rejectedOperations) := by
  intro admitted
  have satisfied := (ClosedPresentation.AuthoredPresentation.admission_iff_contextual
    NamePassing.AuthoredEquations.equations rejectedOperations).mp admitted
  have complete := (rejectedOperations.model.schema_family_iff_contextual NamePassing.AuthoredEquations.equations).mpr
    satisfied
  exact free_tree_rejects_scope_schema (complete ⟨0, by decide⟩)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemas.Controls
