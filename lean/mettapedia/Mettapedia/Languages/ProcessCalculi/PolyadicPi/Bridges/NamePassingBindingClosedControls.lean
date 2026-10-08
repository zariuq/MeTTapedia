import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedComparison
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalControls
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingConstructorControls

/-!
# Generated binding interpretation and complete continuation controls

The actual generated model evaluates ordinary program variables and full
binding bodies. Its current and future calls retain the authored process,
including distinct received positions and the stored value's ambient scope.
An independent tree algebra separately shows that the constructor-only
free category does not identify an operational redex with its contractum.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperations.Controls

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Mettapedia.OSLF.Binding
open IntrinsicScopedConditionalPresheaf MultiBinderPresheaf
open Mettapedia.Languages.LambdaCalculus
open NamePassingOpenInterpretation

abbrev Γ := NamePassingOpenInterpretation.Controls.sourceScope
abbrev Δ := NamePassingOpenInterpretation.Controls.targetScope
abbrev inputs := NamePassingOpenInterpretation.Controls.environment
abbrev first := NamePassingOpenInterpretation.Controls.firstHole
abbrev name := NamePassingOpenInterpretation.Controls.referenceName
abbrev returnName := NamePassingOpenInterpretation.Controls.secondReturn

/-- This is the actual independent binding-model fold, evaluated at its
whole context projections. -/
def evaluated {context : Ctx NamePassing.Presentation.signature}
    (term : NamePassing.Presentation.Program context) :
    Native.operations.context context ⟶ Native.nativePrimitives.termObject :=
  (Native.operations.model.interp [] (embed term)).value (Native.operations.context context)
    (CartesianMonoidalCategory.toUnit _) (Native.operations.model.projections context)

theorem evaluated_whole_function {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (term : NamePassing.Presentation.Program context) (environment : Environment context target) :
    (evaluated term).app (NamePassingCategoricalCompiler.stage target) (Native.inputPoint environment) =
      NamePassingCategoricalCompiler.rawBody
        (interpret term (environment.substitute weakening) (.var .zero)) := by
  rw [evaluated, ClosedPresentation.Operations.meaning_at_projections]
  exact Native.complete_function_comparison term environment

def currentCall (term : NamePassing.Presentation.Program Γ) (result : Name Δ) : TermQ equations Δ .pr :=
  programsAtEquiv NamePassingCategoricalCompiler.algebra .pr (NamePassingCategoricalCompiler.stage Δ)
    (((evaluated term).app (NamePassingCategoricalCompiler.stage Δ) (Native.inputPoint inputs)).app
      (NamePassingCategoricalCompiler.stage Δ) (𝟙 _) (NamePassingCategoricalCompiler.rawPoint result))

theorem generated_first_return :
    currentCall first NamePassingOpenInterpretation.Controls.firstReturn =
      Quotient.mk _ (out1 (.var .zero) (.var (.succ .zero))) := by
  erw [currentCall, evaluated, ClosedPresentation.Operations.meaning_at_projections,
    Native.current_readout, NamePassingOpenInterpretation.Controls.first_program_readout]

theorem generated_changed_return :
    currentCall first returnName = Quotient.mk _ (out1 (.var (.succ .zero)) (.var (.succ .zero))) := by
  erw [currentCall, evaluated, ClosedPresentation.Operations.meaning_at_projections,
    Native.current_readout, NamePassingOpenInterpretation.Controls.changed_program_return]

theorem generated_source_substitution_call :
    currentCall (bind NamePassingOpenInterpretation.Controls.filling first) returnName =
      Quotient.mk _ NamePassingOpenInterpretation.Controls.suppliedCall := by
  erw [currentCall, evaluated, ClosedPresentation.Operations.meaning_at_projections, Native.current_readout]
  rw [NamePassingOpenInterpretation.Controls.filled_hole_readout]

theorem generated_complete_body :
    scopedBodyEquiv NamePassingCategoricalCompiler.algebra (NamePassingCategoricalCompiler.stage Δ).unop [.nm] .pr
      ((evaluated first).app (NamePassingCategoricalCompiler.stage Δ) (Native.inputPoint inputs)) =
      (Quotient.mk _ (out1 (.var .zero) (.var (.succ (.succ .zero)))) : TermQ equations (.nm :: Δ) .pr) := by
  rw [evaluated_whole_function, NamePassingCategoricalCompiler.rawBody_readout]
  simp only [NamePassingOpenInterpretation.Controls.firstHole, interpret]
  rfl

theorem generated_future_collision :
    programsAtEquiv NamePassingCategoricalCompiler.algebra .pr (NamePassingCategoricalCompiler.stage Δ)
      (((evaluated first).app (NamePassingCategoricalCompiler.stage Δ) (Native.inputPoint inputs)).app
        (NamePassingCategoricalCompiler.stage Δ)
        (NamePassingCategoricalCompiler.rawChange NamePassingCategoricalCompiler.Controls.collision)
        (NamePassingCategoricalCompiler.rawPoint (.var .zero))) =
      Quotient.mk _ (out1 (.var .zero) (.var .zero)) := by
  erw [evaluated, ClosedPresentation.Operations.meaning_at_projections, Native.future_readout]
  simp only [NamePassingOpenInterpretation.Controls.firstHole, interpret]
  rfl

theorem generated_future_retains_return_binder :
    scopedBodyEquiv NamePassingCategoricalCompiler.algebra (NamePassingCategoricalCompiler.stage Δ).unop [.nm] .pr
      (Native.nativePrimitives.termObject.map
        (NamePassingCategoricalCompiler.rawChange NamePassingCategoricalCompiler.Controls.collision)
        ((evaluated first).app (NamePassingCategoricalCompiler.stage Δ) (Native.inputPoint inputs))) =
      (Quotient.mk _ (out1 (.var .zero) (.var (.succ .zero))) : TermQ equations (.nm :: Δ) .pr) := by
  rw [evaluated, ClosedPresentation.Operations.meaning_at_projections]
  erw [meaning_comparison]
  simp only [NatTrans.comp_app_apply]
  rw [Native.inputPoint_comparison]
  exact NamePassingCategoricalCompiler.Controls.actual_future_retains_return_binder

theorem generated_stored_value_scope :
    currentCall (NamePassing.Presentation.definition first
      (NamePassing.Presentation.reference (.var .zero))) returnName =
      Quotient.mk _ NamePassingCategoricalCompiler.Controls.expectedDefinition := by
  erw [currentCall, evaluated, ClosedPresentation.Operations.meaning_at_projections, Native.current_readout]
  simp only [NamePassing.Presentation.definition, NamePassing.Presentation.reference, interpret,
    NamePassingOpenInterpretation.Controls.firstHole]
  rfl

theorem generated_received_positions :
    currentCall (NamePassing.Presentation.abstraction NamePassingOpenInterpretation.Controls.body) returnName =
      Quotient.mk _ (inp2 returnName NamePassingCategoricalCompiler.Controls.expectedReceived) := by
  erw [currentCall, evaluated, ClosedPresentation.Operations.meaning_at_projections, Native.current_readout]
  simp only [NamePassing.Presentation.abstraction, NamePassingOpenInterpretation.Controls.body,
    NamePassing.Presentation.application, interpret]
  rfl

theorem generated_scope_equation :
    evaluated (NamePassing.Presentation.application (NamePassing.Presentation.carrier name first first) name) =
      evaluated (NamePassing.Presentation.carrier name first (NamePassing.Presentation.application first name)) := by
  rw [evaluated, evaluated]
  exact Native.static_model_value (.appCarrier _ _ _ _) _ _ _

namespace Tree

open Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation

abbrev primitives := NamePassingConstructorControls.operations
abbrev operations := generated primitives
abbrev Program := NamePassingConstructorControls.Program
abbrev sourceScope := NamePassingConstructorControls.sourceScope
abbrev caller := NamePassingConstructorControls.caller
abbrev instantiated := NamePassingConstructorControls.instantiatedCall

def actualImage {context : Ctx NamePassing.Presentation.signature}
    (term : NamePassing.Presentation.Program context) : ArrowValue (Type) :=
  ⟨operations.interpretation.functor.obj (ClosedPresentation.contextObject NamePassing.Presentation.signature context),
    operations.interpretation.functor.obj (ClosedPresentation.sortObject NamePassing.Presentation.signature .tm),
    operations.interpretation.functor.map (ClosedPresentation.termArrow NamePassing.Presentation.signature term)⟩

def read {context : Ctx NamePassing.Presentation.signature} (term : NamePassing.Presentation.Program context)
    (input : operations.context context) (result : Nat) : Option NamePassingConstructorControls.ProcessTree :=
  (ArrowValue.readAt (some (actualImage term)) (operations.context context) Program).map
    (fun arrow => arrow input result)

theorem read_comparison {context : Ctx NamePassing.Presentation.signature} (term : NamePassing.Presentation.Program context)
    (input : operations.context context) (result : Nat) :
    read term input result = NamePassingConstructorControls.readOpen term (contextMap primitives context input) result := by
  rw [read, actualImage, generated_arrow_comparison, NamePassingConstructorControls.readOpen_semantics]
  change Option.map (fun arrow : operations.context context ⟶ Program => arrow input result)
    (ArrowValue.readAt (some (⟨operations.context context, Program,
      contextMap primitives context ≫ NamePassingConstructorInterpretation.meaning primitives term⟩ : ArrowValue (Type)))
      (operations.context context) Program) = _
  rw [ArrowValue.readAt_supplied]
  rfl

theorem generated_caller_readout (argument result : Nat) :
    read caller (NamePassingConstructorControls.value, argument, PUnit.unit) result =
      some (.fresh (fun callName => .parallel
        (.receive callName (fun pair => .fresh (fun privateName =>
          .parallel (.output 31 privateName) (.send privateName pair.1 pair.2))))
        (.send callName argument result))) := by
  rw [read_comparison]
  exact NamePassingConstructorControls.whole_bound_caller_readout argument result

/-- The actual free binding constructor interpretation does not silently
promote communication to a categorical static equality. -/
theorem generated_constructor_does_not_equate_beta :
    read caller (NamePassingConstructorControls.value, (17 : Nat), PUnit.unit) 23 ≠
      read instantiated (NamePassingConstructorControls.value, (17 : Nat), PUnit.unit) 23 := by
  rw [read_comparison, read_comparison]
  exact NamePassingConstructorControls.constructor_completion_does_not_supply_beta_equality

theorem free_binding_constructor_category_does_not_equate_beta :
    ClosedPresentation.termArrow.{0} NamePassing.Presentation.signature caller ≠
      ClosedPresentation.termArrow.{0} NamePassing.Presentation.signature instantiated := by
  intro same
  apply generated_constructor_does_not_equate_beta
  unfold read actualImage
  erw [same]

end Tree

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperations.Controls
