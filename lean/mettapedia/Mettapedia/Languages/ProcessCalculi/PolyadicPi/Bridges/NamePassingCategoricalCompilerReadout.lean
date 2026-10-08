import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalConstructorReadout

/-!
# The entire independently authored compiler in the categorical model

The complete source constructor tree is read through genuine target
products, abstraction, evaluation and communication primitives. The
comparison retains ordinary source program variables as full return
functions and computes every represented future call.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalCompiler

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open IntrinsicScopedConditionalPresheaf MultiBinderPresheaf
open Mettapedia.Languages.LambdaCalculus
open NamePassingOpenInterpretation NamePassingConstructorInterpretation

theorem parallel_classes {context : Ctx sig} (first second : Proc context) :
    algebra.operation Op.par (.cons (Quotient.mk _ first) (.cons (Quotient.mk _ second) .nil)) =
      (Quotient.mk _ (par first second) : TermQ equations context .pr) :=
  (AuthoredClassified.projection.raw.map_operation Op.par (.cons first (.cons second .nil))).symm

theorem send_classes {context : Ctx sig} (channel first second : Name context) :
    algebra.operation Op.out2 (.cons (Quotient.mk _ channel)
      (.cons (Quotient.mk _ first) (.cons (Quotient.mk _ second) .nil))) =
      (Quotient.mk _ (out2 channel first second) : TermQ equations context .pr) :=
  (AuthoredClassified.projection.raw.map_operation Op.out2
    (.cons channel (.cons first (.cons second .nil)))).symm

theorem input_classes {context : Ctx sig} (channel : Name context) (body : Proc (.nm :: context)) :
    algebra.operation Op.inp1 (.cons (Quotient.mk _ channel) (.cons (Quotient.mk _ body) .nil)) =
      (Quotient.mk _ (inp1 channel body) : TermQ equations context .pr) :=
  (AuthoredClassified.projection.raw.map_operation Op.inp1 (.cons channel (.cons body .nil))).symm

theorem receive_classes {context : Ctx sig} (channel : Name context) (body : Proc (.nm :: .nm :: context)) :
    algebra.operation Op.inp2 (.cons (Quotient.mk _ channel) (.cons (Quotient.mk _ body) .nil)) =
      (Quotient.mk _ (inp2 channel body) : TermQ equations context .pr) :=
  (AuthoredClassified.projection.raw.map_operation Op.inp2 (.cons channel (.cons body .nil))).symm

theorem fresh_classes {context : Ctx sig} (body : Proc (.nm :: context)) :
    algebra.operation Op.nu (.cons (Quotient.mk _ body) .nil) =
      (Quotient.mk _ (nu body) : TermQ equations context .pr) :=
  (AuthoredClassified.projection.raw.map_operation Op.nu (.cons body .nil)).symm

theorem replication_classes {context : Ctx sig} (body : Proc context) :
    algebra.operation Op.rep (.cons (Quotient.mk _ body) .nil) =
      (Quotient.mk _ (rep body) : TermQ equations context .pr) :=
  (AuthoredClassified.projection.raw.map_operation Op.rep (.cons body .nil)).symm

/-- The complete categorical meaning recovers the authored open compiler,
including arbitrary supplied return-sensitive program variables. -/
theorem current_readout : ∀ {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (term : NamePassing.Presentation.Program context) (environment : Environment context target)
    (result : Name target),
    programsAtEquiv algebra .pr (stage target)
        ((((meaning operations term).app (stage target) (contextPoint environment)).app
          (stage target) (𝟙 _)) (rawPoint result)) =
      (Quotient.mk _ (interpret term environment result) : TermQ equations target .pr)
  | _, _, .var position, environment, result => by
      simp only [meaning]
      erw [projection_readout position environment]
      simp only [variablePoint, interpret]
      erw [rawBody_evaluation (environment.program position) result]
  | _, _, .op .reference (.cons name .nil), environment, result => by
      simp only [interpret]
      erw [reference_current name environment result]
  | _, _, .op .abstraction (.cons body .nil), environment, result => by
      simp only [interpret]
      erw [abstraction_shape body environment result, current_readout, receive_classes]
  | _, _, .op .application (.cons function (.cons argument .nil)), environment, result => by
      simp only [interpret]
      erw [application_shape function argument environment result, current_readout,
        send_classes, parallel_classes, fresh_classes]
  | _, _, .op .definition (.cons value (.cons body .nil)), environment, result => by
      simp only [interpret]
      erw [definition_shape value body environment result, current_readout, meaning_body, current_readout,
        input_classes, replication_classes, parallel_classes, fresh_classes]
  | _, _, .op .carrier (.cons name (.cons value (.cons body .nil))), environment, result => by
      simp only [interpret]
      erw [carrier_shape name value body environment result, current_readout, meaning_body,
        current_readout, input_classes, parallel_classes]
termination_by _ _ term _ _ => termSize term
decreasing_by all_goals simp only [termSize, argsSize]; omega

/-- Every actual future call along a represented simultaneous substitution
retains the complete restricted source environment and supplied return name. -/
theorem future_readout {context : Ctx NamePassing.Presentation.signature} {target future : Ctx sig}
    (term : NamePassing.Presentation.Program context) (environment : Environment context target)
    (assigned : Sub sig target future) (result : Name future) :
    programsAtEquiv algebra .pr (stage future)
        ((((meaning operations term).app (stage target) (contextPoint environment)).app
          (stage future) (rawChange assigned)) (rawPoint result)) =
      (Quotient.mk _ (interpret term (environment.substitute assigned) result) :
        TermQ equations future .pr) := by
  rw [meaning_future, current_readout]

/-- The function section itself, not just its current application, is the
authored compiler with its return name left as a genuine bound variable. -/
theorem whole_body_readout {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (term : NamePassing.Presentation.Program context) (environment : Environment context target) :
    scopedBodyEquiv algebra (stage target).unop [.nm] .pr
        ((meaning operations term).app (stage target) (contextPoint environment)) =
      (Quotient.mk _ (interpret term (environment.substitute weakening) (.var .zero)) :
        TermQ equations (.nm :: target) .pr) := by
  rw [meaning_body, current_readout]

theorem whole_function_comparison {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (term : NamePassing.Presentation.Program context) (environment : Environment context target) :
    (meaning operations term).app (stage target) (contextPoint environment) =
      rawBody (interpret term (environment.substitute weakening) (.var .zero)) := by
  apply (scopedBodyEquiv algebra (stage target).unop [.nm] .pr).injective
  rw [whole_body_readout, rawBody_readout]
  rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalCompiler
