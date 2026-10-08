import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperations
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalEquations

/-!
# Complete generated binding and continuation-model comparison

Both meanings are independently constructed. The generic binding evaluator
retains every empty and nonempty function-argument domain, while the
continuation evaluator uses the five actual communication constructor arrows.
Their context and binder comparisons are earned from products, evaluation
and currying, including every ordinary source program variable.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperations

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open NamePassingContinuationOperations

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (primitives : Operations C)

def contextMap (context : Ctx NamePassing.Presentation.signature) :
    (generated primitives).context context ⟶ NamePassingConstructorInterpretation.contextValue primitives context :=
  eqToHom (context_value primitives context)

theorem contextMap_nil : contextMap primitives [] = 𝟙 (𝟙_ C) := rfl

theorem contextMap_cons (sort : NamePassing.Presentation.Srt) (context : Ctx NamePassing.Presentation.signature) :
    contextMap primitives (sort :: context) =
      NamePassingConstructorInterpretation.sortValue primitives sort ◁ contextMap primitives context := by
  unfold contextMap
  rw [whiskerLeft_eqToHom]

theorem projection_comparison : ∀ {context : Ctx NamePassing.Presentation.signature}
    {sort : NamePassing.Presentation.Srt} (position : Var context sort),
    CategoricalBindingModel.projectVar (generated primitives).sort position =
      contextMap primitives context ≫ NamePassingConstructorInterpretation.projection primitives position
  | _ :: _, _, .zero => by
      rw [contextMap_cons]
      exact (whiskerLeft_fst _ _).symm
  | _ :: _, _, .succ position => by
      rw [contextMap_cons]
      change snd _ _ ≫ CategoricalBindingModel.projectVar (generated primitives).sort position =
        (_ ◁ contextMap primitives _) ≫ (snd _ _ ≫ NamePassingConstructorInterpretation.projection primitives position)
      rw [projection_comparison]
      erw [whiskerLeft_snd_assoc]
      rfl

theorem name_comparison {context : Ctx NamePassing.Presentation.signature}
    (name : NamePassing.Presentation.Name context) :
    (generated primitives).meaning name = contextMap primitives context ≫
      NamePassingConstructorInterpretation.nameMeaning primitives name := by
  cases name with
  | var position => exact projection_comparison primitives position
  | op impossible => nomatch impossible

theorem empty_term {context : Ctx NamePassing.Presentation.signature} {sort : NamePassing.Presentation.Srt}
    (term : Term NamePassing.Presentation.signature context sort) :
    MonoidalClosed.curry ((generated primitives).appendContext [] context ≫ (generated primitives).meaning term) ≫
        emptyValue ((generated primitives).sort sort) = (generated primitives).meaning term :=
  empty_curry _

theorem bound_term {context : Ctx NamePassing.Presentation.signature}
    (body : NamePassing.Presentation.Program (.nm :: context))
    (comparison : (generated primitives).meaning body = contextMap primitives (.nm :: context) ≫
      NamePassingConstructorInterpretation.meaning primitives body) :
    MonoidalClosed.curry ((generated primitives).appendContext [.nm] context ≫ (generated primitives).meaning body) ≫
        boundValue primitives = contextMap primitives context ≫
          NamePassingConstructorInterpretation.boundMeaning primitives
            (NamePassingConstructorInterpretation.meaning primitives body) := by
  rw [bound_curry, comparison, contextMap_cons]
  erw [MonoidalClosed.curry_natural_left]
  rw [boundMeaning_curry]

theorem reference_meaning {context : Ctx NamePassing.Presentation.signature}
    (name : NamePassing.Presentation.Name context) :
    (generated primitives).meaning (NamePassing.Presentation.reference name) =
      (generated primitives).meaning name ≫ primitives.reference := by
  change lift (MonoidalClosed.curry ((generated primitives).appendContext [] context ≫
      (generated primitives).meaning name)) (toUnit _) ≫
        (fst _ _ ≫ emptyValue primitives.names ≫ primitives.reference) = _
  rw [lift_fst_assoc]
  rw [← Category.assoc]
  erw [empty_term]

theorem abstraction_meaning {context : Ctx NamePassing.Presentation.signature}
    (body : NamePassing.Presentation.Program (.nm :: context)) :
    (generated primitives).meaning (NamePassing.Presentation.abstraction body) =
      MonoidalClosed.curry ((generated primitives).meaning body) ≫ primitives.abstraction := by
  change lift (MonoidalClosed.curry ((generated primitives).appendContext [.nm] context ≫
      (generated primitives).meaning body)) (toUnit _) ≫
        (fst _ _ ≫ boundValue primitives ≫ primitives.abstraction) = _
  rw [lift_fst_assoc, ← Category.assoc]
  erw [bound_curry]

theorem application_meaning {context : Ctx NamePassing.Presentation.signature}
    (function : NamePassing.Presentation.Program context) (argument : NamePassing.Presentation.Name context) :
    (generated primitives).meaning (NamePassing.Presentation.application function argument) =
      lift ((generated primitives).meaning function) ((generated primitives).meaning argument) ≫
        primitives.application := by
  change lift (MonoidalClosed.curry ((generated primitives).appendContext [] context ≫
      (generated primitives).meaning function))
    (lift (MonoidalClosed.curry ((generated primitives).appendContext [] context ≫
      (generated primitives).meaning argument)) (toUnit _)) ≫
        (lift (fst _ _ ≫ emptyValue primitives.termObject)
          (snd _ _ ≫ fst _ _ ≫ emptyValue primitives.names) ≫ primitives.application) = _
  rw [← Category.assoc, comp_lift]
  simp only [lift_fst_assoc, lift_snd_assoc]
  erw [empty_term, empty_term]

theorem definition_meaning {context : Ctx NamePassing.Presentation.signature}
    (value : NamePassing.Presentation.Program context) (body : NamePassing.Presentation.Program (.nm :: context)) :
    (generated primitives).meaning (NamePassing.Presentation.definition value body) =
      lift ((generated primitives).meaning value) (MonoidalClosed.curry ((generated primitives).meaning body)) ≫
        primitives.definition := by
  change lift (MonoidalClosed.curry ((generated primitives).appendContext [] context ≫
      (generated primitives).meaning value))
    (lift (MonoidalClosed.curry ((generated primitives).appendContext [.nm] context ≫
      (generated primitives).meaning body)) (toUnit _)) ≫
        (lift (fst _ _ ≫ emptyValue primitives.termObject)
          (snd _ _ ≫ fst _ _ ≫ boundValue primitives) ≫ primitives.definition) = _
  rw [← Category.assoc, comp_lift]
  simp only [lift_fst_assoc, lift_snd_assoc]
  erw [empty_term, bound_curry]

theorem carrier_meaning {context : Ctx NamePassing.Presentation.signature}
    (name : NamePassing.Presentation.Name context) (value body : NamePassing.Presentation.Program context) :
    (generated primitives).meaning (NamePassing.Presentation.carrier name value body) =
      lift ((generated primitives).meaning name)
        (lift ((generated primitives).meaning value) ((generated primitives).meaning body)) ≫
          primitives.carrier := by
  change lift (MonoidalClosed.curry ((generated primitives).appendContext [] context ≫
      (generated primitives).meaning name))
    (lift (MonoidalClosed.curry ((generated primitives).appendContext [] context ≫
      (generated primitives).meaning value))
      (lift (MonoidalClosed.curry ((generated primitives).appendContext [] context ≫
        (generated primitives).meaning body)) (toUnit _))) ≫
      (lift (fst _ _ ≫ emptyValue primitives.names)
        (lift (snd _ _ ≫ fst _ _ ≫ emptyValue primitives.termObject)
          (snd _ _ ≫ snd _ _ ≫ fst _ _ ≫ emptyValue primitives.termObject)) ≫ primitives.carrier) = _
  rw [← Category.assoc, comp_lift]
  simp only [comp_lift, lift_fst_assoc, lift_snd_assoc]
  erw [empty_term, empty_term, empty_term]

/-- The complete independent binding evaluator equals the continuation
constructor evaluator, after the earned context comparison. -/
theorem meaning_comparison : ∀ {context : Ctx NamePassing.Presentation.signature}
    (term : NamePassing.Presentation.Program context),
    (generated primitives).meaning term = contextMap primitives context ≫
      NamePassingConstructorInterpretation.meaning primitives term
  | _, .var position => by
      simpa only [ClosedPresentation.Operations.meaning, NamePassingConstructorInterpretation.meaning] using
        projection_comparison primitives position
  | _, .op .reference (.cons name .nil) => by
      erw [reference_meaning, name_comparison]
      simp only [NamePassingConstructorInterpretation.meaning, Category.assoc]
  | _, .op .abstraction (.cons body .nil) => by
      erw [abstraction_meaning, meaning_comparison, contextMap_cons]
      erw [MonoidalClosed.curry_natural_left]
      simp only [NamePassingConstructorInterpretation.meaning, boundMeaning_curry, Category.assoc]
  | _, .op .application (.cons function (.cons argument .nil)) => by
      erw [application_meaning, meaning_comparison, name_comparison, ← comp_lift]
      simp only [NamePassingConstructorInterpretation.meaning, Category.assoc]
  | _, .op .definition (.cons value (.cons body .nil)) => by
      erw [definition_meaning, meaning_comparison, meaning_comparison, contextMap_cons]
      erw [MonoidalClosed.curry_natural_left]
      erw [← comp_lift]
      simp only [NamePassingConstructorInterpretation.meaning, boundMeaning_curry, Category.assoc]
  | _, .op .carrier (.cons name (.cons value (.cons body .nil))) => by
      erw [carrier_meaning, name_comparison, meaning_comparison, meaning_comparison, ← comp_lift, ← comp_lift]
      simp only [NamePassingConstructorInterpretation.meaning, Category.assoc]
termination_by _ term => termSize term
decreasing_by all_goals simp only [termSize, argsSize]; omega

/-- Evaluation of the actual generated binding model at an arbitrary
stage and complete variable environment factors through the earned
continuation comparison. -/
theorem model_value_comparison {context : Ctx NamePassing.Presentation.signature}
    (term : NamePassing.Presentation.Program context) (Z : C)
    (metas : Z ⟶ (generated primitives).model.family [])
    (environment : (generated primitives).model.Env Z context) :
    ((generated primitives).model.interp [] (embed term)).value Z metas environment =
      (generated primitives).model.tupleEnv environment ≫ contextMap primitives context ≫
        NamePassingConstructorInterpretation.meaning primitives term := by
  rw [ClosedPresentation.Operations.meaning_model_value]
  erw [meaning_comparison]

variable [HasFiniteLimits C]

/-- The finite-limit and closed interpretation of the complete generated
term arrow is the independently formed continuation arrow. -/
theorem generated_arrow_comparison {context : Ctx NamePassing.Presentation.signature}
    (term : NamePassing.Presentation.Program context) :
    (⟨(generated primitives).interpretation.functor.obj
        (ClosedPresentation.contextObject.{v} NamePassing.Presentation.signature context),
      (generated primitives).interpretation.functor.obj
        (ClosedPresentation.sortObject NamePassing.Presentation.signature .tm),
      (generated primitives).interpretation.functor.map
        (ClosedPresentation.termArrow NamePassing.Presentation.signature term)⟩ :
          Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.ArrowValue C) =
      ⟨(generated primitives).context context, primitives.termObject,
        contextMap primitives context ≫ NamePassingConstructorInterpretation.meaning primitives term⟩ := by
  rw [ClosedPresentation.Operations.term_complete_readout]
  erw [meaning_comparison]
  rfl

namespace Native

open IntrinsicScopedConditionalPresheaf MultiBinderPresheaf
open NamePassingOpenInterpretation

abbrev nativePrimitives := NamePassingCategoricalCompiler.operations
abbrev operations := generated nativePrimitives

/-- The independently supplied raw environment is inserted through the
inverse of the actual context comparison, retaining all its sections. -/
def inputPoint {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (environment : Environment context target) :
    (operations.context context).obj (NamePassingCategoricalCompiler.stage target) :=
  (eqToIso (context_value nativePrimitives context)).inv.app (NamePassingCategoricalCompiler.stage target)
    (NamePassingCategoricalCompiler.contextPoint environment)

theorem inputPoint_comparison {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (environment : Environment context target) :
    (contextMap nativePrimitives context).app (NamePassingCategoricalCompiler.stage target)
        (inputPoint environment) = NamePassingCategoricalCompiler.contextPoint environment := by
  have complete := congrArg (fun transformation =>
    transformation.app (NamePassingCategoricalCompiler.stage target)
      (NamePassingCategoricalCompiler.contextPoint environment))
    (Iso.inv_hom_id (eqToIso (context_value nativePrimitives context)))
  exact complete

theorem inputPoint_substitution {context : Ctx NamePassing.Presentation.signature} {target future : Ctx sig}
    (environment : Environment context target) (assigned : Sub sig target future) :
    (operations.context context).map (NamePassingCategoricalCompiler.rawChange assigned) (inputPoint environment) =
      inputPoint (environment.substitute assigned) := by
  have natural := (eqToIso (context_value nativePrimitives context)).inv.naturality_apply
    (NamePassingCategoricalCompiler.rawChange assigned) (NamePassingCategoricalCompiler.contextPoint environment)
  rw [NamePassingCategoricalCompiler.contextPoint_substitution] at natural
  exact natural.symm

/-- This equality identifies entire function sections, before any return
name, current or future call has been selected. -/
theorem complete_function_comparison {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (term : NamePassing.Presentation.Program context) (environment : Environment context target) :
    (operations.meaning term).app (NamePassingCategoricalCompiler.stage target) (inputPoint environment) =
      NamePassingCategoricalCompiler.rawBody
        (interpret term (environment.substitute weakening) (.var .zero)) := by
  erw [meaning_comparison]
  simp only [NatTrans.comp_app_apply]
  rw [inputPoint_comparison]
  exact NamePassingCategoricalCompiler.whole_function_comparison term environment

/-- Simultaneous source substitution acts on complete generated function
sections through the independently supplied source environment action. -/
theorem source_function_substitution {before after : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (term : NamePassing.Presentation.Program before) (assigned : Sub NamePassing.Presentation.signature before after)
    (environment : Environment after target) :
    (operations.meaning (bind assigned term)).app (NamePassingCategoricalCompiler.stage target)
        (inputPoint environment) =
      (operations.meaning term).app (NamePassingCategoricalCompiler.stage target)
        (inputPoint (environment.sourceSubstitute assigned)) := by
  erw [complete_function_comparison, complete_function_comparison]
  rw [interpret_source_substitution, ← Environment.sourceSubstitute_target]

theorem current_readout {context : Ctx NamePassing.Presentation.signature} {target : Ctx sig}
    (term : NamePassing.Presentation.Program context) (environment : Environment context target)
    (result : Name target) :
    programsAtEquiv NamePassingCategoricalCompiler.algebra .pr (NamePassingCategoricalCompiler.stage target)
      (((operations.meaning term).app (NamePassingCategoricalCompiler.stage target) (inputPoint environment)).app
        (NamePassingCategoricalCompiler.stage target) (𝟙 _) (NamePassingCategoricalCompiler.rawPoint result)) =
      (Quotient.mk _ (interpret term environment result) : TermQ equations target .pr) := by
  erw [meaning_comparison]
  simp only [NatTrans.comp_app_apply]
  rw [inputPoint_comparison]
  exact NamePassingCategoricalCompiler.current_readout term environment result

theorem future_readout {context : Ctx NamePassing.Presentation.signature} {target future : Ctx sig}
    (term : NamePassing.Presentation.Program context) (environment : Environment context target)
    (assigned : Sub sig target future) (result : Name future) :
    programsAtEquiv NamePassingCategoricalCompiler.algebra .pr (NamePassingCategoricalCompiler.stage future)
      (((operations.meaning term).app (NamePassingCategoricalCompiler.stage target) (inputPoint environment)).app
        (NamePassingCategoricalCompiler.stage future) (NamePassingCategoricalCompiler.rawChange assigned)
        (NamePassingCategoricalCompiler.rawPoint result)) =
      (Quotient.mk _ (interpret term (environment.substitute assigned) result) : TermQ equations future .pr) := by
  erw [meaning_comparison]
  simp only [NatTrans.comp_app_apply]
  rw [inputPoint_comparison]
  exact NamePassingCategoricalCompiler.future_readout term environment assigned result

/-- The actual native categorical binding operation data satisfies every
authored source static equation as equality of whole natural arrows. -/
theorem static_meaning {context : Ctx NamePassing.Presentation.signature}
    {first second : NamePassing.Presentation.Program context}
    (equal : NamePassing.Presentation.StaticEq first second) :
    operations.meaning first = operations.meaning second := by
  erw [meaning_comparison, meaning_comparison, NamePassingCategoricalCompiler.static_arrow equal]

theorem static_generated_arrow {context : Ctx NamePassing.Presentation.signature}
    {first second : NamePassing.Presentation.Program context}
    (equal : NamePassing.Presentation.StaticEq first second) :
    (⟨operations.interpretation.functor.obj
        (ClosedPresentation.contextObject NamePassing.Presentation.signature context),
      operations.interpretation.functor.obj (ClosedPresentation.sortObject NamePassing.Presentation.signature .tm),
      operations.interpretation.functor.map (ClosedPresentation.termArrow NamePassing.Presentation.signature first)⟩ :
        Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.ArrowValue NamePassingCategoricalCompiler.Ambient) =
    ⟨operations.interpretation.functor.obj
        (ClosedPresentation.contextObject NamePassing.Presentation.signature context),
      operations.interpretation.functor.obj (ClosedPresentation.sortObject NamePassing.Presentation.signature .tm),
      operations.interpretation.functor.map (ClosedPresentation.termArrow NamePassing.Presentation.signature second)⟩ := by
  rw [generated_arrow_comparison, generated_arrow_comparison]
  rw [NamePassingCategoricalCompiler.static_arrow equal]

/-- All complete generated-model evaluations respect an authored static
derivation; no selected-call or observation equivalence is used. -/
theorem static_model_value {context : Ctx NamePassing.Presentation.signature}
    {first second : NamePassing.Presentation.Program context}
    (equal : NamePassing.Presentation.StaticEq first second) (Z : NamePassingCategoricalCompiler.Ambient)
    (metas : Z ⟶ operations.model.family []) (environment : operations.model.Env Z context) :
    (operations.model.interp [] (embed first)).value Z metas environment =
      (operations.model.interp [] (embed second)).value Z metas environment := by
  rw [ClosedPresentation.Operations.meaning_model_value, ClosedPresentation.Operations.meaning_model_value,
    static_meaning equal]

end Native

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperations
