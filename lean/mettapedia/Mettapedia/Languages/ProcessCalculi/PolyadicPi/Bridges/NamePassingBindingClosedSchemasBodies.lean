import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedComparison
import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying

/-!
# Complete function-valued schema bodies

A supplied definition-body section has two independent name coordinates:
its reference argument and its return argument. The actual internal currying
and binary context comparisons identify this whole function object with the
two-binder program object. The first raw binder is the return name and the
second is the reference name. Both positions and every future arrow remain
in the comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemas

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding
open IntrinsicScopedConditionalPresheaf MultiBinderPresheaf
open NamePassingCategoricalCompiler
open NamePassingOpenInterpretation

def bodyIso : operations.boundBodyObject ≅ (binders algebra [Srt.nm, Srt.nm]).functorHom (programs algebra Srt.pr) :=
  (MonoidalClosed.ihomCurryIso operations.names operations.names operations.processes).symm ≪≫
    CategoricalOperations.binaryBodyIso algebra

def bodyReadout {context : Ctx sig} (body : operations.boundBodyObject.obj (stage context)) :
    TermQ equations (.nm :: .nm :: context) .pr :=
  scopedBodyEquiv algebra (stage context).unop [.nm, .nm] .pr ((bodyIso.hom).app (stage context) body)

def rawSchemaBody {context : Ctx sig} (body : Proc (.nm :: .nm :: context)) :
    operations.boundBodyObject.obj (stage context) :=
  bodyIso.inv.app (stage context)
    ((scopedBodyEquiv algebra (stage context).unop [.nm, .nm] .pr).symm (Quotient.mk _ body))

theorem rawSchemaBody_readout {context : Ctx sig} (body : Proc (.nm :: .nm :: context)) :
    bodyReadout (rawSchemaBody body) = Quotient.mk _ body := by
  unfold bodyReadout rawSchemaBody
  rw [← NatTrans.comp_app_apply, Iso.inv_hom_id, NatTrans.id_app, types_id_apply]
  exact (scopedBodyEquiv algebra (stage context).unop [.nm, .nm] .pr).apply_symm_apply _

/-- Every supplied complete function section has a raw two-binder
representative. Choice selects a representative of its already supplied
equation class; it does not select a function or discard future inputs. -/
theorem rawSchemaBody_surjective {context : Ctx sig}
    (body : operations.boundBodyObject.obj (stage context)) :
    ∃ raw : Proc (.nm :: .nm :: context), rawSchemaBody raw = body := by
  refine ⟨Quotient.out (bodyReadout body), ?_⟩
  apply (bodyIso.app (stage context)).toEquiv.injective
  apply (scopedBodyEquiv algebra (stage context).unop [.nm, .nm] .pr).injective
  change bodyReadout (rawSchemaBody _) = bodyReadout body
  rw [rawSchemaBody_readout]
  exact Quotient.out_eq _

/-- The comparison evaluates the whole nested section, with the return
coordinate first and the reference coordinate second. -/
theorem bodyIso_future (world future : Base) (change : world ⟶ future)
    (body : operations.boundBodyObject.obj world)
    (arguments : (binders algebra [Srt.nm, Srt.nm]).obj future) :
    ((bodyIso.hom.app world body).app future change) arguments =
      ((body.app future change ((CategoricalOperations.binaryContextIso algebra).inv.app future arguments).2).app
        future (𝟙 future)) ((CategoricalOperations.binaryContextIso algebra).inv.app future arguments).1 := by
  change ((((CategoricalOperations.binaryBodyIso algebra).hom.app world
    ((MonoidalClosed.ihomCurryIso operations.names operations.names operations.processes).inv.app world body)).app
      future change) arguments) = _
  rw [CategoricalOperations.binaryBodyIso_future]
  change (body.app future (change ≫ 𝟙 future)
      (((CategoricalOperations.binaryContextIso algebra).inv.app future arguments).2)).app
    future (𝟙 future) ((CategoricalOperations.binaryContextIso algebra).inv.app future arguments).1 = _
  rw [Category.comp_id]

theorem bodyReadout_canonical {context : Ctx sig}
    (body : operations.boundBodyObject.obj (stage context)) :
    bodyReadout body = programsAtEquiv algebra .pr (stage (.nm :: .nm :: context))
      (((body.app (stage (.nm :: .nm :: context))
        (rawChange (scopeWeakening [.nm, .nm]))
        (rawPoint (.var (.succ .zero) : Name (.nm :: .nm :: context)))).app
          (stage (.nm :: .nm :: context)) (𝟙 _))
        (rawPoint (.var .zero : Name (.nm :: .nm :: context)))) := by
  unfold bodyReadout
  rw [scopedBodyEquiv_apply, bodyIso_future]
  rw [← rawChange_scopeWeakening context [.nm, .nm]]
  erw [binaryNames_points context]
  rfl

/-- The complete two-binder decoding commutes with actual simultaneous
ambient substitution, including identification of names. -/
theorem bodyReadout_substitution {context future : Ctx sig}
    (assigned : Sub sig context future) (body : operations.boundBodyObject.obj (stage context)) :
    bodyReadout (operations.boundBodyObject.map (rawChange assigned) body) =
      algebra.substitution.substitute
        (BindingSubstitutionAlgebra.fromPositions (F := TermQ equations) (Δ := .nm :: .nm :: future)
          (.nm :: .nm :: context) (extendScope algebra [.nm, .nm] (rawChange assigned).unop))
        (bodyReadout body) := by
  unfold bodyReadout
  erw [bodyIso.hom.naturality_apply (rawChange assigned) body]
  exact scopedBodyEquiv_reindex algebra [.nm, .nm] .pr (rawChange assigned) _

theorem bodyReadout_injective {context : Ctx sig} :
    Function.Injective (bodyReadout (context := context)) := by
  intro first second same
  apply (bodyIso.app (stage context)).toEquiv.injective
  exact (scopedBodyEquiv algebra (stage context).unop [.nm, .nm] .pr).injective same

def opening {context : Ctx sig} (result reference : Name context) :
    Sub sig (.nm :: .nm :: context) context
  | _, .zero => result
  | _, .succ .zero => reference
  | _, .succ (.succ old) => .var old

/-- Calling both supplied coordinates opens their ordered raw binders.
The comparison is for the supplied whole function section. -/
theorem rawSchemaBody_call {context : Ctx sig} (body : Proc (.nm :: .nm :: context))
    (reference result : Name context) :
    programsAtEquiv algebra .pr (stage context)
      ((((rawSchemaBody body).app (stage context) (𝟙 _)) (rawPoint reference)).app
        (stage context) (𝟙 _) (rawPoint result)) =
      (Quotient.mk _ (bind (opening result reference) body) : TermQ equations context .pr) := by
  let arguments : (binders algebra [Srt.nm, Srt.nm]).obj (stage context) :=
    (CategoricalOperations.binaryContextIso algebra).hom.app (stage context)
      (rawPoint result, rawPoint reference)
  have compared := bodyIso_future (stage context) (stage context) (𝟙 _)
    (rawSchemaBody body) arguments
  have evaluated := IntrinsicScopedOperationalPresheafPrograms.function_eval_body algebra
    [.nm, .nm] .pr (stage context) arguments (bodyIso.hom.app (stage context) (rawSchemaBody body))
  change programsAtEquiv algebra .pr (stage context)
    (((bodyIso.hom.app (stage context) (rawSchemaBody body)).app (stage context) (𝟙 _)) arguments) =
      algebra.substitution.substitute
        (BindingSubstitutionAlgebra.fromPositions (F := TermQ equations) (Δ := context)
          (Srt.nm :: Srt.nm :: context)
          (Mettapedia.GSLT.LanguageDef.MultiSortedClone.pair algebra.substitution.toClone arguments (𝟙 _)))
        (bodyReadout (rawSchemaBody body)) at evaluated
  rw [rawSchemaBody_readout] at evaluated
  change (((bodyIso.hom.app (stage context) (rawSchemaBody body)).app (stage context) (𝟙 _)) arguments) =
    (((rawSchemaBody body).app (stage context) (𝟙 _) (rawPoint reference)).app
      (stage context) (𝟙 _) (rawPoint result)) at compared
  have through := (congrArg (programsAtEquiv algebra .pr (stage context)) compared).symm.trans evaluated
  have joined := IntrinsicScopedOperationalPresheafPrograms.evaluation_environment algebra
    [Srt.nm, Srt.nm] (stage context) arguments
  have throughJoined := through.trans
    (congrArg (fun environment => algebra.substitution.substitute environment (Quotient.mk _ body)) joined)
  have represented : ∀ sort position,
      (Quotient.mk _ (opening result reference sort position) : TermQ equations context sort) =
        SemanticContextualMetavariables.joinEnvironment
          (BindingSubstitutionAlgebra.fromPositions (F := TermQ equations) (Δ := context)
            [Srt.nm, Srt.nm] arguments)
          (fun _ position => algebra.substitution.injectVar position) sort position := by
    intro sort position
    cases position with
    | zero => rfl
    | succ position =>
      cases position with
      | zero => rfl
      | succ old =>
        cases sort <;> rfl
  exact throughJoined.trans (BindingEquationQuotientSubstitution.substitute_eq_bindQ equations _
    (opening result reference) represented (Quotient.mk _ body))

theorem rawSchemaBody_substitution {context future : Ctx sig}
    (assigned : Sub sig context future) (body : Proc (.nm :: .nm :: context)) :
    operations.boundBodyObject.map (rawChange assigned) (rawSchemaBody body) =
      rawSchemaBody (bind (liftSub assigned [.nm, .nm]) body) := by
  apply bodyReadout_injective
  rw [bodyReadout_substitution, rawSchemaBody_readout, rawSchemaBody_readout]
  have represented : ∀ sort position,
      (Quotient.mk _ (liftSub assigned [Srt.nm, Srt.nm] sort position) :
        TermQ equations (.nm :: .nm :: future) sort) =
        BindingSubstitutionAlgebra.fromPositions (F := TermQ equations) (Δ := Srt.nm :: Srt.nm :: future)
          (Srt.nm :: Srt.nm :: context)
          (extendScope algebra [.nm, .nm] (rawChange assigned).unop) sort position := by
    intro sort position
    change _ = BindingSubstitutionAlgebra.fromPositions (F := TermQ equations) (Δ := Srt.nm :: Srt.nm :: future)
      (Srt.nm :: Srt.nm :: context)
      (extendScope algebra [.nm, .nm]
        (environmentArrow algebra (fun sort position => Quotient.mk _ (assigned sort position)))) sort position
    rw [extendScope_environment]
    exact (rawLift_environment assigned [.nm, .nm] sort position).trans
      (BindingSubstitutionAlgebra.fromPositions_ofEnvironment
        (algebra.substitution.liftEnvironment
          (fun sort position => Quotient.mk _ (assigned sort position)) [.nm, .nm]) position).symm
  exact BindingEquationQuotientSubstitution.substitute_eq_bindQ equations _
    (liftSub assigned [.nm, .nm]) represented (Quotient.mk _ body)

theorem rawSchemaBody_future {context future : Ctx sig}
    (assigned : Sub sig context future) (body : Proc (.nm :: .nm :: context))
    (reference result : Name future) :
    programsAtEquiv algebra .pr (stage future)
      ((((rawSchemaBody body).app (stage future) (rawChange assigned)) (rawPoint reference)).app
        (stage future) (𝟙 _) (rawPoint result)) =
      (Quotient.mk _ (bind (opening result reference)
        (bind (liftSub assigned [.nm, .nm]) body)) : TermQ equations future .pr) := by
  have read := rawSchemaBody_call (bind (liftSub assigned [.nm, .nm]) body) reference result
  rw [← rawSchemaBody_substitution assigned body] at read
  change programsAtEquiv algebra .pr (stage future)
    ((((rawSchemaBody body).app (stage future) (rawChange assigned ≫ 𝟙 _)) (rawPoint reference)).app
      (stage future) (𝟙 _) (rawPoint result)) = _ at read
  rw [Category.comp_id] at read
  exact read

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemas
