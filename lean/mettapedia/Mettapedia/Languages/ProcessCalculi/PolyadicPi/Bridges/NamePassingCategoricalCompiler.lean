import Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperationsReadout
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingConstructorInterpretation
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOpenEquations

/-!
# The categorical continuation compiler in the actual pi equation model

The communication primitives come from the independently authored binding
operators and equation quotient. Their genuine function objects interpret
both source terms and received bodies. The comparison reads supplied raw
program bodies through the actual exponential decoder and evaluation, with
complete ambient substitutions retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalCompiler

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding
open IntrinsicScopedConditionalPresheaf MultiBinderPresheaf
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.Languages.LambdaCalculus
open NamePassingContinuationOperations

abbrev algebra := AuthoredClassified.algebra
abbrev Ambient := CategoricalOperations.Ambient algebra
abbrev Base := IntrinsicScopedConditionalPresheaf.Base algebra

/-- These are the actual pi primitive arrows, not a supplied compiler
interpretation of the source operations. -/
abbrev operations : Operations Ambient where
  names := CategoricalOperations.names algebra
  processes := CategoricalOperations.processes algebra
  empty := CategoricalOperations.empty algebra
  parallel := CategoricalOperations.parallel algebra
  output := CategoricalOperations.output algebra
  send := CategoricalOperations.send algebra
  input := CategoricalOperations.input algebra
  receive := CategoricalOperations.receive algebra
  fresh := CategoricalOperations.fresh algebra
  replication := CategoricalOperations.replication algebra

abbrev stage (context : Ctx sig) : Base :=
  Opposite.op (ContextObject.ofList algebra.substitution.toClone context)

def rawPoint {context : Ctx sig} {sort : Srt} (term : Term sig context sort) :
    (programs algebra sort).obj (stage context) :=
  (programsAtEquiv algebra sort (stage context)).symm (Quotient.mk _ term)

def rawBody {context : Ctx sig} (body : Proc (.nm :: context)) :
    ((binders algebra [Srt.nm]).functorHom (programs algebra Srt.pr)).obj (stage context) :=
  (scopedBodyEquiv algebra (stage context).unop [.nm] .pr).symm (Quotient.mk _ body)

theorem rawPoint_readout {context : Ctx sig} {sort : Srt} (term : Term sig context sort) :
    programsAtEquiv algebra sort (stage context) (rawPoint term) = Quotient.mk _ term :=
  (programsAtEquiv algebra sort (stage context)).apply_symm_apply _

theorem rawBody_readout {context : Ctx sig} (body : Proc (.nm :: context)) :
    scopedBodyEquiv algebra (stage context).unop [.nm] .pr (rawBody body) = Quotient.mk _ body :=
  (scopedBodyEquiv algebra (stage context).unop [.nm] .pr).apply_symm_apply _

/-- Every authored ambient substitution gives an actual arrow in the
equation-clone base, including identifications of variable positions. -/
def rawChange {context future : Ctx sig} (assigned : Sub sig context future) :
    stage context ⟶ stage future :=
  Quiver.Hom.op (fun position => Quotient.mk _ (assigned _ (varOfIdx context position)))

theorem rawChange_environment {context future : Ctx sig} (assigned : Sub sig context future) :
    BindingSubstitutionAlgebra.fromPositions context (rawChange assigned).unop =
      (fun sort position => (Quotient.mk _ (assigned sort position) : TermQ equations future sort)) := by
  funext sort position
  exact BindingSubstitutionAlgebra.fromPositions_ofEnvironment (F := TermQ equations) (Δ := future)
    (fun sort position => (Quotient.mk _ (assigned sort position) : TermQ equations future sort)) position

theorem rawPoint_substitution {context future : Ctx sig} {sort : Srt}
    (assigned : Sub sig context future) (term : Term sig context sort) :
    (programs algebra sort).map (rawChange assigned) (rawPoint term) =
      rawPoint (Mettapedia.OSLF.Binding.bind assigned term) := by
  apply (programsAtEquiv algebra sort (stage future)).injective
  change algebra.substitution.substitute
    (BindingSubstitutionAlgebra.fromPositions context (rawChange assigned).unop)
    (Quotient.mk _ term) = Quotient.mk _ (Mettapedia.OSLF.Binding.bind assigned term)
  rw [rawChange_environment]
  exact (AuthoredClassified.projection.map_substitute assigned term).symm

/-- Evaluation of the complete return function performs the original
capture-avoiding opening. No current-stage approximation replaces it. -/
theorem rawBody_evaluation {context : Ctx sig} (body : Proc (.nm :: context))
    (result : Name context) :
    programsAtEquiv algebra .pr (stage context)
        ((rawBody body).app (stage context) (𝟙 _) (rawPoint result)) =
      (Quotient.mk _ (inst body result) : TermQ equations context .pr) := by
  have evaluated := IntrinsicScopedOperationalPresheafPrograms.function_eval_body
    algebra [.nm] .pr (stage context) (rawPoint result) (rawBody body)
  rw [rawBody_readout] at evaluated
  have joined := IntrinsicScopedOperationalPresheafPrograms.evaluation_environment
    algebra [Srt.nm] (stage context) (rawPoint result)
  have through := evaluated.trans (congrArg
    (fun environment => algebra.substitution.substitute environment (Quotient.mk _ body)) joined)
  have represented : ∀ sort position,
      (Quotient.mk _ (extend result sort position) : TermQ equations context sort) =
        SemanticContextualMetavariables.joinEnvironment
          (BindingSubstitutionAlgebra.fromPositions (F := TermQ equations) (Δ := context)
            [Srt.nm] (rawPoint result))
          (fun _ position => algebra.substitution.injectVar position) sort position := by
    intro sort position
    cases position with
    | zero => rfl
    | succ old => rfl
  exact through.trans
    (BindingEquationQuotientSubstitution.substitute_eq_bindQ equations _
      (extend result) represented (Quotient.mk _ body))

theorem rawLift_environment {context future : Ctx sig} (assigned : Sub sig context future) :
    ∀ (scope : Ctx sig) (sort : Srt) (position : Var (scope ++ context) sort),
      (Quotient.mk _ (liftSub assigned scope sort position) : TermQ equations (scope ++ future) sort) =
        algebra.substitution.liftEnvironment
          (fun sort position => Quotient.mk _ (assigned sort position)) scope sort position
  | [], _, _ => rfl
  | _ :: _, _, .zero => rfl
  | _ :: scope, sort, .succ old => by
      change (Quotient.mk _ (weaken (liftSub assigned scope sort old)) : TermQ equations _ sort) =
        algebra.substitution.weaken _
      rw [← rawLift_environment assigned scope sort old]
      exact (congrArg (Quotient.mk _)
        (bind_var_eq_rename (fun _ position => Var.succ position) (liftSub assigned scope sort old))).symm.trans
        (AuthoredClassified.projection.map_substitute
          (fun _ position => Term.var (Var.succ position)) (liftSub assigned scope sort old))

/-- The actual exponential restriction carries precisely the raw lifted
substitution, preserving its return-name binder. -/
theorem rawBody_substitution {context future : Ctx sig}
    (assigned : Sub sig context future) (body : Proc (.nm :: context)) :
    operations.termObject.map (rawChange assigned) (rawBody body) =
      rawBody (Mettapedia.OSLF.Binding.bind (liftSub assigned [.nm]) body) := by
  apply (scopedBodyEquiv algebra (stage future).unop [.nm] .pr).injective
  change scopedBodyEquiv algebra (stage future).unop [.nm] .pr
    (((binders algebra [Srt.nm]).functorHom (programs algebra Srt.pr)).map
      (rawChange assigned) (rawBody body)) = _
  rw [rawBody_readout, scopedBodyEquiv_reindex, rawBody_readout]
  change algebra.substitution.substitute
    (BindingSubstitutionAlgebra.fromPositions (F := TermQ equations) (Δ := Srt.nm :: future) (Srt.nm :: context)
      (extendScope algebra [Srt.nm] (rawChange assigned).unop))
    (Quotient.mk _ body) = Quotient.mk _ (Mettapedia.OSLF.Binding.bind (liftSub assigned [.nm]) body)
  have represented : ∀ sort position,
      (Quotient.mk _ (liftSub assigned [Srt.nm] sort position) :
        TermQ equations (Srt.nm :: future) sort) =
        BindingSubstitutionAlgebra.fromPositions (F := TermQ equations) (Δ := Srt.nm :: future) (Srt.nm :: context)
          (extendScope algebra [Srt.nm] (rawChange assigned).unop) sort position := by
    intro sort position
    change _ = BindingSubstitutionAlgebra.fromPositions (F := TermQ equations) (Δ := Srt.nm :: future)
      (Srt.nm :: context) (extendScope algebra [Srt.nm]
        (environmentArrow algebra (fun sort position => Quotient.mk _ (assigned sort position)))) sort position
    rw [extendScope_environment]
    exact (rawLift_environment assigned [Srt.nm] sort position).trans
      (BindingSubstitutionAlgebra.fromPositions_ofEnvironment
        (algebra.substitution.liftEnvironment
          (fun sort position => Quotient.mk _ (assigned sort position)) [Srt.nm]) position).symm
  exact BindingEquationQuotientSubstitution.substitute_eq_bindQ equations _
    (liftSub assigned [.nm]) represented (Quotient.mk _ body)

/-- A complete supplied return function agrees with the authored process
at every represented future substitution and every supplied return name. -/
theorem rawBody_future {context future : Ctx sig}
    (assigned : Sub sig context future) (body : Proc (.nm :: context)) (result : Name future) :
    programsAtEquiv algebra .pr (stage future)
        ((rawBody body).app (stage future) (rawChange assigned) (rawPoint result)) =
      (Quotient.mk _ (inst (Mettapedia.OSLF.Binding.bind (liftSub assigned [.nm]) body) result) :
        TermQ equations future .pr) := by
  have evaluated := rawBody_evaluation
    (Mettapedia.OSLF.Binding.bind (liftSub assigned [.nm]) body) result
  rw [← rawBody_substitution assigned body] at evaluated
  change programsAtEquiv algebra .pr (stage future)
    ((rawBody body).app (stage future) (rawChange assigned ≫ 𝟙 _) (rawPoint result)) = _ at evaluated
  rw [Category.comp_id] at evaluated
  exact evaluated

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalCompiler
