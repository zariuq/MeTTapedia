import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafRulePoints
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafBoundContexts

/-!
# Ordered binder-local premise endpoints at operational presheaf points

Evaluating each premise at its canonical extended stage reads the original
rule's child judgment. Captured bodies and closing values use the existing
contextual fold and the actual ordered binder environment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafPremisePoints

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open BindingSubstitutionAlgebra IntrinsicScopedConditionalPresheaf
open MultiBinderPresheaf SecondOrderContext
open IntrinsicScopedOperationalPresheafPrograms
open IntrinsicScopedOperationalPresheafReadback
open IntrinsicScopedOperationalPresheafEquations
open IntrinsicScopedOperationalPresheafRulePoints
open IntrinsicScopedOperationalPresheafBoundContexts
open IntrinsicScopedLocalPolynomial (LocalRule Instance childJudgment)

universe u v
variable {S : Signature}

private theorem stage_liftEnvironment_value
    {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
    (M : CategoricalBindingModel.Model S D) {Z W : D} {Ξ Γ : Ctx S}
    (close : Environment S (M.stage Z).substitution.Carrier Ξ Γ)
    (m : W ⟶ Z) (ρ : M.Env W Γ) (bs : Ctx S) :
    M.envValue ((M.stage Z).substitution.liftEnvironment close bs)
        (M.ctx bs ⊗ W) (snd _ _ ≫ m) (M.extendEnv bs ρ) =
      M.extendEnv bs (M.envValue close W m ρ) := by
  funext s var
  have lifted := restrict_liftEnvironment ⟨[]⟩ (M.stageKripke Z) close bs
  exact (congrArg
    (fun env : Environment S (M.stage Z).substitution.Carrier (bs ++ Ξ) (bs ++ Γ) =>
      (env s var).value (M.ctx bs ⊗ W) (snd _ _ ≫ m) (M.extendEnv bs ρ)) lifted).trans
        (M.liftEnvironment_value close W m ρ bs var)

/-- The generalized closing environment below any premise binders reads the
original capture-avoiding lift of the actual point's closing values. -/
theorem closing_underBinders_point (A : BindingCloneAlgebra.Algebra.{u} S)
    {Z W : target A} {Ξ Γ : Ctx S}
    (close : Environment S ((model A).stage Z).substitution.Carrier Ξ Γ)
    (m : W ⟶ Z) (ρ : (model A).Env W Γ) (bs : Ctx S)
    (X : Base A) (w : W.obj X) :
    readEnv A
        ((model A).envValue (((model A).stage Z).substitution.liftEnvironment close bs)
          ((model A).ctx bs ⊗ W) (snd _ _ ≫ m) ((model A).extendEnv bs ρ))
        (extendedStage A bs X) (canonicalPoint A bs X w) =
      A.substitution.liftEnvironment
        (readEnv A ((model A).envValue close W m ρ) X w) bs := by
  rw [stage_liftEnvironment_value]
  exact readEnv_extend_canonical A ((model A).envValue close W m ρ) bs X w

/-- Restaging a captured body at the canonical binder point substitutes
exactly the old ambient variables behind the new binder prefix. -/
theorem body_underBinders_point (A : BindingCloneAlgebra.Algebra.{u} S)
    {W : target A} {dependencies : Ctx S} {s : S.Srt}
    (body : (model A).ElemOver W dependencies s) (bs : Ctx S)
    (X : Base A) (w : W.obj X) :
    read A ((model A).restageElem (snd _ _) body)
        (extendedStage A bs X) (canonicalPoint A bs X w) =
      A.substitution.substitute
        (A.substitution.liftEnvironment
          (fun _ var => A.substitution.injectVar (weakenVar bs var)) dependencies)
        (read A body X w) := by
  rw [read_restage]
  let f : X ⟶ extendedStage A bs X := Quiver.Hom.op
    (sndProjection A.substitution.toClone
      (ContextObject.ofList A.substitution.toClone bs) X.unop)
  change read A body (extendedStage A bs X) (W.map f w) = _
  have moved := read_reindex A body f w
  exact moved.trans (congrArg
    (fun env => A.substitution.substitute env (read A body X w))
    ((fromPositions_extendScope A dependencies f.unop).trans
      (congrArg (fun env => A.substitution.liftEnvironment env dependencies)
        (fromPositions_snd A bs X))))

/-- A schema endpoint evaluated beneath arbitrary ordered premise binders is
the original contextual fold with weakened ambient values and lifted close. -/
theorem premise_term_point (A : BindingCloneAlgebra.Algebra.{u} S)
    {N : List (MetaArity S)} {Z : target A} {Γ Ξ : Ctx S}
    (body : SemanticContextualMetavariables.Valuation (M := N) ((model A).stage Z) Γ)
    (close : Environment S ((model A).stage Z).substitution.Carrier Ξ Γ)
    (bs : Ctx S) {s : S.Srt} (term : Term (withMetas S N) (bs ++ Ξ) s)
    (X : Base A) (point : ((model A).ctx Γ ⊗ Z).obj X) :
    programsAtEquiv A s (extendedStage A bs X)
        ((SemanticContextualMetavariables.interpretSchema ((model A).stage Z) body
          (SemanticContextualMetavariables.weakenEnvironment ((model A).stage Z) bs
            (fun _ var => ((model A).stage Z).substitution.injectVar var))
          (((model A).stage Z).substitution.liftEnvironment close bs) term).value
            ((model A).ctx bs ⊗ ((model A).ctx Γ ⊗ Z)) (snd _ _ ≫ snd _ _)
            ((model A).extendEnv bs ((model A).genericEnv Γ Z)) |>.app
              (extendedStage A bs X) (canonicalPoint A bs X point)) =
      SemanticContextualMetavariables.interpretSchema A
        (fun index => read A ((model A).captureBody (body index) (snd _ _)
          ((model A).genericEnv Γ Z)) X point)
        (SemanticContextualMetavariables.weakenEnvironment A bs
          (fun _ var => A.substitution.injectVar var))
    (A.substitution.liftEnvironment
          (readEnv A ((model A).envValue close _ (snd _ _)
            ((model A).genericEnv Γ Z)) X point) bs) term := by
  change (∀ index : Fin N.length,
    (model A).ElemOver Z ((N.get index).1 ++ Γ) (N.get index).2) at body
  have value := contextual_stage_value_point A body
    (SemanticContextualMetavariables.weakenEnvironment ((model A).stage Z) bs
      (fun _ var => ((model A).stage Z).substitution.injectVar var))
    (((model A).stage Z).substitution.liftEnvironment close bs)
    (snd _ _ ≫ snd _ _) ((model A).extendEnv bs ((model A).genericEnv Γ Z))
    term (extendedStage A bs X) (canonicalPoint A bs X point)
  have captured :
      (fun index => read A ((model A).captureBody (body index) (snd _ _ ≫ snd _ _)
        ((model A).envValue
          (SemanticContextualMetavariables.weakenEnvironment ((model A).stage Z) bs
            (fun _ var => ((model A).stage Z).substitution.injectVar var)) _
          (snd _ _ ≫ snd _ _) ((model A).extendEnv bs ((model A).genericEnv Γ Z))))
        (extendedStage A bs X) (canonicalPoint A bs X point)) =
      IntrinsicScopedConditionalSubstitution.substValuation A
        (fun _ var => A.substitution.injectVar (weakenVar bs var))
        (fun index => read A ((model A).captureBody (body index) (snd _ _)
          ((model A).genericEnv Γ Z)) X point) := by
    funext index
    rw [captureBody_underBinders]
    exact body_underBinders_point A _ bs X point
  rw [captured, closing_underBinders_point] at value
  have post := IntrinsicScopedConditionalSubstitution.interpretSchema_postAmbient A
    (fun _ var => A.substitution.injectVar var)
    (fun _ var => A.substitution.injectVar (weakenVar bs var))
    (fun index => read A ((model A).captureBody (body index) (snd _ _)
      ((model A).genericEnv Γ Z)) X point)
    (A.substitution.liftEnvironment
      (readEnv A ((model A).envValue close _ (snd _ _) ((model A).genericEnv Γ Z)) X point) bs)
    term
  have ambient : SemanticContextualMetavariables.weakenEnvironment A bs
      (fun _ var => A.substitution.injectVar var :
        Environment S A.substitution.Carrier X.unop.context X.unop.context) =
      (fun _ var => A.substitution.injectVar (weakenVar bs var)) := by
    funext t var
    exact A.substitution.substitute_var _ var
  exact value.trans (by
    rw [ambient]
    simpa only [extendedStage, concat, ContextObject.ofList,
      A.substitution.substitute_identity] using post.symm)

/-- Every authored premise position retains its complete ordered binder
context, declared sort, and both actual child endpoints at the canonical point. -/
theorem pointInstance_child (R : List (LocalRule S))
    {A : BindingCloneAlgebra.Algebra.{u} S} {Z : target A}
    (occurrence : Instance R ((model A).stage Z))
    (position : Fin (R.get occurrence.index).2.premises.length)
    (X : Base A) (point : (occurrenceStage R occurrence).obj X) :
    let bs := ((R.get occurrence.index).2.premises.get position).binders
    (⟨bs ++ X.unop.context,
      (childJudgment R ((model A).stage Z) occurrence position).2.1,
      programsAtEquiv A _ (extendedStage A bs X)
        (((childJudgment R ((model A).stage Z) occurrence position).2.2.1).value
          ((model A).ctx bs ⊗ occurrenceStage R occurrence) (snd _ _ ≫ snd _ _)
          ((model A).extendEnv bs ((model A).genericEnv occurrence.ambient Z)) |>.app
            (extendedStage A bs X) (canonicalPoint A bs X point)),
      programsAtEquiv A _ (extendedStage A bs X)
        (((childJudgment R ((model A).stage Z) occurrence position).2.2.2).value
          ((model A).ctx bs ⊗ occurrenceStage R occurrence) (snd _ _ ≫ snd _ _)
          ((model A).extendEnv bs ((model A).genericEnv occurrence.ambient Z)) |>.app
            (extendedStage A bs X) (canonicalPoint A bs X point))⟩ :
      AuthoredPositionedRulePolynomial.Judgment A) =
        childJudgment R A (pointInstance R occurrence X point) position := by
  let premise := (R.get occurrence.index).2.premises.get position
  have source := premise_term_point A occurrence.valuation occurrence.close premise.binders
    premise.source X point
  have target := premise_term_point A occurrence.valuation occurrence.close premise.binders
    premise.target X point
  exact congrArg
    (fun pair => (⟨premise.binders ++ X.unop.context, premise.sort, pair⟩ :
      AuthoredPositionedRulePolynomial.Judgment A)) (Prod.ext source target)

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafPremisePoints
