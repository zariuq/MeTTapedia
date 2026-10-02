import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafRuleStagePoints
import Mettapedia.OSLF.Syntax.BoundPrefixProjection

/-!
# Rule occurrences commute with actual contextual substitutions

Substituting each complete declared body beneath its dependency prefix agrees
with evaluating the original occurrence through its actual context arrow.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafRuleSubstitutionPoints

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open CategoricalBindingModel BindingSubstitutionAlgebra SecondOrderContext
open IntrinsicScopedConditionalPresheaf (Base programs programsAtEquiv)
open IntrinsicScopedOperationalPresheafPrograms (target model)
open IntrinsicScopedOperationalPresheafReadback (read read_restage)
open IntrinsicScopedOperationalPresheafRulePoints
open IntrinsicScopedOperationalPresheafRuleStagePoints
open IntrinsicScopedOperationalPresheafSubstitution
open IntrinsicScopedLocalPolynomial (LocalRule Instance)

universe u v
variable {S : Signature}

section Generic

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable (M : Model S D)

private abbrev joinedEnv {W : D} {bs Γ : Ctx S}
    (arguments : M.Env W bs) (ambient : M.Env W Γ) : M.Env W (bs ++ Γ) :=
  SemanticContextualMetavariables.joinEnvironment
    (F := fun _ s => W ⟶ M.sort s) (Δ := []) arguments ambient

private theorem extendEnv_prefix {W : D} :
    ∀ (bs : Ctx S) {Γ : Ctx S} (ρ : M.Env W Γ) {s : S.Srt} (var : Var bs s),
      M.extendEnv bs ρ s (injPrefix (Γ := Γ) bs var) = fst _ _ ≫ projectVar M.sort var
  | _ :: _, _, _, _, .zero => rfl
  | _ :: bs, _, ρ, _, .succ var => by
      change lift (fst _ _ ≫ snd _ _) (snd _ _) ≫
        M.extendEnv bs ρ _ (injPrefix bs var) = fst _ _ ≫ snd _ _ ≫ projectVar M.sort var
      rw [extendEnv_prefix, lift_fst_assoc, Category.assoc]

/-- The ordered environment extension is the shared environment join of the
actual new projections with the old values through the ambient projection. -/
theorem extendEnv_joined {W : D} {Γ : Ctx S} (bs : Ctx S) (ambient : M.Env W Γ) :
    joinedEnv M (M.genericEnv bs W) (M.restage (snd _ _) ambient) =
      M.extendEnv bs ambient := by
  funext s var
  have recombine := splitVar_recombine bs var
  cases found : splitVar bs var with
  | inl bound =>
      simp only [found, Sum.elim_inl] at recombine
      rw [← recombine]
      exact (BindingContextualEquationInterpretation.joinEnvironment_prefix
        (F := fun _ t => M.ctx bs ⊗ W ⟶ M.sort t) (Δ := []) bs
        (M.genericEnv bs W) (M.restage (snd _ _) ambient) s bound).trans
          (extendEnv_prefix M bs ambient bound).symm
  | inr old =>
      simp only [found, Sum.elim_inr] at recombine
      rw [← recombine]
      exact (BindingContextualEquationInterpretation.joinEnvironment_ambient
        (F := fun _ t => M.ctx bs ⊗ W ⟶ M.sort t) (Δ := []) bs
        (M.genericEnv bs W) (M.restage (snd _ _) ambient) s old).trans
          (M.extendEnv_old bs ambient old).symm

/-- The generic value of a captured body uses the actual ordered extension
of its ambient values beside the dependency projections. -/
theorem captureBody_elemValue {Z W : D} {dependencies Γ : Ctx S} {s : S.Srt}
    (body : M.ElemOver Z (dependencies ++ Γ) s) (m : W ⟶ Z) (ambient : M.Env W Γ) :
    M.elemValue (M.captureBody body m ambient) =
      body.value (M.ctx dependencies ⊗ W) (snd _ _ ≫ m) (M.extendEnv dependencies ambient) := by
  change body.value _ (snd _ _ ≫ m)
    (joinedEnv M (M.genericEnv dependencies W) (M.restage (snd _ _) ambient)) = _
  rw [extendEnv_joined]

/-- The actual stage lift evaluates to the existing categorical environment
extension below its declared ordered binder list. -/
theorem envValue_stageLift {Z W : D} {Γ Δ : Ctx S}
    (σ : Environment S (M.stage Z).substitution.Carrier Γ Δ)
    (m : W ⟶ Z) (ρ : M.Env W Δ) (bs : Ctx S) :
    M.envValue ((M.stage Z).substitution.liftEnvironment σ bs)
        (M.ctx bs ⊗ W) (snd _ _ ≫ m) (M.extendEnv bs ρ) =
      M.extendEnv bs (M.envValue σ W m ρ) := by
  funext s var
  have lifted := restrict_liftEnvironment ⟨[]⟩ (M.stageKripke Z) σ bs
  exact (congrArg
    (fun env : Environment S (M.stage Z).substitution.Carrier (bs ++ Γ) (bs ++ Δ) =>
      (env s var).value (M.ctx bs ⊗ W) (snd _ _ ≫ m) (M.extendEnv bs ρ)) lifted).trans
        (M.liftEnvironment_value σ W m ρ bs var)

/-- The context substitution arrow reads each actual substituted ambient
value in the original generic ordinary environment. -/
theorem substitutionArrow_environment {Z : D} {Γ Δ : Ctx S}
    (σ : Environment S (M.stage Z).substitution.Carrier Γ Δ) :
    M.restage (substitutionArrow M σ) (M.genericEnv Γ Z) =
      M.envValue σ (M.ctx Δ ⊗ Z) (snd _ _) (M.genericEnv Δ Z) := by
  funext s var
  exact substitutionArrow_coordinate M σ var

/-- Capturing a body substituted beneath its complete dependency prefix is
restaging the original captured body along the actual context substitution. -/
theorem captureBody_substitution {Z : D} {dependencies Γ Δ : Ctx S} {s : S.Srt}
    (σ : Environment S (M.stage Z).substitution.Carrier Γ Δ)
    (body : M.ElemOver Z (dependencies ++ Γ) s) :
    M.captureBody ((M.stage Z).substitution.substitute
        ((M.stage Z).substitution.liftEnvironment σ dependencies) body)
        (snd _ _) (M.genericEnv Δ Z) =
      M.restageElem (substitutionArrow M σ)
        (M.captureBody body (snd _ _) (M.genericEnv Γ Z)) := by
  change Environment S (M.ElemOver Z) Γ Δ at σ
  let substituted : M.ElemOver Z (dependencies ++ Δ) s :=
    (M.stage Z).substitution.substitute
      ((M.stage Z).substitution.liftEnvironment σ dependencies) body
  let first := M.captureBody substituted (snd _ _) (M.genericEnv Δ Z)
  let second := M.restageElem (substitutionArrow M σ)
    (M.captureBody body (snd _ _) (M.genericEnv Γ Z))
  have generic : M.elemValue first = M.elemValue second := by
    change M.elemValue (M.captureBody substituted (snd _ _) (M.genericEnv Δ Z)) =
      M.elemValue (M.restageElem (substitutionArrow M σ)
        (M.captureBody body (snd _ _) (M.genericEnv Γ Z)))
    rw [captureBody_elemValue, Model.elemValue, genericValue_stageRestage]
    change substituted.value _ (snd _ _ ≫ snd _ _)
      (M.extendEnv dependencies (M.genericEnv Δ Z)) =
        (M.ctx dependencies ◁ substitutionArrow M σ) ≫
          M.elemValue (M.captureBody body (snd _ _) (M.genericEnv Γ Z))
    rw [captureBody_elemValue]
    change body.value _ (snd _ _ ≫ snd _ _)
      (M.envValue ((M.stage Z).substitution.liftEnvironment σ dependencies) _
        (snd _ _ ≫ snd _ _) (M.extendEnv dependencies (M.genericEnv Δ Z))) = _
    have lifted := envValue_stageLift M σ (snd _ _) (M.genericEnv Δ Z) dependencies
    have left := congrArg
      (fun env : M.Env (M.ctx dependencies ⊗ (M.ctx Δ ⊗ Z)) (dependencies ++ Γ) =>
        body.value _ (snd _ _ ≫ snd _ _) env) lifted
    have right := body.natural (M.ctx dependencies ◁ substitutionArrow M σ)
      (snd _ _ ≫ snd _ _) (M.extendEnv dependencies (M.genericEnv Γ Z))
    have ambient := substitutionArrow_environment M σ
    rw [← M.extendEnv_restage, ambient, whiskerLeft_snd_assoc, substitutionArrow_snd] at right
    exact left.trans right
  apply Model.ElemOver.ext
  funext U point arguments
  exact (M.value_eq_generic first U point arguments).trans
    ((congrArg (lift (M.tupleEnv arguments) point ≫ ·) generic).trans
      (M.value_eq_generic second U point arguments).symm)

end Generic

variable {A : BindingCloneAlgebra.Algebra.{u} S}
variable (R : List (LocalRule S))

/-- Each complete declared body below contextual substitution is the old
captured value read at the actual substituted context point. -/
theorem pointInstance_valuation_substitution {Z : target A}
    (occurrence : Instance R ((model A).stage Z)) {Δ : Ctx S}
    (σ : Environment S ((model A).stage Z).substitution.Carrier occurrence.ambient Δ)
    (X : Base A) (point : ((model A).ctx Δ ⊗ Z).obj X)
    (index : Fin (R.get occurrence.index).1.length) :
    (pointInstance R (Instance.subst R occurrence σ) X point).valuation index =
      (pointInstance R occurrence X ((substitutionArrow (model A) σ).app X point)).valuation index := by
  have captured := captureBody_substitution (model A) σ (occurrence.valuation index)
  have coordinate := congrArg
    (fun value : (model A).ElemOver ((model A).ctx Δ ⊗ Z)
      (((R.get occurrence.index).1.get index).1) (((R.get occurrence.index).1.get index).2) =>
        read A value X point) captured
  exact coordinate.trans (read_restage A (substitutionArrow (model A) σ) _ X point)

/-- The complete closing environment below contextual substitution reads the
original closing values through the actual context substitution arrow. -/
theorem pointInstance_close_substitution {Z : target A}
    (occurrence : Instance R ((model A).stage Z)) {Δ : Ctx S}
    (σ : Environment S ((model A).stage Z).substitution.Carrier occurrence.ambient Δ)
    (X : Base A) (point : ((model A).ctx Δ ⊗ Z).obj X) :
    (pointInstance R (Instance.subst R occurrence σ) X point).close =
      (pointInstance R occurrence X ((substitutionArrow (model A) σ).app X point)).close := by
  funext s var
  have coordinate := substitutionArrow_value (model A) σ (occurrence.close s var)
  exact congrArg
    (fun f : (model A).ctx Δ ⊗ Z ⟶ programs A s => programsAtEquiv A s X (f.app X point))
    coordinate

/-- The actual whole point occurrence commutes with contextual substitution,
retaining its declaration, every complete contextual body, and all closing values. -/
theorem pointInstance_substitution {Z : target A}
    (occurrence : Instance R ((model A).stage Z)) {Δ : Ctx S}
    (σ : Environment S ((model A).stage Z).substitution.Carrier occurrence.ambient Δ)
    (X : Base A) (point : ((model A).ctx Δ ⊗ Z).obj X) :
    pointInstance R (Instance.subst R occurrence σ) X point =
      pointInstance R occurrence X ((substitutionArrow (model A) σ).app X point) := by
  have valuation :
      (pointInstance R (Instance.subst R occurrence σ) X point).valuation =
        (pointInstance R occurrence X ((substitutionArrow (model A) σ).app X point)).valuation := by
    funext index
    exact pointInstance_valuation_substitution R occurrence σ X point index
  have close := pointInstance_close_substitution R occurrence σ X point
  exact congrArg₂
    (fun valuation close => (⟨occurrence.index, X.unop.context, valuation, close⟩ : Instance R A))
    valuation close

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafRuleSubstitutionPoints
