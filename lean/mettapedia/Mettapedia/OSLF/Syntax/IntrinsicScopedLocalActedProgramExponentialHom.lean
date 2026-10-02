import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramExponential

/-!
# Selected binder arrows at operational classifier stages

The correspondence abstracts ordinary variables to fresh nullary declarations,
uses the actual parameter product comparison, and restores them after changing
stage. It applies to stages carrying event variables and all equation-class
assignments, including assignments which identify metavariables.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open SecondOrderContext SecondOrderVariableAbstraction
open IntrinsicScopedLocalPolynomial IntrinsicScopedLocalActedClassifier

variable {S : Signature} {K : List (MetaArity S)} (equations : List (EqAxiom S K))

/-- Ordinary-context arrows are exactly closed arrows after fresh-parameter
extension, in the actual contextual authored quotient. -/
def abstractionHomEquiv (X : Base equations) (Γ : Ctx S) (s : S.Srt) :
    (X ⟶ (authoredEquationPresentation S equations).quotientFunctor.obj (single S Γ s)) ≃
      ((parameterExtension equations Γ).obj X ⟶
        (authoredEquationPresentation S equations).quotientFunctor.obj (single S [] s)) :=
  (equationTermsRepresented (authoredEquationPresentation S equations) X.as Γ s).trans
    ((variablesQuotientEquiv equations Γ X.as.arities s).trans
      (equationTermsRepresented (authoredEquationPresentation S equations)
        ⟨extendedMetas Γ X.as.arities⟩ [] s).symm)

/-- The abstraction correspondence respects every quotient assignment. -/
theorem abstractionHomEquiv_precompose {X Y : Base equations}
    (f : X ⟶ Y) (Γ : Ctx S) (s : S.Srt)
    (g : Y ⟶ (authoredEquationPresentation S equations).quotientFunctor.obj (single S Γ s)) :
    abstractionHomEquiv equations X Γ s (f ≫ g) =
      (parameterExtension equations Γ).map f ≫ abstractionHomEquiv equations Y Γ s g := by
  induction f using Quot.ind with
  | _ f =>
    induction g using Quot.ind with
    | _ g =>
      apply (equationTermsRepresented (authoredEquationPresentation S equations)
        ⟨extendedMetas Γ X.as.arities⟩ [] s).injective
      change variablesQuotientEquiv equations Γ X.as.arities s
          (substituteTermClass (authoredEquationPresentation S equations) f
            (equationTermsRepresented (authoredEquationPresentation S equations) Y.as Γ s
              ((authoredEquationPresentation S equations).quotientFunctor.map g))) =
        substituteTermClass (authoredEquationPresentation S equations) (liftAssignment Γ f)
          (variablesQuotientEquiv equations Γ Y.as.arities s
            (equationTermsRepresented (authoredEquationPresentation S equations) Y.as Γ s
              ((authoredEquationPresentation S equations).quotientFunctor.map g)))
      exact variablesQuotientEquiv_natural equations Γ s f _

/-- The inverse abstraction correspondence also respects all assignments. -/
theorem abstractionHomEquiv_symm_precompose {X Y : Base equations}
    (f : X ⟶ Y) (Γ : Ctx S) (s : S.Srt)
    (g : (parameterExtension equations Γ).obj Y ⟶
      (authoredEquationPresentation S equations).quotientFunctor.obj (single S [] s)) :
    (abstractionHomEquiv equations X Γ s).symm ((parameterExtension equations Γ).map f ≫ g) =
      f ≫ (abstractionHomEquiv equations Y Γ s).symm g := by
  apply (abstractionHomEquiv equations X Γ s).injective
  rw [Equiv.apply_symm_apply, abstractionHomEquiv_precompose, Equiv.apply_symm_apply]

/-- Precomposition along the actual product comparison is an equivalence. -/
def parameterProductHomEquiv (X : Base equations) (Γ : Ctx S) (T : Base equations) :
    (X ⨯ parameterContext equations Γ ⟶ T) ≃
      ((parameterExtension equations Γ).obj X ⟶ T) where
  toFun f := (extensionProductIso equations Γ X).hom ≫ f
  invFun f := (extensionProductIso equations Γ X).inv ≫ f
  left_inv f := by simp only [Iso.inv_hom_id_assoc]
  right_inv f := by simp only [Iso.hom_inv_id_assoc]

/-- Selected binder arrows over a stage are the arrows out of its actual
product with the ordinary parameter context. -/
def baseSelectedBinderHomEquiv (X : Base equations) (Γ : Ctx S) (s : S.Srt) :
    (X ⨯ parameterContext equations Γ ⟶
      (authoredEquationPresentation S equations).quotientFunctor.obj (single S [] s)) ≃
      (X ⟶ (authoredEquationPresentation S equations).quotientFunctor.obj (single S Γ s)) :=
  (parameterProductHomEquiv equations X Γ _).trans
    (abstractionHomEquiv equations X Γ s).symm

/-- Changing a program stage commutes with selected binder abstraction. -/
theorem baseSelectedBinderHomEquiv_precompose {X Y : Base equations}
    (f : X ⟶ Y) (Γ : Ctx S) (s : S.Srt)
    (g : Y ⨯ parameterContext equations Γ ⟶
      (authoredEquationPresentation S equations).quotientFunctor.obj (single S [] s)) :
    baseSelectedBinderHomEquiv equations X Γ s (prod.map f (𝟙 _) ≫ g) =
      f ≫ baseSelectedBinderHomEquiv equations Y Γ s g := by
  change (abstractionHomEquiv equations X Γ s).symm
      ((extensionProductIso equations Γ X).hom ≫ prod.map f (𝟙 _) ≫ g) =
    f ≫ (abstractionHomEquiv equations Y Γ s).symm
      ((extensionProductIso equations Γ Y).hom ≫ g)
  rw [← Category.assoc, ← extensionProductIso_natural, Category.assoc]
  exact abstractionHomEquiv_symm_precompose equations f Γ s _

variable (R : List (LocalRule S))

/-- The actual classifier arrows exhibit the selected binder power at every
operational stage, without discarding the source's event variables. -/
def selectedBinderHomEquiv (a : Classifier R equations) (Γ : Ctx S) (s : S.Srt) :
    (productWithProgram R equations a (parameterContext equations Γ) ⟶
      (programSection R equations).obj
        ((authoredEquationPresentation S equations).quotientFunctor.obj (single S [] s))) ≃
      (a ⟶ (programSection R equations).obj
        ((authoredEquationPresentation S equations).quotientFunctor.obj (single S Γ s))) :=
  (programHomEquiv R equations _ _).trans
    ((baseSelectedBinderHomEquiv equations a.base Γ s).trans
      (programHomEquiv R equations a _).symm)

/-- The map pairing a change of operational stage with the unchanged parameters. -/
def programParameterMap {a b : Classifier R equations} (f : a ⟶ b) (Γ : Ctx S) :
    productWithProgram R equations a (parameterContext equations Γ) ⟶
      productWithProgram R equations b (parameterContext equations Γ) :=
  programProductLift R equations (programProductFst R equations a _ ≫ f)
    (programProductSnd R equations a _)

/-- Parameter-stage maps have the expected actual paired program assignment. -/
theorem programParameterMap_base {a b : Classifier R equations}
    (f : a ⟶ b) (Γ : Ctx S) :
    (programParameterMap equations R f Γ).base = prod.map f.base (𝟙 _) := by
  rw [programParameterMap, programProductLift_base]
  change prod.lift (prod.fst ≫ f.base) prod.snd = prod.map f.base (𝟙 _)
  apply prod.hom_ext
  · simp only [prod.lift_fst, prod.map_fst]
  · simp only [prod.lift_snd, prod.map_snd, Category.comp_id]

/-- Selected binder abstraction is natural even when the change of stage
substitutes or identifies event variables and program metavariables. -/
theorem selectedBinderHomEquiv_precompose {a b : Classifier R equations}
    (f : a ⟶ b) (Γ : Ctx S) (s : S.Srt)
    (g : productWithProgram R equations b (parameterContext equations Γ) ⟶
      (programSection R equations).obj
        ((authoredEquationPresentation S equations).quotientFunctor.obj (single S [] s))) :
    selectedBinderHomEquiv equations R a Γ s
        (programParameterMap equations R f Γ ≫ g) =
      f ≫ selectedBinderHomEquiv equations R b Γ s g := by
  apply (programHomEquiv R equations a _).injective
  change baseSelectedBinderHomEquiv equations a.base Γ s
      ((programParameterMap equations R f Γ).base ≫ g.base) =
    f.base ≫ baseSelectedBinderHomEquiv equations b.base Γ s g.base
  rw [programParameterMap_base]
  exact baseSelectedBinderHomEquiv_precompose equations f.base Γ s g.base

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
