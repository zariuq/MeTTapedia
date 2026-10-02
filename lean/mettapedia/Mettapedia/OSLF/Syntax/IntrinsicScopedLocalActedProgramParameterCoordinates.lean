import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramExponential
import Mettapedia.OSLF.Syntax.SecondOrderVariableAbstractionEvaluation
import Mettapedia.OSLF.Syntax.CategoricalBindingPreservation

/-!
# Coordinates of the actual fresh-parameter product comparison

The parameter adapter preserves the old program context and each newly
introduced nullary coordinate. These are the assignment equations needed to
read selected exponential evaluation as ordinary capture-avoiding substitution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Functor
open SecondOrderContext SecondOrderVariableAbstraction IntrinsicScopedLocalActedClassifier
open CategoricalBindingModel

variable {S : Signature} {K : List (MetaArity S)} (equations : List (EqAxiom S K))

/-- The recursively chosen adapter retains the old stage coordinate. -/
theorem extensionProductIso_cons_stage (a : S.Srt) (Γ : Ctx S) (X : Base equations) :
    (extensionProductIso equations (a :: Γ) X).hom ≫ prod.fst =
      (extensionProductIso equations Γ ((parameterExtension equations [a]).obj X)).hom ≫
        prod.fst ≫ (headParameterIso equations a X).hom ≫ prod.snd := by
  change ((𝟙 ((parameterExtension equations Γ).obj ((parameterExtension equations [a]).obj X)) ≫
      (parameterProductNatIso equations Γ).hom.app ((parameterExtension equations [a]).obj X) ≫
      prod.map (𝟙 _) (headParameterIso equations a X).hom ≫
      (_root_.CategoryTheory.Limits.prod.associator _ _ _).inv) ≫ (prod.braiding _ _).hom) ≫ prod.fst =
    ((parameterProductNatIso equations Γ).hom.app
      ((parameterExtension equations [a]).obj X) ≫
      (prod.braiding _ _).hom) ≫ prod.fst ≫ (headParameterIso equations a X).hom ≫ prod.snd
  simp only [prod.braiding_hom, prod.associator_inv, Category.assoc, prod.lift_fst, prod.lift_snd, prod.lift_fst_assoc,
    prod.map_snd_assoc, Category.id_comp]

/-- The adapter retains the newest ordinary parameter as its head coordinate. -/
theorem extensionProductIso_cons_head (a : S.Srt) (Γ : Ctx S) (X : Base equations) :
    (extensionProductIso equations (a :: Γ) X).hom ≫ prod.snd ≫ prod.snd =
      (extensionProductIso equations Γ ((parameterExtension equations [a]).obj X)).hom ≫
        prod.fst ≫ (headParameterIso equations a X).hom ≫ prod.fst := by
  change ((𝟙 ((parameterExtension equations Γ).obj ((parameterExtension equations [a]).obj X)) ≫
      (parameterProductNatIso equations Γ).hom.app ((parameterExtension equations [a]).obj X) ≫
      prod.map (𝟙 _) (headParameterIso equations a X).hom ≫
      (_root_.CategoryTheory.Limits.prod.associator _ _ _).inv) ≫ (prod.braiding _ _).hom) ≫ prod.snd ≫ prod.snd =
    ((parameterProductNatIso equations Γ).hom.app
      ((parameterExtension equations [a]).obj X) ≫
      (prod.braiding _ _).hom) ≫ prod.fst ≫ (headParameterIso equations a X).hom ≫ prod.fst
  simp only [prod.braiding_hom, prod.associator_inv, Category.assoc, prod.lift_snd, prod.lift_fst_assoc,
    prod.lift_snd_assoc, prod.map_snd_assoc, Category.id_comp]

/-- The adapter retains all previously introduced ordinary parameter coordinates. -/
theorem extensionProductIso_cons_tail (a : S.Srt) (Γ : Ctx S) (X : Base equations) :
    (extensionProductIso equations (a :: Γ) X).hom ≫ prod.snd ≫ prod.fst =
      (extensionProductIso equations Γ ((parameterExtension equations [a]).obj X)).hom ≫
        prod.snd := by
  change ((𝟙 ((parameterExtension equations Γ).obj ((parameterExtension equations [a]).obj X)) ≫
      (parameterProductNatIso equations Γ).hom.app ((parameterExtension equations [a]).obj X) ≫
      prod.map (𝟙 _) (headParameterIso equations a X).hom ≫
      (_root_.CategoryTheory.Limits.prod.associator _ _ _).inv) ≫ (prod.braiding _ _).hom) ≫ prod.snd ≫ prod.fst =
    ((parameterProductNatIso equations Γ).hom.app
      ((parameterExtension equations [a]).obj X) ≫
      (prod.braiding _ _).hom) ≫ prod.snd
  simp only [prod.braiding_hom, prod.associator_inv, Category.assoc, prod.lift_fst, prod.lift_snd, prod.map_fst, prod.lift_fst_assoc,
    prod.lift_snd_assoc, Category.comp_id, Category.id_comp]

/-- Inclusion of the old declarations through the actual fresh-parameter extension. -/
def oldParameterProjection : (Γ : Ctx S) → (X : Object S) →
    (⟨extendedMetas Γ X.arities⟩ : Object S) ⟶ X
  | [], X => 𝟙 X
  | a :: Γ, X => oldParameterProjection Γ ⟨headMetas a X.arities⟩ ≫
      secondProjection S (single S [] a) X

/-- The stage coordinate of the adapter is exactly the retained old assignment. -/
theorem extensionProductIso_stage (Γ : Ctx S) (X : Base equations) :
    (extensionProductIso equations Γ X).hom ≫ prod.fst =
      (authoredEquationPresentation S equations).quotientFunctor.map
        (oldParameterProjection Γ X.as) := by
  induction Γ generalizing X with
  | nil =>
      change ((prod.leftUnitor X).inv ≫ (prod.braiding _ _).hom) ≫ prod.fst =
        (authoredEquationPresentation S equations).quotientFunctor.map (𝟙 X.as)
      simp only [prod.braiding_hom, prod.leftUnitor_inv, Category.assoc, prod.lift_fst,
        prod.lift_snd]
      exact ((authoredEquationPresentation S equations).quotientFunctor.map_id X.as).symm
  | cons a Γ ih =>
      rw [extensionProductIso_cons_stage, ← Category.assoc, ih]
      change (authoredEquationPresentation S equations).quotientFunctor.map
          (oldParameterProjection Γ (⟨headMetas a X.as.arities⟩ : Object S)) ≫
        (headParameterIso equations a X).hom ≫ prod.snd = _
      rw [headParameterIso_snd]
      exact ((authoredEquationPresentation S equations).quotientFunctor.map_comp _ _).symm

/-- Abstraction of a closed body placed in an ordinary context only shifts
its old declarations. -/
theorem abstractHead_closedBody {M : List (MetaArity S)} (a : S.Srt) (Γ : Ctx S)
    {s : S.Srt} (term : Term (withMetas S M) [] s) :
    abstractHead (bind (emptyEnvironment (withMetas S M) (a :: Γ)) term) =
      bind (emptyEnvironment (withMetas S (headMetas a M)) Γ) (shift a term) := by
  unfold abstractHead shift
  rw [instInto_bind, bind_comp]
  congr 1
  funext r v
  nomatch v

/-- Full abstraction of a closed body placed in an ordinary context retains
exactly its old assignment, including occurrences under local binders. -/
theorem abstractVars_closedBody (Γ : Ctx S) (X : Object S)
    {s : S.Srt} (term : Term (withMetas S X.arities) [] s) :
    abstractVars (bind (emptyEnvironment (withMetas S X.arities) Γ) term) =
      instInto (oldParameterProjection Γ X) term := by
  induction Γ generalizing X with
  | nil =>
      have empty : emptyEnvironment (withMetas S X.arities) [] =
          (fun r v => Term.var (S := withMetas S X.arities) v) := by
        funext r v
        nomatch v
      change bind (emptyEnvironment (withMetas S X.arities) []) term = instInto (𝟙 X) term
      rw [empty, bind_id]
      exact (instInto_metaVar_id term).symm
  | cons a Γ ih =>
      change abstractVars (abstractHead (bind (emptyEnvironment (withMetas S X.arities) (a :: Γ)) term)) = _
      rw [abstractHead_closedBody, ih]
      exact (instInto_instInto (shiftAssignment a)
        (oldParameterProjection Γ ⟨headMetas a X.arities⟩) term)

/-- Each ordinary variable's actual parameter-product coordinate. -/
def parameterVariable : ∀ {Γ : Ctx S} {s : S.Srt}, Var Γ s →
    (parameterContext equations Γ ⟶
      (authoredEquationPresentation S equations).quotientFunctor.obj (single S [] s))
  | _, _, .zero => prod.snd
  | _, _, .succ v => prod.fst ≫ parameterVariable v

/-- Every ordinary parameter coordinate is exactly the corresponding fresh
nullary metavariable produced by actual variable abstraction. -/
theorem extensionProductIso_variable (X : Base equations) :
    ∀ {Γ : Ctx S} {s : S.Srt} (v : Var Γ s),
      (extensionProductIso equations Γ X).hom ≫ prod.snd ≫ parameterVariable equations v =
        (authoredEquationPresentation S equations).quotientFunctor.map
          (termArrow (abstractVars (Term.var (S := withMetas S X.as.arities) v)))
  | a :: Γ, _, .zero => by
      change (extensionProductIso equations (a :: Γ) X).hom ≫ prod.snd ≫ prod.snd = _
      rw [extensionProductIso_cons_head, ← Category.assoc, extensionProductIso_stage]
      change (authoredEquationPresentation S equations).quotientFunctor.map
          (oldParameterProjection Γ (⟨headMetas a X.as.arities⟩ : Object S)) ≫
        (headParameterIso equations a X).hom ≫ prod.fst = _
      rw [headParameterIso_fst, ← Functor.map_comp]
      apply congrArg (authoredEquationPresentation S equations).quotientFunctor.map
      apply (termsRepresented S ⟨extendedMetas Γ (headMetas a X.as.arities)⟩ [] a).injective
      change instInto (oldParameterProjection Γ ⟨headMetas a X.as.arities⟩)
          (fresh (M := X.as.arities) a []) = abstractVars (fresh (M := X.as.arities) a Γ)
      exact (abstractVars_closedBody Γ (⟨headMetas a X.as.arities⟩ : Object S)
        (fresh (M := X.as.arities) a [])).symm
  | a :: Γ, s, .succ v => by
      have tail := congrArg (fun h :
          (parameterExtension equations (a :: Γ)).obj X ⟶ parameterContext equations Γ =>
        h ≫ parameterVariable equations v)
        (extensionProductIso_cons_tail equations a Γ X)
      have combined : (extensionProductIso equations (a :: Γ) X).hom ≫ prod.snd ≫
          prod.fst ≫ parameterVariable equations v =
        (extensionProductIso equations Γ ((parameterExtension equations [a]).obj X)).hom ≫
          prod.snd ≫ parameterVariable equations v := by
        simpa only [Category.assoc] using tail
      exact combined.trans
        (extensionProductIso_variable ((parameterExtension equations [a]).obj X) v)

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
