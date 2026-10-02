import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedYonedaVariableMeaning
import Mettapedia.OSLF.Syntax.SecondOrderEquationModelNaturality

/-!
# Equation-class sections and partial ordinary substitution

Actual represented program sections are equation classes in their declared
ordinary context. The existing quotient clone supplies partial substitution,
including the ordinary variables retained beneath a local binder.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open CategoricalBindingModel SecondOrderContext
open IntrinsicScopedLocalPolynomial IntrinsicScopedLocalActedClassifier

universe w
variable {S : Signature} {K : List (MetaArity S)}
variable (R : List (LocalRule S)) (equations : List (EqAxiom S K))

/-- The genuine represented program section is the existing contextual
equation class, including at classifier stages carrying event variables. -/
def programClassEquiv (a : Classifier R equations) (Γ : Ctx S) (s : S.Srt) :
    (program.{w} R equations Γ s).obj (Opposite.op a) ≃
      TermQ ((authoredEquationPresentation S equations).axioms a.base.as) Γ s where
  toFun x := equationTermsRepresented (authoredEquationPresentation S equations)
    a.base.as Γ s ((programHomEquiv R equations a _).toFun x.down)
  invFun x := ULift.up ((programHomEquiv R equations a _).symm
    ((equationTermsRepresented (authoredEquationPresentation S equations)
      a.base.as Γ s).symm x))
  left_inv x := by
    apply ULift.ext
    have represented := (equationTermsRepresented (authoredEquationPresentation S equations)
      a.base.as Γ s).symm_apply_apply ((programHomEquiv R equations a _).toFun x.down)
    exact (congrArg (programHomEquiv R equations a _).symm represented).trans
      ((programHomEquiv R equations a _).symm_apply_apply x.down)
  right_inv x := by
    have assigned := (programHomEquiv R equations a _).apply_symm_apply
      ((equationTermsRepresented (authoredEquationPresentation S equations)
        a.base.as Γ s).symm x)
    exact (congrArg (equationTermsRepresented (authoredEquationPresentation S equations)
      a.base.as Γ s) assigned).trans
      ((equationTermsRepresented (authoredEquationPresentation S equations)
        a.base.as Γ s).apply_symm_apply x)

/-- Class reindexing is exactly the actual quotient binding-model map. -/
theorem equationTermsRepresented_precompose
    {X Y : Base equations} (f : X ⟶ Y) {Γ : Ctx S} {s : S.Srt}
    (g : Y ⟶ (authoredEquationPresentation S equations).quotientFunctor.obj
      (single S Γ s)) :
    equationTermsRepresented (authoredEquationPresentation S equations) X.as Γ s (f ≫ g) =
      (authoredEquationModelMapQuot S equations f).raw.map
        (equationTermsRepresented (authoredEquationPresentation S equations) Y.as Γ s g) := by
  induction f using Quot.ind with
  | _ f =>
    induction g using Quot.ind with
    | _ g => rfl

/-- The section-to-class comparison is natural for every classifier arrow,
without any injectivity condition on its program assignment. -/
theorem programClassEquiv_reindex {a b : Classifier R equations} (f : a ⟶ b)
    (Γ : Ctx S) (s : S.Srt)
    (x : (program.{w} R equations Γ s).obj (Opposite.op b)) :
    programClassEquiv R equations a Γ s ((program R equations Γ s).map f.op x) =
      (authoredEquationModelMapQuot S equations f.base).raw.map
        (programClassEquiv R equations b Γ s x) :=
  equationTermsRepresented_precompose equations f.base x.down.base

/-- Reading a generalized program element is natural in its arbitrary
presheaf stage and in every classifier restriction. -/
theorem programClassEquiv_arrow_reindex
    {Z : Presheaf.{w} R equations} {Γ : Ctx S} {s : S.Srt}
    (element : Z ⟶ program R equations Γ s)
    {a b : (Classifier R equations)ᵒᵖ} (f : a ⟶ b) (z : Z.obj a) :
    programClassEquiv R equations b.unop Γ s (element.app b (Z.map f z)) =
      (authoredEquationModelMapQuot S equations f.unop.base).raw.map
        (programClassEquiv R equations a.unop Γ s (element.app a z)) := by
  have natural := ConcreteCategory.congr_hom (element.naturality f) z
  exact (congrArg (programClassEquiv R equations b.unop Γ s) natural).trans
    (programClassEquiv_reindex R equations f.unop Γ s (element.app a z))

section PartialSubstitution

universe u v
variable {A : BindingCloneAlgebra.Algebra.{u} S}
variable {B : BindingCloneAlgebra.Algebra.{v} S}

/-- Model maps commute with a change of the ordinary context index. -/
theorem carrierMap_contextCast (h : FreeBindingClone.Hom A B)
    {Γ Δ : Ctx S} (same : Γ = Δ) {s : S.Srt} (x : A.substitution.Carrier Γ s) :
    h.raw.map (same ▸ x) = same ▸ h.raw.map x := by
  cases same
  rfl

/-- Lift a closed ordinary environment beneath an explicit binder list,
retaining that list as the output context. -/
def liftClosedEnvironment (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ : Ctx S}
    (environment : BindingSubstitutionAlgebra.Environment S A.substitution.Carrier Γ [])
    (bs : Ctx S) :
    BindingSubstitutionAlgebra.Environment S A.substitution.Carrier (bs ++ Γ) bs :=
  fun s v => (List.append_nil bs) ▸ A.substitution.liftEnvironment environment bs s v

/-- The retained-binder environment is natural in the binding model. -/
theorem liftClosedEnvironment_map (h : FreeBindingClone.Hom A B)
    {Γ : Ctx S}
    (environment : BindingSubstitutionAlgebra.Environment S A.substitution.Carrier Γ [])
    (bs : Ctx S) :
    (fun s v => h.raw.map (liftClosedEnvironment A environment bs s v)) =
      liftClosedEnvironment B (fun s v => h.raw.map (environment s v)) bs := by
  funext s v
  have mapped := congrFun (congrFun
    (SemanticContextualMetavariables.liftEnvironment_map h environment bs) s) v
  exact (carrierMap_contextCast h (List.append_nil bs) _).trans
    (congrArg (fun x : B.substitution.Carrier (bs ++ []) s =>
      (List.append_nil bs) ▸ x) mapped)

/-- Ordinary substitution fills only the ambient variables of a body and
retains the ordered local binder context. -/
def partialSubstitute (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ : Ctx S} (bs : Ctx S)
    (environment : BindingSubstitutionAlgebra.Environment S A.substitution.Carrier Γ [])
    {s : S.Srt} (body : A.substitution.Carrier (bs ++ Γ) s) :
    A.substitution.Carrier bs s :=
  A.substitution.substitute (liftClosedEnvironment A environment bs) body

/-- Contextual partial substitution is natural for every binding-model map. -/
theorem partialSubstitute_map (h : FreeBindingClone.Hom A B)
    {Γ : Ctx S} (bs : Ctx S)
    (environment : BindingSubstitutionAlgebra.Environment S A.substitution.Carrier Γ [])
    {s : S.Srt} (body : A.substitution.Carrier (bs ++ Γ) s) :
    h.raw.map (partialSubstitute A bs environment body) =
      partialSubstitute B bs (fun s v => h.raw.map (environment s v)) (h.raw.map body) := by
  unfold partialSubstitute
  rw [h.map_substitute, liftClosedEnvironment_map]

end PartialSubstitution

/-- Partially substitute an ordinary environment into a generalized
represented body. The remaining binder list stays explicit. -/
def partialSubstitutionMap {Z : Presheaf.{w} R equations}
    {Γ : Ctx S} (bs : Ctx S) {s : S.Srt}
    (body : Z ⟶ program R equations (bs ++ Γ) s)
    (environment : ∀ (r : S.Srt), Var Γ r → (Z ⟶ program R equations [] r)) :
    Z ⟶ program R equations bs s where
  app a := TypeCat.ofHom fun z => (programClassEquiv.{w} R equations a.unop bs s).symm
    (partialSubstitute (authoredEquationModelAt S equations a.unop.base.as).algebra bs
      (fun r v => programClassEquiv.{w} R equations a.unop [] r ((environment r v).app a z))
      (programClassEquiv.{w} R equations a.unop (bs ++ Γ) s (body.app a z)))
  naturality a b f := by
    apply ConcreteCategory.hom_ext
    intro z
    let A := (authoredEquationModelAt S equations a.unop.base.as).algebra
    let B := (authoredEquationModelAt S equations b.unop.base.as).algebra
    let h : FreeBindingClone.Hom A B :=
      authoredEquationModelMapQuot S equations f.unop.base
    let oldEnvironment : BindingSubstitutionAlgebra.Environment S A.substitution.Carrier Γ [] :=
      fun r v => programClassEquiv.{w} R equations a.unop [] r ((environment r v).app a z)
    let newEnvironment : BindingSubstitutionAlgebra.Environment S B.substitution.Carrier Γ [] :=
      fun r v => programClassEquiv.{w} R equations b.unop [] r
        ((environment r v).app b (Z.map f z))
    let oldBody : A.substitution.Carrier (bs ++ Γ) s :=
      programClassEquiv.{w} R equations a.unop (bs ++ Γ) s (body.app a z)
    let newBody : B.substitution.Carrier (bs ++ Γ) s :=
      programClassEquiv.{w} R equations b.unop (bs ++ Γ) s (body.app b (Z.map f z))
    have environmentEq : newEnvironment = fun r v => h.raw.map (oldEnvironment r v) := by
      funext r v
      exact programClassEquiv_arrow_reindex.{w} R equations (environment r v) f z
    have bodyEq : newBody = h.raw.map oldBody :=
      programClassEquiv_arrow_reindex.{w} R equations body f z
    have classes : partialSubstitute B bs newEnvironment newBody =
        h.raw.map (partialSubstitute A bs oldEnvironment oldBody) :=
      (congrArg₂ (fun
        (env : BindingSubstitutionAlgebra.Environment S B.substitution.Carrier Γ [])
        (term : B.substitution.Carrier (bs ++ Γ) s) => partialSubstitute B bs env term)
        environmentEq bodyEq).trans
        (partialSubstitute_map h bs oldEnvironment oldBody).symm
    apply (programClassEquiv.{w} R equations b.unop bs s).injective
    change (programClassEquiv.{w} R equations b.unop bs s)
        ((programClassEquiv.{w} R equations b.unop bs s).symm
          (partialSubstitute B bs newEnvironment newBody)) =
      (programClassEquiv.{w} R equations b.unop bs s)
        ((program R equations bs s).map f
          ((programClassEquiv.{w} R equations a.unop bs s).symm
            (partialSubstitute A bs oldEnvironment oldBody)))
    have reindex := programClassEquiv_reindex.{w} R equations f.unop bs s
      ((programClassEquiv.{w} R equations a.unop bs s).symm
        (partialSubstitute A bs oldEnvironment oldBody))
    have right := reindex.trans (congrArg h.raw.map
      ((programClassEquiv.{w} R equations a.unop bs s).apply_symm_apply
        (partialSubstitute A bs oldEnvironment oldBody)))
    exact ((programClassEquiv.{w} R equations b.unop bs s).apply_symm_apply _).trans
      (classes.trans right.symm)

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
