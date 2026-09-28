import Mettapedia.GSLT.LanguageDef.MultiSortedCloneOperationPresheaf
import Mettapedia.OSLF.Syntax.BindingEquationContextExtension
import Mettapedia.OSLF.Syntax.ContextualEquationClassEvents
import Mettapedia.OSLF.Syntax.EquationExtensionEventGraph

/-!
# Equation-class terms as pulled-back representables

The existing equation-class term presheaf over intrinsic substitutions agrees,
after changing from typed substitutions to positional environments, with the
presheaf of operations in the authored equation clone. The latter is
represented by a singleton context. This comparison includes the actual
quotient-valued substitution action and the existing equation-extension map
on retained operational states.

The representation is over the quotient context category. Its pullback to
raw contexts is not a claim that the raw context category is cartesian closed
or that the full operational theory's classifying category has been built.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding

open CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.Binding.ContextualEquationClassEvents
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra

variable {S : Signature} {M : List (MetaArity S)}

/-- Quotient-clone substitution by equation classes of raw terms agrees with
the existing syntactic substitution action on those raw terms. -/
theorem quotientClone_substitute_eq_bindQ
    (E : List (EqAxiom S M)) {Γ Δ : Ctx S} {sort : S.Srt}
    (env : (i : Fin Γ.length) → Term S Δ (Γ.get i))
    (q : TermQ E Γ sort) :
    ((BindingEquationQuotientModel.algebra E).substitution.toClone).substitute q
      (fun i => (Quotient.mk _ (env i) : TermQ E Δ (Γ.get i))) =
        bindQ (substVar env) q := by
  change BindingEquationQuotientSubstitution.substitute E
    (fromPositions Γ (fun i => (Quotient.mk _ (env i) : TermQ E Δ (Γ.get i)))) q =
      bindQ (substVar env) q
  apply BindingEquationQuotientSubstitution.substitute_eq_bindQ E _ _ _ q
  intro s v
  have h := bindingHom_fromPositions
    (BindingEquationQuotientModel.projection E) Γ env v
  simp only [BindingEquationQuotientModel.projection] at h
  exact (congrArg (fun t : Term S Δ s => (Quotient.mk _ t : TermQ E Δ s))
    (fromPositions_terms_apply env v)).symm ▸ h

/-- The existing equation-class presheaf, pulled back to clone contexts, is
the operation presheaf of the quotient clone pulled back along the context
quotient. -/
noncomputable def termQPullbackIso
    (E : List (EqAxiom S M)) (sort : S.Srt) :
    (cloneContextToSyntactic S).op ⋙ termQPresheaf E sort ≅
      (termCloneToSemanticContextFunctor S ⋙ quotientContextFunctor E).op ⋙
        operationPresheaf
          ((BindingEquationQuotientModel.algebra E).substitution.toClone) sort where
  hom := {
    app X := TypeCat.ofHom id
    naturality X Y f := by
      apply ConcreteCategory.hom_ext
      intro q
      change bindQ (substVar f.unop) q =
        ((BindingEquationQuotientModel.algebra E).substitution.toClone).substitute q
          (fun i => (Quotient.mk _ (f.unop i) : TermQ E Y.unop.context
            (X.unop.context.get i)))
      exact (quotientClone_substitute_eq_bindQ E f.unop q).symm }
  inv := {
    app X := TypeCat.ofHom id
    naturality X Y f := by
      apply ConcreteCategory.hom_ext
      intro q
      change ((BindingEquationQuotientModel.algebra E).substitution.toClone).substitute q
          (fun i => (Quotient.mk _ (f.unop i) : TermQ E Y.unop.context
            (X.unop.context.get i))) = bindQ (substVar f.unop) q
      exact quotientClone_substitute_eq_bindQ E f.unop q }
  hom_inv_id := by ext X q; rfl
  inv_hom_id := by ext X q; rfl

/-- Equation-class programs over raw clone contexts are the pullback of a
representable presheaf on equation contexts. -/
noncomputable def termQAsPulledYonedaIso
    (E : List (EqAxiom S M)) (sort : S.Srt) :
    (cloneContextToSyntactic S).op ⋙ termQPresheaf E sort ≅
      (termCloneToSemanticContextFunctor S ⋙ quotientContextFunctor E).op ⋙
        yoneda.obj
          (ContextObject.ofList
            ((BindingEquationQuotientModel.algebra E).substitution.toClone)
            [sort]) :=
  (termQPullbackIso E sort) ≪≫
    Functor.isoWhiskerLeft
      (termCloneToSemanticContextFunctor S ⋙ quotientContextFunctor E).op
      (operationPresheafYonedaIso
        ((BindingEquationQuotientModel.algebra E).substitution.toClone) sort)

/-- The existing equation-extension map on state presheaves is the operation
map of the binding-clone comparison, at every raw context. -/
theorem compareStates_eq_operationNatural
    {E F : List (EqAxiom S M)}
    (includeAxiom : BindingEquationExtension.AxiomInclusion E F)
    (sort : S.Srt)
    (X : (ContextObject (termClone S))ᵒᵖ)
    (q : TermQ E X.unop.context sort) :
    (EquationExtensionEventGraph.compareStates includeAxiom sort).app
        ((cloneContextToSyntactic S).op.obj X) q =
      ((BindingEquationExtension.comparisonHom includeAxiom).toCloneTranslation
        |>.operationNatural sort).app
        ((quotientContextFunctor E).op.obj
          ((termCloneToSemanticContextFunctor S).op.obj X)) q := by
  exact EquationExtensionEventGraph.compareStates_eq_comparisonHom
    includeAxiom sort ((cloneContextToSyntactic S).op.obj X) q

end Mettapedia.OSLF.Binding
