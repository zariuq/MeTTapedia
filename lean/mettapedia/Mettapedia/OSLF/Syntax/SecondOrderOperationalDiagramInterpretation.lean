import Mettapedia.OSLF.Syntax.SecondOrderOperationalPresheaf
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Coherent interpretation of context-indexed authored firing trees

The free rule-tree fold is compatible with every map of authored contexts.
Consequently an interpretation of the full diagram of free operational
models is equivalent to a natural interpretation of its binding-equation
base, not merely to unrelated maps at each context.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution

universe u v

/-- Free operational rule-tree generation is an adjunction on whole
context-indexed diagrams, so its fold is coherent under diagram maps as
well as under each individual substitution. -/
noncomputable def operationalDiagramAdjunction
    (C : Type u) [Category.{v} C]
    {S : Signature} {M : List (MetaArity S)}
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    (equations : List (EqAxiom S M)) :
    (Functor.whiskeringRight C
      (FreeBindingEquationModel.Model equations)
      (SubstitutionOperationalModel rules equations)).obj
        (freeSubstitutionOperationalFunctor rules equations) ⊣
    (Functor.whiskeringRight C
      (SubstitutionOperationalModel rules equations)
      (FreeBindingEquationModel.Model equations)).obj
        (forgetSubstitutionOperationalBase rules equations) :=
  (freeSubstitutionOperationalAdjunction rules equations).whiskerRight C

/-- The pointwise free operational-model adjunction extends to diagrams:
interpretation of every authored firing tree is exactly a natural
interpretation of the binding-equation base. The equivalence includes
morphisms at every context and their substitution coherence. -/
noncomputable def operationalDiagramInterpretationEquiv
    {C : Type u} [Category.{v} C]
    {S : Signature} {M : List (MetaArity S)}
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    (equations : List (EqAxiom S M))
    (base : C ⥤ FreeBindingEquationModel.Model equations)
    (target : SubstitutionOperationalModel rules equations) :
    (base ⋙ freeSubstitutionOperationalFunctor rules equations ⟶
      (Functor.const C).obj target) ≃
    (base ⟶ (Functor.const C).obj target.base) where
  toFun interpretation := {
    app := fun context =>
      (SubstitutionOperationalModel.freeHomEquiv rules
        (base.obj context) target) (interpretation.app context)
    naturality := by
      intro first last assignment
      exact congrArg SubstitutionOperationalModel.Hom.base
        (interpretation.naturality assignment) }
  invFun interpretation := {
    app := fun context =>
      (SubstitutionOperationalModel.freeHomEquiv rules
        (base.obj context) target).symm (interpretation.app context)
    naturality := by
      intro first last assignment
      apply (SubstitutionOperationalModel.freeHomEquiv rules
        (base.obj first) target).injective
      exact interpretation.naturality assignment }
  left_inv interpretation := by
    ext context
    exact (SubstitutionOperationalModel.freeHomEquiv rules
      (base.obj context) target).left_inv (interpretation.app context)
  right_inv interpretation := by
    ext context
    exact (SubstitutionOperationalModel.freeHomEquiv rules
      (base.obj context) target).right_inv (interpretation.app context)

/-- The theorem specializes to the actual authored equation-class context
category, including all its higher-order contextual assignments. -/
noncomputable def authoredOperationalDiagramInterpretationEquiv
    (S : Signature) {M : List (MetaArity S)}
    (equations : List (EqAxiom S M))
    (rules : List (IntrinsicScopedConditionalPolynomial.Rule S M))
    (target : SubstitutionOperationalModel rules equations) :
    (authoredQuotientOperationalPresheaf S equations rules ⟶
      (Functor.const
        ((EquationContexts (authoredEquationPresentation S equations))ᵒᵖ)).obj target) ≃
    (authoredEquationQuotientModelPresheaf S equations ⟶
      (Functor.const
        ((EquationContexts (authoredEquationPresentation S equations))ᵒᵖ)).obj target.base) :=
  operationalDiagramInterpretationEquiv rules equations
    (authoredEquationQuotientModelPresheaf S equations) target

end Mettapedia.OSLF.Binding.SecondOrderContext

#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.operationalDiagramInterpretationEquiv
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredOperationalDiagramInterpretationEquiv
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.operationalDiagramAdjunction
