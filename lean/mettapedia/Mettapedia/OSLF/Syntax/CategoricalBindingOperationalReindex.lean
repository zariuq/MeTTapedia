import Mettapedia.OSLF.Syntax.CategoricalBindingQuotientEquivalence
import Mettapedia.OSLF.Syntax.IndexedOperationalModelReindex

/-!
# Operational extension of the binding-equation comparison

Any functorial, proof-relevant rule presentation over the quotient
binding-equation interpretations can be reindexed along their proved
classifying equivalence. The comparison retains the chosen rule algebra and
its individual firing evidence, and commutes with free rule generation and
forgetting to the authored base.

The actual authored scoped-rule presentation must still be constructed as
such a functor; this theorem is its categorical compatibility obligation.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Mettapedia.OSLF.Binding.CategoricalBindingOperationalReindex

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.CategoricalBindingQuotientEquivalence
open Mettapedia.OSLF.Binding.IndexedRulePresentationCategory
open Mettapedia.OSLF.Binding.IndexedOperationalModelsOver

universe u v uBase uIndex uShape uPosition

variable {S : Signature} {schema : List (MetaArity S)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable (Eqs : EquationPresentation S schema)
variable {Base : Type uBase}
variable (Rules : QuotientStructuredFunctor (D := D) Eqs ⥤
  Presentation.{uBase, uIndex, uShape, uPosition} Base)

/-- Adding a functorial algebra of ordered firing constructors is compatible
with the binding-equation classifying equivalence, including maps. -/
noncomputable def operationalBindingEquationEquivalence :
    Model ((bindingEquationEquivalence (D := D) Eqs).functor ⋙ Rules) ≌
      Model Rules := by
  letI : (bindingEquationEquivalence (D := D) Eqs).functor.IsEquivalence :=
    (bindingEquationEquivalence (D := D) Eqs).isEquivalence_functor
  exact reindexEquivalence Rules
    (bindingEquationEquivalence (D := D) Eqs).functor

/-- Forgetting the operational evidence agrees with forgetting before the
binding-equation comparison. -/
theorem operationalBindingEquation_forget :
    reindexFunctor Rules (bindingEquationEquivalence (D := D) Eqs).functor ⋙
      forget Rules =
    forget ((bindingEquationEquivalence (D := D) Eqs).functor ⋙ Rules) ⋙
      (bindingEquationEquivalence (D := D) Eqs).functor := by
  rfl

/-- Free firing-tree generation commutes with the same comparison. -/
theorem operationalBindingEquation_free :
    (bindingEquationEquivalence (D := D) Eqs).functor ⋙ freeFunctor Rules =
    freeFunctor ((bindingEquationEquivalence (D := D) Eqs).functor ⋙ Rules) ⋙
      reindexFunctor Rules (bindingEquationEquivalence (D := D) Eqs).functor := by
  rfl

end Mettapedia.OSLF.Binding.CategoricalBindingOperationalReindex

#print axioms Mettapedia.OSLF.Binding.CategoricalBindingOperationalReindex.operationalBindingEquationEquivalence
