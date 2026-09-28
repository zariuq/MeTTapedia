import Mettapedia.OSLF.Syntax.IndexedOperationalModelsOver
import Mettapedia.OSLF.Syntax.FreeBindingEquationModel
import Mettapedia.OSLF.Syntax.LambdaRulePolynomialMorphism
import Mettapedia.OSLF.Syntax.LambdaBindingEquationOperationalInterpretation

/-!
# The authored lambda equation-and-rule theory as a combined initial model

The general operational-model construction applies to the functor sending a
binding clone satisfying the authored lambda equations to its beta and
congruence rule presentation. The resulting initial object carries the
presented equation quotient and a proof-relevant tree of every firing.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaEquationRuleModels

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaSemanticRulePolynomial
open Mettapedia.OSLF.Binding.LambdaRulePolynomialMorphism

variable {M : List (MetaArity sig)} (E : List (EqAxiom sig M))

/-- Authored lambda beta and congruence rules, functorially attached to any
model satisfying the selected equations. -/
noncomputable def presentationFunctor :
    FreeBindingEquationModel.Model.{0} E ⥤
      IndexedRulePresentationCategory.Presentation Unit where
  obj X := lambdaPresentation X.algebra
  map h := lambdaPresentationMap h
  map_id := by intro X; exact lambdaPresentationMap_id X.algebra
  map_comp := by intro X Y Z f g; exact lambdaPresentationMap_comp f g

/-- A model of the authored equations together with an algebra of retained
rule-firing evidence. -/
abbrev Model := IndexedOperationalModelsOver.Model (presentationFunctor E)

/-- Morphisms preserve equations, substitution, rule constructors and
individual recursive premise evidence. -/
abbrev Hom (X Y : Model E) :=
  IndexedOperationalModelsOver.Hom (presentationFunctor E) X Y

/-- Freely adjoining beta and congruence firing histories to a semantic
lambda equation model is left adjoint to forgetting that evidence algebra. -/
noncomputable def freeAdjunction :
    IndexedOperationalModelsOver.freeFunctor (presentationFunctor E) ⊣
      IndexedOperationalModelsOver.forget (presentationFunctor E) :=
  IndexedOperationalModelsOver.freeAdjunction (presentationFunctor E)

/-- The equation quotient equipped with freely generated proof-relevant
beta and congruence firing histories. -/
noncomputable def presented : Model E :=
  IndexedOperationalModelsOver.free (presentationFunctor E)
    (FreeBindingEquationModel.presented E)

/-- The unique simultaneous interpretation from presented syntax into an
arbitrary authored lambda equation-and-rule model. -/
noncomputable def interpret (target : Model E) : Hom E (presented E) target :=
  IndexedOperationalModelsOver.initialHom (presentationFunctor E)
    (FreeBindingEquationModel.presentedIsInitial E) target

/-- The base component is the original unique interpretation of the authored
equation quotient. -/
theorem interpret_base (target : Model E) :
    (interpret E target).base =
      FreeBindingEquationModel.interpretHom target.base := by
  rfl

/-- The rule component agrees at every context and firing history with the
previous concrete lambda fold. -/
theorem interpret_firing (target : Model E)
    (j : Judgment (FreeBindingEquationModel.presented E).algebra)
    (tree : (rules (FreeBindingEquationModel.presented E).algebra).Fix () j) :
    (interpret E target).evidence.toFun () j tree =
      (LambdaBindingEquationOperationalInterpretation.canonical
        target.base target.evidence.rules).fire j tree := by
  rfl

/-- The combined syntax, equations and retained rule histories are initial
among the corresponding small semantic models. -/
noncomputable def presentedIsInitial : IsInitial (presented E) :=
  IndexedOperationalModelsOver.freeIsInitial (presentationFunctor E)
    (FreeBindingEquationModel.presentedIsInitial E)

#print axioms presentationFunctor
#print axioms freeAdjunction
#print axioms interpret_firing
#print axioms presentedIsInitial

end Mettapedia.OSLF.Binding.LambdaEquationRuleModels
