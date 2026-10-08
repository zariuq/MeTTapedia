import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModelMap
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractPredicateCommutation

/-!
# Successful dependent checks under local predicate model maps

A checked source inhabitant has a checked target image at the supplied
mapped annotation. Conditional refinement transports its actual guard and
complete inhabitant; forgetting computes the image of the supplied refined
value. These are local checker comparisons. They do not assert reflection
of failed checks or compatibility of whole expressions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateModel ContextualPredicateScopeMorphism
open ContextualModelTelescopes ContextualComprehensionMorphism ContextualTelescopeMorphism
open ContextualProductComparison (selfExtend)
open External (bindResult bindResult_eq_some_iff)

universe a c s t m p q
variable {S : Symbols.{a}} {C D : CwfWithTerminal.{c,s,t,m}}
  {sourceModel : LocalModel.{c,s,t,m,p} C} {targetModel : LocalModel.{c,s,t,m,q} D}
  {source : ModelData S C sourceModel} {target : ModelData S D targetModel}

namespace ModelMap

variable (mapping : ModelMap source target)
  {Γ : C.toCwf.Ctx} {Γ' : D.toCwf.Ctx}
  (contexts : context mapping.morphism Γ = Γ')
  {A : C.toCwf.Ty Γ} {A' : D.toCwf.Ty Γ'}
  (types : HEq (mapping.morphism.toFamilyMorphism.mapType A) A')
  (result : Option (Value C.toCwf Γ)) (result' : Option (Value D.toCwf Γ'))
  (values : ∀ value, result = some value →
    ∃ value', result' = some value' ∧ ValueImage mapping.morphism value value')

include contexts types values

theorem checked_image (term : C.toCwf.Tm Γ A)
    (checked : ModelData.check? result A = some term) :
    ∃ term' : D.toCwf.Tm Γ' A', ModelData.check? result' A' = some term' ∧
      HEq (mapping.morphism.toFamilyMorphism.mapTerm term) term' := by
  have sourceRead := (ModelData.check?_eq_some_iff _ _ _).mp checked
  rcases values _ sourceRead with ⟨value', targetRead, related⟩
  rcases ValueImage.at_type mapping.morphism contexts types term value' related with
    ⟨term', valueRead, terms⟩
  rw [valueRead] at targetRead
  exact ⟨term', (ModelData.check?_eq_some_iff _ _ _).mpr targetRead, terms⟩

variable {predicate : sourceModel.doctrine.Predicate (C.toCwf.ext Γ A)}
  {predicate' : targetModel.doctrine.Predicate (D.toCwf.ext Γ' A')}
  (predicates : HEq (mapping.predicates.doctrine.hom (C.toCwf.ext Γ A) predicate) predicate')

include predicates

theorem refinementCheck_image (output : Value C.toCwf Γ)
    (checked : ModelData.refine? sourceModel A predicate result = some output) :
    ∃ output' : Value D.toCwf Γ',
      ModelData.refine? targetModel A' predicate' result' = some output' ∧
        ValueImage mapping.morphism output output' := by
  rcases (ModelData.refine?_eq_some_iff sourceModel A predicate result output).mp checked with
    ⟨term, guard, sourceRead, outputRead⟩
  rcases values _ sourceRead with ⟨value', targetRead, related⟩
  rcases ValueImage.at_type mapping.morphism contexts types term value' related with
    ⟨term', valueRead, terms⟩
  rw [valueRead] at targetRead
  have guard' := mapping.guard_image contexts types predicates term term' terms guard
  refine ⟨⟨targetModel.refinements.refined A' predicate',
      targetModel.refinements.intro A' predicate' term' guard'⟩, ?_, ?_⟩
  · rw [targetRead]
    exact ModelData.refine?_supplied A' predicate' term' guard'
  · rw [← outputRead]
    exact mapping.refine_image contexts types predicates term term' terms guard guard'

omit values

theorem forgettingCheck_image
    (refinedValues : ∀ value, result = some value →
      ∃ value', result' = some value' ∧ ValueImage mapping.morphism value value')
    (output : Value C.toCwf Γ)
    (checked : ModelData.forget? sourceModel A predicate result = some output) :
    ∃ output' : Value D.toCwf Γ',
      ModelData.forget? targetModel A' predicate' result' = some output' ∧
        ValueImage mapping.morphism output output' := by
  have checkRead := checked
  rw [ModelData.forget?] at checkRead
  rcases (bindResult_eq_some_iff _ _ _).mp checkRead with ⟨term, inputChecked, outputRead⟩
  have sourceRead := (ModelData.check?_eq_some_iff _ _ _).mp inputChecked
  rcases refinedValues _ sourceRead with ⟨value', targetRead, related⟩
  rcases ValueImage.at_type mapping.morphism contexts
      (mapping.refinement_image contexts types predicates) term value' related with
    ⟨term', valueRead, terms⟩
  rw [valueRead] at targetRead
  refine ⟨⟨A', targetModel.refinements.forget A' predicate' term'⟩, ?_, ?_⟩
  · simp only [ModelData.forget?, targetRead, ModelData.check?_supplied, bindResult]
  · rw [← Option.some.inj outputRead]
    exact mapping.forget_image contexts types predicates term term' terms

omit types predicates

theorem truth_image :
    HEq (mapping.predicates.doctrine.hom Γ (⊤ : sourceModel.doctrine.Predicate Γ))
      (⊤ : targetModel.doctrine.Predicate Γ') := by
  cases contexts
  exact heq_of_eq (map_top (mapping.predicates.doctrine.hom Γ))

theorem falsehood_image :
    HEq (mapping.predicates.doctrine.hom Γ (⊥ : sourceModel.doctrine.Predicate Γ))
      (⊥ : targetModel.doctrine.Predicate Γ') := by
  cases contexts
  exact heq_of_eq (map_bot (mapping.predicates.doctrine.hom Γ))

theorem and_image {first second : sourceModel.doctrine.Predicate Γ}
    {first' second' : targetModel.doctrine.Predicate Γ'}
    (firsts : HEq (mapping.predicates.doctrine.hom Γ first) first')
    (seconds : HEq (mapping.predicates.doctrine.hom Γ second) second') :
    HEq (mapping.predicates.doctrine.hom Γ (first ⊓ second)) (first' ⊓ second') := by
  cases contexts
  cases eq_of_heq firsts
  cases eq_of_heq seconds
  exact heq_of_eq (map_inf (mapping.predicates.doctrine.hom Γ) first second)

theorem or_image {first second : sourceModel.doctrine.Predicate Γ}
    {first' second' : targetModel.doctrine.Predicate Γ'}
    (firsts : HEq (mapping.predicates.doctrine.hom Γ first) first')
    (seconds : HEq (mapping.predicates.doctrine.hom Γ second) second') :
    HEq (mapping.predicates.doctrine.hom Γ (first ⊔ second)) (first' ⊔ second') := by
  cases contexts
  cases eq_of_heq firsts
  cases eq_of_heq seconds
  exact heq_of_eq (map_sup (mapping.predicates.doctrine.hom Γ) first second)

theorem implication_image {first second : sourceModel.doctrine.Predicate Γ}
    {first' second' : targetModel.doctrine.Predicate Γ'}
    (firsts : HEq (mapping.predicates.doctrine.hom Γ first) first')
    (seconds : HEq (mapping.predicates.doctrine.hom Γ second) second') :
    HEq (mapping.predicates.doctrine.hom Γ (first ⇨ second)) (first' ⇨ second') := by
  cases contexts
  cases eq_of_heq firsts
  cases eq_of_heq seconds
  exact heq_of_eq (map_himp (mapping.predicates.doctrine.hom Γ) first second)

end ModelMap

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
