import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModelMapReadout
import Mettapedia.TypeTheory.ContextualPredicateMorphismComposition

/-!
# Composition of mixed predicate model maps

The actual contextual action, Heyting fibre homomorphisms, local dependent
constructors and primitive readings compose. Units and associativity retain
both kinds of action. Successful evaluations preserve their intermediate and
final complete values, including mixed satisfying assumption scopes.

This is composition of strictly chosen logical maps. It makes no assertion
about arbitrary pseudo logical maps or reflection of unsuccessful checks.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateModel ContextualPredicateModelScopes ContextualPredicateScopeMorphism
open ContextualPredicateMorphism ContextualComprehensionMorphism ContextualTelescopeMorphism
open ContextualModelTelescopes ContextualStrictMorphismComposition ContextualLogicalMorphism

universe a c s t m p q r k
variable {S : Symbols.{a}} {C D E H : CwfWithTerminal.{c,s,t,m}}
  {sourceModel : LocalModel.{c,s,t,m,p} C} {middleModel : LocalModel.{c,s,t,m,q} D}
  {laterModel : LocalModel.{c,s,t,m,r} E} {targetModel : LocalModel.{c,s,t,m,k} H}

namespace ModelMap

def identity (model : ModelData S C sourceModel) : ModelMap model model where
  morphism := StrictCwfMorphism.identity C
  logical := LogicalPreservation.identity sourceModel.products sourceModel.sums.operations
  predicates := PredicateLogicalPreservation.identity sourceModel
  typeParameters symbol := ScopeImage.identity (model.typeParameters symbol)
  typeFamily _ := HEq.rfl
  termParameters symbol := ScopeImage.identity (model.termParameters symbol)
  termType _ := HEq.rfl
  termValue _ := HEq.rfl
  predicateParameters symbol := ScopeImage.identity (model.predicateParameters symbol)
  predicateValue _ := HEq.rfl

def comp {source : ModelData S C sourceModel} {middle : ModelData S D middleModel}
    {target : ModelData S E laterModel}
    (earlier : ModelMap source middle) (later : ModelMap middle target) : ModelMap source target where
  morphism := compose earlier.morphism later.morphism
  logical := earlier.logical.comp later.logical
  predicates := earlier.predicates.comp later.predicates
  typeParameters symbol := ScopeImage.comp earlier.morphism later.morphism
    (earlier.typeParameters symbol) (later.typeParameters symbol)
  typeFamily symbol := (mappedType_heq later.morphism (earlier.typeParameters symbol).contexts
    (earlier.typeFamily symbol)).trans (later.typeFamily symbol)
  termParameters symbol := ScopeImage.comp earlier.morphism later.morphism
    (earlier.termParameters symbol) (later.termParameters symbol)
  termType symbol := (mappedType_heq later.morphism (earlier.termParameters symbol).contexts
    (earlier.termType symbol)).trans (later.termType symbol)
  termValue symbol := (mappedTerm_heq later.morphism (earlier.termParameters symbol).contexts
    (earlier.termType symbol) (earlier.termValue symbol)).trans (later.termValue symbol)
  predicateParameters symbol := ScopeImage.comp earlier.morphism later.morphism
    (earlier.predicateParameters symbol) (later.predicateParameters symbol)
  predicateValue symbol := (mappedPredicate_heq later.predicates.doctrine
    (earlier.predicateParameters symbol).contexts (earlier.predicateValue symbol)).trans
      (later.predicateValue symbol)

/-- The complete contextual action and actual predicate maps determine a
model map. The remaining fields are local preservation certificates. -/
theorem ext_of_actions {source : ModelData S C sourceModel} {target : ModelData S D middleModel}
    {first second : ModelMap source target} (contexts : first.morphism = second.morphism)
    (predicates : HEq first.predicates.doctrine.hom second.predicates.doctrine.hom) :
    first = second := by
  cases first with
  | mk firstMorphism firstLogical firstPredicates firstTypeParameters firstFamily
      firstTermParameters firstType firstValue firstPredicateParameters firstPredicateValue =>
    cases second with
    | mk secondMorphism secondLogical secondPredicates secondTypeParameters secondFamily
        secondTermParameters secondType secondValue secondPredicateParameters secondPredicateValue =>
      cases contexts
      have same : firstPredicates = secondPredicates :=
        PredicateLogicalPreservation.ext_hom (eq_of_heq predicates)
      cases same
      rfl

@[simp] theorem identity_comp {source : ModelData S C sourceModel} {target : ModelData S D middleModel}
    (mapping : ModelMap source target) : (identity source).comp mapping = mapping := by
  apply ext_of_actions (ContextualStrictMorphismComposition.identity_comp mapping.morphism)
  exact heq_of_eq (funext fun Γ => HeytingHom.comp_id (mapping.predicates.doctrine.hom Γ))

@[simp] theorem comp_identity {source : ModelData S C sourceModel} {target : ModelData S D middleModel}
    (mapping : ModelMap source target) : mapping.comp (identity target) = mapping := by
  apply ext_of_actions (ContextualStrictMorphismComposition.comp_identity mapping.morphism)
  exact heq_of_eq (funext fun Γ => HeytingHom.id_comp (mapping.predicates.doctrine.hom Γ))

theorem assoc {source : ModelData S C sourceModel} {middle : ModelData S D middleModel}
    {later : ModelData S E laterModel} {target : ModelData S H targetModel}
    (first : ModelMap source middle) (second : ModelMap middle later) (third : ModelMap later target) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  apply ext_of_actions
    (ContextualStrictMorphismComposition.assoc first.morphism second.morphism third.morphism)
  exact heq_of_eq (funext fun Γ => (HeytingHom.comp_assoc
    (third.predicates.doctrine.hom (context second.morphism (context first.morphism Γ)))
    (second.predicates.doctrine.hom (context first.morphism Γ))
    (first.predicates.doctrine.hom Γ)).symm)

theorem type_composition {source : ModelData S C sourceModel} {middle : ModelData S D middleModel}
    {target : ModelData S E laterModel} (first : ModelMap source middle) (second : ModelMap middle target)
    {Γ : C.toCwf.Ctx} (type : C.toCwf.Ty Γ) :
    (first.comp second).morphism.toFamilyMorphism.mapType type =
      second.morphism.toFamilyMorphism.mapType (first.morphism.toFamilyMorphism.mapType type) := rfl

theorem term_composition {source : ModelData S C sourceModel} {middle : ModelData S D middleModel}
    {target : ModelData S E laterModel} (first : ModelMap source middle) (second : ModelMap middle target)
    {Γ : C.toCwf.Ctx} {A : C.toCwf.Ty Γ} (value : C.toCwf.Tm Γ A) :
    (first.comp second).morphism.toFamilyMorphism.mapTerm value =
      second.morphism.toFamilyMorphism.mapTerm (first.morphism.toFamilyMorphism.mapTerm value) := rfl

theorem predicate_composition {source : ModelData S C sourceModel} {middle : ModelData S D middleModel}
    {target : ModelData S E laterModel} (first : ModelMap source middle) (second : ModelMap middle target)
    {Γ : C.toCwf.Ctx} (predicate : sourceModel.doctrine.Predicate Γ) :
    (first.comp second).predicates.doctrine.hom Γ predicate =
      second.predicates.doctrine.hom (context first.morphism Γ)
        (first.predicates.doctrine.hom Γ predicate) := rfl

theorem arrow_composition {source : ModelData S C sourceModel} {middle : ModelData S D middleModel}
    {target : ModelData S E laterModel} (first : ModelMap source middle) (second : ModelMap middle target)
    {Γ Δ : C.toCwf.Ctx} (arrow : C.toCwf.Sub Γ Δ) :
    (first.comp second).morphism.toFamilyMorphism.base.map arrow =
      second.morphism.toFamilyMorphism.base.map (first.morphism.toFamilyMorphism.base.map arrow) := rfl

/-- Successful context evaluation detects the actual composition of mixed
chosen scope images, including every satisfying assumption. -/
theorem evaluated_context_composition
    {source : ModelData S C sourceModel} {middle : ModelData S D middleModel}
    {target : ModelData S E laterModel} (first : ModelMap source middle) (second : ModelMap middle target)
    {n : Nat} (raw : ContextExpr S n) (Γ : ModelScope C sourceModel n)
    (evaluated : source.evaluateContext raw = some Γ) :
    imageScope (first.comp second).morphism (first.comp second).predicates.assumptions Γ =
      imageScope second.morphism second.predicates.assumptions
        (imageScope first.morphism first.predicates.assumptions Γ) := by
  have firstRead := first.evaluateContext_image raw Γ evaluated
  have secondRead := second.evaluateContext_image raw _ firstRead
  have directRead := (first.comp second).evaluateContext_image raw Γ evaluated
  exact Option.some.inj (directRead.symm.trans secondRead)

theorem evaluateType_composition {source : ModelData S C sourceModel} {middle : ModelData S D middleModel}
    {target : ModelData S E laterModel} (first : ModelMap source middle) (second : ModelMap middle target)
    {n : Nat} (type : TypeExpr S n) (Γ : ModelScope C sourceModel n)
    (Δ : ModelScope D middleModel n) (Θ : ModelScope E laterModel n)
    (earlierContexts : ScopeImage first.morphism Γ Δ) (laterContexts : ScopeImage second.morphism Δ Θ)
    (value : C.toCwf.Ty Γ.1) (supplied : source.evaluateType Γ type = some value) :
    ∃ middleValue finalValue,
      middle.evaluateType Δ type = some middleValue ∧ target.evaluateType Θ type = some finalValue ∧
      HEq (first.morphism.toFamilyMorphism.mapType value) middleValue ∧
      HEq (second.morphism.toFamilyMorphism.mapType middleValue) finalValue ∧
      HEq ((first.comp second).morphism.toFamilyMorphism.mapType value) finalValue := by
  rcases first.evaluateType_image type Γ Δ earlierContexts value supplied with
    ⟨middleValue, middleRead, firstValues⟩
  rcases second.evaluateType_image type Δ Θ laterContexts middleValue middleRead with
    ⟨finalValue, finalRead, secondValues⟩
  exact ⟨middleValue, finalValue, middleRead, finalRead, firstValues, secondValues,
    (mappedType_heq second.morphism earlierContexts.contexts firstValues).trans secondValues⟩

theorem evaluateTerm_composition {source : ModelData S C sourceModel} {middle : ModelData S D middleModel}
    {target : ModelData S E laterModel} (first : ModelMap source middle) (second : ModelMap middle target)
    {n : Nat} (term : TermExpr S n) (Γ : ModelScope C sourceModel n)
    (Δ : ModelScope D middleModel n) (Θ : ModelScope E laterModel n)
    (earlierContexts : ScopeImage first.morphism Γ Δ) (laterContexts : ScopeImage second.morphism Δ Θ)
    (value : Value C.toCwf Γ.1) (supplied : source.evaluateTerm Γ term = some value) :
    ∃ middleValue finalValue,
      middle.evaluateTerm Δ term = some middleValue ∧ target.evaluateTerm Θ term = some finalValue ∧
      ValueImage first.morphism value middleValue ∧ ValueImage second.morphism middleValue finalValue ∧
      ValueImage (first.comp second).morphism value finalValue := by
  rcases first.evaluateTerm_image term Γ Δ earlierContexts value supplied with
    ⟨middleValue, middleRead, firstValues⟩
  rcases second.evaluateTerm_image term Δ Θ laterContexts middleValue middleRead with
    ⟨finalValue, finalRead, secondValues⟩
  exact ⟨middleValue, finalValue, middleRead, finalRead, firstValues, secondValues,
    valueImage_comp first.morphism second.morphism earlierContexts.contexts firstValues secondValues⟩

theorem evaluatePredicate_composition
    {source : ModelData S C sourceModel} {middle : ModelData S D middleModel}
    {target : ModelData S E laterModel} (first : ModelMap source middle) (second : ModelMap middle target)
    {n : Nat} (predicate : PropExpr S n) (Γ : ModelScope C sourceModel n)
    (Δ : ModelScope D middleModel n) (Θ : ModelScope E laterModel n)
    (earlierContexts : ScopeImage first.morphism Γ Δ) (laterContexts : ScopeImage second.morphism Δ Θ)
    (value : sourceModel.doctrine.Predicate Γ.1) (supplied : source.evaluatePredicate Γ predicate = some value) :
    ∃ middleValue finalValue,
      middle.evaluatePredicate Δ predicate = some middleValue ∧
      target.evaluatePredicate Θ predicate = some finalValue ∧
      HEq (first.predicates.doctrine.hom Γ.1 value) middleValue ∧
      HEq (second.predicates.doctrine.hom Δ.1 middleValue) finalValue ∧
      HEq ((first.comp second).predicates.doctrine.hom Γ.1 value) finalValue := by
  rcases first.evaluatePredicate_image predicate Γ Δ earlierContexts value supplied with
    ⟨middleValue, middleRead, firstValues⟩
  rcases second.evaluatePredicate_image predicate Δ Θ laterContexts middleValue middleRead with
    ⟨finalValue, finalRead, secondValues⟩
  exact ⟨middleValue, finalValue, middleRead, finalRead, firstValues, secondValues,
    (mappedPredicate_heq second.predicates.doctrine earlierContexts.contexts firstValues).trans secondValues⟩

theorem evaluateSubstitution_composition
    {source : ModelData S C sourceModel} {middle : ModelData S D middleModel}
    {target : ModelData S E laterModel} (first : ModelMap source middle) (second : ModelMap middle target)
    {n j : Nat} (Γ : ModelScope C sourceModel n) (Δ : ModelScope C sourceModel j)
    (Γ' : ModelScope D middleModel n) (Δ' : ModelScope D middleModel j)
    (Γ'' : ModelScope E laterModel n) (Δ'' : ModelScope E laterModel j)
    (sources : ScopeImage first.morphism Γ Γ') (targets : ScopeImage first.morphism Δ Δ')
    (sources' : ScopeImage second.morphism Γ' Γ'') (targets' : ScopeImage second.morphism Δ' Δ'')
    (substitution : Substitution S j n) (arrow : C.toCwf.Sub Γ.1 Δ.1)
    (supplied : source.evaluateSubstitution Γ Δ substitution = some arrow) :
    target.evaluateSubstitution Γ'' Δ'' substitution = some
      (imageArrow (first.comp second).morphism
        (ScopeImage.comp first.morphism second.morphism sources sources').contexts
        (ScopeImage.comp first.morphism second.morphism targets targets').contexts arrow) := by
  have middleRead := first.evaluateSubstitution_image Γ Δ Γ' Δ' sources targets substitution arrow supplied
  have finalRead := second.evaluateSubstitution_image Γ' Δ' Γ'' Δ'' sources' targets' substitution _ middleRead
  exact finalRead.trans (congrArg some (imageArrow_comp first.morphism second.morphism
    sources.contexts targets.contexts sources'.contexts targets'.contexts arrow))

end ModelMap
end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
