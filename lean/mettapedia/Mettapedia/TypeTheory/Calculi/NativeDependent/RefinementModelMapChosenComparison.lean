import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementCanonicalModelMap
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModelUniverseReadout
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModelMapReadout

/-!
# Complete comparisons on chosen mixed source scopes

Earned source evaluator readbacks recover every supplied type, term,
predicate and guarded substitution. Local logical and primitive model-map
laws identify their independently evaluated target images. The source
syntax remains at its original symbol level; carrier changes raise the
actual source values and leave the predicate carrier independent.

These comparisons concern finite mixed scopes. The retained raw context
objects obtain their coherent comparison through the separate presentation
isomorphisms.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.ModelMapComparison

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualComprehensionMorphism
open Mettapedia.TypeTheory.ContextualTelescopeMorphism
open Mettapedia.TypeTheory.ContextualPredicateModel
open Mettapedia.TypeTheory.ContextualPredicateModelScopes
open Mettapedia.TypeTheory.ContextualPredicateScopeMorphism
open Mettapedia.TypeTheory.ContextualPredicateModelScopeUniverseLift
open Mettapedia.TypeTheory.ContextualCwfUniverseLift
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Refinement.Abstract
open SyntacticReification

universe u z p
variable {S : Symbols.{u}} {D : Signature S}
  {C : CwfWithTerminal.{max u z,max u z,max u z,max u z}}
  {targetModel : LocalModel.{max u z,max u z,max u z,max u z,p} C}
  {target : ModelData S C targetModel}

noncomputable abbrev raisedScope {n : Nat} (scope : SyntacticReification.Scope D n) :
    ModelScope (Interpretation.SourceModel.{u,z} D) (Interpretation.sourceLocalModel.{u,z} D) n :=
  liftScope.{u,u,u,u,u,max u z,max u z,max u z,max u z,0} scope.semantic

variable (headers : HeaderFormation D)
  (first second : ModelMap (Interpretation.sourceData.{u,z} headers) target)

/-- The actual recursively constructed mixed images evaluate the same raw
context, including every successive assumption restriction. -/
theorem image_scope_equal {n : Nat} (scope : SyntacticReification.Scope D n) :
    imageScope first.morphism first.predicates.assumptions (raisedScope.{u,z} scope) =
      imageScope second.morphism second.predicates.assumptions (raisedScope.{u,z} scope) := by
  have sourceRead := (SyntacticModel.data headers).evaluateContext_carrierLift
    scope.raw scope.semantic (SyntacticModel.scope_context_read headers scope)
  have left := first.evaluateContext_image scope.raw (raisedScope.{u,z} scope) sourceRead
  have right := second.evaluateContext_image scope.raw (raisedScope.{u,z} scope) sourceRead
  exact Option.some.inj (left.symm.trans right)

/-- Comparing at the first complete target scope retains all variable
readings and the guarded inclusion structure. -/
theorem second_scope_image {n : Nat} (scope : SyntacticReification.Scope D n) :
    ScopeImage second.morphism (raisedScope.{u,z} scope)
      (imageScope first.morphism first.predicates.assumptions (raisedScope.{u,z} scope)) := by
  rw [image_scope_equal headers first second scope]
  exact imageScope_comparison second.morphism second.predicates.assumptions _

theorem context_equal {n : Nat} (scope : SyntacticReification.Scope D n) :
    context first.morphism (ULift.up ((quotientProjection D).obj scope.source)) =
      context second.morphism (ULift.up ((quotientProjection D).obj scope.source)) :=
  (imageScope_comparison first.morphism first.predicates.assumptions
    (raisedScope.{u,z} scope)).contexts.trans
      (second_scope_image headers first second scope).contexts.symm

/-- Arbitrary complete source family classes are lowered, represented and
raised through the earned source interpreter before their images are compared. -/
theorem type_heq {n : Nat} (scope : SyntacticReification.Scope D n)
    (A : (Interpretation.SourceModel.{u,z} D).toCwf.Ty
      (ULift.up ((quotientProjection D).obj scope.source))) :
    HEq (first.morphism.toFamilyMorphism.mapType A)
      (second.morphism.toFamilyMorphism.mapType A) := by
  let annotation := QuotientCwf.typeRepresentative A.down
  have nativeRead := (SyntacticModel.scope_type_read headers scope annotation).trans
    (congrArg some (QuotientCwf.typeRepresentative_class A.down))
  have sourceRead := (SyntacticModel.data headers).evaluateType_carrierLift
    annotation.code scope.semantic A.down nativeRead
  rcases first.evaluateType_image annotation.code (raisedScope.{u,z} scope) _
    (imageScope_comparison first.morphism first.predicates.assumptions _) A sourceRead with
      ⟨value, read, related⟩
  have other := second.evaluateType_image_unique annotation.code (raisedScope.{u,z} scope) _
    (second_scope_image headers first second scope) A value sourceRead read
  exact related.trans other.symm

/-- Re-admission at the supplied annotation retains the exact term class,
so equality compares the complete sections rather than only inhabitation. -/
theorem term_heq {n : Nat} (scope : SyntacticReification.Scope D n)
    {A : (Interpretation.SourceModel.{u,z} D).toCwf.Ty
      (ULift.up ((quotientProjection D).obj scope.source))}
    (term : (Interpretation.SourceModel.{u,z} D).toCwf.Tm
      (ULift.up ((quotientProjection D).obj scope.source)) A) :
    HEq (first.morphism.toFamilyMorphism.mapTerm term)
      (second.morphism.toFamilyMorphism.mapTerm term) := by
  let annotation := QuotientCwf.typeRepresentative A.down
  let supplied := QuotientCwf.termRepresentative annotation term.down.val
    (term.down.property.trans (QuotientCwf.typeRepresentative_class A.down).symm)
  have classRead : QTerm.mk supplied = term.down.val :=
    QuotientCwf.termRepresentative_class annotation term.down.val
      (term.down.property.trans (QuotientCwf.typeRepresentative_class A.down).symm)
  have sourceRead := SyntacticModel.scope_term_read headers scope supplied
  have whole : (⟨QType.mk annotation, ⟨QTerm.mk supplied,rfl⟩⟩ :
      Value (QuotientCwf.cwf D) ((quotientProjection D).obj scope.source)) =
        ⟨A.down,term.down⟩ := SyntacticReification.value_ext classRead
  rw [whole] at sourceRead
  have liftedRead := (SyntacticModel.data headers).evaluateTerm_carrierLift
    supplied.code scope.semantic _ sourceRead
  rcases first.evaluateTerm_image supplied.code (raisedScope.{u,z} scope) _
    (imageScope_comparison first.morphism first.predicates.assumptions _) _ liftedRead with
      ⟨value, read, related⟩
  have other := second.evaluateTerm_image_unique supplied.code (raisedScope.{u,z} scope) _
    (second_scope_image headers first second scope) _ value liftedRead read
  exact related.terms.trans other.terms.symm

/-- Predicates are the independently authored definable fibre. Every
supplied class is compared, without identifying it with all native sieves. -/
theorem predicate_heq {n : Nat} (scope : SyntacticReification.Scope D n)
    (predicate : (Interpretation.sourceLocalModel.{u,z} D).doctrine.Predicate
      (ULift.up ((quotientProjection D).obj scope.source))) :
    HEq (first.predicates.doctrine.hom _ predicate)
      (second.predicates.doctrine.hom _ predicate) := by
  let supplied := AssumptionModel.chosen predicate.down
  have nativeRead := (SyntacticModel.scope_predicate_read headers scope supplied).trans
    (congrArg some (AssumptionModel.chosen_class predicate.down))
  have sourceRead := (SyntacticModel.data headers).evaluatePredicate_carrierLift
    supplied.code scope.semantic predicate.down nativeRead
  rcases first.evaluatePredicate_image supplied.code (raisedScope.{u,z} scope) _
    (imageScope_comparison first.morphism first.predicates.assumptions _) predicate sourceRead with
      ⟨value, read, related⟩
  have other := second.evaluatePredicate_image_unique supplied.code (raisedScope.{u,z} scope) _
    (second_scope_image headers first second scope) predicate value sourceRead read
  exact related.trans other.symm

/-- Every actual admitted guarded substitution has the same transported
image under both maps. Its exact ordered source components are retained. -/
theorem arrow_heq {n k : Nat} (source : SyntacticReification.Scope D n)
    (destination : SyntacticReification.Scope D k)
    (arrow : (Interpretation.SourceModel.{u,z} D).toCwf.Sub
      (ULift.up ((quotientProjection D).obj source.source))
      (ULift.up ((quotientProjection D).obj destination.source))) :
    HEq (first.morphism.toFamilyMorphism.base.map arrow)
      (second.morphism.toFamilyMorphism.base.map arrow) := by
  let raw := QuotientCwf.representative arrow.down
  have sourceRead := (SyntacticModel.scope_substitution_read headers source destination raw).trans
    (congrArg some (QuotientCwf.project_representative arrow.down))
  have liftedRead := (SyntacticModel.data headers).evaluateSubstitution_carrierLift
    source.semantic destination.semantic raw.substitution arrow.down sourceRead
  have left := first.evaluateSubstitution_image (raisedScope.{u,z} source)
    (raisedScope.{u,z} destination) _ _
    (imageScope_comparison first.morphism first.predicates.assumptions _)
    (imageScope_comparison first.morphism first.predicates.assumptions _) raw.substitution arrow liftedRead
  have right := second.evaluateSubstitution_image (raisedScope.{u,z} source)
    (raisedScope.{u,z} destination) _ _
    (second_scope_image headers first second source)
    (second_scope_image headers first second destination) raw.substitution arrow liftedRead
  have actual := Option.some.inj (left.symm.trans right)
  exact (imageArrow_heq first.morphism _ _ arrow).trans
    ((heq_of_eq actual).trans (imageArrow_heq second.morphism _ _ arrow).symm)

theorem context_equal_mixed {n : Nat} {Γ : QuotientCwf.QContext D}
    (mixed : ScopeData (QuotientCwf.withTerminal D) (generatedModel D).doctrine
      (generatedModel D).assumptions n Γ) :
    context first.morphism (ULift.up Γ) = context second.morphism (ULift.up Γ) := by
  have same := context_equal headers first second (SyntacticReification.Scope.ofSemantic ⟨Γ,mixed⟩)
  have sourceSame := congrArg
    (fun scope : ModelScope (QuotientCwf.withTerminal D) (generatedModel D) n => scope.1)
    (SyntacticReification.Scope.ofSemantic_semantic ⟨Γ,mixed⟩)
  change (quotientProjection D).obj
    (SyntacticReification.Scope.ofSemantic ⟨Γ,mixed⟩).source = Γ at sourceSame
  rw [sourceSame] at same
  exact same

theorem arrow_heq_mixed {n k : Nat} {source destination : QuotientCwf.QContext D}
    (sourceScope : ScopeData (QuotientCwf.withTerminal D) (generatedModel D).doctrine
      (generatedModel D).assumptions n source)
    (targetScope : ScopeData (QuotientCwf.withTerminal D) (generatedModel D).doctrine
      (generatedModel D).assumptions k destination)
    (arrow : (Interpretation.SourceModel.{u,z} D).toCwf.Sub
      (ULift.up source) (ULift.up destination)) :
    HEq (first.morphism.toFamilyMorphism.base.map arrow)
      (second.morphism.toFamilyMorphism.base.map arrow) := by
  rcases source with ⟨⟨sourceArity,sourceRaw,sourceFormed⟩⟩
  rcases destination with ⟨⟨targetArity,targetRaw,targetFormed⟩⟩
  have sourceIndex := SyntacticScopes.scope_arity sourceScope
  have targetIndex := SyntacticScopes.scope_arity targetScope
  cases sourceIndex
  cases targetIndex
  exact arrow_heq headers first second ⟨sourceRaw,sourceFormed,sourceScope⟩
    ⟨targetRaw,targetFormed,targetScope⟩ arrow

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.ModelMapComparison
