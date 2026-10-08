import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntacticQualification
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalModelMapReadout

/-!
# Earned comparisons on the finite chosen source image

Exact authored declaration formation supplies the source evaluator readbacks.
Local primitive and logical model-map laws then identify actual context, family,
section and substitution images. Every comparison below follows from those
readbacks and deterministic target evaluation; no complete-expression or
chosen-image preservation field is supplied.

These comparisons are on actual finite comprehension telescopes. Retained raw
contexts require the presentation isomorphism in the next layer.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.ModelMapComparison

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualComprehensionMorphism
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualTelescopeMorphism
open SyntacticReification

universe u
variable {S : Symbols.{u}} {D : Signature S}
  {C : CwfWithTerminal.{u, u, u, u}} {target : ModelData S C}

variable (headers : HeaderFormation D)
  (first second : ModelMap (SyntacticModel.data headers) target)

/-- Canonical finite telescope images agree because they evaluate the same
independently authored raw context. -/
theorem image_context_equal {n : Nat} (scope : Scope D n) :
    imageContext first.morphism scope.semantic = imageContext second.morphism scope.semantic := by
  have left := first.evaluateContext_image scope.raw scope.semantic
    (SyntacticModel.scope_context_read headers scope)
  have right := second.evaluateContext_image scope.raw scope.semantic
    (SyntacticModel.scope_context_read headers scope)
  exact Option.some.inj (left.symm.trans right)

/-- Both maps can be compared at the first actual target telescope; the
comparison still contains every generic-variable readout. -/
theorem second_context_image {n : Nat} (scope : Scope D n) :
    ContextImage second.morphism scope.semantic
      (imageContext first.morphism scope.semantic) := by
  rw [image_context_equal headers first second scope]
  exact imageContext_comparison second.morphism scope.semantic

theorem context_equal {n : Nat} (scope : Scope D n) :
    context first.morphism ((quotientProjection D).obj scope.source) =
      context second.morphism ((quotientProjection D).obj scope.source) :=
  (imageContext_comparison first.morphism scope.semantic).contexts.trans
    (second_context_image headers first second scope).contexts.symm

/-- Every supplied complete family class is compared, rather than only a
particular representative chosen for a declaration. -/
theorem type_heq {n : Nat} (scope : Scope D n)
    (A : QuotientCwf.Ty ((quotientProjection D).obj scope.source)) :
    HEq (first.morphism.toFamilyMorphism.mapType A)
      (second.morphism.toFamilyMorphism.mapType A) := by
  let annotation := QuotientCwf.typeRepresentative A
  have sourceRead := (SyntacticModel.scope_type_read headers scope annotation).trans
    (congrArg some (QuotientCwf.typeRepresentative_class A))
  rcases first.evaluateType_image annotation.code scope.semantic _
    (imageContext_comparison first.morphism scope.semantic) A sourceRead with
      ⟨value, read, related⟩
  have other := second.evaluateType_image_unique annotation.code scope.semantic _
    (second_context_image headers first second scope) A value sourceRead read
  exact related.trans other.symm

/-- Annotation re-admission preserves the exact supplied term class before
comparing its two model images. -/
theorem term_heq {n : Nat} (scope : Scope D n)
    {A : QuotientCwf.Ty ((quotientProjection D).obj scope.source)}
    (term : QuotientCwf.Tm ((quotientProjection D).obj scope.source) A) :
    HEq (first.morphism.toFamilyMorphism.mapTerm term)
      (second.morphism.toFamilyMorphism.mapTerm term) := by
  let annotation := QuotientCwf.typeRepresentative A
  let supplied := QuotientCwf.termRepresentative annotation term.val
    (term.property.trans (QuotientCwf.typeRepresentative_class A).symm)
  have classRead : QTerm.mk supplied = term.val := QuotientCwf.termRepresentative_class
    annotation term.val (term.property.trans (QuotientCwf.typeRepresentative_class A).symm)
  have sourceRead := SyntacticModel.scope_term_read headers scope supplied
  have whole :
      (⟨QType.mk annotation, ⟨QTerm.mk supplied, rfl⟩⟩ :
        Value (QuotientCwf.cwf D) ((quotientProjection D).obj scope.source)) = ⟨A, term⟩ :=
    SyntacticReification.value_ext classRead
  rw [whole] at sourceRead
  rcases first.evaluateTerm_image supplied.code scope.semantic _
    (imageContext_comparison first.morphism scope.semantic) _ sourceRead with
      ⟨value, read, related⟩
  have other := second.evaluateTerm_image_unique supplied.code scope.semantic _
    (second_context_image headers first second scope) _ value sourceRead read
  exact related.terms.trans other.terms.symm

/-- Actual ordered substitutions, including all dependent positions, have
identical images after transporting their mapped endpoints. -/
theorem arrow_heq {n k : Nat} (source : Scope D n) (destination : Scope D k)
    (arrow : (quotientProjection D).obj source.source ⟶
      (quotientProjection D).obj destination.source) :
    HEq (first.morphism.toFamilyMorphism.base.map arrow)
      (second.morphism.toFamilyMorphism.base.map arrow) := by
  let raw := QuotientCwf.representative arrow
  have sourceRead := (SyntacticModel.scope_substitution_read headers source destination raw).trans
    (congrArg some (QuotientCwf.project_representative arrow))
  have left := first.evaluateSubstitution_image source.semantic destination.semantic _ _
    (imageContext_comparison first.morphism source.semantic)
    (imageContext_comparison first.morphism destination.semantic) raw.substitution arrow sourceRead
  have right := second.evaluateSubstitution_image source.semantic destination.semantic _ _
    (second_context_image headers first second source)
    (second_context_image headers first second destination) raw.substitution arrow sourceRead
  have actual := Option.some.inj (left.symm.trans right)
  exact (imageArrow_heq first.morphism _ _ arrow).trans
    ((heq_of_eq actual).trans (imageArrow_heq second.morphism _ _ arrow).symm)

/-- The same comparison at any actual finite source telescope, independently
of the chosen scope record used to state the evaluator readbacks. -/
theorem context_equal_telescope {n : Nat} {source : quotientContext D}
    (telescope : Telescope (QuotientCwf.withTerminal D) n source) :
    context first.morphism source = context second.morphism source := by
  have same := context_equal headers first second (Scope.ofSemantic ⟨source, telescope⟩)
  have sourceSame := congrArg (fun Γ : Mettapedia.TypeTheory.ContextualModelTelescopes.Context
    (QuotientCwf.withTerminal D) n => Γ.1) (Scope.ofSemantic_semantic ⟨source, telescope⟩)
  change (quotientProjection D).obj (Scope.ofSemantic ⟨source, telescope⟩).source = source at sourceSame
  rw [sourceSame] at same
  exact same

theorem arrow_heq_telescope {n k : Nat} {source destination : quotientContext D}
    (sourceTelescope : Telescope (QuotientCwf.withTerminal D) n source)
    (targetTelescope : Telescope (QuotientCwf.withTerminal D) k destination)
    (arrow : source ⟶ destination) :
    HEq (first.morphism.toFamilyMorphism.base.map arrow)
      (second.morphism.toFamilyMorphism.base.map arrow) := by
  rcases source with ⟨⟨sourceArity, sourceRaw, sourceFormed⟩⟩
  rcases destination with ⟨⟨targetArity, targetRaw, targetFormed⟩⟩
  have sourceIndex := SyntacticTelescopes.telescope_arity sourceTelescope
  have targetIndex := SyntacticTelescopes.telescope_arity targetTelescope
  cases sourceIndex
  cases targetIndex
  exact arrow_heq headers first second ⟨sourceRaw, sourceFormed, sourceTelescope⟩
    ⟨targetRaw, targetFormed, targetTelescope⟩ arrow

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.ModelMapComparison
