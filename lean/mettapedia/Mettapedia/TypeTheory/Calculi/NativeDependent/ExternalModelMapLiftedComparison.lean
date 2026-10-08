import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntacticQualification
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalModelUniverseReadout
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalModelMapReadout

/-!
# Complete source images at common external carrier levels

The syntax remains at its declared symbol level. Its actual contextual model
is raised by the four-carrier adapter, and every source success is raised from
the earned original evaluator readback. Arbitrary lifted family, section and
substitution classes are lowered before selecting their actual syntactic
representatives. No size restriction on the original model is inferred.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.LiftedModelMapComparison

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualComprehensionMorphism
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualTelescopeMorphism
open SyntacticReification
open Mettapedia.TypeTheory.ContextualCwfUniverseLift

universe u z
variable {S : Symbols.{u}} {D : Signature S}
  {C : CwfWithTerminal.{max u z, max u z, max u z, max u z}} {target : ModelData S C}

variable (headers : HeaderFormation D)
  (first second : ModelMap (SyntacticModel.data headers).commonUniverseLift.{u,u,u,u,u,z} target)

/-- Canonical finite telescope images agree because they evaluate the same
independently authored raw context. -/
theorem image_context_equal {n : Nat} (scope : Scope D n) :
    imageContext first.morphism (liftContext.{u,u,u,u,max u z,max u z,max u z,max u z} scope.semantic) = imageContext second.morphism (liftContext.{u,u,u,u,max u z,max u z,max u z,max u z} scope.semantic) := by
  have left := first.evaluateContext_image scope.raw (liftContext.{u,u,u,u,max u z,max u z,max u z,max u z} scope.semantic)
    ((SyntacticModel.data headers).evaluateContext_universeLift.{u,u,u,u,u,max u z,max u z,max u z,max u z}
      scope.raw scope.semantic (SyntacticModel.scope_context_read headers scope))
  have right := second.evaluateContext_image scope.raw (liftContext.{u,u,u,u,max u z,max u z,max u z,max u z} scope.semantic)
    ((SyntacticModel.data headers).evaluateContext_universeLift.{u,u,u,u,u,max u z,max u z,max u z,max u z}
      scope.raw scope.semantic (SyntacticModel.scope_context_read headers scope))
  exact Option.some.inj (left.symm.trans right)

/-- Both maps can be compared at the first actual target telescope; the
comparison still contains every generic-variable readout. -/
theorem second_context_image {n : Nat} (scope : Scope D n) :
    ContextImage second.morphism (liftContext.{u,u,u,u,max u z,max u z,max u z,max u z} scope.semantic)
      (imageContext first.morphism (liftContext.{u,u,u,u,max u z,max u z,max u z,max u z} scope.semantic)) := by
  rw [image_context_equal headers first second scope]
  exact imageContext_comparison second.morphism (liftContext.{u,u,u,u,max u z,max u z,max u z,max u z} scope.semantic)

theorem context_equal {n : Nat} (scope : Scope D n) :
    context first.morphism (ULift.up ((quotientProjection D).obj scope.source)) =
      context second.morphism (ULift.up ((quotientProjection D).obj scope.source)) :=
  (imageContext_comparison first.morphism (liftContext.{u,u,u,u,max u z,max u z,max u z,max u z} scope.semantic)).contexts.trans
    (second_context_image headers first second scope).contexts.symm

/-- Every supplied complete family class is compared, rather than only a
particular representative chosen for a declaration. -/
theorem type_heq {n : Nat} (scope : Scope D n)
    (A : (commonLift.{u,u,u,u,z} (QuotientCwf.cwf D)).Ty
      (ULift.up ((quotientProjection D).obj scope.source))) :
    HEq (first.morphism.toFamilyMorphism.mapType A)
      (second.morphism.toFamilyMorphism.mapType A) := by
  let annotation := QuotientCwf.typeRepresentative A.down
  have nativeRead := (SyntacticModel.scope_type_read headers scope annotation).trans
    (congrArg some (QuotientCwf.typeRepresentative_class A.down))
  have sourceRead := (SyntacticModel.data headers).evaluateType_universeLift.{u,u,u,u,u,max u z,max u z,max u z,max u z}
    annotation.code scope.semantic A.down nativeRead
  rcases first.evaluateType_image annotation.code (liftContext.{u,u,u,u,max u z,max u z,max u z,max u z} scope.semantic) _
    (imageContext_comparison first.morphism (liftContext.{u,u,u,u,max u z,max u z,max u z,max u z} scope.semantic)) A sourceRead with
      ⟨value, read, related⟩
  have other := second.evaluateType_image_unique annotation.code (liftContext.{u,u,u,u,max u z,max u z,max u z,max u z} scope.semantic) _
    (second_context_image headers first second scope) A value sourceRead read
  exact related.trans other.symm

/-- Annotation re-admission preserves the exact supplied term class before
comparing its two model images. -/
theorem term_heq {n : Nat} (scope : Scope D n)
    {A : (commonLift.{u,u,u,u,z} (QuotientCwf.cwf D)).Ty
      (ULift.up ((quotientProjection D).obj scope.source))}
    (term : (commonLift.{u,u,u,u,z} (QuotientCwf.cwf D)).Tm
      (ULift.up ((quotientProjection D).obj scope.source)) A) :
    HEq (first.morphism.toFamilyMorphism.mapTerm term)
      (second.morphism.toFamilyMorphism.mapTerm term) := by
  let annotation := QuotientCwf.typeRepresentative A.down
  let supplied := QuotientCwf.termRepresentative annotation term.down.val
    (term.down.property.trans (QuotientCwf.typeRepresentative_class A.down).symm)
  have classRead : QTerm.mk supplied = term.down.val := QuotientCwf.termRepresentative_class
    annotation term.down.val (term.down.property.trans (QuotientCwf.typeRepresentative_class A.down).symm)
  have sourceRead := SyntacticModel.scope_term_read headers scope supplied
  have whole :
      (⟨QType.mk annotation, ⟨QTerm.mk supplied, rfl⟩⟩ :
        Value (QuotientCwf.cwf D) ((quotientProjection D).obj scope.source)) = ⟨A.down, term.down⟩ :=
    SyntacticReification.value_ext classRead
  rw [whole] at sourceRead
  have liftedRead := (SyntacticModel.data headers).evaluateTerm_universeLift.{u,u,u,u,u,max u z,max u z,max u z,max u z}
    supplied.code scope.semantic _ sourceRead
  rcases first.evaluateTerm_image supplied.code (liftContext.{u,u,u,u,max u z,max u z,max u z,max u z} scope.semantic) _
    (imageContext_comparison first.morphism (liftContext.{u,u,u,u,max u z,max u z,max u z,max u z} scope.semantic)) _ liftedRead with
      ⟨value, read, related⟩
  have other := second.evaluateTerm_image_unique supplied.code (liftContext.{u,u,u,u,max u z,max u z,max u z,max u z} scope.semantic) _
    (second_context_image headers first second scope) _ value liftedRead read
  exact related.terms.trans other.terms.symm

/-- Actual ordered substitutions, including all dependent positions, have
identical images after transporting their mapped endpoints. -/
theorem arrow_heq {n k : Nat} (source : Scope D n) (destination : Scope D k)
    (arrow : (commonLift.{u,u,u,u,z} (QuotientCwf.cwf D)).Sub
      (ULift.up ((quotientProjection D).obj source.source))
      (ULift.up ((quotientProjection D).obj destination.source))) :
    HEq (first.morphism.toFamilyMorphism.base.map arrow)
      (second.morphism.toFamilyMorphism.base.map arrow) := by
  let raw := QuotientCwf.representative arrow.down
  have sourceRead := (SyntacticModel.scope_substitution_read headers source destination raw).trans
    (congrArg some (QuotientCwf.project_representative arrow.down))
  have liftedRead := (SyntacticModel.data headers).evaluateSubstitution_universeLift.{u,u,u,u,u,max u z,max u z,max u z,max u z}
    source.semantic destination.semantic raw.substitution arrow.down sourceRead
  have left := first.evaluateSubstitution_image (liftContext.{u,u,u,u,max u z,max u z,max u z,max u z} source.semantic) (liftContext.{u,u,u,u,max u z,max u z,max u z,max u z} destination.semantic) _ _
    (imageContext_comparison first.morphism (liftContext.{u,u,u,u,max u z,max u z,max u z,max u z} source.semantic))
    (imageContext_comparison first.morphism (liftContext.{u,u,u,u,max u z,max u z,max u z,max u z} destination.semantic)) raw.substitution arrow liftedRead
  have right := second.evaluateSubstitution_image (liftContext.{u,u,u,u,max u z,max u z,max u z,max u z} source.semantic) (liftContext.{u,u,u,u,max u z,max u z,max u z,max u z} destination.semantic) _ _
    (second_context_image headers first second source)
    (second_context_image headers first second destination) raw.substitution arrow liftedRead
  have actual := Option.some.inj (left.symm.trans right)
  exact (imageArrow_heq first.morphism _ _ arrow).trans
    ((heq_of_eq actual).trans (imageArrow_heq second.morphism _ _ arrow).symm)

/-- The same comparison at any actual finite source telescope, independently
of the chosen scope record used to state the evaluator readbacks. -/
theorem context_equal_telescope {n : Nat} {source : quotientContext D}
    (telescope : Telescope (QuotientCwf.withTerminal D) n source) :
    context first.morphism (ULift.up source) = context second.morphism (ULift.up source) := by
  have same := context_equal headers first second (Scope.ofSemantic ⟨source, telescope⟩)
  have sourceSame := congrArg (fun Γ : Mettapedia.TypeTheory.ContextualModelTelescopes.Context
    (QuotientCwf.withTerminal D) n => Γ.1) (Scope.ofSemantic_semantic ⟨source, telescope⟩)
  change (quotientProjection D).obj (Scope.ofSemantic ⟨source, telescope⟩).source = source at sourceSame
  rw [sourceSame] at same
  exact same

theorem arrow_heq_telescope {n k : Nat} {source destination : quotientContext D}
    (sourceTelescope : Telescope (QuotientCwf.withTerminal D) n source)
    (targetTelescope : Telescope (QuotientCwf.withTerminal D) k destination)
    (arrow : (commonLift.{u,u,u,u,z} (QuotientCwf.cwf D)).Sub (ULift.up source) (ULift.up destination)) :
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

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.LiftedModelMapComparison
