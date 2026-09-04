import Mathlib.CategoryTheory.Functor.Basic
import Mettapedia.OSLF.Framework.SelectedNativeTypeFoundationRefinement
import Mettapedia.OSLF.Framework.SelectedNativeTypeFoundationTransport

/-!
# Selected native-type foundation requests

Sparse native-type generation consumes one validated source GSLT together
with an ordered typed demand.  The source language remains the only authored
language; a generation request is merely dependent input to the generator.

A request morphism has one canonical operational shape:

1. reindex the complete demand along an injective structural language map;
2. append an exact residual demand at the target.

This is the total, Grothendieck-style category combining horizontal source
change with vertical demand growth.  The residual is explicit, so a morphism
cannot silently delete, reorder, or merge already allocated carrier and
occurrence slots.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open CategoryTheory

namespace SelectedNativeTypeFoundation

/-- Dependent input to sparse native-type generation: one source GSLT and the
exact typed occurrences requested from it. -/
structure FoundationRequest where
  language : ValidatedLanguageDef
  demand : Demand language

/-- Reindex a request along a structural language map, without adding any new
typed occurrences. -/
noncomputable def FoundationRequest.reindex
    (request : FoundationRequest)
    {target : ValidatedLanguageDef}
    (structural : StructuralMorphism request.language target) :
    FoundationRequest where
  language := target
  demand := request.demand.map structural

/-- Append a target-local residual demand without changing the source GSLT. -/
def FoundationRequest.append (request : FoundationRequest)
    (residual : Demand request.language) : FoundationRequest where
  language := request.language
  demand := request.demand.append residual

/-- A request transformation is injective reindexing followed by exact
append-only demand growth. -/
structure FoundationMorphism (source target : FoundationRequest) where
  structural : StructuralMorphism source.language target.language
  sortInjective : Function.Injective structural.symbols.sort
  residual : Demand target.language
  target_eq :
    (source.demand.map structural).append residual = target.demand

namespace FoundationMorphism

/-- Structural action and exact residual determine a request morphism. -/
@[ext]
theorem ext {source target : FoundationRequest}
    {first second : FoundationMorphism source target}
    (structural : first.structural = second.structural)
    (residual : first.residual = second.residual) : first = second := by
  cases first
  cases second
  cases structural
  cases residual
  rfl

/-- Identity request transformation. -/
noncomputable def id (request : FoundationRequest) :
    FoundationMorphism request request where
  structural := StructuralMorphism.id request.language
  sortInjective := fun _ _ equality => equality
  residual := Demand.empty request.language
  target_eq := by
    rw [Demand.map_id, Demand.append_empty]

/-- Consecutive request transformations compose by transporting the first
residual before appending the second. -/
noncomputable def comp {first second third : FoundationRequest}
    (earlier : FoundationMorphism first second)
    (later : FoundationMorphism second third) :
    FoundationMorphism first third where
  structural := StructuralMorphism.comp earlier.structural later.structural
  sortInjective := later.sortInjective.comp earlier.sortInjective
  residual :=
    (earlier.residual.map later.structural).append later.residual
  target_eq := by
    rw [Demand.map_comp, ← Demand.append_assoc,
      ← Demand.map_append, earlier.target_eq, later.target_eq]

/-- Pure horizontal reindexing has an empty residual. -/
noncomputable def reindex (request : FoundationRequest)
    {target : ValidatedLanguageDef}
    (structural : StructuralMorphism request.language target)
    (sortInjective : Function.Injective structural.symbols.sort) :
    FoundationMorphism request (request.reindex structural) where
  structural := structural
  sortInjective := sortInjective
  residual := Demand.empty target
  target_eq := Demand.append_empty _

/-- Pure vertical refinement has identity structural action. -/
noncomputable def ofDemandRefinement
    {source : ValidatedLanguageDef} {earlier later : Demand source}
    (refinement : DemandRefinement earlier later) :
    FoundationMorphism
      ⟨source, earlier⟩ ⟨source, later⟩ where
  structural := StructuralMorphism.id source
  sortInjective := fun _ _ equality => equality
  residual := refinement.residual
  target_eq := by
    rw [Demand.map_id]
    exact refinement.target_eq

/-- Canonical horizontal part of a mixed request transformation. -/
noncomputable def horizontalPart {source target : FoundationRequest}
    (morphism : FoundationMorphism source target) :
    FoundationMorphism source (source.reindex morphism.structural) :=
  reindex source morphism.structural morphism.sortInjective

/-- Canonical vertical part of a mixed request transformation. -/
noncomputable def verticalPart {source target : FoundationRequest}
    (morphism : FoundationMorphism source target) :
    FoundationMorphism (source.reindex morphism.structural) target :=
  ofDemandRefinement
    { residual := morphism.residual
      target_eq := morphism.target_eq }

/-- Every mixed transformation factors as exact reindexing followed by exact
append-only refinement. -/
theorem horizontal_vertical_factorization
    {source target : FoundationRequest}
    (morphism : FoundationMorphism source target) :
    comp morphism.horizontalPart morphism.verticalPart = morphism := by
  apply FoundationMorphism.ext
  · apply StructuralMorphism.ext
    rfl
  · simp only [horizontalPart, verticalPart, reindex,
      ofDemandRefinement, comp]
    apply Demand.ext
    change [] ++ morphism.residual.typings = morphism.residual.typings
    simp

/-- Every request transformation retains the structurally mapped typing list
as an ordered prefix of its target. -/
theorem typings_prefix {source target : FoundationRequest}
    (morphism : FoundationMorphism source target) :
    (source.demand.map morphism.structural).typings.IsPrefix
      target.demand.typings := by
  rw [← morphism.target_eq]
  exact List.prefix_append _ _

end FoundationMorphism

/-- Generation requests form the total category of injective structural
reindexing and append-only demand refinement. -/
noncomputable instance : CategoryTheory.Category FoundationRequest where
  Hom := FoundationMorphism
  id := FoundationMorphism.id
  comp := FoundationMorphism.comp
  id_comp morphism := by
    apply FoundationMorphism.ext
    · apply StructuralMorphism.ext
      simp [FoundationMorphism.comp, FoundationMorphism.id,
        StructuralMorphism.comp, StructuralMorphism.id,
        LanguageDefSymbolMap.comp, LanguageDefSymbolMap.id]
    · apply Demand.ext
      simp [FoundationMorphism.comp, FoundationMorphism.id,
        Demand.map, Demand.append]
  comp_id morphism := by
    apply FoundationMorphism.ext
    · apply StructuralMorphism.ext
      simp [FoundationMorphism.comp, FoundationMorphism.id,
        StructuralMorphism.comp, StructuralMorphism.id,
        LanguageDefSymbolMap.comp, LanguageDefSymbolMap.id]
    · simp only [FoundationMorphism.comp, FoundationMorphism.id]
      rw [Demand.map_id, Demand.append_empty]
  assoc first second third := by
    apply FoundationMorphism.ext
    · apply StructuralMorphism.ext
      rfl
    · simp only [FoundationMorphism.comp]
      rw [Demand.map_append, Demand.map_comp, Demand.append_assoc]

/-- Forget demand growth and retain the underlying structural language map. -/
noncomputable def forgetDemand :
    CategoryTheory.Functor FoundationRequest ValidatedLanguageDef where
  obj request := request.language
  map morphism := morphism.structural
  map_id request := by
    apply StructuralMorphism.ext
    rfl
  map_comp earlier later := by
    apply StructuralMorphism.ext
    rfl

/-- Reindexing commutes with append-only growth.  This is the elementary
horizontal/vertical square underlying the total request category. -/
theorem reindex_append_square
    (request : FoundationRequest)
    (residual : Demand request.language)
    {target : ValidatedLanguageDef}
    (structural : StructuralMorphism request.language target)
    (sortInjective : Function.Injective structural.symbols.sort) :
    FoundationMorphism.comp
        (FoundationMorphism.reindex request structural sortInjective)
        (FoundationMorphism.ofDemandRefinement
          { residual := residual.map structural
            target_eq := (Demand.map_append structural
              request.demand residual).symm }) =
      FoundationMorphism.comp
        (FoundationMorphism.ofDemandRefinement
          (appendRefinement request.demand residual))
        (FoundationMorphism.reindex (request.append residual)
          structural sortInjective) := by
  apply FoundationMorphism.ext
  · apply StructuralMorphism.ext
    rfl
  · simp only [FoundationMorphism.comp, FoundationMorphism.reindex,
      FoundationMorphism.ofDemandRefinement, appendRefinement]
    apply Demand.ext
    simp [FoundationRequest.reindex, FoundationRequest.append,
      Demand.map, Demand.append]
    exact (List.append_nil _).symm

/-! ## Positive and negative controls -/

namespace FoundationRequestCanary

private def sourceLanguage : LanguageDef :=
  { name := "selected-native-request:two-sorts"
    types := [TypeDecl.plain "selected-native-request:A",
      TypeDecl.plain "selected-native-request:B"]
    terms := []
    equations := []
    rewrites := [] }

private def targetLanguage : LanguageDef :=
  { name := "selected-native-request:one-sort"
    types := [TypeDecl.plain "selected-native-request:Merged"]
    terms := []
    equations := []
    rewrites := [] }

private theorem sourceLanguage_valid : sourceLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [sourceLanguage, LanguageDef.typeNames, TypeDecl.plain]

private theorem targetLanguage_valid : targetLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [targetLanguage, LanguageDef.typeNames, TypeDecl.plain]

private def sourceDefinition : ValidatedLanguageDef :=
  ⟨sourceLanguage, sourceLanguage_valid⟩

private def targetDefinition : ValidatedLanguageDef :=
  ⟨targetLanguage, targetLanguage_valid⟩

private def collapseSymbols : LanguageDefSymbolMap where
  sort := fun _ => "selected-native-request:Merged"
  constructor := _root_.id
  relation := _root_.id
  equation := _root_.id
  rewrite := _root_.id

private def collapse : StructuralMorphism sourceDefinition targetDefinition where
  symbols := collapseSymbols
  mapsTypes declaration membership := by
    change List.Mem declaration
      [TypeDecl.plain "selected-native-request:A",
        TypeDecl.plain "selected-native-request:B"] at membership
    rcases List.mem_cons.mp membership with equality | tailMembership
    · subst declaration
      exact List.Mem.head _
    · have equality := List.mem_singleton.mp tailMembership
      subst declaration
      exact List.Mem.head _
  mapsTerms declaration membership := by
    exact False.elim (List.not_mem_nil membership)
  mapsEquations declaration membership := by
    exact False.elim (List.not_mem_nil membership)
  mapsRewrites declaration membership := by
    exact False.elim (List.not_mem_nil membership)

private def source : FoundationRequest :=
  ⟨sourceDefinition, Demand.empty sourceDefinition⟩

private def target : FoundationRequest :=
  ⟨targetDefinition, Demand.empty targetDefinition⟩

/-- Every generation request has a transformation identity. -/
theorem identity_exists : Nonempty (source ⟶ source) :=
  ⟨FoundationMorphism.id source⟩

/-- A structural map that merges source sorts cannot underlie a request
transformation, even when both demands are empty. -/
theorem collapsing_sort_map_is_rejected :
    ¬ ∃ morphism : source ⟶ target,
      morphism.structural = collapse := by
  rintro ⟨morphism, equality⟩
  have merged :
      "selected-native-request:A" = "selected-native-request:B" :=
    morphism.sortInjective (by
      rw [equality]
      rfl)
  have distinct :
      "selected-native-request:A" ≠ "selected-native-request:B" := by
    decide
  exact distinct merged

/-- A transformation cannot shrink or reorder the already mapped typing
prefix. -/
theorem no_transformation_without_mapped_prefix
    {source target : FoundationRequest}
    (structural : StructuralMorphism source.language target.language)
    (notPrefix :
      ¬ (source.demand.map structural).typings.IsPrefix
        target.demand.typings) :
    ¬ ∃ morphism : source ⟶ target,
      morphism.structural = structural := by
  rintro ⟨morphism, equality⟩
  apply notPrefix
  rw [← equality]
  exact morphism.typings_prefix

end FoundationRequestCanary

#print axioms FoundationMorphism.comp
#print axioms FoundationMorphism.horizontal_vertical_factorization
#print axioms FoundationMorphism.typings_prefix
#print axioms forgetDemand
#print axioms reindex_append_square
#print axioms FoundationRequestCanary.identity_exists
#print axioms FoundationRequestCanary.collapsing_sort_map_is_rejected
#print axioms FoundationRequestCanary.no_transformation_without_mapped_prefix

end SelectedNativeTypeFoundation

end Mettapedia.OSLF.Framework
