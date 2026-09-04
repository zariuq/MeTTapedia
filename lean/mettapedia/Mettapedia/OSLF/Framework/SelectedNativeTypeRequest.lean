import Mathlib.CategoryTheory.Functor.Basic
import Mettapedia.OSLF.Framework.SelectedNativeTypeDemandRefinement
import Mettapedia.OSLF.Framework.SelectedNativeTypeFoundationRequest

/-!
# Total requests for sparse native-type generation

A request consists of one validated source GSLT and one intrinsically profiled
demand over that source.  A request morphism has the canonical incremental
shape: injective structural reindexing followed by an exact complete residual.
It therefore preserves existing carrier slots, occurrence order, multiplicity,
and local profile rows.

The `foundationProjection` functor exposes the profile-independent syntactic
foundation as an internal factor.  It is not the full native-type generator:
different hypercube vertices may have the same foundation projection.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open CategoryTheory

/-- Complete dependent input to sparse native-type generation. -/
structure SelectedNativeTypeRequest where
  language : ValidatedLanguageDef
  demand : SelectedNativeTypeDemand language

namespace SelectedNativeTypeRequest

/-- Structural reindexing without adding selected occurrences. -/
noncomputable def reindex (request : SelectedNativeTypeRequest)
    {target : ValidatedLanguageDef}
    (structural : StructuralMorphism request.language target) :
    SelectedNativeTypeRequest where
  language := target
  demand := request.demand.map structural

/-- Append a target-local complete residual without changing the source. -/
def append (request : SelectedNativeTypeRequest)
    (residual : SelectedNativeTypeDemand request.language) :
    SelectedNativeTypeRequest where
  language := request.language
  demand := request.demand.append residual

/-- Injective structural reindexing followed by exact stable-prefix growth. -/
structure Morphism (source target : SelectedNativeTypeRequest) where
  structural : StructuralMorphism source.language target.language
  sortInjective : Function.Injective structural.symbols.sort
  residual : SelectedNativeTypeDemand target.language
  target_eq :
    (source.demand.map structural).append residual = target.demand

namespace Morphism

/-- Structural action and complete residual determine a request morphism. -/
@[ext]
theorem ext {source target : SelectedNativeTypeRequest}
    {first second : Morphism source target}
    (structural : first.structural = second.structural)
    (residual : first.residual = second.residual) : first = second := by
  cases first
  cases second
  cases structural
  cases residual
  rfl

/-- Identity request transformation. -/
noncomputable def id (request : SelectedNativeTypeRequest) :
    Morphism request request where
  structural := StructuralMorphism.id request.language
  sortInjective := fun _ _ equality => equality
  residual := SelectedNativeTypeDemand.empty request.language
  target_eq := by
    rw [SelectedNativeTypeDemand.map_id,
      SelectedNativeTypeDemand.append_empty]

/-- Composition transports the earlier complete residual before appending the
later one. -/
noncomputable def comp {first second third : SelectedNativeTypeRequest}
    (earlier : Morphism first second)
    (later : Morphism second third) :
    Morphism first third where
  structural := StructuralMorphism.comp earlier.structural later.structural
  sortInjective := later.sortInjective.comp earlier.sortInjective
  residual :=
    (earlier.residual.map later.structural).append later.residual
  target_eq := by
    rw [SelectedNativeTypeDemand.map_comp,
      ← SelectedNativeTypeDemand.append_assoc,
      ← SelectedNativeTypeDemand.map_append,
      earlier.target_eq, later.target_eq]

/-- Pure horizontal reindexing has an empty residual. -/
noncomputable def reindex (request : SelectedNativeTypeRequest)
    {target : ValidatedLanguageDef}
    (structural : StructuralMorphism request.language target)
    (sortInjective : Function.Injective structural.symbols.sort) :
    Morphism request (request.reindex structural) where
  structural := structural
  sortInjective := sortInjective
  residual := SelectedNativeTypeDemand.empty target
  target_eq := SelectedNativeTypeDemand.append_empty _

/-- Pure stable-prefix refinement has identity structural action. -/
noncomputable def ofRefinement
    {source : ValidatedLanguageDef}
    {earlier later : SelectedNativeTypeDemand source}
    (refinement : SelectedNativeTypeDemand.Refinement earlier later) :
    Morphism ⟨source, earlier⟩ ⟨source, later⟩ where
  structural := StructuralMorphism.id source
  sortInjective := fun _ _ equality => equality
  residual := refinement.residual
  target_eq := by
    rw [SelectedNativeTypeDemand.map_id]
    exact refinement.target_eq

/-- Canonical horizontal part of a mixed request transformation. -/
noncomputable def horizontalPart
    {source target : SelectedNativeTypeRequest}
  (morphism : Morphism source target) :
    Morphism source (source.reindex morphism.structural) :=
  reindex source morphism.structural morphism.sortInjective

/-- Canonical vertical part of a mixed request transformation. -/
noncomputable def verticalPart
    {source target : SelectedNativeTypeRequest}
    (morphism : Morphism source target) :
    Morphism (source.reindex morphism.structural) target :=
  ofRefinement
    { residual := morphism.residual
      target_eq := morphism.target_eq }

/-- Every mixed request transformation factors as structural reindexing
followed by exact stable-prefix refinement. -/
theorem horizontal_vertical_factorization
    {source target : SelectedNativeTypeRequest}
    (morphism : Morphism source target) :
    comp morphism.horizontalPart morphism.verticalPart = morphism := by
  apply Morphism.ext
  · apply StructuralMorphism.ext
    rfl
  · simp only [horizontalPart, verticalPart, reindex, ofRefinement, comp]
    exact SelectedNativeTypeDemand.empty_append morphism.residual

/-- Every transformation retains the mapped occurrence list as a prefix. -/
theorem typings_prefix {source target : SelectedNativeTypeRequest}
    (morphism : Morphism source target) :
    (source.demand.map morphism.structural).foundation.typings.IsPrefix
      target.demand.foundation.typings := by
  rw [← morphism.target_eq, SelectedNativeTypeDemand.append_foundation]
  exact List.prefix_append _ _

/-- Every transformation retains the mapped local profile rows as a prefix. -/
theorem choices_prefix {source target : SelectedNativeTypeRequest}
    (morphism : Morphism source target) :
    (source.demand.map morphism.structural).choices.IsPrefix
      target.demand.choices := by
  rw [← morphism.target_eq, SelectedNativeTypeDemand.append_choices]
  exact List.prefix_append _ _

end Morphism

/-- Complete sparse-generation requests form the total category of injective
structural reindexing and stable-prefix profiled growth. -/
noncomputable instance : CategoryTheory.Category SelectedNativeTypeRequest where
  Hom := Morphism
  id := Morphism.id
  comp := Morphism.comp
  id_comp morphism := by
    apply Morphism.ext
    · apply StructuralMorphism.ext
      simp [Morphism.comp, Morphism.id, StructuralMorphism.comp,
        StructuralMorphism.id, LanguageDefSymbolMap.comp,
        LanguageDefSymbolMap.id]
    · simp [Morphism.comp, Morphism.id,
        SelectedNativeTypeDemand.empty_append]
  comp_id morphism := by
    apply Morphism.ext
    · apply StructuralMorphism.ext
      simp [Morphism.comp, Morphism.id, StructuralMorphism.comp,
        StructuralMorphism.id, LanguageDefSymbolMap.comp,
        LanguageDefSymbolMap.id]
    · simp [Morphism.comp, Morphism.id,
        SelectedNativeTypeDemand.append_empty]
  assoc first second third := by
    apply Morphism.ext
    · apply StructuralMorphism.ext
      rfl
    · simp only [Morphism.comp]
      rw [SelectedNativeTypeDemand.map_append,
        SelectedNativeTypeDemand.map_comp,
        SelectedNativeTypeDemand.append_assoc]

/-- Forget generation coordinates and retain the authored source-language
map. -/
noncomputable def forgetDemand :
    CategoryTheory.Functor SelectedNativeTypeRequest ValidatedLanguageDef where
  obj request := request.language
  map morphism := morphism.structural
  map_id request := by
    apply StructuralMorphism.ext
    rfl
  map_comp earlier later := by
    apply StructuralMorphism.ext
    rfl

/-- Project to the profile-independent foundation request.  This is an
internal factorization of generation input, not an alternative public
language representation. -/
noncomputable def foundationProjection :
    CategoryTheory.Functor SelectedNativeTypeRequest
      SelectedNativeTypeFoundation.FoundationRequest where
  obj request := ⟨request.language, request.demand.foundation⟩
  map morphism :=
    { structural := morphism.structural
      sortInjective := morphism.sortInjective
      residual := morphism.residual.foundation
      target_eq := by
        simpa using congrArg SelectedNativeTypeDemand.foundation
          morphism.target_eq }
  map_id request := by
    apply SelectedNativeTypeFoundation.FoundationMorphism.ext
    · rfl
    · rfl
  map_comp earlier later := by
    apply SelectedNativeTypeFoundation.FoundationMorphism.ext
    · rfl
    · change
        ((earlier.residual.map later.structural).append
            later.residual).foundation =
          (earlier.residual.foundation.map later.structural).append
            later.residual.foundation
      rw [SelectedNativeTypeDemand.append_foundation,
        SelectedNativeTypeDemand.map_foundation]

/-- Reindexing commutes with stable-prefix growth. -/
theorem reindex_append_square
    (request : SelectedNativeTypeRequest)
    (residual : SelectedNativeTypeDemand request.language)
    {target : ValidatedLanguageDef}
    (structural : StructuralMorphism request.language target)
    (sortInjective : Function.Injective structural.symbols.sort) :
    Morphism.comp
        (Morphism.reindex request structural sortInjective)
        (Morphism.ofRefinement
          { residual := residual.map structural
            target_eq := (SelectedNativeTypeDemand.map_append structural
              request.demand residual).symm }) =
      Morphism.comp
        (Morphism.ofRefinement
          (SelectedNativeTypeDemand.appendRefinement request.demand residual))
        (Morphism.reindex (request.append residual)
          structural sortInjective) := by
  apply Morphism.ext
  · apply StructuralMorphism.ext
    rfl
  · simp only [Morphism.comp, Morphism.reindex, Morphism.ofRefinement,
      SelectedNativeTypeDemand.appendRefinement]
    exact (SelectedNativeTypeDemand.append_empty
      (residual.map structural)).symm

/-! ## Positive and negative controls -/

namespace Canary

/-- Every request has a transformation identity. -/
theorem identity_exists (request : SelectedNativeTypeRequest) :
    Nonempty (request ⟶ request) :=
  ⟨Morphism.id request⟩

/-- A non-injective sort action cannot underlie a request transformation. -/
theorem noninjective_sort_map_is_rejected
    {source target : SelectedNativeTypeRequest}
    (structural : StructuralMorphism source.language target.language)
    (left right : String)
    (sameImage : structural.symbols.sort left =
      structural.symbols.sort right)
    (distinct : left ≠ right) :
    ¬ ∃ morphism : source ⟶ target,
      morphism.structural = structural := by
  rintro ⟨morphism, equality⟩
  apply distinct
  apply morphism.sortInjective
  rw [equality]
  exact sameImage

/-- A transformation cannot silently change an already mapped profile row. -/
theorem no_transformation_without_mapped_choice_prefix
    {source target : SelectedNativeTypeRequest}
    (structural : StructuralMorphism source.language target.language)
    (notPrefix :
      ¬ (source.demand.map structural).choices.IsPrefix
        target.demand.choices) :
    ¬ ∃ morphism : source ⟶ target,
      morphism.structural = structural := by
  rintro ⟨morphism, equality⟩
  apply notPrefix
  rw [← equality]
  exact morphism.choices_prefix

end Canary

#print axioms Morphism.comp
#print axioms Morphism.horizontal_vertical_factorization
#print axioms Morphism.typings_prefix
#print axioms Morphism.choices_prefix
#print axioms forgetDemand
#print axioms foundationProjection
#print axioms reindex_append_square
#print axioms Canary.identity_exists
#print axioms Canary.noninjective_sort_map_is_rejected
#print axioms Canary.no_transformation_without_mapped_choice_prefix

end SelectedNativeTypeRequest

end Mettapedia.OSLF.Framework
