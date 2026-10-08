import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalModelMapReadout
import Mettapedia.TypeTheory.ContextualLogicalMorphismComposition

/-!
# Composition of external dependent model maps

The actual contextual, logical and primitive actions compose locally.
Their unit and associativity equations follow from the underlying strict
maps; all other fields express earned local preservation. Successful raw
readouts retain both intermediate and final supplied sections.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualComprehensionMorphism
open Mettapedia.TypeTheory.ContextualTelescopeMorphism
open Mettapedia.TypeTheory.ContextualStrictMorphismComposition
open Mettapedia.TypeTheory.ContextualLogicalMorphism

universe a c s t m
variable {S : Symbols.{a}} {C D E H : CwfWithTerminal.{c, s, t, m}}

namespace ModelMap

def identity (model : ModelData S C) : ModelMap model model where
  morphism := StrictCwfMorphism.identity C
  logical := LogicalPreservation.identity model.products model.sums.operations
  typeParameters symbol := contextImage_identity (model.typeParameters symbol)
  typeFamily _ := HEq.rfl
  termParameters symbol := contextImage_identity (model.termParameters symbol)
  termType _ := HEq.rfl
  termValue _ := HEq.rfl

def comp {source : ModelData S C} {middle : ModelData S D} {target : ModelData S E}
    (earlier : ModelMap source middle) (later : ModelMap middle target) : ModelMap source target where
  morphism := compose earlier.morphism later.morphism
  logical := earlier.logical.comp later.logical
  typeParameters symbol := contextImage_comp earlier.morphism later.morphism
    (earlier.typeParameters symbol) (later.typeParameters symbol)
  typeFamily symbol := (mappedType_heq later.morphism (earlier.typeParameters symbol).contexts
    (earlier.typeFamily symbol)).trans (later.typeFamily symbol)
  termParameters symbol := contextImage_comp earlier.morphism later.morphism
    (earlier.termParameters symbol) (later.termParameters symbol)
  termType symbol := (mappedType_heq later.morphism (earlier.termParameters symbol).contexts
    (earlier.termType symbol)).trans (later.termType symbol)
  termValue symbol := (mappedTerm_heq later.morphism (earlier.termParameters symbol).contexts
    (earlier.termType symbol) (earlier.termValue symbol)).trans (later.termValue symbol)

theorem ext_of_morphism {source : ModelData S C} {target : ModelData S D}
    {first second : ModelMap source target} (same : first.morphism = second.morphism) : first = second := by
  cases first
  cases second
  cases same
  rfl

@[simp] theorem identity_comp {source : ModelData S C} {target : ModelData S D}
    (mapping : ModelMap source target) : (identity source).comp mapping = mapping :=
  ext_of_morphism (ContextualStrictMorphismComposition.identity_comp mapping.morphism)

@[simp] theorem comp_identity {source : ModelData S C} {target : ModelData S D}
    (mapping : ModelMap source target) : mapping.comp (identity target) = mapping :=
  ext_of_morphism (ContextualStrictMorphismComposition.comp_identity mapping.morphism)

theorem assoc {source : ModelData S C} {middle : ModelData S D}
    {later : ModelData S E} {target : ModelData S H}
    (first : ModelMap source middle) (second : ModelMap middle later) (third : ModelMap later target) :
    (first.comp second).comp third = first.comp (second.comp third) :=
  ext_of_morphism (ContextualStrictMorphismComposition.assoc first.morphism second.morphism third.morphism)

theorem context_composition {source : ModelData S C} {middle : ModelData S D} {target : ModelData S E}
    (first : ModelMap source middle) (second : ModelMap middle target) {n : Nat} (Γ : Context C n) :
    imageContext (first.comp second).morphism Γ =
      imageContext second.morphism (imageContext first.morphism Γ) :=
  ContextualStrictMorphismComposition.imageContext_comp first.morphism second.morphism Γ.2

theorem term_composition {source : ModelData S C} {middle : ModelData S D} {target : ModelData S E}
    (first : ModelMap source middle) (second : ModelMap middle target)
    {Γ : C.toCwf.Ctx} {A : C.toCwf.Ty Γ} (value : C.toCwf.Tm Γ A) :
    (first.comp second).morphism.toFamilyMorphism.mapTerm value =
      second.morphism.toFamilyMorphism.mapTerm (first.morphism.toFamilyMorphism.mapTerm value) := rfl

theorem evaluateTerm_composition {source : ModelData S C} {middle : ModelData S D} {target : ModelData S E}
    (first : ModelMap source middle) (second : ModelMap middle target) {n : Nat}
    (term : TermExpr S n) (Γ : Context C n) (Δ : Context D n) (Θ : Context E n)
    (earlierContexts : ContextImage first.morphism Γ Δ)
    (laterContexts : ContextImage second.morphism Δ Θ)
    (value : Value C.toCwf Γ.1) (supplied : source.evaluateTerm Γ term = some value) :
    ∃ middleValue finalValue,
      middle.evaluateTerm Δ term = some middleValue ∧
      target.evaluateTerm Θ term = some finalValue ∧
      ValueImage first.morphism value middleValue ∧
      ValueImage second.morphism middleValue finalValue ∧
      ValueImage (first.comp second).morphism value finalValue := by
  rcases first.evaluateTerm_image term Γ Δ earlierContexts value supplied with
    ⟨middleValue, middleRead, firstValues⟩
  rcases second.evaluateTerm_image term Δ Θ laterContexts middleValue middleRead with
    ⟨finalValue, finalRead, secondValues⟩
  exact ⟨middleValue, finalValue, middleRead, finalRead, firstValues, secondValues,
    valueImage_comp first.morphism second.morphism earlierContexts.contexts firstValues secondValues⟩

end ModelMap
end Mettapedia.TypeTheory.Calculi.NativeDependent.External
