import Mathlib.CategoryTheory.Quotient
import Mettapedia.GSLT.LanguageDef.ContinuedCategory
import Mettapedia.GSLT.LanguageDef.LambdaContinuedInteraction

/-!
# The forgetful functor from continued theories, and what it forgets of a map

A morphism of continued theories is a morphism of their underlying iGSLTs
together with a renaming of reflection names.  The forgetful functor keeps
the first and drops the second, so it is not faithful: on a theory that
authors no reflection, every renaming of reflection names gives a morphism
over the same theory map.

What it drops acts on nothing.  Two morphisms over the same theory map act
identically on terms and on canonical keys.  Identifying them gives a
category of continued theories on which the forgetful functor is faithful,
and that is the functor whose fullness and essential image the rest of this
directory studies.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.GSLT.LanguageDef.CIGSLT

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.GSLT.LanguageDef.LambdaContinuedInteraction

namespace Morphism

/-- Replace the reflection renaming of a morphism whose source authors no
reflection.  Every law that mentions the renaming is about a declaration of
the source profile, and there is none. -/
def withReflectionSymbols {source target : CIGSLT} (morphism : Morphism source target)
    (noPresentations : source.reflection.1.presentations = [])
    (noRules : source.reflection.1.rules = [])
    (symbols : ReflectionSymbols) : Morphism source target :=
  { morphism with
    reflectionSymbols := symbols
    mapsReflectivePresentations := by
      intro declaration membership
      rw [noPresentations] at membership
      cases membership
    mapsReflectiveRules := by
      intro declaration membership
      rw [noRules] at membership
      cases membership }

@[simp] theorem withReflectionSymbols_underlying {source target : CIGSLT}
    (morphism : Morphism source target)
    (noPresentations : source.reflection.1.presentations = [])
    (noRules : source.reflection.1.rules = [])
    (symbols : ReflectionSymbols) :
    (morphism.withReflectionSymbols noPresentations noRules symbols).underlying =
      morphism.underlying :=
  rfl

/-- **The dropped datum acts on nothing.**  Two morphisms over the same
theory map send every canonical key to the same canonical key. -/
theorem canonicalKeyMap_eq_of_underlying_eq {source target : CIGSLT}
    {first second : Morphism source target}
    (sameUnderlying : first.underlying = second.underlying)
    (key : source.CanonicalKey) :
    first.canonicalKeyMap key = second.canonicalKeyMap key := by
  apply Subtype.ext
  apply Subtype.ext
  rw [canonicalKeyMap_pattern, canonicalKeyMap_pattern, sameUnderlying]

end Morphism

/-! ## The functor as defined is not faithful -/

/-- A renaming of reflection names other than the identity. -/
def constantReflectionSymbols : ReflectionSymbols where
  presentation := fun _ => "renamed"
  rule := fun _ => "renamed"

/-- The identity of the lambda calculus with its reflection renaming
replaced. -/
def lambdaRenamedIdentity : lambdaCIGSLT ⟶ lambdaCIGSLT :=
  (Morphism.id lambdaCIGSLT).withReflectionSymbols rfl rfl constantReflectionSymbols

/-- It lies over the identity theory map and is not the identity. -/
theorem lambdaRenamedIdentity_over_identity :
    forget.map lambdaRenamedIdentity = forget.map (𝟙 lambdaCIGSLT) ∧
      lambdaRenamedIdentity ≠ 𝟙 lambdaCIGSLT := by
  refine ⟨rfl, ?_⟩
  intro same
  have names := congrArg
    (fun morphism : Morphism lambdaCIGSLT lambdaCIGSLT =>
      morphism.reflectionSymbols.presentation "name") same
  revert names
  show ("renamed" : String) = "name" → False
  decide

/-- **The forgetful functor, as defined, is not faithful.** -/
theorem forget_not_faithful : ¬ forget.Faithful := by
  intro faithful
  exact lambdaRenamedIdentity_over_identity.2
    (faithful.map_injective lambdaRenamedIdentity_over_identity.1)

/-! ## Continued theories up to the underlying theory map -/

/-- Continued theories, with two morphisms identified when they lie over the
same morphism of iGSLTs. -/
abbrev UpToTheoryMap : Type _ := CategoryTheory.Quotient (forget.homRel)

/-- The forgetful functor on that category. -/
def forgetUpToTheoryMap : UpToTheoryMap ⥤ IGSLT :=
  CategoryTheory.Quotient.lift forget.homRel forget (fun _ _ _ _ related => related)

/-- On objects it is the underlying iGSLT. -/
@[simp] theorem forgetUpToTheoryMap_obj (theory : CIGSLT) :
    forgetUpToTheoryMap.obj ((CategoryTheory.Quotient.functor forget.homRel).obj theory) = theory.theory :=
  rfl

/-- On the class of a morphism it is the underlying theory map. -/
@[simp] theorem forgetUpToTheoryMap_map {source target : CIGSLT}
    (morphism : source ⟶ target) :
    forgetUpToTheoryMap.map ((CategoryTheory.Quotient.functor forget.homRel).map morphism) =
      forget.map morphism :=
  rfl

/-- **Faithful.**  A morphism of continued theories, taken up to what acts on
nothing, is determined by its underlying theory map. -/
instance forgetUpToTheoryMap_faithful : forgetUpToTheoryMap.Faithful where
  map_injective := by
    intro source target first second same
    obtain ⟨firstRepresentative, rfl⟩ :=
      (CategoryTheory.Quotient.functor forget.homRel).map_surjective first
    obtain ⟨secondRepresentative, rfl⟩ :=
      (CategoryTheory.Quotient.functor forget.homRel).map_surjective second
    exact (CategoryTheory.Quotient.functor_map_eq_iff forget.homRel _ _).mpr same

end Mettapedia.GSLT.LanguageDef.CIGSLT
