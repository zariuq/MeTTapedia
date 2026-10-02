import Mettapedia.GSLT.LanguageDef.Contexts.Invertible
import Mettapedia.GSLT.LanguageDef.Contexts.Controls.OverObservation

/-!
# A hosting and exhausting morphism that is not the identity

The law-free contact theory has two constants that no rule mentions.
Exchanging them is a map of declarations from the theory to itself, and it is
its own inverse.  It is therefore a morphism that is hosting and exhausting,
and it is not the identity: it sends each constant to the other.

Collapsing the two constants to one, by contrast, is a morphism that is
neither hosting nor exhausting, and the inclusion into the theory with an
observing constructor is hosting and not exhausting.  The exchange is the
positive example beside those two.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Contexts.Controls

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Contexts
open Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-- Exchange the constants `A` and `B`. -/
def swapSymbols : LanguageDefSymbolMap where
  sort := id
  constructor := fun label => if label = "A" then "B" else if label = "B" then "A" else label
  relation := id
  equation := id
  rewrite := id

/-- Exchanging twice changes nothing. -/
theorem swap_involutive : swapSymbols.comp swapSymbols = LanguageDefSymbolMap.id := by
  have constructors : swapSymbols.constructor ∘ swapSymbols.constructor = id := by
    funext label
    simp only [swapSymbols, Function.comp_apply, id_eq]
    by_cases isA : label = "A"
    · subst isA
      simp
    · by_cases isB : label = "B"
      · subst isB
        simp
      · simp [isA, isB]
  simp only [LanguageDefSymbolMap.comp, LanguageDefSymbolMap.id]
  rw [constructors]
  rfl

theorem swap_syncRule : mapRewriteRule swapSymbols syncRule = syncRule := by
  simp [mapRewriteRule, syncRule, join, mapPattern, mapPatternList, swapSymbols,
    mapTypeContext, mapTypeExpr]

/-- The exchange as a map of declarations of the contact theory to itself. -/
def swapStructural : StructuralMorphism bareValidated bareValidated where
  symbols := swapSymbols
  mapsTypes := by
    intro declaration membership
    obtain rfl : declaration = TypeDecl.plain "Proc" := List.mem_singleton.mp membership
    exact List.Mem.head _
  mapsTerms := by
    intro rule membership
    change rule ∈ terms at membership
    simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at membership
    change mapGrammarRule swapSymbols rule ∈ terms
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  mapsEquations := by
    intro equation membership
    cases membership
  mapsRewrites := by
    intro rewrite membership
    obtain rfl : rewrite = syncRule := List.mem_singleton.mp membership
    change mapRewriteRule swapSymbols syncRule ∈ [syncRule]
    rw [swap_syncRule]
    exact List.mem_singleton.mpr rfl

/-- The exchange is its own inverse. -/
theorem swap_inverse : Inverse swapStructural swapStructural :=
  ⟨swap_involutive, swap_involutive⟩

/-- The contact theory declares no collection algebra, so the exchange has no
declared unit to fix. -/
theorem swap_fixesUnits :
    EquationSimulation.FixesDeclaredUnits swapStructural.symbols bareValidated.language :=
  EquationSimulation.fixesDeclaredUnits_of_no_algebra _ (by decide)

theorem swap_preservesEquations : PreservesEquations base swapStructural :=
  preservesEquations_default swapStructural rfl swap_fixesUnits

theorem swap_preservesSteps : PreservesSteps base swapStructural :=
  preservesSteps_default swapStructural rfl swap_fixesUnits

/-- **The exchange is a morphism of theories.** -/
def swapMorphism :
    ContextMorphism (contextTheory base bareValidated) (contextTheory base bareValidated) :=
  swap_inverse.morphism base swap_preservesEquations swap_preservesSteps swap_preservesSteps

/-- **The exchange is hosting and exhausting.** -/
theorem swap_hosting_exhausting :
    swapMorphism.toContextMap.Hosting ∧ swapMorphism.toContextMap.Exhausting :=
  ⟨swap_inverse.hosting base swap_preservesEquations swap_preservesEquations
      swap_preservesSteps swap_preservesSteps,
    swap_inverse.exhausting base swap_preservesEquations⟩

/-- The exchange is not the identity: it sends the first constant to the
second. -/
theorem swap_constantA : (swapMorphism.term constantA).1 = constantB.1 := by
  decide +kernel

theorem swap_moves_a_term : (swapMorphism.term constantA).1 ≠ constantA.1 := by
  decide +kernel

/-- **Over the exchange nothing is added and nothing is lost**: two terms are
bisimilar over all contexts exactly when their images are bisimilar over all
contexts between the images of their interface. -/
theorem swap_bisimilar_iff {origin : Interface} {left right : Term bareValidated.language origin} :
    swapMorphism.targetProbe.Bisimilar (index := origin) (swapMorphism.term left)
        (swapMorphism.term right) ↔
      (contextTheory base bareValidated).fullProbe.Bisimilar (index := origin) left right :=
  swap_inverse.bisimilar_targetProbe_iff base swap_preservesEquations swap_preservesSteps
    swap_preservesSteps

end Mettapedia.GSLT.LanguageDef.Contexts.Controls
