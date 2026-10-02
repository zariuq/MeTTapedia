import Mettapedia.GSLT.LanguageDef.Interaction.Controls.ContactContinued

/-!
# The forgetful functor from continued theories is not full

A morphism of continued theories is injective on canonical keys.  The
morphism of iGSLTs from the law-free contact theory to itself that sends the
constant `B` to the constant `A` preserves bisimilarity and identifies two
canonical keys.  It is a morphism between the underlying iGSLTs of a
continued theory with no lift, so the forgetful functor is not full, with
morphisms taken as defined or up to their underlying theory map.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.GSLT.LanguageDef.CIGSLT

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact

/-- A closed term of the law-free contact theory as a canonical key: with no
law, every term is its own normal form. -/
def bareKey (term : barePresentation.Term) : bareContinued.CanonicalKey :=
  ⟨⟨term.1, ⟨term.2.1, term.2.2.2.1, term.2.2.2.2.1, term.2.2.2.2.2⟩,
    ReflectiveWellSorted.reflectiveScopeSafeAt_empty _ _⟩, rfl⟩

@[simp] theorem bareKey_pattern (term : barePresentation.Term) :
    (bareKey term).1.1 = term.1 :=
  rfl

/-- The two constants are distinct canonical keys. -/
theorem bareKey_constants_distinct : bareKey closedA ≠ bareKey closedB := by
  intro same
  have patterns : termA = termB := congrArg (fun key => key.1.1) same
  revert patterns
  decide

/-- **The key-collapsing morphism has no lift.**  A morphism of continued
theories over it would send two distinct canonical keys to one pattern. -/
theorem collapse_has_no_lift :
    ¬ ∃ lift : bareContinued ⟶ bareContinued, forget.map lift = collapse := by
  rintro ⟨lift, liftsCollapse⟩
  have underlying : lift.underlying = collapse := liftsCollapse
  apply bareKey_constants_distinct
  apply lift.quoteFaithful
  show mapPattern lift.underlying.structural.structural.symbols termA =
    mapPattern lift.underlying.structural.structural.symbols termB
  rw [underlying]
  show mapPattern collapseSymbols termA = mapPattern collapseSymbols termB
  decide +kernel

/-- **Not full.**  The forgetful functor from continued theories is not full. -/
theorem forget_not_full : ¬ forget.Full := by
  intro full
  exact collapse_has_no_lift (full.map_surjective (X := bareContinued) (Y := bareContinued)
    collapse)

/-- Nor is it full when morphisms are taken up to their underlying theory
map. -/
theorem forgetUpToTheoryMap_not_full : ¬ forgetUpToTheoryMap.Full := by
  intro full
  obtain ⟨preimage, image⟩ := full.map_surjective
    (X := (CategoryTheory.Quotient.functor forget.homRel).obj bareContinued)
    (Y := (CategoryTheory.Quotient.functor forget.homRel).obj bareContinued) collapse
  obtain ⟨lift, rfl⟩ := (CategoryTheory.Quotient.functor forget.homRel).map_surjective preimage
  exact collapse_has_no_lift ⟨lift, image⟩

end Mettapedia.GSLT.LanguageDef.CIGSLT
