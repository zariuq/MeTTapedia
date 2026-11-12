import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentBlockTriple

/-!
# Coherence of three dependent helper blocks

Adjacent exchanges are the unique maps with the specified three projections.
The two three-exchange routes therefore agree as actual contextual
substitutions. A block may contain arbitrary internal dependencies; the three
blocks themselves are declared over their common base.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BlockTriple

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

variable {Head : Type} {rules : Rules Head} {Γ : Context rules}

def swapFirst (first second third : Helpers Γ) : frame first second third ⟶ frame second first third :=
  into second first third (toSecond first second third) (toFirst first second third)
    (toThird first second third)
    ((second_base first second third).trans (first_base first second third).symm)
    ((second_base first second third).trans (third_base first second third).symm)

def swapLast (first second third : Helpers Γ) : frame first second third ⟶ frame first third second :=
  into first third second (toFirst first second third) (toThird first second third)
    (toSecond first second third)
    ((first_base first second third).trans (third_base first second third).symm)
    ((first_base first second third).trans (second_base first second third).symm)

theorem swapFirst_first (first second third : Helpers Γ) :
    swapFirst first second third ≫ toFirst second first third = toSecond first second third :=
  into_first _ _ _ _ _ _ _ _

theorem swapFirst_second (first second third : Helpers Γ) :
    swapFirst first second third ≫ toSecond second first third = toFirst first second third :=
  into_second _ _ _ _ _ _ _ _

theorem swapFirst_third (first second third : Helpers Γ) :
    swapFirst first second third ≫ toThird second first third = toThird first second third :=
  into_third _ _ _ _ _ _ _ _

theorem swapLast_first (first second third : Helpers Γ) :
    swapLast first second third ≫ toFirst first third second = toFirst first second third :=
  into_first _ _ _ _ _ _ _ _

theorem swapLast_second (first second third : Helpers Γ) :
    swapLast first second third ≫ toSecond first third second = toThird first second third :=
  into_second _ _ _ _ _ _ _ _

theorem swapLast_third (first second third : Helpers Γ) :
    swapLast first second third ≫ toThird first third second = toSecond first second third :=
  into_third _ _ _ _ _ _ _ _

theorem swapFirst_twice (first second third : Helpers Γ) :
    swapFirst first second third ≫ swapFirst second first third = 𝟙 (frame first second third) := by
  apply hom_ext first second third <;>
    simp only [Category.assoc, Category.id_comp, swapFirst_first, swapFirst_second, swapFirst_third]

theorem swapLast_twice (first second third : Helpers Γ) :
    swapLast first second third ≫ swapLast first third second = 𝟙 (frame first second third) := by
  apply hom_ext first second third <;>
    simp only [Category.assoc, Category.id_comp, swapLast_first, swapLast_second, swapLast_third]

def swapFirstIso (first second third : Helpers Γ) : frame first second third ≅ frame second first third :=
  ⟨swapFirst first second third, swapFirst second first third,
    swapFirst_twice first second third, swapFirst_twice second first third⟩

def swapLastIso (first second third : Helpers Γ) : frame first second third ≅ frame first third second :=
  ⟨swapLast first second third, swapLast first third second,
    swapLast_twice first second third, swapLast_twice first third second⟩

/-- The three adjacent exchanges in either order produce the same actual
frame morphism, including every component inside each telescope. -/
theorem braid (first second third : Helpers Γ) :
    swapFirst first second third ≫ swapLast second first third ≫ swapFirst second third first =
      swapLast first second third ≫ swapFirst first third second ≫ swapLast third first second := by
  apply hom_ext third second first <;>
    simp only [Category.assoc, swapFirst_first, swapFirst_second, swapFirst_third,
      swapLast_first, swapLast_second, swapLast_third]

theorem swapFirst_base (first second third : Helpers Γ) :
    swapFirst first second third ≫ base second first third = base first second third := by
  rw [← first_base second first third, ← Category.assoc, swapFirst_first, second_base]

theorem swapLast_base (first second third : Helpers Γ) :
    swapLast first second third ≫ base first third second = base first second third := by
  rw [← first_base first third second, ← Category.assoc, swapLast_first, first_base]

/-- Projecting away the third block recovers the existing two-block exchange. -/
theorem swapFirst_pair (first second third : Helpers Γ) :
    swapFirst first second third ≫ toPair second first third =
      toPair first second third ≫ exchange first second := by
  apply pair_hom_ext second first
  · simp only [Category.assoc, exchange_weaken]
    change swapFirst first second third ≫ toFirst second first third = toSecond first second third
    exact swapFirst_first _ _ _
  · simp only [Category.assoc, exchange_lift]
    change swapFirst first second third ≫ toSecond second first third = toFirst first second third
    exact swapFirst_second _ _ _

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BlockTriple

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BlockTriple.braid
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BlockTriple.swapFirst_pair
