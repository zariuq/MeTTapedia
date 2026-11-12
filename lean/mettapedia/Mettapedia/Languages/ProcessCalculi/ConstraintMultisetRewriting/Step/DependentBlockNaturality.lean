import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentBlockBraid

/-!
# Helper-block exchanges under later substitution

The reindexed triple maps to the original triple through the actual lifted
substitutions on its three blocks. Either adjacent exchange commutes with
this map. The proofs use the triple's unique factorization, retaining each
block's typed components throughout the change of base.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BlockTriple

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

variable {Head : Type} {rules : Rules Head} {Γ Δ : Context rules}

private theorem lifted_base {X : Context rules} (substitution : Δ ⟶ Γ) (helpers : Helpers Γ)
    (projection : X ⟶ (helpers.reindex substitution).frame) :
    (projection ≫ Helpers.lift substitution helpers) ≫ helpers.weaken =
      (projection ≫ (helpers.reindex substitution).weaken) ≫ substitution := by
  rw [Category.assoc, Helpers.lift_weaken, Category.assoc]

def rebase (substitution : Δ ⟶ Γ) (first second third : Helpers Γ) :
    frame (first.reindex substitution) (second.reindex substitution) (third.reindex substitution) ⟶
      frame first second third :=
  into first second third
    (toFirst (first.reindex substitution) (second.reindex substitution) (third.reindex substitution) ≫
      Helpers.lift substitution first)
    (toSecond (first.reindex substitution) (second.reindex substitution) (third.reindex substitution) ≫
      Helpers.lift substitution second)
    (toThird (first.reindex substitution) (second.reindex substitution) (third.reindex substitution) ≫
      Helpers.lift substitution third)
    (by rw [lifted_base, first_base, lifted_base, second_base])
    (by rw [lifted_base, first_base, lifted_base, third_base])

theorem rebase_first (substitution : Δ ⟶ Γ) (first second third : Helpers Γ) :
    rebase substitution first second third ≫ toFirst first second third =
      toFirst (first.reindex substitution) (second.reindex substitution) (third.reindex substitution) ≫
        Helpers.lift substitution first := into_first _ _ _ _ _ _ _ _

theorem rebase_second (substitution : Δ ⟶ Γ) (first second third : Helpers Γ) :
    rebase substitution first second third ≫ toSecond first second third =
      toSecond (first.reindex substitution) (second.reindex substitution) (third.reindex substitution) ≫
        Helpers.lift substitution second := into_second _ _ _ _ _ _ _ _

theorem rebase_third (substitution : Δ ⟶ Γ) (first second third : Helpers Γ) :
    rebase substitution first second third ≫ toThird first second third =
      toThird (first.reindex substitution) (second.reindex substitution) (third.reindex substitution) ≫
        Helpers.lift substitution third := into_third _ _ _ _ _ _ _ _

theorem rebase_base (substitution : Δ ⟶ Γ) (first second third : Helpers Γ) :
    rebase substitution first second third ≫ base first second third =
      base (first.reindex substitution) (second.reindex substitution) (third.reindex substitution) ≫
        substitution := by
  rw [← first_base first second third, ← Category.assoc, rebase_first, lifted_base, first_base]

theorem swapFirst_natural (substitution : Δ ⟶ Γ) (first second third : Helpers Γ) :
    rebase substitution first second third ≫ swapFirst first second third =
      swapFirst (first.reindex substitution) (second.reindex substitution) (third.reindex substitution) ≫
        rebase substitution second first third := by
  apply hom_ext second first third
  · simp only [Category.assoc, swapFirst_first, rebase_first, rebase_second]
    rw [← Category.assoc, swapFirst_first]
  · simp only [Category.assoc, swapFirst_second, rebase_first, rebase_second]
    rw [← Category.assoc, swapFirst_second]
  · simp only [Category.assoc, swapFirst_third, rebase_third]
    rw [← Category.assoc, swapFirst_third]

theorem swapLast_natural (substitution : Δ ⟶ Γ) (first second third : Helpers Γ) :
    rebase substitution first second third ≫ swapLast first second third =
      swapLast (first.reindex substitution) (second.reindex substitution) (third.reindex substitution) ≫
        rebase substitution first third second := by
  apply hom_ext first third second
  · simp only [Category.assoc, swapLast_first, rebase_first]
    rw [← Category.assoc, swapLast_first]
  · simp only [Category.assoc, swapLast_second, rebase_second, rebase_third]
    rw [← Category.assoc, swapLast_second]
  · simp only [Category.assoc, swapLast_third, rebase_second, rebase_third]
    rw [← Category.assoc, swapLast_third]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BlockTriple

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BlockTriple.swapFirst_natural
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BlockTriple.swapLast_natural
