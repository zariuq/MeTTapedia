import Mettapedia.TypeTheory.DependentProductRestrictionCoverage
import Mettapedia.TypeTheory.DependentProductNativeComparison
import Mettapedia.GSLT.Topos.ClassifierRestriction
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.Logic.Equiv.Bool

/-!
# Evidence-sensitive controls for change of theory

The inclusion of the initial world omits later arguments. Two different
dependent functions then restrict to the same function. Classifier values
also collapse. Equivalences of theories give the positive product and
classifier comparisons through the independently constructed canonical maps.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DependentProductRestrictionControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent
open DependentProductRestriction DependentProductRestrictionCoverage

abbrev Small := Discrete Unit
abbrev Large := WalkingParallelPair

def initialWorld : Small ⥤ Large := (Functor.const Small).obj .zero

def argumentFamily : Large ⥤ Type :=
  parallelPair (TypeCat.ofHom (PEmpty.elim : PEmpty → PUnit))
    (TypeCat.ofHom (PEmpty.elim : PEmpty → PUnit))

def evidenceFamily : argumentFamily.Elements ⥤ Type :=
  (Functor.const _).obj Bool

def constantFunction (value : Bool) : DependentSection argumentFamily evidenceFamily .zero where
  app _ _ _ := value
  naturality _ _ _ := rfl

theorem functions_distinct : constantFunction false ≠ constantFunction true := by
  intro same
  have answer := congrArg (fun f => f.app .one WalkingParallelPairHom.left PUnit.unit) same
  exact Bool.false_ne_true answer

theorem restricted_functions_equal :
    restrictSection initialWorld argumentFamily evidenceFamily
        (X := Discrete.mk ()) (constantFunction false) =
      restrictSection initialWorld argumentFamily evidenceFamily
        (X := Discrete.mk ()) (constantFunction true) := by
  apply DependentSection.ext
  intro Y arrow argument
  exact PEmpty.elim argument

theorem comparison_not_injective :
    ¬ Function.Injective
      (restrictSection initialWorld argumentFamily evidenceFamily (X := Discrete.mk ())) := by
  intro injective
  exact functions_distinct (injective restricted_functions_equal)

/-- Both branches are genuine application results in a reached world. -/
theorem application_reaches_distinction :
    (constantFunction false).app .one WalkingParallelPairHom.left PUnit.unit = false ∧
      (constantFunction true).app .one WalkingParallelPairHom.left PUnit.unit = true := ⟨rfl, rfl⟩

def properFuture : Sieve (WalkingParallelPair.one) where
  arrows {X} _ := X = WalkingParallelPair.zero
  downward_closed := by
    intro Y Z f same g
    subst Y
    cases g
    rfl

def terminalWorld : Small ⥤ Large := (Functor.const Small).obj .one

theorem properFuture_ne_empty : properFuture ≠ ⊥ := by
  intro same
  have member : properFuture WalkingParallelPairHom.left := rfl
  rw [same] at member
  exact member

theorem classifier_loses_future :
    properFuture.functorPullback terminalWorld = (⊥ : Sieve (Discrete.mk ())) := by
  apply Sieve.ext
  intro Y arrow
  change WalkingParallelPair.one = WalkingParallelPair.zero ↔ False
  constructor
  · exact WalkingParallelPair.noConfusion
  · exact False.elim

/-- Equivalence is sufficient for all argument families, not just the
constant example in this module. -/
noncomputable def productsAlongEquivalence {C D : Type} [Category C] [Category D]
    (F : C ≌ D) (A : D ⥤ Type) (B : A.Elements ⥤ Type) :
    F.functor ⋙ dependentFunctions A B ≅
      dependentFunctions (F.functor ⋙ A) (restrictedFamily F.functor A B) :=
  comparisonIso F.functor A B

noncomputable def classifierAlongEquivalence {C D : Type} [Category C] [Category D]
    (F : C ≌ D) :
    F.functor.op ⋙ Mettapedia.GSLT.Topos.omegaFunctor (C := D) ≅
      Mettapedia.GSLT.Topos.omegaFunctor (C := C) :=
  Mettapedia.GSLT.Topos.ClassifierRestriction.comparisonIso F.functor

/-- This theory equivalence actually changes which world is observed. -/
def swappingWorlds : Discrete Bool ≌ Discrete Bool := Discrete.equivalence Equiv.boolNot

theorem swaps_the_world :
    swappingWorlds.functor.obj (Discrete.mk false) = Discrete.mk true := rfl

/-- A nonidentity theory translation preserves the chosen native product
for every dependent codomain, rather than merely a constant truth value. -/
noncomputable def nativeProductsAlongSwapping
    (A : Discrete Bool ⥤ Type) (B : A.Elements ⥤ Type) :
    swappingWorlds.functor ⋙ CategoryIndexedFamilyGeneralPi.generalPiFamily
        (context := Cat.of (Discrete Bool)) A B ≅
      CategoryIndexedFamilyGeneralPi.generalPiFamily (context := Cat.of (Discrete Bool))
        (swappingWorlds.functor ⋙ A) (restrictedFamily swappingWorlds.functor A B) :=
  DependentProductNativeComparison.nativeRestrictionIso swappingWorlds.functor A B

end Mettapedia.TypeTheory.DependentProductRestrictionControls
