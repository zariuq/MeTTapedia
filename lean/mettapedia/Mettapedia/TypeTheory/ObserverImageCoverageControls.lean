import Mettapedia.TypeTheory.DependentProductRestrictionControls
import Mettapedia.CategoryTheory.FunctorOriginImage

/-!
# Object coverage is weaker than dependent future coverage

The discrete presentation reaches every world of a directed category but
omits its outgoing nonidentity arrows. Distinct future-dependent functions
then have identical restrictions. An image retaining arrow origins has
the stronger categorical equivalence, even when the target forgets them.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ObserverImageCoverageControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent
open DependentProductRestriction DependentProductRestrictionCoverage
open DependentProductRestrictionControls

abbrev PresentedWorlds := Discrete WalkingParallelPair

def allWorlds : PresentedWorlds ⥤ Large := Discrete.functor (fun world => world)

theorem every_world_covered (world : Large) : ∃ presented, allWorlds.obj presented = world :=
  ⟨Discrete.mk world, rfl⟩

theorem restriction_loses_future :
    restrictSection allWorlds argumentFamily evidenceFamily
        (X := Discrete.mk .zero) (constantFunction false) =
      restrictSection allWorlds argumentFamily evidenceFamily
        (X := Discrete.mk .zero) (constantFunction true) := by
  apply DependentSection.ext
  intro future arrow argument
  rcases future with ⟨future⟩
  have same : WalkingParallelPair.zero = future := Discrete.eq_of_hom arrow
  subst future
  exact PEmpty.elim argument

theorem comparison_not_injective_despite_world_coverage :
    ¬ Function.Injective
      (restrictSection allWorlds argumentFamily evidenceFamily (X := Discrete.mk .zero)) := by
  intro injective
  exact functions_distinct (injective restriction_loses_future)

theorem future_coverage_fails :
    ¬ (futureLift allWorlds argumentFamily (Discrete.mk .zero)).Initial := by
  intro initial
  have := initial
  exact comparison_not_injective_despite_world_coverage
    (comparison_bijective allWorlds argumentFamily evidenceFamily (Discrete.mk .zero)).1

def eraseArrows : Large ⥤ Discrete Unit := (Functor.const Large).obj (Discrete.mk ())

def firstOrigin :
    Mettapedia.CategoryTheory.FunctorOriginImage.Arrow eraseArrows ⟨.zero⟩ ⟨.one⟩ :=
  ⟨eraseArrows.map WalkingParallelPairHom.left, WalkingParallelPairHom.left, rfl⟩

def secondOrigin :
    Mettapedia.CategoryTheory.FunctorOriginImage.Arrow eraseArrows ⟨.zero⟩ ⟨.one⟩ :=
  ⟨eraseArrows.map WalkingParallelPairHom.right, WalkingParallelPairHom.right, rfl⟩

theorem target_erases_distinction : firstOrigin.target = secondOrigin.target := rfl

theorem retained_origins_distinct : firstOrigin ≠ secondOrigin := by
  intro same
  have routes := congrArg
    (fun arrow : Mettapedia.CategoryTheory.FunctorOriginImage.Arrow eraseArrows ⟨.zero⟩ ⟨.one⟩ =>
      arrow.source) same
  cases routes

/-- Retaining the actual routes earns an equivalence and hence future
coverage. Erasing them merely produces the underlying target functor. -/
def retainedImageEquivalence : Large ≌
    Mettapedia.CategoryTheory.FunctorOriginImage.Object eraseArrows :=
  Mettapedia.CategoryTheory.FunctorOriginImage.equivalence eraseArrows

end Mettapedia.TypeTheory.ObserverImageCoverageControls
