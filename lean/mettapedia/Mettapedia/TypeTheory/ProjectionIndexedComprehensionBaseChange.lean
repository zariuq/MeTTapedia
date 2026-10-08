import Mettapedia.TypeTheory.FibrationComprehensionProfile
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Canonical comparison of chosen fibre substitutions

The comparison is earned from the unique factorization of the supplied
strongly Cartesian lifts. Its components retain the full total arrow.
It supplies the commuting square whose adjunction mates express
Beck--Chevalley for projection-indexed quantification.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.ProjectionIndexedComprehension

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Functor
open HasFibers
open Mettapedia.CategoryTheory.FibrationTwoCategory
open FibrationComprehensionProfile

universe u v f h

namespace Substitution

variable {projection : Fibration.{u,v}}
  [HasFibers.{h,f} projection.functor]
  (chosen : FibrationComprehensionProfile.Substitution projection)
  {first middle last : projection.Base}
  (earlier : first ⟶ middle) (later : middle ⟶ last)

def composedLift (object : Fib projection.functor last) :
    (ι first).obj ((chosen.reindex later ⋙ chosen.reindex earlier).obj object) ⟶
      (ι last).obj object :=
  (chosen.lift earlier).app ((chosen.reindex later).obj object) ≫
    (chosen.lift later).app object

instance composedLift_cartesian (object : Fib projection.functor last) :
    projection.functor.IsStronglyCartesian (earlier ≫ later)
      (composedLift chosen earlier later object) := by
  let := chosen.cartesian earlier ((chosen.reindex later).obj object)
  let := chosen.cartesian later object
  exact inferInstanceAs (projection.functor.IsStronglyCartesian (earlier ≫ later)
    ((chosen.lift earlier).app ((chosen.reindex later).obj object) ≫
      (chosen.lift later).app object))

def compositionComponent (object : Fib projection.functor last) :
    (chosen.reindex later ⋙ chosen.reindex earlier).obj object ≅
      (chosen.reindex (earlier ≫ later)).obj object := by
  let := chosen.cartesian (earlier ≫ later) object
  exact Fib.isoMk
    (IsCartesian.domainUniqueUpToIso projection.functor (earlier ≫ later)
      ((chosen.lift (earlier ≫ later)).app object)
      (composedLift chosen earlier later object)) inferInstance

theorem compositionComponent_lift (object : Fib projection.functor last) :
    (ι first).map (compositionComponent chosen earlier later object).hom ≫
      (chosen.lift (earlier ≫ later)).app object =
        composedLift chosen earlier later object := by
  let := chosen.cartesian (earlier ≫ later) object
  change (ι first).map (Fib.homMk _) ≫ _ = _
  rw [Fib.map_homMk]
  exact IsCartesian.fac projection.functor (earlier ≫ later) _ _

def composition : chosen.reindex later ⋙ chosen.reindex earlier ≅
    chosen.reindex (earlier ≫ later) := by
  refine NatIso.ofComponents (compositionComponent chosen earlier later) ?_
  intro source target arrow
  apply Fib.hom_ext
  let := chosen.cartesian (earlier ≫ later) target
  apply IsCartesian.ext projection.functor (earlier ≫ later)
    ((chosen.lift (earlier ≫ later)).app target)
  simp only [Functor.map_comp, Category.assoc, compositionComponent_lift]
  have whole := (chosen.lift (earlier ≫ later)).naturality arrow
  change (ι first).map ((chosen.reindex (earlier ≫ later)).map arrow) ≫
    (chosen.lift (earlier ≫ later)).app target =
      (chosen.lift (earlier ≫ later)).app source ≫ (ι last).map arrow at whole
  rw [whole]
  rw [← Category.assoc, compositionComponent_lift]
  change
    (ι first).map ((chosen.reindex earlier).map ((chosen.reindex later).map arrow)) ≫
        ((chosen.lift earlier).app ((chosen.reindex later).obj target) ≫
          (chosen.lift later).app target) =
      ((chosen.lift earlier).app ((chosen.reindex later).obj source) ≫
        (chosen.lift later).app source) ≫ (ι last).map arrow
  have earlierNatural := (chosen.lift earlier).naturality ((chosen.reindex later).map arrow)
  change (ι first).map ((chosen.reindex earlier).map ((chosen.reindex later).map arrow)) ≫
      (chosen.lift earlier).app ((chosen.reindex later).obj target) =
    (chosen.lift earlier).app ((chosen.reindex later).obj source) ≫
      (ι middle).map ((chosen.reindex later).map arrow) at earlierNatural
  have laterNatural := (chosen.lift later).naturality arrow
  change (ι middle).map ((chosen.reindex later).map arrow) ≫ (chosen.lift later).app target =
    (chosen.lift later).app source ≫ (ι last).map arrow at laterNatural
  rw [← Category.assoc, earlierNatural, Category.assoc, laterNatural, ← Category.assoc]

theorem composition_lift (object : Fib projection.functor last) :
    (ι first).map ((composition chosen earlier later).hom.app object) ≫
      (chosen.lift (earlier ≫ later)).app object =
        composedLift chosen earlier later object :=
  compositionComponent_lift chosen earlier later object

theorem composition_inv_lift (object : Fib projection.functor last) :
    (ι first).map ((composition chosen earlier later).inv.app object) ≫
        composedLift chosen earlier later object =
      (chosen.lift (earlier ≫ later)).app object := by
  rw [← composition_lift chosen earlier later object, ← Category.assoc,
    ← Functor.map_comp]
  simp only [Iso.inv_hom_id_app]
  rw [(ι first).map_id, Category.id_comp]

theorem transport_lift {source target : projection.Base}
    {firstRoute secondRoute : source ⟶ target} (same : firstRoute = secondRoute)
    (object : Fib projection.functor target) :
    (ι source).map
        ((eqToIso (congrArg (fun route => chosen.reindex route) same)).hom.app object) ≫
      (chosen.lift secondRoute).app object = (chosen.lift firstRoute).app object := by
  cases same
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  rw [(ι source).map_id, Category.id_comp]

variable {first second third fourth : projection.Base}
  {top : first ⟶ second} {left : first ⟶ third}
  {right : second ⟶ fourth} {bottom : third ⟶ fourth}

def square (commutes : top ≫ right = left ≫ bottom) :
    chosen.reindex right ⋙ chosen.reindex top ≅
      chosen.reindex bottom ⋙ chosen.reindex left :=
  composition chosen top right ≪≫
    eqToIso (congrArg (fun route => chosen.reindex route) commutes) ≪≫
      (composition chosen left bottom).symm

theorem square_lift (commutes : top ≫ right = left ≫ bottom)
    (object : Fib projection.functor fourth) :
    (ι first).map ((square chosen commutes).hom.app object) ≫
        composedLift chosen left bottom object =
      composedLift chosen top right object := by
  simp only [square, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.map_comp, Category.assoc, composition_inv_lift]
  rw [transport_lift chosen commutes object, composition_lift]

theorem square_flip (commutes : top ≫ right = left ≫ bottom) :
    square chosen commutes.symm = (square chosen commutes).symm := by
  apply Iso.ext
  simp only [square, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]
  rfl

end Substitution

end Mettapedia.TypeTheory.ProjectionIndexedComprehension
