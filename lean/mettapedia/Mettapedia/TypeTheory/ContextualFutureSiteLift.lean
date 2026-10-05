import Mettapedia.TypeTheory.PresheafSiteLift
import Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers
import Mettapedia.TypeTheory.WiderPresheafDependentFunctions

/-!
# Complete future cones on an explicitly raised equivalent site

The parameter carrier is retained, including arbitrarily wider original
values. Worlds and arrows are raised independently. Each future world and
actual arrival arrow has a constructed inverse lowering; no endpoint,
parallel history or typed parameter coordinate is discarded.

Displayed values are raised by ULift. The full comprehension and displayed
comprehension have explicit inverse context maps, and whole compatible
sections have both inverse laws. This translates authored lower families;
it does not assert that every upper family is a lower image.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualFutureSiteLift

open CategoryTheory
open ContextualWitnessCover
open MaterialSets.Hypersets PowerClassPresheafBaseChange

universe u v w z
variable {D : Type u} [Category.{u} D]

abbrev Raised := PresheafSiteLift.Site D

def base (P : D ⥤ Type v) : Raised (D := D) ⥤ Type v :=
  PresheafSiteLift.compose PresheafSiteLift.Site.downFunctor P

def elementsDown (P : D ⥤ Type v) : (base P).Elements ⥤ P.Elements where
  obj point := ⟨point.1.down, point.2⟩
  map step := ⟨step.1.down, step.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def elementsUp (P : D ⥤ Type v) : P.Elements ⥤ (base P).Elements where
  obj point := ⟨PresheafSiteLift.Site.upFunctor.obj point.1, point.2⟩
  map step := ⟨PresheafSiteLift.Site.upFunctor.map step.1, step.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem elements_up_down (P : D ⥤ Type v) :
    PresheafSiteLift.compose (elementsUp P) (elementsDown P) = PresheafSiteLift.identity P.Elements := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem elements_down_up (P : D ⥤ Type v) :
    PresheafSiteLift.compose (elementsDown P) (elementsUp P) = PresheafSiteLift.identity (base P).Elements := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

def family (P : D ⥤ Type v) (A : P.Elements ⥤ Type w) : (base P).Elements ⥤ Type (max (u+1) w) where
  obj point := ULift.{u+1,w} (A.obj ((elementsDown P).obj point))
  map step := TypeCat.ofHom fun code => ULift.up (A.map ((elementsDown P).map step) code.down)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro code
    exact ULift.ext _ _ (A.map_id_apply ((elementsDown P).obj point) code.down)
  map_comp first later := by
    apply ConcreteCategory.hom_ext
    intro code
    exact ULift.ext _ _ (A.map_comp_apply ((elementsDown P).map first) ((elementsDown P).map later) code.down)

def displayedDown (P : D ⥤ Type v) (A : P.Elements ⥤ Type w) : (family P A).Elements ⥤ A.Elements where
  obj point := ⟨(elementsDown P).obj point.1, point.2.down⟩
  map step := ⟨(elementsDown P).map step.1, congrArg ULift.down step.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def displayedUp (P : D ⥤ Type v) (A : P.Elements ⥤ Type w) : A.Elements ⥤ (family P A).Elements where
  obj point := ⟨(elementsUp P).obj point.1, ULift.up point.2⟩
  map step := ⟨(elementsUp P).map step.1, congrArg ULift.up step.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem displayed_up_down (P : D ⥤ Type v) (A : P.Elements ⥤ Type w) :
    PresheafSiteLift.compose (displayedUp P A) (displayedDown P A) = PresheafSiteLift.identity A.Elements := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem displayed_down_up (P : D ⥤ Type v) (A : P.Elements ⥤ Type w) :
    PresheafSiteLift.compose (displayedDown P A) (displayedUp P A) =
      PresheafSiteLift.identity (family P A).Elements := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

def body (P : D ⥤ Type v) (A : P.Elements ⥤ Type w) (B : A.Elements ⥤ Type z) :
    (family P A).Elements ⥤ Type (max (u+1) z) where
  obj point := ULift.{u+1,z} (B.obj ((displayedDown P A).obj point))
  map step := TypeCat.ofHom fun code => ULift.up (B.map ((displayedDown P A).map step) code.down)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro code
    exact ULift.ext _ _ (B.map_id_apply ((displayedDown P A).obj point) code.down)
  map_comp first later := by
    apply ConcreteCategory.hom_ext
    intro code
    exact ULift.ext _ _ (B.map_comp_apply ((displayedDown P A).map first) ((displayedDown P A).map later) code.down)

def raiseSection (P : D ⥤ Type v) (A : P.Elements ⥤ Type w) (term : A.sections) : (family P A).sections :=
  ⟨fun point => ULift.up (term.val ((elementsDown P).obj point)), by
    intro _ _ step
    exact congrArg ULift.up (term.property ((elementsDown P).map step))⟩

def lowerSection (P : D ⥤ Type v) (A : P.Elements ⥤ Type w) (term : (family P A).sections) : A.sections :=
  ⟨fun point => (term.val ((elementsUp P).obj point)).down, by
    intro _ _ step
    exact congrArg ULift.down (term.property ((elementsUp P).map step))⟩

def sections (P : D ⥤ Type v) (A : P.Elements ⥤ Type w) : A.sections ≃ (family P A).sections where
  toFun := raiseSection P A
  invFun := lowerSection P A
  left_inv term := by
    apply Subtype.ext
    funext point
    rfl
  right_inv term := by
    apply Subtype.ext
    funext point
    rfl

def futureDown (point : Raised (D := D)) : Future.Objects point ⥤ Future.Objects point.down where
  obj future := ⟨future.1.down, future.2.down⟩
  map move := ⟨move.1.down, congrArg ULift.down move.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def futureUp (point : Raised (D := D)) : Future.Objects point.down ⥤ Future.Objects point where
  obj future := ⟨PresheafSiteLift.Site.upFunctor.obj future.1, ULift.up future.2⟩
  map move := ⟨ULift.up move.1, congrArg ULift.up move.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem future_up_down (point : Raised (D := D)) :
    PresheafSiteLift.compose (futureUp point) (futureDown point) = PresheafSiteLift.identity (Future.Objects point.down) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem future_down_up (point : Raised (D := D)) :
    PresheafSiteLift.compose (futureDown point) (futureUp point) = PresheafSiteLift.identity (Future.Objects point) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem future_down_prefix {first second : Raised (D := D)} (step : first ⟶ second) :
    PresheafSiteLift.compose (ContextualSmallFamilyUniverse.futurePrefix step) (futureDown first) =
      PresheafSiteLift.compose (futureDown second) (ContextualSmallFamilyUniverse.futurePrefix step.down) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem future_up_prefix {first second : Raised (D := D)} (step : first ⟶ second) :
    PresheafSiteLift.compose (ContextualSmallFamilyUniverse.futurePrefix step.down) (futureUp first) =
      PresheafSiteLift.compose (futureUp second) (ContextualSmallFamilyUniverse.futurePrefix step) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

def retained (P : D ⥤ Type v) (A : P.Elements ⥤ Type w) : (base P).Elements ⥤ Type w :=
  PresheafSiteLift.compose (elementsDown P) A

def readSection (P : D ⥤ Type v) (A : P.Elements ⥤ Type w) (term : A.sections) : (retained P A).sections :=
  ⟨fun point => term.val ((elementsDown P).obj point), fun step => term.property ((elementsDown P).map step)⟩

def retainedSections (P : D ⥤ Type v) (A : P.Elements ⥤ Type w) : A.sections ≃ (retained P A).sections where
  toFun := readSection P A
  invFun term := ⟨fun point => term.val ((elementsUp P).obj point),
    fun step => term.property ((elementsUp P).map step)⟩
  left_inv term := by
    apply Subtype.ext
    funext point
    rfl
  right_inv term := by
    apply Subtype.ext
    funext point
    rfl

def retainedHom (P : D ⥤ Type v) {first : P.Elements ⥤ Type w} {second : P.Elements ⥤ Type z}
    (operation : WiderPresheafDependentFunctions.Hom first second) :
    WiderPresheafDependentFunctions.Hom (retained P first) (retained P second) where
  app point := operation.app ((elementsDown P).obj point)
  naturality step value := operation.naturality ((elementsDown P).map step) value

end Mettapedia.TypeTheory.ContextualFutureSiteLift
