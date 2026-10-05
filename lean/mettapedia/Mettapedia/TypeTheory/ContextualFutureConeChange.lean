import Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormerCoherence

/-!
# Constructed local future inverses for context-prefix functors

Prefixing complete histories need not be globally injective. At any
retained future point, however, a further future stores the actual arrow
from that point. Its lower target and history are constructed by extending
the retained lower history with that arrow. The actual triangle supplies
the inverse image equation, including parallel arrows.

Both local future functors and their full inverse laws are constructed
below. These are contextual transport data; a W-family operation is not
assumed by the construction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualFutureConeChange

open CategoryTheory
open MaterialSets.Hypersets.PowerClassPresheafBaseChange

universe u
variable {D : Type u} [Category.{u} D] {first second : D} (step : first ⟶ second)

def forward (point : Future.Objects second) :
    Future.Objects point ⥤ Future.Objects ((ContextualSmallFamilyUniverse.futurePrefix step).obj point) :=
  Future.map (ContextualSmallFamilyUniverse.futurePrefix step) point

def recoveredTarget (point : Future.Objects second)
    (future : Future.Objects ((ContextualSmallFamilyUniverse.futurePrefix step).obj point)) : Future.Objects second :=
  ⟨future.1.1, point.2 ≫ future.2.1⟩

def backward (point : Future.Objects second) :
    Future.Objects ((ContextualSmallFamilyUniverse.futurePrefix step).obj point) ⥤ Future.Objects point where
  obj future := ⟨recoveredTarget step point future, ⟨future.2.1, rfl⟩⟩
  map {source target} arrow := ⟨⟨arrow.1.1, by
    change (point.2 ≫ source.2.1) ≫ arrow.1.1 = point.2 ≫ target.2.1
    exact (Category.assoc point.2 source.2.1 arrow.1.1).trans
      (congrArg (fun tail => point.2 ≫ tail) (congrArg Subtype.val arrow.2))⟩, by
      apply Subtype.ext
      change source.2.1 ≫ arrow.1.1 = target.2.1
      exact congrArg Subtype.val arrow.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem backward_target (point : Future.Objects second)
    (future : Future.Objects ((ContextualSmallFamilyUniverse.futurePrefix step).obj point)) :
    ((backward step point).obj future).1.1 = future.1.1 := rfl

theorem backward_arrow (point : Future.Objects second)
    (future : Future.Objects ((ContextualSmallFamilyUniverse.futurePrefix step).obj point)) :
    ((backward step point).obj future).2.1 = future.2.1 := rfl

theorem forward_backward_target (point : Future.Objects second)
    (future : Future.Objects ((ContextualSmallFamilyUniverse.futurePrefix step).obj point)) :
    ((forward step point).obj ((backward step point).obj future)).1 = future.1 := by
  exact Future.objects_ext (first := (forward step point).obj ((backward step point).obj future) |>.1)
    (second := future.1) rfl
    (heq_of_eq ((Category.assoc step point.2 future.2.1).symm.trans future.2.2))

theorem forward_backward_obj (point : Future.Objects second)
    (future : Future.Objects ((ContextualSmallFamilyUniverse.futurePrefix step).obj point)) :
    (forward step point).obj ((backward step point).obj future) = future :=
  Future.objects_ext (forward_backward_target step point future)
    (ContextualSmallFamilyUniverse.futureArrow_heq rfl (forward_backward_target step point future) _ _ HEq.rfl)

theorem backward_forward_target (point : Future.Objects second) (future : Future.Objects point) :
    ((backward step point).obj ((forward step point).obj future)).1 = future.1 :=
  Future.objects_ext rfl (heq_of_eq future.2.2)

theorem backward_forward_obj (point : Future.Objects second) (future : Future.Objects point) :
    (backward step point).obj ((forward step point).obj future) = future :=
  Future.objects_ext (backward_forward_target step point future)
    (ContextualSmallFamilyUniverse.futureArrow_heq rfl (backward_forward_target step point future) _ _ HEq.rfl)

theorem forward_backward (point : Future.Objects second) :
    Cat.compose (backward step point) (forward step point) =
      Cat.identity (Future.Objects ((ContextualSmallFamilyUniverse.futurePrefix step).obj point)) := by
  refine Functor.hext (forward_backward_obj step point) ?_
  intro source target arrow
  exact ContextualSmallFamilyUniverse.futureArrow_heq
    (forward_backward_obj step point source) (forward_backward_obj step point target) _ _
    (ContextualSmallFamilyUniverse.futureArrow_heq
      (forward_backward_target step point source) (forward_backward_target step point target) _ _ HEq.rfl)

theorem backward_forward (point : Future.Objects second) :
    Cat.compose (forward step point) (backward step point) = Cat.identity (Future.Objects point) := by
  refine Functor.hext (backward_forward_obj step point) ?_
  intro source target arrow
  exact ContextualSmallFamilyUniverse.futureArrow_heq
    (backward_forward_obj step point source) (backward_forward_obj step point target) _ _
    (ContextualSmallFamilyUniverse.futureArrow_heq
      (backward_forward_target step point source) (backward_forward_target step point target) _ _ HEq.rfl)

def futureEquiv (point : Future.Objects second) :
    Future.Objects point ≃ Future.Objects ((ContextualSmallFamilyUniverse.futurePrefix step).obj point) where
  toFun := (forward step point).obj
  invFun := (backward step point).obj
  left_inv := backward_forward_obj step point
  right_inv := forward_backward_obj step point

end Mettapedia.TypeTheory.ContextualFutureConeChange
