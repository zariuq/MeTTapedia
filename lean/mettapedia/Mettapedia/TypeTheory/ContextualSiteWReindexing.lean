import Mettapedia.TypeTheory.ContextualSiteW
import Mettapedia.TypeTheory.ContextualWReindexing

/-!
# Structural W lifting commutes with independently formed signatures

Raising a contextual signature retains every world, actual arrow, shape
and dependent position. These laws compare indexed recursion on the two
independently formed tree carriers, including arbitrary context functors.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSiteWReindexing

open CategoryTheory MaterialSets.Hypersets
open ContextualWTypes (RawTree)
open ContextualWReindexing

universe u
variable {D E : Type u} [Category.{u} D] [Category.{u} E]

def liftFunctor (change : D ⥤ E) : PresheafSiteLift.Site D ⥤ PresheafSiteLift.Site E where
  obj point := ⟨change.obj point.down⟩
  map step := ⟨change.map step.down⟩
  map_id point := congrArg ULift.up (change.map_id point.down)
  map_comp first later := congrArg ULift.up (change.map_comp first.down later.down)

def signatureUp (signature : Signature D) : Signature (PresheafSiteLift.Site D) :=
  ⟨ContextualSiteW.shapeUp signature.1, ContextualSiteW.positionUp signature.1 signature.2⟩

theorem signature_under (change : D ⥤ E) (signature : Signature E) :
    under (liftFunctor change) (signatureUp signature) = signatureUp (under change signature) := by
  rfl

theorem raise_congr {first second : Signature D} (signatures : first = second)
    {leftPoint rightPoint : PresheafSiteLift.Site D} (points : leftPoint = rightPoint)
    (left : Raw first leftPoint.down) (right : Raw second rightPoint.down) (trees : HEq left right) :
    HEq (ContextualSiteW.raiseRaw first.1 first.2 leftPoint left)
      (ContextualSiteW.raiseRaw second.1 second.2 rightPoint right) := by
  cases signatures
  cases points
  cases eq_of_heq trees
  rfl

theorem raise_pull_data (change : D ⥤ E) (signature : Signature E)
    {target : E} (tree : Raw signature target) :
    ∀ point : D, ∀ same : change.obj point = target,
      HEq
        (ContextualSiteW.raiseRaw (under change signature).1 (under change signature).2
          (ULift.up point) (pullData change signature tree point same))
        (pullData (liftFunctor change) (signatureUp signature)
          (ContextualSiteW.raiseRaw signature.1 signature.2 (ULift.up target) tree)
          (ULift.up point) (congrArg ULift.up same)) := by
  induction tree with
  | @sup target label children earlier =>
    intro point same
    cases same
    apply heq_of_eq
    apply RawTree.sup_eq_of_cast rfl
    intro next arrow branch
    exact eq_of_heq (earlier _ _ _ next.down rfl)

theorem raise_pull (change : D ⥤ E) (signature : Signature E)
    (point : PresheafSiteLift.Site D) (tree : Raw signature (change.obj point.down)) :
    HEq (ContextualSiteW.raiseRaw (under change signature).1 (under change signature).2
        point (pull change signature point.down tree))
      (pull (liftFunctor change) (signatureUp signature) point
        (ContextualSiteW.raiseRaw signature.1 signature.2 ((liftFunctor change).obj point) tree)) :=
  raise_pull_data change signature tree point.down rfl

end Mettapedia.TypeTheory.ContextualSiteWReindexing
