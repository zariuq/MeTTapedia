import Mettapedia.TypeTheory.DisplayedPresheafEvidenceUniversal
import Mathlib.CategoryTheory.Yoneda

/-!
# Representable origin specifications along a native program map

A caller origin is an actual arrow on the source program's element category.
The corresponding target specification is authored as a representable on
the target element category. Naturality of the program map transports every
origin, and native sum elimination extends this transport to all receipts.
This concerns one common context category, not arbitrary target contexts.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafRepresentableEvidence

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafEvidenceTransport DisplayedPresheafEvidenceUniversal

universe u
variable {C : Type u} [Category.{u} C] {P Q : Cᵒᵖ ⥤ Type u}

def origins (point : P.Elements) : DisplayedFamily P := coyoneda.obj (Opposite.op point)

def originMap (f : P ⟶ Q) (point : P.Elements) :
    origins point ⟶ reindexDisplayed f (origins (f.mapElements.obj point)) where
  app _ := TypeCat.ofHom (fun origin => f.mapElements.map origin)
  naturality first second arrow := by
    ext origin
    exact (f.mapElements.map_comp origin arrow).symm

def originReadout (f : P ⟶ Q) (point : P.Elements) :
    transport f (origins point) ⟶ origins (f.mapElements.obj point) :=
  descend f (originMap f point)

theorem originReadout_computes (f : P ⟶ Q) (point current : P.Elements)
    (origin : (origins point).obj current) :
    (originReadout f point).app (f.mapElements.obj current)
        ((unit f (origins point)).app current origin) = f.mapElements.map origin :=
  descend_unit f (originMap f point) current origin

/-- Transport on element arrows retains their underlying context arrow.
It therefore does not identify two origins at a fixed source point. -/
theorem originMap_injective (f : P ⟶ Q) (point current : P.Elements) :
    Function.Injective ((originMap f point).app current) := by
  intro first second same
  apply Subtype.ext
  exact congrArg (fun arrow => arrow.val) same

theorem originReadout_distinguishes (f : P ⟶ Q) (point current : P.Elements)
    {first second : (origins point).obj current} (different : first ≠ second) :
    (originReadout f point).app (f.mapElements.obj current)
        ((unit f (origins point)).app current first) ≠
      (originReadout f point).app (f.mapElements.obj current)
        ((unit f (origins point)).app current second) := by
  rw [originReadout_computes, originReadout_computes]
  exact fun same => different (originMap_injective f point current same)

end Mettapedia.TypeTheory.DisplayedPresheafRepresentableEvidence
