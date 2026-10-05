import Mettapedia.TypeTheory.DisplayedContextualWitnessCover

/-!
# Optional host-choice existence of small contextual witness covers

This module explicitly selects generator witnesses with `Classical.choice`
from mere pointwise nonemptiness. The free cover, its small carrier and
projection are constructed in the independent choice-free core. Only the
generic selection of witness data, and declarations using that selection,
inherit host choice. This is a model comparison, not a native choice rule or
an interpretation of unrestricted internal Collection.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.HostChoiceContextualWitnessCover

open CategoryTheory ContextualWitnessCover

universe u v

variable {E : Type u} [Category.{u} E]

/-- The host selection is named explicitly and kept outside the core. -/
noncomputable def selectedWitness (R : E ⥤ Type v) (inhabited : ∀ point, Nonempty (R.obj point)) :
    ∀ point, R.obj point := fun point => Classical.choice (inhabited point)

noncomputable def selectedMap (R : E ⥤ Type v) (inhabited : ∀ point, Nonempty (R.obj point)) :
    NaturalHom (free (E := E)) R := fromWitness R (selectedWitness R inhabited)

theorem exists_small_cover_from_nonempty (R : E ⥤ Type v)
    (inhabited : ∀ point, Nonempty (R.obj point)) :
    ∃ (Q : E ⥤ Type u) (_operation : NaturalHom Q R) (covers : NatTrans Q terminal),
      ∀ point, Function.Surjective (covers.app point) :=
  ⟨free, selectedMap R inhabited, projection, projection_surjective⟩

variable {D : Type u} [Category.{u} D] (A : D ⥤ Type u) (R : A.Elements ⥤ Type v)

/-- The generic optional comparison still builds its actual small covering
projection; only its map into the wide witness relation uses host choice. -/
noncomputable def displayedSelectedMap (inhabited : ∀ point, Nonempty (R.obj point)) :
    NaturalHom (DisplayedContextualWitnessCover.smallCover A)
      (DisplayedContextualWitnessCover.totalWitnesses A R) :=
  DisplayedContextualWitnessCover.witnessMap A R (selectedWitness R inhabited)

theorem displayed_selected_projection (inhabited : ∀ point, Nonempty (R.obj point)) :
    (displayedSelectedMap A R inhabited).comp (DisplayedContextualWitnessCover.witnessProjection A R) =
      NaturalHom.ofNatTrans (DisplayedContextualWitnessCover.projection A) :=
  DisplayedContextualWitnessCover.witnessMap_projection A R (selectedWitness R inhabited)

#print axioms selectedWitness
#print axioms selectedMap
#print axioms exists_small_cover_from_nonempty
#print axioms displayedSelectedMap
#print axioms displayed_selected_projection

end Mettapedia.TypeTheory.HostChoiceContextualWitnessCover
