import Mettapedia.GSLT.Topos.PresheafPredicateHeyting
import Mettapedia.GSLT.Topos.PresheafPredicateQuantifierBaseChange

/-!
# Native none query of admitted contextual events

Existential support is the image of the admitted events along their source.
Its Heyting negation excludes an event over every future image of the source.
Present the none query agrees with this native predicate when admitted source fibres
reflect availability along context maps. Ordinary event naturality alone is
not such a reflection condition.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.PresheafEventNone

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w
variable {C : Type u} [Category.{v} C]
variable {E P : Cᵒᵖ ⥤ Type w}

/-- Existential support of the independently admitted events. -/
def enabled (source : E ⟶ P) (admitted : Subfunctor E) : Subfunctor P :=
  admitted.image source

/-- Native negation of existential event support. -/
noncomputable def noneEnabled (source : E ⟶ P) (admitted : Subfunctor E) : Subfunctor P :=
  enabled source admitted ⇨ ⊥

theorem mem_enabled (source : E ⟶ P) (admitted : Subfunctor E)
    (world : Cᵒᵖ) (program : P.obj world) :
    program ∈ (enabled source admitted).obj world ↔
      ∃ event : E.obj world, event ∈ admitted.obj world ∧ source.app world event = program :=
  Iff.rfl

/-- Native none reads every future fibre, including the identity fibre. -/
theorem mem_noneEnabled (source : E ⟶ P) (admitted : Subfunctor E)
    (world : Cᵒᵖ) (program : P.obj world) :
    program ∈ (noneEnabled source admitted).obj world ↔
      ∀ (future : Cᵒᵖ) (change : world ⟶ future),
        ¬ ∃ event : E.obj future,
          event ∈ admitted.obj future ∧ source.app future event = P.map change program := by
  rw [noneEnabled, ← himpPointwise_eq_himp]
  rfl

/-- A local lifting property for admitted source fibres, rather than an
assumption of the desired negative-premise equivalence. -/
def ReflectsAvailability (source : E ⟶ P) (admitted : Subfunctor E) : Prop :=
  ∀ {world future : Cᵒᵖ} (change : world ⟶ future) (program : P.obj world)
    (event : E.obj future), event ∈ admitted.obj future →
    source.app future event = P.map change program →
      ∃ earlier : E.obj world, earlier ∈ admitted.obj world ∧
        source.app world earlier = program

/-- Reflection of admitted fibres earns present none queries as native negation. -/
theorem noneEnabled_iff_present (source : E ⟶ P) (admitted : Subfunctor E)
    (reflection : ReflectsAvailability source admitted)
    (world : Cᵒᵖ) (program : P.obj world) :
    program ∈ (noneEnabled source admitted).obj world ↔
      ¬ ∃ event : E.obj world, event ∈ admitted.obj world ∧ source.app world event = program := by
  rw [mem_noneEnabled]
  constructor
  · intro holds present
    apply holds world (𝟙 world)
    simpa only [Functor.map_id_apply] using present
  · intro holds future change present
    obtain ⟨event, member, over⟩ := present
    exact holds (reflection change program event member over)

/-- Event substitution uses an actual pullback; native none query preserves
the resulting existential support comparison. -/
theorem noneEnabled_beckChevalley {E' P' : Cᵒᵖ ⥤ Type w}
    (eventMap : E' ⟶ E) (source' : E' ⟶ P') (source : E ⟶ P)
    (programMap : P' ⟶ P) (square : IsPullback eventMap source' source programMap)
    (admitted : Subfunctor E) :
    (noneEnabled source admitted).preimage programMap =
      noneEnabled source' (admitted.preimage eventMap) := by
  rw [noneEnabled, preimage_himp]
  change (admitted.image source).preimage programMap ⇨ ⊥ =
    (admitted.preimage eventMap).image source' ⇨ ⊥
  rw [image_beckChevalley eventMap source' source programMap square]

end Mettapedia.GSLT.Topos.PresheafEventNone
