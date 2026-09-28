import Mettapedia.TypeTheory.MaterialSets.Hypersets.WellFounded

/-!
# Kuratowski pairs of hypersets

The Kuratowski pair `kpair x y = {{x}, {x, y}}`. Its projections are derived from union and
separation:

* `fst z = ⋃ ⋂ z`, where `⋂ z` is separated from `⋃ z`;
* `snd z = ⋃ {a ∈ ⋃ z | a ∈ ⋂ z → ⋃ z = ⋂ z}`.

The separating condition of `snd` is a proposition, not a decision, so `snd (kpair x y) = y`
holds without excluded middle (`snd_kpair`), as does `fst (kpair x y) = x` (`fst_kpair`).
Both hold for all hypersets, well-founded or not, and the well-founded part is closed under
pairing and both projections.

**Controls.** `kpair x x = {{x}}` (`kpair_self`); the pair of `∅` and `{∅}` differs from the
pair in the other order (`kpair_empty_ne_swap`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

namespace HSet

variable {x y z a : HSet.{u}}

/-- The Kuratowski pair `{{x}, {x, y}}`. -/
def kpair (x y : HSet.{u}) : HSet.{u} :=
  {{x}, {x, y}}

/-- The intersection of the members of `z`, separated from their union. -/
def sInter (z : HSet.{u}) : HSet.{u} :=
  HSet.sep (fun a => ∀ w ∈ z, a ∈ w) (sUnion z)

/-- The first projection, `⋃ ⋂ z`. -/
def fst (z : HSet.{u}) : HSet.{u} :=
  sUnion (sInter z)

/-- The second projection, `⋃ {a ∈ ⋃ z | a ∈ ⋂ z → ⋃ z = ⋂ z}`. -/
def snd (z : HSet.{u}) : HSet.{u} :=
  sUnion (HSet.sep (fun a => a ∈ sInter z → sUnion z = sInter z) (sUnion z))

theorem mem_sInter : a ∈ sInter z ↔ (∃ w ∈ z, a ∈ w) ∧ ∀ w ∈ z, a ∈ w := by
  rw [sInter, mem_sep, mem_sUnion]

theorem mem_kpair : z ∈ kpair x y ↔ z = {x} ∨ z = {x, y} :=
  mem_pair

theorem mem_sUnion_kpair : a ∈ sUnion (kpair x y) ↔ a = x ∨ a = y := by
  rw [mem_sUnion]
  constructor
  · rintro ⟨w, hw, ha⟩
    rcases mem_kpair.mp hw with rfl | rfl
    · exact Or.inl (mem_singleton.mp ha)
    · exact mem_pair.mp ha
  · rintro (rfl | rfl)
    · exact ⟨{a}, mem_kpair.mpr (Or.inl rfl), mem_singleton_self a⟩
    · exact ⟨{x, a}, mem_kpair.mpr (Or.inr rfl), mem_pair.mpr (Or.inr rfl)⟩

theorem mem_sInter_kpair : a ∈ sInter (kpair x y) ↔ a = x := by
  rw [mem_sInter]
  constructor
  · rintro ⟨_, h⟩
    exact mem_singleton.mp (h {x} (mem_kpair.mpr (Or.inl rfl)))
  · rintro rfl
    refine ⟨⟨{a}, mem_kpair.mpr (Or.inl rfl), mem_singleton_self a⟩, fun w hw => ?_⟩
    rcases mem_kpair.mp hw with rfl | rfl
    · exact mem_singleton_self a
    · exact mem_pair.mpr (Or.inl rfl)

theorem sInter_kpair : sInter (kpair x y) = {x} :=
  ext fun _ => mem_sInter_kpair.trans mem_singleton.symm

/-- The first projection of a Kuratowski pair. -/
theorem fst_kpair (x y : HSet.{u}) : fst (kpair x y) = x := by
  rw [fst, sInter_kpair, sUnion_singleton]

theorem sUnion_kpair_eq_sInter_kpair_iff : sUnion (kpair x y) = sInter (kpair x y) ↔ y = x := by
  constructor
  · intro h
    have hy : y ∈ sUnion (kpair x y) := mem_sUnion_kpair.mpr (Or.inr rfl)
    rw [h] at hy
    exact mem_sInter_kpair.mp hy
  · rintro rfl
    exact ext fun _ => mem_sUnion_kpair.trans (or_self_iff.trans mem_sInter_kpair.symm)

/-- The second projection of a Kuratowski pair. -/
theorem snd_kpair (x y : HSet.{u}) : snd (kpair x y) = y := by
  have separated : HSet.sep (fun a => a ∈ sInter (kpair x y) →
      sUnion (kpair x y) = sInter (kpair x y)) (sUnion (kpair x y)) = {y} := by
    ext a
    rw [mem_sep, mem_sUnion_kpair, mem_sInter_kpair, sUnion_kpair_eq_sInter_kpair_iff,
      mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, h⟩
      · exact (h rfl).symm
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, id⟩
  rw [snd, separated, sUnion_singleton]

theorem kpair_inj {x y x' y' : HSet.{u}} : kpair x y = kpair x' y' ↔ x = x' ∧ y = y' :=
  ⟨fun h => ⟨(fst_kpair x y).symm.trans (h ▸ fst_kpair x' y'),
      (snd_kpair x y).symm.trans (h ▸ snd_kpair x' y')⟩,
    fun ⟨hx, hy⟩ => hx ▸ hy ▸ rfl⟩

/-! ## The well-founded part -/

theorem WF.kpair (hx : x.WF) (hy : y.WF) : (kpair x y).WF :=
  hx.singleton.pair (hx.pair hy)

theorem WF.sInter (hz : z.WF) : (sInter z).WF :=
  hz.sUnion.sep _

theorem WF.fst (hz : z.WF) : (fst z).WF :=
  hz.sInter.sUnion

theorem WF.snd (hz : z.WF) : (snd z).WF :=
  (hz.sUnion.sep _).sUnion

/-! ## Examples -/

theorem kpair_self (x : HSet.{u}) : kpair x x = {{x}} :=
  ext fun _ => mem_kpair.trans
    ⟨fun h => mem_singleton.mpr (h.elim id fun e => e.trans
        (ext fun _ => mem_pair.trans (or_self_iff.trans mem_singleton.symm))),
      fun h => Or.inl (mem_singleton.mp h)⟩

theorem kpair_empty_ne_swap : kpair (∅ : HSet.{u}) {∅} ≠ kpair {∅} ∅ :=
  fun h => empty_ne_singleton_empty ((kpair_inj.mp h).1)

end HSet

end Mettapedia.TypeTheory.MaterialSets.Hypersets
