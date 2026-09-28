import Mettapedia.TypeTheory.MaterialSets.Hypersets.WellFounded

/-!
# No hyperset contains every hyperset

Anti-foundation permits circular membership, `Ω ∈ Ω`, but not a universal set. Separation
excludes a member containing every element of its own carrier, without foundation or excluded
middle (`not_exists_universal_of_separation`, Russell's argument). For hypersets:

* every hyperset `V` has an explicit non-member, the Russell set `{x ∈ V | x ∉ x}`
  (`russell_notMem`);
* no hyperset contains every hyperset (`HSet.not_exists_universal`), and the type `HSet` is not
  the members of any hyperset (`HSet.fst_not_surjective`); so the family of all hypersets,
  indexed by the large type `HSet`, has no image (`HSet.not_exists_image_id`).

So the ambient hyperset universe is a type, not a member of itself.

A set containing every set would be a self-member, and a self-member is not in the accessible
part of membership (`not_acc_of_rel_self`). Hence a universal hyperset would not be
well-founded (`HSet.not_wf_of_forall_mem`), and no well-founded hyperset contains every
well-founded hyperset (`WellFoundedPart.not_exists_universal`).

**Controls.** The Russell set of `Ω` is empty (`russell_quineAtom`); the Russell set of a
well-founded hyperset is the hyperset itself (`russell_of_wf`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets

universe u v

/-- Russell's argument: with separation, no element contains every element of its carrier.
Neither foundation nor excluded middle is used. -/
theorem not_exists_universal_of_separation {S : Type u} (mem : S → S → Prop)
    (separate : ∀ (bound : S) (P : S → Prop), ∃ subset, ∀ x, mem x subset ↔ mem x bound ∧ P x) :
    ¬ ∃ whole, ∀ x, mem x whole := by
  rintro ⟨whole, contains⟩
  obtain ⟨russell, specification⟩ := separate whole fun x => ¬ mem x x
  have absent : ¬ mem russell russell := fun present =>
    ((specification russell).mp present).2 present
  exact absent ((specification russell).mpr ⟨contains russell, absent⟩)

namespace Hypersets

namespace HSet

/-- The Russell set of `V`: the members of `V` that are not members of themselves. -/
def russell (V : HSet.{u}) : HSet.{u} :=
  HSet.sep (fun x => x ∉ x) V

theorem mem_russell {V x : HSet.{u}} : x ∈ russell V ↔ x ∈ V ∧ x ∉ x :=
  mem_sep

/-- The Russell set of `V` is not a member of `V`. -/
theorem russell_notMem (V : HSet.{u}) : russell V ∉ V := fun h => by
  have absent : russell V ∉ russell V := fun present => (mem_russell.mp present).2 present
  exact absent (mem_russell.mpr ⟨h, absent⟩)

theorem exists_notMem (V : HSet.{u}) : ∃ x, x ∉ V :=
  ⟨russell V, russell_notMem V⟩

/-- No hyperset contains every hyperset. -/
theorem not_exists_universal : ¬ ∃ V : HSet.{u}, ∀ x, x ∈ V :=
  not_exists_universal_of_separation (fun x V : HSet.{u} => x ∈ V)
    fun V P => ⟨HSet.sep P V, fun _ => mem_sep⟩

/-- The type `HSet` is not the members of any hyperset. -/
theorem fst_not_surjective (V : HSet.{u}) :
    ¬ Function.Surjective (PSigma.fst : El (· ∈ ·) V → HSet.{u}) := fun h =>
  let ⟨a, ha⟩ := h (russell V)
  russell_notMem V (ha ▸ a.2)

/-- The family of all hypersets has no image: it has no collecting hyperset. -/
theorem not_exists_image_id : ¬ ∃ z : HSet.{u}, ∀ y, y ∈ z ↔ ∃ x, x = y :=
  fun ⟨z, hz⟩ => not_exists_universal ⟨z, fun x => (hz x).mpr ⟨x, rfl⟩⟩

/-- A hyperset containing every hyperset would be a self-member, so it is not well-founded. -/
theorem not_wf_of_forall_mem {V : HSet.{u}} (h : ∀ x, x ∈ V) : ¬ V.WF :=
  not_wf_of_mem_self (h V)

/-! ## Examples -/

theorem russell_quineAtom : russell quineAtom.{u} = ∅ :=
  eq_empty_iff.mpr fun _ h =>
    let ⟨hx, hself⟩ := mem_russell.mp h
    hself (mem_quineAtom.mp hx ▸ quineAtom_mem_self)

theorem russell_of_wf {V : HSet.{u}} (hV : V.WF) : russell V = V :=
  ext fun _ => mem_russell.trans ⟨And.left, fun h => ⟨h, (hV.mem h).notMem_self⟩⟩

end HSet

/-- No well-founded hyperset contains every well-founded hyperset: it would be a self-member. -/
theorem WellFoundedPart.not_exists_universal :
    ¬ ∃ V : WellFoundedPart.{u}, ∀ x : WellFoundedPart.{u}, x.1 ∈ V.1 :=
  fun ⟨V, h⟩ => V.2.notMem_self (h V)

end Hypersets

end Mettapedia.TypeTheory.MaterialSets
