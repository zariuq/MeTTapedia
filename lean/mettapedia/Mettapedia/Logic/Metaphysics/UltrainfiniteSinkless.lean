import Mettapedia.TypeTheory.MaterialSets.Hypersets.AntiFoundation

/-!
# Sinkless collapse: pure structure without empties is one thing

A hyperset is **hereditarily nonempty** (`HereditarilyNonempty`) when every member of its
transitive closure, itself included, has a member. Among hypersets there is exactly one such
thing, Aczel's `Ω = {Ω}`:

* the relation "both are hereditarily nonempty" is a bisimulation of the membership graph
  (`isBisimulation_hereditarilyNonempty`), so by strong extensionality any two hereditarily
  nonempty hypersets are equal (`eq_of_hereditarilyNonempty`);
* `Ω` is hereditarily nonempty (`hereditarilyNonempty_quineAtom`), hence
  `hereditarilyNonempty_iff_eq_quineAtom` and `setOf_hereditarilyNonempty`.

**Presentations.** A graph pictures `Ω` at a node exactly when no sink is reachable from it
(`decorate_eq_quineAtom_iff_sinkless`). The loop and the two-node cycle are two such
presentations; the theorem says that every sinkless presentation, finite or not, of any shape,
pictures the same whole.

**Controls.**
* With a sink, plurality appears: `∅ ≠ {∅}` (`empty_ne_singleton_empty`), and neither is
  hereditarily nonempty (`not_hereditarilyNonempty_empty`,
  `not_hereditarilyNonempty_singleton_empty`).
* A hereditarily nonempty hyperset has no well-founded part: every member of its closure is
  `Ω` itself (`eq_quineAtom_of_inClosure`).

The closure is the reflexive transitive closure of membership, so a member of the closure is
reached by a finite chain of memberships; that chain is the metatheory's reading, while the
statement "no member of the closure is empty" is about the hyperset.

P. Aczel, *Non-well-founded Sets*, CSLI Lecture Notes 14, 1988, chapter 2 (`Ω` and strong
extensionality).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

open Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u



open Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet

/-- `y` is in the transitive closure of `x`, `x` itself included: a finite chain of memberships
leads from `x` down to `y`. -/
def InClosure (x y : HSet.{u}) : Prop :=
  Relation.ReflTransGen (fun a b : HSet.{u} => b ∈ a) x y

/-- **Hereditarily nonempty**: every member of the transitive closure, itself included, has a
member. -/
def HereditarilyNonempty (x : HSet.{u}) : Prop :=
  ∀ y, InClosure x y → ∃ z, z ∈ y

namespace HereditarilyNonempty

variable {x y : HSet.{u}}

theorem nonempty (h : HereditarilyNonempty x) : ∃ z, z ∈ x :=
  h x .refl

theorem mem (h : HereditarilyNonempty x) (hy : y ∈ x) : HereditarilyNonempty y :=
  fun z hz => h z (Relation.ReflTransGen.head hy hz)

end HereditarilyNonempty

/-- Every member of the closure of `Ω` is `Ω`. -/
theorem eq_quineAtom_of_inClosure {y : HSet.{u}} (h : InClosure quineAtom y) : y = quineAtom := by
  induction h with
  | refl => rfl
  | tail _ step ih =>
    subst ih
    exact mem_quineAtom.mp step

theorem hereditarilyNonempty_quineAtom : HereditarilyNonempty quineAtom.{u} := by
  intro y hy
  rw [eq_quineAtom_of_inClosure hy]
  exact ⟨quineAtom, quineAtom_mem_self⟩

/-- **"Both are hereditarily nonempty" is a bisimulation** of the membership graph. -/
theorem isBisimulation_hereditarilyNonempty :
    IsBisimulation (fun x y : HSet.{u} => y ∈ x) (fun x y => y ∈ x)
      (fun x y => HereditarilyNonempty x ∧ HereditarilyNonempty y) := by
  rintro x y ⟨hx, hy⟩
  refine ⟨fun x' hx' => ?_, fun y' hy' => ?_⟩
  · obtain ⟨y', hy'⟩ := hy.nonempty
    exact ⟨y', hy', hx.mem hx', hy.mem hy'⟩
  · obtain ⟨x', hx'⟩ := hx.nonempty
    exact ⟨x', hx', hx.mem hx', hy.mem hy'⟩

/-- **Sinkless collapse**: two hereditarily nonempty hypersets are equal. -/
theorem eq_of_hereditarilyNonempty {x y : HSet.{u}} (hx : HereditarilyNonempty x)
    (hy : HereditarilyNonempty y) : x = y :=
  eq_of_isBisimulation isBisimulation_hereditarilyNonempty ⟨hx, hy⟩

/-- **The only hereditarily nonempty hyperset is `Ω`.** -/
theorem hereditarilyNonempty_iff_eq_quineAtom {x : HSet.{u}} :
    HereditarilyNonempty x ↔ x = quineAtom :=
  ⟨fun hx => eq_of_hereditarilyNonempty hx hereditarilyNonempty_quineAtom,
    fun e => e ▸ hereditarilyNonempty_quineAtom⟩

theorem setOf_hereditarilyNonempty :
    {x : HSet.{u} | HereditarilyNonempty x} = {quineAtom} :=
  Set.ext fun _ => hereditarilyNonempty_iff_eq_quineAtom

/-! ## Presentations: sinkless graphs picture `Ω` -/

section Presentations

variable {α : Type u} {r : α → α → Prop}

/-- The closure of a pictured hyperset is pictured at the reachable nodes. -/
theorem exists_reachable_of_inClosure {a : α} {y : HSet.{u}} (h : InClosure (decorate r a) y) :
    ∃ b, Relation.ReflTransGen r a b ∧ decorate r b = y := by
  induction h with
  | refl => exact ⟨a, .refl, rfl⟩
  | tail _ step ih =>
    obtain ⟨b, hab, rfl⟩ := ih
    obtain ⟨c, hbc, rfl⟩ := mem_decorate.mp step
    exact ⟨c, hab.tail hbc, rfl⟩

theorem inClosure_of_reachable {a b : α} (h : Relation.ReflTransGen r a b) :
    InClosure (decorate r a) (decorate r b) := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail (decorate_mem_decorate hbc)

/-- **A graph pictures `Ω` at a node exactly when no sink is reachable from it.** -/
theorem decorate_eq_quineAtom_iff_sinkless {a : α} :
    decorate r a = quineAtom ↔ ∀ b, Relation.ReflTransGen r a b → ∃ c, r b c := by
  rw [← hereditarilyNonempty_iff_eq_quineAtom]
  constructor
  · intro h b hab
    obtain ⟨z, hz⟩ := h _ (inClosure_of_reachable hab)
    obtain ⟨c, hbc, -⟩ := mem_decorate.mp hz
    exact ⟨c, hbc⟩
  · intro h y hy
    obtain ⟨b, hab, rfl⟩ := exists_reachable_of_inClosure hy
    obtain ⟨c, hbc⟩ := h b hab
    exact ⟨_, decorate_mem_decorate hbc⟩

end Presentations

/-! ## Controls -/

theorem not_hereditarilyNonempty_empty : ¬ HereditarilyNonempty (∅ : HSet.{u}) := fun h =>
  let ⟨z, hz⟩ := h.nonempty
  notMem_empty z hz

theorem not_hereditarilyNonempty_singleton_empty :
    ¬ HereditarilyNonempty ({∅} : HSet.{u}) := fun h =>
  not_hereditarilyNonempty_empty (h.mem (mem_singleton_self ∅))

/-- **With a sink, plurality appears**: `∅` and `{∅}` are two hypersets, and neither is
hereditarily nonempty. -/
theorem sink_plurality :
    (∅ : HSet.{u}) ≠ {∅} ∧ ¬ HereditarilyNonempty (∅ : HSet.{u}) ∧
      ¬ HereditarilyNonempty ({∅} : HSet.{u}) :=
  ⟨empty_ne_singleton_empty, not_hereditarilyNonempty_empty,
    not_hereditarilyNonempty_singleton_empty⟩

/-- The two-node cycle is sinkless, so it pictures `Ω` at each node, as the loop does. -/
theorem twoCycle_sinkless (a : twoCycle.{u}.Node) :
    ∀ b, Relation.ReflTransGen twoCycle.{u}.edge a b → ∃ c, twoCycle.{u}.edge b c :=
  fun b _ => ⟨⟨!b.down⟩, rfl⟩



end Mettapedia.Logic.Metaphysics.Ultrainfinite

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

#print axioms isBisimulation_hereditarilyNonempty
#print axioms eq_of_hereditarilyNonempty
#print axioms hereditarilyNonempty_quineAtom
#print axioms hereditarilyNonempty_iff_eq_quineAtom
#print axioms setOf_hereditarilyNonempty
#print axioms decorate_eq_quineAtom_iff_sinkless
#print axioms eq_quineAtom_of_inClosure
#print axioms sink_plurality
#print axioms twoCycle_sinkless

end Mettapedia.Logic.Metaphysics.Ultrainfinite
