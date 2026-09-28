import Mettapedia.TypeTheory.MaterialSets.Hypersets.Operations

/-!
# The anti-foundation axiom

A decoration of a graph `r` on `α` assigns a hyperset to each node so that the members of
the hyperset at `a` are the hypersets at the children of `a` (`IsDecoration`). Aczel's
anti-foundation axiom says that every graph has exactly one decoration. For hypersets it is a
theorem, for graphs with nodes in `Type u`:

* existence: `decorate r` is a decoration (`isDecoration_decorate`);
* uniqueness: every decoration is `decorate r` (`IsDecoration.eq_decorate`), by strong
  extensionality.

**Controls.**
* `quineAtom`, Aczel's `Ω`, pictured by a one-node loop, satisfies `Ω = {Ω}`
  (`quineAtom_eq_singleton`), and it is the only hyperset `x` with `x = {x}`
  (`eq_singleton_self_iff`). The empty set is not such a solution (`empty_ne_singleton_empty`).
* A one-node loop and a two-node cycle both picture `Ω` (`mk_loop`, `mk_twoCycle`), and both
  nodes of the cycle are decorated by `Ω` (`decorate_twoCycle`). The total relation is a
  bisimulation between them (`loop_equiv_twoCycle`), although their node types have one and two
  elements (`not_nonempty_loop_node_equiv`) and the graphs differ (`loop_ne_twoCycle`):
  bisimulation forgets the shape of the graph.
* The constant family `∅` is not a decoration of the loop (`not_isDecoration_empty_loop`).

P. Aczel, *Non-well-founded Sets*, CSLI Lecture Notes 14, 1988;
J. Barwise and L. Moss, *Vicious Circles*, CSLI Lecture Notes 60, 1996.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

open AccessiblePointedGraph

universe u

namespace HSet

/-! ## Every graph has exactly one decoration -/

section Decoration

variable {α : Type u}

/-- A decoration of the graph `r`: the members of the hyperset at `a` are the hypersets at
the children of `a`. -/
def IsDecoration (r : α → α → Prop) (d : α → HSet.{u}) : Prop :=
  ∀ a y, y ∈ d a ↔ ∃ b, r a b ∧ d b = y

/-- Existence of decorations: every graph is decorated by the hypersets it pictures. -/
theorem isDecoration_decorate (r : α → α → Prop) : IsDecoration r (decorate r) :=
  fun _ _ => mem_decorate

/-- Uniqueness of decorations: a graph has only one decoration. -/
theorem IsDecoration.eq_decorate {r : α → α → Prop} {d : α → HSet.{u}}
    (hd : IsDecoration r d) : d = decorate r := by
  funext a
  refine eq_of_isBisimulation (R := fun x y => ∃ a, d a = x ∧ decorate r a = y) ?_ ⟨a, rfl, rfl⟩
  rintro _ _ ⟨a, rfl, rfl⟩
  refine ⟨fun x' hx => ?_, fun y' hy => ?_⟩
  · obtain ⟨b, hb, rfl⟩ := (hd a x').mp hx
    exact ⟨decorate r b, decorate_mem_decorate hb, b, rfl, rfl⟩
  · obtain ⟨b, hb, rfl⟩ := mem_decorate.mp hy
    exact ⟨d b, (hd a _).mpr ⟨b, hb, rfl⟩, b, rfl, rfl⟩

theorem IsDecoration.unique {r : α → α → Prop} {d d' : α → HSet.{u}} (hd : IsDecoration r d)
    (hd' : IsDecoration r d') : d = d' :=
  hd.eq_decorate.trans hd'.eq_decorate.symm

/-- Aczel's anti-foundation axiom: every graph has exactly one decoration. -/
theorem existsUnique_isDecoration (r : α → α → Prop) : ∃! d, IsDecoration r d :=
  ⟨decorate r, isDecoration_decorate r, fun _ hd => hd.eq_decorate⟩

end Decoration

/-! ## `Ω = {Ω}` -/

/-- The one-node loop. -/
def loop : AccessiblePointedGraph.{u} where
  Node := PUnit
  edge _ _ := True
  point := PUnit.unit
  reachable _ := .refl

/-- Aczel's `Ω`, pictured by the one-node loop. -/
def quineAtom : HSet.{u} :=
  mk loop

theorem decorate_loop (a : loop.{u}.Node) : decorate loop.edge a = quineAtom :=
  (mk_eq_decorate loop).symm

theorem mem_quineAtom {y : HSet.{u}} : y ∈ quineAtom ↔ y = quineAtom := by
  have members : y ∈ decorate loop.edge loop.point ↔
      ∃ b, loop.edge loop.point b ∧ decorate loop.edge b = y :=
    mem_decorate
  rw [decorate_loop] at members
  refine members.trans ⟨fun ⟨b, _, e⟩ => ?_, fun e => ⟨loop.point, trivial, ?_⟩⟩
  · rw [← e, decorate_loop]
  · rw [decorate_loop, e]

theorem quineAtom_mem_self : quineAtom.{u} ∈ quineAtom :=
  mem_quineAtom.mpr rfl

/-- `Ω = {Ω}`. -/
theorem quineAtom_eq_singleton : quineAtom.{u} = {quineAtom} :=
  ext fun _ => mem_quineAtom.trans mem_singleton.symm

/-- `Ω` is the only hyperset `x` with `x = {x}`. -/
theorem eq_quineAtom_of_eq_singleton {x : HSet.{u}} (h : x = {x}) : x = quineAtom := by
  have members : ∀ y, y ∈ x ↔ y = x := fun y => by
    rw [← mem_singleton, ← h]
  have hd : IsDecoration loop.edge fun _ => x := fun _ y =>
    (members y).trans ⟨fun e => ⟨loop.point, trivial, e.symm⟩, fun ⟨_, _, e⟩ => e.symm⟩
  exact (congrFun hd.eq_decorate loop.point).trans (decorate_loop _)

theorem eq_singleton_self_iff {x : HSet.{u}} : x = {x} ↔ x = quineAtom :=
  ⟨eq_quineAtom_of_eq_singleton, fun h => h ▸ quineAtom_eq_singleton⟩

theorem empty_ne_quineAtom : (∅ : HSet.{u}) ≠ quineAtom :=
  fun h => notMem_empty _ (h ▸ quineAtom_mem_self)

/-- The constant family `∅` is not a decoration of the loop. -/
theorem not_isDecoration_empty_loop : ¬ IsDecoration loop.{u}.edge fun _ => ∅ :=
  fun hd => empty_ne_quineAtom ((congrFun hd.eq_decorate loop.point).trans (decorate_loop _))

/-! ## A two-node cycle -/

/-- The two-node cycle: each node has the other as its only child. -/
def twoCycle : AccessiblePointedGraph.{u} where
  Node := ULift.{u} Bool
  edge a b := b.down = !a.down
  point := ⟨true⟩
  reachable
    | ⟨true⟩ => .refl
    | ⟨false⟩ => .single rfl

theorem isDecoration_twoCycle_quineAtom : IsDecoration twoCycle.{u}.edge fun _ => quineAtom :=
  fun a _ => mem_quineAtom.trans
    ⟨fun h => ⟨⟨!a.down⟩, rfl, h.symm⟩, fun ⟨_, _, h⟩ => h.symm⟩

theorem decorate_twoCycle (a : twoCycle.{u}.Node) : decorate twoCycle.edge a = quineAtom :=
  (congrFun isDecoration_twoCycle_quineAtom.eq_decorate a).symm

theorem mk_loop : mk loop.{u} = quineAtom :=
  rfl

theorem mk_twoCycle : mk twoCycle.{u} = quineAtom :=
  (mk_eq_decorate twoCycle).trans (decorate_twoCycle _)

/-- The loop and the two-node cycle are bisimilar: the total relation is a bisimulation. -/
theorem loop_equiv_twoCycle : loop.{u} ≈ twoCycle.{u} :=
  ⟨fun _ _ => True, fun _ b _ =>
    ⟨fun _ _ => ⟨⟨!b.down⟩, rfl, trivial⟩, fun _ _ => ⟨PUnit.unit, trivial, trivial⟩⟩, trivial⟩

/-- The loop has one node and the two-node cycle two. -/
theorem not_nonempty_loop_node_equiv : ¬ Nonempty (loop.{u}.Node ≃ twoCycle.{u}.Node) := by
  rintro ⟨e⟩
  have h : (⟨true⟩ : ULift.{u} Bool) = ⟨false⟩ :=
    e.symm.injective (Subsingleton.elim (α := PUnit) _ _)
  exact absurd (congrArg ULift.down h) Bool.noConfusion

/-- Bisimilar graphs need not be equal. -/
theorem loop_ne_twoCycle : loop.{u} ≠ twoCycle.{u} := fun h => by
  have all : ∀ a b : twoCycle.{u}.Node, a = b :=
    Eq.subst (motive := fun T : Type u => ∀ a b : T, a = b)
      (congrArg AccessiblePointedGraph.Node h) fun a b => Subsingleton.elim (α := PUnit) a b
  exact absurd (congrArg ULift.down (all ⟨true⟩ ⟨false⟩)) Bool.noConfusion

end HSet

end Mettapedia.TypeTheory.MaterialSets.Hypersets
