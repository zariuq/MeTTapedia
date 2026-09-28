import Mettapedia.TypeTheory.MaterialSets.Hypersets.AccessiblePointedGraph

/-!
# Hypersets

`HSet.{u}` is the type of accessible pointed graphs with nodes in `Type u`, modulo
bisimilarity. A hyperset `x` is a member of `mk H` when some child of the point of `H`,
re-pointed, is bisimilar to a graph of `x` (`mk_mem_mk_iff`).

* `decorate r a`: the hyperset pictured by a graph `r` at a node `a`, that is, by the subgraph
  `a` generates. Its members are the hypersets pictured at the children of `a`
  (`mem_decorate`), and bisimilar nodes picture the same hyperset
  (`decorate_eq_decorate_iff`).
* Strong extensionality: a bisimulation of the membership graph of hypersets relates only
  equal hypersets (`eq_of_isBisimulation`), so bisimilarity of hypersets is equality
  (`bisimilar_iff_eq`).
* Extensionality: hypersets with the same members are equal (`ext`).

No choice is used.

The graphs are the process presentations: an edge is evidence of membership, and a graph keeps
the shape and multiplicity of its edges. The quotient is the extensional layer, where
bisimilarity forgets both.

P. Aczel, *Non-well-founded Sets*, CSLI Lecture Notes 14, 1988. Non-well-founded trees, the
final coalgebras of polynomial functors, and their use for non-well-founded sets:
B. van den Berg and F. De Marchi, *Non-well-founded trees in categories*, Annals of Pure and
Applied Logic, 2007.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

open AccessiblePointedGraph

universe u

/-- Hypersets: accessible pointed graphs with nodes in `Type u`, modulo bisimilarity. -/
def HSet : Type (u + 1) :=
  Quotient AccessiblePointedGraph.setoid.{u}

namespace HSet

/-- The hyperset pictured by an accessible pointed graph. -/
def mk (G : AccessiblePointedGraph.{u}) : HSet.{u} :=
  Quotient.mk _ G

theorem mk_eq_mk_iff {G H : AccessiblePointedGraph.{u}} : mk G = mk H ↔ G ≈ H :=
  ⟨Quotient.exact, Quotient.sound⟩

theorem sound {G H : AccessiblePointedGraph.{u}} (h : G ≈ H) : mk G = mk H :=
  Quotient.sound h

@[elab_as_elim]
protected theorem ind {motive : HSet.{u} → Prop} (mk : ∀ G, motive (HSet.mk G)) (x : HSet.{u}) :
    motive x :=
  Quotient.ind mk x

theorem exists_mk (x : HSet.{u}) : ∃ G, mk G = x :=
  Quotient.exists_rep x

/-! ## Decorations -/

section Decoration

variable {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}

/-- The hyperset pictured by the graph `r` at the node `a`: the hyperset of the subgraph that
`a` generates. -/
def decorate (r : α → α → Prop) (a : α) : HSet.{u} :=
  mk (generated r a)

theorem decorate_eq_decorate_iff {a : α} {b : β} :
    decorate r a = decorate s b ↔ Bisimilar r s a b :=
  mk_eq_mk_iff.trans generated_equiv_generated_iff

theorem decorate_eq_of_bisimilar {a : α} {b : β} (h : Bisimilar r s a b) :
    decorate r a = decorate s b :=
  decorate_eq_decorate_iff.mpr h

theorem mk_eq_decorate (G : AccessiblePointedGraph.{u}) : mk G = decorate G.edge G.point :=
  (sound (repoint_point G)).symm

theorem mk_repoint (G : AccessiblePointedGraph.{u}) (n : G.Node) :
    mk (G.repoint n) = decorate G.edge n :=
  rfl

end Decoration

/-! ## Membership -/

theorem exists_child_iff_of_equiv {G H : AccessiblePointedGraph.{u}} (h : G ≈ H)
    (P : HSet.{u} → Prop) :
    (∃ c, G.edge G.point c ∧ P (decorate G.edge c)) ↔
      ∃ c, H.edge H.point c ∧ P (decorate H.edge c) := by
  have h' : Bisimilar G.edge H.edge G.point H.point := h
  constructor
  · rintro ⟨c, hc, hP⟩
    obtain ⟨c', hc', hb⟩ := h'.exists_child_left hc
    exact ⟨c', hc', decorate_eq_of_bisimilar hb ▸ hP⟩
  · rintro ⟨c', hc', hP⟩
    obtain ⟨c, hc, hb⟩ := h'.exists_child_right hc'
    exact ⟨c, hc, (decorate_eq_of_bisimilar hb).symm ▸ hP⟩

/-- `x ∈ y`: some child of the point of a graph of `y`, re-pointed, pictures `x`. -/
protected def Mem (y x : HSet.{u}) : Prop :=
  Quotient.liftOn y (fun H => ∃ c, H.edge H.point c ∧ decorate H.edge c = x)
    fun _ _ h => propext (exists_child_iff_of_equiv h (· = x))

instance : Membership HSet.{u} HSet.{u} :=
  ⟨HSet.Mem⟩

theorem mem_mk {x : HSet.{u}} {H : AccessiblePointedGraph.{u}} :
    x ∈ mk H ↔ ∃ c, H.edge H.point c ∧ decorate H.edge c = x :=
  Iff.rfl

/-- Membership of pictured hypersets: some child of the point, re-pointed, is bisimilar to
the member's graph. -/
theorem mk_mem_mk_iff {G H : AccessiblePointedGraph.{u}} :
    mk G ∈ mk H ↔ ∃ c, H.edge H.point c ∧ G ≈ H.repoint c :=
  exists_congr fun _ => and_congr_right fun _ =>
    mk_eq_mk_iff.trans ⟨Setoid.symm, Setoid.symm⟩

/-- The members of the hyperset pictured at `a` are the hypersets pictured at the children
of `a`. -/
theorem mem_decorate {α : Type u} {r : α → α → Prop} {a : α} {y : HSet.{u}} :
    y ∈ decorate r a ↔ ∃ b, r a b ∧ decorate r b = y := by
  change y ∈ mk (generated r a) ↔ _
  rw [mem_mk]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c.1, hc, (decorate_eq_of_bisimilar (bisimilar_generated r a c)).symm⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, .single hb⟩, hb, decorate_eq_of_bisimilar (bisimilar_generated r a _)⟩

theorem decorate_mem_decorate {α : Type u} {r : α → α → Prop} {a b : α} (h : r a b) :
    decorate r b ∈ decorate r a :=
  mem_decorate.mpr ⟨b, h, rfl⟩

/-! ## Strong extensionality -/

/-- Strong extensionality: a bisimulation of the membership graph of hypersets, whose edges
go from a hyperset to its members, relates only equal hypersets. -/
theorem eq_of_isBisimulation {R : HSet.{u} → HSet.{u} → Prop}
    (hR : IsBisimulation (fun x y : HSet.{u} => y ∈ x) (fun x y => y ∈ x) R)
    {x y : HSet.{u}} (h : R x y) : x = y := by
  induction x using HSet.ind with | mk G => ?_
  induction y using HSet.ind with | mk H => ?_
  refine sound ⟨fun n m => R (decorate G.edge n) (decorate H.edge m), ?_, ?_⟩
  · intro n m hnm
    refine ⟨fun n' hn => ?_, fun m' hm => ?_⟩
    · obtain ⟨y', hy', hR'⟩ := (hR hnm).1 _ (decorate_mem_decorate hn)
      obtain ⟨m', hm, rfl⟩ := mem_decorate.mp hy'
      exact ⟨m', hm, hR'⟩
    · obtain ⟨x', hx', hR'⟩ := (hR hnm).2 _ (decorate_mem_decorate hm)
      obtain ⟨n', hn, rfl⟩ := mem_decorate.mp hx'
      exact ⟨n', hn, hR'⟩
  · show R (decorate G.edge G.point) (decorate H.edge H.point)
    rwa [← mk_eq_decorate, ← mk_eq_decorate]

/-- Bisimilarity in the membership graph of hypersets is equality. -/
theorem bisimilar_iff_eq {x y : HSet.{u}} :
    Bisimilar (fun x y : HSet.{u} => y ∈ x) (fun x y => y ∈ x) x y ↔ x = y :=
  ⟨fun ⟨_, hR, h⟩ => eq_of_isBisimulation hR h, fun e => e ▸ Bisimilar.rfl⟩

/-- Extensionality: hypersets with the same members are equal. -/
@[ext]
theorem ext {x y : HSet.{u}} (h : ∀ z, z ∈ x ↔ z ∈ y) : x = y :=
  eq_of_isBisimulation (R := fun a b => ∀ z, z ∈ a ↔ z ∈ b)
    (fun _ _ hab => ⟨fun a' ha => ⟨a', (hab a').mp ha, fun _ => Iff.rfl⟩,
      fun b' hb => ⟨b', (hab b').mpr hb, fun _ => Iff.rfl⟩⟩) h

end HSet

end Mettapedia.TypeTheory.MaterialSets.Hypersets
