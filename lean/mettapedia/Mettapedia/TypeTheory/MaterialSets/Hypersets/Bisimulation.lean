import Mathlib.Logic.Relation

/-!
# Bisimulations of graphs

A graph on a type `α` is a relation `r : α → α → Prop`, where `r a a'` says that `a'` is a
child of `a`. A bisimulation between a graph `r` on `α` and a graph `s` on `β` relates nodes
whose children are related in both directions. Two nodes are bisimilar when some
bisimulation relates them.

* `IsBisimulation.eq`, `IsBisimulation.flip` and `IsBisimulation.comp`: equality is a
  bisimulation, and bisimulations are closed under converse and composition;
* `Bisimilar.refl`, `Bisimilar.symm` and `Bisimilar.trans`: bisimilarity is an equivalence,
  across graphs on different types;
* `isBisimulation_bisimilar`: bisimilarity is itself a bisimulation, the largest one;
* `isBisimulation_graph`: the graph of a bounded morphism, a map that preserves edges and
  lifts every edge out of an image, is a bisimulation;
* `not_bisimilar_of_child`: a node with a child is bisimilar to no node without children.

Bisimilarity is the equality of non-well-founded sets: P. Aczel, *Non-well-founded Sets*,
CSLI Lecture Notes 14, 1988; J. Barwise and L. Moss, *Vicious Circles*, CSLI Lecture Notes 60,
1996.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- `R` is a bisimulation between the graph `r` on `α` and the graph `s` on `β`: when
`R a b`, each child of `a` is related to some child of `b`, and each child of `b` to some
child of `a`. -/
def IsBisimulation (r : α → α → Prop) (s : β → β → Prop) (R : α → β → Prop) : Prop :=
  ∀ ⦃a b⦄, R a b →
    (∀ a', r a a' → ∃ b', s b b' ∧ R a' b') ∧ (∀ b', s b b' → ∃ a', r a a' ∧ R a' b')

/-- Two nodes are bisimilar when some bisimulation relates them. -/
def Bisimilar (r : α → α → Prop) (s : β → β → Prop) (a : α) (b : β) : Prop :=
  ∃ R : α → β → Prop, IsBisimulation r s R ∧ R a b

variable {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

namespace IsBisimulation

/-- Equality is a bisimulation of a graph with itself. -/
protected theorem eq : IsBisimulation r r Eq := by
  rintro a _ rfl
  exact ⟨fun a' h => ⟨a', h, rfl⟩, fun a' h => ⟨a', h, rfl⟩⟩

/-- The converse of a bisimulation is a bisimulation. -/
protected theorem flip {R : α → β → Prop} (hR : IsBisimulation r s R) :
    IsBisimulation s r (flip R) :=
  fun _ _ h => ⟨(hR h).2, (hR h).1⟩

/-- The composite of two bisimulations is a bisimulation. -/
protected theorem comp {R : α → β → Prop} {S : β → γ → Prop} (hR : IsBisimulation r s R)
    (hS : IsBisimulation s t S) : IsBisimulation r t (Relation.Comp R S) := by
  rintro a c ⟨b, hab, hbc⟩
  refine ⟨fun a' ha => ?_, fun c' hc => ?_⟩
  · obtain ⟨b', hb, hab'⟩ := (hR hab).1 a' ha
    obtain ⟨c', hc, hbc'⟩ := (hS hbc).1 b' hb
    exact ⟨c', hc, b', hab', hbc'⟩
  · obtain ⟨b', hb, hbc'⟩ := (hS hbc).2 c' hc
    obtain ⟨a', ha, hab'⟩ := (hR hab).2 b' hb
    exact ⟨a', ha, b', hab', hbc'⟩

/-- Nodes related by a bisimulation are bisimilar. -/
theorem bisimilar {R : α → β → Prop} (hR : IsBisimulation r s R) {a : α} {b : β}
    (h : R a b) : Bisimilar r s a b :=
  ⟨R, hR, h⟩

end IsBisimulation

/-- Bisimilarity is a bisimulation; it contains every bisimulation. -/
theorem isBisimulation_bisimilar : IsBisimulation r s (Bisimilar r s) := by
  rintro a b ⟨R, hR, hab⟩
  refine ⟨fun a' ha => ?_, fun b' hb => ?_⟩
  · obtain ⟨b', hb, h⟩ := (hR hab).1 a' ha
    exact ⟨b', hb, R, hR, h⟩
  · obtain ⟨a', ha, h⟩ := (hR hab).2 b' hb
    exact ⟨a', ha, R, hR, h⟩

namespace Bisimilar

protected theorem refl (a : α) : Bisimilar r r a a :=
  IsBisimulation.eq.bisimilar rfl

protected theorem rfl {a : α} : Bisimilar r r a a :=
  Bisimilar.refl a

protected theorem symm {a : α} {b : β} : Bisimilar r s a b → Bisimilar s r b a
  | ⟨_, hR, h⟩ => hR.flip.bisimilar h

protected theorem trans {a : α} {b : β} {c : γ} :
    Bisimilar r s a b → Bisimilar s t b c → Bisimilar r t a c
  | ⟨_, hR, hab⟩, ⟨_, hS, hbc⟩ => (hR.comp hS).bisimilar ⟨b, hab, hbc⟩

theorem exists_child_left {a : α} {b : β} (h : Bisimilar r s a b) {a' : α} (ha : r a a') :
    ∃ b', s b b' ∧ Bisimilar r s a' b' :=
  (isBisimulation_bisimilar h).1 a' ha

theorem exists_child_right {a : α} {b : β} (h : Bisimilar r s a b) {b' : β} (hb : s b b') :
    ∃ a', r a a' ∧ Bisimilar r s a' b' :=
  (isBisimulation_bisimilar h).2 b' hb

end Bisimilar

/-- The graph of a bounded morphism, a map that preserves edges and lifts every edge out of
an image, is a bisimulation. -/
theorem isBisimulation_graph {f : α → β} (map : ∀ a a', r a a' → s (f a) (f a'))
    (lift : ∀ a b', s (f a) b' → ∃ a', r a a' ∧ f a' = b') :
    IsBisimulation r s fun a b => f a = b := by
  rintro a _ rfl
  exact ⟨fun a' h => ⟨f a', map a a' h, rfl⟩, lift a⟩

/-- Along a bounded morphism, every node is bisimilar to its image. -/
theorem bisimilar_apply {f : α → β} (map : ∀ a a', r a a' → s (f a) (f a'))
    (lift : ∀ a b', s (f a) b' → ∃ a', r a a' ∧ f a' = b') (a : α) :
    Bisimilar r s a (f a) :=
  (isBisimulation_graph map lift).bisimilar rfl

/-- A node with a child is bisimilar to no node without children. -/
theorem not_bisimilar_of_child {a a' : α} {b : β} (ha : r a a') (hb : ∀ b', ¬ s b b') :
    ¬ Bisimilar r s a b := fun h =>
  let ⟨b', hb', _⟩ := h.exists_child_left ha
  hb b' hb'

end Mettapedia.TypeTheory.MaterialSets.Hypersets
