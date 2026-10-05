import Mettapedia.TypeTheory.MaterialSets.Hypersets.Presentations

/-!
# Labelled decoration from small presentations

A label reading is accompanied by an explicit accessible pointed graph for
each label. The pair encoding then has a small carrier, and its decoration
has exactly the labelled membership equation. Uniqueness is obtained by
extending any proposed solution to that same pair graph.

The graphs of labels are supplied data. The construction and its uniqueness
proof use no selection of quotient representatives. Nodes and labels lie in
`Type u`; their material readings lie in `HSet.{u} : Type (u + 1)`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet

open Relation

universe u

/-- Explicit small presentations of all values in a label reading. -/
structure PresentedLabels {β : Type u} (reading : β → HSet.{u}) : Type (u + 1) where
  graph : β → AccessiblePointedGraph.{u}
  mk_graph : ∀ b, HSet.mk (graph b) = reading b

namespace PresentedLabels

variable {α β : Type u} {ℓ : β → HSet.{u}}

/-- A family of authored graphs supplies the reading it actually pictures. -/
def ofGraphs (graphs : β → AccessiblePointedGraph.{u}) :
    PresentedLabels (fun b => HSet.mk (graphs b)) :=
  ⟨graphs, fun _ => rfl⟩

/-- The small carrier contains states, pair nodes and the supplied label graphs. -/
abbrev Nodes (p : PresentedLabels ℓ) (α : Type u) : Type u :=
  LabelCarrier (α := α) (fun b => (p.graph b).Node)

/-- A labelled transition is represented by the membership graph of its
Kuratowski pair, with the supplied label graph attached. -/
def edge (p : PresentedLabels ℓ) (r : α → β → α → Prop) :
    p.Nodes α → p.Nodes α → Prop
  | .atom a, .paired b a' => r a b a'
  | .paired b _, .single b' => b = b'
  | .paired b a', .couple b' a'' => b = b' ∧ a' = a''
  | .single b, .label b' n => ∃ h : b = b', h ▸ (p.graph b).point = n
  | .couple b _, .label b' n => ∃ h : b = b', h ▸ (p.graph b).point = n
  | .couple _ a', .atom a'' => a' = a''
  | .label b n, .label b' m => ∃ h : b = b', (p.graph b).edge n (h ▸ m)
  | _, _ => False

/-- The material value of a state in the explicit pair graph. -/
def decorate (p : PresentedLabels ℓ) (r : α → β → α → Prop) (a : α) : HSet.{u} :=
  HSet.decorate (p.edge r) (LabelCarrier.atom a)

/-- Attaching a label graph preserves the value at each of its nodes. -/
theorem decorate_label (p : PresentedLabels ℓ) (r : α → β → α → Prop)
    (b : β) (n : (p.graph b).Node) :
    HSet.decorate (p.edge r) (LabelCarrier.label b n) =
      HSet.decorate (p.graph b).edge n := by
  exact (HSet.decorate_eq_of_bisimilar (bisimilar_apply
    (r := (p.graph b).edge) (s := p.edge r)
    (f := fun m : (p.graph b).Node => LabelCarrier.label b m)
    (fun _n m hedge => ⟨rfl, hedge⟩)
    (fun _n t ht => by
      cases t with
      | label b' m =>
        rcases ht with ⟨rfl, hedge⟩
        exact ⟨m, hedge, rfl⟩
      | atom _ => cases ht
      | paired _ _ => cases ht
      | single _ => cases ht
      | couple _ _ => cases ht)
    n)).symm

/-- The singleton node pictures the singleton of the declared label reading. -/
theorem decorate_single (p : PresentedLabels ℓ) (r : α → β → α → Prop) (b : β) :
    HSet.decorate (p.edge r) (LabelCarrier.single b) = {ℓ b} := by
  ext y
  rw [HSet.mem_decorate, mem_singleton]
  constructor
  · rintro ⟨t, ht, rfl⟩
    cases t with
    | label b' n =>
      rcases ht with ⟨rfl, hn⟩
      rw [p.decorate_label, ← hn, ← HSet.mk_eq_decorate, p.mk_graph]
    | atom _ => cases ht
    | paired _ _ => cases ht
    | single _ => cases ht
    | couple _ _ => cases ht
  · intro rfl
    refine ⟨LabelCarrier.label b (p.graph b).point, ⟨rfl, rfl⟩, ?_⟩
    rw [p.decorate_label, ← HSet.mk_eq_decorate, p.mk_graph]

/-- The unordered pair node retains both the label and the target value. -/
theorem decorate_couple (p : PresentedLabels ℓ) (r : α → β → α → Prop)
    (b : β) (a' : α) :
    HSet.decorate (p.edge r) (LabelCarrier.couple b a') =
      {ℓ b, p.decorate r a'} := by
  ext y
  rw [HSet.mem_decorate, mem_pair]
  constructor
  · rintro ⟨t, ht, rfl⟩
    cases t with
    | label b' n =>
      rcases ht with ⟨rfl, hn⟩
      exact Or.inl (by rw [p.decorate_label, ← hn, ← HSet.mk_eq_decorate, p.mk_graph])
    | atom a'' =>
      cases ht
      exact Or.inr rfl
    | paired _ _ => cases ht
    | single _ => cases ht
    | couple _ _ => cases ht
  · rintro (rfl | rfl)
    · refine ⟨LabelCarrier.label b (p.graph b).point, ⟨rfl, rfl⟩, ?_⟩
      rw [p.decorate_label, ← HSet.mk_eq_decorate, p.mk_graph]
    · exact ⟨LabelCarrier.atom a', rfl, rfl⟩

/-- The pair node pictures the actual Kuratowski pair. -/
theorem decorate_paired (p : PresentedLabels ℓ) (r : α → β → α → Prop)
    (b : β) (a' : α) :
    HSet.decorate (p.edge r) (LabelCarrier.paired b a') =
      kpair (ℓ b) (p.decorate r a') := by
  ext y
  rw [HSet.mem_decorate, mem_kpair, decorate]
  constructor
  · rintro ⟨t, ht, rfl⟩
    cases t with
    | single b' =>
      cases ht
      exact Or.inl (p.decorate_single r b)
    | couple b' a'' =>
      rcases ht with ⟨rfl, rfl⟩
      exact Or.inr (p.decorate_couple r b a')
    | atom _ => cases ht
    | paired _ _ => cases ht
    | label _ _ => cases ht
  · rintro (rfl | rfl)
    · exact ⟨LabelCarrier.single b, rfl, p.decorate_single r b⟩
    · exact ⟨LabelCarrier.couple b a', ⟨rfl, rfl⟩, p.decorate_couple r b a'⟩

/-- Exact material membership retains the read label and decorated successor. -/
theorem mem_decorate (p : PresentedLabels ℓ) {r : α → β → α → Prop}
    {a : α} {y : HSet.{u}} :
    y ∈ p.decorate r a ↔
      ∃ b a', r a b a' ∧ y = kpair (ℓ b) (p.decorate r a') := by
  rw [decorate, HSet.mem_decorate]
  constructor
  · rintro ⟨t, ht, rfl⟩
    cases t with
    | paired b a' => exact ⟨b, a', ht, p.decorate_paired r b a'⟩
    | atom _ => cases ht
    | single _ => cases ht
    | couple _ _ => cases ht
    | label _ _ => cases ht
  · rintro ⟨b, a', hr, rfl⟩
    exact ⟨LabelCarrier.paired b a', hr, p.decorate_paired r b a'⟩

theorem isLabelledDecoration (p : PresentedLabels ℓ) (r : α → β → α → Prop) :
    IsLabelledDecoration r ℓ (p.decorate r) :=
  fun _ _ => p.mem_decorate

/-- A proposed labelled solution extends to every auxiliary node of the pair graph. -/
def extend (p : PresentedLabels ℓ) (d : α → HSet.{u}) : p.Nodes α → HSet.{u}
  | .atom a => d a
  | .paired b a' => kpair (ℓ b) (d a')
  | .single b => {ℓ b}
  | .couple b a' => {ℓ b, d a'}
  | .label b n => HSet.decorate (p.graph b).edge n

/-- The extended solution satisfies the unlabelled decoration equation. -/
theorem extend_isDecoration (p : PresentedLabels ℓ) {r : α → β → α → Prop}
    {d : α → HSet.{u}} (hd : IsLabelledDecoration r ℓ d) :
    IsDecoration (p.edge r) (p.extend d) := by
  intro n y
  cases n with
  | atom a =>
    rw [extend, hd a y]
    constructor
    · rintro ⟨b, a', hr, rfl⟩
      exact ⟨LabelCarrier.paired b a', hr, rfl⟩
    · rintro ⟨t, ht, he⟩
      cases t with
      | paired b a' => exact ⟨b, a', ht, he.symm⟩
      | atom _ => cases ht
      | single _ => cases ht
      | couple _ _ => cases ht
      | label _ _ => cases ht
  | paired b a' =>
    rw [extend, mem_kpair]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨LabelCarrier.single b, rfl, rfl⟩
      · exact ⟨LabelCarrier.couple b a', ⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨t, ht, he⟩
      cases t with
      | single b' =>
        cases ht
        exact Or.inl he.symm
      | couple b' a'' =>
        rcases ht with ⟨rfl, rfl⟩
        exact Or.inr he.symm
      | atom _ => cases ht
      | paired _ _ => cases ht
      | label _ _ => cases ht
  | single b =>
    rw [extend, mem_singleton]
    constructor
    · rintro rfl
      refine ⟨LabelCarrier.label b (p.graph b).point, ⟨rfl, rfl⟩, ?_⟩
      rw [extend, ← HSet.mk_eq_decorate, p.mk_graph]
    · rintro ⟨t, ht, he⟩
      cases t with
      | label b' n =>
        rcases ht with ⟨rfl, hn⟩
        rw [← he, extend, ← hn, ← HSet.mk_eq_decorate, p.mk_graph]
      | atom _ => cases ht
      | paired _ _ => cases ht
      | single _ => cases ht
      | couple _ _ => cases ht
  | couple b a' =>
    rw [extend, mem_pair]
    constructor
    · rintro (rfl | rfl)
      · refine ⟨LabelCarrier.label b (p.graph b).point, ⟨rfl, rfl⟩, ?_⟩
        rw [extend, ← HSet.mk_eq_decorate, p.mk_graph]
      · exact ⟨LabelCarrier.atom a', rfl, rfl⟩
    · rintro ⟨t, ht, he⟩
      cases t with
      | label b' n =>
        rcases ht with ⟨rfl, hn⟩
        exact Or.inl (by rw [← he, extend, ← hn, ← HSet.mk_eq_decorate, p.mk_graph])
      | atom a'' =>
        cases ht
        exact Or.inr he.symm
      | paired _ _ => cases ht
      | single _ => cases ht
      | couple _ _ => cases ht
  | label b n =>
    rw [extend, HSet.mem_decorate]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨LabelCarrier.label b m, ⟨rfl, hm⟩, rfl⟩
    · rintro ⟨t, ht, he⟩
      cases t with
      | label b' m =>
        rcases ht with ⟨rfl, hm⟩
        exact ⟨m, hm, he⟩
      | atom _ => cases ht
      | paired _ _ => cases ht
      | single _ => cases ht
      | couple _ _ => cases ht

/-- Uniqueness follows from unlabelled anti-foundation on the supplied pair graph. -/
theorem unique (p : PresentedLabels ℓ) {r : α → β → α → Prop} {d : α → HSet.{u}}
    (hd : IsLabelledDecoration r ℓ d) : d = p.decorate r := by
  funext a
  exact congrFun (p.extend_isDecoration hd).eq_decorate (LabelCarrier.atom a)

theorem existsUnique (p : PresentedLabels ℓ) (r : α → β → α → Prop) :
    ∃! d, IsLabelledDecoration r ℓ d :=
  ⟨p.decorate r, p.isLabelledDecoration r, fun _ hd => p.unique hd⟩

/-- Different small presentations of the same reading have the same state values. -/
theorem presentation_independent (p q : PresentedLabels ℓ) (r : α → β → α → Prop) :
    p.decorate r = q.decorate r :=
  q.unique (p.isLabelledDecoration r)

/-- Only readings of labels on actual transitions affect a decoration. -/
theorem reading_independent {ℓ' : β → HSet.{u}}
    (p : PresentedLabels ℓ) (q : PresentedLabels ℓ') (r : α → β → α → Prop)
    (agree : ∀ a b a', r a b a' → ℓ b = ℓ' b) : p.decorate r = q.decorate r := by
  apply q.unique
  intro a y
  rw [p.mem_decorate]
  constructor
  · rintro ⟨b, a', hr, he⟩
    exact ⟨b, a', hr, by rw [← agree a b a' hr]; exact he⟩
  · rintro ⟨b, a', hr, he⟩
    exact ⟨b, a', hr, by rw [agree a b a' hr]; exact he⟩

end PresentedLabels

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet
