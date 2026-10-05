import Mettapedia.GSLT.Logic.QuotientObservers
import Mettapedia.TypeTheory.MaterialSets.Hypersets.Bisimulation

/-!
# One scheme for several anti-foundation axioms

A graph is a carrier and a child relation: `edge a b` means that `b` is a member of the
picture at `a`. Aczel compares the anti-foundation axioms by the equivalence they use to
identify nodes. The equivalence has to be a bisimulation, so that the quotient still has a
well-defined set of members. That is the relation he calls regular. It is not the later use
of "regular" for an Aczel–Mendler bisimulation in a regular category; that notion is not
used here.

For such a relation `≡`, a canonical decoration solves the membership equations and sends
two nodes to the same set exactly when `≡` relates them. Coinduction is the forward half:
related nodes denote the same set. The solution lemma is the same map, read as the unique
canonical solution of the system. A target that is strongly extensional has at most one
decoration of any graph, and that decoration respects every regular identification.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.AntiFoundation

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.GSLT.QuotientObservers

universe u

variable {α V : Type u}

/-- `edge a b` means that `b` is a child of `a`. -/
abbrev Edge (α : Type u) := α → α → Prop

/-- Membership in a carrier of pictures. `mem m s` means that `m` is a member of `s`. -/
abbrev MemRel (V : Type u) := V → V → Prop

/-- Membership read as a child relation. The second argument is the member. -/
abbrev memChild {V : Type u} (mem : MemRel V) : V → V → Prop :=
  fun parent child => mem child parent

/-- The members of `d a` are the values of `d` at the children of `a`. -/
def IsDecoration (edge : Edge α) (mem : MemRel V) (d : α → V) : Prop :=
  ∀ a y, mem y (d a) ↔ ∃ b, edge a b ∧ y = d b

/-- A solution of the membership equations of a graph is a decoration. -/
abbrev IsSolution (edge : Edge α) (mem : MemRel V) (d : α → V) : Prop :=
  IsDecoration edge mem d

/-- A set equal to the singleton of itself. -/
def IsQuine (mem : MemRel V) (q : V) : Prop :=
  ∀ y, mem y q ↔ y = q

/-- Every bisimulation of `child` relates only equal elements. The second argument of
`child` is the child. For a membership, pass `memChild`. -/
def StronglyExtensional (child : MemRel V) : Prop :=
  ∀ R, IsBisimulation child child R → ∀ x y, R x y → x = y

/-- Distinct nodes have distinct sets of children. -/
def WeaklyExtensional (edge : Edge α) : Prop :=
  ∀ a b, (∀ c, edge a c ↔ edge b c) → a = b

/-- An equivalence that is a bisimulation. Quotienting by it leaves membership well-defined. -/
structure RegularIdentification (edge : Edge α) where
  /-- The identification. -/
  ident : α → α → Prop
  /-- It is an equivalence. -/
  equiv : Equivalence ident
  /-- It is a bisimulation of `edge` with itself. -/
  bisim : IsBisimulation edge edge ident

/-- Bisimilarity is a regular identification, and it contains every other one. -/
def RegularIdentification.bisimilarity (edge : Edge α) : RegularIdentification edge where
  ident := Bisimilar edge edge
  equiv := ⟨Bisimilar.refl, fun {_ _} h => h.symm, fun {_ _ _} h k => h.trans k⟩
  bisim := isBisimulation_bisimilar

theorem RegularIdentification.toBisimilar {edge : Edge α} (R : RegularIdentification edge)
    {a b : α} (h : R.ident a b) : Bisimilar edge edge a b :=
  R.bisim.bisimilar h

/-- A constant map at a Quine atom decorates every graph in which each node has a child. -/
theorem isDecoration_const_quine {edge : Edge α} {mem : MemRel V} {q : V}
    (children : ∀ a, ∃ b, edge a b) (quine : IsQuine mem q) :
    IsDecoration edge mem (fun _ => q) := by
  intro a y
  constructor
  · intro hy
    obtain ⟨b, hb⟩ := children a
    exact ⟨b, hb, (quine y).mp hy⟩
  · intro ⟨_, _, hy⟩
    exact (quine y).mpr hy

/-- The loop's decorations are exactly the constant maps at a Quine atom. -/
theorem loop_decoration_iff {edge : Edge α} {mem : MemRel V} {a0 : α}
    (only : ∀ a, a = a0) (child : edge a0 a0) (d : α → V) :
    IsDecoration edge mem d ↔ IsQuine mem (d a0) := by
  constructor
  · intro hd y
    constructor
    · intro hy
      obtain ⟨b, _, eq⟩ := (hd a0 y).mp hy
      exact eq.trans (congrArg d (only b))
    · intro hy
      exact (hd a0 y).mpr ⟨a0, child, hy⟩
  · intro hq a y
    cases only a
    constructor
    · intro hy
      exact ⟨a0, child, (hq y).mp hy⟩
    · intro ⟨b, _, eq⟩
      exact (hq y).mpr (eq.trans (congrArg d (only b)))

/-- A canonical decoration solves the equations and uses `≡` as its kernel. -/
structure CanonicalDecoration (edge : Edge α) (ident : α → α → Prop) (mem : MemRel V)
    (d : α → V) : Prop where
  /-- It solves the membership equations. -/
  decoration : IsDecoration edge mem d
  /-- Related nodes denote the same set. -/
  respects : Respects ident d
  /-- Nodes that denote the same set were already related. -/
  reflects : ∀ a b, d a = d b → ident a b

/-- The axiom for `≡`: every graph has one canonical decoration, unique pointwise. -/
def CanonicalAxiom (edge : Edge α) (ident : α → α → Prop) (mem : MemRel V) : Prop :=
  ∃ d, CanonicalDecoration edge ident mem d ∧
    ∀ d', CanonicalDecoration edge ident mem d' → ∀ a, d' a = d a

/-- Coinduction: a canonical decoration sends related nodes to the same set. -/
theorem CanonicalDecoration.coinduction {edge : Edge α} {ident : α → α → Prop}
    {mem : MemRel V} {d : α → V} (h : CanonicalDecoration edge ident mem d) :
    Respects ident d :=
  h.respects

/-- The solution lemma: the canonical decoration is the unique canonical solution. -/
theorem solution_lemma {edge : Edge α} {ident : α → α → Prop} {mem : MemRel V}
    (canon : CanonicalAxiom edge ident mem) :
    ∃ d, IsSolution edge mem d ∧ Respects ident d ∧
      (∀ a b, d a = d b → ident a b) ∧
      ∀ d', IsSolution edge mem d' → Respects ident d' →
        (∀ a b, d' a = d' b → ident a b) → ∀ a, d' a = d a := by
  obtain ⟨d, hd, unique⟩ := canon
  exact ⟨d, hd.decoration, hd.respects, hd.reflects, fun d' decoration respects reflects a =>
    unique d' ⟨decoration, respects, reflects⟩ a⟩

/-- Into a strongly extensional membership, bisimilar nodes receive the same value. -/
theorem coinduction_of_strong {edge : Edge α} {mem : MemRel V} {d : α → V}
    (hd : IsDecoration edge mem d) (strong : StronglyExtensional (memChild mem)) {a b : α}
    (h : Bisimilar edge edge a b) : d a = d b := by
  let child := memChild mem
  let R : V → V → Prop := fun x y => ∃ a b, d a = x ∧ d b = y ∧ Bisimilar edge edge a b
  have hR : IsBisimulation child child R := by
    intro x y ⟨a, b, hxa, hyb, hab⟩
    subst hxa
    subst hyb
    constructor
    · intro x' hx
      obtain ⟨a', ha, rfl⟩ := (hd a x').mp hx
      obtain ⟨b', hb, hab'⟩ := hab.exists_child_left ha
      exact ⟨d b', (hd b (d b')).mpr ⟨b', hb, rfl⟩, a', b', rfl, rfl, hab'⟩
    · intro y' hy
      obtain ⟨b', hb, rfl⟩ := (hd b y').mp hy
      obtain ⟨a', ha, hab'⟩ := hab.exists_child_right hb
      exact ⟨d a', (hd a (d a')).mpr ⟨a', ha, rfl⟩, a', b', rfl, rfl, hab'⟩
  exact strong R hR (d a) (d b) ⟨a, b, rfl, rfl, h⟩

/-- Into a strongly extensional membership, a graph has at most one decoration. -/
theorem unique_decoration_of_strong {edge : Edge α} {mem : MemRel V} {d d' : α → V}
    (hd : IsDecoration edge mem d) (hd' : IsDecoration edge mem d')
    (strong : StronglyExtensional (memChild mem)) (a : α) : d a = d' a := by
  let child := memChild mem
  let R : V → V → Prop := fun x y => ∃ a, d a = x ∧ d' a = y
  have hR : IsBisimulation child child R := by
    intro x y ⟨a, hxa, hya⟩
    subst hxa
    subst hya
    constructor
    · intro x' hx
      obtain ⟨b, hb, rfl⟩ := (hd a x').mp hx
      exact ⟨d' b, (hd' a (d' b)).mpr ⟨b, hb, rfl⟩, b, rfl, rfl⟩
    · intro y' hy
      obtain ⟨b, hb, rfl⟩ := (hd' a y').mp hy
      exact ⟨d b, (hd a (d b)).mpr ⟨b, hb, rfl⟩, b, rfl, rfl⟩
  exact strong R hR (d a) (d' a) ⟨a, rfl, rfl⟩

/-- A decoration into a strongly extensional membership respects every regular identification. -/
theorem respects_regular_of_strong {edge : Edge α} {mem : MemRel V} {d : α → V}
    (R : RegularIdentification edge) (hd : IsDecoration edge mem d)
    (strong : StronglyExtensional (memChild mem)) : Respects R.ident d :=
  fun _ _ h => coinduction_of_strong hd strong (R.toBisimilar h)

/-- The kernel of any decoration is a bisimulation. Equal values were already bisimilar. -/
theorem decoration_kernel_bisim {edge : Edge α} {mem : MemRel V} {d : α → V}
    (hd : IsDecoration edge mem d) {a b : α} (h : d a = d b) :
    Bisimilar edge edge a b := by
  let R : α → α → Prop := fun x y => d x = d y
  have hR : IsBisimulation edge edge R := by
    intro x y hxy
    constructor
    · intro x' hx
      have memx : mem (d x') (d x) := (hd x (d x')).mpr ⟨x', hx, rfl⟩
      obtain ⟨y', hy, he⟩ := (hd y (d x')).mp (hxy ▸ memx)
      exact ⟨y', hy, he⟩
    · intro y' hy
      have memy : mem (d y') (d y) := (hd y (d y')).mpr ⟨y', hy, rfl⟩
      obtain ⟨x', hx, he⟩ := (hd x (d y')).mp (hxy.symm ▸ memy)
      exact ⟨x', hx, he.symm⟩
  exact hR.bisimilar h

end Mettapedia.SetTheory.AntiFoundation
