import Mathlib.Data.List.Forall2
import Mathlib.Data.Fintype.Prod
import Mettapedia.Machines.PeTTaLeafEquality
import Mettapedia.TypeTheory.MaterialSets.Hypersets.Bisimulation

/-!
# Ordered term graphs and finite observations

A rational term has a finite graph presentation, but its observable unfolding
can be infinite. Constructor names and argument positions are retained here;
graph sharing and the number of nodes used to present a cycle are not part of
term equality. This differs from the unlabelled membership graphs used for
hypersets, which forget both argument order and repeated edges.

`bisimilar_iff_observe_eq` proves that the relational graph definition agrees
with every finite unfolding. It holds without assuming that the presentation
is finite, and thus applies in particular to finite runtime graphs. The
examples distinguish this equality from graph identity and from unlabelled
graph bisimilarity. `checkCertificate` checks a finite candidate relation using
only labels, child lists, and pair membership. Accepted certificates are sound,
and finite graphs have such a certificate exactly when their roots are
bisimilar. Certificate generation and its efficiency are separate obligations.

Labels are a parameter: a language must separately specify variable identity,
numeric leaf comparison, and the distinction between atoms and zero-argument
compounds.

Bisimilarity is an equivalence (`Bisimilar.refl`, `.symm`, `.trans`). A
transport (`IsTransport`) copies a graph into another presentation, each node
to one node with its label and the images of its ordered children, as a copy
across a foreign boundary with node memoization does; a transported node is
the term it was copied from (`IsTransport.bisimilar`), and transports compose,
so a round trip returns the same term (`IsTransport.round_trip`). A boundary
that converts labels is a transport of the relabelled graph (`Graph.mapLabel`).
A hash of a bounded unfolding gives equal terms equal hashes and needs no
cycle detection (`observe_hash_compatible`).

`PeTTaEq` is PeTTa's `==` on term graphs: bisimilarity once numeric leaves are
replaced by their value class (`PeTTaLeafEquality.cls`), atoms, variables and
compound names kept. On two leaves it is exactly the runtime's leaf decision
(`pettaClass_number_eq_iff`). The examples are the rational terms of the
reference's `numeric_equality` test: a cycle equals itself with a NaN leaf, an
integer leaf and a float leaf of the same value give equal cycles, a cycle
equals its unrolling, and unequal leaves or zero-argument compounds of
different names give unequal ones.

The file does not verify a runtime's conversion code, unification, or garbage
collection.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RationalTermGraph

universe u v w x

/-- Ordered children preserve constructor arity, argument position, and repeated
arguments. A finite node type gives a finite presentation of a rational term. -/
structure Graph (Node : Type u) (Label : Type v) where
  label : Node → Label
  children : Node → List Node

/-- The observation at the depth boundary reveals nothing further. -/
inductive Observation (Label : Type v) where
  | cut
  | node (label : Label) (children : List (Observation Label))

/-- Finite unfolding, including the complete ordered child list at each revealed
node. This terminates even for a cyclic graph. -/
def observe {Node : Type u} {Label : Type v} (g : Graph Node Label) :
    Nat → Node → Observation Label
  | 0, _ => .cut
  | depth + 1, node =>
      .node (g.label node) ((g.children node).map (observe g depth))

/-- A graph bisimulation compares corresponding argument positions. -/
def IsBisimulation {A : Type u} {B : Type w} {Label : Type v}
    (g : Graph A Label) (h : Graph B Label) (R : A → B → Prop) : Prop :=
  ∀ ⦃a b⦄, R a b → g.label a = h.label b ∧
    List.Forall₂ R (g.children a) (h.children b)

/-- Equality by ordered unfolding, independent of graph presentation. -/
def Bisimilar {A : Type u} {B : Type w} {Label : Type v}
    (g : Graph A Label) (h : Graph B Label) (a : A) (b : B) : Prop :=
  ∃ R, IsBisimulation g h R ∧ R a b

private theorem forall₂_iff_map_eq {A : Type u} {B : Type w} {C : Type v}
    (f : A → C) (g : B → C) (xs : List A) (ys : List B) :
    List.Forall₂ (fun x y => f x = g y) xs ys ↔ xs.map f = ys.map g := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp
  | cons x xs ih =>
      cases ys with
      | nil => simp
      | cons y ys => simp [List.forall₂_cons, ih]

private theorem forall₂_forall {A : Type u} {B : Type w}
    (R : Nat → A → B → Prop) (xs : List A) (ys : List B) :
    (∀ depth, List.Forall₂ (R depth) xs ys) ↔
      List.Forall₂ (fun x y => ∀ depth, R depth x y) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp
  | cons x xs ih =>
      cases ys with
      | nil => simp
      | cons y ys => simp [List.forall₂_cons, forall_and, ih]

/-- A bisimulation certifies equality at every finite observation depth. -/
theorem IsBisimulation.observe_eq {A : Type u} {B : Type w} {Label : Type v}
    {g : Graph A Label} {h : Graph B Label} {R : A → B → Prop}
    (hR : IsBisimulation g h R) {a b} (hab : R a b) (depth : Nat) :
    observe g depth a = observe h depth b := by
  induction depth generalizing a b with
  | zero => rfl
  | succ depth ih =>
      obtain ⟨hl, hc⟩ := hR hab
      simp only [observe, Observation.node.injEq, hl, true_and]
      apply (forall₂_iff_map_eq _ _ _ _).mp
      exact hc.imp fun _ _ hxy => ih hxy

/-- Agreement at every finite depth itself supplies a bisimulation. -/
theorem isBisimulation_observe_eq {A : Type u} {B : Type w} {Label : Type v}
    (g : Graph A Label) (h : Graph B Label) :
    IsBisimulation g h (fun a b => ∀ depth, observe g depth a = observe h depth b) := by
  intro a b hab
  have layer (depth : Nat) := Observation.node.inj (hab (depth + 1))
  refine ⟨(layer 0).1, ?_⟩
  apply (forall₂_forall _ _ _).mp
  intro depth
  exact (forall₂_iff_map_eq _ _ _ _).mpr (layer depth).2

/-- The graph relation and independently defined finite unfoldings characterize
the same equality, including on cyclic presentations. -/
theorem bisimilar_iff_observe_eq {A : Type u} {B : Type w} {Label : Type v}
    {g : Graph A Label} {h : Graph B Label} {a b} :
    Bisimilar g h a b ↔ ∀ depth, observe g depth a = observe h depth b := by
  constructor
  · rintro ⟨R, hR, hab⟩ depth
    exact hR.observe_eq hab depth
  · intro hab
    exact ⟨_, isBisimulation_observe_eq g h, hab⟩

/-- A finite distinguishing observation refutes bisimilarity. -/
theorem not_bisimilar_of_observe_ne {A : Type u} {B : Type w} {Label : Type v}
    {g : Graph A Label} {h : Graph B Label} {a b depth}
    (hne : observe g depth a ≠ observe h depth b) : ¬ Bisimilar g h a b := by
  intro hab
  exact hne (bisimilar_iff_observe_eq.mp hab depth)

section Certificates

variable {A : Type u} {B : Type w} {Label : Type v}
variable [DecidableEq A] [DecidableEq B] [DecidableEq Label]

/-- Check corresponding child positions against a supplied finite relation.
Unequal arities fail; a repeated child must satisfy each occurrence separately. -/
def checkChildren (pairs : List (A × B)) : List A → List B → Bool
  | [], [] => true
  | a :: as, b :: bs => decide ((a, b) ∈ pairs) && checkChildren pairs as bs
  | _, _ => false

theorem checkChildren_eq_true_iff (pairs : List (A × B)) (xs : List A) (ys : List B) :
    checkChildren pairs xs ys = true ↔
      List.Forall₂ (fun a b => (a, b) ∈ pairs) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [checkChildren]
  | cons x xs ih =>
      cases ys with
      | nil => simp [checkChildren]
      | cons y ys => simp [checkChildren, List.forall₂_cons, ih]

/-- A certificate must include the requested root pair. Every listed pair is
checked independently for equal labels and related corresponding children.
The checker traverses finite lists; it never recursively unfolds the graph. -/
def checkCertificate (g : Graph A Label) (h : Graph B Label)
    (pairs : List (A × B)) (a : A) (b : B) : Bool :=
  decide ((a, b) ∈ pairs) && pairs.all (fun p =>
    decide (g.label p.1 = h.label p.2) &&
      checkChildren pairs (g.children p.1) (h.children p.2))

theorem checkCertificate_eq_true_iff (g : Graph A Label) (h : Graph B Label)
    (pairs : List (A × B)) (a : A) (b : B) :
    checkCertificate g h pairs a b = true ↔
      (a, b) ∈ pairs ∧ IsBisimulation g h (fun x y => (x, y) ∈ pairs) := by
  simp only [checkCertificate, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    checkChildren_eq_true_iff, IsBisimulation]
  constructor
  · rintro ⟨hab, hall⟩
    exact ⟨hab, fun x y hxy => hall (x, y) hxy⟩
  · rintro ⟨hab, hall⟩
    exact ⟨hab, fun p hp => hall hp⟩

/-- A successful finite certificate certifies the semantic graph equality. -/
theorem checkCertificate_sound {g : Graph A Label} {h : Graph B Label}
    {pairs : List (A × B)} {a : A} {b : B}
    (hcheck : checkCertificate g h pairs a b = true) : Bisimilar g h a b := by
  obtain ⟨hab, hall⟩ := (checkCertificate_eq_true_iff g h pairs a b).mp hcheck
  exact ⟨_, hall, hab⟩

/-- For finite node types, every bisimilar root pair has a finite certificate.
This existence proof enumerates the witnessing relation; it does not claim an
efficient algorithm for discovering that relation. -/
theorem exists_certificate_iff_bisimilar [Fintype A] [Fintype B]
    (g : Graph A Label) (h : Graph B Label) (a : A) (b : B) :
    (∃ pairs, checkCertificate g h pairs a b = true) ↔ Bisimilar g h a b := by
  constructor
  · rintro ⟨pairs, hcheck⟩
    exact checkCertificate_sound hcheck
  · rintro ⟨R, hR, hab⟩
    classical
    let pairs := (Finset.univ.filter (fun p : A × B => R p.1 p.2)).toList
    have mem_iff (x : A) (y : B) : (x, y) ∈ pairs ↔ R x y := by
      simp [pairs]
    refine ⟨pairs, (checkCertificate_eq_true_iff g h pairs a b).mpr
      ⟨(mem_iff a b).mpr hab, ?_⟩⟩
    intro x y hxy
    obtain ⟨hl, hc⟩ := hR ((mem_iff x y).mp hxy)
    exact ⟨hl, hc.imp fun x' y' hxy' => (mem_iff x' y').mpr hxy'⟩

end Certificates

section Equivalence

variable {A : Type u} {B : Type w} {C : Type x} {Label : Type v}

theorem Bisimilar.refl (g : Graph A Label) (a : A) : Bisimilar g g a a :=
  bisimilar_iff_observe_eq.mpr fun _ => rfl

theorem Bisimilar.symm {g : Graph A Label} {h : Graph B Label} {a : A} {b : B}
    (hab : Bisimilar g h a b) : Bisimilar h g b a :=
  bisimilar_iff_observe_eq.mpr fun depth =>
    (bisimilar_iff_observe_eq.mp hab depth).symm

theorem Bisimilar.trans {g : Graph A Label} {h : Graph B Label} {k : Graph C Label}
    {a : A} {b : B} {c : C} (hab : Bisimilar g h a b) (hbc : Bisimilar h k b c) :
    Bisimilar g k a c :=
  bisimilar_iff_observe_eq.mpr fun depth =>
    (bisimilar_iff_observe_eq.mp hab depth).trans (bisimilar_iff_observe_eq.mp hbc depth)

/-- A hash of a bounded unfolding gives bisimilar nodes equal hashes: it reads
finitely many nodes, so it never loops on a cycle. -/
theorem observe_hash_compatible {H : Type x} (hash : Observation Label → H)
    (depth : Nat) {g : Graph A Label} {h : Graph B Label} {a : A} {b : B}
    (hab : Bisimilar g h a b) : hash (observe g depth a) = hash (observe h depth b) := by
  rw [bisimilar_iff_observe_eq.mp hab depth]

end Equivalence

section Transport

variable {A : Type u} {B : Type w} {C : Type x} {Label : Type v}

/-- A transport of `g` into `h`: every node of `g` goes to one node of `h`
with the same label, whose ordered children are the images of the node's
children. A copy that visits each node once and records where it went (node
memoization) is one, and so is a copy that shares nothing. -/
structure IsTransport (g : Graph A Label) (h : Graph B Label) (m : A → B) : Prop where
  label : ∀ a, h.label (m a) = g.label a
  children : ∀ a, h.children (m a) = (g.children a).map m

theorem IsTransport.isBisimulation {g : Graph A Label} {h : Graph B Label} {m : A → B}
    (hm : IsTransport g h m) : IsBisimulation g h (fun a b => m a = b) := by
  rintro a _ rfl
  refine ⟨(hm.label a).symm, ?_⟩
  rw [hm.children a, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun _ _ => rfl

/-- A transported node is the term it was copied from, cycles and sharing
included. -/
theorem IsTransport.bisimilar {g : Graph A Label} {h : Graph B Label} {m : A → B}
    (hm : IsTransport g h m) (a : A) : Bisimilar g h a (m a) :=
  ⟨_, hm.isBisimulation, rfl⟩

theorem IsTransport.comp {g : Graph A Label} {h : Graph B Label} {k : Graph C Label}
    {m : A → B} {n : B → C} (hm : IsTransport g h m) (hn : IsTransport h k n) :
    IsTransport g k (n ∘ m) where
  label a := by rw [Function.comp_apply, hn.label, hm.label]
  children a := by rw [Function.comp_apply, hn.children, hm.children, List.map_map]

/-- Across a boundary and back, a term is itself. -/
theorem IsTransport.round_trip {g : Graph A Label} {h : Graph B Label}
    {m : A → B} {n : B → A} (hm : IsTransport g h m) (hn : IsTransport h g n) (a : A) :
    Bisimilar g g a (n (m a)) :=
  (hm.comp hn).bisimilar a

end Transport

section Relabel

variable {A : Type u} {B : Type w} {C : Type x} {Label : Type v} {K : Type v}

/-- The graph with every label replaced by its image: a boundary that converts
labels (a foreign number to the runtime's) transports this graph. -/
def Graph.mapLabel (f : Label → K) (g : Graph A Label) : Graph A K where
  label a := f (g.label a)
  children := g.children

/-- Equality of terms whose labels compare through `f`. -/
def BisimilarBy (f : Label → K) (g : Graph A Label) (h : Graph B Label)
    (a : A) (b : B) : Prop :=
  Bisimilar (g.mapLabel f) (h.mapLabel f) a b

theorem BisimilarBy.refl (f : Label → K) (g : Graph A Label) (a : A) :
    BisimilarBy f g g a a :=
  Bisimilar.refl _ a

theorem BisimilarBy.symm {f : Label → K} {g : Graph A Label} {h : Graph B Label}
    {a : A} {b : B} (hab : BisimilarBy f g h a b) : BisimilarBy f h g b a :=
  Bisimilar.symm hab

theorem BisimilarBy.trans {f : Label → K} {g : Graph A Label} {h : Graph B Label}
    {k : Graph C Label} {a : A} {b : B} {c : C} (hab : BisimilarBy f g h a b)
    (hbc : BisimilarBy f h k b c) : BisimilarBy f g k a c :=
  Bisimilar.trans hab hbc

/-- Equal terms are equal through any label map. -/
theorem Bisimilar.by_map (f : Label → K) {g : Graph A Label} {h : Graph B Label}
    {a : A} {b : B} (hab : Bisimilar g h a b) : BisimilarBy f g h a b := by
  obtain ⟨R, hR, hr⟩ := hab
  refine ⟨R, fun x y hxy => ?_, hr⟩
  obtain ⟨hl, hc⟩ := hR hxy
  exact ⟨congrArg f hl, hc⟩

/-- A transport keeps a node's term through any label map. -/
theorem IsTransport.bisimilarBy (f : Label → K) {g : Graph A Label}
    {h : Graph B Label} {m : A → B} (hm : IsTransport g h m) (a : A) :
    BisimilarBy f g h a (m a) :=
  (hm.bisimilar a).by_map f

end Relabel

/-- Preserve leaf classes in addition to any chosen numeric comparison policy.
The numeric parameter can carry exact values, or an identity-sensitive format;
choosing it is a language obligation, not a graph-algorithm decision. -/
inductive TermLabel (Symbol : Type u) (Variable : Type v) (Number : Type w) where
  | atom (name : Symbol)
  | variable (id : Variable)
  | number (value : Number)
  | compound (name : Symbol)
  deriving DecidableEq

/-- A zero-argument compound and a symbol of the same spelling are distinct. -/
theorem atom_ne_compound {Symbol : Type u} {Variable : Type v} {Number : Type w}
    (name : Symbol) :
    (TermLabel.atom name : TermLabel Symbol Variable Number) ≠ .compound name := by
  intro h
  cases h

/-- Distinct variable identities do not become equal merely because both are
unbound. Alpha-renaming requires a separate, consistent renaming relation. -/
theorem variable_ne_of_ne {Symbol : Type u} {Variable : Type v} {Number : Type w}
    {x y : Variable} (hne : x ≠ y) :
    (TermLabel.variable x : TermLabel Symbol Variable Number) ≠ .variable y := by
  intro h
  exact hne (TermLabel.variable.inj h)

section PeTTa

open Mettapedia.Machines.PeTTaLeafEquality

variable {Symbol : Type u} {Variable : Type v}

/-- A label as PeTTa's `==` reads it: a number by its value class, an atom, a
variable and a compound name as they are. -/
def TermLabel.pettaClass : TermLabel Symbol Variable Num → TermLabel Symbol Variable Cls
  | .atom name => .atom name
  | .variable id => .variable id
  | .number value => .number (cls value)
  | .compound name => .compound name

/-- On two numeric leaves the class comparison is the runtime's decision. -/
theorem pettaClass_number_eq_iff (x y : Num) :
    (TermLabel.number x : TermLabel Symbol Variable Num).pettaClass =
      (TermLabel.number y).pettaClass ↔ valueEq x y = true := by
  simp [TermLabel.pettaClass, valueEq_iff]

/-- A number is never an atom, a variable, or a compound name. -/
theorem pettaClass_number_ne_atom (x : Num) (name : Symbol) :
    (TermLabel.number x : TermLabel Symbol Variable Num).pettaClass ≠
      (TermLabel.atom name).pettaClass := by
  simp [TermLabel.pettaClass]

/-- PeTTa's `==` on term graphs, cyclic ones included. -/
def PeTTaEq {A : Type w} {B : Type x} (g : Graph A (TermLabel Symbol Variable Num))
    (h : Graph B (TermLabel Symbol Variable Num)) (a : A) (b : B) : Prop :=
  BisimilarBy TermLabel.pettaClass g h a b

end PeTTa

namespace Examples

/-- One node presenting the infinite unary term `f(f(...))`. -/
def oneCycle : Graph Unit Nat where
  label _ := 0
  children _ := [()]

/-- Two nodes presenting the same infinite unary term. -/
def twoCycle : Graph Bool Nat where
  label _ := 0
  children b := [!b]

/-- Equality of rational terms is weaker than graph isomorphism: a cycle may
have a different number of nodes while unfolding to the same term. -/
theorem one_cycle_bisimilar_two_cycle (b : Bool) :
    Bisimilar oneCycle twoCycle () b := by
  refine ⟨fun a b => oneCycle.label a = twoCycle.label b, ?_, rfl⟩
  intro a c hac
  exact ⟨hac, .cons rfl .nil⟩

/-- The complete two-pair certificate validates the differently sized cycles. -/
theorem complete_cycle_certificate :
    checkCertificate oneCycle twoCycle [((), false), ((), true)] () false = true := by
  decide

/-- Merely listing the roots is insufficient: the next argument pair is absent. -/
theorem incomplete_cycle_certificate_rejected :
    checkCertificate oneCycle twoCycle [((), false)] () false = false := by
  decide

/-- Local conditions on an empty relation cannot certify an omitted root. -/
theorem empty_cycle_certificate_rejected :
    checkCertificate oneCycle twoCycle [] () false = false := by
  decide

inductive PairNode where
  | root | left | right
  deriving DecidableEq

/-- Swap only argument positions, retaining node labels and graph nodes. -/
def pairGraph (swapped : Bool) : Graph PairNode Nat where
  label
    | .root => 0
    | .left => 1
    | .right => 2
  children
    | .root => if swapped then [.right, .left] else [.left, .right]
    | _ => []

/-- Forgetting argument positions yields an ordinary unlabelled edge relation. -/
def unlabelledEdge {Node : Type u} {Label : Type v} (g : Graph Node Label)
    (a b : Node) : Prop := b ∈ g.children a

/-- The unlabelled representation cannot see that arguments were swapped. -/
theorem pair_unlabelled_edges_eq :
    unlabelledEdge (pairGraph false) = unlabelledEdge (pairGraph true) := by
  funext a b
  cases a <;> cases b <;> simp [unlabelledEdge, pairGraph]

/-- Consequently hyperset-style bisimilarity accepts the swapped pair. -/
theorem pair_unlabelled_bisimilar :
    Mettapedia.TypeTheory.MaterialSets.Hypersets.Bisimilar
      (unlabelledEdge (pairGraph false)) (unlabelledEdge (pairGraph true))
      PairNode.root PairNode.root := by
  rw [pair_unlabelled_edges_eq]
  exact Mettapedia.TypeTheory.MaterialSets.Hypersets.Bisimilar.rfl

/-- Ordered term equality rejects it at depth two. -/
theorem pair_not_bisimilar :
    ¬ Bisimilar (pairGraph false) (pairGraph true) PairNode.root PairNode.root := by
  apply not_bisimilar_of_observe_ne (depth := 2)
  simp [observe, pairGraph]

/-- Listing the unequal leaf pairs does not hide their unequal labels. -/
theorem swapped_pair_certificate_rejected :
    checkCertificate (pairGraph false) (pairGraph true)
      [(.root, .root), (.left, .right), (.right, .left)]
      PairNode.root PairNode.root = false := by
  decide

/-- A repeated argument is semantically significant, although membership
relations discard repeated edges. -/
def repeatedArgument (twice : Bool) : Graph Bool Nat where
  label b := if b then 1 else 0
  children b := if b then [] else if twice then [true, true] else [true]

theorem repeated_argument_unlabelled_edges_eq :
    unlabelledEdge (repeatedArgument false) = unlabelledEdge (repeatedArgument true) := by
  funext a b
  cases a <;> cases b <;> simp [unlabelledEdge, repeatedArgument]

theorem repeated_argument_not_bisimilar :
    ¬ Bisimilar (repeatedArgument false) (repeatedArgument true) false false := by
  apply not_bisimilar_of_observe_ne (depth := 1)
  simp [observe, repeatedArgument]

/-- A related child cannot justify a mismatch in the number of arguments. -/
theorem unequal_arity_certificate_rejected :
    checkCertificate (repeatedArgument false) (repeatedArgument true)
      [(false, false), (true, true)] false false = false := by
  decide

end Examples

namespace PeTTaExamples

open Mettapedia.Machines.PeTTaLeafEquality

inductive Sym where
  | f | z | q
  deriving DecidableEq

/-- Nodes of `c = f(leaf, c)`. -/
inductive Loop where
  | root | leaf
  deriving DecidableEq

/-- `c = f(n, c)`, with `leaf` the first argument. -/
def loop (leaf : TermLabel Sym Nat Num) : Graph Loop (TermLabel Sym Nat Num) where
  label
    | .root => .compound .f
    | .leaf => leaf
  children
    | .root => [.leaf, .root]
    | .leaf => []

/-- Nodes of `d = f(n, f(n, d))`, the same term unrolled once. -/
inductive Loop2 where
  | root | leaf | inner | innerLeaf
  deriving DecidableEq

def loop2 (leaf : TermLabel Sym Nat Num) : Graph Loop2 (TermLabel Sym Nat Num) where
  label
    | .root => .compound .f
    | .inner => .compound .f
    | _ => leaf
  children
    | .root => [.leaf, .inner]
    | .inner => [.innerLeaf, .root]
    | _ => []

/-- A cycle with a NaN leaf is `==` to itself, and to the cycle of another NaN. -/
theorem nan_loop_eq :
    PeTTaEq (loop (.number (.nan 1))) (loop (.number (.nan 2))) Loop.root Loop.root :=
  checkCertificate_sound (pairs := [(.root, .root), (.leaf, .leaf)]) (by decide)

/-- `c = f(1, c)` and `d = f(1.0, d)` are `==`. -/
theorem int_float_loop_eq :
    PeTTaEq (loop (.number (.int 1))) (loop (.number (.fin 1))) Loop.root Loop.root :=
  checkCertificate_sound (pairs := [(.root, .root), (.leaf, .leaf)]) (by decide)

/-- `c = f(1, c)` and its unrolling `d = f(1, f(1, d))` are `==`. -/
theorem loop_eq_unrolled :
    PeTTaEq (loop (.number (.int 1))) (loop2 (.number (.int 1))) Loop.root Loop2.root :=
  checkCertificate_sound
    (pairs := [(.root, .root), (.leaf, .leaf), (.root, .inner), (.leaf, .innerLeaf)])
    (by decide)

/-- `c = f(1, c)` and `d = f(2, d)` are not. -/
theorem loop_ne_other_leaf :
    ¬ PeTTaEq (loop (.number (.int 1))) (loop (.number (.int 2))) Loop.root Loop.root := by
  apply not_bisimilar_of_observe_ne (depth := 2)
  simp [observe, loop, Graph.mapLabel, TermLabel.pettaClass, cls]

/-- `f(z(), c)` and `f(q(), d)`: zero-argument compounds of different names
are different leaves. -/
theorem loop_ne_other_compound :
    ¬ PeTTaEq (loop (.compound .z)) (loop (.compound .q)) Loop.root Loop.root := by
  apply not_bisimilar_of_observe_ne (depth := 2)
  simp [observe, loop, Graph.mapLabel, TermLabel.pettaClass]

/-- A zero-argument compound is not the atom of its name. -/
theorem loop_ne_atom_leaf :
    ¬ PeTTaEq (loop (.compound .z)) (loop (.atom .z)) Loop.root Loop.root := by
  apply not_bisimilar_of_observe_ne (depth := 2)
  simp [observe, loop, Graph.mapLabel, TermLabel.pettaClass]

end PeTTaExamples

end Mettapedia.Machines.RationalTermGraph
