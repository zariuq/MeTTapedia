import Mettapedia.OSLF.Syntax.FreePresheafEventExtension
import Mettapedia.TypeTheory.IndexedPolynomial

/-!
# A proof-relevant event graph as a nullary rule polynomial

At a fixed stage and endpoint pair, a graph's event fibre is precisely the
initial algebra of a polynomial with one nullary constructor per individual
event. The comparison preserves multiple events with the same endpoints.
It is independent of images, subobject classifiers, and any choice of
equation quotient on states.

Premise-bearing rules need additional recursive positions. The nullary
comparison is the graph component of a larger operational rule algebra.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.EventGraphNullaryPolynomial

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.FreePresheafEventExtension

universe u v w

variable {C : Type u} [Category.{v} C] {V : C ⥤ Type w}
    (G : Graph V)

/-- Individual firings with a specified endpoint pair at one context. -/
abbrev EndpointFiber (X : C) (pair : V.obj X × V.obj X) :=
  {event : G.edge.obj X //
    G.source.app X event = pair.1 ∧ G.target.app X event = pair.2}

/-- The index remembers context and both states, including their sorts when
the state presheaf itself is sorted. -/
abbrev Judgment := Σ X : C, V.obj X × V.obj X

/-- A graph event is a nullary constructor at exactly its endpoint judgment. -/
def rules : IndexedPolynomial Unit (fun _ => Judgment (V := V)) where
  Shape _ j := EndpointFiber G j.1 j.2
  Position _ := Empty
  next _ impossible := impossible.elim

/-- Construct the one-node derivation for a graph firing. -/
def eventTree {X : C} {pair : V.obj X × V.obj X}
    (event : EndpointFiber G X pair) :
    (rules G).Fix () ⟨X, pair⟩ :=
  .roll event (fun impossible => impossible.elim)

/-- Read the individual firing back from the root of its one-node tree. -/
def treeEvent {X : C} {pair : V.obj X × V.obj X}
    (tree : (rules G).Fix () ⟨X, pair⟩) :
    EndpointFiber G X pair :=
  ((IndexedPolynomial.Fix.out (rules G) tree).1)

/-- Reindex both endpoints along a context map. -/
def reindexPair {X Y : C} (f : X ⟶ Y)
    (pair : V.obj X × V.obj X) : V.obj Y × V.obj Y :=
  (V.map f pair.1, V.map f pair.2)

theorem reindexPair_id {X : C} (pair : V.obj X × V.obj X) :
    reindexPair (𝟙 X) pair = pair := by
  cases pair
  simp [reindexPair]

theorem reindexPair_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (pair : V.obj X × V.obj X) :
    reindexPair (f ≫ g) pair = reindexPair g (reindexPair f pair) := by
  cases pair
  simp [reindexPair]

/-- Reindex a retained firing, with naturality supplying its new endpoint
proofs. The edge itself is mapped, rather than reconstructed from endpoint
existence. -/
def reindexEvent {X Y : C} (f : X ⟶ Y)
    {pair : V.obj X × V.obj X} (event : EndpointFiber G X pair) :
    EndpointFiber G Y (reindexPair f pair) := by
  refine ⟨G.edge.map f event.1, ?_, ?_⟩
  · have natural := congrArg
        (fun h : G.edge.obj X ⟶ V.obj Y => h event.1)
        (G.source.naturality f)
    simp [reindexPair, event.2.1] at natural ⊢
  · have natural := congrArg
        (fun h : G.edge.obj X ⟶ V.obj Y => h event.1)
        (G.target.naturality f)
    simp [reindexPair, event.2.2] at natural ⊢

/-- Identity reindexing retains the same individual firing. Heterogeneous
equality accounts for the propositionally equal endpoint-fibre indices. -/
theorem reindexEvent_id {X : C} {pair : V.obj X × V.obj X}
    (event : EndpointFiber G X pair) :
    HEq (reindexEvent G (𝟙 X) event) event := by
  rw [Subtype.heq_iff_coe_eq]
  · simp [reindexEvent]
  · intro value
    simp [reindexPair]

/-- Successive context maps act on the retained event itself. -/
theorem reindexEvent_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    {pair : V.obj X × V.obj X} (event : EndpointFiber G X pair) :
    HEq (reindexEvent G (f ≫ g) event)
      (reindexEvent G g (reindexEvent G f event)) := by
  rw [Subtype.heq_iff_coe_eq]
  · simp [reindexEvent]
  · intro value
    simp [reindexPair]

/-- Reindex the one-node constructor corresponding to a retained firing. -/
def reindexTree {X Y : C} (f : X ⟶ Y)
    {pair : V.obj X × V.obj X}
    (tree : (rules G).Fix () ⟨X, pair⟩) :
    (rules G).Fix () ⟨Y, reindexPair f pair⟩ :=
  eventTree G (reindexEvent G f (treeEvent G tree))

theorem reindexTree_eventTree {X Y : C} (f : X ⟶ Y)
    {pair : V.obj X × V.obj X} (event : EndpointFiber G X pair) :
    reindexTree G f (eventTree G event) =
      eventTree G (reindexEvent G f event) := by
  rfl

/-- The entire endpoint fibre, rather than its mere truth value, is
isomorphic to the corresponding initial-algebra fibre. -/
def eventFiberEquiv (X : C) (pair : V.obj X × V.obj X) :
    EndpointFiber G X pair ≃ (rules G).Fix () ⟨X, pair⟩ where
  toFun := eventTree G
  invFun := treeEvent G
  left_inv := by
    intro event
    rfl
  right_inv := by
    intro tree
    have emptyChildren :
        (IndexedPolynomial.Fix.out (rules G) tree).2 =
          (fun impossible => impossible.elim) := by
      funext impossible
      exact impossible.elim
    change IndexedPolynomial.Fix.roll
        ((IndexedPolynomial.Fix.out (rules G) tree).1)
        (fun impossible => impossible.elim) = tree
    rw [← emptyChildren]
    exact IndexedPolynomial.Fix.rollExtension_out (rules G) tree

/-- Distinct firing witnesses at identical endpoints give distinct initial
constructor trees. The endpoint predicate cannot make this distinction. -/
theorem distinct_trees_of_distinct_events {X : C}
    {pair : V.obj X × V.obj X}
    (first second : EndpointFiber G X pair)
    (distinct : first.1 ≠ second.1) :
    eventTree G first ≠ eventTree G second := by
  intro equal
  have fibreEqual := (eventFiberEquiv G X pair).injective equal
  exact distinct (congrArg Subtype.val fibreEqual)

#print axioms eventFiberEquiv
#print axioms distinct_trees_of_distinct_events
#print axioms reindexEvent_comp

end Mettapedia.OSLF.Binding.EventGraphNullaryPolynomial
