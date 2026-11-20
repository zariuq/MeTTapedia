import Mettapedia.Machines.CMemory.Borrowing

/-!
# Regions and modes, decided

Containment and disjointness of regions and the order of loan modes, each as a
Bool function by plain recursion and pattern matching with its meaning as a
proposition and an `_iff` lemma. Regions name logical allocations, not numerical
C addresses.
-/

set_option autoImplicit false

namespace Mettapedia.Ownership

open Mettapedia.Machines.CMemory.Borrowing

def containsB (outer inner : Region) : Bool :=
  outer.root == inner.root && outer.first ≤ inner.first && inner.finish ≤ outer.finish

theorem containsB_iff (outer inner : Region) : containsB outer inner = true ↔ outer.Contains inner := by
  simp [containsB, Region.Contains, and_assoc]

def disjointB (a b : Region) : Bool :=
  a.root != b.root || a.finish ≤ b.first || b.finish ≤ a.first

theorem disjointB_iff (a b : Region) : disjointB a b = true ↔ a.Disjoint b := by
  simp [disjointB, Region.Disjoint, or_assoc]

def allowsB (parent child : Mode) : Bool := parent == .exclusive || child == .shared

theorem allowsB_iff (parent child : Mode) : allowsB parent child = true ↔
    (parent = .shared → child = .shared) := by
  cases parent <;> cases child <;> decide

end Mettapedia.Ownership
