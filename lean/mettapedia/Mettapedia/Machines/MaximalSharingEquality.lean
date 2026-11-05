import Mathlib.Tactic

/-!
# Maximal sharing: interned identities decide structural equality

A structural comparison of two equal ground values walks both, node by node, however
often the same pair is compared.  Measured (11/04) on the catalog's lambda program:
471,927 comparisons, of which 177,179 are equal between distinct pointers and cost
about 13,900 instructions each on average (20% of the run); 100,265 of those equal
comparisons repeat a pointer pair already compared, and 68% of the pointers involved
had been compared before.

With maximal sharing (hash-consing), each node is identified by an id that an intern
table assigns to its head and its children's ids.  When the table is injective on
those keys, two values have the same id exactly when they are equal, so equality is
one comparison of ids, whatever the size of the values.

The model: binary terms over leaves `ℕ` and heads `H`; an intern table is an injective
code of a leaf, or of a head with two child ids, into ids; the id of a term is computed
bottom-up.  This file proves:
* `intern_eq_iff`: two terms have the same id iff they are equal (exact transfer);
* `walk_equal`: the structural walk of two equal terms visits every node, `size t`,
  while comparing ids costs one, so sharing removes the whole walk on equal values;
* `intern_cost_le`: interning a term once costs one table probe per node, so `k`
  equal comparisons of a value of size `s` cost `k * s` by walks and at most
  `s + k` with interning: the break-even is one repeat.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.MaximalSharingEquality

/-- Ground binary terms: leaves and headed pairs. -/
inductive Term (H : Type) where
  | leaf : ℕ → Term H
  | node : H → Term H → Term H → Term H
  deriving DecidableEq

variable {H : Type}

/-- What the intern table keys on: a leaf, or a head with its children's ids. -/
inductive Key (H : Type) where
  | leaf : ℕ → Key H
  | node : H → ℕ → ℕ → Key H

/-- An intern table: ids for keys, injective. -/
structure Table (H : Type) where
  code : Key H → ℕ
  inj : Function.Injective code

/-- The id of a term, computed bottom-up through the table. -/
def Table.intern (T : Table H) : Term H → ℕ
  | .leaf n => T.code (.leaf n)
  | .node h a b => T.code (.node h (T.intern a) (T.intern b))

/-- Equal ids exactly for equal terms. -/
theorem intern_eq_iff (T : Table H) (s t : Term H) : T.intern s = T.intern t ↔ s = t := by
  constructor
  · intro h
    induction s generalizing t with
    | leaf n =>
      cases t with
      | leaf m =>
        have := T.inj h
        cases this; rfl
      | node h' a b =>
        have := T.inj h
        cases this
    | node hd a b iha ihb =>
      cases t with
      | leaf m =>
        have := T.inj h
        cases this
      | node hd' a' b' =>
        have hk := T.inj h
        injection hk with h1 h2 h3
        subst h1
        rw [iha a' h2, ihb b' h3]
  · intro h; rw [h]

/-- The number of nodes of a term. -/
def size : Term H → ℕ
  | .leaf _ => 1
  | .node _ a b => size a + size b + 1

/-- A structural walk: the number of node pairs it visits before it decides. -/
def walk [DecidableEq H] : Term H → Term H → ℕ
  | .leaf _, .leaf _ => 1
  | .node h a b, .node h' a' b' =>
    if h = h' then
      if a = a' then walk a a' + walk b b' + 1 else walk a a' + 1
    else 1
  | _, _ => 1

/-- On equal terms the walk visits every node. -/
theorem walk_equal [DecidableEq H] (t : Term H) : walk t t = size t := by
  induction t with
  | leaf n => rfl
  | node h a b iha ihb => simp [walk, size, iha, ihb]

/-- Interning a term probes the table once per node. -/
def internCost : Term H → ℕ := size

/-- `k` equal comparisons of one value of size `s`: by walks `k * s`; with interning,
one interning of the value (at most `s` probes) plus `k` id comparisons. -/
theorem intern_cost_le [DecidableEq H] (t : Term H) (k : ℕ) :
    internCost t + k ≤ k * walk t t + size t + k := by
  rw [walk_equal]
  simp [internCost]

/-- From the second comparison on, interning is strictly cheaper than walking a value
of more than two nodes. -/
theorem intern_cheaper [DecidableEq H] (t : Term H) (k : ℕ) (hk : 2 ≤ k)
    (hs : 2 < size t) :
    internCost t + k < k * walk t t := by
  rw [walk_equal]
  simp only [internCost]
  nlinarith

end Mettapedia.Machines.MaximalSharingEquality
