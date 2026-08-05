import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Order.Lattice

/-!
# The two-level algebra of spaces and queries

One symbol caused a week of confusion: relational "join" is an order-theoretic
**meet**.  This module states the two-level picture once, with the collision
dissolved:

* **Query level.**  A query is a constraint on environments; conjunction is
  the pointwise meet.  Conjunction is therefore commutative, associative,
  idempotent, and has the always-true constraint as its unit — the `(,)` of
  the engine, whose one-success/no-bindings behaviour is exactly `top`.
  The engine's seed-threaded fold (each conjunct filtered against the
  solutions of the previous ones) computes precisely the simultaneous meet:
  `foldConj_eq_meet`.  That theorem is the license for implementing the join
  as a left fold, including the sourced form where every leg carries its own
  space — a leg is just a query, and the fold does not care where its
  constraints came from.
* **Space level.**  A space is an `M`-valued assignment of multiplicities to
  atoms.  Union is pointwise addition (multiplicities add); meet is pointwise
  minimum (each atom kept with the smaller multiplicity — the standard bag
  operations, degrading to set union/intersection on the Boolean carrier).
* **The connecting law.**  Weighted answers distribute over space union:
  aggregating candidates against `S ⊔ T` equals the sum of aggregating
  against each — `weightedAnswers_union`.  Union feeds ⊕; conjunction feeds
  the meet; the two levels never share a symbol.

Everything is finite and elementary; no choice principles are needed
anywhere in the module.
-/

namespace Mettapedia.GSLT.Dynamics.SpaceQueryAlgebra

/-! ## Query level: conjunction is the meet of constraints -/

variable {Env : Type}

/-- A query, as the constraint its solutions satisfy. -/
abbrev Query (Env : Type) := Env → Prop

/-- Conjunction of queries: both constraints hold. -/
def conj (p q : Query Env) : Query Env := fun θ => p θ ∧ q θ

/-- The unit of conjunction: the constraint that always holds.  This is the
engine's `(,)` — one success, restricting nothing. -/
def unitQ : Query Env := fun _ => True

theorem conj_comm (p q : Query Env) : conj p q = conj q p := by
  funext θ; exact propext ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩

theorem conj_assoc (p q r : Query Env) :
    conj (conj p q) r = conj p (conj q r) := by
  funext θ; exact propext and_assoc

theorem conj_idem (p : Query Env) : conj p p = p := by
  funext θ; exact propext and_self_iff

theorem conj_unit_left (p : Query Env) : conj unitQ p = p := by
  funext θ; exact propext ⟨fun ⟨_, h⟩ => h, fun h => ⟨trivial, h⟩⟩

theorem conj_unit_right (p : Query Env) : conj p unitQ = p := by
  funext θ; exact propext ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, trivial⟩⟩

/-- Disjunction of queries: either constraint holds.  This is the constraint
(solution-set) level; the engine's answer bags keep duplicates, so `(| p p)`
duplicates answers operationally — idempotence below is a set-level fact, and
the multiplicity-honest laws are the aggregate ones in the weighted layer. -/
def disj (p q : Query Env) : Query Env := fun θ => p θ ∨ q θ

/-- The unit of disjunction: the unsatisfiable constraint — the engine's
`(|)`, zero answers.  With `unitQ` this completes the semiring picture:
`(,)` is the 1 and `(|)` is the 0 of the query algebra. -/
def zeroQ : Query Env := fun _ => False

theorem disj_comm (p q : Query Env) : disj p q = disj q p := by
  funext θ; exact propext or_comm

theorem disj_assoc (p q r : Query Env) :
    disj (disj p q) r = disj p (disj q r) := by
  funext θ; exact propext or_assoc

theorem disj_unit_left (p : Query Env) : disj zeroQ p = p := by
  funext θ; exact propext ⟨fun h => h.elim False.elim id, Or.inr⟩

theorem disj_unit_right (p : Query Env) : disj p zeroQ = p := by
  funext θ; exact propext ⟨fun h => h.elim id False.elim, Or.inl⟩

/-- The 0 annihilates the 1's product: conjoining with the unsatisfiable
constraint is unsatisfiable. -/
theorem conj_zero (p : Query Env) : conj p zeroQ = zeroQ := by
  funext θ; exact propext ⟨fun ⟨_, h⟩ => h, False.elim⟩

theorem zero_conj (p : Query Env) : conj zeroQ p = zeroQ := by
  funext θ; exact propext ⟨fun ⟨h, _⟩ => h, False.elim⟩

/-- **Distributivity** — conjunction over disjunction, giving disjunctive
normal form: `(, p (| q r)) = (| (, p q) (, p r))`.  Comma and pipe with
their units are the query algebra's (·, 1, ⊕, 0). -/
theorem conj_disj_distrib_left (p q r : Query Env) :
    conj p (disj q r) = disj (conj p q) (conj p r) := by
  funext θ; exact propext and_or_left

theorem conj_disj_distrib_right (p q r : Query Env) :
    conj (disj p q) r = disj (conj p r) (conj q r) := by
  funext θ; exact propext or_and_right

/-- The simultaneous meet of a list of constraints. -/
def meetAll (qs : List (Query Env)) : Query Env :=
  fun θ => ∀ q ∈ qs, q θ

/-- The engine's evaluation order: a left fold that filters each conjunct
against the accumulated constraint — seeds threaded leg by leg. -/
def foldConj (qs : List (Query Env)) : Query Env :=
  qs.foldl conj unitQ

/-- Folding from an accumulated constraint conjoins it with the rest. -/
theorem foldl_conj_acc (qs : List (Query Env)) (acc : Query Env) :
    qs.foldl conj acc = conj acc (meetAll qs) := by
  induction qs generalizing acc with
  | nil =>
    funext θ
    exact propext ⟨fun h => ⟨h, fun q hq => absurd hq (List.not_mem_nil)⟩,
      fun ⟨h, _⟩ => h⟩
  | cons q rest ih =>
    simp only [List.foldl_cons, ih]
    funext θ
    refine propext ⟨?_, ?_⟩
    · rintro ⟨⟨ha, hq⟩, hrest⟩
      exact ⟨ha, by
        intro r hr
        rcases List.mem_cons.mp hr with h | h
        · exact h ▸ hq
        · exact hrest r h⟩
    · rintro ⟨ha, hall⟩
      exact ⟨⟨ha, hall q (by simp)⟩, fun r hr => hall r (by simp [hr])⟩

/-- **The implementation license.**  The seed-threaded fold computes exactly
the simultaneous meet: evaluation order is administrative, the constraint is
order-free.  A sourced conjunction — each leg a query against its own space —
is the same statement, since a leg is just a query. -/
theorem foldConj_eq_meet (qs : List (Query Env)) :
    foldConj qs = meetAll qs := by
  unfold foldConj
  rw [foldl_conj_acc, conj_unit_left]

/-- The engine's unit law `(,)`: folding no conjuncts constrains nothing. -/
theorem foldConj_nil : foldConj ([] : List (Query Env)) = unitQ := rfl

/-- The engine's singleton law `(, p) = p`. -/
theorem foldConj_singleton (p : Query Env) : foldConj [p] = p := by
  rw [foldConj_eq_meet]
  funext θ
  refine propext ⟨fun h => h p (by simp), fun h q hq => ?_⟩
  rcases List.mem_singleton.mp hq with rfl
  exact h

/-- Conjunction of the meets is the meet of the concatenation: legs may be
grouped freely. -/
theorem meetAll_append (qs rs : List (Query Env)) :
    conj (meetAll qs) (meetAll rs) = meetAll (qs ++ rs) := by
  funext θ
  refine propext ⟨?_, ?_⟩
  · rintro ⟨hq, hr⟩ q hmem
    rcases List.mem_append.mp hmem with h | h
    · exact hq q h
    · exact hr q h
  · intro h
    exact ⟨fun q hq => h q (by simp [hq]), fun r hr => h r (by simp [hr])⟩

/-! ## Space level: pointwise multiplicities -/

variable {Atom : Type}

/-- A space as an assignment of multiplicities. -/
abbrev MSpace (Atom : Type) := Atom → ℕ

/-- Union: multiplicities add. -/
def sUnion (S T : MSpace Atom) : MSpace Atom := fun x => S x + T x

/-- Meet: each atom kept with the smaller multiplicity. -/
def sMeet (S T : MSpace Atom) : MSpace Atom := fun x => min (S x) (T x)

theorem sUnion_comm (S T : MSpace Atom) : sUnion S T = sUnion T S := by
  funext x; exact Nat.add_comm _ _

theorem sUnion_assoc (S T U : MSpace Atom) :
    sUnion (sUnion S T) U = sUnion S (sUnion T U) := by
  funext x; exact Nat.add_assoc _ _ _

theorem sMeet_comm (S T : MSpace Atom) : sMeet S T = sMeet T S := by
  funext x; exact Nat.min_comm _ _

theorem sMeet_assoc (S T U : MSpace Atom) :
    sMeet (sMeet S T) U = sMeet S (sMeet T U) := by
  funext x; exact Nat.min_assoc (S x) (T x) (U x)

theorem sMeet_idem (S : MSpace Atom) : sMeet S S = S := by
  funext x; exact Nat.min_self _

/-- The meet never exceeds either operand: intersection filters, pointwise. -/
theorem sMeet_le_left (S T : MSpace Atom) (x : Atom) : sMeet S T x ≤ S x :=
  Nat.min_le_left _ _

theorem sMeet_le_right (S T : MSpace Atom) (x : Atom) : sMeet S T x ≤ T x :=
  Nat.min_le_right _ _

/-! ## The connecting law: answers distribute over union -/

/-- The aggregate weight of a candidate list against a space: each candidate
counts with its multiplicity. -/
def weightedAnswers (S : MSpace Atom) (cands : List Atom) : ℕ :=
  (cands.map S).sum

/-- **Distribution.**  Querying the union is the sum of querying the parts —
union of spaces surfaces in answers as ⊕, which is also why per-source
attribution is recoverable from a union query by receipts: the sum
decomposes. -/
theorem weightedAnswers_union (S T : MSpace Atom) (cands : List Atom) :
    weightedAnswers (sUnion S T) cands
      = weightedAnswers S cands + weightedAnswers T cands := by
  induction cands with
  | nil => rfl
  | cons c rest ih =>
    simp only [weightedAnswers, List.map_cons, List.sum_cons] at ih ⊢
    simp only [sUnion] at *
    omega

/-- The meet is bounded by both queries, aggregate-wise: an intersection
query never answers more than either source. -/
theorem weightedAnswers_meet_le_left (S T : MSpace Atom) (cands : List Atom) :
    weightedAnswers (sMeet S T) cands ≤ weightedAnswers S cands := by
  induction cands with
  | nil => exact Nat.le_refl _
  | cons c rest ih =>
    simp only [weightedAnswers, List.map_cons, List.sum_cons] at ih ⊢
    exact Nat.add_le_add (sMeet_le_left S T c) ih

/-- **Pattern-disjunction, bag-honestly.**  A disjunctive pattern's candidates
are the concatenation of the per-disjunct candidates, and the aggregate is the
sum: `match(S, (| p q)) = match(S, p) ⊕ match(S, q)` at the answer-bag level —
the mirror of `weightedAnswers_union`, with the pipe on the pattern side
instead of the space side.  Multiplicity preserved, no idempotence claimed. -/
theorem weightedAnswers_append (S : MSpace Atom) (c₁ c₂ : List Atom) :
    weightedAnswers S (c₁ ++ c₂)
      = weightedAnswers S c₁ + weightedAnswers S c₂ := by
  simp [weightedAnswers, List.sum_append]

end Mettapedia.GSLT.Dynamics.SpaceQueryAlgebra
