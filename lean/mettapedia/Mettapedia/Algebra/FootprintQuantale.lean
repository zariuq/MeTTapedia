import Mettapedia.Algebra.QuantaleWeakness

/-!
# Footprint quantale (generic over the label type)

The grading algebra for axiom/rule footprints: `Q = ((Set α)ᵒᵈ, ∪, ∅, ⊇)` —
footprints compose by union, ordered by **reverse inclusion**: a smaller
footprint is a *stronger* claim ("proved using no more than q"), with unit
`∅ = ⊤` ("uses nothing"), making the quantale **integral**. This is the
Lawvere-metric pattern (`([0,∞], ≥, +, 0)`) with sets of labels in place of
distances.

The order direction is load-bearing: with plain inclusion, `q ∪ ∅ = q ≠ ∅`
violates `⊗`-preservation of the empty sup, so `(P(α), ∪, ∅, ⊆)` is NOT a
quantale — building this instance is what catches that class of error.

Carrier note: `Set α`, not `Finset α` — `Finset` carries no `CompleteLattice`
for infinite `α` (arbitrary sups escape finiteness). Finiteness is a property
of *computed* footprints (extractors return finite sets), never of the
algebra.

Nothing language-specific belongs here. Metamath instantiation
(`gradedProvable` over mm-lean4, footprint extractors) lives at
`Languages/Metamath/`; the labeled-span graded modalities live at
`OSLF/Framework/`. The seam that composes them is the shared label
vocabulary: one quantale, `syntaxFootprint ∪ logicalFootprint`.
-/

namespace Mettapedia.Algebra.FootprintQuantale

open Mettapedia.Algebra.QuantaleWeakness

/-- Footprints over labels `α`, ordered by reverse inclusion. -/
abbrev Footprint (α : Type*) := (Set α)ᵒᵈ

namespace Footprint

variable {α : Type*}

def ofSet (s : Set α) : Footprint α := OrderDual.toDual s

def labels (q : Footprint α) : Set α := OrderDual.ofDual q

@[simp] theorem labels_ofSet (s : Set α) : (ofSet s).labels = s := rfl

@[simp] theorem ofSet_labels (q : Footprint α) : ofSet q.labels = q := rfl

/-- Union of the underlying label sets IS the lattice meet of the dual order —
the observation that makes every law below a stock lattice fact. -/
instance : CommMonoid (Footprint α) where
  mul q r := q ⊓ r
  one := ⊤
  mul_assoc _ _ _ := inf_assoc ..
  one_mul _ := top_inf_eq ..
  mul_one _ := inf_top_eq ..
  mul_comm _ _ := inf_comm ..

@[simp] theorem labels_mul (q r : Footprint α) :
    (q * r).labels = q.labels ∪ r.labels := rfl

@[simp] theorem labels_one : (1 : Footprint α).labels = ∅ := rfl

/-- The order, unfolded: `q ≤ r` iff `r`'s labels are contained in `q`'s —
"stronger claim = fewer labels used." -/
theorem le_iff_superset (q r : Footprint α) : q ≤ r ↔ r.labels ⊆ q.labels :=
  Iff.rfl

/-- Integrality: the unit is the top element ("uses nothing" is strongest). -/
theorem one_eq_top : (1 : Footprint α) = ⊤ := rfl

/-- The quantale laws are the frame law of the dual complete Boolean algebra:
`mul = ⊓`, and `x ⊓ sSup s = ⨆ y ∈ s, x ⊓ y`. -/
instance : IsCommQuantale (Footprint α) :=
  IsCommQuantale.ofCommSemigroup (fun _ _ => inf_sSup_eq)

-- concrete sanity: composition unions, unit vanishes, order reverses
example : (ofSet {1} : Footprint ℕ) * ofSet {2} = ofSet ({1, 2} : Set ℕ) := by
  show ofSet ({1} ∪ {2} : Set ℕ) = ofSet ({1, 2} : Set ℕ)
  rw [Set.singleton_union]

example : (ofSet {1, 2} : Footprint ℕ) ≤ ofSet {1} := by
  rw [le_iff_superset]
  intro a ha
  simp only [labels_ofSet, Set.mem_insert_iff, Set.mem_singleton_iff] at *
  exact Or.inl ha

example : (1 : Footprint ℕ) * ofSet {3} = ofSet {3} := one_mul _

end Footprint

end Mettapedia.Algebra.FootprintQuantale
