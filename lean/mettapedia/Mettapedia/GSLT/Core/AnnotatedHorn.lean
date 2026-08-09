import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# Counting is a semiring homomorphism from derivation bags

A one-step semantics over a definite (positive Horn) program has two readings.
The **witness** reading produces a bag of derivations: for each rule whose head
matches, one derivation per choice of a witness for each body atom.  The
**annotation** reading produces a number: the multiplicity of the answer.

The claim relating them is that multiplicity is a semiring homomorphism —
multiplicities multiply along a rule body and add across rules — so the counted
reading is exactly `ℕ`-annotated Horn.  Here that is proved rather than
asserted:

* `card_bagProduct` — the multiplicative half.  A rule body is a product: one
  witness chosen per body atom, so the count is the product of the counts.
* `card_listSum` — the additive half.  Alternative rules are a sum.
* `card_stepBag` — the two together: counting the witness bag of one step
  equals the `ℕ`-annotated step on the counts.

## Why the negative matters as much

`support_forgets_multiplicity` exhibits two rules deriving one atom whose
witness bag has two elements and whose support has one.  So the set-valued
(support) quotient is **not** the counted semantics, and a storage layer that
keeps only presence realizes strictly less.

`support_faithful_for_provability` is its companion: the support quotient is
exact for *whether* an atom is derivable, and only loses *how many ways*.  That
pair is the precise statement of what a set-valued backend does and does not
implement.
-/

namespace Mettapedia.GSLT.Core.AnnotatedHorn

universe u v

/-- One definite clause: a head derivable from an ordered body. -/
structure DefiniteRule (Atom : Type u) where
  /-- The atoms that must already hold. -/
  body : List Atom
  /-- The atom this clause derives. -/
  head : Atom

variable {Atom : Type u} {Witness : Type v}

/-! ## A rule body is a product

One derivation of a rule instance is one choice of witness per body atom. -/

/-- All ways of choosing one witness from each of an ordered list of bags. -/
def bagProduct : List (Multiset Witness) → Multiset (List Witness)
  | [] => {[]}
  | bag :: bags =>
      bag.bind fun witness => (bagProduct bags).map fun rest => witness :: rest

@[simp] theorem bagProduct_nil :
    bagProduct ([] : List (Multiset Witness)) = {[]} := rfl

@[simp] theorem bagProduct_cons (bag : Multiset Witness)
    (bags : List (Multiset Witness)) :
    bagProduct (bag :: bags) =
      bag.bind fun witness => (bagProduct bags).map fun rest => witness :: rest :=
  rfl

/-- **The multiplicative half.**  The number of derivations of a rule body is
the product of the numbers of derivations of its atoms. -/
theorem card_bagProduct (bags : List (Multiset Witness)) :
    Multiset.card (bagProduct bags) = (bags.map Multiset.card).prod := by
  induction bags with
  | nil => simp
  | cons bag bags inductionHypothesis =>
      simp [Multiset.card_bind, Multiset.map_const', Multiset.sum_replicate,
        inductionHypothesis, mul_comm]

/-! ## Alternative rules are a sum -/

/-- **The additive half.**  Counting a collected family of bags adds. -/
theorem card_listSum (bags : List (Multiset Witness)) :
    Multiset.card bags.sum = (bags.map Multiset.card).sum := by
  induction bags with
  | nil => simp
  | cons bag bags inductionHypothesis =>
      simp [inductionHypothesis]

/-! ## One step, both ways -/

variable [DecidableEq Atom]

/-- The bag of one-step derivations of an atom: for each rule that derives it,
one derivation per choice of witnesses for the body. -/
def stepBag (rules : List (DefiniteRule Atom))
    (assign : Atom → Multiset Witness) (atom : Atom) : Multiset (List Witness) :=
  ((rules.filter fun rule => decide (rule.head = atom)).map fun rule =>
    bagProduct (rule.body.map assign)).sum

/-- The `ℕ`-annotated one-step operator: sum over rules of the product over the
body. -/
def stepCount (rules : List (DefiniteRule Atom)) (count : Atom → Nat)
    (atom : Atom) : Nat :=
  ((rules.filter fun rule => decide (rule.head = atom)).map fun rule =>
    (rule.body.map count).prod).sum

/-- **Counting commutes with one step.**  So the counted reading of a definite
program *is* its `ℕ`-annotated reading: multiplicities multiply along a body and
add across rules, because the witness bag is a product along a body and a sum
across rules. -/
theorem card_stepBag (rules : List (DefiniteRule Atom))
    (assign : Atom → Multiset Witness) (atom : Atom) :
    Multiset.card (stepBag rules assign atom) =
      stepCount rules (fun other => Multiset.card (assign other)) atom := by
  simp only [stepBag, stepCount, card_listSum, List.map_map, Function.comp_def,
    card_bagProduct, List.map_map]

/-! ## Monotonicity

The step is monotone in its annotation, which is what makes the least fixpoint
exist and makes bottom-up evaluation converge. -/

omit [DecidableEq Atom] in
private theorem prod_map_le {atoms : List Atom} {first second : Atom → Nat}
    (below : ∀ atom, first atom ≤ second atom) :
    (atoms.map first).prod ≤ (atoms.map second).prod := by
  induction atoms with
  | nil => simp
  | cons atom atoms inductionHypothesis =>
      simp only [List.map_cons, List.prod_cons]
      exact Nat.mul_le_mul (below atom) inductionHypothesis

private theorem sum_map_le {Item : Type _} {items : List Item} {first second : Item → Nat}
    (below : ∀ item, first item ≤ second item) :
    (items.map first).sum ≤ (items.map second).sum := by
  induction items with
  | nil => simp
  | cons item items inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (below item) inductionHypothesis

theorem stepCount_mono (rules : List (DefiniteRule Atom))
    {first second : Atom → Nat} (below : ∀ atom, first atom ≤ second atom)
    (atom : Atom) : stepCount rules first atom ≤ stepCount rules second atom := by
  simp only [stepCount]
  exact sum_map_le fun _ => prod_map_le below

/-! ## What a set-valued backend loses -/

private def twoWaysRule (atom : Atom) : DefiniteRule Atom :=
  { body := [], head := atom }

/-- **The support quotient forgets multiplicity.**  Two rules deriving one atom
give a witness bag of two elements whose support has one, so a storage layer
keeping only presence implements strictly less than the counted semantics. -/
theorem support_forgets_multiplicity (atom : Atom) :
    Multiset.card
        (stepBag [twoWaysRule atom, twoWaysRule atom]
          (fun _ => (∅ : Multiset Unit)) atom) ≠
      (stepBag [twoWaysRule atom, twoWaysRule atom]
        (fun _ => (∅ : Multiset Unit)) atom).toFinset.card := by
  simp [stepBag, twoWaysRule]

/-- **The support quotient is exact for provability.**  It loses only *how many
ways*, never *whether*.  With the previous theorem this states precisely what a
presence-only backend implements and what it does not. -/
theorem support_faithful_for_provability (rules : List (DefiniteRule Atom))
    (assign : Atom → Multiset Witness) (atom : Atom) :
    stepBag rules assign atom ≠ 0 ↔
      0 < stepCount rules (fun other => Multiset.card (assign other)) atom := by
  rw [← card_stepBag]
  constructor
  · intro nonempty
    exact Nat.pos_of_ne_zero fun zero =>
      nonempty (Multiset.card_eq_zero.mp zero)
  · intro positive empty
    rw [empty] at positive
    simp at positive

end Mettapedia.GSLT.Core.AnnotatedHorn
