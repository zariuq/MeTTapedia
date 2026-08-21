import Mettapedia.GSLT.Parsing.FiniteHornSaturation

/-!
# Pointwise fact projections erase list structure

A pointwise fact projection maps each list element to a finite set of facts and
unions those contributions. Consequently, it forgets both order and
multiplicity before any downstream semantics runs. A positive finite-Horn
program consuming that fact set cannot recover either distinction.

This file proves the exact obstruction. If a Boolean verdict distinguishes two
lists with the same members, no pointwise fact projection followed by the
project's finite-Horn saturation semantics computes that verdict. Duplication
and permutation are useful corollaries.

This is not a limitation of Horn logic in general. An encoding may preserve
order by adding positions, prefixes, or transitions to its facts. The theorem
says that such structure is necessary whenever the source verdict observes
it; a position-free set projection does not make the structure disappear.
-/

namespace Mettapedia.GSLT.Parsing.PointwiseProjection

open Mettapedia.Logic.LP
open Mettapedia.GSLT.Parsing.FiniteHornSaturation

/-! ## Pointwise projection

A pointwise projection lets each element contribute facts independently of its
position and occurrence count. The atom vocabulary is arbitrary. -/

structure PointwiseFactProjection (Item : Type*) (α : Type*) [DecidableEq α] where
  /-- The definite program interpreting the encoded facts. -/
  program : PropProgram α
  /-- Per-item, position-free, multiplicity-free fact contribution. -/
  encode : Item → Finset α
  /-- The acceptance goal. -/
  goal : α

variable {Item : Type*} {α : Type*} [DecidableEq α]

/-- The fact base of a list: the union of its items' contributions. -/
def factsOf (E : PointwiseFactProjection Item α) : List Item → Finset α
  | [] => ∅
  | x :: xs => E.encode x ∪ factsOf E xs

theorem mem_factsOf {E : PointwiseFactProjection Item α} {a : α} :
    ∀ {xs : List Item}, a ∈ factsOf E xs ↔ ∃ x ∈ xs, a ∈ E.encode x
  | [] => by simp [factsOf]
  | x :: xs => by
      simp [factsOf, Finset.mem_union, mem_factsOf (xs := xs)]

/-- The fact base sees only membership: any two lists with the same members
project to the same facts. This is where duplication and order are
erased — before the program ever runs. -/
theorem factsOf_congr {E : PointwiseFactProjection Item α} {u v : List Item}
    (hmem : ∀ s, s ∈ u ↔ s ∈ v) : factsOf E u = factsOf E v := by
  ext a
  simp only [mem_factsOf]
  constructor
  · rintro ⟨s, hs, ha⟩; exact ⟨s, (hmem s).mp hs, ha⟩
  · rintro ⟨s, hs, ha⟩; exact ⟨s, (hmem s).mpr hs, ha⟩

/-- Acceptance under a set projection: the goal saturates from the projected
facts.  `saturate` is the project's finite-Horn semantics, sound and complete
for derivability (`saturate_iff_derivable`). -/
def Accepts (E : PointwiseFactProjection Item α) (xs : List Item) : Prop :=
  E.goal ∈ saturate E.program (factsOf E xs)

/-- A projection is faithful to a verdict when saturation acceptance coincides
with the verdict on every database. -/
def Faithful (verdict : List Item → Bool)
    (E : PointwiseFactProjection Item α) : Prop :=
  ∀ xs : List Item, verdict xs = true ↔ Accepts E xs

/-! ## Structural obstruction -/

/-- **No faithful pointwise fact projection.** If a verdict distinguishes two
lists with the same members, then no such projection — over any atom type,
program, and goal — is faithful to it. -/
theorem no_faithful_pointwise_fact_projection (verdict : List Item → Bool)
    {u v : List Item} (hmem : ∀ x, x ∈ u ↔ x ∈ v)
    (hne : verdict u ≠ verdict v) :
    ¬ ∃ E : PointwiseFactProjection Item α, Faithful verdict E := by
  rintro ⟨E, hF⟩
  have hfacts : factsOf E u = factsOf E v := factsOf_congr hmem
  have hiff : verdict u = true ↔ verdict v = true := by
    rw [hF u, hF v]
    unfold Accepts
    rw [hfacts]
  cases hu : verdict u <;> cases hv : verdict v <;>
    simp_all

/-- Duplication form: a verdict that flips when an already-present statement
is repeated admits no faithful set projection. -/
theorem no_faithful_of_duplication (verdict : List Item → Bool)
    {xs : List Item} {x : Item} (hx : x ∈ xs)
    (hne : verdict xs ≠ verdict (x :: xs)) :
    ¬ ∃ E : PointwiseFactProjection Item α, Faithful verdict E :=
  no_faithful_pointwise_fact_projection verdict
    (fun t => by
      constructor
      · intro ht; exact List.mem_cons_of_mem x ht
      · intro ht
        rcases List.mem_cons.mp ht with h | h
        · exact h ▸ hx
        · exact h)
    hne

/-- Permutation form: a verdict that distinguishes two permutations of the
same statement list admits no faithful set projection. -/
theorem no_faithful_of_permutation (verdict : List Item → Bool)
    {u v : List Item} (hperm : u.Perm v)
    (hne : verdict u ≠ verdict v) :
    ¬ ∃ E : PointwiseFactProjection Item α, Faithful verdict E :=
  no_faithful_pointwise_fact_projection verdict (fun _ => hperm.mem_iff) hne

/-! ## Positive and negative examples -/

theorem saturate_empty_program (facts : Finset α) :
    Mettapedia.GSLT.Parsing.FiniteHornSaturation.saturate
        (∅ : PropProgram α) facts = facts := by
  have iterate_empty (fuel : Nat) :
      iterate (∅ : PropProgram α) facts fuel = facts := by
    induction fuel with
    | zero => rfl
    | succ fuel ih =>
        simp [iterate, step, fired, ih]
  exact iterate_empty _

/-- A verdict that depends only on membership is compatible with the
information retained by a pointwise fact projection. -/
def containsTrue (xs : List Bool) : Bool := xs.any id

/-- One explicit faithful projection for the membership-only verdict. -/
def containsTrueProjection : PointwiseFactProjection Bool Bool where
  program := ∅
  encode
    | false => ∅
    | true => {true}
  goal := true

theorem containsTrueProjection_faithful :
    Faithful containsTrue containsTrueProjection := by
  intro xs
  rw [show Accepts containsTrueProjection xs ↔
      true ∈ factsOf containsTrueProjection xs by
        simp only [Accepts, containsTrueProjection]
        rw [saturate_empty_program]]
  simp [containsTrue, mem_factsOf, containsTrueProjection]

/-- This verdict accepts exactly one occurrence of `true`. -/
def exactlyOneTrue : List Bool → Bool
  | [true] => true
  | _ => false

/-- Multiplicity-sensitive verdicts cannot factor through pointwise facts. -/
theorem exactlyOneTrue_no_faithful_projection :
    ¬ ∃ E : PointwiseFactProjection Bool α, Faithful exactlyOneTrue E :=
  no_faithful_of_duplication exactlyOneTrue (xs := [true])
    (x := true) (by simp) (by decide)

/-- This verdict accepts one particular order of two distinct items. -/
def falseBeforeTrue : List Bool → Bool
  | [false, true] => true
  | _ => false

/-- Order-sensitive verdicts cannot factor through pointwise facts. -/
theorem falseBeforeTrue_no_faithful_projection :
    ¬ ∃ E : PointwiseFactProjection Bool α, Faithful falseBeforeTrue E :=
  no_faithful_of_permutation falseBeforeTrue
    (u := [false, true]) (v := [true, false]) (by decide) (by decide)

end Mettapedia.GSLT.Parsing.PointwiseProjection
