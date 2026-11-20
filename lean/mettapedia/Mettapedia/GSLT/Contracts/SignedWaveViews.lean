import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Waves
import Mathlib.Tactic.Ring

/-!
# Signed edits of an admitted occurrence wave

An occurrence is present with weight one or absent with weight zero.
An admitted take contributes minus one and a fresh make plus one.
Pairwise clash exclusion makes the effect of an amalgamated wave the
sum of the effects of its members. The shared pre-state is included
once, not once per branch.

This is a bridge from the snapshot step to an incremental view of its
result. The view example is a bilinear join; recursive maintenance is
not part of the bridge. Neither the signed patch nor view arithmetic
decides which candidates were legal at the cut.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.SignedWaveViews

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {Occurrence Row : Type*} [DecidableEq Occurrence]

def weight (live : Finset Occurrence) (row : Occurrence) : Int :=
  if row ∈ live then 1 else 0

def edit (c : Commit Occurrence Row) (row : Occurrence) : Int :=
  weight c.made row - weight c.taken row

theorem fire_weight {label : Occurrence → Row} {store : Finset Occurrence} {c : Commit Occurrence Row}
    (admitted : Enabled label store c) (row : Occurrence) :
    weight (fire store c) row = weight store row + edit c row := by
  by_cases taken : row ∈ c.taken
  · have live := admitted.taken_subset taken
    have notMade : row ∉ c.made := fun made => Finset.disjoint_left.mp admitted.fresh made live
    simp [weight, edit, mem_fire, taken, live, notMade]
  · by_cases made : row ∈ c.made
    · have notLive : row ∉ store := Finset.disjoint_left.mp admitted.fresh made
      simp [weight, edit, mem_fire, taken, made, notLive]
    · simp [weight, edit, mem_fire, taken, made]

private theorem weight_union {first second : Finset Occurrence} (apart : Disjoint first second)
    (row : Occurrence) : weight (first ∪ second) row = weight first row + weight second row := by
  by_cases lhs : row ∈ first
  · have rhs : row ∉ second := Finset.disjoint_left.mp apart lhs
    simp [weight, lhs, rhs]
  · simp [weight, lhs]

def sumEdits (wave : List (Commit Occurrence Row)) (row : Occurrence) : Int :=
  (wave.map (fun c => edit c row)).sum

theorem amalgamate_edit_eq_sum (wave : List (Commit Occurrence Row))
    (noClash : wave.Pairwise (fun c d => ¬ Clash c d)) (row : Occurrence) :
    edit (amalgamate wave) row = sumEdits wave row := by
  induction wave with
  | nil => simp [edit, amalgamate, takenOf, madeOf, weight, sumEdits]
  | cons c rest ih =>
      obtain ⟨each, noClashRest⟩ := List.pairwise_cons.mp noClash
      have writesApart : Disjoint c.made (madeOf rest) := by
        refine Finset.disjoint_left.mpr fun row localMade possible => ?_
        obtain ⟨d, inRest, foreignMade⟩ := mem_madeOf.mp possible
        have separate : Disjoint c.made d.made := by
          classical
          exact Classical.not_not.mp (fun conflict => each d inRest (Or.inr conflict))
        exact Finset.disjoint_left.mp separate localMade foreignMade
      have takesApart : Disjoint c.taken (takenOf rest) := by
        refine Finset.disjoint_left.mpr fun row localTake possible => ?_
        obtain ⟨d, inRest, foreignTake⟩ := mem_takenOf.mp possible
        have separate : Disjoint c.taken d.taken := by
          classical
          exact Classical.not_not.mp (fun conflict => each d inRest (Or.inl conflict))
        exact Finset.disjoint_left.mp separate localTake foreignTake
      change weight (c.made ∪ madeOf rest) row - weight (c.taken ∪ takenOf rest) row =
        edit c row + sumEdits rest row
      rw [weight_union writesApart, weight_union takesApart, ← ih noClashRest]
      simp only [edit, amalgamate]
      ring

/-- Add the effects, not the final snapshots. Associativity and
commutativity concern this observation of the admitted wave. -/
theorem wave_weight {label : Occurrence → Row} {store : Finset Occurrence}
    {wave : List (Commit Occurrence Row)} (admitted : EveryEnabled label store wave)
    (row : Occurrence) :
    weight (fire store (amalgamate wave)) row = weight store row + sumEdits wave row := by
  rw [fire_weight admitted.2.2, amalgamate_edit_eq_sum wave admitted.2.1]

def join (fits : Occurrence → Occurrence → Bool) (left right : Occurrence → Int)
    (p q : Occurrence) : Int :=
  if fits p q then left p * right q else 0

def joinEdit (fits : Occurrence → Occurrence → Bool) (left right dl dr : Occurrence → Int)
    (p q : Occurrence) : Int :=
  join fits dl right p q + join fits left dr p q + join fits dl dr p q

omit [DecidableEq Occurrence] in
theorem join_update (fits : Occurrence → Occurrence → Bool) (left right dl dr : Occurrence → Int)
    (p q : Occurrence) :
    join fits left right p q + joinEdit fits left right dl dr p q =
      join fits (fun o => left o + dl o) (fun o => right o + dr o) p q := by
  unfold joinEdit join
  cases fits p q <;> simp
  ring

/-- One update of a correct cache is the join evaluated from the
committed store. The same result holds for any admitted serialization
by the existing occurrence-wave theorem. -/
theorem view_after_wave (fits : Occurrence → Occurrence → Bool)
    {label : Occurrence → Row} {store : Finset Occurrence} {wave : List (Commit Occurrence Row)}
    (admitted : EveryEnabled label store wave) {cache : Occurrence → Occurrence → Int}
    (exactBefore : cache = join fits (weight store) (weight store)) :
    (fun p q => cache p q + joinEdit fits (weight store) (weight store)
      (sumEdits wave) (sumEdits wave) p q) =
      join fits (weight (fire store (amalgamate wave))) (weight (fire store (amalgamate wave))) := by
  funext p q
  rw [exactBefore, join_update]
  simp only [join, wave_weight admitted]

/-- Maintain the same join along a sequence of committed edits. The
update uses the old input and the edit, not a recomputed join. -/
def maintain (fits : Occurrence → Occurrence → Bool) (store : Finset Occurrence)
    (cache : Occurrence → Occurrence → Int) : List (Commit Occurrence Row) → Occurrence → Occurrence → Int
  | [] => cache
  | c :: rest => maintain fits (fire store c)
      (fun p q => cache p q + joinEdit fits (weight store) (weight store) (edit c) (edit c) p q) rest

theorem maintain_eq_recompute (fits : Occurrence → Occurrence → Bool)
    {label : Occurrence → Row} {store : Finset Occurrence} {plan : List (Commit Occurrence Row)}
    (run : Executable label store plan) (cache : Occurrence → Occurrence → Int)
    (exactBefore : cache = join fits (weight store) (weight store)) :
    maintain fits store cache plan =
      join fits (weight (fireList store plan)) (weight (fireList store plan)) := by
  induction run generalizing cache with
  | nil _ => exact exactBefore
  | cons admitted _ ih =>
      rw [maintain, fireList_cons]
      apply ih
      funext p q
      rw [exactBefore, join_update]
      simp only [join, fire_weight admitted]

namespace Controls

private def initial : Finset Nat := {0, 1}
private def takes : Commit Nat Unit := ⟨{0, 1}, ∅, ∅, []⟩
private def cross (a b : Nat) : Bool := a == 0 && b == 1

theorem simultaneous_takes_need_cross_term :
    join cross (weight initial) (weight initial) 0 1 +
      joinEdit cross (weight initial) (weight initial) (edit takes) (edit takes) 0 1 = 0 ∧
    join cross (weight initial) (weight initial) 0 1 +
      join cross (edit takes) (weight initial) 0 1 +
      join cross (weight initial) (edit takes) 0 1 = -1 := by
  decide

theorem summing_final_snapshots_counts_the_base_twice :
    weight initial 0 + weight initial 0 ≠ weight initial 0 := by
  decide

end Controls

#print axioms fire_weight
#print axioms amalgamate_edit_eq_sum
#print axioms wave_weight
#print axioms join_update
#print axioms view_after_wave
#print axioms maintain_eq_recompute
#print axioms Controls.simultaneous_takes_need_cross_term
#print axioms Controls.summing_final_snapshots_counts_the_base_twice

end Mettapedia.GSLT.Contracts.SignedWaveViews
