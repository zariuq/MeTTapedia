import Mathlib.Data.List.Basic
import Mathlib.Data.List.Flatten

/-!
# Exact ordered prefiltering

Each occurrence in a fixed source word has an independent observation,
possibly empty or producing several results. An ordered candidate
subword gives exactly the original observations if and only if it
retains the subword of all contributing occurrences.

This is a law for a fixed per-occurrence producer. It does not license
reordering effects, changing the producer after a state update, or
deduplicating rows with equal payloads.
-/

set_option autoImplicit false

namespace Mettapedia.Data.List.OrderedPrefilter

variable {Row Answer : Type*}

def contributes (observe : Row → List Answer) (row : Row) : Bool :=
  !(observe row).isEmpty

@[simp] theorem contributes_iff (observe : Row → List Answer) (row : Row) :
    contributes observe row = true ↔ observe row ≠ [] := by
  cases emitted : observe row <;> simp [contributes, emitted]

private theorem flatMap_filter_contributes (observe : Row → List Answer) (rows : List Row) :
    (rows.filter (contributes observe)).flatMap observe = rows.flatMap observe := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      cases emitted : observe row <;>
        simp [List.flatMap_cons, contributes, emitted, ih]

/-- For any ordered candidate subword, exact answers are equivalent to
retaining every contributing occurrence in order. Neither source row
equality nor answer equality need be decidable. -/
theorem flatMap_eq_iff (observe : Row → List Answer)
    {candidates source : List Row} (ordered : candidates.Sublist source) :
    candidates.flatMap observe = source.flatMap observe ↔
      (source.filter (contributes observe)).Sublist candidates := by
  constructor
  · intro exact
    induction ordered with
    | slnil => exact List.Sublist.slnil
    | cons row remaining ih =>
        cases emitted : observe row with
        | nil =>
            have tail := ih (by simpa only [List.flatMap_cons, emitted, List.nil_append] using exact)
            simpa [contributes, emitted] using tail
        | cons answer rest =>
            have shorter := (remaining.flatMap observe).length_le
            have sameLength := congrArg List.length exact
            simp only [List.flatMap_cons, List.length_append, emitted, List.length_cons] at sameLength
            omega
    | cons_cons row remaining ih =>
        have sameTail := List.append_cancel_left (by simpa only [List.flatMap_cons] using exact)
        cases emitted : observe row with
        | nil => simpa [contributes, emitted] using List.Sublist.cons row (ih sameTail)
        | cons answer rest =>
            simpa [contributes, emitted] using List.Sublist.cons_cons row (ih sameTail)
  · intro covers
    apply (ordered.flatMap observe).antisymm
    simpa only [flatMap_filter_contributes] using covers.flatMap observe

/-- For a Boolean filter the subword obligation is a local implication on
rows in the source word. -/
theorem filter_filter_eq_iff (keep accept : Row → Bool) (rows : List Row) :
    (rows.filter keep).filter accept = rows.filter accept ↔
      ∀ row ∈ rows, accept row = true → keep row = true := by
  have commutes : (rows.filter keep).filter accept = (rows.filter accept).filter keep := by
    simp only [List.filter_filter, Bool.and_comm]
  rw [commutes, List.filter_eq_self]
  exact ⟨fun covered row member accepted =>
    covered row (List.mem_filter.mpr ⟨member, accepted⟩),
    fun covered row member =>
      covered row (List.mem_filter.mp member).1 (List.mem_filter.mp member).2⟩

theorem filter_candidates (keep accept : Row → Bool)
    (covers : ∀ row, accept row = true → keep row = true) (rows : List Row) :
    (rows.filter keep).filter accept = rows.filter accept :=
  (filter_filter_eq_iff keep accept rows).mpr fun row _ => covers row

theorem filter_flatMap_eq_iff (keep : Row → Bool) (observe : Row → List Answer) (rows : List Row) :
    (rows.filter keep).flatMap observe = rows.flatMap observe ↔
      ∀ row ∈ rows, observe row ≠ [] → keep row = true := by
  rw [flatMap_eq_iff observe List.filter_sublist]
  constructor
  · intro covered row member emits
    exact (List.mem_filter.mp (covered.subset
      (List.mem_filter.mpr ⟨member, (contributes_iff _ _).mpr emits⟩))).2
  · intro covered
    have same := (filter_filter_eq_iff keep (contributes observe) rows).mpr fun row member emits =>
      covered row member ((contributes_iff _ _).mp emits)
    rw [← same]
    exact List.filter_sublist

/-- A deterministic exact matcher is the zero-or-one-answer instance. -/
theorem filter_filterMap_eq (keep : Row → Bool) (observe : Row → Option Answer) (rows : List Row)
    (covers : ∀ row ∈ rows, ∀ answer, observe row = some answer → keep row = true) :
    (rows.filter keep).filterMap observe = rows.filterMap observe := by
  rw [List.filterMap_eq_flatMap_toList, List.filterMap_eq_flatMap_toList]
  apply (filter_flatMap_eq_iff keep (fun row => (observe row).toList) rows).mpr
  intro row member emits
  cases found : observe row with
  | none => simp [found] at emits
  | some answer => exact covers row member answer found

namespace Controls

private def emit (row : Nat) : List Nat :=
  if row = 0 then [7, 8] else if row = 1 then [9] else []

theorem ordered_pruning_retains_every_answer :
    ([0, 1, 0] : List Nat).flatMap emit = [0, 2, 1, 0].flatMap emit :=
  (flatMap_eq_iff emit (by decide : [0, 1, 0].Sublist [0, 2, 1, 0])).mpr (by decide)

/-- Value membership cannot detect a lost duplicate occurrence. -/
theorem matched_value_membership_is_not_enough :
    (∀ row ∈ [0, 1, 0], row ∈ ([0, 1] : List Nat)) ∧
    ([0, 1] : List Nat).flatMap emit ≠ [0, 1, 0].flatMap emit := by
  constructor
  · simp
  · decide

end Controls

#print axioms flatMap_eq_iff
#print axioms filter_filter_eq_iff
#print axioms filter_flatMap_eq_iff
#print axioms filter_filterMap_eq
#print axioms Controls.ordered_pruning_retains_every_answer
#print axioms Controls.matched_value_membership_is_not_enough

end Mettapedia.Data.List.OrderedPrefilter
