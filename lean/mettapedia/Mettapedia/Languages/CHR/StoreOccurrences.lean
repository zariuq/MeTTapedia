import Mettapedia.Languages.CHR.Refinement
import Mathlib.Logic.Relation

/-! Occurrence identity under the refined relation. A step keeps or removes
store occurrences and adds at most the occurrence it introduces, at the
state's next identifier; it never changes the constraint of an identifier.
Along any run from a well-formed state, two store occurrences with the same
identifier are therefore the same occurrence. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.StoreOccurrences

/-- Each later store occurrence is an earlier one or is new at `nextId`. -/
theorem step_store {program : Program} {first second : State} (step : Step program first second) :
    ∀ occurrence ∈ second.store, occurrence ∈ first.store ∨ occurrence.id = first.nextId := by
  intro occurrence member
  cases step with
  | introduce environment head goals tail constraint tasks running grounded =>
    rcases List.mem_append.mp member with old | new
    · exact .inl old
    · exact .inr (by rw [List.mem_singleton.mp new])
  | fire active cursor tail occurrence' rule environment selection tasks running atCursor atRule
      matched activeHead fresh guarded =>
    left
    have sub : List.Sublist (selection.kept ++ selection.rest)
        (selection.kept ++ selection.removed ++ selection.rest) :=
      (List.sublist_append_left selection.kept selection.removed).append_right selection.rest
    exact matched.1.mem_iff.mpr (sub.mem member)
  | _ => exact .inl member

theorem step_nextId {program : Program} {first second : State} (step : Step program first second) :
    first.nextId ≤ second.nextId := by
  cases step with
  | introduce => exact Nat.le_succ _
  | fire => exact Nat.le_refl _
  | _ => exact Nat.le_refl _

theorem run_nextId {program : Program} {first second : State}
    (run : Relation.ReflTransGen (Step program) first second) : first.nextId ≤ second.nextId := by
  induction run with
  | refl => exact Nat.le_refl _
  | tail _ step previous => exact Nat.le_trans previous (step_nextId step)

theorem run_wellFormed {program : Program} {first second : State}
    (run : Relation.ReflTransGen (Step program) first second) (formed : first.WellFormed) :
    second.WellFormed := by
  induction run with
  | refl => exact formed
  | tail _ step previous => exact step.wellFormed previous

theorem same_id_same_occurrence {store : List Occurrence} (distinct : (store.map Occurrence.id).Nodup)
    {first second : Occurrence} (firstMember : first ∈ store) (secondMember : second ∈ store)
    (same : first.id = second.id) : first = second := by
  induction store with
  | nil => simp at firstMember
  | cons head rest ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at distinct
    rcases List.mem_cons.mp firstMember with rfl | firstRest <;>
      rcases List.mem_cons.mp secondMember with rfl | secondRest
    · rfl
    · exact absurd same.symm (distinct.1 second secondRest)
    · exact absurd same (distinct.1 first firstRest)
    · exact ih distinct.2 firstRest secondRest

/-- An identifier keeps its occurrence along every run. -/
theorem identifier_stable {program : Program} {first second : State}
    (run : Relation.ReflTransGen (Step program) first second) (formed : first.WellFormed)
    {earlier later : Occurrence} (earlierMember : earlier ∈ first.store) (laterMember : later ∈ second.store)
    (same : earlier.id = later.id) : earlier = later := by
  induction run generalizing later with
  | refl => exact same_id_same_occurrence formed.1 earlierMember laterMember same
  | tail before step previous =>
    rcases step_store step later laterMember with kept | new
    · exact previous kept same
    · have bound := Nat.lt_of_lt_of_le (formed.2 earlier earlierMember) (run_nextId before)
      omega

#print axioms identifier_stable

end Mettapedia.Languages.CHR.StoreOccurrences
