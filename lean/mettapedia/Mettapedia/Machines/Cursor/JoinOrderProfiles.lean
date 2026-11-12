import Mettapedia.Machines.Cursor.ReadScopeComposition
import Mettapedia.Machines.Cursor.LetPlacement

/-!
# Join order under caller effects, and a current-joint alternative

A Boolean relation over two finite read regions has a commutative completed
bag when both regions are fixed. The same exchange is observable for nested
read scopes when the caller changes a region between answers. Even changing
the order of stored rows can then change which answers occur.

The final selector is a distinct profile: on each request it searches for
an unreported pair that satisfies the relation in the current world. It stops
at the first such pair without constructing the whole product. Its keys denote
occurrence identities, so its seen list tracks identities rather than payload
equality. Native indexing, ordering policy, identity allocation and cost are
not proved here. In particular this is not an unconditional replacement for
either a snapshot query or the nested source computation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.JoinOrderProfiles

open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Trace Search)
open ReadScopeComposition

variable {A B : Type}

def reversedJoined (relation : A → B → Bool) (left : List A) (right : List B) : List (A × B) :=
  right.flatMap fun second => (left.filter fun first => relation first second).map (·, second)

/-- The result bag of a fixed relational join is unchanged by exchanging
the two enumeration axes. This does not identify ordered streams. -/
theorem fixed_join_bag_commutes (relation : A → B → Bool) (left : List A) (right : List B) :
    (joined relation left right).Perm (reversedJoined relation left right) := by
  have axes := LetPlacement.matrix_bag_agreement left right (fun first second => (first, second))
  have filtered := axes.filter (fun pair => relation pair.1 pair.2)
  simpa [LetPlacement.innerMatrix, LetPlacement.outerMatrix, joined, selected,
    reversedJoined, List.filter_flatMap, List.filter_map, Function.comp_def] using filtered

def rightFirst (relation : A → B → Bool) : Search (World A B) (A × B) := fun world =>
  ((Search.superpose world.right).bind fun second current =>
    Search.superpose ((current.left.filter fun first => relation first second).map (·, second)) current)
    world

namespace Controls

open ReadScopeComposition.Controls

def bFirst : World Nat Nat := ⟨[1, 0], [0]⟩

theorem changing_conjunct_order_changes_answers :
    ((composed sameKey).bind addRight adding).drain.1 = [0, 1] ∧
      ((rightFirst sameKey).bind addRight adding).drain.1 = [0] := by decide

theorem changing_fact_order_changes_answers :
    ((composed sameKey).bind addRight bFirst).drain.1 = [0] ∧
      ((composed sameKey).bind addRight bFirst).drain.2 = ⟨[1, 0], [0, 1]⟩ := by decide

def removedLeft : World Nat Nat := ⟨[0], [0]⟩
def newRight : World Nat Nat := ⟨[0], [0, 1]⟩

def replaceAcrossRegions (pair : Nat × Nat) : Search (World Nat Nat) Nat := fun world =>
  .answer pair.1 ⟨world.left.filter (· != 1), world.right ++ [1]⟩ .done

def jointlyPresent (key : Nat) (world : World Nat Nat) : Prop :=
  key ∈ world.left ∧ key ∈ world.right

/-- The outer row is retained from before its deletion. The later inner
read sees the inserted counterpart. No state in this concrete schedule has
both rows for key1, yet the nested query returns1. -/
theorem nested_answer_can_combine_different_times :
    ((composed sameKey).bind replaceAcrossRegions adding).drain = ([0, 1], ⟨[0], [0, 1, 1]⟩) ∧
      (∀ world ∈ [adding, removedLeft, newRight, (⟨[0], [0, 1, 1]⟩ : World Nat Nat)],
        ¬ jointlyPresent 1 world) := by
  constructor
  · decide
  · simp [jointlyPresent, adding, removedLeft, newRight]

theorem stable_order_changes_only_order_in_this_control :
    (composed sameKey (⟨[0, 1], [0, 1]⟩ : World Nat Nat)).drain.1 = [(0, 0), (1, 1)] ∧
      (composed sameKey (⟨[1, 0], [0, 1]⟩ : World Nat Nat)).drain.1 = [(1, 1), (0, 0)] := by decide

end Controls

variable [DecidableEq A] [DecidableEq B]

def rightChoice (relation : A → B → Bool) (seen : List (A × B)) (first : A) :
    List B → Option (A × B)
  | [] => none
  | second :: later =>
      if relation first second = true ∧ (first, second) ∉ seen then some (first, second)
      else rightChoice relation seen first later

def currentChoice (relation : A → B → Bool) (seen : List (A × B)) :
    List A → List B → Option (A × B)
  | [], _ => none
  | first :: later, right =>
      match rightChoice relation seen first right with
      | some pair => some pair
      | none => currentChoice relation seen later right

theorem rightChoice_sound (relation : A → B → Bool) (seen : List (A × B))
    (first : A) (right : List B) (pair : A × B)
    (found : rightChoice relation seen first right = some pair) :
    pair.1 = first ∧ pair.2 ∈ right ∧ relation pair.1 pair.2 = true ∧ pair ∉ seen := by
  induction right with
  | nil => simp [rightChoice] at found
  | cons second later ih =>
      by_cases eligible : relation first second = true ∧ (first, second) ∉ seen
      · simp only [rightChoice, if_pos eligible, Option.some.injEq] at found
        subst pair
        exact ⟨rfl, List.mem_cons_self, eligible⟩
      · simp only [rightChoice, if_neg eligible] at found
        obtain ⟨same, member, matched, fresh⟩ := ih found
        exact ⟨same, List.mem_cons_of_mem _ member, matched, fresh⟩

theorem rightChoice_none_iff (relation : A → B → Bool) (seen : List (A × B))
    (first : A) (right : List B) :
    rightChoice relation seen first right = none ↔
      ∀ second ∈ right, relation first second = true → (first, second) ∈ seen := by
  induction right with
  | nil => simp [rightChoice]
  | cons second later ih =>
      by_cases eligible : relation first second = true ∧ (first, second) ∉ seen
      · simp [rightChoice, eligible]
      · simp only [rightChoice, if_neg eligible, ih, List.forall_mem_cons]
        have head : relation first second = true → (first, second) ∈ seen := by tauto
        tauto

/-- Every selected pair satisfies both reads at this request's world and
has not already been reported. The proof supplies no cold revalidation pass
after the selector has established those facts. -/
theorem currentChoice_sound (relation : A → B → Bool) (seen : List (A × B))
    (left : List A) (right : List B) (pair : A × B)
    (found : currentChoice relation seen left right = some pair) :
    pair.1 ∈ left ∧ pair.2 ∈ right ∧ relation pair.1 pair.2 = true ∧ pair ∉ seen := by
  induction left with
  | nil => simp [currentChoice] at found
  | cons first later ih =>
      cases chosen : rightChoice relation seen first right with
      | none =>
          simp only [currentChoice, chosen] at found
          obtain ⟨member, rest⟩ := ih found
          exact ⟨List.mem_cons_of_mem _ member, rest⟩
      | some candidate =>
          simp only [currentChoice, chosen, Option.some.injEq] at found
          subst candidate
          obtain ⟨same, rest⟩ := rightChoice_sound relation seen first right pair chosen
          exact ⟨List.mem_cons.mpr (Or.inl same), rest⟩

theorem currentChoice_none_iff (relation : A → B → Bool) (seen : List (A × B))
    (left : List A) (right : List B) :
    currentChoice relation seen left right = none ↔
      ∀ first ∈ left, ∀ second ∈ right,
        relation first second = true → (first, second) ∈ seen := by
  induction left with
  | nil => simp [currentChoice]
  | cons first later ih =>
      cases chosen : rightChoice relation seen first right with
      | none =>
          have head := (rightChoice_none_iff relation seen first right).mp chosen
          simp only [currentChoice, chosen, ih, List.forall_mem_cons]
          tauto
      | some pair =>
          obtain ⟨same, member, matched, fresh⟩ := rightChoice_sound relation seen first right pair chosen
          simp only [currentChoice, chosen, reduceCtorEq, false_iff]
          intro allSeen
          exact fresh (allSeen pair.1 (List.mem_cons.mpr (Or.inl same)) pair.2 member matched)

namespace CurrentControls

open ReadScopeComposition.Controls JoinOrderProfiles.Controls

theorem current_join_can_see_new_pair :
    currentChoice sameKey [] adding.left adding.right = some (0, 0) ∧
      currentChoice sameKey [(0, 0)] adding.left [0, 1] = some (1, 1) := by decide

theorem current_join_rejects_pair_that_never_coexisted :
    currentChoice sameKey [(0, 0)] newRight.left newRight.right = none := by decide

theorem current_join_does_not_replay_reported_pair :
    currentChoice sameKey [(0, 0), (1, 1)] [0, 1] [0, 1] = none := by decide

theorem current_join_does_not_share_entry_query_contract :
    currentChoice sameKey [(0, 0)] [0, 1] [0, 1] = some (1, 1) ∧
      (wholeEntry sameKey adding).drain.1 = [(0, 0)] := by decide

end CurrentControls

end Mettapedia.Machines.Cursor.JoinOrderProfiles
