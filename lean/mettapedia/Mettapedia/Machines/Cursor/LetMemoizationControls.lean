import Mettapedia.Machines.Cursor.LetMemoization
import Mettapedia.Machines.Cursor.LetPlacement
import Mettapedia.Machines.Cursor.Fold

/-! # Sharing a choice description keeps independent per-candidate choice -/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.LetMemoization.Controls

abbrev Item := Nat × List Nat

def build (_ : Unit) : List Nat := [1, 2]
def consume (prior : List Item) (item : Item) : List Item := prior ++ [item]
def client := Fold.client consume

def answer (M : Provider (Sequence.protocol Item)) :
    Outcome M client () → Option (List Item)
  | .paused _ => none
  | .done completed => some completed.2.1

def memoPacket := Fold.start (memoized (Row := Nat) build) consume (start build [10, 20]) []
def sourcePacket := Fold.start (repeated (Row := Nat) build) consume [10, 20] []
def memoRun := advance (memoized build) client (memoizedCalls build) 4 memoPacket
def sourceRun := advance (repeated build) client (repeatedCalls build) 4 sourcePacket

theorem same_candidate_descriptions :
    answer _ memoRun.2 = some [(10, [1, 2]), (20, [1, 2])] ∧
      answer _ sourceRun.2 = answer _ memoRun.2 := by decide

theorem builder_count_changes_not_choice_scope : memoRun.1 = 1 ∧ sourceRun.1 = 2 := by decide

def expand (items : List Item) : List (Nat × Nat) :=
  items.flatMap (fun item => item.2.map (fun value => (item.1, value)))

/-- Each row still gets all its alternatives, in row-major order. A shared
chosen value for the whole call would produce a different ordered stream. -/
theorem shared_description_is_not_outer_choice :
    (answer _ memoRun.2).map expand =
      some (LetPlacement.innerMatrix [10, 20] [1, 2] Prod.mk) ∧
    (answer _ memoRun.2).map expand ≠
      some (LetPlacement.outerMatrix [10, 20] [1, 2] Prod.mk) := by decide

def paused := advance (memoized build) client (memoizedCalls build) 1 memoPacket
def resumed := resume (memoized build) client (memoizedCalls build) 3 paused

theorem retained_memo_does_not_build_again :
    paused.1 = 1 ∧ resumed.1 = 1 ∧ answer _ resumed.2 = answer _ memoRun.2 := by decide

theorem empty_candidates_do_not_build :
    let stopped := advance (memoized (Row := Nat) build) client (memoizedCalls build) 2
      (Fold.start _ consume (start build []) [])
    stopped.1 = 0 ∧ answer _ stopped.2 = some [] := by decide

theorem wrong_cached_recipe_is_not_licensed (cell : Cell build) : cell.saved ≠ some [999] := by
  intro wrong
  have correct := cell.correct [999] wrong
  simp [build] at correct

theorem call_savings_do_not_pay_every_overhead :
    @priced Nat (List Nat) build 10 2 1 () () (start build [10, 20]) () = 13 ∧
      @repeatedCalls Nat (List Nat) build () () [10, 20] () = 1 := by decide

#print axioms observation
#print axioms builder_calls_le_one
#print axioms calls_le_source
#print axioms first_request_can_cost_more

end Mettapedia.Machines.Cursor.LetMemoization.Controls
