import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Charge
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.OrderedStore

/-!
# Consumable budgets on actual admitted transform runs

A natural-valued conserved charge bounds the number of firings that each spend
at least one credit and create none. This is an explicit resource profile, not
a restriction on the ambient calculus. The occurrence instance counts selected
payloads in the real ordered store, using the existing weight charge and run.

Update credits do not bound matching, failed candidates, reads or CPU work.
Replenishment can permit further work; reaching zero credits is not a fixed
point of every operation. These laws do not insert a runtime counting pass.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ConsumableBudget

universe uObj uTm uHom uOcc uState uFiring

variable {Obj : Type uObj} {Tm : Obj → Type uTm} {Hom : Obj → Obj → Type uHom}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uState} {Firing : State → Type uFiring}
  {P : Step X O State Firing}

theorem made_total_zero (charge : ConservedCharge P Nat) {state : State} (run : P.Run state)
    (noneMade : ∀ event ∈ run.word, charge.made event.1 event.2 = 0) :
    charge.runMade run = 0 := by
  induction run with
  | nil => rfl
  | @cons state firing admitted rest ih =>
      have first := noneMade ⟨state, firing⟩ (by simp [Step.Run.word])
      have later := ih (fun event member => noneMade event (by simp [Step.Run.word, member]))
      change charge.made state firing + charge.runMade rest = 0
      rw [first, later]

theorem length_le_taken (charge : ConservedCharge P Nat) {state : State} (run : P.Run state)
    (spending : ∀ event ∈ run.word, 0 < charge.taken event.1 event.2) :
    run.word.length ≤ charge.runTaken run := by
  induction run with
  | nil => exact Nat.le_refl 0
  | @cons state firing admitted rest ih =>
      have first := spending ⟨state, firing⟩ (by simp [Step.Run.word])
      change 0 < charge.taken state firing at first
      have later := ih (fun event member => spending event (by simp [Step.Run.word, member]))
      change rest.word.length + 1 ≤ charge.taken state firing + charge.runTaken rest
      omega

/-- This applies to every finite prefix, because the argument is the actual
admitted run, not an assumption that its producer has been exhausted. -/
theorem length_le_initial (charge : ConservedCharge P Nat) {state : State} (run : P.Run state)
    (spending : ∀ event ∈ run.word,
      0 < charge.taken event.1 event.2 ∧ charge.made event.1 event.2 = 0) :
    run.word.length ≤ charge.potential state := by
  have consumed := length_le_taken charge run (fun event member => (spending event member).1)
  have noGeneration := made_total_zero charge run (fun event member => (spending event member).2)
  have balance := charge.run_balance run
  omega

/-- Count credit-spending events while allowing uncharged reads and routing
between them. No such event is deleted from the underlying run. -/
def spendingCount (charge : ConservedCharge P Nat) : {state : State} → P.Run state → Nat
  | _, .nil _ => 0
  | state, .cons firing _ rest =>
      (if 0 < charge.taken state firing then 1 else 0) + spendingCount charge rest

theorem spending_count_le_taken (charge : ConservedCharge P Nat) {state : State} (run : P.Run state) :
    spendingCount charge run ≤ charge.runTaken run := by
  induction run with
  | nil => exact Nat.le_refl 0
  | @cons state firing admitted rest ih =>
      change (if 0 < charge.taken state firing then 1 else 0) + spendingCount charge rest ≤
        charge.taken state firing + charge.runTaken rest
      split <;> omega

theorem spending_count_eq_filter (charge : ConservedCharge P Nat) {state : State} (run : P.Run state) :
    spendingCount charge run =
      (run.word.filter fun event => decide (0 < charge.taken event.1 event.2)).length := by
  induction run with
  | nil => rfl
  | @cons state firing admitted rest ih =>
      by_cases spent : 0 < charge.taken state firing <;>
        simp [spendingCount, Step.Run.word, spent, ih, Nat.add_comm]

/-- A branch can have several ordered publication events. Only the events
that spend credits count toward the update budget; all their effects remain. -/
theorem spending_count_bound (charge : ConservedCharge P Nat) {state : State} (run : P.Run state)
    (noneMade : ∀ event ∈ run.word, charge.made event.1 event.2 = 0) :
    spendingCount charge run ≤ charge.potential state := by
  have consumed := spending_count_le_taken charge run
  have noGeneration := made_total_zero charge run noneMade
  have balance := charge.run_balance run
  omega

theorem no_spending_at_zero (charge : ConservedCharge P Nat) {state : State} (firing : Firing state)
    (empty : charge.potential state = 0) (spends : 0 < charge.taken state firing)
    (noneMade : charge.made state firing = 0) : ¬ P.Admits firing := by
  intro admitted
  have balance := charge.balance firing admitted
  omega

section Occurrences

variable (X : Frames Tm Hom) (a : Obj) (label : O → Tm a) (isCredit : Tm a → Bool)

def credits : ConservedCharge (OrderedStore.step X a label) Nat :=
  weightCharge (OrderedStore.step X a label) fun occurrence => if isCredit (label occurrence) then 1 else 0

private theorem weighted_count (predicate : O → Bool) (rows : List O) (unique : rows.Nodup) :
    (∑ occurrence ∈ rows.toFinset, if predicate occurrence then 1 else 0 : Nat) =
      (rows.filter predicate).length := by
  rw [Finset.sum_boole, ← List.toFinset_filter, List.toFinset_card_of_nodup (unique.filter predicate)]
  simp

theorem potential_counts_rows (state : OrderedStore.State (Tm := Tm) a O) (unique : state.2.Nodup) :
    (credits X a label isCredit).potential state =
      (state.2.filter fun occurrence => isCredit (label occurrence)).length :=
  weighted_count _ _ unique

theorem selected_credit_spends (state : OrderedStore.State (Tm := Tm) a O)
    (request : OrderedStore.Publication (Tm a) O)
    (selected : ∃ occurrence ∈ request.selection.taken, isCredit (label occurrence) = true) :
    0 < (credits X a label isCredit).taken state request := by
  rcases selected with ⟨occurrence, member, credit⟩
  change 0 < (∑ item ∈ request.selection.taken.toFinset,
    if isCredit (label item) then 1 else 0 : Nat)
  apply Finset.sum_pos_iff.mpr
  exact ⟨occurrence, List.mem_toFinset.mpr member, by simp [credit]⟩

theorem no_credit_made (state : OrderedStore.State (Tm := Tm) a O)
    (request : OrderedStore.Publication (Tm a) O)
    (noneMade : ∀ occurrence ∈ request.selection.made, isCredit (label occurrence) = false) :
    (credits X a label isCredit).made state request = 0 := by
  change (∑ item ∈ request.selection.made.toFinset,
    if isCredit (label item) then 1 else 0 : Nat) = 0
  apply Finset.sum_eq_zero
  intro occurrence member
  simp [noneMade occurrence (List.mem_toFinset.mp member)]

/-- A source resource policy supplies one real selected credit per update.
The resulting bound is derived from occurrence conservation, not assumed as
part of admission or as an evaluator-equivalence hypothesis. -/
theorem update_count_bound (state : OrderedStore.State (Tm := Tm) a O)
    (unique : state.2.Nodup) (run : (OrderedStore.step X a label).Run state)
    (policy : ∀ event ∈ run.word,
      (∃ occurrence ∈ event.2.selection.taken, isCredit (label occurrence) = true) ∧
      (∀ occurrence ∈ event.2.selection.made, isCredit (label occurrence) = false)) :
    run.word.length ≤ (state.2.filter fun occurrence => isCredit (label occurrence)).length := by
  rw [← potential_counts_rows X a label isCredit state unique]
  apply length_le_initial
  intro event member
  exact ⟨selected_credit_spends X a label isCredit event.1 event.2 (policy event member).1,
    no_credit_made X a label isCredit event.1 event.2 (policy event member).2⟩

/-- A read is a real event that spends no credit. The update-count theorem
therefore cannot be used to bound arbitrary source transitions or reads. -/
theorem read_spends_zero (state : OrderedStore.State (Tm := Tm) a O) (read : List O) :
    (credits X a label isCredit).taken state ⟨⟨[], read, []⟩, []⟩ = 0 := by
  simp [credits, weightCharge, OrderedStore.step, OrderedStore.effect]

/-- Creating a credit changes the resource available to a later prefix; the
zero-credit refusal law does not assert that further work is impossible. -/
theorem replenishment (state : OrderedStore.State (Tm := Tm) a O)
    (request : OrderedStore.Publication (Tm a) O)
    (admitted : (OrderedStore.step X a label).Admits (s := state) request)
    (noSpend : (credits X a label isCredit).taken state request = 0)
    (made : (credits X a label isCredit).made state request = 1) :
    (credits X a label isCredit).potential ((OrderedStore.step X a label).result request admitted) =
      (credits X a label isCredit).potential state + 1 := by
  have balance := (credits X a label isCredit).balance request admitted
  omega

end Occurrences

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ConsumableBudget
