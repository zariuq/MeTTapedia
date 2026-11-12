import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ConsumableBudget
import Mettapedia.Languages.MeTTa.ContextualTransform.ConcreteStorePrograms
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaTransformDemand

/-!
# A canonical update-credit cycle in the source library and real transform step

The authored example has three jobs and two credits. Its source library run
claims two jobs. A separate target construction uses four admitted primitive
events: take, route, take, route. Its q/out projections agree with the source
observations. The conserved charge bounds spending events, not all events.

This is a concrete operational calibration, not whole-family source lowering
adequacy, named-space completeness or C correspondence. It does not fuse an
entire firing and destination evaluation into one purported atomic write.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Experimental.DerivedTransformForms.BudgetCycle

open OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Interface
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)
open ContextualTransform

def job (term : Atom) : Atom := .expression [.symbol "job", term]
def credit (term : Atom) : Atom := .expression [.symbol "credit", term]
def reply (term : Atom) : Atom := .expression [.symbol "done", term]

def sources : PeTTa.LibTransform.Sources :=
  ⟨[.pat .take (job (.var "j")), .pat .take (credit (.var "credit"))], [], none⟩

def sourceStart : List Atom :=
  [job (.symbol "a"), job (.symbol "b"), job (.symbol "c"),
    credit (.symbol "one"), credit (.symbol "two")]

def sourceResult := (PeTTa.LibTransform.transform sources (reply (.var "j")) sourceStart).drain

theorem source_budget_exact :
    sourceResult = ([reply (.symbol "a"), reply (.symbol "b")], [job (.symbol "c")]) := by
  decide +kernel

theorem source_replenished :
    (PeTTa.LibTransform.transform sources (reply (.var "j"))
      (sourceResult.2 ++ [credit (.symbol "three")])).drain = ([reply (.symbol "c")], []) := by
  rw [source_budget_exact]
  decide +kernel

/-- A zero-credit store can still do other work. Resource refusal is not a
global fixed point or an ambient-language restriction. -/
theorem unbudgeted_source_still_enabled :
    (PeTTa.LibTransform.transform ⟨[.pat .take (job (.var "j"))], [], none⟩
      (reply (.var "j")) [job (.symbol "c")]).drain = ([reply (.symbol "c")], []) := by
  decide +kernel

def atRegion (region : String) (term : Atom) : Atom :=
  .expression [.symbol "at", .symbol region, term]

def label : Nat → Atom
  | 0 => atRegion "q" (job (.symbol "a"))
  | 1 => atRegion "q" (job (.symbol "b"))
  | 2 => atRegion "q" (job (.symbol "c"))
  | 3 => atRegion "q" (credit (.symbol "one"))
  | 4 => atRegion "q" (credit (.symbol "two"))
  | 5 => atRegion "out" (reply (.symbol "a"))
  | 6 => atRegion "out" (reply (.symbol "b"))
  | other => .expression [.symbol "unused", .grounded (.int other)]

def actualStep : Step PeTTaStoreSelection.atomFrames Nat
    (EquationStore Atom × List Nat) (fun _ => OrderedStore.Publication Atom Nat) :=
  OrderedStore.step PeTTaStoreSelection.atomFrames PUnit.unit label

def state (rows : List Nat) : EquationStore Atom × List Nat :=
  (ConcreteStorePrograms.knowledge, rows)

def request (taken made : List Nat) : OrderedStore.Publication Atom Nat :=
  ⟨⟨taken, [], made⟩, []⟩

private theorem admission (rows taken made : List Nat)
    (unique : rows.Nodup ∧ taken.Nodup ∧ made.Nodup)
    (inside : taken.toFinset ⊆ rows.toFinset) (fresh : Disjoint made.toFinset rows.toFinset) :
    actualStep.Admits (s := state rows) (request taken made) := by
  refine ⟨unique, ?_, ConcreteStorePrograms.consistent⟩
  refine ⟨inside, ?_, ?_, fresh, ?_⟩
  · simp [request, OrderedStore.Publication.commit, Selection.commit]
  · simp [request, OrderedStore.Publication.commit, Selection.commit]
  · intro query member
    simp [request, OrderedStore.Publication.commit] at member

theorem take_a : actualStep.Admits (s := state [0, 1, 2, 3, 4]) (request [0, 3] []) :=
  admission _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem route_a : actualStep.Admits (s := state [1, 2, 4]) (request [] [5]) :=
  admission _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem take_b : actualStep.Admits (s := state [1, 2, 4, 5]) (request [1, 4] []) :=
  admission _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem route_b : actualStep.Admits (s := state [2, 5]) (request [] [6]) :=
  admission _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

def targetRun : actualStep.Run (state [0, 1, 2, 3, 4]) :=
  .cons (request [0, 3] []) take_a
    (.cons (request [] [5]) route_a
      (.cons (request [1, 4] []) take_b (.cons (request [] [6]) route_b (.nil _))))

def regionPayloads (region : String) (rows : List Nat) : List Atom := rows.filterMap fun occurrence =>
  match label occurrence with
  | .expression [.symbol "at", .symbol located, value] => if region == located then some value else none
  | _ => none

theorem target_source_observations :
    regionPayloads "q" targetRun.last.2 = sourceResult.2 ∧
      regionPayloads "out" targetRun.last.2 = sourceResult.1 := by
  rw [source_budget_exact]
  decide +kernel

def isCredit : Atom → Bool
  | .expression [.symbol "at", .symbol "q", .expression [.symbol "credit", _]] => true
  | _ => false

def charge : ConservedCharge actualStep Nat :=
  ConsumableBudget.credits PeTTaStoreSelection.atomFrames PUnit.unit label isCredit

theorem update_bound : ConsumableBudget.spendingCount charge targetRun ≤ 2 := by
  have bound := ConsumableBudget.spending_count_bound charge targetRun (by
    intro event member
    simp only [targetRun, Step.Run.word, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide +kernel)
  exact bound

theorem two_updates_four_events :
    ConsumableBudget.spendingCount charge targetRun = 2 ∧ targetRun.word.length = 4 := by
  decide +kernel

/-- Applying the update-credit bound to every primitive event would be false:
the routing events have observable writes but spend no update credit. -/
theorem event_count_is_not_credit_count :
    charge.potential (state [0, 1, 2, 3, 4]) < targetRun.word.length := by
  decide +kernel

end Mettapedia.Languages.MeTTa.Experimental.DerivedTransformForms.BudgetCycle
