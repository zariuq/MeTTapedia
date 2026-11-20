import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Worlds.GuardTiming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Interaction

/-!
# Publication, import and merge in both guard timings

The existing captured-row example publishes x with its knowledge x = 5.
The actual reader imports that row with a fresh unknown, then the existing
besideJoining merges the two worlds. The complete run has the same endpoints
under both timings. Its final knowledge retains the original and opened
unknowns, and the copied row is observed as 5 at every satisfying solution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.GuardTiming.RunControls

open RuleSyntax RuleSyntax.Worlds
open RuleSyntax.Equivalence (System)
open RuleSyntax.Examples (Tm X E x c demo boundRequest everywhere)
open RuleSyntax.Worlds.Controls
  (fiveRow emptyReader importFiring besideJoining publication_enables copy_label nineRequest)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (atoms)
open Mettapedia.Logic.LP

def reader : System Tm Nat := ⟨demo, emptyReader⟩
def publisher : System Tm Nat := ⟨∅, boundRequest⟩
def publishedPublisher : System Tm Nat := ⟨∅, withoutRow boundRequest 0⟩
def importedState : State Tm Nat := importFiring.result X emptyReader
def importedReader : System Tm Nat := ⟨demo, importedState⟩

def start : Bag Tm Nat := ⟨reader ::ₘ publisher ::ₘ 0, ∅⟩
def published : Bag Tm Nat := ⟨reader ::ₘ publishedPublisher ::ₘ 0, insert fiveRow ∅⟩
def imported : Bag Tm Nat := ⟨importedReader ::ₘ publishedPublisher ::ₘ 0, insert fiveRow ∅⟩
def mergedState : State Tm Nat := besideJoining.join importedState publishedPublisher.state
def finish : Bag Tm Nat := ⟨{(⟨demo ∪ ∅, mergedState⟩ : System Tm Nat)}, insert fiveRow ∅⟩

theorem publish_step : Move X besideJoining (events X Nat E) start published := publication_enables.1

theorem import_step : Move X besideJoining (events X Nat E) published imported := publication_enables.2.1

theorem merged_knowledge :
    mergedState.knowledge = [((Term.var 1 : Term atoms), c 5), (x, c 5)] := rfl

theorem merged_solvable : X.Solvable mergedState.knowledge := by
  refine ⟨PUnit.unit, everywhere 5, ?_⟩
  intro equation member
  rw [merged_knowledge] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem merge_step : Move X besideJoining (events X Nat E) imported finish :=
  Move.merge (X := X) (J := besideJoining) (family := events X Nat E)
    0 (insert fiveRow ∅) importedReader publishedPublisher merged_solvable

theorem after_run : Relation.ReflTransGen (Move X besideJoining (events X Nat E)) start finish :=
  ((Relation.ReflTransGen.single publish_step).tail import_step).tail merge_step

theorem demo_quiet : ∀ rule ∈ demo, Quiet rule := by
  intro rule member
  simp only [RuleSyntax.Examples.demo, Set.mem_insert_iff, Set.mem_singleton_iff] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

theorem start_quiet : RulesSatisfy Quiet start := by
  intro world member rule visible
  have worlds : world = reader ∨ world = publisher := by simpa [start] using member
  rcases worlds with rfl | rfl
  · rcases visible with own | shared
    · exact demo_quiet rule own
    · exact absurd shared (Set.notMem_empty _)
  · rcases visible with own | shared
    · exact absurd own (Set.notMem_empty _)
    · exact absurd shared (Set.notMem_empty _)

theorem finish_quiet : RulesSatisfy Quiet finish :=
  rulesSatisfy_runs X besideJoining Quiet (snapshot_quiet_rule Nat) start_quiet after_run

theorem before_run : Relation.ReflTransGen (Move X besideJoining (beforeEvents X Nat E)) start finish :=
  (quiet_world_runs_iff X Nat E besideJoining start_quiet).mpr after_run

theorem same_run_endpoints :
    Relation.ReflTransGen (Move X besideJoining (beforeEvents X Nat E)) start finish ∧
      Relation.ReflTransGen (Move X besideJoining (events X Nat E)) start finish :=
  ⟨before_run, after_run⟩

theorem published_row_removed : 0 ∉ publishedPublisher.state.present := by decide

theorem copied_row_present : importedState.present = {0} := by decide

theorem final_rows : mergedState.present = {0} := by decide

theorem final_label : mergedState.label 0 = (Term.var 1 : Term atoms) := by
  have present : 0 ∈ importedState.present := by decide
  change (if 0 ∈ importedState.present then importedState.label 0 else publishedPublisher.state.label 0) = _
  rw [if_pos present]
  exact copy_label

theorem final_captured_knowledge (solution : Subst atoms)
    (solved : X.Models (a := PUnit.unit) (b := PUnit.unit) solution mergedState.knowledge) :
    solution 1 = c 5 ∧ solution 0 = c 5 := by
  rw [merged_knowledge] at solved
  exact ⟨solved (Term.var 1, c 5) List.mem_cons_self,
    solved (x, c 5) (List.mem_cons_of_mem _ List.mem_cons_self)⟩

theorem final_row_reads_five (solution : Subst atoms)
    (solved : X.Models (a := PUnit.unit) (b := PUnit.unit) solution mergedState.knowledge) :
    X.act (a := PUnit.unit) (b := PUnit.unit) solution (mergedState.label 0) = c 5 := by
  rw [final_label]
  exact (final_captured_knowledge solution solved).1

theorem final_space_retained : finish.space = {fiveRow} := by simp [finish]

theorem nine_request_solvable : X.Solvable nineRequest.knowledge := by
  refine ⟨PUnit.unit, everywhere 9, ?_⟩
  intro equation member
  change equation ∈ [(x, c 9)] at member
  rw [List.mem_singleton] at member
  subst equation
  rfl

/-- The added knowledge is checked jointly by the actual merge guard. -/
theorem contradictory_merge_refused :
    ¬ X.Solvable (besideJoining.join mergedState nineRequest).knowledge := by
  rintro ⟨target, solution, solved⟩
  cases target
  have split := (Frames.models_append (X := X) (a := PUnit.unit) (b := PUnit.unit)
    solution mergedState.knowledge nineRequest.knowledge).mp solved
  have five := (final_captured_knowledge solution split.1).2
  have nine : solution 0 = c 9 := split.2 (x, c 9) List.mem_cons_self
  have impossible : (c 5 : Term atoms) = c 9 := five.symm.trans nine
  exact absurd (Term.const.inj impossible) (by decide)

theorem individually_solvable_but_jointly_refused :
    X.Solvable mergedState.knowledge ∧ X.Solvable nineRequest.knowledge ∧
      ¬ X.Solvable (besideJoining.join mergedState nineRequest).knowledge :=
  ⟨merged_solvable, nine_request_solvable, contradictory_merge_refused⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.GuardTiming.RunControls
