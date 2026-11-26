import Mettapedia.Machines.TIsa.Derivation.SymbolicRun
import Mettapedia.Machines.TIsa.Derivation.SymbolicRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SynchronousUpdate
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricOffers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.RoundControls

/-!
# Publications in a symbolic run

A rule reads a caller's unknown and binds it to a value. Reopening the
rule does not change what the caller learns from the publication.
At zero fuel the same rule does not publish.
For batches, mutually excluding makes pass the joint snapshot test but
do not form a round; a refresh with an exact count can form a round.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.SymbolicFiring.RunExamples

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax.Controls (atoms action)
open RuleSyntax.Examples (c x answer answerFiring answer_admitted openRequest)
open RuleSyntax.JointFirings (bagOf)
open RuleSyntax.JointFirings.Synchronous (empty both makeOne makeTwo both_admitted no_run_reaches)
open RuleSyntax.JointFirings.SymmetricMatches (reprogram reprogram_admission information_eq)
open RuleSyntax.StepWeb.Rounds (run_of_firesInOrder stateAfter_eq_result)
open RuleSyntax.StepWeb.Rounds.Controls

private def start : LiveWorld atoms := LiveWorld.initial openRequest [0] (by decide) (by decide)

private def binding : Rules atoms := [answer]

private theorem binding_found : ∃ success, search (Equiv.refl ℕ) binding start = some success := by
  cases found : search (Equiv.refl ℕ) binding start with
  | none =>
    have member : answerFiring.rule ∈ binding.program := List.mem_cons_self
    let original := reprogram answerFiring member
    have admitted : original.Admits (act atoms) start.state :=
      (reprogram_admission openRequest answerFiring member).mpr answer_admitted
    have quiet := (search_empty_iff (signature := atoms) (Equiv.refl ℕ) binding start).mp found
    exact (quiet original admitted).elim
  | some success => exact ⟨success, rfl⟩

theorem binding_survives_publication :
    ∃ success : Accepted binding start,
      Runs (Equiv.refl ℕ) binding (.entry 1 start) (.entry 0 success.publish) ∧
      ∀ σ, Unifies σ success.publish.state.knowledge → σ 0 = c 5 := by
  obtain ⟨success, found⟩ := binding_found
  have prepared := scan_reaches (Equiv.refl ℕ) binding 1 start (attempts (Equiv.refl ℕ) binding start)
  have ready : Runs (Equiv.refl ℕ) binding (.entry 1 start) (.fund 1 start success) := by
    change Runs (Equiv.refl ℕ) binding (.scan 1 start (attempts (Equiv.refl ℕ) binding start))
      (scanResult binding 1 start (search (Equiv.refl ℕ) binding start)) at prepared
    rw [found] at prepared
    exact .head rfl prepared
  refine ⟨success, (ready.tail rfl).tail rfl, ?_⟩
  intro σ solved
  let firing := success.selected.firing
  have isAnswer : firing.rule = answer := List.mem_singleton.mp firing.member
  have width := success.selected.shaped.2.2.2.2.1
  have readWidth : firing.selection.read.length = 1 := by
    change firing.rule.body.read.length = firing.selection.read.length at width
    rw [isAnswer] at width
    exact width.symm
  obtain ⟨i, read⟩ := List.length_eq_one_iff.mp readWidth
  have used : i ∈ firing.selection.read.toFinset := List.mem_toFinset.mpr (read ▸ List.mem_cons_self)
  have only : i = 0 := Finset.mem_singleton.mp (success.selected.enabled.kept_subset used)
  subst i
  change Unifies σ (firing.information (act atoms) start.state) at solved
  rw [information_eq, isAnswer, read] at solved
  change ∀ e ∈ [(firing.opening.applyTerm x, x), (firing.opening.applyTerm x, c 5)],
    σ.applyTerm e.1 = σ.applyTerm e.2 at solved
  have relates := solved (firing.opening.applyTerm x, x) List.mem_cons_self
  have value := solved (firing.opening.applyTerm x, c 5) (List.mem_cons_of_mem _ List.mem_cons_self)
  exact relates.symm.trans value

theorem no_publication_at_zero_fuel :
    run (Equiv.refl ℕ) binding 0 start = .exhausted start := by
  obtain ⟨success, found⟩ := binding_found
  simp [run, SnapshotMachine.run, found]

private def exclusion : SymbolicBatch.Prepared
    (program := RuleSyntax.JointFirings.Synchronous.program) empty :=
  ⟨both, List.cons_ne_nil _ _, both_admitted.1⟩

theorem jointly_enabled_absence_guards_do_not_give_a_round :
    (SymbolicBatch.evaluate .joint exclusion).isSome = true ∧
      SymbolicRound.evaluate empty [makeOne, makeTwo]
        (List.cons_ne_nil _ _) both_admitted.1 = none := by
  constructor
  · obtain ⟨answer, fires⟩ := SymbolicBatch.admitted_has_result .joint exclusion
      (RuleSyntax.JointFirings.Bag.admits_of_admitsOwn (act atoms) both_admitted)
    simp [fires]
  · cases published : SymbolicRound.evaluate empty [makeOne, makeTwo]
      (List.cons_ne_nil _ _) both_admitted.1 with
    | none => rfl
    | some output =>
      let orders := [makeOne, makeTwo]
      have round := ((SymbolicRound.evaluate_exact empty orders _
        both_admitted.1 output.1 output.2).mp published).1
      have fired := run_of_firesInOrder action _ orders (round.2 orders (.refl _)).1
      rw [stateAfter_eq_result action _ orders both_admitted.1 both_admitted.2.1] at fired
      exact (no_run_reaches fired).elim

theorem exact_count_can_survive_a_refresh_in_either_order :
    (SymbolicRound.evaluate oneToken refreshPair (List.cons_ne_nil _ _) refreshPair_admitted.1).isSome = true := by
  let prepared : SymbolicBatch.Prepared (program := refreshing) oneToken :=
    ⟨bagOf action refreshPair, List.cons_ne_nil _ _, refreshPair_admitted.1⟩
  obtain ⟨answer, fires⟩ := SymbolicBatch.admitted_has_result .memberOwn prepared refreshPair_admitted
  have solved := ((SymbolicBatch.evaluate_exact .memberOwn prepared answer _).mp fires).1
  rw [(SymbolicRound.evaluate_exact oneToken refreshPair (List.cons_ne_nil _ _) refreshPair_admitted.1
    answer _).mpr ⟨refresh_separates.2.1, solved, rfl⟩]
  rfl

end Mettapedia.Machines.TIsa.Derivation.SymbolicFiring.RunExamples
