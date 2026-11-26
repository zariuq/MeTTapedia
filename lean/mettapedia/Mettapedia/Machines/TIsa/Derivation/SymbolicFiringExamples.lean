import Mettapedia.Machines.TIsa.Derivation.SymbolicFiring
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Rewriting

/-!
# A symbolic take on presence and exact count

One occurrence already carries the expected value. Another contains
an unknown that can equal it, but need not. A tell binds the rule's
fresh unknown to the expected value: asking for presence succeeds,
asking for exactly one occurrence does not.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.SymbolicFiring.Examples

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Logic.LP (Subst)
open RuleSyntax.OneFrame (ext)
open RuleSyntax.Presentation.Schematic (SState SRule rowSig shift toTerm)
open RuleSyntax.Machines (stateBound shift_fresh_of_bound)

private abbrev FixtureTerm := RuleSyntax.Presentation.Schematic.Tm

private def value : FixtureTerm := toTerm (.sym 17)
private def before : SState ℕ :=
  ⟨PUnit.unit, [], {0, 1}, fun occurrence => if occurrence = 0 then value else .var 0⟩

private def opened : FixtureTerm := .var (stateBound before)

private def command (guard : Check FixtureTerm) : SRule :=
  ⟨PUnit.unit, ⟨[], [], [(.var 0, value)], [guard], [.var 0]⟩, []⟩

private def firing (guard : Check FixtureTerm) :
    RuleSyntax.Firing ℕ (ext (FirstOrder.action rowSig)) {r | r ∈ [command guard]} before.frame :=
  ⟨command guard, List.mem_cons_self, PUnit.unit, shift (stateBound before), ⟨[], [], [2]⟩, []⟩

private def selection (guard : Check FixtureTerm) : Selection (program := {r | r ∈ [command guard]}) before where
  firing := firing guard
  shaped := ⟨shift_fresh_of_bound (firing guard) rfl, by simp [firing], by simp [firing], rfl, rfl, rfl, rfl⟩
  enabled := by
    change Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Enabled
      (fun _ : ℕ => ()) ({0, 1} : Finset ℕ)
      ((⟨[], [], [2]⟩ : Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Selection ℕ).commit (T := Unit))
    decide +kernel

private def anyRequest := selection (.predicate .any (.var 0))
private def countRequest := selection (.count (.var 0) 1)

private theorem solves_tell (guard : Check FixtureTerm) (assignment : Subst rowSig) :
    (act rowSig).Models (a := PUnit.unit) (b := PUnit.unit) assignment (problem (selection guard)) ↔
      assignment.applyTerm opened = value := by
  change (∀ e ∈ [(opened, value)], assignment.applyTerm e.1 = assignment.applyTerm e.2) ↔ _
  simp [value, toTerm, Subst.applyTerm]

private def allValues : Subst rowSig := fun _ => value

private theorem known (guard : Check FixtureTerm) :
    (act rowSig).Models (a := PUnit.unit) (b := PUnit.unit) allValues (problem (selection guard)) :=
  (solves_tell guard allValues).mpr rfl

private theorem presence_admitted : Admitted anyRequest := by
  refine ⟨anyRequest.shaped, anyRequest.enabled, ⟨PUnit.unit, allValues, known _⟩, ?_⟩
  intro frame assignment model
  cases frame
  constructor
  · intro check inRule
    change check ∈ [(.predicate .any opened : Check FixtureTerm)] at inRule
    obtain rfl := List.mem_singleton.mp inRule
    change ∃ occurrence ∈ before.present, assignment.applyTerm opened =
      assignment.applyTerm ((Subst.id rowSig).applyTerm (before.label occurrence))
    refine ⟨0, by decide +kernel, ?_⟩
    rw [Subst.applyTerm_id, (solves_tell _ _).mp model]
    rfl
  · intro query placed
    exact (List.not_mem_nil placed).elim

private theorem count_not_admitted : ¬Admitted countRequest := by
  intro admitted
  have checked := (admitted.2.2.2 PUnit.unit allValues (known _)).1
    (.count opened 1) (by change Check.count opened 1 ∈ [Check.count opened 1]; simp)
  let decode : ℕ → FixtureTerm := fun occurrence => (Subst.id rowSig).applyTerm (before.label occurrence)
  change (RuleSyntax.matchesAt (act rowSig) (a := PUnit.unit) (b := PUnit.unit)
    allValues decode before.present opened).card = 1 at checked
  have readsAll : RuleSyntax.matchesAt (act rowSig) (a := PUnit.unit) (b := PUnit.unit)
      allValues decode before.present opened = before.present := by
    ext occurrence
    rw [RuleSyntax.mem_matchesAt]
    refine ⟨And.left, fun present => ⟨present, ?_⟩⟩
    change allValues.applyTerm opened = allValues.applyTerm ((Subst.id rowSig).applyTerm (before.label occurrence))
    rw [Subst.applyTerm_id]
    by_cases zero : occurrence = 0
    · simp [before, zero, allValues, opened, value, toTerm]
    · simp [before, zero, allValues, opened]
  rw [readsAll] at checked
  have two : before.present.card = 2 := by decide +kernel
  omega

theorem tell_makes_presence_entailed : (evaluate anyRequest).isSome = true := by
  obtain ⟨_, found⟩ := admitted_has_computed_result anyRequest presence_admitted
  rw [found]
  rfl

theorem a_possible_second_occurrence_refuses_exact_one : (evaluate countRequest).isNone = true := by
  rw [(refuses_exactly_when_not_admitted countRequest).mpr count_not_admitted]
  rfl

theorem selected_run_keeps_the_tell_and_publishes :
    ∃ (answer : Subst rowSig) (after : SState ℕ),
      Passes anyRequest .resolve (.finished (some (answer, after))) ∧
      2 ∈ after.present ∧
      (opened, value) ∈ after.knowledge ∧
      (FirstOrder.action rowSig).Principal after.knowledge answer := by
  obtain ⟨result, computed⟩ := Option.isSome_iff_exists.mp tell_makes_presence_entailed
  obtain ⟨answer, after⟩ := result
  have exact := (evaluate_exact anyRequest answer after).mp computed
  refine ⟨answer, after, (selected_run_iff anyRequest _).mpr computed.symm, ?_, ?_,
    principal_result anyRequest computed⟩
  · rw [exact.2.2]
    decide +kernel
  · rw [exact.2.2]
    change (opened, value) ∈ [(opened, value)]
    exact List.mem_cons_self

end Mettapedia.Machines.TIsa.Derivation.SymbolicFiring.Examples
