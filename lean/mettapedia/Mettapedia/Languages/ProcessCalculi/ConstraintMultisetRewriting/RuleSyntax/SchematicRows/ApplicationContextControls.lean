import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationContextCost

/-!
# A genuine repeated-application control for full-context growth

Two ground shared rows enable the same application repeatedly. Actual admitted
runs of arbitrary length keep the same reading set after the first step, but
their unfolded captured interfaces grow exponentially. This is not a vacuous
conditional bound or a claim about physical memory allocation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine.ContextControls

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationSyntax

def domain : Tm := symbol 20
def codomain : Tm := symbol 21
def function : Tm := symbol 10
def argument : Tm := symbol 11
def major : Tm := judgment 0 function (arrow 1 domain codomain)
def minor : Tm := judgment 0 argument domain

def entry : Store Nat :=
  ⟨PUnit.unit, [], {0, 1}, fun o => .shared (if o = 0 then major else minor)⟩

theorem entry_known : X.Models (a := PUnit.unit) (b := PUnit.unit) (Subst.id rowSig) entry.knowledge :=
  Interface.Frames.models_nil _

theorem major_reading : (entry.label 0).ReadsAt X (b := PUnit.unit) (Subst.id rowSig) major := by
  change (Subst.id rowSig).applyTerm major = major
  exact Subst.applyTerm_id _

theorem minor_reading : (entry.label 1).ReadsAt X (b := PUnit.unit) (Subst.id rowSig) minor := by
  change (Subst.id rowSig).applyTerm minor = minor
  exact Subst.applyTerm_id _

theorem entry_context_length : (context entry).length = 2 := by
  simp [context, entry, State.ambientTerms, Row.ambientTerms, List.length_flatMap]

theorem repeated_application (n : Nat) :
    ∃ execution : ProtectedRun 0 1 entry (Subst.id rowSig), execution.run.word.length = n ∧
      storeReadings execution.run.last execution.source =
        if n = 0 then storeReadings entry (Subst.id rowSig)
        else storeReadings entry (Subst.id rowSig) ∪ pairFamily 0 1 entry (Subst.id rowSig) 0 1 := by
  induction n with
  | zero => exact ⟨ProtectedRun.start entry_known, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨first, length, firstView⟩ := ih
    obtain ⟨made, fresh⟩ := Infinite.exists_notMem_finset first.run.last.present
    have majorPresent := run_present_mono first.run (show 0 ∈ entry.present by decide)
    have minorPresent := run_present_mono first.run (show 1 ∈ entry.present by decide)
    have majorReading := (first.retained_reading_iff 0 (by decide) major).mpr major_reading
    have minorReading := (first.retained_reading_iff 1 (by decide) minor).mpr minor_reading
    obtain ⟨f, admitted, same, source, known, agrees, _, _⟩ :=
      application_realized 0 1 first.run.last first.source first.known 0 1 made majorPresent
        minorPresent fresh function argument domain codomain majorReading minorReading
    let second : ProtectedRun 0 1 first.run.last first.source :=
      ProtectedRun.single f admitted source known agrees
    have secondView : storeReadings second.run.last second.source =
        storeReadings first.run.last first.source ∪ pairFamily 0 1 first.run.last first.source 0 1 :=
      candidate_result_readings f admitted first.source source first.known agrees 0 1 made
        majorPresent minorPresent fresh same
    refine ⟨first.append second, ?_, ?_⟩
    · change (first.run.append second.run).word.length = n + 1
      rw [Interface.Step.Run.word_append, List.length_append]
      change first.run.word.length + 1 = n + 1
      rw [length]
    · rw [ProtectedRun.append_last, ProtectedRun.append_source, secondView, firstView,
        pairFamily_retained first 0 1 (by decide) (by decide), if_neg (Nat.succ_ne_zero n)]
      by_cases zero : n = 0
      · rw [if_pos zero]
      · simp only [if_neg zero, Set.union_assoc, Set.union_self]

theorem exponential_context_with_fixed_readings (n : Nat) :
    ∃ execution : ProtectedRun 0 1 entry (Subst.id rowSig),
      execution.run.word.length = n + 1 ∧
      (context execution.run.last).length = 2 ^ (n + 2) ∧
      storeReadings execution.run.last execution.source =
        storeReadings entry (Subst.id rowSig) ∪ pairFamily 0 1 entry (Subst.id rowSig) 0 1 := by
  obtain ⟨execution, length, readings⟩ := repeated_application (n + 1)
  have cost := run_context_length execution.run (show entry.knowledge = [] from rfl)
  rw [length, entry_context_length] at cost
  rw [if_neg (Nat.succ_ne_zero n)] at readings
  exact ⟨execution, length, cost.trans (Nat.pow_succ 2 (n + 1)).symm, readings⟩

#print axioms repeated_application
#print axioms exponential_context_with_fixed_readings

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine.ContextControls
