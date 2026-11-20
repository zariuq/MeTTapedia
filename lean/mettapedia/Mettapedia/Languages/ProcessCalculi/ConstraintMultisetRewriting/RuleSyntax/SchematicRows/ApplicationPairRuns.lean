import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationFamilyModels
import Mathlib.Data.Fintype.EquivFin

/-!
# Exact protected executions for one occurrence pair

A compatible pair is processed by one actual admitted application; an
incompatible pair leaves the store unchanged. One returned interpretation
retains the old reading families and the entire new pair family together.
The existence construction is semantic, not a new executable guard oracle.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationSyntax

universe uOcc
variable {judgmentTag arrowTag : Nat} {O : Type uOcc} [DecidableEq O] {s : Store O}

def storeReadings (s : Store O) (caller : Subst rowSig) : Set Tm :=
  {value | ∃ o ∈ s.present, (s.label o).ReadsAt X (b := PUnit.unit) caller value}

theorem ProtectedRun.readings_mono {caller : Subst rowSig}
    (execution : ProtectedRun judgmentTag arrowTag s caller) :
    storeReadings s caller ⊆ storeReadings execution.run.last execution.source := by
  rintro value ⟨o, present, reading⟩
  exact ⟨o, run_present_mono execution.run present,
    (execution.retained_reading_iff o present value).mpr reading⟩

theorem pairFamily_retained {caller : Subst rowSig}
    (execution : ProtectedRun judgmentTag arrowTag s caller)
    (major minor : O) (majorPresent : major ∈ s.present) (minorPresent : minor ∈ s.present) :
    pairFamily judgmentTag arrowTag execution.run.last execution.source major minor =
      pairFamily judgmentTag arrowTag s caller major minor := by
  ext value
  constructor
  · rintro ⟨function, argument, domain, codomain, first, second, output⟩
    exact ⟨function, argument, domain, codomain,
      (execution.retained_reading_iff major majorPresent _).mp first,
      (execution.retained_reading_iff minor minorPresent _).mp second, output⟩
  · rintro ⟨function, argument, domain, codomain, first, second, output⟩
    exact ⟨function, argument, domain, codomain,
      (execution.retained_reading_iff major majorPresent _).mpr first,
      (execution.retained_reading_iff minor minorPresent _).mpr second, output⟩

theorem candidate_present (f : Attempt judgmentTag arrowTag O s) (major minor made : O)
    (same : f.raw = candidate judgmentTag arrowTag (sourceBound s) s major minor made) :
    f.result.present = insert made s.present := by
  change MeTTaCalculus.OccurrenceCommits.fire s.present (f.raw.selection.commit (T := Unit)) = _
  rw [same]
  ext o
  simp [candidate, Selection.commit, MeTTaCalculus.OccurrenceCommits.fire]

theorem candidate_result_readings (f : Attempt judgmentTag arrowTag O s)
    (admitted : (machine judgmentTag arrowTag O).Admits f)
    (caller source : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge)
    (agrees : ∀ term ∈ context s,
      source.applyTerm (f.answer.applyTerm term) = caller.applyTerm term)
    (major minor made : O) (majorPresent : major ∈ s.present)
    (minorPresent : minor ∈ s.present) (madeFresh : made ∉ s.present)
    (same : f.raw = candidate judgmentTag arrowTag (sourceBound s) s major minor made) :
    storeReadings f.result source =
      storeReadings s caller ∪ pairFamily judgmentTag arrowTag s caller major minor := by
  let execution : ProtectedRun judgmentTag arrowTag s caller :=
    ProtectedRun.single f admitted source (Interface.Frames.models_nil _) agrees
  ext value
  constructor
  · rintro ⟨o, present, reading⟩
    rw [candidate_present f major minor made same, Finset.mem_insert] at present
    rcases present with sameOccurrence | old
    · subst o
      exact Or.inr ((candidate_family_iff f admitted caller source known agrees major minor made
        majorPresent minorPresent madeFresh same value).mp reading)
    · exact Or.inl ⟨o, old, (execution.retained_reading_iff o old value).mp reading⟩
  · rintro (⟨o, present, reading⟩ | new)
    · exact ⟨o, f.present_mono admitted present,
        (execution.retained_reading_iff o present value).mpr reading⟩
    · exact ⟨made, (candidate_present f major minor made same).symm ▸ Finset.mem_insert_self _ _,
        (candidate_family_iff f admitted caller source known agrees major minor made
          majorPresent minorPresent madeFresh same value).mpr new⟩

variable [Infinite O]

theorem pair_run_exists (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge)
    (major minor : O) (majorPresent : major ∈ s.present) (minorPresent : minor ∈ s.present) :
    ∃ execution : ProtectedRun judgmentTag arrowTag s caller,
      storeReadings execution.run.last execution.source =
        storeReadings s caller ∪ pairFamily judgmentTag arrowTag s caller major minor := by
  classical
  by_cases compatible : (pairFamily judgmentTag arrowTag s caller major minor).Nonempty
  · obtain ⟨value, function, argument, domain, codomain, first, second, _⟩ := compatible
    obtain ⟨made, fresh⟩ := Infinite.exists_notMem_finset s.present
    obtain ⟨f, admitted, same, source, solved, agrees, _, _⟩ :=
      application_realized judgmentTag arrowTag s caller known major minor made majorPresent
        minorPresent fresh function argument domain codomain first second
    refine ⟨ProtectedRun.single f admitted source solved agrees, ?_⟩
    exact candidate_result_readings f admitted caller source known agrees major minor made
      majorPresent minorPresent fresh same
  · refine ⟨ProtectedRun.start known, ?_⟩
    change storeReadings s caller =
      storeReadings s caller ∪ pairFamily judgmentTag arrowTag s caller major minor
    ext value
    constructor
    · exact Or.inl
    · rintro (old | new)
      · exact old
      · exact False.elim (compatible ⟨value, new⟩)

#print axioms ProtectedRun.readings_mono
#print axioms pairFamily_retained
#print axioms candidate_present
#print axioms candidate_result_readings
#print axioms pair_run_exists

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
