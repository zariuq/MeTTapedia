import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceQueries
import Mettapedia.Machines.Cursor.ReadOnlyQuery

/-!
# Source queries through the existing retained cursor

The source compiler supplies the client of the existing read protocol. Its
paused and completed outcomes, saved continuation, read certificate and charge
are those of that protocol. A completed empty answer is related to the
independent source judgment; exhaustion alone exposes no answer.

The read provider denotes one immutable view. Validated resumption may use a
new view after checking the performed reads, including empty ones. The native
runtime still owes the complete region scanner, view lifetime and atomic
validation/execution boundary. The bounds below count region reads and the
return inspection, not the internal work of matching or pure computed sources.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Query.Execution

open Mettapedia.Machines

universe u
variable {O V T P : Type u} [DecidableEq O]

abbrev Result (O V T : Type u) (scan : (T → Bool) → List O) :=
  Nat × Cursor.ReadOnlyQuery.Result (Answer := List (Subst V T × List (Pick O T))) scan

/-- Begin the compiled source query with the existing protocol's empty read
certificate. Fuel is an inspection budget, not a completeness claim. -/
def execute (L : TermLayer V T P) (m : Matcher V T P) (label : O → T)
    (scan : (T → Bool) → List O) (template : List P) (source : SourceList V T P)
    (σ : Subst V T) (fuel : Nat) : Result O V T scan :=
  Cursor.advance (Cursor.ReadOnlyQuery.provider scan) Cursor.ReadOnlyQuery.client
    (Cursor.ReadOnlyQuery.readCharge scan) fuel
    ⟨.unit, compile L m label template source σ, []⟩

/-- Actual completed execution recovers the source row bag and the exact
ordered read certificate of the compiled query. -/
theorem completed_rows (L : TermLayer V T P) (m : Matcher V T P) (label : O → T)
    (S : Finset O) (scan : (T → Bool) → List O) (scanned : Complete label S scan)
    (template : List P) (source : SourceList V T P) (σ : Subst V T) (fuel : Nat)
    (observation : ReadOnlyQuery.Observation (T → Bool) (List O)
      (List (Subst V T × List (Pick O T))))
    (finished : Cursor.ReadOnlyQuery.completed? scan
      (execute L m label scan template source σ fuel).2 = some observation) :
    (observation.answer : Multiset (Subst V T × List (Pick O T))) =
        rows L m label S template source σ ∧
      observation.reads = (ReadOnlyQuery.run scan (compile L m label template source σ)).reads := by
  have exactResult := Cursor.ReadOnlyQuery.completed_correct scan fuel
    (compile L m label template source σ) observation finished
  subst observation
  exact ⟨run_compile L m label S scan scanned template source σ, rfl⟩

/-- The concrete compiler terminates on this view after its finite read
path and one return inspection. The reported charge counts exactly the reads. -/
theorem execute_complete (L : TermLayer V T P) (m : Matcher V T P) (label : O → T)
    (scan : (T → Bool) → List O) (template : List P) (source : SourceList V T P)
    (σ : Subst V T) :
    let result := ReadOnlyQuery.run scan (compile L m label template source σ)
    execute L m label scan template source σ (result.reads.length + 1) =
      (result.reads.length, .done ⟨.unit, result.answer, result.reads.reverse⟩) := by
  simpa only [execute, List.append_nil] using Cursor.ReadOnlyQuery.advance_complete scan
    (compile L m label template source σ) []

/-- Splitting a budget preserves the entire packet and accumulated charge,
not just the eventual answer. Prior reads are not performed a second time. -/
theorem execute_split (L : TermLayer V T P) (m : Matcher V T P) (label : O → T)
    (scan : (T → Bool) → List O) (template : List P) (source : SourceList V T P)
    (σ : Subst V T) (first extra : Nat) :
    execute L m label scan template source σ (first + extra) =
      Cursor.resume (Cursor.ReadOnlyQuery.provider scan) Cursor.ReadOnlyQuery.client
        (Cursor.ReadOnlyQuery.readCharge scan) extra
        (execute L m label scan template source σ first) :=
  Cursor.ReadOnlyQuery.advance_split scan first extra (compile L m label template source σ) []

omit [DecidableEq O] in
/-- An unfinished source query has no completed answer, even if its visited
regions have all been empty. This reuses the cursor outcome distinction. -/
theorem paused_has_no_answer (scan : (T → Bool) → List O)
    (pending : Cursor.Packet (Cursor.ReadOnlyQuery.provider scan)
      (Cursor.ReadOnlyQuery.client (Answer := List (Subst V T × List (Pick O T)))) .unit) :
    Cursor.ReadOnlyQuery.completed? scan (.paused pending) = none := rfl

/-- A completed negative result is exactly absence in the independent
source relation, with its matcher and pure-computation hypotheses explicit. -/
theorem completed_absence [DecidableEq V]
    (L : TermLayer V T P) (m : Matcher V T P) (label : O → T) (S : Finset O)
    (scan : (T → Bool) → List O) (scanned : Complete label S scan)
    (sound : Matcher.Sound L m) (complete : Matcher.Complete L m)
    (minimal : Matcher.Minimal L m) (source : SourceList V T P)
    (respects : ∀ eval ∈ source.lets, Respects L eval) (σ : Subst V T) (fuel : Nat)
    (observation : ReadOnlyQuery.Observation (T → Bool) (List O)
      (List (Subst V T × List (Pick O T))))
    (finished : Cursor.ReadOnlyQuery.completed? scan
      (execute L m label scan [] source σ fuel).2 = some observation) :
    observation.answer = [] ↔ ¬ ∃ x, DRow L label S [] source σ x := by
  have exactResult := Cursor.ReadOnlyQuery.completed_correct scan fuel
    (compile L m label [] source σ) observation finished
  subst observation
  exact run_empty_iff_no_declarative L m label S scan scanned sound complete minimal source respects σ

/-- Completed execution invents no declarative row and represents every
declarative alternative modulo the selected term theory. Minimality is at
that observation; distinct occurrence picks are not identified by it. -/
theorem completed_agreement [DecidableEq V]
    (L : TermLayer V T P) (m : Matcher V T P) (label : O → T) (S : Finset O)
    (scan : (T → Bool) → List O) (scanned : Complete label S scan)
    (sound : Matcher.Sound L m) (complete : Matcher.Complete L m)
    (minimal : Matcher.Minimal L m) (template : List P) (source : SourceList V T P)
    (respects : ∀ eval ∈ source.lets, Respects L eval) (σ : Subst V T) (fuel : Nat)
    (observation : ReadOnlyQuery.Observation (T → Bool) (List O)
      (List (Subst V T × List (Pick O T))))
    (finished : Cursor.ReadOnlyQuery.completed? scan
      (execute L m label scan template source σ fuel).2 = some observation) :
    (∀ x ∈ observation.answer, DRow L label S template source σ x) ∧
      (∀ σ', SubstEquiv L.E σ σ' → ∀ y, DRow L label S template source σ' y →
        ∃ x ∈ observation.answer, RowEquiv L x y) ∧
      ((observation.answer : Multiset (Subst V T × List (Pick O T))).map
        (Quotient.mk (rowSetoid L))).Nodup := by
  have equal := (completed_rows L m label S scan scanned template source σ fuel observation finished).1
  have agreed := agreement (label := label) (S := S) (template := template)
    sound complete minimal source respects σ
  rw [← equal] at agreed
  simpa only [Multiset.mem_coe] using agreed

/-- Successful validation and resumption of an earned packet, followed by
actual completion, recover the source rows in the new view. No correctness
claim about the old store or an unexecuted suffix is assumed. -/
theorem resumed_rows (L : TermLayer V T P) (m : Matcher V T P) (label : O → T)
    (S : Finset O) (before current : (T → Bool) → List O)
    (scanned : Complete label S current) (template : List P)
    (source : SourceList V T P) (σ : Subst V T) (first extra : Nat)
    (packet : Result O V T current)
    (resumed : Cursor.ReadOnlyQuery.resumeValidated before current extra
      (execute L m label before template source σ first) = .ok packet)
    (observation : ReadOnlyQuery.Observation (T → Bool) (List O)
      (List (Subst V T × List (Pick O T))))
    (finished : Cursor.ReadOnlyQuery.completed? current packet.2 = some observation) :
    (observation.answer : Multiset (Subst V T × List (Pick O T))) =
      rows L m label S template source σ := by
  have valid : ReadOnlyQuery.checkReads current (Cursor.ReadOnlyQuery.recorded before
      (execute L m label before template source σ first).2) = true := by
    by_contra invalid
    simp [Cursor.ReadOnlyQuery.resumeValidated, invalid] at resumed
  have exactResume := Cursor.ReadOnlyQuery.resumeValidated_exact before current first extra
    (compile L m label template source σ) [] valid
  change Cursor.ReadOnlyQuery.resumeValidated before current extra
    (execute L m label before template source σ first) =
      .ok (execute L m label current template source σ (first + extra)) at exactResume
  rw [exactResume] at resumed
  cases resumed
  exact (completed_rows L m label S current scanned template source σ (first + extra)
    observation finished).1

#print axioms completed_rows
#print axioms execute_complete
#print axioms completed_absence
#print axioms completed_agreement
#print axioms resumed_rows

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Query.Execution
