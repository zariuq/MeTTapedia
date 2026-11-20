import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment.Readback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Divergence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.RhoTarget

/-!
# All actual firings and runs on the clean rho domain

The target step is the existing four-rule transform step, restricted to clean
points. Closure proves that this restriction removes no admitted transition
from a clean state. Communications read as source reductions; administrative
firings preserve the decoded process. Source steps lift to nonempty target
runs. Administrative progress, reachable barbs and divergence are retained.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open ByInstantiation (G Closed)

def Move (before after : Point) : Prop := Encodings.Moves before.val after.val
abbrev Runs := Relation.ReflTransGen Move

/-- The original program has no transition out of the clean domain. -/
theorem clean_closed {before after : RawState} (clean : Clean before) (moved : Encodings.Moves before after) :
    Clean after := by
  obtain ⟨certificate⟩ := clean
  obtain ⟨process, _, represented⟩ := Encodings.reaches_sound
    ⟨certificate.value, certificate.represents⟩ (.single moved)
  exact clean_of_represents represented

/-- Every admitted firing is present in the restricted calculus. No extra
guard is imposed merely to make the correspondence true. -/
theorem every_firing_lifts (before : Point) (firing : ByInstantiation.Firing before.val)
    (admitted : firing.Admits ByInstantiation.knowledge before.val) :
    ∃ after : Point, after.val = firing.result ByInstantiation.knowledge before.val ∧ Move before after := by
  have step : Encodings.Moves before.val (firing.result ByInstantiation.knowledge before.val) :=
    ⟨firing, admitted, rfl⟩
  exact ⟨⟨_, clean_closed before.property step⟩, rfl, step⟩

theorem runs_raw {before after : Point} (run : Runs before after) : Encodings.Runs before.val after.val := by
  induction run with
  | refl => exact .refl
  | tail previous step ih => exact ih.tail step

theorem raw_runs_lift (before : Point) {last : RawState} (run : Encodings.Runs before.val last) :
    ∃ after : Point, after.val = last ∧ Runs before after := by
  induction run with
  | refl => exact ⟨before, rfl, .refl⟩
  | @tail middle last previous step ih =>
      obtain ⟨point, equal, lifted⟩ := ih
      rw [← equal] at step
      let after : Point := ⟨last, clean_closed point.property step⟩
      exact ⟨after, rfl, lifted.tail step⟩

theorem source_step_congr {first first' last last' : RhoProcess}
    (before : rhoProcessEquations.r first first') (after : rhoProcessEquations.r last last') :
    rhoLanguageDefGSLT.Step first last ↔ rhoLanguageDefGSLT.Step first' last' := by
  rw [CanonicalReaction.publicStep_iff, CanonicalReaction.publicStep_iff,
    (fromProcess_eq_iff _ _).mpr before, (fromProcess_eq_iff _ _).mpr after]

/-- An actual target move reads as either exactly one source reduction or
an unchanged canonical source process. -/
theorem move_reads {before after : Point} (moved : Move before after) :
    rhoLanguageDefGSLT.Step (readback before) (readback after) ∨ readback before = readback after := by
  rcases (ByInstantiation.succ_iff _ _).mp moved with communication | administrative
  · obtain ⟨process, step, represented⟩ :=
      ByInstantiation.reflective_calculus_by_instantiation.2.2.2.1 (readback_represents before) communication
    have final := rhoProcessEquations.iseqv.symm (readback_equations after represented)
    exact .inl ((source_step_congr (rhoProcessEquations.iseqv.refl _) final).mp step)
  · have represented := ByInstantiation.reflective_calculus_by_instantiation.2.2.1
      (readback_represents before) administrative
    have same := rhoProcessEquations.iseqv.symm (readback_equations after represented)
    exact .inr (readback_eq_of_same same)

theorem runs_read {before after : Point} (run : Runs before after) :
    Relation.ReflTransGen rhoLanguageDefGSLT.Step (readback before) (readback after) := by
  induction run with
  | refl => exact .refl
  | tail previous step ih =>
      rcases move_reads step with real | silent
      · exact ih.tail real
      · rwa [← silent]

/-- Each source reduction has a nonempty target implementation from every
clean point representing its source, including non-compiler intermediates. -/
theorem source_step_lifts (before : Point) {process : RhoProcess}
    (step : rhoLanguageDefGSLT.Step (readback before) process) :
    ∃ after : Point, Relation.TransGen Move before after ∧ rhoProcessEquations.r (readback after) process := by
  obtain ⟨middle, last, value, administration, communication, represented⟩ :=
    ByInstantiation.communication_complete (certificate before).represents step
  obtain ⟨midpoint, midEq, lifted⟩ := raw_runs_lift before (Encodings.runs_of_administrative administration)
  have rawLast := Encodings.communicates_moves communication
  rw [← midEq] at rawLast
  let after : Point := ⟨last, clean_closed midpoint.property rawLast⟩
  refine ⟨after, Relation.TransGen.tail'_iff.mpr ⟨midpoint, lifted, rawLast⟩, ?_⟩
  exact readback_equations after ⟨value, represented⟩

theorem source_runs_lift (before : Point) {process : RhoProcess}
    (run : Relation.ReflTransGen rhoLanguageDefGSLT.Step (readback before) process) :
    ∃ after : Point, Runs before after ∧ rhoProcessEquations.r (readback after) process := by
  obtain ⟨last, targetRun, represented⟩ := Encodings.reaches_complete (readback_represents before) run
  obtain ⟨after, equal, lifted⟩ := raw_runs_lift before targetRun
  rw [← equal] at represented
  exact ⟨after, lifted, readback_equations after represented⟩

theorem administrative_bound (before : Point) {last : RawState} {count : Nat}
    (run : ByInstantiation.AdministrativeRun count before.val last) :
    count ≤ ByInstantiation.weightOf before.val.present (certificate before).value :=
  ByInstantiation.administration_bounded (certificate before).represents run

theorem reachable_outputs (before : Point) (channel : G [] .nm) (closed : Closed channel) :
    Encodings.SourceSucceeds (Canonical.canonicalize (ByInstantiation.read channel)) (readback before) ↔
      ∃ after : Point, Runs before after ∧ Encodings.OutBarb channel after.val := by
  rw [Encodings.weak_barbs_agree (readback_represents before) closed]
  constructor
  · rintro ⟨last, run, output⟩
    obtain ⟨after, rfl, lifted⟩ := raw_runs_lift before run
    exact ⟨after, lifted, output⟩
  · rintro ⟨after, run, output⟩
    exact ⟨after.val, runs_raw run, output⟩

theorem divergence_iff (before : Point) :
    (∃ states : Nat → RawState, states 0 = before.val ∧ ∀ n, Encodings.Moves (states n) (states (n + 1))) ↔
      ∃ processes : Nat → RhoProcess, processes 0 = readback before ∧
        ∀ n, rhoLanguageDefGSLT.Step (processes n) (processes (n + 1)) :=
  ⟨Encodings.divergence_reflected (readback_represents before),
    Encodings.divergence_preserved (readback_represents before)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment
