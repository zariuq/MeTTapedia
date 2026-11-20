import Mettapedia.GSLT.Core.OperationalNormalization

/-!
# Administrative progress for existing operational readbacks

Every actual target step either exposes a source step, or keeps the same source
state and decreases a well-founded rank. The rank can reset when the source
advances. Source accessibility then implies target accessibility.

Composition uses the intermediate state retained by relational composition and
composes the two proved accessibility transfers. It does not choose a new rank
from an erased existential witness. No finite branching or computability of the
systems or rank is required.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Progress

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational

universe uS uM uT uR uQ

/-- A local progress certificate for actual implementation steps. -/
structure Certificate {source : GSLT.{uS}} {target : GSLT.{uT}}
    (readback : OperationalReadback source target) where
  Rank : Type uR
  decreases : Rank → Rank → Prop
  wellFounded : WellFounded decreases
  rank : source.Term → target.Term → Rank
  readStep : ∀ {origin : source.Term} {current next : target.Term},
    readback.related origin current → target.Step current next →
      (readback.related origin next ∧ decreases (rank origin next) (rank origin current)) ∨
        ∃ after, source.Step origin after ∧ readback.related after next

namespace Certificate

variable {source : GSLT.{uS}} {middle : GSLT.{uM}} {target : GSLT.{uT}}
  {readback : OperationalReadback source target}

/-- A rank decrease is needed only when no source step is exposed. -/
def ofNat (rank : source.Term → target.Term → Nat)
    (readStep : ∀ {origin : source.Term} {current next : target.Term},
      readback.related origin current → target.Step current next →
        (readback.related origin next ∧ rank origin next < rank origin current) ∨
          ∃ after, source.Step origin after ∧ readback.related after next) :
    Certificate.{uS, uT, 0} readback where
  Rank := Nat
  decreases := (· < ·)
  wellFounded := Nat.lt_wfRel.wf
  rank := rank
  readStep := readStep

/-- Step-for-step reflection is the case with no administrative step. -/
def ofReflection
    (reflect : ∀ {origin : source.Term} {current next : target.Term},
      readback.related origin current → target.Step current next →
        ∃ after, source.Step origin after ∧ readback.related after next) :
    Certificate.{uS, uT, 0} readback :=
  ofNat (fun _ _ => 0) (fun related step => .inr (reflect related step))

/-- Source normalization and terminating administration imply target normalization.
The inner induction restarts after each real source transition. -/
theorem normalization_preserved (progress : Certificate.{uS, uT, uR} readback)
    {origin : source.Term} {current : target.Term}
    (normalizing : Acc (fun after before => source.Step before after) origin)
    (related : readback.related origin current) :
    Acc (fun next state => target.Step state next) current := by
  induction normalizing generalizing current with
  | intro origin _ ih =>
    have run : ∀ bound : progress.Rank, ∀ state : target.Term,
        progress.rank origin state = bound → readback.related origin state →
          Acc (fun next before => target.Step before next) state := by
      intro bound
      induction bound using progress.wellFounded.induction with
      | h bound smaller =>
        intro state atBound same
        refine .intro state ?_
        intro next stepped
        rcases progress.readStep same stepped with ⟨nextRelated, decreased⟩ |
          ⟨after, sourceStep, nextRelated⟩
        · rw [atBound] at decreased
          exact smaller _ decreased next rfl nextRelated
        · exact ih after sourceStep nextRelated
    exact run _ current rfl related

/-- A genuine infinite implementation execution entails a source infinite execution. -/
theorem infinite_execution_reflected (progress : Certificate.{uS, uT, uR} readback)
    {origin : source.Term} {current : target.Term}
    (related : readback.related origin current)
    (runtime : Nat → target.Term) (starts : runtime 0 = current)
    (steps : ∀ index, target.Step (runtime index) (runtime (index + 1))) :
    ∃ execution : Nat → source.Term, execution 0 = origin ∧
      ∀ index, source.Step (execution index) (execution (index + 1)) := by
  have targetDiverges : ¬ Acc (fun next state => target.Step state next) current :=
    not_acc_iff_exists_descending_chain.mpr ⟨runtime, starts, steps⟩
  have sourceDiverges : ¬ Acc (fun after before => source.Step before after) origin :=
    fun normalizing => targetDiverges (progress.normalization_preserved normalizing related)
  exact not_acc_iff_exists_descending_chain.mp sourceDiverges

/-- Progress guarantees compose through the same intermediate state as the actual readback. -/
theorem normalization_preserved_comp
    {first : OperationalReadback source middle} {second : OperationalReadback middle target}
    (firstProgress : Certificate.{uS, uM, uR} first)
    (secondProgress : Certificate.{uM, uT, uQ} second)
    {origin : source.Term} {current : target.Term}
    (normalizing : Acc (fun after before => source.Step before after) origin)
    (related : (first.comp second).related origin current) :
    Acc (fun next state => target.Step state next) current := by
  obtain ⟨between, before, after⟩ := related
  exact secondProgress.normalization_preserved
    (firstProgress.normalization_preserved normalizing before) after

/-- No-added-divergence for a composed readback, without a chosen global composite rank. -/
theorem infinite_execution_reflected_comp
    {first : OperationalReadback source middle} {second : OperationalReadback middle target}
    (firstProgress : Certificate.{uS, uM, uR} first)
    (secondProgress : Certificate.{uM, uT, uQ} second)
    {origin : source.Term} {current : target.Term}
    (related : (first.comp second).related origin current)
    (runtime : Nat → target.Term) (starts : runtime 0 = current)
    (steps : ∀ index, target.Step (runtime index) (runtime (index + 1))) :
    ∃ execution : Nat → source.Term, execution 0 = origin ∧
      ∀ index, source.Step (execution index) (execution (index + 1)) := by
  obtain ⟨between, before, after⟩ := related
  obtain ⟨middleRun, middleStart, middleSteps⟩ :=
    secondProgress.infinite_execution_reflected after runtime starts steps
  exact firstProgress.infinite_execution_reflected before middleRun middleStart middleSteps

end Certificate

/-- Both normalization directions require both the positive implementation and administrative
progress obligations. Neither alone is inferred from finite correspondence. -/
theorem normalization_iff {source : GSLT.{uS}} {target : GSLT.{uT}}
    (comparison : OperationalCorrespondence source target)
    (progress : Certificate.{uS, uT, uR} comparison.toOperationalReadback)
    (positiveForward : ∀ {origin after : source.Term} {current : target.Term},
      comparison.related origin current → source.Step origin after →
      ∃ final, ∃ path : ExecutionPath target current final,
        0 < path.length ∧ comparison.related after final)
    {origin : source.Term} {current : target.Term} (related : comparison.related origin current) :
    Acc (fun after before => source.Step before after) origin ↔
      Acc (fun next state => target.Step state next) current :=
  ⟨fun normalizing => progress.normalization_preserved normalizing related,
    fun normalizing => comparison.normalization_reflected positiveForward related normalizing⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Progress

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Progress.Certificate.normalization_preserved
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Progress.Certificate.infinite_execution_reflected
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Progress.Certificate.normalization_preserved_comp
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Progress.normalization_iff
