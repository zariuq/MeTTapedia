import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.SettlingStep

/-!
# Admission after the match

**Admission after the match** (`AdmitsAfterMatch`) is the dependent full step's admission with one
change: a made row must be typed in the comprehension of the firing's information
(`TypedAfterMatch`), instead of in its raw frame. It is a semantic rule: it names no frame for the
result.

* **Conservativity** (`admitsAfterMatch_of_admits`): the present step's admissions are admissions
  after the match; on firings whose rows are typed in the frame the two coincide
  (`admitsAfterMatch_iff_of_frameTyped`).
* **The semantic settler realizes it** (`ideal_admits_of_admitsAfterMatch`): a firing admitted after
  the match whose information has an initial solution is admitted by the settling step with the
  semantic settler.
* **The settling step admits nothing beyond it, up to agreement** (`settling_admitsUpToAgreement`):
  every firing a settling step admits is admitted after the match, with its rows typed up to
  agreement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull (Make State Firing relabel)
open UnificationWithLevels (Agree InitialSolution)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L) {O : Type} [DecidableEq O]

/-- **Admission after the match**: the step's admission, with each made row typed in the
comprehension of the firing's information. -/
def AdmitsAfterMatch {s : State rules O} (f : Firing levels s) : Prop :=
  (f.taken.Nodup ∧ f.made.Nodup ∧ f.takes.length = f.taken.length ∧ f.reads.length = f.read.length ∧
      ∀ m ∈ f.makes, TypedAfterMatch levels f.information m.2) ∧
    Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
    (frames levels).Solvable f.information ∧ (frames levels).Entails f.information (fun _ τ => f.Holds τ)

/-- **Admission up to agreement**: the same, with each made row typed up to agreement. -/
def AdmitsUpToAgreement {s : State rules O} (f : Firing levels s) : Prop :=
  (f.taken.Nodup ∧ f.made.Nodup ∧ f.takes.length = f.taken.length ∧ f.reads.length = f.read.length ∧
      ∀ m ∈ f.makes, TypedUpToAgreement levels f.information m.2) ∧
    Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
    (frames levels).Solvable f.information ∧ (frames levels).Entails f.information (fun _ τ => f.Holds τ)

/-- **Conservativity**: the present step's admissions are admissions after the match. -/
theorem admitsAfterMatch_of_admits {s : State rules O} {f : Firing levels s}
    (admitted : (DependentFull.step levels O).Admits f) : AdmitsAfterMatch levels f := by
  obtain ⟨⟨a, b, c, d, typed⟩, enabled, solvable, holds⟩ := admitted
  exact ⟨⟨a, b, c, d, fun m member => typedAfterMatch_of_wellTyped levels _ (typed m member)⟩,
    enabled, solvable, holds⟩

/-- On firings whose rows are typed in the frame, admission after the match is the present
admission. -/
theorem admitsAfterMatch_iff_of_frameTyped {s : State rules O} {f : Firing levels s}
    (typed : FrameTyped levels f) :
    AdmitsAfterMatch levels f ↔ (DependentFull.step levels O).Admits f := by
  refine ⟨fun ⟨⟨a, b, c, d, _⟩, enabled, solvable, holds⟩ => ?_, admitsAfterMatch_of_admits levels⟩
  exact ⟨⟨a, b, c, d, typed⟩, enabled, solvable, holds⟩

/-- Admission after the match implies admission up to agreement. -/
theorem AdmitsAfterMatch.upToAgreement {s : State rules O} {f : Firing levels s}
    (admitted : AdmitsAfterMatch levels f) : AdmitsUpToAgreement levels f := by
  obtain ⟨⟨a, b, c, d, typed⟩, enabled, solvable, holds⟩ := admitted
  exact ⟨⟨a, b, c, d, fun m member => TypedAfterMatch.upToAgreement levels (typed m member)⟩,
    enabled, solvable, holds⟩

/-- **The semantic settler realizes admission after the match** wherever the information has an
initial solution. -/
theorem ideal_admits_of_admitsAfterMatch {s : State rules O} {f : Firing levels s}
    (admitted : AdmitsAfterMatch levels f) {M : Context rules} {σ : M ⟶ f.helpers.frame}
    (initial : InitialSolution (frames levels) f.information σ) :
    (settlingStep levels O (Settler.ideal levels)).Admits f := by
  obtain ⟨⟨a, b, c, d, typed⟩, enabled, solvable, holds⟩ := admitted
  refine ⟨⟨a, b, c, d, fun m member => ?_⟩, enabled, solvable, holds⟩
  by_cases frameTyped : FrameTyped levels f
  · rw [plan_of_frameTyped levels _ frameTyped]
    exact (Make.reindex_id' m.2).symm ▸ frameTyped m member
  · rw [plan_of_not_frameTyped levels _ frameTyped]
    obtain ⟨M', σ', initial', settles⟩ := Settler.ideal_settles levels initial
    rw [settles]
    exact settled_complete levels initial'.solves (typed m member)

/-- **A settling step admits nothing beyond admission up to agreement.** -/
theorem settling_admitsUpToAgreement (settler : Settler levels) {s : State rules O} {f : Firing levels s}
    (admitted : (settlingStep levels O settler).Admits f) : AdmitsUpToAgreement levels f := by
  have rows := settling_typedUpToAgreement levels settler admitted
  obtain ⟨⟨a, b, c, d, _⟩, enabled, solvable, holds⟩ := admitted
  exact ⟨⟨a, b, c, d, rows⟩, enabled, solvable, holds⟩

end NativeTypesOnTheStep

#print axioms NativeTypesOnTheStep.admitsAfterMatch_of_admits
#print axioms NativeTypesOnTheStep.admitsAfterMatch_iff_of_frameTyped
#print axioms NativeTypesOnTheStep.AdmitsAfterMatch.upToAgreement
#print axioms NativeTypesOnTheStep.ideal_admits_of_admitsAfterMatch
#print axioms NativeTypesOnTheStep.settling_admitsUpToAgreement

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
