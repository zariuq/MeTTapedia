import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ScheduleComposition

/-!
# Occurrence composition and cut for the core theorem-space invariant

An occurrence realization records the existing guarded rewriting process step together
with its enabled occurrence commit. Erasing that record gives the existing
`System.Run`; it is not a separate proof execution semantics. Compiling the
occurrence schedule preserves its final store and theorem-space provenance.

The independent closure also admits cut and conservative extension by derived
rules. A derived rule retains all premises of its supplied derivation. These
results do not supply open-schema overlap enumeration or guest adequacy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uI uV uT uP uN uO
variable {I : Type uI} {V : Type uV} {T : Type uT} {P : Type uP} {N : Type uN} {O : Type uO}

namespace Derivable

/-- Replace each assumed premise by its derivation; admitted inference rules are unchanged. -/
theorem cut {initial replacement : T → Prop} {infers : Multiset T → T → Prop}
    {conclusion : T} (proof : Derivable initial infers conclusion)
    (supply : ∀ premise, initial premise → Derivable replacement infers premise) :
    Derivable replacement infers conclusion := by
  induction proof with
  | initial hypothesis => exact supply _ hypothesis
  | infer rule premises ih => exact .infer rule ih

/-- Installing rules derived from the base theory is conservative for every initial context. -/
theorem conservative_extension {initial : T → Prop}
    {base extra : Multiset T → T → Prop}
    (certified : ∀ premises conclusion, extra premises conclusion →
      Derivable (fun t => t ∈ premises) base conclusion)
    {conclusion : T} (proof : Derivable initial (fun ps c => base ps c ∨ extra ps c) conclusion) :
    Derivable initial base conclusion := by
  induction proof with
  | initial hypothesis => exact .initial hypothesis
  | @infer premises conclusion rule children ih =>
    rcases rule with primitive | derived
    · exact .infer primitive ih
    · exact (certified premises conclusion derived).cut ih

end Derivable

namespace System

variable [DecidableEq O] {C : Calculus V T P N} {theorems : N}
variable (system : System C I theorems) (label : O → T)

/-- Occurrence witnesses for the same core steps already used by `System.Run`. -/
inductive OccurrenceRun : Finset O → List (I × Commit O T) → Finset O → Prop
  | nil (store : Finset O) : OccurrenceRun store [] store
  | cons {before after : Finset O} {actor : I} {commit : Commit O T}
      {schedule : List (I × Commit O T)} :
      Enabled label before commit →
      system.Step actor (labels label before) (labels label (fire before commit)) →
      OccurrenceRun (fire before commit) schedule after →
      OccurrenceRun before ((actor, commit) :: schedule) after

namespace OccurrenceRun

variable {system label}

theorem erase {before after : Finset O} {schedule : List (I × Commit O T)}
    (run : system.OccurrenceRun label before schedule after) :
    system.Run (labels label before) (schedule.map Prod.fst) (labels label after) := by
  induction run with
  | nil store => exact .nil _
  | cons enabled step rest ih => exact .cons step ih

theorem executable {before after : Finset O} {schedule : List (I × Commit O T)}
    (run : system.OccurrenceRun label before schedule after) :
    Executable label before (schedule.map Prod.snd) := by
  induction run with
  | nil store => exact .nil _
  | cons enabled step rest ih => exact .cons enabled ih

theorem final_store {before after : Finset O} {schedule : List (I × Commit O T)}
    (run : system.OccurrenceRun label before schedule after) :
    fireList before (schedule.map Prod.snd) = after := by
  induction run with
  | nil store => rfl
  | cons enabled step rest ih => exact ih

/-- The finite compiled condition is satisfied and its effect realizes the actual run. -/
theorem compiled {before after : Finset O} {schedule : List (I × Commit O T)}
    (run : system.OccurrenceRun label before schedule after) :
    (CompiledSchedule.compile label (schedule.map Prod.snd)).condition.Holds label before ∧
      fire before (CompiledSchedule.compile label (schedule.map Prod.snd)).effect = after :=
  ⟨(CompiledSchedule.compile_condition_iff _ _ _).mpr run.executable,
    (CompiledSchedule.compile_effect run.executable).trans run.final_store⟩

/-- Conditional occurrence composition preserves the actual core theorem-space invariant. -/
theorem compiled_allDerivable [DecidableEq N]
    {before after : Finset O} {schedule : List (I × Commit O T)}
    (run : system.OccurrenceRun label before schedule after) {initial : T → Prop}
    (validBefore : AllDerivable C theorems
      (Derivable initial (InstalledInfers C theorems (system.process system.kernel).rules))
      (labels label before)) :
    AllDerivable C theorems
      (Derivable initial (InstalledInfers C theorems (system.process system.kernel).rules))
      (labels label (fire before (CompiledSchedule.compile label (schedule.map Prod.snd)).effect)) := by
  rw [run.compiled.2]
  exact system.run_allDerivable run.erase validBefore

end OccurrenceRun
end System

namespace CutControls

def inference (premises : Multiset Nat) (conclusion : Nat) : Prop :=
  premises = {0} ∧ conclusion = 1

theorem local_assumption_suffices : Derivable (fun t => t = 0) inference 1 := by
  apply Derivable.infer (premises := {0}) ⟨rfl, rfl⟩
  intro t member
  exact .initial (by simpa using member)

/-- A closed-looking conclusion does not justify deleting the hypothesis that produced it. -/
theorem removing_local_assumption_is_invalid : ¬Derivable (fun _ => False) inference 1 := by
  intro proof
  have impossible {conclusion : Nat} (derived : Derivable (fun _ => False) inference conclusion) : False := by
    induction derived with
    | initial hypothesis => exact hypothesis
    | @infer premises conclusion rule children ih =>
      apply ih 0
      rw [rule.1]
      simp
  exact impossible proof

end CutControls
end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel
