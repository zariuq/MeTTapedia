import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.FiringReceipts
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ScheduleComposition

/-!
# Conditional composition of receipts tied to actual guarded rewriting firings

Every receipt is justified against an installed rule with its actual matching
selections. The existing occurrence-condition compiler then transports its
exact check observations and computes a net effect. Satisfying the compiled
condition expands to a run of the existing guarded rewriting process.

This is composition of matched receipts. It does not enumerate open overlaps,
identify event traces, or justify atomic replacement across interference.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

universe uO uV uT uP uN
variable {O : Type uO} {V : Type uV} {T : Type uT} {P : Type uP} {N : Type uN}
variable [DecidableEq O] {C : Calculus V T P N}

/-- A finite firing receipt certified for an installed rule. The original
world is a proof witness; it is not stored as executable certificate data. -/
structure CertifiedFiring (process : C.Process) (label : O → T) where
  installed : Contract × Rule V T P
  member : installed ∈ process.rules
  receipt : FiringReceipt O V T
  justified : ∃ before, receipt.ValidAt (C.readers.layer installed.1) installed.2 label before

namespace CertifiedFiring

variable {process : C.Process} {label : O → T}

noncomputable def commit (firing : CertifiedFiring process label) : Commit O T :=
  firing.receipt.commit (C.readers.layer firing.installed.1) firing.installed.2

theorem step [DecidableEq T] (firing : CertifiedFiring process label) {before : Finset O}
    (enabled : Enabled label before firing.commit) :
    process.Step (labels label before) (labels label (fire before firing.commit)) := by
  obtain ⟨origin, valid⟩ := firing.justified
  exact ⟨firing.installed, firing.member, (valid.reuse enabled).step⟩

theorem installed_instance [DecidableEq N] (firing : CertifiedFiring process label)
    (theorems : N) {output : O} (produced : output ∈ firing.receipt.outputs)
    (atTheorems : C.space (label output) = theorems) :
    TierZeroKernel.InstalledInfers C theorems process.rules
      (labels label (firing.receipt.premiseOccurrences C.space label theorems)) (label output) := by
  obtain ⟨origin, valid⟩ := firing.justified
  exact ⟨firing.installed, firing.member, valid.ruleInstance_occurrences theorems produced atTheorems⟩

noncomputable def compile (label : O → T) (firings : List (CertifiedFiring process label)) : CompiledSchedule O T :=
  CompiledSchedule.compile label (firings.map commit)

theorem executable_realizes [DecidableEq T] (firings : List (CertifiedFiring process label))
    (before : Finset O) (enabled : Executable label before (firings.map commit)) :
    Relation.ReflTransGen process.Step (labels label before)
      (labels label (fireList before (firings.map commit))) := by
  induction firings generalizing before with
  | nil => exact .refl
  | cons first rest ih =>
      obtain ⟨one, later⟩ := executable_cons_iff.mp enabled
      exact (Relation.ReflTransGen.single (first.step one)).trans (ih _ later)

/-- The finite compiled condition is enough to expand the net update into
actual installed-rule firings with all recorded checks retained. -/
theorem compile_realizes [DecidableEq T] (firings : List (CertifiedFiring process label)) (before : Finset O)
    (admitted : (compile label firings).condition.Holds label before) :
    Relation.ReflTransGen process.Step (labels label before)
      (labels label (fire before (compile label firings).effect)) := by
  have enabled := (CompiledSchedule.compile_condition_iff label (firings.map commit) before).mp admitted
  rw [show fire before (compile label firings).effect = fireList before (firings.map commit) from
    CompiledSchedule.compile_effect enabled]
  exact executable_realizes firings before enabled

/-- Any independently established invariant of the process is preserved by
the compiled receipt block. No equality of event traces is asserted. -/
theorem compile_preserves [DecidableEq T] (firings : List (CertifiedFiring process label)) (before : Finset O)
    (invariant : Multiset T → Prop)
    (preserves : ∀ {first second}, process.Step first second → invariant first → invariant second)
    (initial : invariant (labels label before))
    (admitted : (compile label firings).condition.Holds label before) :
    invariant (labels label (fire before (compile label firings).effect)) := by
  have run := compile_realizes firings before admitted
  generalize labels label (fire before (compile label firings).effect) = final at run ⊢
  induction run with
  | refl => exact initial
  | tail earlier step ih => exact preserves step ih

end CertifiedFiring
end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting
