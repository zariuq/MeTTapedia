import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.PartialRecursive

/-!
# From Mathlib's machine to the step, as one correspondence

`PartialRecursive` relates the authored machine to the step of its program, one reduction for one firing. A step
of Mathlib's `Turing.ToPartrec` machine is one or more reductions of the authored machine: Mathlib's `stepRet`
returns through the continuation and evaluates the next code down to its first return at once, and the authored
language does this one reduction at a time. The terms in between are the pending evaluations and the returns
inside one step of Mathlib's machine.

* **A point is pending in a configuration** (`Pending`): the point is the configuration itself, or a pending
  evaluation or a return whose completion is the configuration's successor.
* `pending_successor`: a reduction from a pending point stays pending in the same configuration or completes
  its step. `pending_step`: from a pending point, the authored machine reaches the configuration's successor.
* **The correspondence** (`mathlibHosted`): an `OperationalCorrespondence` from Mathlib's machine
  (`PartrecMachine.mathlibMachine`) to the authored machine's generated theory. A reduction is read back as no
  step or one step of Mathlib's machine; a step of Mathlib's machine is realized by a path of reductions. It
  is the two-way form of `PartrecMachine.machineRealization` and `PartrecMachine.halting_reflected`.
* **Composed with the step** (`fromMathlib`): `mathlibHosted` composed with `composite`, a correspondence from
  Mathlib's machine to the step of the nineteen-rule program. A firing is read back as no step or one step of
  Mathlib's machine; a step of Mathlib's machine is realized by a path of firings.
* `halts_from_iff`: from a state that reads as the row of a configuration, the program reaches a state halted
  with `w` exactly when Mathlib's machine reaches `halt w` from the configuration.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.PartialRecursive

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Languages.PartrecMachine
open Turing.ToPartrec
open NamesOnTheStep (Expr)
open Presentation.Schematic

/-- **A point is pending in a configuration of Mathlib's machine**: it is the configuration, or a return or a
pending evaluation whose completion is the configuration's successor. -/
def Pending (origin : Cfg) : Point → Prop
  | .config (.halt v) => origin = .halt v
  | .config (.ret k v) => Turing.ToPartrec.step origin = some (stepRet k v)
  | .normal c k v => Turing.ToPartrec.step origin = some (stepNormal c k v)

/-- A configuration is pending in itself. -/
theorem pending_self (cfg : Cfg) : Pending cfg (.config cfg) := by
  cases cfg <;> rfl

/-- **A reduction from a pending point stays pending in the configuration, or completes its step.** -/
theorem pending_successor {origin : Cfg} {p p' : Point} (pending : Pending origin p)
    (stepped : successor p = some p') :
    Pending origin p' ∨ ∃ after, after ∈ Turing.ToPartrec.step origin ∧ Pending after p' := by
  cases p with
  | normal c k v =>
      rw [← Option.some.inj stepped]
      cases c with
      | zero' => exact Or.inr ⟨.ret k (0 :: v), pending, rfl⟩
      | succ =>
          cases v with
          | nil => exact Or.inr ⟨.ret k [1], pending, rfl⟩
          | cons n w => exact Or.inr ⟨.ret k [n + 1], pending, rfl⟩
      | tail =>
          cases v with
          | nil => exact Or.inr ⟨.ret k [], pending, rfl⟩
          | cons n w => exact Or.inr ⟨.ret k w, pending, rfl⟩
      | cons f fs => exact Or.inl pending
      | comp f g => exact Or.inl pending
      | case f g => rcases v with _ | ⟨_ | y, w⟩ <;> exact Or.inl pending
      | fix f => exact Or.inl pending
  | config cfg =>
      cases cfg with
      | halt v => cases stepped
      | ret k v =>
          rw [← Option.some.inj stepped]
          cases k with
          | halt => exact Or.inr ⟨.halt v, pending, rfl⟩
          | cons₁ fs as k => exact Or.inl pending
          | cons₂ ns k => cases ns <;> exact Or.inl pending
          | comp f k => exact Or.inl pending
          | fix f k => rcases v with _ | ⟨_ | n, w⟩ <;> exact Or.inl pending

/-- **From a pending point the authored machine reaches the configuration's successor.** -/
theorem pending_step {origin after : Cfg} {p : Point} (pending : Pending origin p)
    (stepped : after ∈ Turing.ToPartrec.step origin) :
    Relation.ReflTransGen Reduces p.pattern (encCfg after) := by
  cases p with
  | normal c k v =>
      have same : after = stepNormal c k v :=
        Option.some.inj ((Option.mem_def.mp stepped).symm.trans pending)
      rw [same]
      exact normal_reaches_stepNormal c k v
  | config cfg =>
      cases cfg with
      | halt v =>
          have isHalt : origin = .halt v := pending
          rw [isHalt] at stepped
          cases Option.mem_def.mp stepped
      | ret k v =>
          have same : after = stepRet k v :=
            Option.some.inj ((Option.mem_def.mp stepped).symm.trans pending)
          rw [same]
          exact (ret_reaches_stepRet k v).to_reflTransGen

/-- A term of the authored language is pending in a configuration of Mathlib's machine. -/
def MachinePending (origin : Cfg) (term : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) : Prop :=
  ∃ p : Point, term = p.pattern ∧ Pending origin p

/-- **Mathlib's machine and the authored machine**: a reduction is no step or one step of Mathlib's machine,
and a step of Mathlib's machine is a path of reductions. -/
def mathlibHosted : OperationalCorrespondence mathlibMachine machineTheory where
  related := MachinePending
  readStep := by
    rintro origin term next ⟨p, rfl, pending⟩ stepped
    obtain ⟨p', advanced, rfl⟩ :=
      (reduces_iff_successor p next).mp ((reduces_iff_generatedStep _ _).mpr stepped)
    rcases pending_successor pending advanced with silent | ⟨after, machineStep, pendingAfter⟩
    · exact Or.inl ⟨p', rfl, silent⟩
    · exact Or.inr ⟨after, machineStep, p', rfl, pendingAfter⟩
  forward := by
    rintro origin after term ⟨p, rfl, pending⟩ stepped
    exact ⟨encCfg after, (executionPath_nonempty_iff_multiStep machineTheory _ _).mpr
      ((reflTransGen_reduces_iff_multiStep _ _).mp (pending_step pending stepped)),
      .config after, rfl, pending_self after⟩

/-- **Mathlib's machine and the step of the program**: a firing is no step or one step of Mathlib's machine,
and a step of Mathlib's machine is a path of firings. -/
def fromMathlib : OperationalCorrespondence mathlibMachine (stepSystem ℕ program) :=
  mathlibHosted.comp composite

/-- Related configurations and states agree on being halted with an output. -/
theorem observesMathlib (w : List ℕ) {origin : Cfg} {s : SState ℕ}
    (related : ∃ term, MachinePending origin term ∧ ∃ bag, Hosts term bag ∧ ReadsBag s bag) :
    origin = .halt w ↔ HaltedWith w s := by
  obtain ⟨term, ⟨p, isP, pending⟩, hosted⟩ := related
  have atStep := observes w hosted
  constructor
  · intro isHalt
    apply atStep.mp
    rw [isHalt] at pending
    cases p with
    | normal c k v => cases pending
    | config cfg =>
        cases cfg with
        | halt v =>
            have same : Cfg.halt w = Cfg.halt v := pending
            exact isP.trans (congrArg (fun c => (Point.config c).pattern) same.symm)
        | ret k v => cases pending
  · intro halted
    have isPoint : p = .config (.halt w) := pattern_halt (isP.symm.trans (atStep.mpr halted))
    rw [isPoint] at pending
    exact pending

/-- **The program halts exactly when Mathlib's machine does**: from a state that reads as the row of a
configuration, the program reaches a state halted with `w` exactly when Mathlib's machine reaches `halt w`
from the configuration. -/
theorem halts_from_iff (cfg : Cfg) (w : List ℕ) {s : SState ℕ} (reads : ReadsBag s {eCfg cfg}) :
    (∃ s', (stepSystem ℕ program).MultiStep s s' ∧ HaltedWith w s') ↔
      mathlibMachine.MultiStep cfg (.halt w) := by
  have transfer := fromMathlib.reachable_iff (fun c : Cfg => c = .halt w) (HaltedWith w)
    (fun {origin current} related => observesMathlib w (origin := origin) (s := current) related)
    (origin := cfg) (current := s)
    ⟨encCfg cfg, ⟨.config cfg, rfl, pending_self cfg⟩, ({eCfg cfg} : Multiset Expr),
      ⟨.config cfg, rfl, rfl⟩, reads⟩
  constructor
  · intro halts
    obtain ⟨after, path, rfl⟩ := transfer.mpr halts
    exact path
  · intro path
    exact transfer.mp ⟨_, path, rfl⟩

#print axioms pending_successor
#print axioms pending_step
#print axioms mathlibHosted
#print axioms fromMathlib
#print axioms halts_from_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.PartialRecursive
