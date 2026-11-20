import Mettapedia.Machines.NetworkBackpressure
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationExecution

/-!
# The byte-service model at the authored tcalc boundary

The module imports `Tcalc.Transitions` and adds receiver states and service
firings. Total decoders reject malformed syntax. The interpretation uses the
same preparation, permission and effects as `NetworkBackpressure`.

The execution theorem relates actual module rewriting to admitted abstract
steps. This binds the mathematical counterexample to the structured model;
it does not refine an OS, lwIP, or a compiler implementation to that model.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NetworkServiceModule

open Mettapedia.Machines.NetworkBackpressure

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.LanguageDef.ModuleSource
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation
open scoped Commands

-- The module reader resolves imports by the source file's basename.
namespace tcalc
abbrev module := Tcalc.module
abbrev library := Tcalc.library
end tcalc

#module_file "../../../../metta/gslt/module/NetworkBackpressure.module"
#module_roundtrip NetworkBackpressure

def language : LanguageDef := NetworkBackpressure.language.toOption.get (by decide +kernel)

set_option maxHeartbeats 2000000 in
theorem uses_tcalc_transition : language.rewrites =
    Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.language.rewrites :=
  by decide +kernel

def encodeCount : Nat → Pattern
  | 0 => .apply "NbZero" []
  | n + 1 => .apply "NbSucc" [encodeCount n]

def decodeCount : Pattern → Option Nat
  | .apply "NbZero" [] => some 0
  | .apply "NbSucc" [n] => (decodeCount n).map Nat.succ
  | _ => none

@[simp] theorem decode_encode_count (n : Nat) : decodeCount (encodeCount n) = some n := by
  induction n <;> simp_all [encodeCount, decodeCount]

def encodeState (s : State) : Pattern :=
  .apply "NbState" [encodeCount s.backlog, encodeCount s.queued, encodeCount s.uncredited,
    encodeCount s.window, encodeCount s.delivered, encodeCount s.committed, encodeCount s.timers]

def decodeState : Pattern → Option State
  | .apply "NbState" [b, q, u, w, d, c, t] => do
      return ⟨← decodeCount b, ← decodeCount q, ← decodeCount u, ← decodeCount w,
        ← decodeCount d, ← decodeCount c, ← decodeCount t⟩
  | _ => none

@[simp] theorem decode_encode_state (s : State) : decodeState (encodeState s) = some s := by
  cases s
  simp [encodeState, decodeState]

def encodeAction : Action → Pattern
  | .append => .apply "NbAppend" []
  | .commit => .apply "NbCommit" []
  | .receive n => .apply "NbReceive" [encodeCount n]
  | .read n => .apply "NbRead" [encodeCount n]
  | .credit => .apply "NbCredit" []
  | .timer => .apply "NbTimer" []

def decodeAction : Pattern → Option Action
  | .apply "NbAppend" [] => some .append
  | .apply "NbCommit" [] => some .commit
  | .apply "NbReceive" [n] => (decodeCount n).map Action.receive
  | .apply "NbRead" [n] => (decodeCount n).map Action.read
  | .apply "NbCredit" [] => some .credit
  | .apply "NbTimer" [] => some .timer
  | _ => none

@[simp] theorem decode_encode_action (a : Action) : decodeAction (encodeAction a) = some a := by
  cases a <;> simp [encodeAction, decodeAction]

def queries (batch : Nat) : Queries where
  prepare state firing := do
    let s ← decodeState state
    let a ← decodeAction firing
    if Prepared s a then some (encodeState (apply a s)) else none
  permit state firing :=
    match decodeState state, decodeAction firing with
    | some s, some a => decide (Permitted batch s a)
    | _, _ => false

theorem execution (batch : Nat) (s : State) (a : Action) :
    rewriteStepWithPremisesUsing (queries batch).relations language
      (request (encodeState s) (encodeAction a)) =
        if Admitted batch s a then [atState (encodeState (apply a s))] else [] := by
  have same : rewriteStepWithPremisesUsing (queries batch).relations language
      (request (encodeState s) (encodeAction a)) =
      rewriteStepWithPremisesUsing (queries batch).relations
        Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.language
          (request (encodeState s) (encodeAction a)) := by
    unfold rewriteStepWithPremisesUsing
    rw [uses_tcalc_transition]
    let rule : RewriteRule := ⟨"Execute", [],
      [.relationQuery "prepared" [.fvar "s", .fvar "f", .fvar "t"],
       .relationQuery "permitted" [.fvar "s", .fvar "f"]],
      .apply "Request" [.fvar "s", .fvar "f"], .apply "At" [.fvar "t"], none⟩
    have single :
        Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.language.rewrites =
          [rule] := by decide +kernel
    rw [single]
    dsimp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      applyRuleWithPremisesUsing,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule,
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule,
      applyPremisesWithEnv, premiseStepWithEnv, relationQueryStep, builtinRelationTuples, rule]
  rw [same, Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.execution]
  simp only [queries, decode_encode_state, decode_encode_action]
  by_cases ready : Prepared s a <;> by_cases permit : Permitted batch s a <;>
    simp [ready, permit, Admitted]

/-- The admitted effect and target are reflected by actual authored rewriting,
not only by a comparison of two copies of the transition definition. -/
theorem emitted_iff (batch : Nat) (s t : State) (a : Action) :
    atState (encodeState t) ∈ rewriteStepWithPremisesUsing (queries batch).relations language
      (request (encodeState s) (encodeAction a)) ↔
        Admitted batch s a ∧ t = apply a s := by
  rw [execution]
  split
  next admitted =>
    simp only [List.mem_singleton]
    constructor
    · intro eq
      have encoded : encodeState t = encodeState (apply a s) := by
        simpa [atState] using eq
      have decoded := congrArg decodeState encoded
      exact ⟨admitted, by simpa using decoded⟩
    · rintro ⟨_, rfl⟩
      rfl
  next refused => simp [refused]

theorem prepared_blocked_read (batch queued window t : Nat) (pending : 0 < queued) :
    (queries batch).prepare (encodeState (cycleState batch queued window t))
      (encodeAction (.read 1)) =
        some (encodeState (apply (.read 1) (cycleState batch queued window t))) ∧
    rewriteStepWithPremisesUsing (queries batch).relations language
      (request (encodeState (cycleState batch queued window t)) (encodeAction (.read 1))) = [] := by
  have boundary := prepared_read_not_permitted batch queued window t pending
  dsimp only [starvation] at boundary
  constructor
  · simp [queries, boundary.1]
  · rw [execution]
    simp [Admitted, boundary.2]

theorem cycle_executes (batch queued window t : Nat) :
    rewriteStepWithPremisesUsing (queries batch).relations language
      (request (encodeState (cycleState batch queued window t)) (encodeAction (cycleAction t))) =
        [atState (encodeState (cycleState batch queued window (t + 1)))] := by
  rw [execution, if_pos (cycle_admitted _ _ _ _), cycle_next]

theorem run_step_executes {batch : Nat} (r : Run batch) (t : Nat) :
    rewriteStepWithPremisesUsing (queries batch).relations language
      (request (encodeState (r.state t)) (encodeAction (r.action t))) =
        [atState (encodeState (r.state (t + 1)))] := by
  rw [execution, if_pos (r.admitted t), r.next]

/-- At each opening, the read is an actual permitted alternative in the
authored module. The weakly just pulse instead selects the new append. -/
theorem pulse_read_available {batch : Nat} (positive : 0 < batch)
    (queued window turn : Nat) (pending : 0 < queued) :
    rewriteStepWithPremisesUsing (queries batch).relations language
      (request (encodeState ((pulse batch queued window).state (2 * turn + 1)))
        (encodeAction (.read 1))) =
      [atState (encodeState
        (apply (.read 1) ((pulse batch queued window).state (2 * turn + 1))))] := by
  rw [execution]
  apply if_pos
  have even : (2 * turn + 1 + 1) % 2 = 0 := by omega
  simp [Admitted, Prepared, Permitted, Action.actor, Eligible, pulse, cycleState, even]
  omega

theorem malformed_state_refused (batch : Nat) :
    (queries batch).prepare (.apply "NbState" []) (encodeAction .timer) = none := rfl

#print axioms execution
#print axioms emitted_iff
#print axioms prepared_blocked_read
#print axioms cycle_executes
#print axioms run_step_executes
#print axioms pulse_read_available

end Mettapedia.Machines.NetworkServiceModule
