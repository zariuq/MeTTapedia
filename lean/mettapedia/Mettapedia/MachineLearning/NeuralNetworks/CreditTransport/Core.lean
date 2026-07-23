import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Defs

/-!
# Credit-transport systems

This module gives a method-independent semantics for finite credit-assignment
executions.  A system declares its objective, local state, enabled events,
state transition, observable signal, pre-optimizer update, resource charge,
derivative oracle, and locality boundary.

The transition is total.  `ScheduleEnabledFrom` separately records whether an
event list is a licensed execution from the state actually reached by every
prefix.  This keeps asynchronous order explicit without adding a choice of
decidability for `enabled` to the mathematical interface.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

/-- The external information source used to construct a credit signal. -/
inductive OracleKind where
  | exactReverseVjp
  | localJvpOrVjp
  | broadcastOutputError
  | learnedCreditProxy
  | learnedInverseTarget
  | forwardPerturbation
  | functionEvaluation
  | forwardEligibilityTrace
  | equilibriumResponse
  | reversibleTrajectoryEcho
  | auxiliaryBlockSolve
  | detachedLocalObjective
  | parameterUpdateTransform
  | localClosedForm
  | terminalVerifierReward
  deriving DecidableEq, Repr

/-- An auditable declaration of oracle access.

The list is intentionally intensional: repeated entries may represent repeated
oracle calls and are accounted for separately by `ResourceVector`.
-/
structure OracleAudit where
  accesses : List OracleKind
  teacherDependent : Bool := false
  deriving Repr

namespace OracleAudit

/-- Whether a particular oracle kind is declared. -/
def Declares (audit : OracleAudit) (kind : OracleKind) : Prop :=
  kind ∈ audit.accesses

@[simp] theorem declares_mk_iff
    (accesses : List OracleKind) (teacherDependent : Bool) (kind : OracleKind) :
    (OracleAudit.mk accesses teacherDependent).Declares kind ↔ kind ∈ accesses :=
  Iff.rfl

end OracleAudit

/-- Coarse dependency scope, ordered from site-local to terminal-global. -/
inductive LocalityClass where
  | strictlySiteLocal
  | edgeNeighborLocal
  | moduleLocal
  | broadcastLocal
  | globalForward
  | globalReverse
  | functionEvaluationGlobal
  | checkerTerminalGlobal
  deriving DecidableEq, Repr

namespace LocalityClass

/-- A monotone numeric embedding of the declared locality lattice. -/
def rank : LocalityClass → Nat
  | .strictlySiteLocal => 0
  | .edgeNeighborLocal => 1
  | .moduleLocal => 2
  | .broadcastLocal => 3
  | .globalForward => 4
  | .globalReverse => 5
  | .functionEvaluationGlobal => 6
  | .checkerTerminalGlobal => 7

/-- `a` uses no broader dependency scope than `b`. -/
def NoBroaderThan (a b : LocalityClass) : Prop := a.rank ≤ b.rank

theorem noBroaderThan_refl (a : LocalityClass) : a.NoBroaderThan a :=
  Nat.le_refl _

theorem noBroaderThan_trans {a b c : LocalityClass}
    (hab : a.NoBroaderThan b) (hbc : b.NoBroaderThan c) :
    a.NoBroaderThan c :=
  Nat.le_trans hab hbc

end LocalityClass

/-- Locality is a declared scope together with an inspectable event dependency
relation.  The relation records which event sites may influence which others;
it is not inferred from a method name. -/
structure LocalityAudit (Event : Type*) where
  scope : LocalityClass
  dependsOn : Event → Event → Prop

/-- A minimal honesty condition: exact global reverse differentiation cannot be
certified as narrower than global reverse. -/
def OracleLocalityConsistent (oracle : OracleAudit)
    {Event : Type*} (locality : LocalityAudit Event) : Prop :=
  oracle.Declares .exactReverseVjp →
    LocalityClass.globalReverse.NoBroaderThan locality.scope

/-- Resource coordinates charged by a finite credit-transport execution.

The coordinates deliberately do not collapse to one scalar.  Their sequential
and parallel composition laws live in `ResourceSemantics`.
-/
@[ext] structure ResourceVector where
  scalarWork : Nat := 0
  criticalPathSpan : Nat := 0
  persistentMemory : Nat := 0
  peakTemporaryMemory : Nat := 0
  bytesCommunicated : Nat := 0
  synchronizationRounds : Nat := 0
  exactReverseCalls : Nat := 0
  localDerivativeCalls : Nat := 0
  functionEvaluations : Nat := 0
  checkerEvaluations : Nat := 0
  deriving DecidableEq, Repr

namespace ResourceVector

/-- The resource-free execution. -/
def zero : ResourceVector := {}

instance : Zero ResourceVector := ⟨zero⟩

@[simp] theorem zero_scalarWork : (0 : ResourceVector).scalarWork = 0 := rfl
@[simp] theorem zero_criticalPathSpan : (0 : ResourceVector).criticalPathSpan = 0 := rfl
@[simp] theorem zero_persistentMemory : (0 : ResourceVector).persistentMemory = 0 := rfl
@[simp] theorem zero_peakTemporaryMemory : (0 : ResourceVector).peakTemporaryMemory = 0 := rfl
@[simp] theorem zero_bytesCommunicated : (0 : ResourceVector).bytesCommunicated = 0 := rfl
@[simp] theorem zero_synchronizationRounds :
    (0 : ResourceVector).synchronizationRounds = 0 := rfl
@[simp] theorem zero_exactReverseCalls : (0 : ResourceVector).exactReverseCalls = 0 := rfl
@[simp] theorem zero_localDerivativeCalls :
    (0 : ResourceVector).localDerivativeCalls = 0 := rfl
@[simp] theorem zero_functionEvaluations :
    (0 : ResourceVector).functionEvaluations = 0 := rfl
@[simp] theorem zero_checkerEvaluations :
    (0 : ResourceVector).checkerEvaluations = 0 := rfl

end ResourceVector

/-- A finite credit-transport machine before optimizer transport. -/
structure CreditTransportSystem
    (Problem Parameter LocalState Event Signal Update : Type*) where
  objective : Problem → Parameter → ℝ
  initialState : Problem → Parameter → LocalState
  enabled : Problem → Parameter → LocalState → Event → Prop
  transition : Problem → Parameter → Event → LocalState → LocalState
  signal : Problem → Parameter → LocalState → Signal
  readUpdate : Problem → Parameter → LocalState → Update
  eventCost : Problem → Parameter → LocalState → Event → ResourceVector
  oracleAudit : OracleAudit
  localityAudit : LocalityAudit Event

namespace CreditTransportSystem

variable {Problem Parameter LocalState Event Signal Update : Type*}
variable (system : CreditTransportSystem
  Problem Parameter LocalState Event Signal Update)

/-- Execute a concrete ordered event list from an arbitrary local state. -/
def runFrom (problem : Problem) (parameter : Parameter) :
    LocalState → List Event → LocalState
  | state, [] => state
  | state, event :: events =>
      runFrom problem parameter
        (system.transition problem parameter event state) events

/-- Execute a schedule from the declared initializer. -/
def run (problem : Problem) (parameter : Parameter) (events : List Event) : LocalState :=
  system.runFrom problem parameter (system.initialState problem parameter) events

/-- Include the starting state and every state reached by the event schedule. -/
def traceFrom (problem : Problem) (parameter : Parameter) :
    LocalState → List Event → List LocalState
  | state, [] => [state]
  | state, event :: events =>
      state :: traceFrom problem parameter
        (system.transition problem parameter event state) events

/-- The state trace from the declared initializer. -/
def trace (problem : Problem) (parameter : Parameter) (events : List Event) :
    List LocalState :=
  system.traceFrom problem parameter (system.initialState problem parameter) events

/-- Observable credit values along a finite execution. -/
def signalTrace (problem : Problem) (parameter : Parameter) (events : List Event) :
    List Signal :=
  (system.trace problem parameter events).map (system.signal problem parameter)

/-- The pre-optimizer update read after the final event. -/
def finalUpdate (problem : Problem) (parameter : Parameter) (events : List Event) : Update :=
  system.readUpdate problem parameter (system.run problem parameter events)

/-- Every event is enabled at the exact state reached by its preceding prefix. -/
def ScheduleEnabledFrom (problem : Problem) (parameter : Parameter) :
    LocalState → List Event → Prop
  | _, [] => True
  | state, event :: events =>
      system.enabled problem parameter state event ∧
        ScheduleEnabledFrom problem parameter
          (system.transition problem parameter event state) events

/-- Schedule validity from the declared initializer. -/
def ScheduleEnabled (problem : Problem) (parameter : Parameter)
    (events : List Event) : Prop :=
  system.ScheduleEnabledFrom problem parameter
    (system.initialState problem parameter) events

/-- A state fixed by every enabled transition. -/
def IsEquilibriumAt (problem : Problem) (parameter : Parameter)
    (state : LocalState) : Prop :=
  ∀ event, system.enabled problem parameter state event →
    system.transition problem parameter event state = state

@[simp] theorem runFrom_nil (problem : Problem) (parameter : Parameter)
    (state : LocalState) :
    system.runFrom problem parameter state [] = state :=
  rfl

@[simp] theorem runFrom_cons (problem : Problem) (parameter : Parameter)
    (state : LocalState) (event : Event) (events : List Event) :
    system.runFrom problem parameter state (event :: events) =
      system.runFrom problem parameter
        (system.transition problem parameter event state) events :=
  rfl

theorem runFrom_append (problem : Problem) (parameter : Parameter)
    (state : LocalState) (events₁ events₂ : List Event) :
    system.runFrom problem parameter state (events₁ ++ events₂) =
      system.runFrom problem parameter
        (system.runFrom problem parameter state events₁) events₂ := by
  induction events₁ generalizing state with
  | nil => rfl
  | cons event events₁ ih =>
      simp only [List.cons_append, runFrom_cons]
      exact ih (system.transition problem parameter event state)

@[simp] theorem traceFrom_nil (problem : Problem) (parameter : Parameter)
    (state : LocalState) :
    system.traceFrom problem parameter state [] = [state] :=
  rfl

@[simp] theorem traceFrom_cons (problem : Problem) (parameter : Parameter)
    (state : LocalState) (event : Event) (events : List Event) :
    system.traceFrom problem parameter state (event :: events) =
      state :: system.traceFrom problem parameter
        (system.transition problem parameter event state) events :=
  rfl

theorem traceFrom_length (problem : Problem) (parameter : Parameter)
    (state : LocalState) (events : List Event) :
    (system.traceFrom problem parameter state events).length = events.length + 1 := by
  induction events generalizing state with
  | nil => rfl
  | cons event events ih =>
      simp only [traceFrom_cons, List.length_cons]
      exact congrArg Nat.succ (ih (system.transition problem parameter event state))

theorem trace_length (problem : Problem) (parameter : Parameter)
    (events : List Event) :
    (system.trace problem parameter events).length = events.length + 1 :=
  system.traceFrom_length problem parameter
    (system.initialState problem parameter) events

@[simp] theorem trace_head? (problem : Problem) (parameter : Parameter)
    (events : List Event) :
    (system.trace problem parameter events).head? =
      some (system.initialState problem parameter) := by
  cases events <;> rfl

theorem signalTrace_length (problem : Problem) (parameter : Parameter)
    (events : List Event) :
    (system.signalTrace problem parameter events).length = events.length + 1 := by
  simp only [signalTrace, List.length_map, trace_length]

theorem scheduleEnabledFrom_append (problem : Problem) (parameter : Parameter)
    (state : LocalState) (events₁ events₂ : List Event) :
    system.ScheduleEnabledFrom problem parameter state (events₁ ++ events₂) ↔
      system.ScheduleEnabledFrom problem parameter state events₁ ∧
      system.ScheduleEnabledFrom problem parameter
        (system.runFrom problem parameter state events₁) events₂ := by
  induction events₁ generalizing state with
  | nil => simp [ScheduleEnabledFrom, runFrom]
  | cons event events₁ ih =>
      simp only [List.cons_append, ScheduleEnabledFrom, runFrom_cons]
      rw [ih]
      tauto

end CreditTransportSystem

#print axioms LocalityClass.noBroaderThan_trans
#print axioms CreditTransportSystem.runFrom_append
#print axioms CreditTransportSystem.trace_length
#print axioms CreditTransportSystem.scheduleEnabledFrom_append

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
