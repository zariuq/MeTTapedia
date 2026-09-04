import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.Core.BindingStoreCapabilityAlgebra
import Mettapedia.GSLT.LanguageDef.AuthoritativeSlotTrailCompilation
import Mettapedia.Logic.LP.Unification

/-!
# Unification elimination traces and transactional binding realization

Martelli--Montanari unification is the semantic authority.  This module
refines its execution to an explicit trace of elimination updates together
with a typed stop reason.  Observing a successful trace gives exactly the
substitution returned by the source unifier; every unsuccessful trace observes
as failure, including one that performed speculative eliminations before a
later conflict or fuel boundary.

The second layer is representation-independent.  Any physical binding store
whose logical write is substitution composition may execute the trace.
Successful execution commits the exact source substitution over the entrance
environment, while every unsuccessful execution rolls back to the exact
entrance denotation.  This does not claim that a particular C binding builder
implements the interface; that remains a separate physical-refinement
obligation.
-/

namespace Mettapedia.GSLT.LanguageDef.UnificationEliminationTraceCompilation

open Mettapedia.Logic.LP
open Mettapedia.GSLT.Core.BindingStoreCapabilityAlgebra

variable {signature : LPSignature}
  [DecidableEq signature.vars]
  [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols]

abbrev Equation (signature : LPSignature) :=
  Term signature × Term signature

/-- One source-level elimination, retained in chronological execution order. -/
abbrev BindingUpdate (signature : LPSignature) :=
  signature.vars × Term signature

/-- Why the explicit trace stopped.  Only `success` publishes a substitution. -/
inductive StopReason where
  | success
  | fuelExhausted
  | occursCheck
  | constructorConflict
deriving DecidableEq, Repr

/-- An operational unification artifact.  `updates` includes speculative
eliminations made before a later failure so a physical realization can prove
that its rollback path is exact. -/
structure EliminationTrace (signature : LPSignature) where
  updates : List (BindingUpdate signature)
  stop : StopReason

/-- Compose a chronological elimination trace into its substitution. -/
def traceSubst : List (BindingUpdate signature) → Subst signature
  | [] => Subst.id signature
  | (key, term) :: updates =>
      traceSubst updates ∘ₛ Subst.single key term

/-- The public observation of a trace.  Failed speculative prefixes do not
publish a partial substitution. -/
def observe (trace : EliminationTrace signature) : Option (Subst signature) :=
  match trace.stop with
  | .success => some (traceSubst trace.updates)
  | _ => none

/-- Prefix one attempted elimination while retaining the recursive stop
reason. -/
def EliminationTrace.record
    (update : BindingUpdate signature)
    (trace : EliminationTrace signature) : EliminationTrace signature :=
  { updates := update :: trace.updates, stop := trace.stop }

omit [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols] in
/-- Prefixing a trace update composes it into a successful observation and
remains unobservable after every failure reason. -/
@[simp] theorem observe_record
    (update : BindingUpdate signature)
    (trace : EliminationTrace signature) :
    observe (trace.record update) =
      match observe trace with
      | some substitution =>
          some (substitution ∘ₛ Subst.single update.1 update.2)
      | none => none := by
  cases trace with
  | mk updates stop =>
      cases stop <;> rfl

/-- Martelli--Montanari execution with an explicit elimination trace.

Delete and rigid decomposition perform no binding update.  Elimination records
the attempted write even if the recursively transformed equation set later
fails. -/
def runTrace : Nat → List (Equation signature) → EliminationTrace signature
  | 0, _ => ⟨[], .fuelExhausted⟩
  | _, [] => ⟨[], .success⟩
  | fuel + 1, (left, right) :: rest =>
      match left with
      | .var key =>
          match right with
          | .var other =>
              if key = other then runTrace fuel rest
              else
                let single := Subst.single key (.var other)
                (runTrace fuel (single.applyEqs rest)).record
                  (key, .var other)
          | term =>
              if term.occursIn key then ⟨[], .occursCheck⟩
              else
                let single := Subst.single key term
                (runTrace fuel (single.applyEqs rest)).record
                  (key, term)
      | .const constant =>
          match right with
          | .var key =>
              if (Term.const constant).occursIn key then
                ⟨[], .occursCheck⟩
              else
                let single := Subst.single key (.const constant)
                (runTrace fuel (single.applyEqs rest)).record
                  (key, .const constant)
          | .const other =>
              if constant = other then runTrace fuel rest
              else ⟨[], .constructorConflict⟩
          | .app _ _ => ⟨[], .constructorConflict⟩
      | .app function arguments =>
          match right with
          | .var key =>
              if (Term.app function arguments).occursIn key then
                ⟨[], .occursCheck⟩
              else
                let term := Term.app function arguments
                let single := Subst.single key term
                (runTrace fuel (single.applyEqs rest)).record
                  (key, term)
          | .const _ => ⟨[], .constructorConflict⟩
          | .app other otherArguments =>
              if same : function = other then
                runTrace fuel
                  (finPairsToList arguments (same ▸ otherArguments) ++ rest)
              else ⟨[], .constructorConflict⟩

/-- The explicit trace has exactly the complete observation of the source
unifier, including every failure and fuel boundary. -/
theorem observe_runTrace_exact
    (fuel : Nat) (equations : List (Equation signature)) :
    observe (runTrace fuel equations) = unifyFuel fuel equations := by
  induction fuel generalizing equations with
  | zero => simp [runTrace, observe, unifyFuel]
  | succ fuel inductionHypothesis =>
      cases equations with
      | nil => simp [runTrace, observe, unifyFuel, traceSubst]
      | cons equation rest =>
          rcases equation with ⟨left, right⟩
          cases left <;> cases right <;>
            simp only [runTrace, unifyFuel]
          · split
            · exact inductionHypothesis rest
            · rw [observe_record, inductionHypothesis]
              cases recursive : unifyFuel fuel
                  ((Subst.single _ (.var _)).applyEqs rest) <;>
                simp
          · split
            · rfl
            · rw [observe_record, inductionHypothesis]
              cases recursive : unifyFuel fuel
                  ((Subst.single _ (.const _)).applyEqs rest) <;>
                simp
          · split
            · rfl
            · rw [observe_record, inductionHypothesis]
              cases recursive : unifyFuel fuel
                  ((Subst.single _ (.app _ _)).applyEqs rest) <;>
                simp
          · split
            · rfl
            · rw [observe_record, inductionHypothesis]
              cases recursive : unifyFuel fuel
                  ((Subst.single _ (.const _)).applyEqs rest) <;>
                simp
          · split
            · exact inductionHypothesis rest
            · rfl
          · rfl
          · split
            · rfl
            · rw [observe_record, inductionHypothesis]
              cases recursive : unifyFuel fuel
                  ((Subst.single _ (.app _ _)).applyEqs rest) <;>
                simp
          · rfl
          · split
            · exact inductionHypothesis _
            · rfl

/-- Trace production as a composable certified realization. -/
def eliminationTraceRealization :
    Mettapedia.GSLT.SimpleRealization
      (Nat × List (Equation signature))
      (EliminationTrace signature)
      (Option (Subst signature)) where
  compile := fun _ source => runTrace source.1 source.2
  observeSource := fun _ source => unifyFuel source.1 source.2
  observeArtifact := fun _ trace => observe trace
  adequate := by
    intro _ source
    exact observe_runTrace_exact source.1 source.2

/-! ## Transactional realization -/

/-- A rollback store whose authoritative logical write is exactly one
Martelli--Montanari substitution composition. -/
structure EliminationRollbackStore
    (signature : LPSignature)
    [DecidableEq signature.vars]
    (Physical : Type*) (Mark : Type*) where
  store : LinearRollbackStore
    (Subst signature) Physical Mark (BindingUpdate signature)
  logicalWrite_eq : ∀ substitution update,
    store.logicalWrite substitution update =
      Subst.single update.1 update.2 ∘ₛ substitution

namespace EliminationRollbackStore

variable {Physical : Type*} {Mark : Type*}

omit [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols] in
/-- A finite chronological update trace denotes its composed substitution
over the entrance environment. -/
theorem logicalWriteMany_eq
    (implementation : EliminationRollbackStore signature Physical Mark)
    (substitution : Subst signature)
    (updates : List (BindingUpdate signature)) :
    implementation.store.logicalWriteMany substitution updates =
      traceSubst updates ∘ₛ substitution := by
  induction updates generalizing substitution with
  | nil => simp [BindingStore.logicalWriteMany, traceSubst,
      Subst.comp_id_left]
  | cons update updates inductionHypothesis =>
      rw [BindingStore.logicalWriteMany,
        implementation.logicalWrite_eq,
        inductionHypothesis]
      simp only [traceSubst]
      exact (Subst.comp_assoc _ _ substitution).symm

/-- Execute a trace transactionally: success commits; every other stop reason
rolls back the complete speculative prefix. -/
def execute
    (implementation : EliminationRollbackStore signature Physical Mark)
    (physical : Physical) (trace : EliminationTrace signature) : Physical :=
  let evolved := implementation.store.toBindingStore.writeMany
    physical trace.updates
  match trace.stop with
  | .success => evolved
  | _ => implementation.store.rollback evolved
      (implementation.store.save physical)

/-- Execute an observer-free terminal suffix by publishing its writes only
after the trace is known to succeed.  This realization is admissible only
when no later elimination, occurs check, guard, or external observer reads the
buffered suffix; otherwise the ordinary chronological `execute` path remains
authoritative. -/
def executeBufferedTerminal
    (implementation : EliminationRollbackStore signature Physical Mark)
    (physical : Physical) (trace : EliminationTrace signature) : Physical :=
  match trace.stop with
  | .success => implementation.store.toBindingStore.writeMany
      physical trace.updates
  | _ => physical

omit [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols] in
/-- Transactional execution has one complete observation law.  Success adds
the exact trace substitution over the entrance environment; every failure is
the observational identity. -/
theorem denote_execute
    (implementation : EliminationRollbackStore signature Physical Mark)
    (physical : Physical) (trace : EliminationTrace signature) :
    implementation.store.denote
        (implementation.execute physical trace) =
      match observe trace with
      | some substitution =>
          substitution ∘ₛ implementation.store.denote physical
      | none => implementation.store.denote physical := by
  cases reason : trace.stop with
  | success =>
      rw [execute, reason]
      simp only [observe, reason]
      rw [implementation.store.writeMany_exact,
        implementation.logicalWriteMany_eq]
  | fuelExhausted | occursCheck | constructorConflict =>
      rw [execute, reason]
      simp only [observe, reason]
      exact implementation.store.rollback_after_writeMany_exact
        physical trace.updates

omit [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols] in
/-- An observer-free buffered terminal suffix has exactly the same final
logical observation as chronological writes followed by rollback on failure.
The theorem is intentionally about the final boundary; it grants no license
to skip writes that an intermediate operation can inspect. -/
theorem denote_executeBufferedTerminal
    (implementation : EliminationRollbackStore signature Physical Mark)
    (physical : Physical) (trace : EliminationTrace signature) :
    implementation.store.denote
        (implementation.executeBufferedTerminal physical trace) =
      implementation.store.denote
        (implementation.execute physical trace) := by
  rw [implementation.denote_execute]
  cases reason : trace.stop with
  | success =>
      rw [executeBufferedTerminal, reason]
      simp only [observe, reason]
      rw [implementation.store.writeMany_exact,
        implementation.logicalWriteMany_eq]
  | fuelExhausted | occursCheck | constructorConflict =>
      simp [executeBufferedTerminal, reason, observe]

/-- The buffered realization performs no physical writes on any failed
terminal suffix. -/
def bufferedWriteCount (trace : EliminationTrace signature) : Nat :=
  match trace.stop with
  | .success => trace.updates.length
  | _ => 0

omit [DecidableEq signature.vars]
  [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols] in
theorem bufferedWriteCount_eq_zero_of_failure
    (trace : EliminationTrace signature)
    (failed : trace.stop ≠ .success) :
    bufferedWriteCount trace = 0 := by
  cases reason : trace.stop <;> simp_all [bufferedWriteCount]

/-- Running and executing the trace therefore agrees exactly with the source
unifier's success/failure result at the physical denotation boundary. -/
theorem denote_execute_runTrace
    (implementation : EliminationRollbackStore signature Physical Mark)
    (physical : Physical) (fuel : Nat)
    (equations : List (Equation signature)) :
    implementation.store.denote
        (implementation.execute physical (runTrace fuel equations)) =
      match unifyFuel fuel equations with
      | some substitution =>
          substitution ∘ₛ implementation.store.denote physical
      | none => implementation.store.denote physical := by
  rw [implementation.denote_execute]
  rw [observe_runTrace_exact]

end EliminationRollbackStore

/-! ## Positive and negative controls -/

namespace Canaries

private inductive Constant where
  | zero
  | one
deriving DecidableEq

private inductive Variable where
  | left
  | right
deriving DecidableEq

private inductive Relation where
  | relation
deriving DecidableEq

private inductive Function where
  | unary
deriving DecidableEq

private def canarySignature : LPSignature where
  constants := Constant
  vars := Variable
  relationSymbols := Relation
  relationArity := fun _ => 0
  functionSymbols := Function
  functionArity := fun _ => 1

private def canaryVariableDecidableEq : DecidableEq canarySignature.vars := by
  change DecidableEq Variable
  infer_instance

private def canaryConstantDecidableEq : DecidableEq canarySignature.constants := by
  change DecidableEq Constant
  infer_instance

private def canaryFunctionDecidableEq :
    DecidableEq canarySignature.functionSymbols := by
  change DecidableEq Function
  infer_instance

private local instance : DecidableEq canarySignature.vars :=
  canaryVariableDecidableEq

private local instance : DecidableEq canarySignature.constants :=
  canaryConstantDecidableEq

private local instance : DecidableEq canarySignature.functionSymbols :=
  canaryFunctionDecidableEq

private def left : Term canarySignature := .var Variable.left
private def right : Term canarySignature := .var Variable.right
private def zero : Term canarySignature := .const Constant.zero
private def one : Term canarySignature := .const Constant.one

private def variableInventory :
    FiniteEnvironmentCompilation.Inventory Variable where
  keys := [.left, .right]
  nodup := by decide

private def emptyDenseState :
    AuthoritativeSlotTrailCompilation.State variableInventory
      (Term canarySignature) :=
  { slots := FiniteEnvironmentCompilation.emptyDenseEnvironment
      variableInventory
    trail := [] }

private def lateDenseWrites :
    List (FiniteEnvironmentCompilation.DenseWrite variableInventory
      (Term canarySignature)) :=
  [(⟨0, by decide⟩, zero)]
/-- A successful two-binding trace publishes both eliminations. -/
example :
    (runTrace 3 [(left, zero), (right, one)]).stop = .success ∧
      (runTrace 3 [(left, zero), (right, one)]).updates =
        [(Variable.left, zero), (Variable.right, one)] := by
  simp [runTrace, left, right, zero, one, canarySignature,
    Term.occursIn, Subst.applyEqs, Subst.applyTerm, Subst.single,
    EliminationTrace.record]

/-- An occurs-check stop never publishes a partial substitution.  The generic
exactness theorem above connects this stop reason to the source unifier. -/
example :
    observe ({ updates := [], stop := .occursCheck } :
      EliminationTrace canarySignature) = none := by
  rfl

/-- Rigid constructor conflict fails before any binding write. -/
example :
    (runTrace 2 [(zero, one)]).stop = .constructorConflict ∧
      (runTrace 2 [(zero, one)]).updates = [] := by
  simp [runTrace, zero, one, canarySignature]

/-- A later conflict retains the speculative prefix for physical rollback but
does not publish that partial binding. -/
example :
    observe (runTrace 3 [(left, zero), (zero, one)]) = none ∧
      (runTrace 3 [(left, zero), (zero, one)]).updates =
        [(Variable.left, zero)] := by
  simp [runTrace, left, zero, one, canarySignature, Term.occursIn,
    Subst.applyEqs, Subst.applyTerm,
    EliminationTrace.record, observe]

/-- The same late-conflict trace compiles through a generated variable
inventory to one dense write, and the value-restoring trail returns the exact
physical entrance state. -/
example :
    FiniteEnvironmentCompilation.compileWrites? variableInventory
        (runTrace 3 [(left, zero), (zero, one)]).updates =
      some lateDenseWrites ∧
    AuthoritativeSlotTrailCompilation.rollbackTo? variableInventory
        (AuthoritativeSlotTrailCompilation.mark emptyDenseState)
      (AuthoritativeSlotTrailCompilation.run variableInventory
          emptyDenseState lateDenseWrites) = some emptyDenseState := by
  constructor
  · let leftSlot : variableInventory.Slot := ⟨0, by decide⟩
    have selected :
        variableInventory.resolve? Variable.left = some leftSlot :=
      (variableInventory.resolve?_eq_some_iff Variable.left leftSlot).2 rfl
    simp [runTrace, left, zero, one, canarySignature, Term.occursIn,
      Subst.applyEqs, Subst.applyTerm, EliminationTrace.record,
      lateDenseWrites, FiniteEnvironmentCompilation.compileWrites?,
      FiniteEnvironmentCompilation.compileWrite?, selected, leftSlot]
  · exact AuthoritativeSlotTrailCompilation.rollbackTo?_run
      variableInventory emptyDenseState lateDenseWrites

/-- Fuel exhaustion after one elimination likewise retains the attempted write
only as rollback evidence. -/
example :
    (runTrace 1 [(left, zero), (right, one)]).stop = .fuelExhausted ∧
      observe (runTrace 1 [(left, zero), (right, one)]) = none ∧
      (runTrace 1 [(left, zero), (right, one)]).updates =
        [(Variable.left, zero)] := by
  simp [runTrace, left, zero, canarySignature, Term.occursIn,
    EliminationTrace.record, observe]

/-- A failed terminal suffix may retain attempted writes as evidence while
the buffered physical realization performs none of them. -/
example :
    (runTrace 3 [(left, zero), (zero, one)]).updates.length = 1 ∧
      EliminationRollbackStore.bufferedWriteCount
        (runTrace 3 [(left, zero), (zero, one)]) = 0 := by
  simp [runTrace, left, zero, one, canarySignature, Term.occursIn,
    Subst.applyEqs, Subst.applyTerm, EliminationTrace.record,
    EliminationRollbackStore.bufferedWriteCount]

/-- Successful terminal suffixes publish every chronological write. -/
example :
    EliminationRollbackStore.bufferedWriteCount
        (runTrace 3 [(left, zero), (right, one)]) = 2 := by
  decide

end Canaries

#print axioms observe_runTrace_exact
#print axioms eliminationTraceRealization
#print axioms EliminationRollbackStore.logicalWriteMany_eq
#print axioms EliminationRollbackStore.denote_execute
#print axioms EliminationRollbackStore.denote_executeBufferedTerminal
#print axioms EliminationRollbackStore.bufferedWriteCount_eq_zero_of_failure
#print axioms EliminationRollbackStore.denote_execute_runTrace

end Mettapedia.GSLT.LanguageDef.UnificationEliminationTraceCompilation
