import Mettapedia.Machines.RegisterCode
import Mettapedia.Machines.TIsa.CellEffects

/-!
# RegisterCode operands in the transform profile

The source instruction and its scoping/liveness machinery are RegisterCode's.
Only scalar operations are interpreted here. Calls remain a compilation
boundary. Literal operands consume no resource, and repeated register operands
share their occurrence through the finite cell recipe.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.RegisterProfile

open Cells CellEffects

def truth (value : Word) : Option Bool :=
  if value = 0 then some false else if value = 1 then some true else none

def semantics : RegisterCode.Sem Word Word Scalar Nat Nat where
  patReads _ := []
  patSlots pattern := [pattern]
  lit := id
  op := Scalar.evaluate
  truth := truth
  bindLet pattern value registers := some (Function.update registers pattern (some value))
  bindLet_frame := by
    intro pattern value registers after same key outside
    cases same
    exact Function.update_of_ne (by simpa using outside) _ _
  bindLet_local := by
    intro pattern value left right _
    refine Option.Rel.some fun key member => ?_
    simp only [List.mem_singleton] at member
    subst key
    simp
  enter _ _ := none

def operandValue (values : Nat → Word) : RegisterCode.Operand Word → Word
  | .reg index => values index
  | .lit value => value

def operandRegisters : List (RegisterCode.Operand Word) → List Nat
  | [] => []
  | .reg index :: later => index :: operandRegisters later
  | .lit _ :: later => operandRegisters later

def rebuild : List (RegisterCode.Operand Word) → List Word → Option (List Word)
  | [], [] => some []
  | .reg _ :: later, value :: remaining => (rebuild later remaining).map (value :: ·)
  | .lit value :: later, remaining => (rebuild later remaining).map (value :: ·)
  | _, _ => none

theorem rebuild_readback (arguments : List (RegisterCode.Operand Word)) (values : Nat → Word) :
    rebuild arguments ((operandRegisters arguments).map values) =
      some (arguments.map (operandValue values)) := by
  induction arguments with
  | nil => rfl
  | cons argument later ih =>
      cases argument <;> simp [rebuild, operandRegisters, operandValue, ih]

def initialized (values : Nat → Word) : RegisterCode.Regs Word := fun register => some (values register)

def initializedOn (keys : Finset Nat) (values : Nat → Word) : RegisterCode.Regs Word :=
  fun register => if register ∈ keys then some (values register) else none

/-- Reuse the source's backward liveness; a dead initial slot needs no value. -/
def initialCheck (code : List (RegisterCode.Instr Word Scalar Nat Nat)) (initializedKeys out : Finset Nat) : Bool :=
  decide (RegisterCode.liveIn semantics.toPatterns code out ⊆ initializedKeys)

theorem initialCheck_iff (code : List (RegisterCode.Instr Word Scalar Nat Nat)) (initializedKeys out : Finset Nat) :
    initialCheck code initializedKeys out = true ↔
      RegisterCode.liveIn semantics.toPatterns code out ⊆ initializedKeys := by
  exact decide_eq_true_iff

theorem partial_initialization_live (code : List (RegisterCode.Instr Word Scalar Nat Nat))
    (initializedKeys out : Finset Nat) (values : Nat → Word)
    (checked : initialCheck code initializedKeys out = true) :
    Option.Rel (RegisterCode.Outcome.Agree out)
      (RegisterCode.exec semantics (fun _ _ => none) code (initialized values))
      (RegisterCode.exec semantics (fun _ _ => none) code (initializedOn initializedKeys values)) := by
  apply RegisterCode.exec_live
  intro register live
  have present := (initialCheck_iff code initializedKeys out).mp checked live
  simp [initialized, initializedOn, present]

theorem readAll_initialized (arguments : List (RegisterCode.Operand Word)) (values : Nat → Word) :
    RegisterCode.readAll semantics (initialized values) arguments = some (arguments.map (operandValue values)) := by
  induction arguments with
  | nil => rfl
  | cons argument later ih =>
      cases argument <;> simp only [RegisterCode.readAll, RegisterCode.read, ih] <;> rfl

structure Write where
  destination : Nat
  operation : Scalar
  arguments : List (RegisterCode.Operand Word)

def Write.source (write : Write) : RegisterCode.Instr Word Scalar Nat Nat :=
  .op write.destination write.operation write.arguments

def Write.recipe (write : Write) : Recipe Nat where
  inputs := operandRegisters write.arguments
  outputs := [write.destination]
  guard := fun inputs outputs => match outputs with
    | [result] => ((rebuild write.arguments inputs).bind write.operation.evaluate) == some result
    | _ => false

theorem Write.guard_iff (write : Write) (before after : Nat → Word) :
    write.recipe.guard (write.recipe.inputs.map before) (write.recipe.outputs.map after) = true ↔
      write.operation.evaluate (write.arguments.map (operandValue before)) = some (after write.destination) := by
  simp [recipe, rebuild_readback]

theorem Write.source_step (write : Write) (before : Nat → Word) :
    RegisterCode.step semantics (fun _ _ => none) write.source (initialized before) =
      (write.operation.evaluate (write.arguments.map (operandValue before))).map
        (fun value => .next (initialized (Function.update before write.destination value))) := by
  change ((RegisterCode.readAll semantics (initialized before) write.arguments).bind fun arguments =>
    (write.operation.evaluate arguments).map fun value =>
      RegisterCode.Outcome.next (Function.update (initialized before) write.destination (some value))) = _
  rw [readAll_initialized]
  simp only [Option.bind_some]
  congr 1
  funext value
  congr 1
  funext register
  by_cases same : register = write.destination <;> simp [initialized, same]

theorem Write.overwrite_eq (write : Write) (before after : Nat → Word) :
    overwrite write.recipe.writes before after = Function.update before write.destination (after write.destination) := by
  funext register
  by_cases same : register = write.destination <;> simp [overwrite, Recipe.writes, recipe, same]

/-- A source scalar step realizes the actual consume/keep/produce operation. -/
theorem Write.realized (write : Write) (keys : Finset Nat) (before : Nat → Word) (result : Word)
    (included : write.recipe.support ⊆ keys)
    (computed : write.operation.evaluate (write.arguments.map (operandValue before)) = some result) :
    ∃ invocation : Invocation write.recipe,
      CellEffects.system.Enables (encode keys before) invocation ∧
      CellEffects.system.fire (encode keys before) invocation =
        encode keys (Function.update before write.destination result) := by
  let after := Function.update before write.destination result
  have guarded : write.recipe.guard (write.recipe.inputs.map before) (write.recipe.outputs.map after) = true := by
    apply (write.guard_iff before after).mpr
    simpa [after] using computed
  obtain ⟨invocation, enabled, equal⟩ := effect_realized write.recipe keys before after included guarded
  refine ⟨invocation, enabled, ?_⟩
  simpa [write.overwrite_eq, after] using equal

def operandFits : RegisterCode.Operand Word → Bool
  | .reg register => decide (register < 12)
  | .lit _ => true

/-- This scalar compilation tranche explicitly declines all non-write forms. -/
def scalarWrite? : RegisterCode.Instr Word Scalar Nat Nat → Option Write
  | .move destination argument =>
      if destination < 12 && operandFits argument then
        some ⟨destination, .copy, [argument]⟩ else none
  | .op destination operation arguments =>
      if destination < 12 && arguments.all operandFits then
        some ⟨destination, operation, arguments⟩ else none
  | .bind argument destination =>
      if destination < 12 && operandFits argument then
        some ⟨destination, .copy, [argument]⟩ else none
  | _ => none

theorem scalarWrite?_source_step (instruction : RegisterCode.Instr Word Scalar Nat Nat)
    (write : Write) (accepted : scalarWrite? instruction = some write) (before : Nat → Word) :
    RegisterCode.step semantics (fun _ _ => none) instruction (initialized before) =
      RegisterCode.step semantics (fun _ _ => none) write.source (initialized before) := by
  cases instruction with
  | move destination argument =>
      simp only [scalarWrite?] at accepted
      split at accepted
      · cases Option.some.inj accepted
        cases argument <;> rfl
      · cases accepted
  | op destination operation arguments =>
      simp only [scalarWrite?] at accepted
      split at accepted
      · cases Option.some.inj accepted
        rfl
      · cases accepted
  | bind argument destination =>
      simp only [scalarWrite?] at accepted
      split at accepted
      · cases Option.some.inj accepted
        cases argument <;> rfl
      · cases accepted
  | opRet operation arguments => cases accepted
  | ite condition yes no => cases accepted
  | iteOp operation arguments yes no => cases accepted
  | call destination head arguments => cases accepted
  | tailCall head arguments => cases accepted
  | ret result => cases accepted

theorem scalarWrite?_refines (instruction : RegisterCode.Instr Word Scalar Nat Nat)
    (write : Write) (accepted : scalarWrite? instruction = some write) (before : Nat → Word) :
    RegisterCode.step semantics (fun _ _ => none) instruction (initialized before) =
      (write.operation.evaluate (write.arguments.map (operandValue before))).map
        (fun value => RegisterCode.Outcome.next (initialized (Function.update before write.destination value))) := by
  rw [scalarWrite?_source_step instruction write accepted, write.source_step]

theorem operandRegisters_eq (arguments : List (RegisterCode.Operand Word)) :
    (operandRegisters arguments).toFinset = RegisterCode.operandRegs arguments := by
  induction arguments with
  | nil => rfl
  | cons argument later ih =>
      cases argument <;> simp [operandRegisters, RegisterCode.operandRegs, RegisterCode.Operand.regs, ih]

/-- The recipe reads exactly the source operand part of RegisterCode's live-in. -/
theorem Write.liveIn (write : Write) (out : Finset Nat) :
    RegisterCode.liveStep semantics.toPatterns write.source out =
      out.erase write.destination ∪ write.recipe.inputs.toFinset := by
  simp [source, RegisterCode.liveStep, recipe, operandRegisters_eq]

theorem Write.source_live (write : Write) (out : Finset Nat)
    (left right : RegisterCode.Regs Word)
    (agree : ∀ register ∈ out.erase write.destination ∪ write.recipe.inputs.toFinset,
      left register = right register) :
    Option.Rel (RegisterCode.Outcome.Agree out)
      (RegisterCode.step semantics (fun _ _ => none) write.source left)
      (RegisterCode.step semantics (fun _ _ => none) write.source right) := by
  apply RegisterCode.step_live
  rw [write.liveIn]
  exact agree

/-- Independent scalar readback of a prescribed, ordered resource block. -/
def runWrites : List Write → (Nat → Word) → Option (Nat → Word)
  | [], before => some before
  | write :: later, before => do
      let value ← write.operation.evaluate (write.arguments.map (operandValue before))
      runWrites later (Function.update before write.destination value)

theorem runWrites_source (writes : List Write) (before : Nat → Word) :
    RegisterCode.exec semantics (fun _ _ => none) (writes.map Write.source) (initialized before) =
      (runWrites writes before).map (fun after => RegisterCode.Outcome.next (initialized after)) := by
  induction writes generalizing before with
  | nil => rfl
  | cons write later ih =>
      simp only [List.map_cons, RegisterCode.exec, write.source_step, runWrites]
      cases computed : write.operation.evaluate (write.arguments.map (operandValue before)) with
      | none => rfl
      | some value =>
          simpa only [Option.bind_eq_bind, Option.map_some, Option.bind_some, RegisterCode.andThen] using
            ih (Function.update before write.destination value)

def lowerWrites? (instructions : List (RegisterCode.Instr Word Scalar Nat Nat)) : Option (List Write) :=
  instructions.mapM scalarWrite?

theorem lowerWrites?_source (instructions : List (RegisterCode.Instr Word Scalar Nat Nat))
    (writes : List Write) (accepted : lowerWrites? instructions = some writes) (before : Nat → Word) :
    RegisterCode.exec semantics (fun _ _ => none) instructions (initialized before) =
      (runWrites writes before).map (fun after => RegisterCode.Outcome.next (initialized after)) := by
  induction instructions generalizing writes before with
  | nil =>
      have same : writes = [] := (Option.some.inj accepted).symm
      subst writes
      rfl
  | cons instruction later ih =>
      simp only [lowerWrites?, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at accepted
      obtain ⟨write, first, remaining, rest, equal⟩ := accepted
      have same : writes = write :: remaining := (Option.some.inj equal).symm
      subst writes
      simp only [RegisterCode.exec, scalarWrite?_refines instruction write first, runWrites]
      cases computed : write.operation.evaluate (write.arguments.map (operandValue before)) with
      | none => rfl
      | some value =>
          simpa only [Option.bind_eq_bind, Option.map_some, Option.bind_some, RegisterCode.andThen] using
            ih remaining rest (Function.update before write.destination value)

namespace Controls

example : rebuild [.lit 9, .reg 2, .reg 2] [7, 7] = some [9, 7, 7] := by decide
example : rebuild [.reg 2] [] = none := by decide
example : (scalarWrite? (.call 0 1 [.reg 0])).isNone = true := by decide
example : (scalarWrite? (.op 12 (.binary .add) [.reg 0, .lit 1])).isNone = true := by decide
example : (scalarWrite? (.op 1 (.binary .add) [.reg 0, .lit 1])).isSome = true := by decide

example : initialCheck [.op 0 (.binary .add) [.reg 1, .lit 1]] {1} {0} = true := by decide
example : initialCheck [.op 0 (.binary .add) [.reg 1, .lit 1]] ∅ {0} = false := by decide
example : initialCheck [.move 0 (.lit 7)] ∅ {0} = true := by decide

end Controls

end Mettapedia.Machines.TIsa.RegisterProfile
