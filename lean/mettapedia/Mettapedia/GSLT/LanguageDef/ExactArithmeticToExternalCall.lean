import Mettapedia.GSLT.LanguageDef.ExternalCallMachine
import Mettapedia.GSLT.LanguageDef.ExternalCallMachineTransitionAdmission
import Mettapedia.GSLT.LanguageDef.ExactArithmeticNTT
import Mettapedia.GSLT.LanguageDef.ArithmeticExternalCallPilot
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Exact-arithmetic lowering into the authored external-call machine

This module defines the first compiler boundary between the independently
authored exact-arithmetic and external-call language definitions. It lowers each
canonical arithmetic operation term to an external-call program term. Partial operations
receive an explicit zero-divisor branch before the external call; total
operations call the external directly.

The results below establish canonical source decoding, compiler-image
soundness, injectivity, exact instruction layouts, and a negative control for
an unguarded partial operation.  The universal section then proves the
request-local source/target operational square, including preservation and
no-invention for both completion outcomes and exact ordered receipts.  C data
structures, emitted C, GMP, linked execution, and NIK admission remain
separate realization boundaries.
-/

namespace Mettapedia.GSLT.LanguageDef.ExactArithmeticToExternalCall

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.ArithmeticExtension.ExactInteger
open Mettapedia.GSLT.LanguageDef.ExternalCallMachine
open Mettapedia.GSLT.LanguageDef.ExternalCallMachineTransitionAdmission
open Mettapedia.GSLT.LanguageDef.ExactArithmeticNTT

def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def natPattern : Nat → Pattern
  | 0 => a "external-call:nat-zero"
  | n + 1 => a "external-call:nat-succ" [natPattern n]

def slot (index : Nat) : Pattern :=
  a "external-call:slot-id" [natPattern index]

def label (index : Nat) : Pattern :=
  a "external-call:label" [natPattern index]

def external (index : Nat) : Pattern :=
  a "external-call:external-id" [natPattern index]

/-- A builtin-string atom in the canonical theorem-side pattern carrier. -/
private def stringAtom (value : String) : Pattern := a value

def fault (className : String) : Pattern :=
  a "external-call:fault" [stringAtom className]

private def instructionList : List Pattern → Pattern
  | [] => a "external-call:instruction-nil"
  | instruction :: rest =>
      a "external-call:instruction-cons" [instruction, instructionList rest]

private def externalList : List Pattern → Pattern
  | [] => a "external-call:external-nil"
  | declaration :: rest =>
      a "external-call:external-cons" [declaration, externalList rest]

def targetLinkName : CoreOp → String
  | .add => "cetta_external_call_exact_integer_add_v1"
  | .sub => "cetta_external_call_exact_integer_sub_v1"
  | .mul => "cetta_external_call_exact_integer_mul_v1"
  | .tquot => "cetta_external_call_exact_integer_tquot_v1"
  | .fquot => "cetta_external_call_exact_integer_fquot_v1"
  | .trem => "cetta_external_call_exact_integer_trem_v1"
  | .frem => "cetta_external_call_exact_integer_frem_v1"

private def binaryExternal (operation : CoreOp) : Pattern :=
  a "external-call:binary-external"
    [external 0, stringAtom (targetLinkName operation),
     slot 0, slot 1, slot 2]

private def callExternal (value language engine resource : Nat) : Pattern :=
  a "external-call:call-binary"
    [external 0, label value, label language, label engine, label resource]

private def returnValue : Pattern := a "external-call:return-value" [slot 2]
private def returnDeclined : Pattern := a "external-call:return-declined"
private def returnLanguageFault : Pattern :=
  a "external-call:return-language-fault" [fault "language-fault"]
private def returnEngineFault : Pattern :=
  a "external-call:return-engine-fault" [fault "engine-fault"]
private def returnResourceFault : Pattern :=
  a "external-call:return-resource-fault" [fault "resource-fault"]

private def totalProgram (operation : CoreOp) : Pattern :=
  a "external-call:program"
    [instructionList [
       callExternal 1 2 3 4,
       returnValue,
       returnLanguageFault,
       returnEngineFault,
       returnResourceFault],
     externalList [binaryExternal operation],
     label 0]

private def guardedProgram (operation : CoreOp) : Pattern :=
  a "external-call:program"
    [instructionList [
       a "external-call:branch-zero" [slot 1, label 1, label 2],
       returnDeclined,
       callExternal 3 4 5 6,
       returnValue,
       returnLanguageFault,
       returnEngineFault,
       returnResourceFault],
     externalList [binaryExternal operation],
     label 0]

/-- Canonical exact-arithmetic operation terms in the authored source
language. -/
def encodeSourceOperation : CoreOp → Pattern
  | .add => a "arith:add"
  | .sub => a "arith:sub"
  | .mul => a "arith:mul"
  | .tquot => a "arith:tquot"
  | .fquot => a "arith:fquot"
  | .trem => a "arith:trem"
  | .frem => a "arith:frem"

/-- Fail-closed decoding of the canonical operation fragment. -/
def decodeSourceOperation? : Pattern → Option CoreOp
  | .apply "arith:add" [] => some .add
  | .apply "arith:sub" [] => some .sub
  | .apply "arith:mul" [] => some .mul
  | .apply "arith:tquot" [] => some .tquot
  | .apply "arith:fquot" [] => some .fquot
  | .apply "arith:trem" [] => some .trem
  | .apply "arith:frem" [] => some .frem
  | _ => none

/-- The typed compiler into the authored ExternalCall program vocabulary. -/
def compileCoreOperation (operation : CoreOp) : Pattern :=
  if operation.isPartial then guardedProgram operation else totalProgram operation

/-- The canonical pattern-level compiler is defined only on the exact
arithmetic operation fragment. -/
def compileSourceOperation? (source : Pattern) : Option Pattern :=
  (decodeSourceOperation? source).map compileCoreOperation

def CompilerImage (target : Pattern) : Prop :=
  ∃ operation, compileCoreOperation operation = target

@[simp] theorem decode_encode_source (operation : CoreOp) :
    decodeSourceOperation? (encodeSourceOperation operation) = some operation := by
  cases operation <;> rfl

theorem encodeSourceOperation_injective :
    Function.Injective encodeSourceOperation := by
  intro first second equal
  cases first <;> cases second <;>
    simp [encodeSourceOperation, a] at equal ⊢

@[simp] theorem compile_encoded_source (operation : CoreOp) :
    compileSourceOperation? (encodeSourceOperation operation) =
      some (compileCoreOperation operation) := by
  cases operation <;> rfl

/-- Every successful compiler result is in the image of the seven authored
source operations. -/
theorem successful_compilation_has_source {source target : Pattern}
    (compiled : compileSourceOperation? source = some target) :
    CompilerImage target := by
  unfold compileSourceOperation? at compiled
  cases decoded : decodeSourceOperation? source with
  | none => simp [decoded] at compiled
  | some operation =>
      simp [decoded] at compiled
      exact ⟨operation, compiled⟩

/-- Malformed constructor arity is rejected rather than repaired. -/
theorem malformed_add_rejected :
    compileSourceOperation? (a "arith:add" [a "invented-argument"]) = none := by
  rfl

def instructionCount? : Pattern → Option Nat
  | .apply "external-call:instruction-nil" [] => some 0
  | .apply "external-call:instruction-cons" [_instruction, rest] =>
      (instructionCount? rest).map Nat.succ
  | _ => none

def beginsWithZeroGuard : Pattern → Bool
  | .apply "external-call:program"
      [.apply "external-call:instruction-cons"
        [.apply "external-call:branch-zero" [_slot, _zero, _nonzero], _rest],
       _externals, _entry] => true
  | _ => false

def beginsWithExternalCall : Pattern → Bool
  | .apply "external-call:program"
      [.apply "external-call:instruction-cons"
        [.apply "external-call:call-binary"
          [_external, _value, _language, _engine, _resource], _rest],
       _externals, _entry] => true
  | _ => false

def programInstructionCount? : Pattern → Option Nat
  | .apply "external-call:program" [instructions, _externals, _entry] =>
      instructionCount? instructions
  | _ => none

theorem compiled_layout (operation : CoreOp) :
    if operation.isPartial then
      beginsWithZeroGuard (compileCoreOperation operation) = true ∧
      programInstructionCount? (compileCoreOperation operation) = some 7
    else
      beginsWithExternalCall (compileCoreOperation operation) = true ∧
      programInstructionCount? (compileCoreOperation operation) = some 5 := by
  cases operation <;> decide

/-- Operation identity survives compilation through the external link name,
so distinct arithmetic operations cannot collapse to one ExternalCall program. -/
theorem compileCoreOperation_injective :
    Function.Injective compileCoreOperation := by
  intro first second equal
  cases first <;> cases second <;>
    simp [compileCoreOperation, guardedProgram, totalProgram, binaryExternal,
      targetLinkName, CoreOp.isPartial, instructionList, externalList, natPattern,
      slot, label, external, stringAtom, callExternal, returnValue,
      returnDeclined, returnLanguageFault, returnEngineFault,
      returnResourceFault, fault, a] at equal ⊢

/-- A finite translation validator for the exact compiler image.  It accepts
only one of the seven canonical guarded/total layouts above. -/
def decodeCompiledOperation? (target : Pattern) : Option CoreOp :=
  if target = compileCoreOperation .add then some .add
  else if target = compileCoreOperation .sub then some .sub
  else if target = compileCoreOperation .mul then some .mul
  else if target = compileCoreOperation .tquot then some .tquot
  else if target = compileCoreOperation .fquot then some .fquot
  else if target = compileCoreOperation .trem then some .trem
  else if target = compileCoreOperation .frem then some .frem
  else none

@[simp] theorem decode_compiled_operation (operation : CoreOp) :
    decodeCompiledOperation? (compileCoreOperation operation) =
      some operation := by
  cases operation <;>
    simp [decodeCompiledOperation?, compileCoreOperation_injective.eq_iff]

/-- Validator acceptance reflects exact compiler-image membership rather than
merely checking a shared endpoint or instruction count. -/
theorem decode_compiled_operation_sound {target : Pattern} {operation : CoreOp}
    (decoded : decodeCompiledOperation? target = some operation) :
    target = compileCoreOperation operation := by
  unfold decodeCompiledOperation? at decoded
  split at decoded <;> rename_i addEqual
  · cases decoded
    exact addEqual
  split at decoded <;> rename_i subEqual
  · cases decoded
    exact subEqual
  split at decoded <;> rename_i mulEqual
  · cases decoded
    exact mulEqual
  split at decoded <;> rename_i tquotEqual
  · cases decoded
    exact tquotEqual
  split at decoded <;> rename_i fquotEqual
  · cases decoded
    exact fquotEqual
  split at decoded <;> rename_i tremEqual
  · cases decoded
    exact tremEqual
  split at decoded <;> rename_i fremEqual
  · cases decoded
    exact fremEqual
  · contradiction

/-- A partial operation emitted without its zero-divisor branch is outside
the compiler image, even though the raw ExternalCall vocabulary can express it. -/
theorem unguarded_tquot_not_in_compiler_image :
    ¬ CompilerImage (totalProgram .tquot) := by
  intro image
  rcases image with ⟨operation, equal⟩
  cases operation <;>
    simp [compileCoreOperation, guardedProgram, totalProgram, binaryExternal,
      targetLinkName, CoreOp.isPartial, instructionList, externalList, natPattern,
      slot, label, external, stringAtom, callExternal, returnValue,
      returnDeclined, returnLanguageFault, returnEngineFault,
      returnResourceFault, fault, a] at equal

theorem unguarded_tquot_validator_rejects :
    decodeCompiledOperation? (totalProgram .tquot) = none := by
  simp only [decodeCompiledOperation?]
  split <;> rename_i addEqual
  · exact False.elim (unguarded_tquot_not_in_compiler_image
      ⟨.add, addEqual.symm⟩)
  split <;> rename_i subEqual
  · exact False.elim (unguarded_tquot_not_in_compiler_image
      ⟨.sub, subEqual.symm⟩)
  split <;> rename_i mulEqual
  · exact False.elim (unguarded_tquot_not_in_compiler_image
      ⟨.mul, mulEqual.symm⟩)
  split <;> rename_i tquotEqual
  · exact False.elim (unguarded_tquot_not_in_compiler_image
      ⟨.tquot, tquotEqual.symm⟩)
  split <;> rename_i fquotEqual
  · exact False.elim (unguarded_tquot_not_in_compiler_image
      ⟨.fquot, fquotEqual.symm⟩)
  split <;> rename_i tremEqual
  · exact False.elim (unguarded_tquot_not_in_compiler_image
      ⟨.trem, tremEqual.symm⟩)
  split <;> rename_i fremEqual
  · exact False.elim (unguarded_tquot_not_in_compiler_image
      ⟨.frem, fremEqual.symm⟩)
  · rfl

/-- Both the source operation vocabulary and the target instruction
vocabulary used by the compiler occur in their independently authored
LanguageDefs. -/
theorem compiler_vocabulary_is_authored :
    (∀ sourceLabel ∈
        ["arith:add", "arith:sub", "arith:mul", "arith:tquot",
         "arith:fquot", "arith:trem", "arith:frem"],
      sourceLabel ∈ exactArithmetic.terms.map (·.label)) ∧
    (∀ targetLabel ∈
        ["external-call:program", "external-call:branch-zero", "external-call:call-binary",
         "external-call:return-value", "external-call:return-declined",
         "external-call:return-language-fault", "external-call:return-engine-fault",
         "external-call:return-resource-fault", "external-call:binary-external"],
      targetLabel ∈ externalCallLanguage.terms.map (·.label)) := by
  decide

/-! ## Executable source-to-target canaries

These finite OSLF executions cross the actual compiler boundary above.  Their
relation environments state independent facts for one external call and one
zero test; they are not a universal external-call adequacy theorem.
-/

private def exactInteger (name : String) : Pattern :=
  a "external-call:exact-integer" [a name]

def slotEmpty : Pattern := a "external-call:slot-empty"
def slotValue (value : Pattern) : Pattern := a "external-call:slot-value" [value]
def storeNil : Pattern := a "external-call:store-nil"
def storeCons (value rest : Pattern) : Pattern :=
  a "external-call:store-cons" [value, rest]

def store3 (first second third : Pattern) : Pattern :=
  storeCons first (storeCons second (storeCons third storeNil))

private def fuelInfinite : Pattern := a "external-call:fuel-infinite"
def receiptNil : Pattern := a "external-call:receipt-nil"

private def run (program pc store receipt : Pattern) : Pattern :=
  a "external-call:run" [program, pc, store, fuelInfinite, receipt]

private def halted (outcome receipt : Pattern) : Pattern :=
  a "external-call:halted" [outcome, receipt]

def stepReceipt (pc receipt : Pattern) : Pattern :=
  a "external-call:receipt-cons" [a "external-call:step-event" [pc], receipt]

def externalReceipt
    (externalId outcome pc receipt : Pattern) : Pattern :=
  a "external-call:receipt-cons"
    [a "external-call:external-event" [externalId, outcome], stepReceipt pc receipt]

private def addTwo : Pattern := exactInteger "integer:2"
private def addThree : Pattern := exactInteger "integer:3"
private def addFive : Pattern := exactInteger "integer:5"
private def zero : Pattern := exactInteger "integer:0"

private def addStore : Pattern :=
  store3 (slotValue addTwo) (slotValue addThree) slotEmpty

private def addResultStore : Pattern :=
  store3 (slotValue addTwo) (slotValue addThree) (slotValue addFive)

private def addExternalOutcome : Pattern :=
  a "external-call:external-value" [addResultStore]

def addDemoRelationEnv : RelationEnv where
  tuples := fun relation _arguments =>
    if relation == "ExternalCallConsumeFuel" then
      [[fuelInfinite, fuelInfinite]]
    else if relation == "ExternalCallFetchInstruction" then
      [[compileCoreOperation .add, label 0, callExternal 1 2 3 4],
       [compileCoreOperation .add, label 1, returnValue]]
    else if relation == "ExternalCallCallBinaryExternal" then
      [[compileCoreOperation .add, external 0, addStore, addExternalOutcome]]
    else if relation == "ExternalCallReadSlot" then
      [[addResultStore, slot 2, addFive]]
    else
      []

private def addStart : Pattern :=
  run (compileCoreOperation .add) (label 0) addStore receiptNil

private def addDone : Pattern :=
  halted (a "external-call:outcome-value" [addFive])
    (stepReceipt (label 1)
      (externalReceipt (external 0) addExternalOutcome (label 0) receiptNil))

/-- The compiled addition program executes through ExternalCall's authored call and
return rules to the same endpoint as the exact-arithmetic source demo. -/
theorem compiled_add_executes_exactly :
    normalizeFirstUsing addDemoRelationEnv externalCallLanguage 1 2 addStart = addDone := by
  decide +kernel

private def tquotStore : Pattern :=
  store3 (slotValue addThree) (slotValue zero) slotEmpty

def tquotZeroDemoRelationEnv : RelationEnv where
  tuples := fun relation _arguments =>
    if relation == "ExternalCallConsumeFuel" then
      [[fuelInfinite, fuelInfinite]]
    else if relation == "ExternalCallFetchInstruction" then
      [[compileCoreOperation .tquot, label 0,
        a "external-call:branch-zero" [slot 1, label 1, label 2]],
       [compileCoreOperation .tquot, label 1, returnDeclined]]
    else if relation == "ExternalCallReadSlot" then
      [[tquotStore, slot 1, zero]]
    else if relation == "ExternalCallIsZero" then
      [[zero]]
    else
      []

private def tquotZeroStart : Pattern :=
  run (compileCoreOperation .tquot) (label 0) tquotStore receiptNil

private def tquotZeroDone : Pattern :=
  halted (a "external-call:outcome-declined")
    (stepReceipt (label 1) (stepReceipt (label 0) receiptNil))

/-- The zero divisor takes the authored guard and never reaches the external
call relation. -/
theorem compiled_tquot_zero_declines_exactly :
    normalizeFirstUsing tquotZeroDemoRelationEnv externalCallLanguage 1 2 tquotZeroStart =
      tquotZeroDone := by
  decide +kernel

/-- Negative control: the guarded zero-divisor execution cannot invent the
value returned by the positive addition path. -/
theorem compiled_tquot_zero_does_not_invent_add_value :
    normalizeFirstUsing tquotZeroDemoRelationEnv externalCallLanguage 1 2 tquotZeroStart ≠
      addDone := by
  decide +kernel

/-! ## Universal authored-ExternalCall reference execution

The finite canaries above are useful diagnostics.  This section supplies the
next stronger boundary: a relation environment for every exact operation and
integer pair.  Its external result is computed by the independently defined
target operation from `ArithmeticExternalCallPilot`, never by `coreSem` or by the C
implementation.  A separate theorem then connects that target operation to
the source mathematical semantics.

This reference environment models only the admitted successful exact-integer
external.  Language, engine, resource, and finite-fuel outcomes remain part of
the authored ExternalCall GSLT and require their own realization contracts.
-/

private def targetOperation (operation : CoreOp) :
    ArithmeticExternalCallPilot.CompiledOp :=
  ArithmeticExternalCallPilot.compileSyntax operation

def targetUndefinedAt (operation : CoreOp) (second : Int) : Prop :=
  (targetOperation operation).undefinedAt second

private instance targetUndefinedAtDecidable
    (operation : CoreOp) (second : Int) :
    Decidable (targetUndefinedAt operation second) := by
  unfold targetUndefinedAt
  infer_instance

def targetValue (operation : CoreOp) (first second : Int) : Int :=
  (targetOperation operation).fn first second

def integerAtom (value : Int) : Pattern := a (toString value)
def exactIntegerValue (value : Int) : Pattern :=
  a "external-call:exact-integer" [integerAtom value]

def inputStore (first second : Int) : Pattern :=
  store3 (slotValue (exactIntegerValue first))
    (slotValue (exactIntegerValue second)) slotEmpty

def resultStore (operation : CoreOp) (first second : Int) : Pattern :=
  store3 (slotValue (exactIntegerValue first))
    (slotValue (exactIntegerValue second))
    (slotValue (exactIntegerValue (targetValue operation first second)))

def targetExternalValue
    (operation : CoreOp) (first second : Int) : Pattern :=
  a "external-call:external-value" [resultStore operation first second]

private def totalFetchRows (operation : CoreOp) : List (List Pattern) :=
  let program := compileCoreOperation operation
  [
    [program, label 0, callExternal 1 2 3 4],
    [program, label 1, returnValue],
    [program, label 2, returnLanguageFault],
    [program, label 3, returnEngineFault],
    [program, label 4, returnResourceFault]
  ]

private def guardedFetchRows (operation : CoreOp) : List (List Pattern) :=
  let program := compileCoreOperation operation
  [
    [program, label 0, a "external-call:branch-zero" [slot 1, label 1, label 2]],
    [program, label 1, returnDeclined],
    [program, label 2, callExternal 3 4 5 6],
    [program, label 3, returnValue],
    [program, label 4, returnLanguageFault],
    [program, label 5, returnEngineFault],
    [program, label 6, returnResourceFault]
  ]

private def fetchRows (operation : CoreOp) : List (List Pattern) :=
  if operation.isPartial then guardedFetchRows operation
  else totalFetchRows operation

/-- A request-local, independently target-defined realization of ExternalCall's open
relations.  Returning complete tuples lets the generic relation-query matcher
bind outputs while checking every already-bound input. -/
def arithmeticExternalCallReferenceEnv
    (operation : CoreOp) (first second : Int) : RelationEnv where
  tuples := fun relation _arguments =>
    if relation == "ExternalCallConsumeFuel" then
      [[fuelInfinite, fuelInfinite]]
    else if relation == "ExternalCallFetchInstruction" then
      fetchRows operation
    else if relation == "ExternalCallReadSlot" then
      [[inputStore first second, slot 1, exactIntegerValue second],
       [resultStore operation first second, slot 2,
        exactIntegerValue (targetValue operation first second)]]
    else if relation == "ExternalCallIsZero" then
      if second = 0 then [[exactIntegerValue second]] else []
    else if relation == "ExternalCallIsNonzero" then
      if second = 0 then [] else [[exactIntegerValue second]]
    else if relation == "ExternalCallCallBinaryExternal" then
      if targetUndefinedAt operation second then [] else
        [[compileCoreOperation operation, external 0,
          inputStore first second,
          targetExternalValue operation first second]]
    else
      []

def compiledExternalCallStart (operation : CoreOp) (first second : Int) : Pattern :=
  run (compileCoreOperation operation) (label 0)
    (inputStore first second) receiptNil

def compiledExternalCallOutcome (operation : CoreOp) (first second : Int) : Pattern :=
  if targetUndefinedAt operation second then
    a "external-call:outcome-declined"
  else
    a "external-call:outcome-value" [exactIntegerValue (targetValue operation first second)]

def compiledExternalCallReceipt (operation : CoreOp) (first second : Int) : Pattern :=
  if targetUndefinedAt operation second then
    stepReceipt (label 1) (stepReceipt (label 0) receiptNil)
  else if operation.isPartial then
    stepReceipt (label 3)
      (externalReceipt (external 0)
        (targetExternalValue operation first second) (label 2)
        (stepReceipt (label 0) receiptNil))
  else
    stepReceipt (label 1)
      (externalReceipt (external 0)
        (targetExternalValue operation first second) (label 0) receiptNil)

def compiledExternalCallDone (operation : CoreOp) (first second : Int) : Pattern :=
  halted (compiledExternalCallOutcome operation first second)
    (compiledExternalCallReceipt operation first second)

theorem targetUndefinedAt_iff
    (operation : CoreOp) (second : Int) :
    targetUndefinedAt operation second ↔ undefinedAt operation second := by
  exact ArithmeticExternalCallPilot.compileSyntax_undefinedAt operation second

theorem targetValue_eq
    (operation : CoreOp) (first second : Int) :
    targetValue operation first second = operation.fn first second := by
  exact congrFun
    (congrFun (ArithmeticExternalCallPilot.compileSyntax_fn operation) first) second

/-- ExternalCall's target-side value and definedness contracts agree with the shared
mathematical exact-integer semantics.  The ExternalCall relation environment above does
not use this theorem in its definition. -/
theorem compiledExternalCallOutcome_commutes
    (operation : CoreOp) (first second : Int) :
    compiledExternalCallOutcome operation first second =
      match coreSem operation first second with
      | .declined => a "external-call:outcome-declined"
      | .val value => a "external-call:outcome-value" [exactIntegerValue value] := by
  by_cases undefined : undefinedAt operation second
  · have targetUndefined : targetUndefinedAt operation second :=
      (ArithmeticExternalCallPilot.compileSyntax_undefinedAt operation second).2
        undefined
    rw [coreSem_pos undefined first]
    simp [compiledExternalCallOutcome, targetUndefined]
  · have targetDefined : ¬ targetUndefinedAt operation second :=
      fun targetUndefined => undefined
        ((ArithmeticExternalCallPilot.compileSyntax_undefinedAt operation second).1
          targetUndefined)
    rw [coreSem_neg undefined first]
    simp [compiledExternalCallOutcome, targetDefined, targetValue, targetOperation]

/-- The configuration reached by the first authored ExternalCall transition.  Making
this configuration explicit is the first node in the compiler-image trace;
later steps can be proved and composed without asking the generic engine to
normalize an opaque multi-step computation in one reduction. -/
def compiledExternalCallAfterFirst
    (operation : CoreOp) (first second : Int) : Pattern :=
  let program := compileCoreOperation operation
  if targetUndefinedAt operation second then
    run program (label 1) (inputStore first second)
      (stepReceipt (label 0) receiptNil)
  else if operation.isPartial then
    run program (label 2) (inputStore first second)
      (stepReceipt (label 0) receiptNil)
  else
    run program (label 1) (resultStore operation first second)
      (externalReceipt (external 0)
        (targetExternalValue operation first second) (label 0) receiptNil)

private theorem match_compiledExternalCallStart
    (rule : RewriteRule)
    (leftShape : rule.left =
      ExternalCallMachine.run (ExternalCallMachine.v "program") (ExternalCallMachine.v "pc")
        (ExternalCallMachine.v "store") (ExternalCallMachine.v "fuel")
        (ExternalCallMachine.v "receipt"))
    (operation : CoreOp) (first second : Int) :
    matchPatternForRule externalCallLanguage rule
        (compiledExternalCallStart operation first second) =
      [ExternalCallMachine.runMatchBindings (compileCoreOperation operation)
        (label 0) (inputStore first second) fuelInfinite receiptNil] := by
  simpa [compiledExternalCallStart, run, ExternalCallMachine.run, a, ExternalCallMachine.a] using
    ExternalCallMachine.match_run_transition rule leftShape
      (compileCoreOperation operation) (label 0)
      (inputStore first second) fuelInfinite receiptNil

/-- All three compiler-entry transition schemas structurally match every
compiled start configuration with the same proof-relevant binding order.
Their premises, not an implementation-side dispatcher, select the applicable
edge. -/
theorem compiledExternalCallStart_matches_entry_transitions
    (operation : CoreOp) (first second : Int) :
    let bindings := ExternalCallMachine.runMatchBindings
      (compileCoreOperation operation) (label 0)
      (inputStore first second) fuelInfinite receiptNil
    matchPatternForRule externalCallLanguage ExternalCallMachine.callValueTransition
        (compiledExternalCallStart operation first second) = [bindings] ∧
      matchPatternForRule externalCallLanguage ExternalCallMachine.branchZeroTransition
        (compiledExternalCallStart operation first second) = [bindings] ∧
      matchPatternForRule externalCallLanguage ExternalCallMachine.branchNonzeroTransition
        (compiledExternalCallStart operation first second) = [bindings] := by
  exact ⟨
    match_compiledExternalCallStart ExternalCallMachine.callValueTransition rfl
      operation first second,
    match_compiledExternalCallStart ExternalCallMachine.branchZeroTransition rfl
      operation first second,
    match_compiledExternalCallStart ExternalCallMachine.branchNonzeroTransition rfl
      operation first second⟩

/-- Undefined target calls are absent from the independently target-defined
external relation.  The ExternalCall guard therefore cannot be bypassed by an oracle
row at a zero divisor. -/
theorem referenceEnv_no_external_when_undefined
    (operation : CoreOp) (first second : Int)
    (undefined : targetUndefinedAt operation second)
    (arguments : List Pattern) :
    (arithmeticExternalCallReferenceEnv operation first second).tuples
        "ExternalCallCallBinaryExternal" arguments = [] := by
  simp [arithmeticExternalCallReferenceEnv, undefined]

/-- At every defined input the reference environment contains exactly the
one target-operation row, including the compiled program and resulting
store.  No source evaluator appears in the row. -/
theorem referenceEnv_external_exact_when_defined
    (operation : CoreOp) (first second : Int)
    (defined : ¬ targetUndefinedAt operation second)
    (arguments : List Pattern) :
    (arithmeticExternalCallReferenceEnv operation first second).tuples
        "ExternalCallCallBinaryExternal" arguments =
      [[compileCoreOperation operation, external 0,
        inputStore first second,
        targetExternalValue operation first second]] := by
  simp [arithmeticExternalCallReferenceEnv, defined]

/-! ## Exact query fibres on the compiler image

The no-invention direction needs elimination as well as the constructive
transition lemmas below.  These small equalities expose the functional pieces
of this particular reference environment without claiming that relation
environments are functional in general.
-/

private theorem referenceEnv_consume_exact
    (operation : CoreOp) (first second : Int)
    (program pc store receipt : Pattern) :
    premiseStepWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (runMatchBindings program pc store fuelInfinite receipt)
        consumeFuel =
      [consumedBindings program pc store fuelInfinite receipt fuelInfinite] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    arithmeticExternalCallReferenceEnv, consumeFuel, query, ExternalCallMachine.v,
    runMatchBindings, consumedBindings,
    matchRelationArgs, matchRelationArgument, Bindings.lookup,
    applyBindings, mergeBindings]

private theorem referenceEnv_total_fetch_call_exact
    (operation : CoreOp) (first second : Int)
    (total : operation.isPartial = false) :
    premiseStepWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (consumedBindings (compileCoreOperation operation) (label 0)
          (inputStore first second) fuelInfinite receiptNil fuelInfinite)
        (fetch (ExternalCallMachine.a "external-call:call-binary"
          [ExternalCallMachine.v "external", ExternalCallMachine.v "ifValue",
           ExternalCallMachine.v "ifLanguageFault", ExternalCallMachine.v "ifEngineFault",
           ExternalCallMachine.v "ifResourceFault"])) =
      [callFetchedBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil fuelInfinite
        (external 0) (label 1) (label 2) (label 3) (label 4)] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    arithmeticExternalCallReferenceEnv, fetchRows, totalFetchRows, total,
    fetch, query, ExternalCallMachine.a, ExternalCallMachine.v, callExternal,
    returnValue, returnLanguageFault, returnEngineFault,
    returnResourceFault, label, external, natPattern, a,
    consumedBindings, callFetchedBindings, runMatchBindings,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    Bindings.lookup,
    applyBindings, mergeBindings]

private theorem referenceEnv_total_fetch_branch_empty
    (operation : CoreOp) (first second : Int)
    (total : operation.isPartial = false) :
    premiseStepWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (consumedBindings (compileCoreOperation operation) (label 0)
          (inputStore first second) fuelInfinite receiptNil fuelInfinite)
        (fetch (ExternalCallMachine.a "external-call:branch-zero"
          [ExternalCallMachine.v "slot", ExternalCallMachine.v "ifZero",
           ExternalCallMachine.v "ifNonzero"])) = [] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    arithmeticExternalCallReferenceEnv, fetchRows, totalFetchRows, total,
    fetch, query, ExternalCallMachine.a, ExternalCallMachine.v, callExternal,
    returnValue, returnLanguageFault, returnEngineFault,
    returnResourceFault, label, external, slot, natPattern, fault, a,
    consumedBindings, runMatchBindings, matchRelationArgs,
    matchRelationArgument, matchPattern, Bindings.lookup,
    applyBindings, mergeBindings]

private theorem referenceEnv_total_fetch_noncall_empty
    (operation : CoreOp) (first second : Int)
    (total : operation.isPartial = false)
    (instructionName : String) (arguments : List Pattern)
    (notCall : instructionName ≠ "external-call:call-binary") :
    premiseStepWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (consumedBindings (compileCoreOperation operation) (label 0)
          (inputStore first second) fuelInfinite receiptNil fuelInfinite)
        (fetch (ExternalCallMachine.a instructionName arguments)) = [] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    arithmeticExternalCallReferenceEnv, fetchRows, totalFetchRows, total,
    fetch, query, ExternalCallMachine.a, ExternalCallMachine.v, callExternal,
    returnValue, returnLanguageFault, returnEngineFault,
    returnResourceFault, label, external, natPattern, fault, a,
    consumedBindings, runMatchBindings, matchRelationArgs,
    matchRelationArgument, matchPattern, Bindings.lookup,
    applyBindings, mergeBindings, notCall]

private theorem referenceEnv_call_value_exact
    (operation : CoreOp) (first second : Int)
    (pc ifValue ifLanguageFault ifEngineFault ifResourceFault receipt : Pattern)
    (defined : ¬ targetUndefinedAt operation second) :
    premiseStepWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (callFetchedBindings (compileCoreOperation operation) pc
          (inputStore first second) fuelInfinite receipt fuelInfinite
          (external 0) ifValue ifLanguageFault ifEngineFault
          ifResourceFault)
        (query "ExternalCallCallBinaryExternal"
          [ExternalCallMachine.v "program", ExternalCallMachine.v "external",
           ExternalCallMachine.v "store",
           ExternalCallMachine.a "external-call:external-value" [ExternalCallMachine.v "nextStore"]]) =
      [callValueBindings (compileCoreOperation operation) pc
        (inputStore first second) fuelInfinite receipt fuelInfinite
        (external 0) ifValue ifLanguageFault ifEngineFault
        ifResourceFault (resultStore operation first second)] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    arithmeticExternalCallReferenceEnv, defined, targetExternalValue,
    query, ExternalCallMachine.a, ExternalCallMachine.v, external, natPattern, a,
    callFetchedBindings, callValueBindings, consumedBindings,
    runMatchBindings, matchRelationArgs, matchRelationArgument,
    matchPattern, matchArgs, Bindings.lookup, applyBindings, mergeBindings]

private theorem referenceEnv_call_nonvalue_empty
    (operation : CoreOp) (first second : Int)
    (pc ifValue ifLanguageFault ifEngineFault ifResourceFault receipt : Pattern)
    (defined : ¬ targetUndefinedAt operation second)
    (outcomeTag : String) (notValue : outcomeTag ≠ "external-call:external-value") :
    premiseStepWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (callFetchedBindings (compileCoreOperation operation) pc
          (inputStore first second) fuelInfinite receipt fuelInfinite
          (external 0) ifValue ifLanguageFault ifEngineFault
          ifResourceFault)
        (query "ExternalCallCallBinaryExternal"
          [ExternalCallMachine.v "program", ExternalCallMachine.v "external",
           ExternalCallMachine.v "store",
           ExternalCallMachine.a outcomeTag [ExternalCallMachine.v "fault"]]) = [] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    arithmeticExternalCallReferenceEnv, defined, targetExternalValue,
    query, ExternalCallMachine.a, ExternalCallMachine.v, external, natPattern, a,
    callFetchedBindings, consumedBindings, runMatchBindings,
    matchRelationArgs, matchRelationArgument, matchPattern,
    Bindings.lookup, applyBindings, mergeBindings, notValue]

private theorem referenceEnv_total_fetch_return_value_exact
    (operation : CoreOp) (first second : Int)
    (total : operation.isPartial = false) (receipt : Pattern) :
    premiseStepWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (consumedBindings (compileCoreOperation operation) (label 1)
          (resultStore operation first second) fuelInfinite receipt fuelInfinite)
        (fetch (ExternalCallMachine.a "external-call:return-value" [ExternalCallMachine.v "slot"])) =
      [returnFetchedBindings (compileCoreOperation operation) (label 1)
        (resultStore operation first second) fuelInfinite receipt fuelInfinite
        (slot 2)] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    arithmeticExternalCallReferenceEnv, fetchRows, totalFetchRows, total,
    fetch, query, ExternalCallMachine.a, ExternalCallMachine.v, callExternal,
    returnValue, returnLanguageFault, returnEngineFault,
    returnResourceFault, label, external, slot, natPattern, fault, a,
    consumedBindings, returnFetchedBindings, runMatchBindings,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    Bindings.lookup, applyBindings, mergeBindings]

private theorem referenceEnv_total_fetch_at_one_nonreturn_empty
    (operation : CoreOp) (first second : Int)
    (total : operation.isPartial = false) (receipt : Pattern)
    (instructionName : String) (arguments : List Pattern)
    (notReturn : instructionName ≠ "external-call:return-value") :
    premiseStepWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (consumedBindings (compileCoreOperation operation) (label 1)
          (resultStore operation first second) fuelInfinite receipt fuelInfinite)
        (fetch (ExternalCallMachine.a instructionName arguments)) = [] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    arithmeticExternalCallReferenceEnv, fetchRows, totalFetchRows, total,
    fetch, query, ExternalCallMachine.a, ExternalCallMachine.v, callExternal,
    returnValue, returnLanguageFault, returnEngineFault,
    returnResourceFault, label, external, slot, natPattern, fault, a,
    consumedBindings, runMatchBindings, matchRelationArgs,
    matchRelationArgument, matchPattern, Bindings.lookup,
    applyBindings, mergeBindings, notReturn]

private theorem referenceEnv_read_result_exact
    (operation : CoreOp) (first second : Int)
    (pc receipt : Pattern) :
    premiseStepWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (returnFetchedBindings (compileCoreOperation operation) pc
          (resultStore operation first second) fuelInfinite receipt fuelInfinite
          (slot 2))
        (query "ExternalCallReadSlot"
          [ExternalCallMachine.v "store", ExternalCallMachine.v "slot",
           ExternalCallMachine.v "value"]) =
      [returnReadBindings (compileCoreOperation operation) pc
        (resultStore operation first second) fuelInfinite receipt fuelInfinite
        (slot 2) (exactIntegerValue (targetValue operation first second))] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    arithmeticExternalCallReferenceEnv, query, ExternalCallMachine.v,
    returnFetchedBindings, returnReadBindings, consumedBindings,
    runMatchBindings, slot, natPattern, exactIntegerValue, integerAtom, a,
    matchRelationArgs, matchRelationArgument,
    Bindings.lookup, applyBindings, mergeBindings]

private theorem referenceEnv_guarded_fetch_branch_exact
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true) :
    premiseStepWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (consumedBindings (compileCoreOperation operation) (label 0)
          (inputStore first second) fuelInfinite receiptNil fuelInfinite)
        (fetch (ExternalCallMachine.a "external-call:branch-zero"
          [ExternalCallMachine.v "slot", ExternalCallMachine.v "ifZero",
           ExternalCallMachine.v "ifNonzero"])) =
      [branchFetchedBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil fuelInfinite
        (slot 1) (label 1) (label 2)] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    arithmeticExternalCallReferenceEnv, fetchRows, guardedFetchRows, hPartial,
    fetch, query, ExternalCallMachine.a, ExternalCallMachine.v, callExternal,
    returnValue, returnDeclined, returnLanguageFault, returnEngineFault,
    returnResourceFault, label, external, slot, natPattern, fault, a,
    consumedBindings, branchFetchedBindings, runMatchBindings,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    Bindings.lookup, applyBindings, mergeBindings]

private theorem referenceEnv_guarded_fetch_zero_nonbranch_empty
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (instructionName : String) (arguments : List Pattern)
    (notBranch : instructionName ≠ "external-call:branch-zero") :
    premiseStepWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (consumedBindings (compileCoreOperation operation) (label 0)
          (inputStore first second) fuelInfinite receiptNil fuelInfinite)
        (fetch (ExternalCallMachine.a instructionName arguments)) = [] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    arithmeticExternalCallReferenceEnv, fetchRows, guardedFetchRows, hPartial,
    fetch, query, ExternalCallMachine.a, ExternalCallMachine.v, callExternal,
    returnValue, returnDeclined, returnLanguageFault, returnEngineFault,
    returnResourceFault, label, external, slot, natPattern, fault, a,
    consumedBindings, runMatchBindings, matchRelationArgs,
    matchRelationArgument, matchPattern, Bindings.lookup,
    applyBindings, mergeBindings, notBranch]

private theorem referenceEnv_read_guard_input_exact
    (operation : CoreOp) (first second : Int) :
    premiseStepWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (branchFetchedBindings (compileCoreOperation operation) (label 0)
          (inputStore first second) fuelInfinite receiptNil fuelInfinite
          (slot 1) (label 1) (label 2))
        (query "ExternalCallReadSlot"
          [ExternalCallMachine.v "store", ExternalCallMachine.v "slot",
           ExternalCallMachine.v "value"]) =
      [branchReadBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil fuelInfinite
        (slot 1) (label 1) (label 2) (exactIntegerValue second)] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    arithmeticExternalCallReferenceEnv, query, ExternalCallMachine.v,
    branchFetchedBindings, branchReadBindings, consumedBindings,
    runMatchBindings, slot, label, natPattern, exactIntegerValue,
    inputStore, resultStore, store3, storeCons, storeNil, slotValue,
    slotEmpty, integerAtom, a, matchRelationArgs, matchRelationArgument,
    Bindings.lookup, applyBindings, mergeBindings]

private theorem referenceEnv_zero_test_exact
    (operation : CoreOp) (first second : Int)
    (zeroDivisor : second = 0) :
    let bindings := branchReadBindings (compileCoreOperation operation)
      (label 0) (inputStore first second) fuelInfinite receiptNil fuelInfinite
      (slot 1) (label 1) (label 2) (exactIntegerValue second)
    premiseStepWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage bindings
        (query "ExternalCallIsZero" [ExternalCallMachine.v "value"]) = [bindings] := by
  subst second
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    arithmeticExternalCallReferenceEnv, query, ExternalCallMachine.v,
    branchReadBindings, branchFetchedBindings, consumedBindings,
    runMatchBindings, Bindings.lookup, exactIntegerValue, integerAtom,
    matchRelationArgs, matchRelationArgument, applyBindings, mergeBindings]

private theorem referenceEnv_nonzero_test_empty_at_zero
    (operation : CoreOp) (first second : Int)
    (zeroDivisor : second = 0) :
    let bindings := branchReadBindings (compileCoreOperation operation)
      (label 0) (inputStore first second) fuelInfinite receiptNil fuelInfinite
      (slot 1) (label 1) (label 2) (exactIntegerValue second)
    premiseStepWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage bindings
        (query "ExternalCallIsNonzero" [ExternalCallMachine.v "value"]) = [] := by
  subst second
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    arithmeticExternalCallReferenceEnv, query]

private theorem referenceEnv_nonzero_test_exact
    (operation : CoreOp) (first second : Int)
    (nonzeroDivisor : second ≠ 0) :
    let bindings := branchReadBindings (compileCoreOperation operation)
      (label 0) (inputStore first second) fuelInfinite receiptNil fuelInfinite
      (slot 1) (label 1) (label 2) (exactIntegerValue second)
    premiseStepWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage bindings
        (query "ExternalCallIsNonzero" [ExternalCallMachine.v "value"]) = [bindings] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    arithmeticExternalCallReferenceEnv, query, nonzeroDivisor, ExternalCallMachine.v,
    branchReadBindings, branchFetchedBindings, consumedBindings,
    runMatchBindings, Bindings.lookup, exactIntegerValue, integerAtom,
    matchRelationArgs, matchRelationArgument, applyBindings, mergeBindings]

private theorem referenceEnv_zero_test_empty_at_nonzero
    (operation : CoreOp) (first second : Int)
    (nonzeroDivisor : second ≠ 0) :
    let bindings := branchReadBindings (compileCoreOperation operation)
      (label 0) (inputStore first second) fuelInfinite receiptNil fuelInfinite
      (slot 1) (label 1) (label 2) (exactIntegerValue second)
    premiseStepWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage bindings
        (query "ExternalCallIsZero" [ExternalCallMachine.v "value"]) = [] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    arithmeticExternalCallReferenceEnv, query, nonzeroDivisor]

private theorem guarded_zero_branch_premises_exact
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (zeroDivisor : second = 0) :
    applyPremisesWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        branchZeroTransition.premises
        (runMatchBindings (compileCoreOperation operation) (label 0)
          (inputStore first second) fuelInfinite receiptNil) =
      [branchReadBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil fuelInfinite
        (slot 1) (label 1) (label 2) (exactIntegerValue second)] := by
  simp only [branchZeroTransition, branchRule, applyPremisesWithEnv,
    List.foldl_cons, List.foldl_nil, List.flatMap_singleton]
  rw [referenceEnv_consume_exact]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_guarded_fetch_branch_exact operation first second hPartial]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_read_guard_input_exact operation first second]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_zero_test_exact operation first second zeroDivisor]

private theorem guarded_zero_nonzero_branch_premises_empty
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (zeroDivisor : second = 0) :
    applyPremisesWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        branchNonzeroTransition.premises
        (runMatchBindings (compileCoreOperation operation) (label 0)
          (inputStore first second) fuelInfinite receiptNil) = [] := by
  simp only [branchNonzeroTransition, branchRule, applyPremisesWithEnv,
    List.foldl_cons, List.foldl_nil, List.flatMap_singleton]
  rw [referenceEnv_consume_exact]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_guarded_fetch_branch_exact operation first second hPartial]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_read_guard_input_exact operation first second]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_nonzero_test_empty_at_zero operation first second zeroDivisor]

private theorem guarded_nonzero_branch_premises_exact
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (nonzeroDivisor : second ≠ 0) :
    applyPremisesWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        branchNonzeroTransition.premises
        (runMatchBindings (compileCoreOperation operation) (label 0)
          (inputStore first second) fuelInfinite receiptNil) =
      [branchReadBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil fuelInfinite
        (slot 1) (label 1) (label 2) (exactIntegerValue second)] := by
  simp only [branchNonzeroTransition, branchRule, applyPremisesWithEnv,
    List.foldl_cons, List.foldl_nil, List.flatMap_singleton]
  rw [referenceEnv_consume_exact]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_guarded_fetch_branch_exact operation first second hPartial]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_read_guard_input_exact operation first second]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_nonzero_test_exact operation first second nonzeroDivisor]

private theorem guarded_nonzero_zero_branch_premises_empty
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (nonzeroDivisor : second ≠ 0) :
    applyPremisesWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        branchZeroTransition.premises
        (runMatchBindings (compileCoreOperation operation) (label 0)
          (inputStore first second) fuelInfinite receiptNil) = [] := by
  simp only [branchZeroTransition, branchRule, applyPremisesWithEnv,
    List.foldl_cons, List.foldl_nil, List.flatMap_singleton]
  rw [referenceEnv_consume_exact]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_guarded_fetch_branch_exact operation first second hPartial]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_read_guard_input_exact operation first second]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_zero_test_empty_at_nonzero operation first second
    nonzeroDivisor]

private theorem total_call_premises_exact
    (operation : CoreOp) (first second : Int)
    (total : operation.isPartial = false)
    (defined : ¬ targetUndefinedAt operation second) :
    applyPremisesWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        callValueTransition.premises
        (runMatchBindings (compileCoreOperation operation) (label 0)
          (inputStore first second) fuelInfinite receiptNil) =
      [callValueBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil fuelInfinite
        (external 0) (label 1) (label 2) (label 3) (label 4)
        (resultStore operation first second)] := by
  simp only [callValueTransition, callRule, applyPremisesWithEnv,
    List.foldl_cons, List.foldl_nil, List.flatMap_singleton]
  rw [referenceEnv_consume_exact]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_total_fetch_call_exact operation first second total]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_call_value_exact operation first second
    (label 0) (label 1) (label 2) (label 3) (label 4) receiptNil defined]

private theorem total_branch_premises_empty
    (operation : CoreOp) (first second : Int)
    (total : operation.isPartial = false)
    (name test target : String) :
    applyPremisesWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (branchRule name test target).premises
        (runMatchBindings (compileCoreOperation operation) (label 0)
          (inputStore first second) fuelInfinite receiptNil) = [] := by
  simp only [branchRule, applyPremisesWithEnv, List.foldl_cons,
    List.foldl_nil, List.flatMap_singleton]
  rw [referenceEnv_consume_exact]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_total_fetch_branch_empty operation first second total]
  rfl

private theorem total_call_nonvalue_premises_empty
    (operation : CoreOp) (first second : Int)
    (total : operation.isPartial = false)
    (defined : ¬ targetUndefinedAt operation second)
    (name target outcomeTag : String)
    (notValue : outcomeTag ≠ "external-call:external-value") :
    applyPremisesWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (callRule name target false
          (ExternalCallMachine.a outcomeTag [ExternalCallMachine.v "fault"])
          (ExternalCallMachine.v "store")).premises
        (runMatchBindings (compileCoreOperation operation) (label 0)
          (inputStore first second) fuelInfinite receiptNil) = [] := by
  simp only [callRule, applyPremisesWithEnv, List.foldl_cons,
    List.foldl_nil, List.flatMap_singleton]
  rw [referenceEnv_consume_exact]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_total_fetch_call_exact operation first second total]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_call_nonvalue_empty operation first second
    (label 0) (label 1) (label 2) (label 3) (label 4) receiptNil
    defined outcomeTag notValue]

private theorem total_noncall_premises_empty
    (operation : CoreOp) (first second : Int)
    (total : operation.isPartial = false)
    (instructionName : String) (arguments : List Pattern)
    (notCall : instructionName ≠ "external-call:call-binary")
    (remaining : List Premise) :
    applyPremisesWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (consumeFuel :: fetch (ExternalCallMachine.a instructionName arguments) ::
          remaining)
        (runMatchBindings (compileCoreOperation operation) (label 0)
          (inputStore first second) fuelInfinite receiptNil) = [] := by
  unfold applyPremisesWithEnv
  rw [List.foldl_cons]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_consume_exact]
  simp only [List.foldl_cons, List.flatMap_singleton]
  rw [referenceEnv_total_fetch_noncall_empty operation first second total
    instructionName arguments notCall]
  induction remaining with
  | nil => rfl
  | cons premise rest inductionHypothesis =>
      simp only [List.foldl_cons, List.flatMap_nil]
      exact inductionHypothesis

private theorem guarded_start_nonbranch_premises_empty
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (instructionName : String) (arguments : List Pattern)
    (notBranch : instructionName ≠ "external-call:branch-zero")
    (remaining : List Premise) :
    applyPremisesWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (consumeFuel :: fetch (ExternalCallMachine.a instructionName arguments) ::
          remaining)
        (runMatchBindings (compileCoreOperation operation) (label 0)
          (inputStore first second) fuelInfinite receiptNil) = [] := by
  unfold applyPremisesWithEnv
  rw [List.foldl_cons]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_consume_exact]
  simp only [List.foldl_cons, List.flatMap_singleton]
  rw [referenceEnv_guarded_fetch_zero_nonbranch_empty
    operation first second hPartial instructionName arguments notBranch]
  induction remaining with
  | nil => rfl
  | cons premise rest inductionHypothesis =>
      simp only [List.foldl_cons, List.flatMap_nil]
      exact inductionHypothesis

/-! ## Universal traces assembled from named authored ExternalCall edges -/

private theorem admittedExternalCallStep
    {relationEnv : RelationEnv} {source target : Pattern}
    (member : target ∈
      rewriteAt (engineBasePremises relationEnv) externalCallLanguage 1 source) :
    langReducesUsing relationEnv externalCallLanguage source target :=
  exec_to_langReducesUsing relationEnv externalCallLanguage ⟨1, member⟩

private def totalCallReceipt
    (operation : CoreOp) (first second : Int) : Pattern :=
  externalReceipt (external 0)
    (targetExternalValue operation first second) (label 0) receiptNil

private def totalAfterCall
    (operation : CoreOp) (first second : Int) : Pattern :=
  run (compileCoreOperation operation) (label 1)
    (resultStore operation first second)
    (totalCallReceipt operation first second)

private theorem total_return_premises_exact
    (operation : CoreOp) (first second : Int)
    (total : operation.isPartial = false) :
    applyPremisesWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        returnValueTransition.premises
        (runMatchBindings (compileCoreOperation operation) (label 1)
          (resultStore operation first second) fuelInfinite
          (totalCallReceipt operation first second)) =
      [returnReadBindings (compileCoreOperation operation) (label 1)
        (resultStore operation first second) fuelInfinite
        (totalCallReceipt operation first second) fuelInfinite (slot 2)
        (exactIntegerValue (targetValue operation first second))] := by
  simp only [returnValueTransition, applyPremisesWithEnv,
    List.foldl_cons, List.foldl_nil, List.flatMap_singleton]
  rw [referenceEnv_consume_exact]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_total_fetch_return_value_exact operation first second
    total (totalCallReceipt operation first second)]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_read_result_exact operation first second
    (label 1) (totalCallReceipt operation first second)]

private theorem total_after_call_nonreturn_premises_empty
    (operation : CoreOp) (first second : Int)
    (total : operation.isPartial = false)
    (instructionName : String) (arguments : List Pattern)
    (notReturn : instructionName ≠ "external-call:return-value")
    (remaining : List Premise) :
    applyPremisesWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (consumeFuel :: fetch (ExternalCallMachine.a instructionName arguments) ::
          remaining)
        (runMatchBindings (compileCoreOperation operation) (label 1)
          (resultStore operation first second) fuelInfinite
          (totalCallReceipt operation first second)) = [] := by
  unfold applyPremisesWithEnv
  rw [List.foldl_cons]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_consume_exact]
  simp only [List.foldl_cons, List.flatMap_singleton]
  rw [referenceEnv_total_fetch_at_one_nonreturn_empty
    operation first second total (totalCallReceipt operation first second)
    instructionName arguments notReturn]
  induction remaining with
  | nil => rfl
  | cons premise rest inductionHypothesis =>
      simp only [List.foldl_cons, List.flatMap_nil]
      exact inductionHypothesis

private theorem match_totalAfterCall
    (rule : RewriteRule)
    (leftShape : rule.left =
      ExternalCallMachine.run (ExternalCallMachine.v "program") (ExternalCallMachine.v "pc")
        (ExternalCallMachine.v "store") (ExternalCallMachine.v "fuel")
        (ExternalCallMachine.v "receipt"))
    (operation : CoreOp) (first second : Int) :
    matchPatternForRule externalCallLanguage rule (totalAfterCall operation first second) =
      [runMatchBindings (compileCoreOperation operation) (label 1)
        (resultStore operation first second) fuelInfinite
        (totalCallReceipt operation first second)] := by
  simpa [totalAfterCall, run, ExternalCallMachine.run, a, ExternalCallMachine.a] using
    match_run_transition rule leftShape
      (compileCoreOperation operation) (label 1)
      (resultStore operation first second) fuelInfinite
      (totalCallReceipt operation first second)

private theorem total_start_step_unique
    (operation : CoreOp) (first second : Int)
    (total : operation.isPartial = false)
    (defined : ¬ targetUndefinedAt operation second)
    {target : Pattern}
    (step :
      langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
        externalCallLanguage (compiledExternalCallStart operation first second) target) :
    target = totalAfterCall operation first second := by
  have root :
      RootStep (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (compiledExternalCallStart operation first second) target :=
    (step_iff_rootStep_of_noncontextualRules
      externalCallLanguage_rules_noncontextual).mp step
  rcases root with
    ⟨rule, ruleMember, initialBindings, matched,
      finalBindings, premises, targetEq⟩
  change rule ∈ externalCallLanguageTransitions at ruleMember
  simp only [externalCallLanguageTransitions, List.mem_cons, List.mem_nil_iff,
    or_false] at ruleMember
  rcases ruleMember with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [matchPatternForRule_eq_syntactic, fuelExhaustedRule,
      compiledExternalCallStart, run, ExternalCallMachine.run, fuelInfinite,
      a, ExternalCallMachine.a, ExternalCallMachine.v, matchPattern, matchArgs] at matched
  all_goals
    rw [match_compiledExternalCallStart _ rfl operation first second] at matched
    simp only [List.mem_singleton] at matched
    subst initialBindings
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (branchRule "external-call:branch-zero" "ExternalCallIsZero" "ifZero").premises
      (runMatchBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil) at premises
    rw [total_branch_premises_empty operation first second total
      "external-call:branch-zero" "ExternalCallIsZero" "ifZero"] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (branchRule "external-call:branch-nonzero" "ExternalCallIsNonzero" "ifNonzero").premises
      (runMatchBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil) at premises
    rw [total_branch_premises_empty operation first second total
      "external-call:branch-nonzero" "ExternalCallIsNonzero" "ifNonzero"] at premises
    simp at premises
  · rw [total_call_premises_exact operation first second total defined]
      at premises
    simp only [List.mem_singleton] at premises
    subst finalBindings
    calc
      target = applyBindingsForRule externalCallLanguage callValueTransition
          (callValueBindings (compileCoreOperation operation) (label 0)
            (inputStore first second) fuelInfinite receiptNil fuelInfinite
            (external 0) (label 1) (label 2) (label 3) (label 4)
            (resultStore operation first second)) := targetEq.symm
      _ = totalAfterCall operation first second := by
        simp [callValueTransition, callRule,
          applyBindingsForRule_eq_syntactic, callValueBindings,
          callFetchedBindings, consumedBindings, runMatchBindings,
          totalAfterCall, totalCallReceipt, targetExternalValue, externalReceipt,
          ExternalCallMachine.externalReceipt, stepReceipt, ExternalCallMachine.stepReceipt,
          run, ExternalCallMachine.run, ExternalCallMachine.a, ExternalCallMachine.v,
          applyBindings, a]
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (callRule "external-call:call-language-fault" "ifLanguageFault" false
        (ExternalCallMachine.a "external-call:external-language-fault" [ExternalCallMachine.v "fault"])
        (ExternalCallMachine.v "store")).premises
      (runMatchBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil) at premises
    rw [total_call_nonvalue_premises_empty operation first second total
      defined "external-call:call-language-fault" "ifLanguageFault"
      "external-call:external-language-fault" (by decide)] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (callRule "external-call:call-engine-fault" "ifEngineFault" false
        (ExternalCallMachine.a "external-call:external-engine-fault" [ExternalCallMachine.v "fault"])
        (ExternalCallMachine.v "store")).premises
      (runMatchBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil) at premises
    rw [total_call_nonvalue_premises_empty operation first second total
      defined "external-call:call-engine-fault" "ifEngineFault"
      "external-call:external-engine-fault" (by decide)] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (callRule "external-call:call-resource-fault" "ifResourceFault" false
        (ExternalCallMachine.a "external-call:external-resource-fault" [ExternalCallMachine.v "fault"])
        (ExternalCallMachine.v "store")).premises
      (runMatchBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil) at premises
    rw [total_call_nonvalue_premises_empty operation first second total
      defined "external-call:call-resource-fault" "ifResourceFault"
      "external-call:external-resource-fault" (by decide)] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch
        (ExternalCallMachine.a "external-call:return-value" [ExternalCallMachine.v "slot"]) ::
        [query "ExternalCallReadSlot"
          [ExternalCallMachine.v "store", ExternalCallMachine.v "slot",
           ExternalCallMachine.v "value"]])
      (runMatchBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil) at premises
    rw [total_noncall_premises_empty operation first second total
      "external-call:return-value" [ExternalCallMachine.v "slot"] (by decide) _] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch (ExternalCallMachine.a "external-call:return-declined") :: [])
      (runMatchBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil) at premises
    rw [total_noncall_premises_empty operation first second total
      "external-call:return-declined" [] (by decide) []] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch
        (ExternalCallMachine.a "external-call:return-language-fault" [ExternalCallMachine.v "fault"]) :: [])
      (runMatchBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil) at premises
    rw [total_noncall_premises_empty operation first second total
      "external-call:return-language-fault" [ExternalCallMachine.v "fault"]
      (by decide) []] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch
        (ExternalCallMachine.a "external-call:return-engine-fault" [ExternalCallMachine.v "fault"]) :: [])
      (runMatchBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil) at premises
    rw [total_noncall_premises_empty operation first second total
      "external-call:return-engine-fault" [ExternalCallMachine.v "fault"]
      (by decide) []] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch
        (ExternalCallMachine.a "external-call:return-resource-fault" [ExternalCallMachine.v "fault"]) :: [])
      (runMatchBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil) at premises
    rw [total_noncall_premises_empty operation first second total
      "external-call:return-resource-fault" [ExternalCallMachine.v "fault"]
      (by decide) []] at premises
    simp at premises

private theorem total_after_call_step_unique
    (operation : CoreOp) (first second : Int)
    (total : operation.isPartial = false)
    (defined : ¬ targetUndefinedAt operation second)
    {target : Pattern}
    (step :
      langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
        externalCallLanguage (totalAfterCall operation first second) target) :
    target = compiledExternalCallDone operation first second := by
  have root :
      RootStep (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (totalAfterCall operation first second) target :=
    (step_iff_rootStep_of_noncontextualRules
      externalCallLanguage_rules_noncontextual).mp step
  rcases root with
    ⟨rule, ruleMember, initialBindings, matched,
      finalBindings, premises, targetEq⟩
  change rule ∈ externalCallLanguageTransitions at ruleMember
  simp only [externalCallLanguageTransitions, List.mem_cons, List.mem_nil_iff,
    or_false] at ruleMember
  rcases ruleMember with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [matchPatternForRule_eq_syntactic, fuelExhaustedRule,
      totalAfterCall, totalCallReceipt, run, ExternalCallMachine.run, fuelInfinite,
      a, ExternalCallMachine.a, ExternalCallMachine.v, matchPattern, matchArgs] at matched
  all_goals
    rw [match_totalAfterCall _ rfl operation first second] at matched
    simp only [List.mem_singleton] at matched
    subst initialBindings
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch (ExternalCallMachine.a "external-call:branch-zero"
        [ExternalCallMachine.v "slot", ExternalCallMachine.v "ifZero",
         ExternalCallMachine.v "ifNonzero"]) ::
        [query "ExternalCallReadSlot"
          [ExternalCallMachine.v "store", ExternalCallMachine.v "slot", ExternalCallMachine.v "value"],
         query "ExternalCallIsZero" [ExternalCallMachine.v "value"]])
      (runMatchBindings (compileCoreOperation operation) (label 1)
        (resultStore operation first second) fuelInfinite
        (totalCallReceipt operation first second)) at premises
    rw [total_after_call_nonreturn_premises_empty operation first second total
      "external-call:branch-zero"
      [ExternalCallMachine.v "slot", ExternalCallMachine.v "ifZero", ExternalCallMachine.v "ifNonzero"]
      (by decide) _] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch (ExternalCallMachine.a "external-call:branch-zero"
        [ExternalCallMachine.v "slot", ExternalCallMachine.v "ifZero",
         ExternalCallMachine.v "ifNonzero"]) ::
        [query "ExternalCallReadSlot"
          [ExternalCallMachine.v "store", ExternalCallMachine.v "slot", ExternalCallMachine.v "value"],
         query "ExternalCallIsNonzero" [ExternalCallMachine.v "value"]])
      (runMatchBindings (compileCoreOperation operation) (label 1)
        (resultStore operation first second) fuelInfinite
        (totalCallReceipt operation first second)) at premises
    rw [total_after_call_nonreturn_premises_empty operation first second total
      "external-call:branch-zero"
      [ExternalCallMachine.v "slot", ExternalCallMachine.v "ifZero", ExternalCallMachine.v "ifNonzero"]
      (by decide) _] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch (ExternalCallMachine.a "external-call:call-binary"
        [ExternalCallMachine.v "external", ExternalCallMachine.v "ifValue",
         ExternalCallMachine.v "ifLanguageFault", ExternalCallMachine.v "ifEngineFault",
         ExternalCallMachine.v "ifResourceFault"]) ::
        [query "ExternalCallCallBinaryExternal"
          [ExternalCallMachine.v "program", ExternalCallMachine.v "external",
           ExternalCallMachine.v "store",
           ExternalCallMachine.a "external-call:external-value" [ExternalCallMachine.v "nextStore"]]])
      (runMatchBindings (compileCoreOperation operation) (label 1)
        (resultStore operation first second) fuelInfinite
        (totalCallReceipt operation first second)) at premises
    rw [total_after_call_nonreturn_premises_empty operation first second total
      "external-call:call-binary"
      [ExternalCallMachine.v "external", ExternalCallMachine.v "ifValue",
       ExternalCallMachine.v "ifLanguageFault", ExternalCallMachine.v "ifEngineFault",
       ExternalCallMachine.v "ifResourceFault"] (by decide) _] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch (ExternalCallMachine.a "external-call:call-binary"
        [ExternalCallMachine.v "external", ExternalCallMachine.v "ifValue",
         ExternalCallMachine.v "ifLanguageFault", ExternalCallMachine.v "ifEngineFault",
         ExternalCallMachine.v "ifResourceFault"]) ::
        [query "ExternalCallCallBinaryExternal"
          [ExternalCallMachine.v "program", ExternalCallMachine.v "external",
           ExternalCallMachine.v "store",
           ExternalCallMachine.a "external-call:external-language-fault"
             [ExternalCallMachine.v "fault"]]])
      (runMatchBindings (compileCoreOperation operation) (label 1)
        (resultStore operation first second) fuelInfinite
        (totalCallReceipt operation first second)) at premises
    rw [total_after_call_nonreturn_premises_empty operation first second total
      "external-call:call-binary"
      [ExternalCallMachine.v "external", ExternalCallMachine.v "ifValue",
       ExternalCallMachine.v "ifLanguageFault", ExternalCallMachine.v "ifEngineFault",
       ExternalCallMachine.v "ifResourceFault"] (by decide) _] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch (ExternalCallMachine.a "external-call:call-binary"
        [ExternalCallMachine.v "external", ExternalCallMachine.v "ifValue",
         ExternalCallMachine.v "ifLanguageFault", ExternalCallMachine.v "ifEngineFault",
         ExternalCallMachine.v "ifResourceFault"]) ::
        [query "ExternalCallCallBinaryExternal"
          [ExternalCallMachine.v "program", ExternalCallMachine.v "external",
           ExternalCallMachine.v "store",
           ExternalCallMachine.a "external-call:external-engine-fault"
             [ExternalCallMachine.v "fault"]]])
      (runMatchBindings (compileCoreOperation operation) (label 1)
        (resultStore operation first second) fuelInfinite
        (totalCallReceipt operation first second)) at premises
    rw [total_after_call_nonreturn_premises_empty operation first second total
      "external-call:call-binary"
      [ExternalCallMachine.v "external", ExternalCallMachine.v "ifValue",
       ExternalCallMachine.v "ifLanguageFault", ExternalCallMachine.v "ifEngineFault",
       ExternalCallMachine.v "ifResourceFault"] (by decide) _] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch (ExternalCallMachine.a "external-call:call-binary"
        [ExternalCallMachine.v "external", ExternalCallMachine.v "ifValue",
         ExternalCallMachine.v "ifLanguageFault", ExternalCallMachine.v "ifEngineFault",
         ExternalCallMachine.v "ifResourceFault"]) ::
        [query "ExternalCallCallBinaryExternal"
          [ExternalCallMachine.v "program", ExternalCallMachine.v "external",
           ExternalCallMachine.v "store",
           ExternalCallMachine.a "external-call:external-resource-fault"
             [ExternalCallMachine.v "fault"]]])
      (runMatchBindings (compileCoreOperation operation) (label 1)
        (resultStore operation first second) fuelInfinite
        (totalCallReceipt operation first second)) at premises
    rw [total_after_call_nonreturn_premises_empty operation first second total
      "external-call:call-binary"
      [ExternalCallMachine.v "external", ExternalCallMachine.v "ifValue",
       ExternalCallMachine.v "ifLanguageFault", ExternalCallMachine.v "ifEngineFault",
       ExternalCallMachine.v "ifResourceFault"] (by decide) _] at premises
    simp at premises
  · rw [total_return_premises_exact operation first second total] at premises
    simp only [List.mem_singleton] at premises
    subst finalBindings
    calc
      target = applyBindingsForRule externalCallLanguage returnValueTransition
          (returnReadBindings (compileCoreOperation operation) (label 1)
            (resultStore operation first second) fuelInfinite
            (totalCallReceipt operation first second) fuelInfinite (slot 2)
            (exactIntegerValue (targetValue operation first second))) :=
        targetEq.symm
      _ = compiledExternalCallDone operation first second := by
        simp [returnValueTransition, applyBindingsForRule_eq_syntactic,
          returnReadBindings, returnFetchedBindings, consumedBindings,
          runMatchBindings, compiledExternalCallDone, compiledExternalCallOutcome,
          compiledExternalCallReceipt, total, defined, totalCallReceipt,
          targetExternalValue, exactIntegerValue, stepReceipt,
          ExternalCallMachine.stepReceipt, halted, ExternalCallMachine.halted,
          ExternalCallMachine.a, ExternalCallMachine.v, applyBindings, a]
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch (ExternalCallMachine.a "external-call:return-declined") :: [])
      (runMatchBindings (compileCoreOperation operation) (label 1)
        (resultStore operation first second) fuelInfinite
        (totalCallReceipt operation first second)) at premises
    rw [total_after_call_nonreturn_premises_empty operation first second total
      "external-call:return-declined" [] (by decide) []] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch
        (ExternalCallMachine.a "external-call:return-language-fault" [ExternalCallMachine.v "fault"]) :: [])
      (runMatchBindings (compileCoreOperation operation) (label 1)
        (resultStore operation first second) fuelInfinite
        (totalCallReceipt operation first second)) at premises
    rw [total_after_call_nonreturn_premises_empty operation first second total
      "external-call:return-language-fault" [ExternalCallMachine.v "fault"]
      (by decide) []] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch
        (ExternalCallMachine.a "external-call:return-engine-fault" [ExternalCallMachine.v "fault"]) :: [])
      (runMatchBindings (compileCoreOperation operation) (label 1)
        (resultStore operation first second) fuelInfinite
        (totalCallReceipt operation first second)) at premises
    rw [total_after_call_nonreturn_premises_empty operation first second total
      "external-call:return-engine-fault" [ExternalCallMachine.v "fault"]
      (by decide) []] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch
        (ExternalCallMachine.a "external-call:return-resource-fault" [ExternalCallMachine.v "fault"]) :: [])
      (runMatchBindings (compileCoreOperation operation) (label 1)
        (resultStore operation first second) fuelInfinite
        (totalCallReceipt operation first second)) at premises
    rw [total_after_call_nonreturn_premises_empty operation first second total
      "external-call:return-resource-fault" [ExternalCallMachine.v "fault"]
      (by decide) []] at premises
    simp at premises

private def guardedBranchReceipt : Pattern :=
  stepReceipt (label 0) receiptNil

private def guardedExternalReceipt
    (operation : CoreOp) (first second : Int) : Pattern :=
  externalReceipt (external 0)
    (targetExternalValue operation first second) (label 2)
    guardedBranchReceipt

private def guardedAfterBranch
    (operation : CoreOp) (first second : Int) (targetLabel : Nat) : Pattern :=
  run (compileCoreOperation operation) (label targetLabel)
    (inputStore first second) guardedBranchReceipt

private def guardedAfterCall
    (operation : CoreOp) (first second : Int) : Pattern :=
  run (compileCoreOperation operation) (label 3)
    (resultStore operation first second)
    (guardedExternalReceipt operation first second)

private theorem referenceEnv_guarded_fetch_declined_exact
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true) (receipt : Pattern) :
    premiseStepWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (consumedBindings (compileCoreOperation operation) (label 1)
          (inputStore first second) fuelInfinite receipt fuelInfinite)
        (fetch (ExternalCallMachine.a "external-call:return-declined")) =
      [consumedBindings (compileCoreOperation operation) (label 1)
        (inputStore first second) fuelInfinite receipt fuelInfinite] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    arithmeticExternalCallReferenceEnv, fetchRows, guardedFetchRows, hPartial,
    fetch, query, ExternalCallMachine.a, ExternalCallMachine.v, callExternal,
    returnValue, returnDeclined, returnLanguageFault, returnEngineFault,
    returnResourceFault, label, external, slot, natPattern, fault, a,
    consumedBindings, runMatchBindings, matchRelationArgs,
    matchRelationArgument, matchPattern, matchArgs, Bindings.lookup,
    applyBindings, mergeBindings]

private theorem referenceEnv_guarded_fetch_at_one_nondeclined_empty
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true) (receipt : Pattern)
    (instructionName : String) (arguments : List Pattern)
    (notDeclined : instructionName ≠ "external-call:return-declined") :
    premiseStepWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (consumedBindings (compileCoreOperation operation) (label 1)
          (inputStore first second) fuelInfinite receipt fuelInfinite)
        (fetch (ExternalCallMachine.a instructionName arguments)) = [] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    arithmeticExternalCallReferenceEnv, fetchRows, guardedFetchRows, hPartial,
    fetch, query, ExternalCallMachine.a, ExternalCallMachine.v, callExternal,
    returnValue, returnDeclined, returnLanguageFault, returnEngineFault,
    returnResourceFault, label, external, slot, natPattern, fault, a,
    consumedBindings, runMatchBindings, matchRelationArgs,
    matchRelationArgument, matchPattern, Bindings.lookup,
    applyBindings, mergeBindings, notDeclined]

private theorem referenceEnv_guarded_fetch_call_exact
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true) (receipt : Pattern) :
    premiseStepWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (consumedBindings (compileCoreOperation operation) (label 2)
          (inputStore first second) fuelInfinite receipt fuelInfinite)
        (fetch (ExternalCallMachine.a "external-call:call-binary"
          [ExternalCallMachine.v "external", ExternalCallMachine.v "ifValue",
           ExternalCallMachine.v "ifLanguageFault", ExternalCallMachine.v "ifEngineFault",
           ExternalCallMachine.v "ifResourceFault"])) =
      [callFetchedBindings (compileCoreOperation operation) (label 2)
        (inputStore first second) fuelInfinite receipt fuelInfinite
        (external 0) (label 3) (label 4) (label 5) (label 6)] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    arithmeticExternalCallReferenceEnv, fetchRows, guardedFetchRows, hPartial,
    fetch, query, ExternalCallMachine.a, ExternalCallMachine.v, callExternal,
    returnValue, returnDeclined, returnLanguageFault, returnEngineFault,
    returnResourceFault, label, external, slot, natPattern, fault, a,
    consumedBindings, callFetchedBindings, runMatchBindings,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    Bindings.lookup, applyBindings, mergeBindings]

private theorem referenceEnv_guarded_fetch_at_two_noncall_empty
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true) (receipt : Pattern)
    (instructionName : String) (arguments : List Pattern)
    (notCall : instructionName ≠ "external-call:call-binary") :
    premiseStepWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (consumedBindings (compileCoreOperation operation) (label 2)
          (inputStore first second) fuelInfinite receipt fuelInfinite)
        (fetch (ExternalCallMachine.a instructionName arguments)) = [] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    arithmeticExternalCallReferenceEnv, fetchRows, guardedFetchRows, hPartial,
    fetch, query, ExternalCallMachine.a, ExternalCallMachine.v, callExternal,
    returnValue, returnDeclined, returnLanguageFault, returnEngineFault,
    returnResourceFault, label, external, slot, natPattern, fault, a,
    consumedBindings, runMatchBindings, matchRelationArgs,
    matchRelationArgument, matchPattern, Bindings.lookup,
    applyBindings, mergeBindings, notCall]

private theorem referenceEnv_guarded_fetch_return_value_exact
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true) (receipt : Pattern) :
    premiseStepWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (consumedBindings (compileCoreOperation operation) (label 3)
          (resultStore operation first second) fuelInfinite receipt fuelInfinite)
        (fetch (ExternalCallMachine.a "external-call:return-value" [ExternalCallMachine.v "slot"])) =
      [returnFetchedBindings (compileCoreOperation operation) (label 3)
        (resultStore operation first second) fuelInfinite receipt fuelInfinite
        (slot 2)] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    arithmeticExternalCallReferenceEnv, fetchRows, guardedFetchRows, hPartial,
    fetch, query, ExternalCallMachine.a, ExternalCallMachine.v, callExternal,
    returnValue, returnDeclined, returnLanguageFault, returnEngineFault,
    returnResourceFault, label, external, slot, natPattern, fault, a,
    consumedBindings, returnFetchedBindings, runMatchBindings,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    Bindings.lookup, applyBindings, mergeBindings]

private theorem referenceEnv_guarded_fetch_at_three_nonreturn_empty
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true) (receipt : Pattern)
    (instructionName : String) (arguments : List Pattern)
    (notReturn : instructionName ≠ "external-call:return-value") :
    premiseStepWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (consumedBindings (compileCoreOperation operation) (label 3)
          (resultStore operation first second) fuelInfinite receipt fuelInfinite)
        (fetch (ExternalCallMachine.a instructionName arguments)) = [] := by
  simp [premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
    arithmeticExternalCallReferenceEnv, fetchRows, guardedFetchRows, hPartial,
    fetch, query, ExternalCallMachine.a, ExternalCallMachine.v, callExternal,
    returnValue, returnDeclined, returnLanguageFault, returnEngineFault,
    returnResourceFault, label, external, slot, natPattern, fault, a,
    consumedBindings, runMatchBindings, matchRelationArgs,
    matchRelationArgument, matchPattern, Bindings.lookup,
    applyBindings, mergeBindings, notReturn]

private theorem guarded_decline_premises_exact
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true) :
    applyPremisesWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        returnDeclinedTransition.premises
        (runMatchBindings (compileCoreOperation operation) (label 1)
          (inputStore first second) fuelInfinite guardedBranchReceipt) =
      [consumedBindings (compileCoreOperation operation) (label 1)
        (inputStore first second) fuelInfinite guardedBranchReceipt
        fuelInfinite] := by
  simp only [returnDeclinedTransition, applyPremisesWithEnv,
    List.foldl_cons, List.foldl_nil, List.flatMap_singleton]
  rw [referenceEnv_consume_exact]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_guarded_fetch_declined_exact
    operation first second hPartial guardedBranchReceipt]

private theorem guarded_after_decline_nondeclined_premises_empty
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (instructionName : String) (arguments : List Pattern)
    (notDeclined : instructionName ≠ "external-call:return-declined")
    (remaining : List Premise) :
    applyPremisesWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (consumeFuel :: fetch (ExternalCallMachine.a instructionName arguments) ::
          remaining)
        (runMatchBindings (compileCoreOperation operation) (label 1)
          (inputStore first second) fuelInfinite guardedBranchReceipt) = [] := by
  unfold applyPremisesWithEnv
  rw [List.foldl_cons]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_consume_exact]
  simp only [List.foldl_cons, List.flatMap_singleton]
  rw [referenceEnv_guarded_fetch_at_one_nondeclined_empty
    operation first second hPartial guardedBranchReceipt
    instructionName arguments notDeclined]
  induction remaining with
  | nil => rfl
  | cons premise rest inductionHypothesis =>
      simp only [List.foldl_cons, List.flatMap_nil]
      exact inductionHypothesis

private theorem guarded_call_premises_exact
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (defined : ¬ targetUndefinedAt operation second) :
    applyPremisesWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        callValueTransition.premises
        (runMatchBindings (compileCoreOperation operation) (label 2)
          (inputStore first second) fuelInfinite guardedBranchReceipt) =
      [callValueBindings (compileCoreOperation operation) (label 2)
        (inputStore first second) fuelInfinite guardedBranchReceipt fuelInfinite
        (external 0) (label 3) (label 4) (label 5) (label 6)
        (resultStore operation first second)] := by
  simp only [callValueTransition, callRule, applyPremisesWithEnv,
    List.foldl_cons, List.foldl_nil, List.flatMap_singleton]
  rw [referenceEnv_consume_exact]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_guarded_fetch_call_exact operation first second hPartial
    guardedBranchReceipt]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_call_value_exact operation first second
    (label 2) (label 3) (label 4) (label 5) (label 6)
    guardedBranchReceipt defined]

private theorem guarded_call_nonvalue_premises_empty
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (defined : ¬ targetUndefinedAt operation second)
    (name target outcomeTag : String)
    (notValue : outcomeTag ≠ "external-call:external-value") :
    applyPremisesWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (callRule name target false
          (ExternalCallMachine.a outcomeTag [ExternalCallMachine.v "fault"])
          (ExternalCallMachine.v "store")).premises
        (runMatchBindings (compileCoreOperation operation) (label 2)
          (inputStore first second) fuelInfinite guardedBranchReceipt) = [] := by
  simp only [callRule, applyPremisesWithEnv, List.foldl_cons,
    List.foldl_nil, List.flatMap_singleton]
  rw [referenceEnv_consume_exact]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_guarded_fetch_call_exact operation first second hPartial
    guardedBranchReceipt]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_call_nonvalue_empty operation first second
    (label 2) (label 3) (label 4) (label 5) (label 6)
    guardedBranchReceipt defined outcomeTag notValue]

private theorem guarded_after_branch_noncall_premises_empty
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (instructionName : String) (arguments : List Pattern)
    (notCall : instructionName ≠ "external-call:call-binary")
    (remaining : List Premise) :
    applyPremisesWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (consumeFuel :: fetch (ExternalCallMachine.a instructionName arguments) ::
          remaining)
        (runMatchBindings (compileCoreOperation operation) (label 2)
          (inputStore first second) fuelInfinite guardedBranchReceipt) = [] := by
  unfold applyPremisesWithEnv
  rw [List.foldl_cons]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_consume_exact]
  simp only [List.foldl_cons, List.flatMap_singleton]
  rw [referenceEnv_guarded_fetch_at_two_noncall_empty
    operation first second hPartial guardedBranchReceipt
    instructionName arguments notCall]
  induction remaining with
  | nil => rfl
  | cons premise rest inductionHypothesis =>
      simp only [List.foldl_cons, List.flatMap_nil]
      exact inductionHypothesis

private theorem guarded_return_premises_exact
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true) :
    applyPremisesWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        returnValueTransition.premises
        (runMatchBindings (compileCoreOperation operation) (label 3)
          (resultStore operation first second) fuelInfinite
          (guardedExternalReceipt operation first second)) =
      [returnReadBindings (compileCoreOperation operation) (label 3)
        (resultStore operation first second) fuelInfinite
        (guardedExternalReceipt operation first second) fuelInfinite (slot 2)
        (exactIntegerValue (targetValue operation first second))] := by
  simp only [returnValueTransition, applyPremisesWithEnv,
    List.foldl_cons, List.foldl_nil, List.flatMap_singleton]
  rw [referenceEnv_consume_exact]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_guarded_fetch_return_value_exact
    operation first second hPartial
    (guardedExternalReceipt operation first second)]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_read_result_exact operation first second
    (label 3) (guardedExternalReceipt operation first second)]

private theorem guarded_after_call_nonreturn_premises_empty
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (instructionName : String) (arguments : List Pattern)
    (notReturn : instructionName ≠ "external-call:return-value")
    (remaining : List Premise) :
    applyPremisesWithEnv
        (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (consumeFuel :: fetch (ExternalCallMachine.a instructionName arguments) ::
          remaining)
        (runMatchBindings (compileCoreOperation operation) (label 3)
          (resultStore operation first second) fuelInfinite
          (guardedExternalReceipt operation first second)) = [] := by
  unfold applyPremisesWithEnv
  rw [List.foldl_cons]
  simp only [List.flatMap_singleton]
  rw [referenceEnv_consume_exact]
  simp only [List.foldl_cons, List.flatMap_singleton]
  rw [referenceEnv_guarded_fetch_at_three_nonreturn_empty
    operation first second hPartial
    (guardedExternalReceipt operation first second)
    instructionName arguments notReturn]
  induction remaining with
  | nil => rfl
  | cons premise rest inductionHypothesis =>
      simp only [List.foldl_cons, List.flatMap_nil]
      exact inductionHypothesis

private theorem match_guardedAfterBranch
    (rule : RewriteRule)
    (leftShape : rule.left =
      ExternalCallMachine.run (ExternalCallMachine.v "program") (ExternalCallMachine.v "pc")
        (ExternalCallMachine.v "store") (ExternalCallMachine.v "fuel")
        (ExternalCallMachine.v "receipt"))
    (operation : CoreOp) (first second : Int) (targetLabel : Nat) :
    matchPatternForRule externalCallLanguage rule
        (guardedAfterBranch operation first second targetLabel) =
      [runMatchBindings (compileCoreOperation operation) (label targetLabel)
        (inputStore first second) fuelInfinite guardedBranchReceipt] := by
  simpa [guardedAfterBranch, run, ExternalCallMachine.run, a, ExternalCallMachine.a] using
    match_run_transition rule leftShape
      (compileCoreOperation operation) (label targetLabel)
      (inputStore first second) fuelInfinite guardedBranchReceipt

private theorem match_guardedAfterCall
    (rule : RewriteRule)
    (leftShape : rule.left =
      ExternalCallMachine.run (ExternalCallMachine.v "program") (ExternalCallMachine.v "pc")
        (ExternalCallMachine.v "store") (ExternalCallMachine.v "fuel")
        (ExternalCallMachine.v "receipt"))
    (operation : CoreOp) (first second : Int) :
    matchPatternForRule externalCallLanguage rule
        (guardedAfterCall operation first second) =
      [runMatchBindings (compileCoreOperation operation) (label 3)
        (resultStore operation first second) fuelInfinite
        (guardedExternalReceipt operation first second)] := by
  simpa [guardedAfterCall, run, ExternalCallMachine.run, a, ExternalCallMachine.a] using
    match_run_transition rule leftShape
      (compileCoreOperation operation) (label 3)
      (resultStore operation first second) fuelInfinite
      (guardedExternalReceipt operation first second)

/-- A running ExternalCall state is deterministic whenever every non-fuel rule's
reachable premise fibre resolves to the same target.  This packages the
common root-step inversion without assuming global determinism of arbitrary
relation environments or arbitrary ExternalCall programs. -/
private theorem running_step_unique_from_resolver
    (relationEnv : RelationEnv)
    (program pc store receipt desired : Pattern)
    (resolve : ∀ rule,
      rule ∈ externalCallLanguageTransitions →
      rule.name ≠ "external-call:fuel-exhausted" →
      ∀ finalBindings,
        finalBindings ∈ applyPremisesWithEnv relationEnv externalCallLanguage rule.premises
          (runMatchBindings program pc store fuelInfinite receipt) →
        applyBindingsForRule externalCallLanguage rule finalBindings = desired)
    {target : Pattern}
    (step : langReducesUsing relationEnv externalCallLanguage
      (run program pc store receipt) target) :
    target = desired := by
  have root : RootStep relationEnv externalCallLanguage
      (run program pc store receipt) target :=
    (step_iff_rootStep_of_noncontextualRules
      externalCallLanguage_rules_noncontextual).mp step
  rcases root with
    ⟨rule, ruleMember, initialBindings, matched,
      finalBindings, premises, targetEq⟩
  change rule ∈ externalCallLanguageTransitions at ruleMember
  simp only [externalCallLanguageTransitions, List.mem_cons, List.mem_nil_iff,
    or_false] at ruleMember
  rcases ruleMember with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [matchPatternForRule_eq_syntactic, fuelExhaustedRule,
      run, ExternalCallMachine.run, fuelInfinite,
      a, ExternalCallMachine.a, ExternalCallMachine.v, matchPattern, matchArgs] at matched
  all_goals
    change initialBindings ∈ matchPatternForRule externalCallLanguage _
      (ExternalCallMachine.run program pc store fuelInfinite receipt) at matched
    rw [match_run_transition _ rfl program pc store fuelInfinite receipt]
      at matched
    simp only [List.mem_singleton] at matched
    subst initialBindings
    exact targetEq.symm.trans
      (resolve _ (by simp [externalCallLanguageTransitions]) (by decide)
        finalBindings premises)

private theorem guarded_start_step_unique_from_fibres
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (desired : Pattern)
    (zeroFinal nonzeroFinal : Option Bindings)
    (zeroPremises :
      applyPremisesWithEnv
          (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
          branchZeroTransition.premises
          (runMatchBindings (compileCoreOperation operation) (label 0)
            (inputStore first second) fuelInfinite receiptNil) =
        zeroFinal.toList)
    (nonzeroPremises :
      applyPremisesWithEnv
          (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
          branchNonzeroTransition.premises
          (runMatchBindings (compileCoreOperation operation) (label 0)
            (inputStore first second) fuelInfinite receiptNil) =
        nonzeroFinal.toList)
    (zeroTarget : ∀ finalBindings,
      zeroFinal = some finalBindings →
        applyBindingsForRule externalCallLanguage branchZeroTransition finalBindings =
          desired)
    (nonzeroTarget : ∀ finalBindings,
      nonzeroFinal = some finalBindings →
        applyBindingsForRule externalCallLanguage branchNonzeroTransition finalBindings =
          desired)
    {target : Pattern}
    (step :
      langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
        externalCallLanguage (compiledExternalCallStart operation first second) target) :
    target = desired := by
  have root :
      RootStep (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
        (compiledExternalCallStart operation first second) target :=
    (step_iff_rootStep_of_noncontextualRules
      externalCallLanguage_rules_noncontextual).mp step
  rcases root with
    ⟨rule, ruleMember, initialBindings, matched,
      finalBindings, premises, targetEq⟩
  change rule ∈ externalCallLanguageTransitions at ruleMember
  simp only [externalCallLanguageTransitions, List.mem_cons, List.mem_nil_iff,
    or_false] at ruleMember
  rcases ruleMember with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [matchPatternForRule_eq_syntactic, fuelExhaustedRule,
      compiledExternalCallStart, run, ExternalCallMachine.run, fuelInfinite,
      a, ExternalCallMachine.a, ExternalCallMachine.v, matchPattern, matchArgs] at matched
  all_goals
    rw [match_compiledExternalCallStart _ rfl operation first second] at matched
    simp only [List.mem_singleton] at matched
    subst initialBindings
  · rw [zeroPremises] at premises
    cases zeroCase : zeroFinal with
    | none => simp [zeroCase] at premises
    | some admitted =>
        simp [zeroCase] at premises
        subst finalBindings
        exact targetEq.symm.trans (zeroTarget admitted zeroCase)
  · rw [nonzeroPremises] at premises
    cases nonzeroCase : nonzeroFinal with
    | none => simp [nonzeroCase] at premises
    | some admitted =>
        simp [nonzeroCase] at premises
        subst finalBindings
        exact targetEq.symm.trans (nonzeroTarget admitted nonzeroCase)
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch (ExternalCallMachine.a "external-call:call-binary"
        [ExternalCallMachine.v "external", ExternalCallMachine.v "ifValue",
         ExternalCallMachine.v "ifLanguageFault", ExternalCallMachine.v "ifEngineFault",
         ExternalCallMachine.v "ifResourceFault"]) ::
        [query "ExternalCallCallBinaryExternal"
          [ExternalCallMachine.v "program", ExternalCallMachine.v "external",
           ExternalCallMachine.v "store",
           ExternalCallMachine.a "external-call:external-value" [ExternalCallMachine.v "nextStore"]]])
      (runMatchBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil) at premises
    rw [guarded_start_nonbranch_premises_empty operation first second hPartial
      "external-call:call-binary"
      [ExternalCallMachine.v "external", ExternalCallMachine.v "ifValue",
       ExternalCallMachine.v "ifLanguageFault", ExternalCallMachine.v "ifEngineFault",
       ExternalCallMachine.v "ifResourceFault"] (by decide) _] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch (ExternalCallMachine.a "external-call:call-binary"
        [ExternalCallMachine.v "external", ExternalCallMachine.v "ifValue",
         ExternalCallMachine.v "ifLanguageFault", ExternalCallMachine.v "ifEngineFault",
         ExternalCallMachine.v "ifResourceFault"]) ::
        [query "ExternalCallCallBinaryExternal"
          [ExternalCallMachine.v "program", ExternalCallMachine.v "external",
           ExternalCallMachine.v "store",
           ExternalCallMachine.a "external-call:external-language-fault"
             [ExternalCallMachine.v "fault"]]])
      (runMatchBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil) at premises
    rw [guarded_start_nonbranch_premises_empty operation first second hPartial
      "external-call:call-binary"
      [ExternalCallMachine.v "external", ExternalCallMachine.v "ifValue",
       ExternalCallMachine.v "ifLanguageFault", ExternalCallMachine.v "ifEngineFault",
       ExternalCallMachine.v "ifResourceFault"] (by decide) _] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch (ExternalCallMachine.a "external-call:call-binary"
        [ExternalCallMachine.v "external", ExternalCallMachine.v "ifValue",
         ExternalCallMachine.v "ifLanguageFault", ExternalCallMachine.v "ifEngineFault",
         ExternalCallMachine.v "ifResourceFault"]) ::
        [query "ExternalCallCallBinaryExternal"
          [ExternalCallMachine.v "program", ExternalCallMachine.v "external",
           ExternalCallMachine.v "store",
           ExternalCallMachine.a "external-call:external-engine-fault"
             [ExternalCallMachine.v "fault"]]])
      (runMatchBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil) at premises
    rw [guarded_start_nonbranch_premises_empty operation first second hPartial
      "external-call:call-binary"
      [ExternalCallMachine.v "external", ExternalCallMachine.v "ifValue",
       ExternalCallMachine.v "ifLanguageFault", ExternalCallMachine.v "ifEngineFault",
       ExternalCallMachine.v "ifResourceFault"] (by decide) _] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch (ExternalCallMachine.a "external-call:call-binary"
        [ExternalCallMachine.v "external", ExternalCallMachine.v "ifValue",
         ExternalCallMachine.v "ifLanguageFault", ExternalCallMachine.v "ifEngineFault",
         ExternalCallMachine.v "ifResourceFault"]) ::
        [query "ExternalCallCallBinaryExternal"
          [ExternalCallMachine.v "program", ExternalCallMachine.v "external",
           ExternalCallMachine.v "store",
           ExternalCallMachine.a "external-call:external-resource-fault"
             [ExternalCallMachine.v "fault"]]])
      (runMatchBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil) at premises
    rw [guarded_start_nonbranch_premises_empty operation first second hPartial
      "external-call:call-binary"
      [ExternalCallMachine.v "external", ExternalCallMachine.v "ifValue",
       ExternalCallMachine.v "ifLanguageFault", ExternalCallMachine.v "ifEngineFault",
       ExternalCallMachine.v "ifResourceFault"] (by decide) _] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch
        (ExternalCallMachine.a "external-call:return-value" [ExternalCallMachine.v "slot"]) ::
        [query "ExternalCallReadSlot"
          [ExternalCallMachine.v "store", ExternalCallMachine.v "slot",
           ExternalCallMachine.v "value"]])
      (runMatchBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil) at premises
    rw [guarded_start_nonbranch_premises_empty operation first second hPartial
      "external-call:return-value" [ExternalCallMachine.v "slot"] (by decide) _] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch (ExternalCallMachine.a "external-call:return-declined") :: [])
      (runMatchBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil) at premises
    rw [guarded_start_nonbranch_premises_empty operation first second hPartial
      "external-call:return-declined" [] (by decide) []] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch
        (ExternalCallMachine.a "external-call:return-language-fault" [ExternalCallMachine.v "fault"]) :: [])
      (runMatchBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil) at premises
    rw [guarded_start_nonbranch_premises_empty operation first second hPartial
      "external-call:return-language-fault" [ExternalCallMachine.v "fault"]
      (by decide) []] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch
        (ExternalCallMachine.a "external-call:return-engine-fault" [ExternalCallMachine.v "fault"]) :: [])
      (runMatchBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil) at premises
    rw [guarded_start_nonbranch_premises_empty operation first second hPartial
      "external-call:return-engine-fault" [ExternalCallMachine.v "fault"]
      (by decide) []] at premises
    simp at premises
  · change finalBindings ∈ applyPremisesWithEnv
      (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
      (consumeFuel :: fetch
        (ExternalCallMachine.a "external-call:return-resource-fault" [ExternalCallMachine.v "fault"]) :: [])
      (runMatchBindings (compileCoreOperation operation) (label 0)
        (inputStore first second) fuelInfinite receiptNil) at premises
    rw [guarded_start_nonbranch_premises_empty operation first second hPartial
      "external-call:return-resource-fault" [ExternalCallMachine.v "fault"]
      (by decide) []] at premises
    simp at premises

private theorem guarded_zero_start_step_unique
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (zeroDivisor : second = 0)
    {target : Pattern}
    (step :
      langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
        externalCallLanguage (compiledExternalCallStart operation first second) target) :
    target = guardedAfterBranch operation first second 1 := by
  let final := branchReadBindings (compileCoreOperation operation) (label 0)
    (inputStore first second) fuelInfinite receiptNil fuelInfinite
    (slot 1) (label 1) (label 2) (exactIntegerValue second)
  apply guarded_start_step_unique_from_fibres operation first second hPartial
    (guardedAfterBranch operation first second 1) (some final) none
  · simpa [final] using
      guarded_zero_branch_premises_exact operation first second hPartial
        zeroDivisor
  · simpa using
      guarded_zero_nonzero_branch_premises_empty operation first second
        hPartial zeroDivisor
  · intro admitted admittedEq
    simp [final] at admittedEq
    subst admitted
    simp [branchZeroTransition, branchRule,
      applyBindingsForRule_eq_syntactic, branchReadBindings,
      branchFetchedBindings, consumedBindings, runMatchBindings,
      guardedAfterBranch, guardedBranchReceipt,
      stepReceipt, ExternalCallMachine.stepReceipt,
      run, ExternalCallMachine.run, ExternalCallMachine.a, ExternalCallMachine.v,
      applyBindings, a]
  · intro admitted admittedEq
    simp at admittedEq
  · exact step

private theorem guarded_nonzero_start_step_unique
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (nonzeroDivisor : second ≠ 0)
    {target : Pattern}
    (step :
      langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
        externalCallLanguage (compiledExternalCallStart operation first second) target) :
    target = guardedAfterBranch operation first second 2 := by
  let final := branchReadBindings (compileCoreOperation operation) (label 0)
    (inputStore first second) fuelInfinite receiptNil fuelInfinite
    (slot 1) (label 1) (label 2) (exactIntegerValue second)
  apply guarded_start_step_unique_from_fibres operation first second hPartial
    (guardedAfterBranch operation first second 2) none (some final)
  · simpa using
      guarded_nonzero_zero_branch_premises_empty operation first second
        hPartial nonzeroDivisor
  · simpa [final] using
      guarded_nonzero_branch_premises_exact operation first second hPartial
        nonzeroDivisor
  · intro admitted admittedEq
    simp at admittedEq
  · intro admitted admittedEq
    simp [final] at admittedEq
    subst admitted
    simp [branchNonzeroTransition, branchRule,
      applyBindingsForRule_eq_syntactic, branchReadBindings,
      branchFetchedBindings, consumedBindings, runMatchBindings,
      guardedAfterBranch, guardedBranchReceipt,
      stepReceipt, ExternalCallMachine.stepReceipt,
      run, ExternalCallMachine.run, ExternalCallMachine.a, ExternalCallMachine.v,
      applyBindings, a]
  · exact step

private theorem guarded_decline_step_unique
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (undefined : targetUndefinedAt operation second)
    {target : Pattern}
    (step :
      langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
        externalCallLanguage (guardedAfterBranch operation first second 1) target) :
    target = compiledExternalCallDone operation first second := by
  apply running_step_unique_from_resolver
    (arithmeticExternalCallReferenceEnv operation first second)
    (compileCoreOperation operation) (label 1) (inputStore first second)
    guardedBranchReceipt (compiledExternalCallDone operation first second)
  · intro rule ruleMember nonFuel finalBindings premises
    change rule ∈ externalCallLanguageTransitions at ruleMember
    simp only [externalCallLanguageTransitions, List.mem_cons, List.mem_nil_iff,
      or_false] at ruleMember
    rcases ruleMember with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | exact (nonFuel rfl).elim
      | (rw [guarded_decline_premises_exact operation first second hPartial]
            at premises
         simp only [List.mem_singleton] at premises
         subst finalBindings
         simp [returnDeclinedTransition, applyBindingsForRule_eq_syntactic,
           consumedBindings, runMatchBindings,
           compiledExternalCallDone, compiledExternalCallOutcome, compiledExternalCallReceipt, undefined,
           guardedBranchReceipt, stepReceipt, ExternalCallMachine.stepReceipt,
           halted, ExternalCallMachine.halted, ExternalCallMachine.a, ExternalCallMachine.v,
           applyBindings, a])
      | (change finalBindings ∈ applyPremisesWithEnv
            (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
            (consumeFuel :: fetch (ExternalCallMachine.a _ _) :: _)
            (runMatchBindings (compileCoreOperation operation) (label 1)
              (inputStore first second) fuelInfinite guardedBranchReceipt)
            at premises
         rw [guarded_after_decline_nondeclined_premises_empty
           operation first second hPartial _ _ (by decide) _] at premises
         simp at premises)
  · exact step

private theorem guarded_call_step_unique
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (defined : ¬ targetUndefinedAt operation second)
    {target : Pattern}
    (step :
      langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
        externalCallLanguage (guardedAfterBranch operation first second 2) target) :
    target = guardedAfterCall operation first second := by
  apply running_step_unique_from_resolver
    (arithmeticExternalCallReferenceEnv operation first second)
    (compileCoreOperation operation) (label 2) (inputStore first second)
    guardedBranchReceipt (guardedAfterCall operation first second)
  · intro rule ruleMember nonFuel finalBindings premises
    change rule ∈ externalCallLanguageTransitions at ruleMember
    simp only [externalCallLanguageTransitions, List.mem_cons, List.mem_nil_iff,
      or_false] at ruleMember
    rcases ruleMember with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | exact (nonFuel rfl).elim
      | (rw [guarded_call_premises_exact operation first second hPartial
            defined] at premises
         simp only [List.mem_singleton] at premises
         subst finalBindings
         simp [callValueTransition, callRule,
           applyBindingsForRule_eq_syntactic,
           callValueBindings, callFetchedBindings, consumedBindings,
           runMatchBindings, guardedAfterCall, guardedExternalReceipt,
           guardedBranchReceipt, targetExternalValue,
           externalReceipt, ExternalCallMachine.externalReceipt,
           stepReceipt, ExternalCallMachine.stepReceipt,
           run, ExternalCallMachine.run, ExternalCallMachine.a, ExternalCallMachine.v,
           applyBindings, a])
      | (change finalBindings ∈ applyPremisesWithEnv
            (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
            (callRule _ _ false
              (ExternalCallMachine.a _ [ExternalCallMachine.v "fault"])
              (ExternalCallMachine.v "store")).premises
            (runMatchBindings (compileCoreOperation operation) (label 2)
              (inputStore first second) fuelInfinite guardedBranchReceipt)
            at premises
         rw [guarded_call_nonvalue_premises_empty
            operation first second hPartial defined _ _ _ (by decide)]
            at premises
         simp at premises)
      | (change finalBindings ∈ applyPremisesWithEnv
            (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
            (consumeFuel :: fetch (ExternalCallMachine.a _ _) :: _)
            (runMatchBindings (compileCoreOperation operation) (label 2)
              (inputStore first second) fuelInfinite guardedBranchReceipt)
            at premises
         rw [guarded_after_branch_noncall_premises_empty
           operation first second hPartial _ _ (by decide) _] at premises
         simp at premises)
  · exact step

private theorem guarded_return_step_unique
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (defined : ¬ targetUndefinedAt operation second)
    {target : Pattern}
    (step :
      langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
        externalCallLanguage (guardedAfterCall operation first second) target) :
    target = compiledExternalCallDone operation first second := by
  apply running_step_unique_from_resolver
    (arithmeticExternalCallReferenceEnv operation first second)
    (compileCoreOperation operation) (label 3)
    (resultStore operation first second)
    (guardedExternalReceipt operation first second)
    (compiledExternalCallDone operation first second)
  · intro rule ruleMember nonFuel finalBindings premises
    change rule ∈ externalCallLanguageTransitions at ruleMember
    simp only [externalCallLanguageTransitions, List.mem_cons, List.mem_nil_iff,
      or_false] at ruleMember
    rcases ruleMember with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | exact (nonFuel rfl).elim
      | (rw [guarded_return_premises_exact operation first second hPartial]
            at premises
         simp only [List.mem_singleton] at premises
         subst finalBindings
         simp [returnValueTransition, applyBindingsForRule_eq_syntactic,
           returnReadBindings, returnFetchedBindings, consumedBindings,
           runMatchBindings, compiledExternalCallDone, compiledExternalCallOutcome,
           compiledExternalCallReceipt, hPartial, defined,
           guardedExternalReceipt, guardedBranchReceipt,
           targetExternalValue, exactIntegerValue,
           stepReceipt, ExternalCallMachine.stepReceipt,
           halted, ExternalCallMachine.halted, ExternalCallMachine.a, ExternalCallMachine.v,
           applyBindings, a])
      | (change finalBindings ∈ applyPremisesWithEnv
            (arithmeticExternalCallReferenceEnv operation first second) externalCallLanguage
            (consumeFuel :: fetch (ExternalCallMachine.a _ _) :: _)
            (runMatchBindings (compileCoreOperation operation) (label 3)
              (resultStore operation first second) fuelInfinite
              (guardedExternalReceipt operation first second))
            at premises
         rw [guarded_after_call_nonreturn_premises_empty
           operation first second hPartial _ _ (by decide) _] at premises
         simp at premises)
  · exact step

private theorem total_call_step
    (operation : CoreOp) (first second : Int)
    (total : operation.isPartial = false)
    (defined : ¬ targetUndefinedAt operation second) :
    langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
      externalCallLanguage (compiledExternalCallStart operation first second)
      (totalAfterCall operation first second) := by
  apply admittedExternalCallStep
  simpa [compiledExternalCallStart, totalAfterCall, totalCallReceipt,
    run, ExternalCallMachine.run,
    externalReceipt, ExternalCallMachine.externalReceipt, targetExternalValue,
    stepReceipt, ExternalCallMachine.stepReceipt, a, ExternalCallMachine.a] using
    (callValueTransition_mem_rewriteAt
      (relationEnv := arithmeticExternalCallReferenceEnv operation first second)
      (program := compileCoreOperation operation)
      (pc := label 0) (store := inputStore first second)
      (fuel := fuelInfinite) (receipt := receiptNil)
      (nextFuel := fuelInfinite) (external := external 0)
      (ifValue := label 1) (ifLanguageFault := label 2)
      (ifEngineFault := label 3) (ifResourceFault := label 4)
      (nextStore := resultStore operation first second)
      (by simp [arithmeticExternalCallReferenceEnv])
      (by simp [arithmeticExternalCallReferenceEnv, fetchRows, totalFetchRows, total,
        callExternal, a, ExternalCallMachine.a])
      (by simp [arithmeticExternalCallReferenceEnv, defined, targetExternalValue,
        a, ExternalCallMachine.a]))

private theorem total_return_step
    (operation : CoreOp) (first second : Int)
    (total : operation.isPartial = false)
    (defined : ¬ targetUndefinedAt operation second) :
    langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
      externalCallLanguage (totalAfterCall operation first second)
      (compiledExternalCallDone operation first second) := by
  apply admittedExternalCallStep
  simpa [totalAfterCall, totalCallReceipt, compiledExternalCallDone, compiledExternalCallOutcome,
    compiledExternalCallReceipt, total, defined, run, halted,
    ExternalCallMachine.run, ExternalCallMachine.halted,
    externalReceipt, ExternalCallMachine.externalReceipt,
    stepReceipt, ExternalCallMachine.stepReceipt, targetExternalValue,
    exactIntegerValue, a, ExternalCallMachine.a] using
    (returnValueTransition_mem_rewriteAt
      (relationEnv := arithmeticExternalCallReferenceEnv operation first second)
      (program := compileCoreOperation operation)
      (pc := label 1) (store := resultStore operation first second)
      (fuel := fuelInfinite)
      (receipt := externalReceipt (external 0)
        (targetExternalValue operation first second) (label 0) receiptNil)
      (nextFuel := fuelInfinite) (slot := slot 2)
      (value := exactIntegerValue (targetValue operation first second))
      (by simp [arithmeticExternalCallReferenceEnv])
      (by simp [arithmeticExternalCallReferenceEnv, fetchRows, totalFetchRows, total,
        returnValue, a, ExternalCallMachine.a])
      (by simp [arithmeticExternalCallReferenceEnv, exactIntegerValue, a]))

private theorem guarded_zero_branch_step
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (zeroDivisor : second = 0) :
    langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
      externalCallLanguage (compiledExternalCallStart operation first second)
      (guardedAfterBranch operation first second 1) := by
  apply admittedExternalCallStep
  simpa [compiledExternalCallStart, guardedAfterBranch, guardedBranchReceipt,
    run, ExternalCallMachine.run,
    stepReceipt, ExternalCallMachine.stepReceipt, a, ExternalCallMachine.a] using
    (branchTransition_mem_rewriteAt
      (relationEnv := arithmeticExternalCallReferenceEnv operation first second)
      (rule := branchZeroTransition) (test := "ExternalCallIsZero")
      (program := compileCoreOperation operation)
      (pc := label 0) (store := inputStore first second)
      (fuel := fuelInfinite) (receipt := receiptNil)
      (nextFuel := fuelInfinite) (slot := slot 1)
      (ifZero := label 1) (ifNonzero := label 2)
      (value := exactIntegerValue second) (target := label 1)
      (by simp [externalCallLanguage, externalCallLanguageTransitions])
      rfl rfl
      (by simp [branchZeroTransition, branchRule,
        applyBindingsForRule_eq_syntactic, branchReadBindings,
        branchFetchedBindings, consumedBindings, runMatchBindings,
        applyBindings, ExternalCallMachine.run, ExternalCallMachine.stepReceipt,
        ExternalCallMachine.a, ExternalCallMachine.v])
      (by simp [arithmeticExternalCallReferenceEnv])
      (by simp [arithmeticExternalCallReferenceEnv, fetchRows, guardedFetchRows,
        hPartial, a, ExternalCallMachine.a])
      (by simp [arithmeticExternalCallReferenceEnv, exactIntegerValue, a])
      (by simp [arithmeticExternalCallReferenceEnv, zeroDivisor,
        exactIntegerValue, a]))

private theorem guarded_nonzero_branch_step
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (nonzeroDivisor : second ≠ 0) :
    langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
      externalCallLanguage (compiledExternalCallStart operation first second)
      (guardedAfterBranch operation first second 2) := by
  apply admittedExternalCallStep
  simpa [compiledExternalCallStart, guardedAfterBranch, guardedBranchReceipt,
    run, ExternalCallMachine.run,
    stepReceipt, ExternalCallMachine.stepReceipt, a, ExternalCallMachine.a] using
    (branchTransition_mem_rewriteAt
      (relationEnv := arithmeticExternalCallReferenceEnv operation first second)
      (rule := branchNonzeroTransition) (test := "ExternalCallIsNonzero")
      (program := compileCoreOperation operation)
      (pc := label 0) (store := inputStore first second)
      (fuel := fuelInfinite) (receipt := receiptNil)
      (nextFuel := fuelInfinite) (slot := slot 1)
      (ifZero := label 1) (ifNonzero := label 2)
      (value := exactIntegerValue second) (target := label 2)
      (by simp [externalCallLanguage, externalCallLanguageTransitions])
      rfl rfl
      (by simp [branchNonzeroTransition, branchRule,
        applyBindingsForRule_eq_syntactic, branchReadBindings,
        branchFetchedBindings, consumedBindings, runMatchBindings,
        applyBindings, ExternalCallMachine.run, ExternalCallMachine.stepReceipt,
        ExternalCallMachine.a, ExternalCallMachine.v])
      (by simp [arithmeticExternalCallReferenceEnv])
      (by simp [arithmeticExternalCallReferenceEnv, fetchRows, guardedFetchRows,
        hPartial, a, ExternalCallMachine.a])
      (by simp [arithmeticExternalCallReferenceEnv, exactIntegerValue, a])
      (by simp [arithmeticExternalCallReferenceEnv, nonzeroDivisor,
        exactIntegerValue, a]))

private theorem guarded_call_step
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (defined : ¬ targetUndefinedAt operation second) :
    langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
      externalCallLanguage (guardedAfterBranch operation first second 2)
      (guardedAfterCall operation first second) := by
  apply admittedExternalCallStep
  simpa [guardedAfterBranch, guardedAfterCall, guardedBranchReceipt,
    guardedExternalReceipt, run, ExternalCallMachine.run,
    externalReceipt, ExternalCallMachine.externalReceipt, targetExternalValue,
    stepReceipt, ExternalCallMachine.stepReceipt, a, ExternalCallMachine.a] using
    (callValueTransition_mem_rewriteAt
      (relationEnv := arithmeticExternalCallReferenceEnv operation first second)
      (program := compileCoreOperation operation)
      (pc := label 2) (store := inputStore first second)
      (fuel := fuelInfinite)
      (receipt := stepReceipt (label 0) receiptNil)
      (nextFuel := fuelInfinite) (external := external 0)
      (ifValue := label 3) (ifLanguageFault := label 4)
      (ifEngineFault := label 5) (ifResourceFault := label 6)
      (nextStore := resultStore operation first second)
      (by simp [arithmeticExternalCallReferenceEnv])
      (by simp [arithmeticExternalCallReferenceEnv, fetchRows, guardedFetchRows,
        hPartial, callExternal, a, ExternalCallMachine.a])
      (by simp [arithmeticExternalCallReferenceEnv, defined, targetExternalValue,
        a, ExternalCallMachine.a]))

private theorem guarded_return_step
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (defined : ¬ targetUndefinedAt operation second) :
    langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
      externalCallLanguage (guardedAfterCall operation first second)
      (compiledExternalCallDone operation first second) := by
  apply admittedExternalCallStep
  simpa [guardedAfterCall, guardedExternalReceipt, guardedBranchReceipt,
    compiledExternalCallDone, compiledExternalCallOutcome,
    compiledExternalCallReceipt, hPartial, defined, run, halted,
    ExternalCallMachine.run, ExternalCallMachine.halted,
    externalReceipt, ExternalCallMachine.externalReceipt,
    stepReceipt, ExternalCallMachine.stepReceipt, targetExternalValue,
    exactIntegerValue, a, ExternalCallMachine.a] using
    (returnValueTransition_mem_rewriteAt
      (relationEnv := arithmeticExternalCallReferenceEnv operation first second)
      (program := compileCoreOperation operation)
      (pc := label 3) (store := resultStore operation first second)
      (fuel := fuelInfinite)
      (receipt := externalReceipt (external 0)
        (targetExternalValue operation first second) (label 2)
        (stepReceipt (label 0) receiptNil))
      (nextFuel := fuelInfinite) (slot := slot 2)
      (value := exactIntegerValue (targetValue operation first second))
      (by simp [arithmeticExternalCallReferenceEnv])
      (by simp [arithmeticExternalCallReferenceEnv, fetchRows, guardedFetchRows,
        hPartial, returnValue, a, ExternalCallMachine.a])
      (by simp [arithmeticExternalCallReferenceEnv, exactIntegerValue, a]))

private theorem guarded_decline_step
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (undefined : targetUndefinedAt operation second) :
    langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
      externalCallLanguage (guardedAfterBranch operation first second 1)
      (compiledExternalCallDone operation first second) := by
  apply admittedExternalCallStep
  simpa [guardedAfterBranch, guardedBranchReceipt,
    compiledExternalCallDone, compiledExternalCallOutcome,
    compiledExternalCallReceipt, undefined, run, halted,
    ExternalCallMachine.run, ExternalCallMachine.halted,
    stepReceipt, ExternalCallMachine.stepReceipt, a, ExternalCallMachine.a] using
    (returnDeclinedTransition_mem_rewriteAt
      (relationEnv := arithmeticExternalCallReferenceEnv operation first second)
      (program := compileCoreOperation operation)
      (pc := label 1) (store := inputStore first second)
      (fuel := fuelInfinite)
      (receipt := stepReceipt (label 0) receiptNil)
      (nextFuel := fuelInfinite)
      (by simp [arithmeticExternalCallReferenceEnv])
      (by simp [arithmeticExternalCallReferenceEnv, fetchRows, guardedFetchRows,
        hPartial, returnDeclined, a, ExternalCallMachine.a]))

/-- Every exact operation and integer pair has an explicit finite authored-ExternalCall
trace to the declared outcome and ordered receipt.  Total operations take two
edges; defined partial operations take three; zero divisors take the guarded
decline path and never require an external-call row. -/
theorem compiledExternalCall_reaches_declared_done
    (operation : CoreOp) (first second : Int) :
    Relation.ReflTransGen
      (langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
        externalCallLanguage)
      (compiledExternalCallStart operation first second)
      (compiledExternalCallDone operation first second) := by
  by_cases hPartial : operation.isPartial = true
  · by_cases undefined : targetUndefinedAt operation second
    · have targetUndefined :
          (ArithmeticExternalCallPilot.compileSyntax operation).undefinedAt second := by
        simpa [targetUndefinedAt, targetOperation] using undefined
      have sourceUndefined : undefinedAt operation second :=
        (ArithmeticExternalCallPilot.compileSyntax_undefinedAt
          operation second).1 targetUndefined
      have zeroDivisor : second = 0 := sourceUndefined.2
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail Relation.ReflTransGen.refl
          (guarded_zero_branch_step operation first second
            hPartial zeroDivisor))
        (guarded_decline_step operation first second hPartial undefined)
    · have nonzeroDivisor : second ≠ 0 := by
        intro zeroDivisor
        apply undefined
        have sourceUndefined : undefinedAt operation second :=
          ⟨hPartial, zeroDivisor⟩
        have targetUndefined :=
          (ArithmeticExternalCallPilot.compileSyntax_undefinedAt
            operation second).2 sourceUndefined
        simpa [targetUndefinedAt, targetOperation] using targetUndefined
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail
          (Relation.ReflTransGen.tail Relation.ReflTransGen.refl
            (guarded_nonzero_branch_step operation first second
              hPartial nonzeroDivisor))
          (guarded_call_step operation first second hPartial undefined))
        (guarded_return_step operation first second hPartial undefined)
  · have total : operation.isPartial = false :=
      Bool.eq_false_of_not_eq_true hPartial
    have defined : ¬ targetUndefinedAt operation second := by
      intro targetUndefined
      have compiledUndefined :
          (ArithmeticExternalCallPilot.compileSyntax operation).undefinedAt second := by
        simpa [targetUndefinedAt, targetOperation] using targetUndefined
      have sourceUndefined : undefinedAt operation second :=
        (ArithmeticExternalCallPilot.compileSyntax_undefinedAt
          operation second).1 compiledUndefined
      exact hPartial sourceUndefined.1
    exact Relation.ReflTransGen.tail
      (Relation.ReflTransGen.tail Relation.ReflTransGen.refl
        (total_call_step operation first second total defined))
      (total_return_step operation first second total defined)

private theorem no_step_from_compiledExternalCallDone
    (operation : CoreOp) (first second : Int) (target : Pattern) :
    ¬ langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
      externalCallLanguage (compiledExternalCallDone operation first second) target := by
  simpa [compiledExternalCallDone, halted, ExternalCallMachine.halted, a, ExternalCallMachine.a] using
    (no_step_from_halted
      (arithmeticExternalCallReferenceEnv operation first second)
      (compiledExternalCallOutcome operation first second)
      (compiledExternalCallReceipt operation first second) target)

/-- Every target reachable from a compiled total-operation start is one of
the two running phases or the declared terminal configuration. -/
private theorem total_reachable_classification
    (operation : CoreOp) (first second : Int)
    (total : operation.isPartial = false)
    (defined : ¬ targetUndefinedAt operation second)
    {target : Pattern}
    (path : Relation.ReflTransGen
      (langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
        externalCallLanguage)
      (compiledExternalCallStart operation first second) target) :
    target = compiledExternalCallStart operation first second ∨
      target = totalAfterCall operation first second ∨
      target = compiledExternalCallDone operation first second := by
  induction path with
  | refl => exact Or.inl rfl
  | tail prior edge inductionHypothesis =>
      rcases inductionHypothesis with atStart | atAfterCall | atDone
      · subst atStart
        exact Or.inr (Or.inl
          (total_start_step_unique operation first second total defined edge))
      · subst atAfterCall
        exact Or.inr (Or.inr
          (total_after_call_step_unique operation first second total defined edge))
      · subst atDone
        exact (no_step_from_compiledExternalCallDone operation first second _ edge).elim

/-- Reachable total-operation completion reflects both the declared outcome
and the exact ordered receipt.  This is the proof-relevant no-invention half
for the total compiler image. -/
private theorem total_halted_no_invention
    (operation : CoreOp) (first second : Int)
    (total : operation.isPartial = false)
    (defined : ¬ targetUndefinedAt operation second)
    (outcome receipt : Pattern)
    (path : Relation.ReflTransGen
      (langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
        externalCallLanguage)
      (compiledExternalCallStart operation first second) (halted outcome receipt)) :
    outcome = compiledExternalCallOutcome operation first second ∧
      receipt = compiledExternalCallReceipt operation first second := by
  rcases total_reachable_classification operation first second total defined
      path with atStart | atAfterCall | atDone
  · simp [compiledExternalCallStart, run, halted, a] at atStart
  · simp [totalAfterCall, run, halted, a] at atAfterCall
  · simpa [compiledExternalCallDone, halted, ExternalCallMachine.halted,
      a, ExternalCallMachine.a] using atDone

private theorem guarded_zero_reachable_classification
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (undefined : targetUndefinedAt operation second)
    (zeroDivisor : second = 0)
    {target : Pattern}
    (path : Relation.ReflTransGen
      (langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
        externalCallLanguage)
      (compiledExternalCallStart operation first second) target) :
    target = compiledExternalCallStart operation first second ∨
      target = guardedAfterBranch operation first second 1 ∨
      target = compiledExternalCallDone operation first second := by
  induction path with
  | refl => exact Or.inl rfl
  | tail prior edge inductionHypothesis =>
      rcases inductionHypothesis with atStart | atAfterBranch | atDone
      · subst atStart
        exact Or.inr (Or.inl
          (guarded_zero_start_step_unique operation first second
            hPartial zeroDivisor edge))
      · subst atAfterBranch
        exact Or.inr (Or.inr
          (guarded_decline_step_unique operation first second
            hPartial undefined edge))
      · subst atDone
        exact (no_step_from_compiledExternalCallDone operation first second _ edge).elim

private theorem guarded_nonzero_reachable_classification
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (defined : ¬ targetUndefinedAt operation second)
    (nonzeroDivisor : second ≠ 0)
    {target : Pattern}
    (path : Relation.ReflTransGen
      (langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
        externalCallLanguage)
      (compiledExternalCallStart operation first second) target) :
    target = compiledExternalCallStart operation first second ∨
      target = guardedAfterBranch operation first second 2 ∨
      target = guardedAfterCall operation first second ∨
      target = compiledExternalCallDone operation first second := by
  induction path with
  | refl => exact Or.inl rfl
  | tail prior edge inductionHypothesis =>
      rcases inductionHypothesis with
        atStart | atAfterBranch | atAfterCall | atDone
      · subst atStart
        exact Or.inr (Or.inl
          (guarded_nonzero_start_step_unique operation first second
            hPartial nonzeroDivisor edge))
      · subst atAfterBranch
        exact Or.inr (Or.inr (Or.inl
          (guarded_call_step_unique operation first second
            hPartial defined edge)))
      · subst atAfterCall
        exact Or.inr (Or.inr (Or.inr
          (guarded_return_step_unique operation first second
            hPartial defined edge)))
      · subst atDone
        exact (no_step_from_compiledExternalCallDone operation first second _ edge).elim

private theorem guarded_zero_halted_no_invention
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (undefined : targetUndefinedAt operation second)
    (zeroDivisor : second = 0)
    (outcome receipt : Pattern)
    (path : Relation.ReflTransGen
      (langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
        externalCallLanguage)
      (compiledExternalCallStart operation first second) (halted outcome receipt)) :
    outcome = compiledExternalCallOutcome operation first second ∧
      receipt = compiledExternalCallReceipt operation first second := by
  rcases guarded_zero_reachable_classification
      operation first second hPartial undefined zeroDivisor path with
    atStart | atAfterBranch | atDone
  · simp [compiledExternalCallStart, run, halted, a] at atStart
  · simp [guardedAfterBranch, run, halted, a] at atAfterBranch
  · simpa [compiledExternalCallDone, halted, ExternalCallMachine.halted,
      a, ExternalCallMachine.a] using atDone

private theorem guarded_nonzero_halted_no_invention
    (operation : CoreOp) (first second : Int)
    (hPartial : operation.isPartial = true)
    (defined : ¬ targetUndefinedAt operation second)
    (nonzeroDivisor : second ≠ 0)
    (outcome receipt : Pattern)
    (path : Relation.ReflTransGen
      (langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
        externalCallLanguage)
      (compiledExternalCallStart operation first second) (halted outcome receipt)) :
    outcome = compiledExternalCallOutcome operation first second ∧
      receipt = compiledExternalCallReceipt operation first second := by
  rcases guarded_nonzero_reachable_classification
      operation first second hPartial defined nonzeroDivisor path with
    atStart | atAfterBranch | atAfterCall | atDone
  · simp [compiledExternalCallStart, run, halted, a] at atStart
  · simp [guardedAfterBranch, run, halted, a] at atAfterBranch
  · simp [guardedAfterCall, run, halted, a] at atAfterCall
  · simpa [compiledExternalCallDone, halted, ExternalCallMachine.halted,
      a, ExternalCallMachine.a] using atDone

/-- Every halted configuration reachable from the compiled ExternalCall image reflects
the independently declared outcome and the exact ordered receipt.  Together
with `compiledExternalCall_reaches_declared_done`, this is preservation and
proof-relevant no-invention for all seven operations and all integer inputs. -/
theorem compiledExternalCall_halted_no_invention
    (operation : CoreOp) (first second : Int)
    (outcome receipt : Pattern)
    (path : Relation.ReflTransGen
      (langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
        externalCallLanguage)
      (compiledExternalCallStart operation first second) (halted outcome receipt)) :
    outcome = compiledExternalCallOutcome operation first second ∧
      receipt = compiledExternalCallReceipt operation first second := by
  by_cases hPartial : operation.isPartial = true
  · by_cases undefined : targetUndefinedAt operation second
    · have targetUndefined :
          (ArithmeticExternalCallPilot.compileSyntax operation).undefinedAt second := by
        simpa [targetUndefinedAt, targetOperation] using undefined
      have sourceUndefined : undefinedAt operation second :=
        (ArithmeticExternalCallPilot.compileSyntax_undefinedAt
          operation second).1 targetUndefined
      exact guarded_zero_halted_no_invention operation first second
        hPartial undefined sourceUndefined.2 outcome receipt path
    · have nonzeroDivisor : second ≠ 0 := by
        intro zeroDivisor
        apply undefined
        have sourceUndefined : undefinedAt operation second :=
          ⟨hPartial, zeroDivisor⟩
        have targetUndefined :=
          (ArithmeticExternalCallPilot.compileSyntax_undefinedAt
            operation second).2 sourceUndefined
        simpa [targetUndefinedAt, targetOperation] using targetUndefined
      exact guarded_nonzero_halted_no_invention operation first second
        hPartial undefined nonzeroDivisor outcome receipt path
  · have total : operation.isPartial = false :=
      Bool.eq_false_of_not_eq_true hPartial
    have defined : ¬ targetUndefinedAt operation second := by
      intro targetUndefined
      have compiledUndefined :
          (ArithmeticExternalCallPilot.compileSyntax operation).undefinedAt second := by
        simpa [targetUndefinedAt, targetOperation] using targetUndefined
      have sourceUndefined : undefinedAt operation second :=
        (ArithmeticExternalCallPilot.compileSyntax_undefinedAt
          operation second).1 compiledUndefined
      exact hPartial sourceUndefined.1
    exact total_halted_no_invention operation first second total defined
      outcome receipt path

/-- Negative control: no different outcome or receipt can be reached from a
compiled start under the same authored ExternalCall relation environment. -/
theorem compiledExternalCall_cannot_invent_completion
    (operation : CoreOp) (first second : Int)
    (outcome receipt : Pattern)
    (different : outcome ≠ compiledExternalCallOutcome operation first second ∨
      receipt ≠ compiledExternalCallReceipt operation first second) :
    ¬ Relation.ReflTransGen
      (langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
        externalCallLanguage)
      (compiledExternalCallStart operation first second) (halted outcome receipt) := by
  intro path
  have reflected := compiledExternalCall_halted_no_invention
    operation first second outcome receipt path
  rcases different with outcomeDifferent | receiptDifferent
  · exact outcomeDifferent reflected.1
  · exact receiptDifferent reflected.2

/-! ## Source execution and observation preservation -/

private def sourceOutcomePattern
    (operation : CoreOp) (first second : Int) : Pattern :=
  match coreSem operation first second with
  | .declined => a "arith:outcome-declined"
  | .val value => a "arith:outcome-value" [integerAtom value]

private def sourceRelationName : CoreOp → String
  | .add => "ExactIntegerAdd"
  | .sub => "ExactIntegerSub"
  | .mul => "ExactIntegerMul"
  | .tquot => "ExactIntegerTQuot"
  | .fquot => "ExactIntegerFQuot"
  | .trem => "ExactIntegerTRem"
  | .frem => "ExactIntegerFRem"

/-- The universal source-side arithmetic relation.  Unlike the target
external relation, this environment is defined directly by the independently
authored mathematical source semantics. -/
def arithmeticSourceReferenceEnv
    (operation : CoreOp) (first second : Int) : RelationEnv where
  tuples := fun relation _arguments =>
    if relation == sourceRelationName operation then
      [[integerAtom first, integerAtom second,
        sourceOutcomePattern operation first second]]
    else
      []

def arithmeticSourceStart
    (operation : CoreOp) (first second : Int) : Pattern :=
  a "arith:eval"
    [encodeSourceOperation operation, integerAtom first, integerAtom second]

def arithmeticSourceDone
    (operation : CoreOp) (first second : Int) : Pattern :=
  a "arith:halted" [sourceOutcomePattern operation first second]

private def sourceOperationName : CoreOp → String
  | .add => "arith:add"
  | .sub => "arith:sub"
  | .mul => "arith:mul"
  | .tquot => "arith:tquot"
  | .fquot => "arith:fquot"
  | .trem => "arith:trem"
  | .frem => "arith:frem"

private def sourceRule (operation : CoreOp) : RewriteRule :=
  evaluateRule (sourceOperationName operation) (sourceRelationName operation)

private theorem encodeSourceOperation_eq
    (operation : CoreOp) :
    encodeSourceOperation operation =
      ExactArithmeticNTT.a (sourceOperationName operation) := by
  cases operation <;>
    rfl

private def sourceInitialBindings (first second : Int) : Bindings := [
  ("first", integerAtom first), ("second", integerAtom second)]

private def sourceFinalBindings
    (operation : CoreOp) (first second : Int) : Bindings :=
  ("outcome", sourceOutcomePattern operation first second) ::
    sourceInitialBindings first second

private theorem sourceRule_member (operation : CoreOp) :
    sourceRule operation ∈ exactArithmetic.rewrites := by
  cases operation <;>
    simp [sourceRule, sourceOperationName, sourceRelationName,
      exactArithmetic, evaluateRule]

private theorem sourceRule_premises (operation : CoreOp) :
    (sourceRule operation).premises =
      [.relationQuery (sourceRelationName operation)
        [.fvar "first", .fvar "second", .fvar "outcome"]] := by
  rfl

private theorem match_sourceRule
    (operation : CoreOp) (first second : Int) :
    matchPatternForRule exactArithmetic (sourceRule operation)
        (arithmeticSourceStart operation first second) =
      [sourceInitialBindings first second] := by
  simpa [sourceRule, arithmeticSourceStart, encodeSourceOperation_eq,
    sourceInitialBindings, integerAtom, ExactArithmeticNTT.a, a] using
    (match_evaluateRule (sourceOperationName operation)
      (sourceRelationName operation) (integerAtom first)
      (integerAtom second))

private theorem sourceQuery_matches
    (operation : CoreOp) (first second : Int) :
    [("outcome", sourceOutcomePattern operation first second)] ∈
      matchRelationArgs (sourceInitialBindings first second)
        [.fvar "first", .fvar "second", .fvar "outcome"]
        [integerAtom first, integerAtom second,
          sourceOutcomePattern operation first second] := by
  simp [matchRelationArgs, matchRelationArgument, sourceInitialBindings,
    Bindings.lookup, mergeBindings]

private theorem sourcePremise_member
    (operation : CoreOp) (first second : Int) :
    sourceFinalBindings operation first second ∈
      applyPremisesWithEnv
        (arithmeticSourceReferenceEnv operation first second)
        exactArithmetic (sourceRule operation).premises
        (sourceInitialBindings first second) := by
  have queryMember :
      sourceFinalBindings operation first second ∈
        premiseStepWithEnv
          (arithmeticSourceReferenceEnv operation first second)
          exactArithmetic (sourceInitialBindings first second)
          (.relationQuery (sourceRelationName operation)
            [.fvar "first", .fvar "second", .fvar "outcome"]) := by
    apply premiseStepWithEnv_relationQuery_of_env_tuple
      (tuple := [integerAtom first, integerAtom second,
        sourceOutcomePattern operation first second])
      (extension := [("outcome",
        sourceOutcomePattern operation first second)])
    · simp [arithmeticSourceReferenceEnv, sourceInitialBindings,
        sourceRelationName, sourceOutcomePattern, integerAtom,
        applyBindings]
    · exact sourceQuery_matches operation first second
    · simp [sourceFinalBindings, sourceInitialBindings, mergeBindings]
  rw [sourceRule_premises]
  simpa [applyPremisesWithEnv] using queryMember

private theorem sourceRule_result
    (operation : CoreOp) (first second : Int) :
    applyBindingsForRule exactArithmetic (sourceRule operation)
        (sourceFinalBindings operation first second) =
      arithmeticSourceDone operation first second := by
  cases operation <;>
    simp [sourceRule, evaluateRule, sourceFinalBindings,
      sourceInitialBindings, arithmeticSourceDone,
      applyBindingsForRule_eq_syntactic, applyBindings,
      sourceOutcomePattern, integerAtom, ExactArithmeticNTT.a,
      ExactArithmeticNTT.v, a]

/-- Every exact-arithmetic request takes the one authored source rule to its
mathematical outcome.  This is a universal OSLF step, not a finite-vector
normalization claim. -/
theorem exactArithmetic_reaches_declared_done
    (operation : CoreOp) (first second : Int) :
    langReducesUsing (arithmeticSourceReferenceEnv operation first second)
      exactArithmetic (arithmeticSourceStart operation first second)
      (arithmeticSourceDone operation first second) := by
  apply step_of_rule
    (rule := sourceRule operation)
    (initialBindings := sourceInitialBindings first second)
    (finalBindings := sourceFinalBindings operation first second)
  · exact sourceRule_member operation
  · rw [match_sourceRule]
    simp
  · rw [sourceRule_premises]
    exact .relationQuery .nil
  · exact sourcePremise_member operation first second
  · exact sourceRule_result operation first second

/-- The universal source step and the universal target trace meet at the same
mathematical arithmetic observation.  The target retains its independently
authored ordered receipt in addition to that shared observation. -/
theorem exactArithmetic_to_ExternalCall_preserves_observation
    (operation : CoreOp) (first second : Int) :
    langReducesUsing (arithmeticSourceReferenceEnv operation first second)
        exactArithmetic (arithmeticSourceStart operation first second)
        (arithmeticSourceDone operation first second) ∧
      Relation.ReflTransGen
        (langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
          externalCallLanguage)
        (compiledExternalCallStart operation first second)
        (compiledExternalCallDone operation first second) ∧
      compiledExternalCallOutcome operation first second =
        match coreSem operation first second with
        | .declined => a "external-call:outcome-declined"
        | .val value =>
            a "external-call:outcome-value" [exactIntegerValue value] := by
  exact ⟨exactArithmetic_reaches_declared_done operation first second,
    compiledExternalCall_reaches_declared_done operation first second,
    compiledExternalCallOutcome_commutes operation first second⟩

/-- Request-local two-sided compiler square at the declared completion
observation.  The source owns the mathematical result; the target must reach
that result, cannot reach a different result, and must retain its exact
ordered receipt. -/
theorem exactArithmetic_to_ExternalCall_hosts_completion
    (operation : CoreOp) (first second : Int) :
    langReducesUsing (arithmeticSourceReferenceEnv operation first second)
        exactArithmetic (arithmeticSourceStart operation first second)
        (arithmeticSourceDone operation first second) ∧
      Relation.ReflTransGen
        (langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
          externalCallLanguage)
        (compiledExternalCallStart operation first second)
        (compiledExternalCallDone operation first second) ∧
      ∀ outcome receipt,
        Relation.ReflTransGen
          (langReducesUsing (arithmeticExternalCallReferenceEnv operation first second)
            externalCallLanguage)
          (compiledExternalCallStart operation first second) (halted outcome receipt) →
        outcome =
            (match coreSem operation first second with
            | .declined => a "external-call:outcome-declined"
            | .val value =>
                a "external-call:outcome-value" [exactIntegerValue value]) ∧
          receipt = compiledExternalCallReceipt operation first second := by
  refine ⟨exactArithmetic_reaches_declared_done operation first second,
    compiledExternalCall_reaches_declared_done operation first second, ?_⟩
  intro outcome receipt path
  have reflected := compiledExternalCall_halted_no_invention
    operation first second outcome receipt path
  exact ⟨reflected.1.trans
    (compiledExternalCallOutcome_commutes operation first second), reflected.2⟩

#print axioms compiler_vocabulary_is_authored
#print axioms compiledExternalCall_halted_no_invention
#print axioms exactArithmetic_to_ExternalCall_preserves_observation
#print axioms exactArithmetic_to_ExternalCall_hosts_completion

end Mettapedia.GSLT.LanguageDef.ExactArithmeticToExternalCall
