import Mettapedia.Machines.CMemory.ScalarBytes
import Mettapedia.Machines.CMemory.DependencyCapacityReads

/-!
# Retained local C control with typed block-memory effects

The source fragment combines the shared UInt32 reader, pure local-loop
executor, typed loads/stores and a declared realloc service. It executes the
supplied expressions and statements; unsupported syntax reaches undefined
rather than a substituted program. Local declaration scopes are restored.

Administrative fuel exhaustion, falling off the function and a returned
Boolean are distinct. This interpretation covers typed cells and explicit
byte requests, not native object layout or the whole C memory model.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.LocalMemory

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open ScalarBytes

structure Context where
  values : ScalarRead.Environment Ptr
  types : Types

structure Services where
  abi : ABI
  allocatorName : Name

def Context.bind (context : Context) (type : CType) (name : Name)
    (value : ScalarRead.Value Ptr) : Context :=
  ⟨Function.update context.values name (some value),
    Function.update context.types name (some type)⟩

def pointers (context : Context) : DependencyCapacityReads.Pointers := fun name =>
  match context.values name with
  | some (.identity pointer) => pointer
  | _ => none

def words (context : Context) : DependencyCapacityReads.Words := fun name =>
  match context.values name with
  | some (.unsigned value) => some value
  | _ => none

def readWord (context : Context) (expression : CExpr) : CProg CVal UInt32 :=
  DependencyCapacityReads.readWord (pointers context) (words context) expression

/-- The service accepts byte requests only when they denote whole cells. -/
def readPointer (services : Services) (context : Context) : CExpr → CProg CVal (Option Ptr)
  | .identifier name => match context.values name with
      | some (.identity value) => pure value
      | _ => CProg.undefined
  | .null => pure none
  | .unary .dereference (.identifier name) => match pointers context name with
      | some pointer => CProg.loadPtr pointer
      | none => CProg.undefined
  | .call name [old, size] =>
      if name = services.allocatorName then do
        let pointer ← readPointer services context old
        match wide? services.abi context.types context.values size with
        | some bytes => match (cells? services.abi
              (bytes.value % services.abi.sizeWidth.modulus)) with
            | some extent => CProg.realloc pointer extent
            | none => CProg.undefined
        | none => CProg.undefined
      else CProg.undefined
  | _ => CProg.undefined

def readTruth (services : Services) (context : Context) : CExpr → CProg CVal Bool
  | .bool value => pure value
  | .binary .le left right => do
      let first ← readWord context left
      let second ← readWord context right
      pure (decide (first ≤ second))
  | .binary .gt left right => match
      wide? services.abi context.types context.values left,
      wide? services.abi context.types context.values right with
      | some first, some second => pure (decide (second.value < first.value))
      | _, _ => CProg.undefined
  | .unary .not operand => do
      let pointer ← readPointer services context operand
      pure (!pointer.isSome)
  | .identifier name => match context.values name with
      | some value => match ScalarRead.truth? value with
          | some truth => pure truth
          | none => CProg.undefined
      | none => CProg.undefined
  | _ => CProg.undefined

def initialValue (services : Services) (context : Context) (type : CType)
    (expression : CExpr) : CProg CVal (ScalarRead.Value Ptr) :=
  if type = ⟨"uint32_t".toList, 0⟩ then
    readWord context expression >>= fun value => pure (.unsigned value)
  else if type = ⟨"bool".toList, 0⟩ then
    readTruth services context expression >>= fun value => pure (.boolean value)
  else if 0 < type.pointers then
    readPointer services context expression >>= fun value => pure (.identity value)
  else CProg.undefined

def store (services : Services) (context : Context) (target value : CExpr) : CProg CVal Unit :=
  match target with
  | .unary .dereference (.identifier name) =>
      match pointers context name, typeOf? context.types target with
      | some pointer, some type =>
          if type = ⟨"uint32_t".toList, 0⟩ then do
            let word ← readWord context value
            CProg.store pointer (.u32 word)
          else if 0 < type.pointers then do
            let object ← readPointer services context value
            CProg.store pointer (.ptr object)
          else CProg.undefined
      | _, _ => CProg.undefined
  | _ => CProg.undefined

inductive Flow where
  | next (context : Context)
  | returned (value : Bool)
  | exhausted

def restore (context : Context) (name : Name) : Flow → Flow
  | .next updated => .next ⟨Function.update updated.values name (context.values name),
      Function.update updated.types name (context.types name)⟩
  | other => other

/-- A supplied while body is handled by the existing pure typed local service.
Memory effects inside a loop body remain outside that service's admitted
fragment; they cannot silently become pure local assignments. -/
def execute (services : Services) (loopFuel : Nat) :
    Nat → Context → List CStatement → CProg CVal Flow
  | 0, _, _ => pure .exhausted
  | _ + 1, context, [] => pure (.next context)
  | fuel + 1, context, statement :: rest => match statement with
      | .declare type name initial => do
          let value ← initialValue services context type initial
          let result ← execute services loopFuel fuel (context.bind type name value) rest
          pure (restore context name result)
      | .branch condition yes no => do
          let test ← readTruth services context condition
          let result ← execute services loopFuel fuel context (if test then yes else no)
          match result with
          | .next updated => execute services loopFuel fuel updated rest
          | other => pure other
      | .whileLoop condition body =>
          match LocalLoop.whileStatement (fun _ _ => none) 4 loopFuel context.values
              (.whileLoop condition body) with
          | some (.finished (some (.next values))) =>
              execute services loopFuel fuel ⟨values, context.types⟩ rest
          | some (.finished (some (.returned _ (some (.boolean value))))) => pure (.returned value)
          | some .exhausted => pure .exhausted
          | _ => CProg.undefined
      | .assign target value => do
          store services context target value
          execute services loopFuel fuel context rest
      | .return (some value) => do
          let result ← readTruth services context value
          pure (.returned result)
      | _ => CProg.undefined

inductive Result where
  | completed (value : Bool)
  | missingReturn
  | exhausted
  deriving DecidableEq, Repr

def result : Flow → Result
  | .returned value => .completed value
  | .next _ => .missingReturn
  | .exhausted => .exhausted

/-- Argument values bind to the parsed parameter names and types in order. -/
def argumentFits (type : CType) : ScalarRead.Value Ptr → Bool
  | .signed _ => false
  | .unsigned _ => type == ⟨"uint32_t".toList, 0⟩
  | .unsigned64 _ => false
  | .boolean _ => type == ⟨"bool".toList, 0⟩
  | .identity _ => decide (0 < type.pointers)
  | .identities _ => false
  | .wordRecord _ => false

def arguments? (base : Context) : List CDeclaratorParameter →
    List (ScalarRead.Value Ptr) → Option Context
  | [], [] => some base
  | parameter :: parameters, value :: values =>
      if argumentFits parameter.type.unqualified value then
        arguments? (base.bind parameter.type.unqualified parameter.name value) parameters values
      else none
  | _, _ => none

def runFunction? (services : Services) (base : Context)
    (arguments : List (ScalarRead.Value Ptr)) (bodyFuel loopFuel : Nat)
    (function : CDeclaratorFunction) : Option (CProg CVal Result) := do
  if function.result ≠ ⟨"bool".toList, 0⟩ then none else do
    let context ← arguments? base function.parameters arguments
    some (execute services loopFuel bodyFuel context function.body >>= fun flow => pure (result flow))

def runText? (names : TypeNames) (text : String) (services : Services) (base : Context)
    (arguments : List (ScalarRead.Value Ptr)) (bodyFuel loopFuel : Nat) :
    Option (CProg CVal Result) :=
  (declaratorFunctionText? names text.toList).bind
    (runFunction? services base arguments bodyFuel loopFuel)

namespace Controls

def noBindings : Context := ⟨fun _ => none, fun _ => none⟩
def sampleServices : Services := ⟨ScalarBytes.Controls.abi64, "resize".toList⟩

theorem actual_return_is_not_replaced :
    execute sampleServices 32 4 noBindings [.return (some (.bool false))] =
      pure (.returned false) := rfl

theorem falling_off_is_not_success :
    (execute sampleServices 32 1 noBindings [] >>= fun flow => pure (result flow)) =
      pure .missingReturn := rfl

theorem proof_fuel_is_not_c_failure :
    (execute sampleServices 32 0 noBindings [.return (some (.bool false))] >>=
      fun flow => pure (result flow)) =
      pure .exhausted := rfl

theorem empty_false_branch_does_not_execute_invalid_then :
    execute sampleServices 32 4 noBindings
      [.branch (.bool false) [.effect (.identifier "absent".toList)] [],
       .return (some (.bool true))] = pure (.returned true) := rfl

theorem unknown_allocator_not_called :
    readPointer sampleServices noBindings (.call "other".toList
      [.null, .sizeOf ⟨"Space".toList, 1⟩]) = CProg.undefined := rfl

/-- This UInt32 allocator profile does not silently admit a signed argument. -/
theorem signed_argument_is_not_reinterpreted (value : Int32) :
    argumentFits ⟨"uint32_t".toList, 0⟩ (.signed value) = false := rfl

theorem wide_argument_is_not_narrowed (value : UInt64) :
    argumentFits ⟨"uint32_t".toList, 0⟩ (.unsigned64 value) = false := rfl

theorem record_argument_is_not_a_pointer (fields : List (Name × UInt64)) :
    argumentFits ⟨"Space".toList, 1⟩ (.wordRecord fields) = false := rfl

theorem known_allocator_uses_actual_request :
    readPointer sampleServices noBindings (.call "resize".toList
      [.null, .sizeOf ⟨"Space".toList, 1⟩]) = CProg.realloc none 1 := rfl

theorem statement_store_uses_actual_target (left right : Ptr) :
    store sampleServices
      ((noBindings.bind ⟨"uint32_t".toList, 1⟩ "a".toList (.identity (some left))).bind
        ⟨"uint32_t".toList, 1⟩ "b".toList (.identity (some right)))
      (.unary .dereference (.identifier "b".toList)) (.unsignedInteger 17) =
      CProg.store right (.u32 17) := rfl

theorem local_declaration_restores_previous_binding (previous current : UInt32) :
    execute sampleServices 32 4
      (noBindings.bind ⟨"uint32_t".toList, 0⟩ "x".toList (.unsigned previous))
      [.declare ⟨"uint32_t".toList, 0⟩ "x".toList (.unsignedInteger current.toNat)] =
      pure (.next (noBindings.bind ⟨"uint32_t".toList, 0⟩ "x".toList (.unsigned previous))) := by
  simp only [execute, initialValue, readWord, DependencyCapacityReads.readWord,
    current.toNat_lt, if_true, UInt32.ofNat_toNat, Prog.pure_eq, Prog.ret_bind,
    Prog.bind_eq, Context.bind, restore]
  simp only [Function.update_idem, Function.update_self]

end Controls

end Mettapedia.Machines.CMemory.LocalMemory
