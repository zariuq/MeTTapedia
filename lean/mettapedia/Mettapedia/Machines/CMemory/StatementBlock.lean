import Mettapedia.Machines.CMemory.ReadBlock
import Mettapedia.Machines.CMemory.Array
import Mettapedia.Machines.CMemory.ScalarBytes
import Mettapedia.GSLT.LanguageDef.NativeOpsCLocalBlock

/-!
# Scoped physical blocks with an assignment service

The block retains declarations, selected branches, read loops, break and
return, while its assignment service may execute physical stores. Flow,
restoration, scalar conversion and flat counted reads reuse the existing
services. Specializing assignments to the read service is proved to recover
the previously checked block interpreter.

Named expression/effect and automatic-storage providers reuse this flow.
Their contracts must justify calls and the lifetime of temporary arrays.
The default outer counted operation retains the existing read-only profile.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.StatementBlock

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open ReadExpressions
open ReadBlock (Result Flow resume restore declaredValue)

abbrev Assignment := Layout → Environment → CStatement → CProg CVal Environment
abbrev Effect := Layout → Environment → CExpr → CProg CVal Unit
abbrev ArrayBinder := Layout → Environment → CType → Name → Option CExpr → List CExpr →
  (Environment → CProg CVal Result) → CProg CVal Result
abbrev Reader := Layout → Environment → CExpr → CProg CVal CVal

/-- The region supplies already owned automatic cells and remains responsible
for their extent, freshness and lifetime through every returned flow. It is
not an allocator with an invented nullable/failure result. -/
abbrev AutomaticRegion (Context : Type := Environment) :=
  Name → Nat → (Ptr → CProg CVal (Result Context)) → CProg CVal (Result Context)

namespace AutomaticRegion

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC (Name)
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open ReadExpressions ReadBlock

/-- An entry/body/exit implementation over the existing operation tree.
Entry and exit are supplied storage-lifetime services, not heap allocations
invented for automatic storage. Exit runs after every normally returned flow.
Undefined operations have no returned flow and are not repaired here. -/
def bracket {Context : Type} (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit) : AutomaticRegion Context :=
  fun name extent body => do
    let address ← enter name extent
    let result ← body address
    leave name address extent
    pure result

/-- Pure readout fusion retains the entire operation tree. A region which
inspects its returned flow need not have this property. -/
def PureReadoutLaw {Context : Type} (region : AutomaticRegion Context) : Prop :=
  ∀ (name : Name) (extent : Nat) (body : Ptr → CProg CVal (Result Context))
    (readout : Result Context → Result Context),
    (region name extent body >>= fun result => pure (readout result)) =
      region name extent (fun address => body address >>= fun result => pure (readout result))

theorem bracket_pure_readout {Context : Type} (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit) :
    PureReadoutLaw (bracket (Context := Context) enter leave) := by
  intro name extent body readout
  simp only [bracket, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]

theorem bracket_retains_entry_body_exit {Context : Type} (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit) (name : Name) (extent : Nat)
    (body : Ptr → CProg CVal (Result Context)) :
    bracket enter leave name extent body =
      (enter name extent >>= fun address => body address >>= fun result =>
        leave name address extent >>= fun _ => pure result) := rfl

theorem bracket_return_keeps_exit (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit) (name : Name) (extent : Nat)
    (environment : ReadExpressions.Environment) (value : Option CVal) :
    bracket enter leave name extent (fun _ => pure (.finished (.returned environment value))) =
      (enter name extent >>= fun address => leave name address extent >>= fun _ =>
        pure (.finished (.returned environment value))) := by
  simp only [bracket, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

theorem bracket_break_keeps_exit (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit) (name : Name) (extent : Nat)
    (environment : ReadExpressions.Environment) :
    bracket enter leave name extent (fun _ => pure (.finished (.broken environment))) =
      (enter name extent >>= fun address => leave name address extent >>= fun _ =>
        pure (.finished (.broken environment))) := by
  simp only [bracket, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

theorem bracket_undefined_does_not_invent_exit {Context : Type} (enter : Name → Nat → CProg CVal Ptr)
    (leave : Name → Ptr → Nat → CProg CVal Unit) (name : Name) (extent : Nat) :
    bracket (Context := Context) enter leave name extent (fun _ => CProg.undefined) =
      (enter name extent >>= fun _ => CProg.undefined) := by
  unfold bracket
  congr 1
  funext address
  exact undefined_bind _


/-- A normal lexical exit retains cleanup before the same completed flow.
Statement-proof exhaustion is not a C scope exit, and cannot manufacture a
cleanup callback. Nonlocal unwinding requires its own provider contract. -/
def normalExit {Context : Type} (cleanup : Flow Context → CProg CVal Unit) :
    Result Context → CProg CVal (Result Context)
  | .finished flow => cleanup flow >>= fun _ => pure (.finished flow)
  | .exhausted => pure .exhausted

/-- Decorate the existing automatic region, preserving its entry and physical
exit. The callback runs inside the live region, before that region returns and
before declaration restoration. It may observe the complete returned flow. -/
def withCleanup {Context : Type} (region : AutomaticRegion Context)
    (cleanup : Name → Ptr → Nat → Flow Context → CProg CVal Unit) :
    AutomaticRegion Context := fun name extent body =>
  region name extent (fun address => body address >>= normalExit (cleanup name address extent))

theorem completed_exit_keeps_cleanup {Context : Type}
    (cleanup : Flow Context → CProg CVal Unit) (flow : Flow Context) :
    normalExit cleanup (.finished flow) =
      (cleanup flow >>= fun _ => pure (.finished flow)) := rfl

theorem exhaustion_does_not_run_cleanup {Context : Type}
    (cleanup : Flow Context → CProg CVal Unit) :
    normalExit cleanup .exhausted = pure .exhausted := rfl

/-- Cleanup composition preserves the flow and the exact callback order.
The nested declaration's callback precedes the enclosing declaration's. -/
theorem nested_completed_cleanup_order {Context : Type}
    (inner outer : Flow Context → CProg CVal Unit) (flow : Flow Context) :
    (normalExit inner (.finished flow) >>= normalExit outer) =
      (inner flow >>= fun _ => outer flow >>= fun _ => pure (.finished flow)) := by
  simp only [normalExit, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]

theorem nested_exhaustion_does_not_run_cleanup {Context : Type}
    (inner outer : Flow Context → CProg CVal Unit) :
    (normalExit inner .exhausted >>= normalExit outer) = pure .exhausted := by
  simp only [normalExit, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

/-- Undefined body execution retains the automatic region; it does not invent
a normally returned flow or an exit callback. -/
theorem undefined_body_does_not_invent_cleanup {Context : Type}
    (region : AutomaticRegion Context)
    (cleanup : Name → Ptr → Nat → Flow Context → CProg CVal Unit)
    (name : Name) (extent : Nat) :
    withCleanup region cleanup name extent (fun _ => CProg.undefined) =
      region name extent (fun _ => CProg.undefined) := by
  unfold withCleanup
  congr 1
  funext address
  exact undefined_bind _

/-- The same returned context reaches cleanup before its lexical restoration.
This equality does not license moving an inspecting callback after restoration. -/
theorem cleanup_keeps_live_region_and_flow {Context : Type}
    (region : AutomaticRegion Context)
    (cleanup : Name → Ptr → Nat → Flow Context → CProg CVal Unit)
    (name : Name) (extent : Nat) (body : Ptr → CProg CVal (Result Context)) :
    withCleanup region cleanup name extent body =
      region name extent (fun address => body address >>= fun result =>
        match result with
        | .finished flow => cleanup name address extent flow >>= fun _ => pure (.finished flow)
        | .exhausted => pure .exhausted) := rfl


namespace Controls

/-- An inspecting handler can distinguish a local binding before restoration.
Its explicit refusal witnesses why readout fusion needs a proved law. -/
def inspectedName : Name := "temporary".toList
def inspectedEnvironment : ReadExpressions.Environment := fun _ => none

def inspecting : AutomaticRegion := fun _ _ body => do
  let result ← body ⟨1, 0⟩
  match result with
  | .finished (.returned environment _) =>
      if environment inspectedName = some (.bool true) then pure .exhausted
      else pure result
  | _ => pure result

def inspectedBody (_ : Ptr) : CProg CVal Result :=
  pure (.finished (.returned
    (Function.update inspectedEnvironment inspectedName (some (.bool true)))
    (some (.bool false))))

theorem inspected_flow_before_restoration :
    (inspecting inspectedName 1 inspectedBody >>= fun result =>
      pure (restore inspectedName none result)) = pure .exhausted := by rfl

theorem inspected_flow_after_restoration :
    inspecting inspectedName 1 (fun address => inspectedBody address >>= fun result =>
      pure (restore inspectedName none result)) =
        pure (.finished (.returned inspectedEnvironment (some (.bool false)))) := by
  simp only [inspecting, inspectedBody, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  have restored := returned_declaration_restores_scope inspectedEnvironment inspectedName
    (some (.bool true)) (some (.bool false))
  change restore inspectedName none
    (.finished (.returned (Function.update inspectedEnvironment inspectedName (some (.bool true)))
      (some (.bool false)))) = .finished (.returned inspectedEnvironment (some (.bool false))) at restored
  rw [restored]
  rfl

theorem inspecting_region_is_not_pure_readout : ¬ PureReadoutLaw inspecting := by
  intro lawful
  have wrong := lawful inspectedName 1 inspectedBody (restore inspectedName none)
  rw [inspected_flow_before_restoration, inspected_flow_after_restoration] at wrong
  cases wrong

end Controls

end AutomaticRegion

/-- Object-pointer declarations retain the actual nullable pointer. The caller
admits the pointee type and native representation separately; scalar defaults
reuse the existing declaration conversion. -/
def objectInitialValue (type : CType) (value : CVal) : CProg CVal CVal :=
  if 0 < type.pointers then pointer value >>= fun address => pure (.ptr address)
  else if type = ⟨"uint64_t".toList, 0⟩ then
    match value with
    | .u64 word => pure (.u64 word)
    | .u32 word => pure (.u64 (UInt64.ofNat word.toNat))
    | _ => CProg.undefined
  else declaredValue type value

/-- An inferred-size array evaluates every initializer, checks its declared
element conversion and initializes its supplied physical cells before entering
the actual continuation. Explicit bounds are outside this profile. -/
def arrayBinding (read : Reader) (region : AutomaticRegion) : ArrayBinder :=
  fun layout environment type name extent initializers continuation =>
    match extent with
    | none => do
        let values ← initializers.mapM (fun initializer => do
          let value ← read layout environment initializer
          objectInitialValue type value)
        region name values.length fun address => do
          CProg.initializeCells address values
          continuation (Function.update environment name (some (.ptr (some address))))
    | some _ => CProg.undefined

/-- This profile reads the owner then the right-hand expression. Its C source
correspondence must establish those operands commute or satisfy that order.
It writes the descriptor's scalar cell and preserves the local environment. -/
def fieldAssignment (read : Reader) : Assignment := fun layout environment statement =>
  match statement with
  | .assign (.field owner name true) rhs => do
      let actualOwner ← read layout environment owner
      let value ← read layout environment rhs
      storeField layout actualOwner name value
      pure environment
  | _ => CProg.undefined

theorem nullable_object_declaration_retains_value (type : CType) (value : Option Ptr)
    (object : 0 < type.pointers) :
    objectInitialValue type (.ptr value) = pure (.ptr value) := by
  simp only [objectInitialValue, object, ↓reduceIte, pointer, Prog.pure_eq,
    Prog.bind_eq, Prog.ret_bind]

theorem field_assignment_retains_actual_operands (read : Reader) (layout : Layout)
    (environment : Environment) (owner rhs : CExpr) (name : Name) :
    fieldAssignment read layout environment (.assign (.field owner name true) rhs) =
      (read layout environment owner >>= fun actualOwner =>
        read layout environment rhs >>= fun value =>
          storeField layout actualOwner name value >>= fun _ => pure environment) := rfl

/-- Additional operations use the same scoped block and flow. Their providers
must separately establish expression, declaration, effect and automatic-storage
contracts. The default retains the existing read-only fragment. -/
structure Services where
  read : Reader := expression
  initialValue : CType → CVal → CProg CVal CVal := declaredValue
  effect : Effect := fun _ _ _ => CProg.undefined
  array : ArrayBinder := fun _ _ _ _ _ _ _ => CProg.undefined
  counted : Layout → Nat → Environment → CStatement → CProg CVal ReadLoops.Result := ReadLoops.counted
  uninitialized : Layout → Environment → CType → Name →
    (Environment → CProg CVal Result) → CProg CVal Result :=
    fun _ _ _ _ _ => CProg.undefined


/-- A typed context can distinguish rvalues, object places and uninitialized
bindings without putting a record address in the scalar-value environment.
Declaration providers retain entry, continuation, exit and scope restoration;
they do not gain permission to reorder any of these operations. -/
structure ScopedServices (Context : Type) where
  read : Layout → Context → CExpr → CProg CVal CVal
  declaration : Layout → Context → CType → Name → Option CExpr →
    (Context → CProg CVal (Result Context)) → CProg CVal (Result Context)
  declarationCleanup : Layout → Context → CType → Name → Option CExpr → Name →
    (Context → CProg CVal (Result Context)) → CProg CVal (Result Context) :=
    fun _ _ _ _ _ _ _ => CProg.undefined
  array : Layout → Context → CType → Name → Option CExpr → List CExpr →
    (Context → CProg CVal (Result Context)) → CProg CVal (Result Context)
  effect : Layout → Context → CExpr → CProg CVal Unit
  assignment : Layout → Context → CStatement → CProg CVal Context
  counted : Layout → Nat → Context → CStatement → CProg CVal (Result Context)
  nestedBlocks : Bool := false
  selectSwitch : Layout → Context → CExpr → List (CExpr × List CStatement) →
    List CStatement → CProg CVal (List CStatement) := fun _ _ _ _ _ => CProg.undefined

/-- The switch owns its break. It retains return and exhaustion and passes
all current context information to the unchanged outer continuation. -/
def resumeSwitch {Context : Type}
    (continuation : Context → CProg CVal (Result Context)) :
    Result Context → CProg CVal (Result Context)
  | .finished (.broken context) => continuation context
  | result => resume continuation result

/-- The selected-arm profile reuses the retained pure local-control planner.
Case constants come from an admitted static inventory, not physical reads or
callback replies at dispatch time. Integer widths and conversions remain those
of the existing scalar profile. Pointer and Boolean selectors are not admitted. -/
def integerSwitchBody (constants : ScalarRead.Environment Ptr) (selector : CVal)
    (cases : List (CExpr × List CStatement)) (otherwise : List CStatement) :
    CProg CVal (List CStatement) :=
  match selector with
  | .i32 _ | .u32 _ | .u64 _ =>
      resolved (LocalBlock.switchBody? (fun _ _ => none) constants (scalar selector) cases otherwise)
  | _ => CProg.undefined

theorem switch_break_enters_outer_continuation {Context : Type}
    (continuation : Context → CProg CVal (Result Context)) (context : Context) :
    resumeSwitch continuation (.finished (.broken context)) = continuation context := rfl

theorem switch_return_bypasses_outer_continuation {Context : Type}
    (continuation : Context → CProg CVal (Result Context))
    (context : Context) (value : Option CVal) :
    resumeSwitch continuation (.finished (.returned context value)) =
      pure (.finished (.returned context value)) := rfl

theorem switch_exhaustion_remains_incomplete {Context : Type}
    (continuation : Context → CProg CVal (Result Context)) :
    resumeSwitch continuation .exhausted = pure .exhausted := rfl

def executeScopedWith {Context : Type} (services : ScopedServices Context)
    (layout : Layout) (loopFuel fuel : Nat) (environment : Context)
    (body : List CStatement) : CProg CVal (Result Context) :=
  match body with
  | [] => pure (.finished (.next environment))
  | statement :: rest => match fuel with
    | 0 => pure .exhausted
    | fuel + 1 => match statement with
      | .empty => executeScopedWith services layout loopFuel fuel environment rest
      | .declare type name rhs =>
          services.declaration layout environment type name (some rhs)
            (fun updated => executeScopedWith services layout loopFuel fuel updated rest)
      | .declareCleanup type name initial cleanup =>
          services.declarationCleanup layout environment type name initial cleanup
            (fun updated => executeScopedWith services layout loopFuel fuel updated rest)
      | .declareUninitialized type name =>
          services.declaration layout environment type name none
            (fun updated => executeScopedWith services layout loopFuel fuel updated rest)
      | .declareArray type name extent initializers =>
          services.array layout environment type name extent initializers
            (fun updated => executeScopedWith services layout loopFuel fuel updated rest)
      | .effect operand => do
          services.effect layout environment operand
          executeScopedWith services layout loopFuel fuel environment rest
      | .assign _ _ | .compoundAssign _ _ _ => do
          let updated ← services.assignment layout environment statement
          executeScopedWith services layout loopFuel fuel updated rest
      | .branch condition yes no => do
          let actual ← services.read layout environment condition
          let selected ← truth actual
          let result ← executeScopedWith services layout loopFuel fuel environment (if selected then yes else no)
          resume (fun updated => executeScopedWith services layout loopFuel fuel updated rest) result
      | .block selected =>
          if services.nestedBlocks then do
            let result ← executeScopedWith services layout loopFuel fuel environment selected
            resume (fun updated => executeScopedWith services layout loopFuel fuel updated rest) result
          else CProg.undefined
      | .switch selector cases otherwise => do
          let selected ← services.selectSwitch layout environment selector cases otherwise
          let result ← executeScopedWith services layout loopFuel fuel environment selected
          resumeSwitch (fun updated => executeScopedWith services layout loopFuel fuel updated rest) result
      | .forLoop _ _ _ _ _ _ => do
          let result ← services.counted layout loopFuel environment statement
          resume (fun updated => executeScopedWith services layout loopFuel fuel updated rest) result
      | .break => pure (.finished (.broken environment))
      | .return none => pure (.finished (.returned environment none))
      | .return (some rhs) => do
          let actual ← services.read layout environment rhs
          pure (.finished (.returned environment (some actual)))
      | _ => CProg.undefined

/-- A scalar assignment composes with its remaining statements without
expanding the continuation or duplicating its operation tree. -/
theorem scoped_assignment_keeps_continuation {Context : Type}
    (services : ScopedServices Context) (layout : Layout) (loopFuel fuel : Nat)
    (context : Context) (target rhs : CExpr) (rest : List CStatement) :
    executeScopedWith services layout loopFuel (fuel + 1) context (.assign target rhs :: rest) =
      (services.assignment layout context (.assign target rhs) >>= fun updated =>
        executeScopedWith services layout loopFuel fuel updated rest) := by
  rw [executeScopedWith.eq_def]

/-- An initialized declaration exposes only its own scoped service; the
remaining statements stay in the original complete continuation. -/
theorem scoped_initialized_declaration_keeps_continuation {Context : Type}
    (services : ScopedServices Context) (layout : Layout) (loopFuel fuel : Nat)
    (context : Context) (type : CType) (name : Name) (operand : CExpr) (rest : List CStatement) :
    executeScopedWith services layout loopFuel (fuel + 1) context (.declare type name operand :: rest) =
      services.declaration layout context type name (some operand)
        (fun updated => executeScopedWith services layout loopFuel fuel updated rest) := by
  rw [executeScopedWith.eq_def]

/-- A discarded effect occurs before the same retained continuation. The law
permits neither effect erasure nor a change in its observation time. -/
theorem scoped_effect_keeps_continuation {Context : Type}
    (services : ScopedServices Context) (layout : Layout) (loopFuel fuel : Nat)
    (context : Context) (operand : CExpr) (rest : List CStatement) :
    executeScopedWith services layout loopFuel (fuel + 1) context (.effect operand :: rest) =
      (services.effect layout context operand >>= fun _ =>
        executeScopedWith services layout loopFuel fuel context rest) := by
  rw [executeScopedWith.eq_def]

/-- The syntax's callback remains part of the same scoped declaration service;
it cannot become an ordinary declaration by erasing the attribute. -/
theorem scoped_cleanup_declaration_retains_provider {Context : Type}
    (services : ScopedServices Context) (layout : Layout) (loopFuel fuel : Nat)
    (context : Context) (type : CType) (name callback : Name) (initial : Option CExpr)
    (rest : List CStatement) :
    executeScopedWith services layout loopFuel (fuel + 1) context
      (.declareCleanup type name initial callback :: rest) =
        services.declarationCleanup layout context type name initial callback
          (fun updated => executeScopedWith services layout loopFuel fuel updated rest) := by
  rw [executeScopedWith.eq_def]

/-- Switch selection retains the current reader state and complete arm plan.
Only the switch handler consumes a break; the outer continuation is unchanged. -/
theorem scoped_switch_keeps_selection_and_flow {Context : Type}
    (services : ScopedServices Context) (layout : Layout) (loopFuel fuel : Nat)
    (context : Context) (selector : CExpr) (cases : List (CExpr × List CStatement))
    (otherwise rest : List CStatement) :
    executeScopedWith services layout loopFuel (fuel + 1) context
      (.switch selector cases otherwise :: rest) =
      (services.selectSwitch layout context selector cases otherwise >>= fun selected =>
        executeScopedWith services layout loopFuel fuel context selected >>= fun result =>
          resumeSwitch (fun updated => executeScopedWith services layout loopFuel fuel updated rest) result) := by
  rw [executeScopedWith.eq_def]

/-- An admitted nested block keeps its own declaration extents and propagates
its complete returned flow before the outer statements continue. -/
theorem scoped_nested_block_keeps_flow {Context : Type}
    (services : ScopedServices Context) (layout : Layout) (loopFuel fuel : Nat)
    (context : Context) (selected rest : List CStatement)
    (admitted : services.nestedBlocks = true) :
    executeScopedWith services layout loopFuel (fuel + 1) context (.block selected :: rest) =
      (executeScopedWith services layout loopFuel fuel context selected >>= fun result =>
        resume (fun updated => executeScopedWith services layout loopFuel fuel updated rest) result) := by
  rw [executeScopedWith.eq_def]
  simp only [admitted, ↓reduceIte]

/-- A finite prefix of context-preserving assignments composes its retained
operations in source order. Each primitive realization is required separately;
the suffix, effects and suspended operation tree remain unchanged. -/
theorem scoped_assignment_prefix_keeps_operations {Context : Type}
    (services : ScopedServices Context) (layout : Layout) (loopFuel fuel : Nat)
    (context : Context) (assignments : List ((CExpr × CExpr) × CProg CVal Unit))
    (rest : List CStatement)
    (realizes : ∀ entry ∈ assignments,
      services.assignment layout context (.assign entry.1.1 entry.1.2) =
        (entry.2 >>= fun _ => pure context)) :
    executeScopedWith services layout loopFuel (fuel + assignments.length) context
      (assignments.map (fun entry => CStatement.assign entry.1.1 entry.1.2) ++ rest) =
      assignments.foldr (fun entry next => entry.2 >>= fun _ => next)
        (executeScopedWith services layout loopFuel fuel context rest) := by
  induction assignments with
  | nil => simp only [List.length_nil, Nat.add_zero, List.map_nil, List.nil_append, List.foldr_nil]
  | cons entry entries ih =>
      simp only [List.length_cons, Nat.add_succ, List.map_cons, List.cons_append, List.foldr_cons]
      rw [scoped_assignment_keeps_continuation, realizes entry (by simp only [List.mem_cons, true_or])]
      simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc]
      congr 1
      funext ignored
      exact ih (fun item member => realizes item (List.mem_cons_of_mem entry member))

/-- A shared parsed-function entry point retains the complete body action.
The absent-parse case is outside the admitted C fragment. Using one eliminator
lets source comparisons compose without re-evaluating a closed parser merely
to compare independently elaborated match expressions. -/
def executeParsedBody {ParameterSyntax Context : Type}
    (execute : List CStatement → CProg CVal (ReadBlock.Result Context))
    (parsed : Option (CFunctionSyntax ParameterSyntax)) : CProg CVal (ReadBlock.Result Context) :=
  parsed.elim CProg.undefined (fun function => execute function.body)

theorem execute_parsed_body_some {ParameterSyntax Context : Type}
    (execute : List CStatement → CProg CVal (ReadBlock.Result Context))
    (function : CFunctionSyntax ParameterSyntax) :
    executeParsedBody execute (some function) = execute function.body := rfl

theorem execute_parsed_body_none {ParameterSyntax Context : Type}
    (execute : List CStatement → CProg CVal (ReadBlock.Result Context)) :
    executeParsedBody execute (none : Option (CFunctionSyntax ParameterSyntax)) = CProg.undefined := rfl


namespace SwitchControls

def constants : ScalarRead.Environment Ptr := fun _ => none

theorem pointer_selector_cannot_choose_default (pointer : Option Ptr)
    (otherwise : List CStatement) :
    integerSwitchBody constants (.ptr pointer) [] otherwise = CProg.undefined := rfl

theorem boolean_selector_requires_its_own_promotion (flag : Bool)
    (otherwise : List CStatement) :
    integerSwitchBody constants (.bool flag) [] otherwise = CProg.undefined := rfl

theorem missing_constant_does_not_choose_default :
    integerSwitchBody constants (.u32 1) [(.identifier "missing".toList, [])]
      [.return (some (.bool true))] = CProg.undefined := rfl

theorem consecutive_labels_keep_one_body_occurrence :
    integerSwitchBody constants (.u32 1)
      [(.unsignedInteger 1, []), (.unsignedInteger 2, [.effect (.call "tick".toList [])])]
      [.return (some (.bool false))] =
      pure [.block [], .block [.effect (.call "tick".toList [])],
        .block [.return (some (.bool false))]] := rfl

theorem unknown_integer_selects_actual_default :
    integerSwitchBody constants (.u32 3)
      [(.unsignedInteger 1, [.return (some (.bool true))])]
      [.return (some (.bool false))] =
      pure [.block [.return (some (.bool false))]] := rfl

end SwitchControls

namespace ObjectBindings

/-- Local records have places, while local scalars have optional values.
An uninitialized scalar is still declared and shields an outer name. -/
inductive Binding where
  | scalar (type : CType) (value : Option CVal)
  | object (type : CType) (address : Ptr)
  deriving DecidableEq, Repr

abbrev Context := Name → Option Binding

def values (context : Context) : Environment := fun name =>
  match context name with
  | some (.scalar _ value) => value
  | _ => none

def declared (context : Context) : Name → Bool := fun name => (context name).isSome

def types (context : Context) (outside : ScalarBytes.Types) : ScalarBytes.Types := fun name =>
  match context name with
  | some (.scalar type _) | some (.object type _) => some type
  | none => outside name

def places (context : Context) (outside : Name → Option Ptr) : Name → Option Ptr := fun name =>
  match context name with
  | some (.object _ address) => some address
  | some (.scalar _ _) => none
  | none => outside name

/-- A by-value record call returns all its typed cells, not a borrowed
address or a scalar pointer masquerading as the record. The service must
justify its declared result type, field values, effects and dependencies. -/
structure RecordCall where
  resultType : CType
  invoke : List CVal → CProg CVal (List CVal)

/-- Native byte extents and logical cell extents are separate inputs. The
profile does not infer one from the other or assume a null-pointer encoding. -/
structure Profile where
  values : Calls
  locations : Locations
  outsideTypes : ScalarBytes.Types
  outsidePlaces : Name → Option Ptr
  fieldTypes : ScalarBytes.FieldTypes
  cellExtent : CType → Option Nat
  byteExtent : CType → Option Nat
  sizeWidth : ScalarBytes.SizeWidth
  recordFields : Option (CType → Layout) := none
  caseConstants : ScalarRead.Environment Ptr := fun _ => none
  recordCalls : Name → Option RecordCall := fun _ => none
  scalarAliases : CType → Option CType := fun _ => none

/-- Static field descriptors are indexed by the retained owner type. Arrow
removes its one pointer level; dot keeps its object type. No field offset is
selected by a value or by the field's spelling alone. -/
def fieldLayouts (profile : Profile) (context : Context) (layouts : CType → Layout)
    (owner : CExpr) (throughPointer : Bool) : Layout := fun name => do
  let type ← ScalarBytes.typeOf? (types context profile.outsideTypes) owner profile.fieldTypes
  let recordType ← if throughPointer then match type.pointers with
    | 0 => none
    | depth + 1 => some ⟨type.name, depth⟩
    else some type
  layouts recordType name

def size (profile : Profile) (context : Context) (operand : CExpr) : Option CVal := do
  let type ← match operand with
    | .sizeOf type => some type
    | .sizeOfExpr operand => ScalarBytes.typeOf? (types context profile.outsideTypes) operand profile.fieldTypes
    | _ => none
  let extent ← profile.byteExtent type
  if extent < profile.sizeWidth.modulus then
    some (match profile.sizeWidth with
      | .bits32 => .u32 (UInt32.ofNat extent)
      | .bits64 => .u64 (UInt64.ofNat extent))
  else none

def objects (profile : Profile) (context : Context) : ObjectReads where
  place := some (places context profile.outsidePlaces)
  size := size profile context
  fields := profile.recordFields.map (fieldLayouts profile context)

def read (profile : Profile) (layout : Layout) (context : Context) (operand : CExpr) :
    CProg CVal CVal :=
  expressionWithNames (localOrLocated (values context) (declared context) profile.locations)
    profile.values layout operand (objects profile context)

def place (profile : Profile) (layout : Layout) (context : Context) (operand : CExpr) :
    CProg CVal Ptr :=
  placeWithNames (localOrLocated (values context) (declared context) profile.locations)
    profile.values layout operand (objects profile context)

def restore (name : Name) (previous : Option Binding) (result : Result Context) : Result Context :=
  result.mapContext (fun context => Function.update context name previous)

/-- A scalar typedef is resolved by the supplied static inventory. Missing
aliases retain the established conversion; no spelling or stored value guesses
an aliasedType. Native typedef agreement remains a source obligation. -/
def scalarInitialValue (profile : Profile) (type : CType) (value : CVal) : CProg CVal CVal :=
  objectInitialValue ((profile.scalarAliases type).getD type) value

/-- Record-place initialization snapshots the entire source before writing.
A declared by-value call instead evaluates its actual arguments, executes the
call, checks the complete return extent, and initializes every destination
cell. Unknown calls, result types and incomplete returns reach undefined.
They are not repaired with zeroing or an invented address. The call's effects
remain before a failed return-extent check. -/
def initializeRecord (profile : Profile) (layout : Layout) (context : Context)
    (type : CType) (extent : Nat) (address : Ptr) (operand : CExpr) : CProg CVal Unit :=
  if ScalarBytes.typeOf? (types context profile.outsideTypes) operand profile.fieldTypes = some type then do
    let source ← place profile layout context operand
    CProg.copyCells source address extent
  else match operand with
    | .call name arguments => do
        let service ← resolved (profile.recordCalls name)
        if service.resultType = type then do
          let actual ← argumentsWithNames
            (localOrLocated (values context) (declared context) profile.locations)
            profile.values layout arguments (objects profile context)
          let fields ← service.invoke actual
          if fields.length = extent then CProg.initializeCells address fields
          else CProg.undefined
        else CProg.undefined
    | _ => CProg.undefined

/-- Record declarations enter supplied automatic storage. An initialized
record binds its new local place before resolving the initializer, checks the
same record type and copies every source cell before any destination write.
Uninitialized records are neither zeroed nor read. Scalar initializers use the
existing admitted profile. Every returned flow restores the previous binding after
the region returns, retaining the region's own inspection order. -/
def declaration (profile : Profile) (region : AutomaticRegion Context)
    (layout : Layout) (context : Context) (type : CType) (name : Name)
    (initial : Option CExpr) (continuation : Context → CProg CVal (Result Context)) :
    CProg CVal (Result Context) := do
  let result ← match profile.cellExtent type with
    | some extent => match initial with
        | none => region name extent (fun address =>
            continuation (Function.update context name (some (.object type address))))
        | some operand => region name extent fun address => do
            let updated := Function.update context name (some (.object type address))
            initializeRecord profile layout updated type extent address operand
            continuation updated
    | none => match initial with
        | none => continuation (Function.update context name (some (.scalar type none)))
        | some operand => do
            let actual ← read profile layout context operand
            let value ← scalarInitialValue profile type actual
            continuation (Function.update context name (some (.scalar type (some value))))
  pure (restore name (context name) result)

theorem returned_local_restores_previous_binding (context : Context) (name : Name)
    (binding : Binding) (value : Option CVal) :
    restore name (context name)
      (.finished (.returned (Function.update context name (some binding)) value)) =
        .finished (.returned context value) := by
  simp only [restore, Result.mapContext, Flow.mapContext,
    Function.update_idem, Function.update_eq_self]

theorem local_object_address_does_not_read_value (profile : Profile) (layout : Layout)
    (context : Context) (name : Name) (type : CType) (address : Ptr)
    (bound : context name = some (.object type address)) :
    read profile layout context (.unary .address (.identifier name)) =
      pure (.ptr (some address)) := by
  simp only [read, expressionWithNames.eq_def, objects, placeWithNames.eq_def,
    places, bound, Option.bind_some, resolved, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

theorem local_record_has_no_scalar_rvalue (profile : Profile) (layout : Layout)
    (context : Context) (name : Name) (type : CType) (address : Ptr)
    (bound : context name = some (.object type address)) :
    read profile layout context (.identifier name) = CProg.undefined := by
  simp only [read, expressionWithNames.eq_def, localOrLocated, values, declared,
    bound, Option.isSome_some, ↓reduceIte]

theorem local_uninitialized_scalar_shields_outer (profile : Profile) (layout : Layout)
    (context : Context) (name : Name) (type : CType)
    (bound : context name = some (.scalar type none)) :
    read profile layout context (.identifier name) = CProg.undefined := by
  simp only [read, expressionWithNames.eq_def, localOrLocated, values, declared,
    bound, Option.isSome_some, ↓reduceIte]

theorem declared_record_keeps_entry_and_continuation (profile : Profile)
    (region : AutomaticRegion Context) (layout : Layout) (context : Context)
    (type : CType) (name : Name) (extent : Nat)
    (record : profile.cellExtent type = some extent)
    (continuation : Context → CProg CVal (Result Context)) :
    declaration profile region layout context type name none continuation =
      (region name extent (fun address =>
        continuation (Function.update context name (some (.object type address)))) >>= fun result =>
        pure (restore name (context name) result)) := by
  simp only [declaration, record]

/-- A record initializer observes the newly introduced binding, not a
same-spelled outer object. The copy retains pointer references and complete
source-before-destination ordering; it does not clone reachable objects. -/
theorem initialized_record_keeps_scope_and_complete_copy (profile : Profile)
    (region : AutomaticRegion Context) (layout : Layout) (context : Context)
    (type : CType) (name : Name) (extent : Nat) (operand : CExpr)
    (record : profile.cellExtent type = some extent)
    (sourceType : ∀ address, ScalarBytes.typeOf?
      (types (Function.update context name (some (.object type address))) profile.outsideTypes)
      operand profile.fieldTypes = some type)
    (continuation : Context → CProg CVal (Result Context)) :
    declaration profile region layout context type name (some operand) continuation =
      (region name extent (fun address =>
        place profile layout (Function.update context name (some (.object type address))) operand >>=
          fun source => CProg.copyCells source address extent >>= fun _ =>
            continuation (Function.update context name (some (.object type address)))) >>= fun result =>
        pure (restore name (context name) result)) := by
  simp only [declaration, record]
  congr 1
  congr 1
  funext address
  simp only [initializeRecord, sourceType address, ↓reduceIte,
    Prog.bind_eq, Prog.bind_assoc]

/-- A missing or incompatible record type does not invent an initializer.
The automatic region still retains its entry and any inspection of undefined
body execution; this is not a fabricated normal refusal or a cleanup promise. -/
theorem incompatible_record_initializer_retains_undefined (profile : Profile)
    (region : AutomaticRegion Context) (layout : Layout) (context : Context)
    (type : CType) (name : Name) (extent : Nat) (operand : CExpr)
    (record : profile.cellExtent type = some extent)
    (sourceType : ∀ address, ScalarBytes.typeOf?
      (types (Function.update context name (some (.object type address))) profile.outsideTypes)
      operand profile.fieldTypes ≠ some type)
    (noCall : ∀ callee arguments, operand ≠ .call callee arguments)
    (continuation : Context → CProg CVal (Result Context)) :
    declaration profile region layout context type name (some operand) continuation =
      (region name extent (fun _ => CProg.undefined) >>= fun result =>
        pure (restore name (context name) result)) := by
  simp only [declaration, record]
  congr 1
  congr 1
  funext address
  simp only [initializeRecord, sourceType address, ↓reduceIte]
  cases operand <;> first
    | exact False.elim (noCall _ _ rfl)
    | exact undefined_bind _

/-- Resolving the initializer under the new inventory prevents accidental
capture of an outer record with the same printed identifier. The memory
provider must separately reject reads of uninitialized automatic cells. -/
theorem record_initializer_name_is_local (profile : Profile) (layout : Layout)
    (context : Context) (type : CType) (name : Name) (address : Ptr) :
    place profile layout (Function.update context name (some (.object type address)))
      (.identifier name) = pure address := by
  simp only [place, placeWithNames.eq_def, objects, places, Function.update_self,
    Option.bind_some, resolved]



/-- By-value initialization retains argument evaluation, the complete call
and its return-extent check before entering the original continuation. -/
theorem record_call_keeps_arguments_and_complete_return (profile : Profile)
    (layout : Layout) (context : Context) (type : CType) (extent : Nat) (address : Ptr)
    (name : Name) (arguments : List CExpr) (service : RecordCall)
    (admitted : profile.recordCalls name = some service)
    (typed : service.resultType = type) :
    initializeRecord profile layout context type extent address (.call name arguments) =
      (argumentsWithNames
        (localOrLocated (values context) (declared context) profile.locations)
        profile.values layout arguments (objects profile context) >>= fun actual =>
        service.invoke actual >>= fun fields =>
          if fields.length = extent then CProg.initializeCells address fields else CProg.undefined) := by
  have noType : (none : Option CType) ≠ some type := by intro impossible; cases impossible
  simp only [initializeRecord, ScalarBytes.typeOf?, noType, ↓reduceIte,
    admitted, resolved, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, typed]

theorem unknown_record_call_is_not_a_pointer_result (profile : Profile)
    (layout : Layout) (context : Context) (type : CType) (extent : Nat) (address : Ptr)
    (name : Name) (arguments : List CExpr) (unknown : profile.recordCalls name = none) :
    initializeRecord profile layout context type extent address (.call name arguments) = CProg.undefined := by
  have noType : (none : Option CType) ≠ some type := by intro impossible; cases impossible
  simp only [initializeRecord, ScalarBytes.typeOf?, noType, ↓reduceIte,
    unknown, resolved, undefined_bind]

theorem wrong_record_call_type_is_not_reinterpreted (profile : Profile)
    (layout : Layout) (context : Context) (type : CType) (extent : Nat) (address : Ptr)
    (name : Name) (arguments : List CExpr) (service : RecordCall)
    (admitted : profile.recordCalls name = some service)
    (wrong : service.resultType ≠ type) :
    initializeRecord profile layout context type extent address (.call name arguments) = CProg.undefined := by
  have noType : (none : Option CType) ≠ some type := by intro impossible; cases impossible
  simp only [initializeRecord, ScalarBytes.typeOf?, noType, ↓reduceIte,
    admitted, resolved, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, wrong]

/-- Cleanup is attached to the declaration's actual automatic region, while
its binding and storage remain live. The callback sees the completed flow
before lexical restoration. This record profile does not invent scalar cleanup,
unwinding or callbacks on proof exhaustion. -/
def declarationCleanup (profile : Profile) (region : AutomaticRegion Context)
    (cleanup : Name → Ptr → Flow Context → CProg CVal Unit)
    (layout : Layout) (context : Context) (type : CType) (name : Name)
    (initial : Option CExpr) (callback : Name)
    (continuation : Context → CProg CVal (Result Context)) : CProg CVal (Result Context) :=
  match profile.cellExtent type with
  | none => CProg.undefined
  | some _ => declaration profile
      (AutomaticRegion.withCleanup region (fun _ address _ flow => cleanup callback address flow))
      layout context type name initial continuation

theorem cleanup_declaration_keeps_region_and_callback (profile : Profile)
    (region : AutomaticRegion Context)
    (cleanup : Name → Ptr → Flow Context → CProg CVal Unit)
    (layout : Layout) (context : Context) (type : CType) (name callback : Name)
    (initial : Option CExpr) (extent : Nat) (record : profile.cellExtent type = some extent)
    (continuation : Context → CProg CVal (Result Context)) :
    declarationCleanup profile region cleanup layout context type name initial callback continuation =
      declaration profile
        (AutomaticRegion.withCleanup region (fun _ address _ flow => cleanup callback address flow))
        layout context type name initial continuation := by
  simp only [declarationCleanup, record]

theorem unsupported_cleanup_storage_is_not_silent (profile : Profile)
    (region : AutomaticRegion Context)
    (cleanup : Name → Ptr → Flow Context → CProg CVal Unit)
    (layout : Layout) (context : Context) (type : CType) (name callback : Name)
    (initial : Option CExpr) (outside : profile.cellExtent type = none)
    (continuation : Context → CProg CVal (Result Context)) :
    declarationCleanup profile region cleanup layout context type name initial callback continuation =
      CProg.undefined := by simp only [declarationCleanup, outside]

/-- Scalar assignment updates an existing local binding or a typed physical
field. It does not introduce a new binding, turn a record into a pointer-valued
rvalue, or reinterpret a stored scalar tag. -/
def writeValue (profile : Profile) (layout : Layout) (context : Context)
    (target : CExpr) (value : CVal) : CProg CVal Context :=
  match target with
  | .identifier name => match context name with
      | some (.scalar type _) => do
          let converted ← scalarInitialValue profile type value
          pure (Function.update context name (some (.scalar type (some converted))))
      | some (.object _ _) => CProg.undefined
      | none => do
          let type ← resolved (profile.outsideTypes name)
          let converted ← scalarInitialValue profile type value
          let address ← place profile layout context target
          CProg.store address converted
          pure context
  | .field owner name throughPointer => do
      let descriptor ← resolved
        (((objects profile context).fieldLayout layout owner throughPointer) name)
      if descriptor.kind = valueKind value then do
        let address ← place profile layout context target
        CProg.store address value
        pure context
      else CProg.undefined
  | .unary .dereference _ => do
      let type ← resolved (ScalarBytes.typeOf? (types context profile.outsideTypes)
        target profile.fieldTypes)
      let converted ← scalarInitialValue profile type value
      let address ← place profile layout context target
      CProg.store address converted
      pure context
  | _ => CProg.undefined

/-- Record assignment reads the complete admitted typed-cell value before any
destination store. Its ownership proof is `CProg.copy_cells`. It transports
pointer references rather than copying their reachable objects. Scalar
assignment reads the actual right-hand operand before resolving its store.
The source comparison must justify this order for C's unsequenced operands;
native padding and byte encodings remain separate ABI obligations. -/
def assignment (profile : Profile) (layout : Layout) (context : Context) :
    CStatement → CProg CVal Context
  | .assign target operand => do
      let type ← resolved (ScalarBytes.typeOf? (types context profile.outsideTypes)
        target profile.fieldTypes)
      match profile.cellExtent type with
      | some extent =>
          if ScalarBytes.typeOf? (types context profile.outsideTypes)
              operand profile.fieldTypes = some type then do
            let destination ← place profile layout context target
            let source ← place profile layout context operand
            CProg.copyCells source destination extent
            pure context
          else CProg.undefined
      | none => do
          let value ← read profile layout context operand
          writeValue profile layout context target value
  | _ => CProg.undefined

/-- Dispatch reads its selector once through the same live object reader.
Case planning uses the declared static inventory and retains fall-through arms.
The source bridge admits the existing braced/return arm grammar separately. -/
def selectSwitch (profile : Profile) (layout : Layout) (context : Context)
    (selector : CExpr) (cases : List (CExpr × List CStatement))
    (otherwise : List CStatement) : CProg CVal (List CStatement) := do
  let value ← read profile layout context selector
  integerSwitchBody profile.caseConstants value cases otherwise

/-- All supported typed declarations and assignments use the existing scoped
statement engine. Blocks and integer switches retain their full flows. Effect
providers retain actual calls. Arrays and loops are outside this record profile;
they are not silently ignored or approximated. -/
def services (profile : Profile) (region : AutomaticRegion Context)
    (effect : Layout → Context → CExpr → CProg CVal Unit)
    (cleanup : Name → Ptr → Flow Context → CProg CVal Unit := fun _ _ _ => CProg.undefined) :
    ScopedServices Context where
  read := read profile
  declaration := declaration profile region
  declarationCleanup := declarationCleanup profile region cleanup
  array := fun _ _ _ _ _ _ _ => CProg.undefined
  effect := effect
  assignment := assignment profile
  counted := fun _ _ _ _ => CProg.undefined
  nestedBlocks := true
  selectSwitch := selectSwitch profile

theorem switch_selector_uses_live_reader (profile : Profile) (layout : Layout)
    (context : Context) (selector : CExpr) (cases : List (CExpr × List CStatement))
    (otherwise : List CStatement) :
    selectSwitch profile layout context selector cases otherwise =
      (read profile layout context selector >>= fun value =>
        integerSwitchBody profile.caseConstants value cases otherwise) := rfl

theorem wide_local_initialization_retains_word (value : UInt64) :
    objectInitialValue ⟨"uint64_t".toList, 0⟩ (.u64 value) = pure (.u64 value) := rfl

/-- Conversion from an unsigned 32-bit value to the admitted 64-bit type
keeps its natural value exactly, including values above signed-int range. -/
theorem unsigned_widening_retains_word (value : UInt32) :
    objectInitialValue ⟨"uint64_t".toList, 0⟩ (.u32 value) =
      pure (.u64 (UInt64.ofNat value.toNat)) := rfl

theorem unsigned_widening_keeps_natural_value (value : UInt32) :
    (UInt64.ofNat value.toNat).toNat = value.toNat := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
  have bounded := value.toNat_lt
  omega

theorem declared_wide_alias_retains_value (profile : Profile) (aliasedType : CType) (value : UInt64)
    (declaredAlias : profile.scalarAliases aliasedType = some ⟨"uint64_t".toList, 0⟩) :
    scalarInitialValue profile aliasedType (.u64 value) = pure (.u64 value) := by
  simp only [scalarInitialValue, declaredAlias, Option.getD_some, objectInitialValue]
  rfl

theorem declared_wide_alias_widens_unsigned (profile : Profile) (aliasedType : CType) (value : UInt32)
    (declaredAlias : profile.scalarAliases aliasedType = some ⟨"uint64_t".toList, 0⟩) :
    scalarInitialValue profile aliasedType (.u32 value) =
      pure (.u64 (UInt64.ofNat value.toNat)) := by
  simp only [scalarInitialValue, declaredAlias, Option.getD_some, objectInitialValue]
  rfl

theorem record_assignment_retains_snapshot (profile : Profile) (layout : Layout)
    (context : Context) (target operand : CExpr) (type : CType) (extent : Nat)
    (targetType : ScalarBytes.typeOf? (types context profile.outsideTypes)
      target profile.fieldTypes = some type)
    (sourceType : ScalarBytes.typeOf? (types context profile.outsideTypes)
      operand profile.fieldTypes = some type)
    (record : profile.cellExtent type = some extent) :
    assignment profile layout context (.assign target operand) =
      (place profile layout context target >>= fun destination =>
        place profile layout context operand >>= fun source =>
          CProg.copyCells source destination extent >>= fun _ => pure context) := by
  simp only [assignment, targetType, resolved, Prog.bind_eq, Prog.pure_eq,
    Prog.ret_bind, record, sourceType, ↓reduceIte]

theorem incompatible_record_assignment_rejected (profile : Profile) (layout : Layout)
    (context : Context) (target operand : CExpr) (type : CType) (extent : Nat)
    (targetType : ScalarBytes.typeOf? (types context profile.outsideTypes)
      target profile.fieldTypes = some type)
    (sourceType : ScalarBytes.typeOf? (types context profile.outsideTypes)
      operand profile.fieldTypes ≠ some type)
    (record : profile.cellExtent type = some extent) :
    assignment profile layout context (.assign target operand) = CProg.undefined := by
  simp only [assignment, targetType, resolved, Prog.bind_eq, Prog.pure_eq,
    Prog.ret_bind, record, sourceType, ↓reduceIte]

theorem scalar_field_write_keeps_place_and_value (profile : Profile) (layout : Layout)
    (context : Context) (owner : CExpr) (name : Name) (throughPointer : Bool)
    (value : CVal) (offset : Nat)
    (selected : ((objects profile context).fieldLayout layout owner throughPointer) name =
      some ⟨offset, valueKind value⟩) :
    writeValue profile layout context (.field owner name throughPointer) value =
      (place profile layout context (.field owner name throughPointer) >>= fun address =>
        CProg.store address value >>= fun _ => pure context) := by
  simp only [writeValue, selected, resolved, Prog.bind_eq, Prog.pure_eq,
    Prog.ret_bind, ↓reduceIte]

theorem wrongly_typed_scalar_field_write_rejected (profile : Profile) (layout : Layout)
    (context : Context) (owner : CExpr) (name : Name) (throughPointer : Bool)
    (value : CVal) (descriptor : Field)
    (selected : ((objects profile context).fieldLayout layout owner throughPointer) name =
      some descriptor)
    (wrong : descriptor.kind ≠ valueKind value) :
    writeValue profile layout context (.field owner name throughPointer) value =
      CProg.undefined := by
  simp only [writeValue, selected, resolved, Prog.bind_eq, Prog.pure_eq,
    Prog.ret_bind, wrong, ↓reduceIte]

theorem scalar_write_cannot_replace_record_binding (profile : Profile) (layout : Layout)
    (context : Context) (name : Name) (type : CType) (address : Ptr) (value : CVal)
    (bound : context name = some (.object type address)) :
    writeValue profile layout context (.identifier name) value = CProg.undefined := by
  simp only [writeValue, bound]

theorem local_scalar_write_refines_existing_inventory (profile : Profile) (layout : Layout)
    (context : Context) (name : Name) (type : CType) (previous : Option CVal)
    (value : CVal) (bound : context name = some (.scalar type previous)) :
    writeValue profile layout context (.identifier name) value =
      (scalarInitialValue profile type value >>= fun converted =>
        pure (Function.update context name (some (.scalar type (some converted))))) := by
  simp only [writeValue, bound]


theorem arrow_layout_uses_retained_record_type (profile : Profile) (context : Context)
    (layouts : CType → Layout) (fallback : Layout) (owner : CExpr) (type : CType)
    (provided : profile.recordFields = some layouts)
    (typed : ScalarBytes.typeOf? (types context profile.outsideTypes) owner profile.fieldTypes =
      some ⟨type.name, type.pointers + 1⟩) :
    (objects profile context).fieldLayout fallback owner true = layouts type := by
  funext name
  simp only [objects, ReadExpressions.ObjectReads.fieldLayout, provided, Option.map_some,
    fieldLayouts, typed, bind, Option.bind_some, ↓reduceIte]

theorem dot_layout_uses_retained_object_type (profile : Profile) (context : Context)
    (layouts : CType → Layout) (fallback : Layout) (owner : CExpr) (type : CType)
    (provided : profile.recordFields = some layouts)
    (typed : ScalarBytes.typeOf? (types context profile.outsideTypes) owner profile.fieldTypes =
      some type) :
    (objects profile context).fieldLayout fallback owner false = layouts type := by
  funext name
  simp only [objects, ReadExpressions.ObjectReads.fieldLayout, provided, Option.map_some,
    fieldLayouts, typed, bind, Option.bind_some, Bool.false_eq_true, if_false]

/-- A missing owner type has no invented global-name descriptor in the
explicit record profile. -/
theorem unknown_owner_type_is_not_global_fallback (profile : Profile) (context : Context)
    (layouts : CType → Layout) (fallback : Layout) (owner : CExpr) (throughPointer : Bool)
    (provided : profile.recordFields = some layouts)
    (unknown : ScalarBytes.typeOf? (types context profile.outsideTypes) owner profile.fieldTypes = none) :
    (objects profile context).fieldLayout fallback owner throughPointer = (fun _ => none) := by
  funext name
  simp only [objects, ReadExpressions.ObjectReads.fieldLayout, provided, Option.map_some,
    fieldLayouts, unknown, bind, Option.bind_none]


/-- Scalar introduction retains the live initializer read, typed conversion,
complete continuation and restoration of the previous local binding. -/
theorem initialized_scalar_keeps_read_conversion_and_flow (profile : Profile)
    (region : AutomaticRegion Context) (layout : Layout) (context : Context)
    (type : CType) (name : Name) (operand : CExpr)
    (scalar : profile.cellExtent type = none)
    (continuation : Context → CProg CVal (Result Context)) :
    declaration profile region layout context type name (some operand) continuation =
      (read profile layout context operand >>= fun actual =>
        scalarInitialValue profile type actual >>= fun value =>
          continuation (Function.update context name (some (.scalar type (some value)))) >>=
            fun result => pure (restore name (context name) result)) := by
  simp only [declaration, scalar, Prog.bind_eq]

/-- Aggregate introduction retains its complete by-value initializer in the
new object's context and the region's own inspection of every returned flow. -/
theorem initialized_record_keeps_initializer_region_and_flow (profile : Profile)
    (region : AutomaticRegion Context) (layout : Layout) (context : Context)
    (type : CType) (name : Name) (extent : Nat) (operand : CExpr)
    (record : profile.cellExtent type = some extent)
    (continuation : Context → CProg CVal (Result Context)) :
    declaration profile region layout context type name (some operand) continuation =
      (region name extent (fun address =>
        let updated := Function.update context name (some (.object type address))
        initializeRecord profile layout updated type extent address operand >>= fun _ =>
          continuation updated) >>= fun result => pure (restore name (context name) result)) := by
  simp only [declaration, record]

end ObjectBindings

/-- Existing scalar and array clients use the same context-polymorphic engine.
An uninitialized declaration is accepted only by its declared provider. -/
def Services.scoped (services : Services) (assign : Assignment) :
    ScopedServices Environment where
  read := services.read
  declaration := fun layout environment type name initial continuation =>
    match initial with
    | none => services.uninitialized layout environment type name continuation
    | some rhs => do
        let actual ← services.read layout environment rhs
        let value ← services.initialValue type actual
        let result ← continuation (Function.update environment name (some value))
        pure (restore name (environment name) result)
  array := fun layout environment type name extent values continuation => do
    let result ← services.array layout environment type name extent values continuation
    pure (restore name (environment name) result)
  effect := services.effect
  assignment := assign
  counted := fun layout fuel environment statement => do
    let result ← services.counted layout fuel environment statement
    pure (match result with
      | .finished updated => .finished (.next updated)
      | .exhausted => .exhausted)

def executeWith (services : Services) (assign : Assignment) (layout : Layout) (loopFuel fuel : Nat)
    (environment : Environment) (body : List CStatement) : CProg CVal Result :=
  executeScopedWith (services.scoped assign) layout loopFuel fuel environment body

theorem executeWith_equation (services : Services) (assign : Assignment) (layout : Layout)
    (loopFuel fuel : Nat) (environment : Environment) (body : List CStatement) :
    executeWith services assign layout loopFuel fuel environment body =
      (match body with
      | [] => pure (.finished (.next environment))
      | statement :: rest => match fuel with
        | 0 => pure .exhausted
        | fuel + 1 => match statement with
          | .empty => executeWith services assign layout loopFuel fuel environment rest
          | .declare type name rhs => do
              let actual ← services.read layout environment rhs
              let initial ← services.initialValue type actual
              let result ← executeWith services assign layout loopFuel fuel
                (Function.update environment name (some initial)) rest
              pure (restore name (environment name) result)
          | .declareUninitialized type name =>
              services.uninitialized layout environment type name
                (fun updated => executeWith services assign layout loopFuel fuel updated rest)
          | .declareArray type name extent initializers => do
              let result ← services.array layout environment type name extent initializers
                (fun updated => executeWith services assign layout loopFuel fuel updated rest)
              pure (restore name (environment name) result)
          | .effect operand => do
              services.effect layout environment operand
              executeWith services assign layout loopFuel fuel environment rest
          | .assign _ _ | .compoundAssign _ _ _ => do
              let updated ← assign layout environment statement
              executeWith services assign layout loopFuel fuel updated rest
          | .branch condition yes no => do
              let actual ← services.read layout environment condition
              let selected ← truth actual
              let result ← executeWith services assign layout loopFuel fuel environment (if selected then yes else no)
              resume (fun updated => executeWith services assign layout loopFuel fuel updated rest) result
          | .forLoop _ _ _ _ _ _ => do
              let result ← services.counted layout loopFuel environment statement
              match result with
              | .finished updated => executeWith services assign layout loopFuel fuel updated rest
              | .exhausted => pure .exhausted
          | .break => pure (.finished (.broken environment))
          | .return none => pure (.finished (.returned environment none))
          | .return (some rhs) => do
              let actual ← services.read layout environment rhs
              pure (.finished (.returned environment (some actual)))
          | _ => CProg.undefined) := by
  cases body with
  | nil => rw [executeWith, executeScopedWith.eq_def]
  | cons statement rest =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases statement
          case «return» value => cases value <;> rfl
          case «switch» selector cases otherwise =>
            rw [executeWith, executeScopedWith.eq_def]
            dsimp only [Services.scoped]
            exact undefined_bind _
          all_goals try rfl
          simp only [executeWith, executeScopedWith, Services.scoped,
            Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
          congr 1
          funext value
          cases value <;> rfl

/-- Existing clients retain the same public argument types, using the same
block interpreter under its read-only expression and declaration profile. -/
def execute (assign : Assignment) (layout : Layout) (loopFuel fuel : Nat)
    (environment : Environment) (body : List CStatement) : CProg CVal Result :=
  executeWith {} assign layout loopFuel fuel environment body

def loop (assign : Assignment) (layout : Layout) (innerFuel bodyFuel : Nat)
    (condition step : CExpr) (body : List CStatement) (fuel : Nat)
    (environment : Environment) : CProg CVal Result := do
  let actual ← expression layout environment condition
  let selected ← truth actual
  if selected then match fuel with
    | 0 => pure .exhausted
    | fuel + 1 => do
        let result ← execute assign layout innerFuel bodyFuel environment body
        match result with
        | .finished (.next updated) => do
            let advanced ← ReadLoops.increment updated step
            loop assign layout innerFuel bodyFuel condition step body fuel advanced
        | .finished (.broken updated) => pure (.finished (.next updated))
        | result => pure result
  else pure (.finished (.next environment))

def counted (assign : Assignment) (layout : Layout) (innerFuel bodyFuel fuel : Nat)
    (environment : Environment) : CStatement → CProg CVal Result
  | .forLoop type name initial condition step body =>
      if type = ⟨"uint32_t".toList, 0⟩ then do
        let actual ← expression layout environment initial
        let unsigned ← word actual
        let result ← loop assign layout innerFuel bodyFuel condition step body fuel
          (Function.update environment name (some (.u32 unsigned)))
        pure (restore name (environment name) result)
      else CProg.undefined
  | _ => CProg.undefined

theorem read_assignment_specialization (layout : Layout) (loopFuel fuel : Nat)
    (environment : Environment) (body : List CStatement) :
    execute ReadBlock.assign layout loopFuel fuel environment body =
      ReadBlock.execute layout loopFuel fuel environment body := by
  change executeWith {} ReadBlock.assign layout loopFuel fuel environment body = _
  induction fuel generalizing environment body with
  | zero => cases body <;> rfl
  | succ fuel ih =>
    cases body with
    | nil => rfl
    | cons statement rest =>
      cases statement
      case «return» value =>
        cases value <;> rw [executeWith_equation, ReadBlock.execute.eq_def]
      all_goals rw [executeWith_equation, ReadBlock.execute.eq_def]
      all_goals simp only [ih, undefined_bind]
      all_goals rfl

theorem empty_body_completes (assign : Assignment) (layout : Layout) (loopFuel fuel : Nat)
    (environment : Environment) :
    execute assign layout loopFuel fuel environment [] = pure (.finished (.next environment)) := by
  rw [execute, executeWith_equation]

theorem declaration_retains_actual_read_and_scope (assign : Assignment) (layout : Layout)
    (loopFuel fuel : Nat) (environment : Environment) (type : CType) (name : Name)
    (rhs : CExpr) (rest : List CStatement) :
    execute assign layout loopFuel (fuel + 1) environment (.declare type name rhs :: rest) =
      (expression layout environment rhs >>= fun actual => declaredValue type actual >>= fun initial =>
        execute assign layout loopFuel fuel (Function.update environment name (some initial)) rest >>=
          fun result => pure (restore name (environment name) result)) := by
  rw [execute, executeWith_equation]
  rfl

theorem branch_retains_selected_body_and_continuation (assign : Assignment) (layout : Layout)
    (loopFuel fuel : Nat) (environment : Environment) (condition : CExpr)
    (yes no rest : List CStatement) :
    execute assign layout loopFuel (fuel + 1) environment (.branch condition yes no :: rest) =
      (expression layout environment condition >>= fun actual => truth actual >>= fun selected =>
        execute assign layout loopFuel fuel environment (if selected then yes else no) >>=
          resume (fun updated => execute assign layout loopFuel fuel updated rest)) := by
  rw [execute, executeWith_equation]
  rfl

theorem nested_loop_retains_actual_read_service (assign : Assignment) (layout : Layout)
    (loopFuel fuel : Nat) (environment : Environment) (type : CType) (name : Name)
    (initial condition step : CExpr) (body rest : List CStatement) :
    execute assign layout loopFuel (fuel + 1) environment
      (.forLoop type name initial condition step body :: rest) =
      (ReadLoops.counted layout loopFuel environment (.forLoop type name initial condition step body)
        >>= fun result => match result with
          | .finished updated => execute assign layout loopFuel fuel updated rest
          | .exhausted => pure .exhausted) := by
  rw [execute, executeWith_equation]
  rfl

theorem assignment_executes_supplied_service (assign : Assignment) (layout : Layout)
    (loopFuel fuel : Nat) (environment : Environment) (location rhs : CExpr)
    (rest : List CStatement) :
    execute assign layout loopFuel (fuel + 1) environment (.assign location rhs :: rest) =
      (assign layout environment (.assign location rhs) >>= fun updated =>
        execute assign layout loopFuel fuel updated rest) := by
  rw [execute, executeWith_equation]
  rfl

theorem counted_retains_initializer_and_scope (assign : Assignment) (layout : Layout)
    (innerFuel bodyFuel fuel : Nat) (environment : Environment) (name : Name)
    (condition step : CExpr) (body : List CStatement) :
    counted assign layout innerFuel bodyFuel fuel environment
      (.forLoop ⟨"uint32_t".toList, 0⟩ name (.unsignedInteger 0) condition step body) =
      (loop assign layout innerFuel bodyFuel condition step body fuel
        (Function.update environment name (some (.u32 0))) >>= fun result =>
          pure (restore name (environment name) result)) := rfl

namespace Controls

def forbiddenAssignment : Assignment := fun _ _ _ => CProg.undefined
def layout : Layout := fun _ => none
def environment : Environment := fun _ => none

theorem array_explicit_extent_is_not_silently_ignored (read : Reader)
    (region : AutomaticRegion) (type : CType) (name : Name) (extent : CExpr)
    (initializers : List CExpr) (continuation : Environment → CProg CVal Result) :
    arrayBinding read region layout environment type name (some extent) initializers continuation =
      CProg.undefined := rfl

theorem object_declaration_does_not_repair_wrong_scalar (type : CType) (value : UInt32)
    (object : 0 < type.pointers) :
    objectInitialValue type (.u32 value) = CProg.undefined := by
  simp only [objectInitialValue, object, ↓reduceIte, pointer, undefined_bind]

theorem nonfield_assignment_is_not_invented (read : Reader) (name : Name) (rhs : CExpr) :
    fieldAssignment read layout environment (.assign (.identifier name) rhs) =
      CProg.undefined := rfl

theorem unselected_store_service_is_not_executed (body : List CStatement) :
    execute forbiddenAssignment layout 0 2 environment [.branch (.bool false) body []] =
      pure (.finished (.next environment)) := rfl

theorem return_never_enters_later_store_service (body : List CStatement) :
    execute forbiddenAssignment layout 0 1 environment (.return (some (.bool false)) :: body) =
      pure (.finished (.returned environment (some (.bool false)))) := rfl

theorem break_never_enters_later_store_service (body : List CStatement) :
    execute forbiddenAssignment layout 0 1 environment (.break :: body) =
      pure (.finished (.broken environment)) := rfl

end Controls

end Mettapedia.Machines.CMemory.StatementBlock

namespace Mettapedia.Machines.CMemory.StatementBlock.ObjectBindings

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open ReadExpressions

/-- An initialized local scalar resolves to its declared value, without
consulting a same-spelled global location. -/
theorem initialized_local_keeps_its_value (profile : Profile) (layout : Layout)
    (context : Context) (name : Name) (type : CType) (value : CVal)
    (known : context name = some (.scalar type (some value))) :
    read profile layout context (.identifier name) = pure value := by
  simp only [read, expressionWithNames.eq_def, localOrLocated, values, known]

/-- A local object's field inventory follows its declared record type, while
its scalar contents remain unread. -/
theorem local_object_keeps_field_inventory (profile : Profile) (fallback : Layout)
    (context : Context) (layouts : CType → Layout) (name : Name) (type : CType) (address : Ptr)
    (inventory : profile.recordFields = some layouts)
    (known : context name = some (.object type address)) :
    (objects profile context).fieldLayout fallback (.identifier name) false = layouts type := by
  simp only [objects, ObjectReads.fieldLayout, inventory, Option.map_some]
  funext fieldName
  simp only [fieldLayouts, ScalarBytes.typeOf?, types, known, bind, Option.bind_some, Bool.false_eq_true, if_false]

/-- A scalar pointer selects the pointee's record inventory. Nullable values
still retain the validity and dereference obligations of the reader. -/
theorem local_pointer_keeps_field_inventory (profile : Profile) (fallback : Layout)
    (context : Context) (layouts : CType → Layout) (name : Name) (typeName : Name)
    (depth : Nat) (address : Option Ptr)
    (inventory : profile.recordFields = some layouts)
    (known : context name = some (.scalar ⟨typeName, depth + 1⟩ (some (.ptr address)))) :
    (objects profile context).fieldLayout fallback (.identifier name) true = layouts ⟨typeName, depth⟩ := by
  simp only [objects, ObjectReads.fieldLayout, inventory, Option.map_some]
  funext fieldName
  simp only [fieldLayouts, ScalarBytes.typeOf?, types, known, bind, Option.bind_some, ↓reduceIte]

/-- Dot field reads obtain the object's place, retain the declared owner
inventory and then use the common typed cell reader. -/
theorem local_object_field_keeps_place_and_inventory (profile : Profile) (fallback : Layout)
    (context : Context) (layouts : CType → Layout) (name fieldName : Name)
    (type : CType) (address : Ptr)
    (inventory : profile.recordFields = some layouts)
    (known : context name = some (.object type address)) :
    read profile fallback context (.field (.identifier name) fieldName false) =
      field (layouts type) (.ptr (some address)) fieldName := by
  have selected := local_object_keeps_field_inventory profile fallback context layouts name type address inventory known
  simp only [read, expressionWithNames.eq_def, objects, placeWithNames.eq_def,
    places, known, Option.bind_some, resolved, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]
  exact congrArg (fun layout => field layout (CVal.ptr (some address)) fieldName) selected

/-- Arrow field reads retain the local nullable reference and its declared
pointee inventory; they do not replace it with a value snapshot. -/
theorem local_pointer_field_keeps_reference_and_inventory (profile : Profile) (fallback : Layout)
    (context : Context) (layouts : CType → Layout) (name fieldName typeName : Name)
    (depth : Nat) (address : Option Ptr)
    (inventory : profile.recordFields = some layouts)
    (known : context name = some (.scalar ⟨typeName, depth + 1⟩ (some (.ptr address)))) :
    read profile fallback context (.field (.identifier name) fieldName true) =
      field (layouts ⟨typeName, depth⟩) (.ptr address) fieldName := by
  rw [read, expressionWithNames.eq_def]
  change (read profile fallback context (.identifier name) >>= fun owner =>
    field ((objects profile context).fieldLayout fallback (.identifier name) true) owner fieldName) = _
  rw [initialized_local_keeps_its_value profile fallback context name _ _ known,
    local_pointer_keeps_field_inventory profile fallback context layouts name typeName depth address inventory known]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

/-- A declared object retains its actual place without a scalar read. -/
theorem local_object_keeps_place (profile : Profile) (layout : Layout)
    (context : Context) (name : Name) (type : CType) (address : Ptr)
    (known : context name = some (.object type address)) :
    place profile layout context (.identifier name) = pure address := by
  simp only [place, placeWithNames.eq_def, objects, places, known, Option.bind_some, resolved]

/-- Dot addressing retains the actual local place and its owner descriptor.
The descriptor's kind need not be a scalar: embedded fields keep addresses. -/
theorem local_object_field_keeps_address (profile : Profile) (fallback : Layout)
    (context : Context) (layouts : CType → Layout) (name fieldName : Name)
    (type : CType) (address : Ptr) (offset : Nat) (kind : FieldKind)
    (inventory : profile.recordFields = some layouts)
    (known : context name = some (.object type address))
    (selected : layouts type fieldName = some ⟨offset, kind⟩) :
    place profile fallback context (.field (.identifier name) fieldName false) = pure (address + offset) := by
  rw [place, placeWithNames.eq_def]
  change (place profile fallback context (.identifier name) >>= fun owner =>
    resolved (((objects profile context).fieldLayout fallback (.identifier name) false) fieldName) >>=
      fun descriptor => pure (owner + descriptor.offset)) = _
  rw [local_object_keeps_place profile fallback context name type address known,
    local_object_keeps_field_inventory profile fallback context layouts name type address inventory known,
    selected]
  simp only [resolved, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

/-- Arrow addressing reads the exact nullable reference first. Dereference
failure and pointer validity are not repaired by the static inventory law. -/
theorem local_pointer_field_keeps_address (profile : Profile) (fallback : Layout)
    (context : Context) (layouts : CType → Layout) (name fieldName typeName : Name)
    (depth : Nat) (address : Option Ptr)
    (inventory : profile.recordFields = some layouts)
    (known : context name = some (.scalar ⟨typeName, depth + 1⟩ (some (.ptr address)))) :
    place profile fallback context (.field (.identifier name) fieldName true) =
      fieldAddress (layouts ⟨typeName, depth⟩) (.ptr address) fieldName := by
  rw [place, placeWithNames.eq_def]
  change (read profile fallback context (.identifier name) >>= fun owner =>
    fieldAddress ((objects profile context).fieldLayout fallback (.identifier name) true) owner fieldName) = _
  rw [initialized_local_keeps_its_value profile fallback context name _ _ known,
    local_pointer_keeps_field_inventory profile fallback context layouts name typeName depth address inventory known]
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

end Mettapedia.Machines.CMemory.StatementBlock.ObjectBindings
