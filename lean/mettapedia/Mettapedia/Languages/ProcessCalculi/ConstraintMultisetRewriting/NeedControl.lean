import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedStoreOperations
import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceInstructions

/-!
# Call-time-choice controls with explicit snapshot references

Runtime controls use natural snapshot names rather than embedding source
stores. Stored alternatives and returned results keep their own references.
An edit continuation has one marked snapshot position, filled only after
the requested copy and operation finish. All other references are retained.

Decoding is a mathematical comparison with the independently owned source
instructions. It is not a function called by a transform rule.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedControl

open Mettapedia.Machines.BranchLocalNeed
open CallTimeChoice (Store Val VExp Comp Outcome Program Suspension Memo Prim candidates primOutcome unquoteHead)

abbrev Result (StoreName : Type) := Outcome × StoreName

inductive Goal (StoreName : Type) where
  | eval (snapshot : StoreName) (environment : List (Val Nat)) (code : Comp)
  | alts (snapshot : StoreName) (branches : List (Comp × List (Val Nat)))
  | seqK (rest : Comp) (environment : List (Val Nat)) (results : List (Result StoreName))
  | forceVal (snapshot : StoreName) (value : Val Nat)
  | commitK (cell : Nat) (results : List (Result StoreName))
  | followK (results : List (Result StoreName))
  deriving DecidableEq, Repr

inductive Frame (StoreName : Type) where
  | sequence (rest : Comp) (environment : List (Val Nat))
  | commit (cell : Nat)
  | follow
  | later (goal : Goal StoreName)
  | append (earlier : List (Result StoreName))
  | cons (earlier : Result StoreName)
  deriving DecidableEq, Repr

inductive Control (StoreName : Type) where
  | task (goal : Goal StoreName) (stack : List (Frame StoreName))
  | returned (results : List (Result StoreName)) (stack : List (Frame StoreName))
  deriving DecidableEq, Repr

variable {A B C : Type}

def resultMap (change : A → B) (result : Result A) : Result B := (result.1,change result.2)

def Goal.map (change : A → B) : Goal A → Goal B
  | .eval snapshot environment code => .eval (change snapshot) environment code
  | .alts snapshot branches => .alts (change snapshot) branches
  | .seqK rest environment results => .seqK rest environment (results.map (resultMap change))
  | .forceVal snapshot value => .forceVal (change snapshot) value
  | .commitK cell results => .commitK cell (results.map (resultMap change))
  | .followK results => .followK (results.map (resultMap change))

def Frame.map (change : A → B) : Frame A → Frame B
  | .sequence rest environment => .sequence rest environment
  | .commit cell => .commit cell
  | .follow => .follow
  | .later goal => .later (goal.map change)
  | .append earlier => .append (earlier.map (resultMap change))
  | .cons earlier => .cons (resultMap change earlier)

def Control.map (change : A → B) : Control A → Control B
  | .task goal stack => .task (goal.map change) (stack.map (Frame.map change))
  | .returned results stack => .returned (results.map (resultMap change)) (stack.map (Frame.map change))

@[simp] theorem resultMap_id : resultMap (id : A → A) = id := by funext result; cases result; rfl
@[simp] theorem resultMap_comp (first : A → B) (second : B → C) (result : Result A) :
    resultMap second (resultMap first result) = resultMap (second ∘ first) result := rfl

@[simp] theorem resultMap_pair (change : A → B) (outcome : Outcome) (name : A) :
    resultMap change (outcome,name) = (outcome,change name) := rfl

@[simp] theorem resultMap_list (first : A → B) (second : B → C) (results : List (Result A)) :
    (results.map (resultMap first)).map (resultMap second) = results.map (resultMap (second ∘ first)) := by
  simp [List.map_map,Function.comp_def]

@[simp] theorem Goal.map_id : Goal.map (id : A → A) = id := by
  funext goal
  cases goal <;> simp [Goal.map]
@[simp] theorem Goal.map_comp (first : A → B) (second : B → C) (goal : Goal A) :
    (goal.map first).map second = goal.map (second ∘ first) := by
  cases goal <;> simp [Goal.map,List.map_map,Function.comp_def]

@[simp] theorem Frame.map_id : Frame.map (id : A → A) = id := by
  funext frame
  cases frame <;> simp [Frame.map]
@[simp] theorem Frame.map_comp (first : A → B) (second : B → C) (frame : Frame A) :
    (frame.map first).map second = frame.map (second ∘ first) := by
  cases frame <;> simp [Frame.map,List.map_map,Function.comp_def]

@[simp] theorem Control.map_id : Control.map (id : A → A) = id := by
  funext control
  cases control <;> simp [Control.map]
@[simp] theorem Control.map_comp (first : A → B) (second : B → C) (control : Control A) :
    (control.map first).map second = control.map (second ∘ first) := by
  cases control <;> simp [Control.map,List.map_map,Function.comp_def]

def Goal.decode (stores : A → Store) : Goal A → CallTimeChoice.Goal
  | .eval snapshot environment code => .eval (stores snapshot) environment code
  | .alts snapshot branches => .alts (stores snapshot) branches
  | .seqK rest environment results => .seqK rest environment (results.map (resultMap stores))
  | .forceVal snapshot value => .forceVal (stores snapshot) value
  | .commitK cell results => .commitK cell (results.map (resultMap stores))
  | .followK results => .followK (results.map (resultMap stores))

def Frame.decode (stores : A → Store) : Frame A → CallTimeChoiceInstructions.Frame
  | .sequence rest environment => .sequence rest environment
  | .commit cell => .commit cell
  | .follow => .follow
  | .later goal => .later (goal.decode stores)
  | .append earlier => .append (earlier.map (resultMap stores))
  | .cons earlier => .cons (resultMap stores earlier)

def Control.decode (stores : A → Store) : Control A → CallTimeChoiceInstructions.Control
  | .task goal stack => .task (goal.decode stores) (stack.map (Frame.decode stores))
  | .returned results stack => .returned (results.map (resultMap stores)) (stack.map (Frame.decode stores))

@[simp] theorem Goal.decode_map (change : A → B) (stores : B → Store) (goal : Goal A) :
    (goal.map change).decode stores = goal.decode (stores ∘ change) := by
  cases goal <;> simp [Goal.map,Goal.decode,List.map_map,Function.comp_def]

@[simp] theorem Frame.decode_map (change : A → B) (stores : B → Store) (frame : Frame A) :
    (frame.map change).decode stores = frame.decode (stores ∘ change) := by
  cases frame <;> simp [Frame.map,Frame.decode,List.map_map,Function.comp_def]

@[simp] theorem Frame.decode_list_map (change : A → B) (stores : B → Store) (stack : List (Frame A)) :
    (stack.map (Frame.map change)).map (Frame.decode stores) = stack.map (Frame.decode (stores ∘ change)) := by
  simp [List.map_map,Function.comp_def]

@[simp] theorem Control.decode_map (change : A → B) (stores : B → Store) (control : Control A) :
    (control.map change).decode stores = control.decode (stores ∘ change) := by
  cases control <;> simp [Control.map,Control.decode,List.map_map,Function.comp_def]

/-- Existing names are marked; `none` denotes only the newly edited
snapshot. This is data with explicit substitution, not an opaque callback. -/
abbrev Resume := Control (Option Nat)

def resumeAt (snapshot : Nat) (resume : Resume) : Control Nat :=
  resume.map (fun name => name.getD snapshot)

inductive Action where
  | direct (control : Control Nat)
  | edit (source : Nat) (operation : NeedStoreOperations.Operation) (resume : Resume)
  deriving DecidableEq

def Action.decode (stores : Nat → Store) : Action → CallTimeChoiceInstructions.Control
  | .direct control => control.decode stores
  | .edit source operation resume =>
      resume.decode (fun name => match name with
        | none => operation.apply (stores source)
        | some old => stores old)

structure Plan where
  input : Control Nat
  reads : List (SnapshotCopy.Row Suspension)
  action : Action
  deriving DecidableEq

/-- Interpretation of the few data rows read by instruction selection.
Physical realization must establish these facts from the actual world. -/
def RowMatches (stores : Nat → Store) : SnapshotCopy.Row Suspension → Prop
  | .ready _ => True
  | .metadata snapshot count trace => count = (stores snapshot).cells.length ∧ trace = (stores snapshot).trace
  | .cell snapshot index value => (stores snapshot).cells[index]? = some value
  | _ => False

def Plan.Supported (stores : Nat → Store) (plan : Plan) : Prop :=
  ∀ row ∈ plan.reads, RowMatches stores row

/-- Finite instruction shapes. Their guards inspect values and the fixed
program table; actual store observations are explicit rows of the plan. -/
inductive Intent (program : Program) where
  | ret (source : Nat) (env : List (Val Nat)) (value : VExp) (stack : List (Frame Nat))
  | seq (source : Nat) (env : List (Val Nat)) (first rest : Comp) (stack : List (Frame Nat))
  | need (source count : Nat) (trace : List Nat) (env : List (Val Nat)) (producer body : Comp) (stack : List (Frame Nat))
  | delay (source count : Nat) (trace : List Nat) (env : List (Val Nat)) (producer body : Comp) (stack : List (Frame Nat))
  | force (source : Nat) (env : List (Val Nat)) (value : VExp) (stack : List (Frame Nat))
  | caseConHit (source : Nat) (env : List (Val Nat)) (value : VExp) (name arity : Nat) (hit miss : Comp)
      (fields : List (Val Nat)) (matched : (value.eval env).matchCon name arity = some fields) (stack : List (Frame Nat))
  | caseConMiss (source : Nat) (env : List (Val Nat)) (value : VExp) (name arity : Nat) (hit miss : Comp)
      (unmatched : (value.eval env).matchCon name arity = none) (stack : List (Frame Nat))
  | caseAppHit (source : Nat) (env : List (Val Nat)) (value : VExp) (hit miss : Comp) (head arg : Val Nat)
      (matched : (value.eval env).matchApp = some (head,arg)) (stack : List (Frame Nat))
  | caseAppMiss (source : Nat) (env : List (Val Nat)) (value : VExp) (hit miss : Comp)
      (unmatched : (value.eval env).matchApp = none) (stack : List (Frame Nat))
  | call (source : Nat) (env : List (Val Nat)) (function : Nat) (args : List VExp)
      (available : candidates program function args.length ≠ []) (stack : List (Frame Nat))
  | callNone (source : Nat) (env : List (Val Nat)) (function : Nat) (args : List VExp)
      (empty : candidates program function args.length = []) (stack : List (Frame Nat))
  | callRule (source : Nat) (env : List (Val Nat)) (index : Nat) (args : List VExp) (rule : CallTimeChoice.Rule)
      (selected : program[index]? = some rule) (arity : rule.arity = args.length) (stack : List (Frame Nat))
  | callRuleNone (source : Nat) (env : List (Val Nat)) (index : Nat) (args : List VExp)
      (missing : ∀ rule, program[index]? = some rule → rule.arity ≠ args.length) (stack : List (Frame Nat))
  | choose (source : Nat) (env : List (Val Nat)) (first second : Comp) (stack : List (Frame Nat))
  | fail (source : Nat) (env : List (Val Nat)) (stack : List (Frame Nat))
  | emit (source : Nat) (env : List (Val Nat)) (event : Nat) (rest : Comp) (stack : List (Frame Nat))
  | quote (source count : Nat) (trace : List Nat) (env : List (Val Nat)) (code : Comp) (stack : List (Frame Nat))
  | runCode (source : Nat) (env : List (Val Nat)) (value : VExp) (cell : Nat) (record : Suspension)
      (code : value.eval env = .code cell) (stack : List (Frame Nat))
  | runOther (source : Nat) (env : List (Val Nat)) (value : VExp)
      (notCode : ∀ cell, value.eval env ≠ .code cell) (stack : List (Frame Nat))
  | prim (source : Nat) (env : List (Val Nat)) (operation : Prim) (args : List VExp) (stack : List (Frame Nat))
  | altsNil (source : Nat) (stack : List (Frame Nat))
  | altsCons (source : Nat) (code : Comp) (env : List (Val Nat))
      (remaining : List (Comp × List (Val Nat))) (stack : List (Frame Nat))
  | seqKNil (code : Comp) (env : List (Val Nat)) (stack : List (Frame Nat))
  | seqKOk (code : Comp) (env : List (Val Nat)) (value : Val Nat) (source : Nat)
      (remaining : List (Result Nat)) (stack : List (Frame Nat))
  | seqKStop (code : Comp) (env : List (Val Nat)) (outcome : Outcome) (source : Nat)
      (remaining : List (Result Nat)) (stopped : outcome.isOk = false) (stack : List (Frame Nat))
  | forceWhnf (source : Nat) (value : Val Nat) (ready : value.isCell = false) (stack : List (Frame Nat))
  | forceDone (source cell : Nat) (record : Suspension) (value : Val Nat)
      (done : record.memo = .done value) (stack : List (Frame Nat))
  | forceBlackhole (source cell : Nat) (record : Suspension)
      (busy : record.memo = .evaluating) (stack : List (Frame Nat))
  | forcePending (source cell : Nat) (record : Suspension)
      (pending : record.memo = .pending) (stack : List (Frame Nat))
  | forceThunk (source cell : Nat) (record : Suspension) (stack : List (Frame Nat))
  | commitNil (cell : Nat) (stack : List (Frame Nat))
  | commitOk (cell : Nat) (value : Val Nat) (source : Nat) (remaining : List (Result Nat)) (stack : List (Frame Nat))
  | commitStop (cell : Nat) (outcome : Outcome) (source : Nat) (remaining : List (Result Nat))
      (stopped : outcome.isOk = false) (stack : List (Frame Nat))
  | followNil (stack : List (Frame Nat))
  | followOk (value : Val Nat) (source : Nat) (remaining : List (Result Nat)) (stack : List (Frame Nat))
  | followStop (outcome : Outcome) (source : Nat) (remaining : List (Result Nat))
      (stopped : outcome.isOk = false) (stack : List (Frame Nat))
  | sequenceReturn (results : List (Result Nat)) (code : Comp) (env : List (Val Nat)) (stack : List (Frame Nat))
  | commitReturn (results : List (Result Nat)) (cell : Nat) (stack : List (Frame Nat))
  | followReturn (results : List (Result Nat)) (stack : List (Frame Nat))
  | laterReturn (results : List (Result Nat)) (goal : Goal Nat) (stack : List (Frame Nat))
  | appendReturn (first second : List (Result Nat)) (stack : List (Frame Nat))
  | consReturn (first : Result Nat) (remaining : List (Result Nat)) (stack : List (Frame Nat))

def Intent.plan {program : Program} : Intent program → Plan
  | .ret source env value stack =>
      ⟨.task (.eval source env (.ret value)) stack,[.ready source],
        .direct (.returned [(.ok (value.eval env),source)] stack)⟩
  | .seq source env first rest stack =>
      ⟨.task (.eval source env (.seq first rest)) stack,[],
        .direct (.task (.eval source env first) (.sequence rest env :: stack))⟩
  | .need source count trace env producer body stack =>
      ⟨.task (.eval source env (.need producer body)) stack,[.ready source,.metadata source count trace],
        .edit source (.allocate producer env)
          (.task (.eval none (.need count :: env) body) (stack.map (Frame.map some)))⟩
  | .delay source count trace env producer body stack =>
      ⟨.task (.eval source env (.delay producer body)) stack,[.ready source,.metadata source count trace],
        .edit source (.allocate producer env)
          (.task (.eval none (.thunk count :: env) body) (stack.map (Frame.map some)))⟩
  | .force source env value stack =>
      ⟨.task (.eval source env (.force value)) stack,[],.direct (.task (.forceVal source (value.eval env)) stack)⟩
  | .caseConHit source env value name arity hit miss fields _ stack =>
      ⟨.task (.eval source env (.caseCon value name arity hit miss)) stack,[],
        .direct (.task (.eval source (fields++env) hit) stack)⟩
  | .caseConMiss source env value name arity hit miss _ stack =>
      ⟨.task (.eval source env (.caseCon value name arity hit miss)) stack,[],.direct (.task (.eval source env miss) stack)⟩
  | .caseAppHit source env value hit miss head arg _ stack =>
      ⟨.task (.eval source env (.caseApp value hit miss)) stack,[],
        .direct (.task (.eval source (head::arg::env) hit) stack)⟩
  | .caseAppMiss source env value hit miss _ stack =>
      ⟨.task (.eval source env (.caseApp value hit miss)) stack,[],.direct (.task (.eval source env miss) stack)⟩
  | .call source env function args _ stack =>
      ⟨.task (.eval source env (.call function args)) stack,[],
        .direct (.task (.alts source ((candidates program function args.length).map
          fun rule => (rule.body,args.map (·.eval env)))) stack)⟩
  | .callNone source env function args _ stack =>
      ⟨.task (.eval source env (.call function args)) stack,[],.direct (.returned [(.fail,source)] stack)⟩
  | .callRule source env index args rule _ _ stack =>
      ⟨.task (.eval source env (.callRule index args)) stack,[],
        .direct (.task (.eval source (args.map (·.eval env)) rule.body) stack)⟩
  | .callRuleNone source env index args _ stack =>
      ⟨.task (.eval source env (.callRule index args)) stack,[],.direct (.returned [(.fail,source)] stack)⟩
  | .choose source env first second stack =>
      ⟨.task (.eval source env (.choose first second)) stack,[],
        .direct (.task (.eval source env first) (.later (.eval source env second) :: stack))⟩
  | .fail source env stack =>
      ⟨.task (.eval source env .fail) stack,[],.direct (.returned [(.fail,source)] stack)⟩
  | .emit source env event rest stack =>
      ⟨.task (.eval source env (.emit event rest)) stack,[.ready source],
        .edit source (.emit event) (.task (.eval none env rest) (stack.map (Frame.map some)))⟩
  | .quote source count trace env code stack =>
      ⟨.task (.eval source env (.quote code)) stack,[.ready source,.metadata source count trace],
        .edit source (.allocate code env) (.returned [(.ok (.code count),none)] (stack.map (Frame.map some)))⟩
  | .runCode source env value cell record _ stack =>
      ⟨.task (.eval source env (.run value)) stack,[.ready source,.cell source cell record],
        .direct (.task (.eval source record.env record.code) (.follow :: stack))⟩
  | .runOther source env value _ stack =>
      ⟨.task (.eval source env (.run value)) stack,[],
        .direct (.returned [(.ok (.app (.sym unquoteHead) (value.eval env)),source)] stack)⟩
  | .prim source env operation args stack =>
      ⟨.task (.eval source env (.prim operation args)) stack,[],
        .direct (.returned [(primOutcome operation (args.map (·.eval env)),source)] stack)⟩
  | .altsNil source stack => ⟨.task (.alts source []) stack,[],.direct (.returned [] stack)⟩
  | .altsCons source code env remaining stack =>
      ⟨.task (.alts source ((code,env)::remaining)) stack,[],
        .direct (.task (.eval source env code) (.later (.alts source remaining) :: stack))⟩
  | .seqKNil code env stack => ⟨.task (.seqK code env []) stack,[],.direct (.returned [] stack)⟩
  | .seqKOk code env value source remaining stack =>
      ⟨.task (.seqK code env ((.ok value,source)::remaining)) stack,[],
        .direct (.task (.eval source (value::env) code) (.later (.seqK code env remaining) :: stack))⟩
  | .seqKStop code env outcome source remaining _ stack =>
      ⟨.task (.seqK code env ((outcome,source)::remaining)) stack,[],
        .direct (.task (.seqK code env remaining) (.cons (outcome,source) :: stack))⟩
  | .forceWhnf source value _ stack =>
      ⟨.task (.forceVal source value) stack,[],.direct (.returned [(.ok value,source)] stack)⟩
  | .forceDone source cell record value _ stack =>
      ⟨.task (.forceVal source (.need cell)) stack,[.ready source,.cell source cell record],
        .direct (.task (.forceVal source value) stack)⟩
  | .forceBlackhole source cell record _ stack =>
      ⟨.task (.forceVal source (.need cell)) stack,[.ready source,.cell source cell record],
        .direct (.returned [(.blackhole,source)] stack)⟩
  | .forcePending source cell record _ stack =>
      ⟨.task (.forceVal source (.need cell)) stack,[.ready source,.cell source cell record],
        .edit source (.memo cell .evaluating)
          (.task (.eval none record.env record.code) (.commit cell :: stack.map (Frame.map some)))⟩
  | .forceThunk source cell record stack =>
      ⟨.task (.forceVal source (.thunk cell)) stack,[.ready source,.cell source cell record],
        .direct (.task (.eval source record.env record.code) (.follow :: stack))⟩
  | .commitNil cell stack => ⟨.task (.commitK cell []) stack,[],.direct (.returned [] stack)⟩
  | .commitOk cell value source remaining stack =>
      ⟨.task (.commitK cell ((.ok value,source)::remaining)) stack,[.ready source],
        .edit source (.memo cell (.done value))
          (.task (.forceVal none value)
            (.later (.commitK cell (remaining.map (resultMap some))) :: stack.map (Frame.map some)))⟩
  | .commitStop cell outcome source remaining _ stack =>
      ⟨.task (.commitK cell ((outcome,source)::remaining)) stack,[.ready source],
        .edit source (.memo cell .pending)
          (.task (.commitK cell (remaining.map (resultMap some)))
            (.cons (outcome,none) :: stack.map (Frame.map some)))⟩
  | .followNil stack => ⟨.task (.followK []) stack,[],.direct (.returned [] stack)⟩
  | .followOk value source remaining stack =>
      ⟨.task (.followK ((.ok value,source)::remaining)) stack,[],
        .direct (.task (.forceVal source value) (.later (.followK remaining) :: stack))⟩
  | .followStop outcome source remaining _ stack =>
      ⟨.task (.followK ((outcome,source)::remaining)) stack,[],
        .direct (.task (.followK remaining) (.cons (outcome,source) :: stack))⟩
  | .sequenceReturn results code env stack =>
      ⟨.returned results (.sequence code env :: stack),[],.direct (.task (.seqK code env results) stack)⟩
  | .commitReturn results cell stack =>
      ⟨.returned results (.commit cell :: stack),[],.direct (.task (.commitK cell results) stack)⟩
  | .followReturn results stack =>
      ⟨.returned results (.follow :: stack),[],.direct (.task (.followK results) stack)⟩
  | .laterReturn results goal stack =>
      ⟨.returned results (.later goal :: stack),[],.direct (.task goal (.append results :: stack))⟩
  | .appendReturn first second stack =>
      ⟨.returned second (.append first :: stack),[],.direct (.returned (first++second) stack)⟩
  | .consReturn first remaining stack =>
      ⟨.returned remaining (.cons first :: stack),[],.direct (.returned (first::remaining) stack)⟩

private theorem supported_metadata {stores : Nat → Store} {plan : Plan}
    (supported : plan.Supported stores) (source count : Nat) (trace : List Nat)
    (read : SnapshotCopy.Row.metadata source count trace ∈ plan.reads) :
    count = (stores source).cells.length ∧ trace = (stores source).trace := supported _ read

private theorem supported_cell {stores : Nat → Store} {plan : Plan}
    (supported : plan.Supported stores) (source cell : Nat) (record : Suspension)
    (read : SnapshotCopy.Row.cell source cell record ∈ plan.reads) :
    (stores source).cells[cell]? = some record := supported _ read

theorem Intent.read_kind {program : Program} (intent : Intent program) (row : SnapshotCopy.Row Suspension)
    (member : row ∈ intent.plan.reads) :
    (∃ name, row = .ready name) ∨ (∃ name count trace, row = .metadata name count trace) ∨
      (∃ name index value, row = .cell name index value) := by
  cases intent <;> simp_all [Intent.plan]
  all_goals rcases member with rfl | rfl <;> simp

attribute [local simp] Frame.decode.eq_1 Frame.decode.eq_2 Frame.decode.eq_3
  Frame.decode.eq_4 Frame.decode.eq_5 Frame.decode.eq_6

/-- Every declared control plan, with its actual read facts, implements
one existing source instruction. No source transition is an admission
premise of an intent or its plan. -/
theorem Intent.source_step {program : Program} (intent : Intent program) (stores : Nat → Store)
    (supported : intent.plan.Supported stores) :
    CallTimeChoiceInstructions.Instruction program
      (intent.plan.input.decode stores) (intent.plan.action.decode stores) := by
  cases intent with
  | ret source env value stack =>
      exact .ret (stores source) env value (stack.map (Frame.decode stores))
  | seq source env first rest stack =>
      exact .seq (stores source) env first rest (stack.map (Frame.decode stores))
  | need source count trace env producer body stack =>
      obtain ⟨rfl,_⟩ := supported_metadata supported source count trace (by simp [Intent.plan])
      simpa [Intent.plan,Control.decode,Goal.decode,Action.decode,
        Function.comp_def,NeedStoreOperations.Operation.apply] using
        CallTimeChoiceInstructions.Instruction.need (P := program) (stores source) env producer body (stack.map (Frame.decode stores))
  | delay source count trace env producer body stack =>
      obtain ⟨rfl,_⟩ := supported_metadata supported source count trace (by simp [Intent.plan])
      simpa [Intent.plan,Control.decode,Goal.decode,Action.decode,
        Function.comp_def,NeedStoreOperations.Operation.apply] using
        CallTimeChoiceInstructions.Instruction.delay (P := program) (stores source) env producer body (stack.map (Frame.decode stores))
  | force source env value stack => exact .force (stores source) env value (stack.map (Frame.decode stores))
  | caseConHit source env value name arity hit miss fields matched stack =>
      exact .caseConHit (stores source) env value name arity hit miss fields matched (stack.map (Frame.decode stores))
  | caseConMiss source env value name arity hit miss unmatched stack =>
      exact .caseConMiss (stores source) env value name arity hit miss unmatched (stack.map (Frame.decode stores))
  | caseAppHit source env value hit miss head arg matched stack =>
      exact .caseAppHit (stores source) env value hit miss head arg matched (stack.map (Frame.decode stores))
  | caseAppMiss source env value hit miss unmatched stack =>
      exact .caseAppMiss (stores source) env value hit miss unmatched (stack.map (Frame.decode stores))
  | call source env function args available stack =>
      exact .call (stores source) env function args available (stack.map (Frame.decode stores))
  | callNone source env function args empty stack =>
      exact .callNone (stores source) env function args empty (stack.map (Frame.decode stores))
  | callRule source env index args rule selected arity stack =>
      exact .callRule (stores source) env index args rule selected arity (stack.map (Frame.decode stores))
  | callRuleNone source env index args missing stack =>
      exact .callRuleNone (stores source) env index args missing (stack.map (Frame.decode stores))
  | choose source env first second stack => exact .choose (stores source) env first second (stack.map (Frame.decode stores))
  | fail source env stack => exact .fail (stores source) env (stack.map (Frame.decode stores))
  | emit source env event rest stack =>
      simpa [Intent.plan,Control.decode,Goal.decode,Action.decode,
        Function.comp_def,NeedStoreOperations.Operation.apply] using
        CallTimeChoiceInstructions.Instruction.emit (P := program) (stores source) env event rest (stack.map (Frame.decode stores))
  | quote source count trace env code stack =>
      obtain ⟨rfl,_⟩ := supported_metadata supported source count trace (by simp [Intent.plan])
      simpa [Intent.plan,Control.decode,Goal.decode,Action.decode,
        Function.comp_def,NeedStoreOperations.Operation.apply] using
        CallTimeChoiceInstructions.Instruction.quote (P := program) (stores source) env code (stack.map (Frame.decode stores))
  | runCode source env value cell record code stack =>
      exact .runCode (stores source) env value cell record code
        (supported_cell supported source cell record (by simp [Intent.plan])) (stack.map (Frame.decode stores))
  | runOther source env value notCode stack =>
      exact .runOther (stores source) env value notCode (stack.map (Frame.decode stores))
  | prim source env operation args stack =>
      exact .prim (stores source) env operation args (stack.map (Frame.decode stores))
  | altsNil source stack => exact .altsNil (stores source) (stack.map (Frame.decode stores))
  | altsCons source code env remaining stack =>
      exact .altsCons (stores source) code env remaining (stack.map (Frame.decode stores))
  | seqKNil code env stack => exact .seqKNil code env (stack.map (Frame.decode stores))
  | seqKOk code env value source remaining stack =>
      exact .seqKOk code env value (stores source) (remaining.map (resultMap stores)) (stack.map (Frame.decode stores))
  | seqKStop code env outcome source remaining stopped stack =>
      exact .seqKStop code env outcome (stores source) (remaining.map (resultMap stores)) stopped (stack.map (Frame.decode stores))
  | forceWhnf source value ready stack => exact .forceWhnf (stores source) value ready (stack.map (Frame.decode stores))
  | forceDone source cell record value done stack =>
      exact .forceDone (stores source) cell record value
        (supported_cell supported source cell record (by simp [Intent.plan])) done (stack.map (Frame.decode stores))
  | forceBlackhole source cell record busy stack =>
      exact .forceBlackhole (stores source) cell record
        (supported_cell supported source cell record (by simp [Intent.plan])) busy (stack.map (Frame.decode stores))
  | forcePending source cell record pending stack =>
      have found := supported_cell supported source cell record (by simp [Intent.plan])
      simpa [Intent.plan,Control.decode,Goal.decode,Action.decode,
        Function.comp_def,NeedStoreOperations.Operation.apply] using
        CallTimeChoiceInstructions.Instruction.forcePending (P := program) (stores source) cell record found pending (stack.map (Frame.decode stores))
  | forceThunk source cell record stack =>
      exact .forceThunk (stores source) cell record
        (supported_cell supported source cell record (by simp [Intent.plan])) (stack.map (Frame.decode stores))
  | commitNil cell stack => exact .commitNil cell (stack.map (Frame.decode stores))
  | commitOk cell value source remaining stack =>
      simpa [Intent.plan,Control.decode,Goal.decode,Action.decode,
        Function.comp_def,NeedStoreOperations.Operation.apply] using
        CallTimeChoiceInstructions.Instruction.commitOk (P := program) cell value (stores source)
          (remaining.map (resultMap stores)) (stack.map (Frame.decode stores))
  | commitStop cell outcome source remaining stopped stack =>
      simpa [Intent.plan,Control.decode,Goal.decode,Action.decode,
        Function.comp_def,NeedStoreOperations.Operation.apply] using
        CallTimeChoiceInstructions.Instruction.commitStop (P := program) cell outcome (stores source)
          (remaining.map (resultMap stores)) stopped (stack.map (Frame.decode stores))
  | followNil stack => exact .followNil (stack.map (Frame.decode stores))
  | followOk value source remaining stack =>
      exact .followOk value (stores source) (remaining.map (resultMap stores)) (stack.map (Frame.decode stores))
  | followStop outcome source remaining stopped stack =>
      exact .followStop outcome (stores source) (remaining.map (resultMap stores)) stopped (stack.map (Frame.decode stores))
  | sequenceReturn results code env stack => exact .sequenceReturn (results.map (resultMap stores)) code env (stack.map (Frame.decode stores))
  | commitReturn results cell stack => exact .commitReturn (results.map (resultMap stores)) cell (stack.map (Frame.decode stores))
  | followReturn results stack => exact .followReturn (results.map (resultMap stores)) (stack.map (Frame.decode stores))
  | laterReturn results goal stack =>
      exact .laterReturn (results.map (resultMap stores)) (goal.decode stores) (stack.map (Frame.decode stores))
  | appendReturn first second stack =>
      simpa [Intent.plan,Control.decode,Action.decode,List.map_append] using
        CallTimeChoiceInstructions.Instruction.appendReturn (P := program)
          (first.map (resultMap stores)) (second.map (resultMap stores)) (stack.map (Frame.decode stores))
  | consReturn first remaining stack =>
      exact .consReturn (resultMap stores first) (remaining.map (resultMap stores)) (stack.map (Frame.decode stores))

/-- Construct a local instruction instance in a source model. This does
not run a subcomputation: it examines one root and the rows it will read.
Physical rule admission remains independent of this witness constructor. -/
def selectForModel (program : Program) (stores : Nat → Store) : Control Nat → Option (Intent program)
  | .returned _ [] => none
  | .returned results (.sequence code env :: stack) => some (.sequenceReturn results code env stack)
  | .returned results (.commit cell :: stack) => some (.commitReturn results cell stack)
  | .returned results (.follow :: stack) => some (.followReturn results stack)
  | .returned results (.later goal :: stack) => some (.laterReturn results goal stack)
  | .returned results (.append earlier :: stack) => some (.appendReturn earlier results stack)
  | .returned results (.cons earlier :: stack) => some (.consReturn earlier results stack)
  | .task (.eval source env code) stack => match code with
    | .ret value => some (.ret source env value stack)
    | .seq first rest => some (.seq source env first rest stack)
    | .need producer body => some (.need source (stores source).cells.length (stores source).trace env producer body stack)
    | .delay producer body => some (.delay source (stores source).cells.length (stores source).trace env producer body stack)
    | .force value => some (.force source env value stack)
    | .caseCon value name arity hit miss =>
        match matched : (value.eval env).matchCon name arity with
        | some fields => some (.caseConHit source env value name arity hit miss fields matched stack)
        | none => some (.caseConMiss source env value name arity hit miss matched stack)
    | .caseApp value hit miss =>
        match matched : (value.eval env).matchApp with
        | some (head,arg) => some (.caseAppHit source env value hit miss head arg matched stack)
        | none => some (.caseAppMiss source env value hit miss matched stack)
    | .call function args =>
        if empty : candidates program function args.length = [] then some (.callNone source env function args empty stack)
        else some (.call source env function args empty stack)
    | .callRule index args =>
        match found : program[index]? with
        | some rule =>
            if arity : rule.arity = args.length then some (.callRule source env index args rule found arity stack)
            else some (.callRuleNone source env index args (by intro other selected; have same := Option.some.inj (found.symm.trans selected); subst other; exact arity) stack)
        | none => some (.callRuleNone source env index args (by intro other selected; simp [found] at selected) stack)
    | .choose first second => some (.choose source env first second stack)
    | .fail => some (.fail source env stack)
    | .emit event rest => some (.emit source env event rest stack)
    | .quote code => some (.quote source (stores source).cells.length (stores source).trace env code stack)
    | .run value =>
        match atValue : value.eval env with
        | .code cell => match found : (stores source).cells[cell]? with
          | some record => some (.runCode source env value cell record atValue stack)
          | none => none
        | .sym name => some (.runOther source env value (by intro cell; simp [atValue]) stack)
        | .app head arg => some (.runOther source env value (by intro cell; simp [atValue]) stack)
        | .need cell => some (.runOther source env value (by intro other; simp [atValue]) stack)
        | .thunk cell => some (.runOther source env value (by intro other; simp [atValue]) stack)
    | .prim operation args => some (.prim source env operation args stack)
  | .task (.alts source []) stack => some (.altsNil source stack)
  | .task (.alts source ((code,env)::remaining)) stack => some (.altsCons source code env remaining stack)
  | .task (.seqK code env []) stack => some (.seqKNil code env stack)
  | .task (.seqK code env ((.ok value,source)::remaining)) stack => some (.seqKOk code env value source remaining stack)
  | .task (.seqK code env ((.fail,source)::remaining)) stack => some (.seqKStop code env .fail source remaining rfl stack)
  | .task (.seqK code env ((.blackhole,source)::remaining)) stack => some (.seqKStop code env .blackhole source remaining rfl stack)
  | .task (.forceVal source value) stack => match value with
    | .need cell => match found : (stores source).cells[cell]? with
      | none => none
      | some record => match atMemo : record.memo with
        | .done value => some (.forceDone source cell record value atMemo stack)
        | .evaluating => some (.forceBlackhole source cell record atMemo stack)
        | .pending => some (.forcePending source cell record atMemo stack)
    | .thunk cell => match found : (stores source).cells[cell]? with
      | none => none
      | some record => some (.forceThunk source cell record stack)
    | .sym name => some (.forceWhnf source (.sym name) rfl stack)
    | .app head arg => some (.forceWhnf source (.app head arg) rfl stack)
    | .code cell => some (.forceWhnf source (.code cell) rfl stack)
  | .task (.commitK cell []) stack => some (.commitNil cell stack)
  | .task (.commitK cell ((.ok value,source)::remaining)) stack => some (.commitOk cell value source remaining stack)
  | .task (.commitK cell ((.fail,source)::remaining)) stack => some (.commitStop cell .fail source remaining rfl stack)
  | .task (.commitK cell ((.blackhole,source)::remaining)) stack => some (.commitStop cell .blackhole source remaining rfl stack)
  | .task (.followK []) stack => some (.followNil stack)
  | .task (.followK ((.ok value,source)::remaining)) stack => some (.followOk value source remaining stack)
  | .task (.followK ((.fail,source)::remaining)) stack => some (.followStop .fail source remaining rfl stack)
  | .task (.followK ((.blackhole,source)::remaining)) stack => some (.followStop .blackhole source remaining rfl stack)

set_option maxHeartbeats 1000000 in
theorem selectForModel_spec {program : Program} {stores : Nat → Store} {control : Control Nat}
    {intent : Intent program} (selected : selectForModel program stores control = some intent) :
    intent.plan.input = control ∧ intent.plan.Supported stores := by
  unfold selectForModel at selected
  repeat' first
    | split at selected
    | subst intent
    | cases selected
    | simp_all [Intent.plan,Plan.Supported,RowMatches]

set_option maxHeartbeats 1000000 in
theorem no_selection_next_none {program : Program} {stores : Nat → Store} {control : Control Nat}
    (selected : selectForModel program stores control = none) :
    CallTimeChoiceInstructions.next program (control.decode stores) = none := by
  unfold selectForModel at selected
  repeat' first
    | split at selected
    | cases selected
    | simp_all [CallTimeChoiceInstructions.next,Control.decode,Goal.decode]

/-- The complete existing instruction grammar is covered in both
directions, preserving each saved/result-associated store interpretation. -/
theorem source_instruction_iff_supported_plan (program : Program) (stores : Nat → Store)
    (control : Control Nat) (next : CallTimeChoiceInstructions.Control) :
    CallTimeChoiceInstructions.Instruction program (control.decode stores) next ↔
      ∃ intent : Intent program, intent.plan.input = control ∧ intent.plan.Supported stores ∧
        intent.plan.action.decode stores = next := by
  constructor
  · intro instruction
    cases chosen : selectForModel program stores control with
    | none =>
        have absent := no_selection_next_none chosen
        have present := CallTimeChoiceInstructions.next_complete instruction
        rw [absent] at present
        cases present
    | some intent =>
        have properties := selectForModel_spec chosen
        have source := intent.source_step stores properties.2
        rw [properties.1] at source
        have same := Option.some.inj
          ((CallTimeChoiceInstructions.next_complete source).symm.trans
            (CallTimeChoiceInstructions.next_complete instruction))
        exact ⟨intent,properties.1,properties.2,same⟩
  · rintro ⟨intent,input,supported,output⟩
    have source := intent.source_step stores supported
    simpa only [input,output] using source

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedControl
