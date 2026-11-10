import Mettapedia.GSLT.LanguageDef.OwnershipCalls
import Mettapedia.Machines.CMemory.PermissionFlow

/-!
# Module admission for ownership plans

This checks the permission projection emitted from a typed native C body.
Foreign implementations must obey their named contracts; the source-to-plan
projection, scalar operations and compiler remain tested boundaries. Admission
does prove that every finite execution of the *recorded* control flow avoids
undefined permission operations and satisfies its recorded result contract.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Ownership

open Mettapedia.Machines.CMemory.Borrowing
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.PermissionFlow

inductive ResultSpec where
  | value
  | static (nullable : Bool)
  | borrowed (allowed : Region) (writing nullable : Bool)
  | viewed (allowed : Region) (writing : Bool)
  | owned (family : Nat) (nullable : Bool)
  deriving DecidableEq, Repr

def clean (s : State) : Bool :=
  s.loans == initial.loans && s.allocations == initial.allocations && s.authorities.isEmpty &&
    s.transfers.isEmpty

def nullOnly (s : State) : Bool := s.nullResult && s.result.isNone && s.ownedResult.isNone

def returnAllowed (spec : ResultSpec) (s : State) : Bool :=
  clean s && match spec with
  | .value => s.result.isNone && s.ownedResult.isNone && !s.nullResult
  | .static nullable =>
      (nullable && nullOnly s) || (!s.nullResult && s.ownedResult.isNone &&
        match s.result with | some r => r.root == 0 && !s.resultWriting | none => false)
  | .borrowed allowed writing nullable =>
      (nullable && nullOnly s) || (!s.nullResult && s.ownedResult.isNone &&
        s.resultWriting == writing &&
        match s.result with | some r => decide (allowed.Contains r) | none => false)
  | .owned family nullable =>
      (nullable && nullOnly s) || (!s.nullResult && s.result.isNone && s.ownedResult == some family)
  | .viewed allowed writing =>
      !s.nullResult && s.ownedResult.isNone && s.resultWriting == writing &&
        decide (s.result = some allowed)

structure Function where
  name : String
  signature : Signature
  inputs : List Nat
  ambient : List (Nat × Nat)
  result : ResultSpec
  body : Plan Action
  deriving DecidableEq, Repr

structure Foreign where
  name : String
  signature : Signature
  obligation : String
  deriving DecidableEq, Repr

structure Module where
  foreign : List Foreign
  functions : List Function
  deriving DecidableEq, Repr

def Module.names (m : Module) : List String :=
  m.foreign.map Foreign.name ++ m.functions.map Function.name

def Module.callables (m : Module) : List Callable :=
  m.foreign.map (fun f => ⟨f.name, f.signature⟩) ++
    m.functions.map (fun f => ⟨f.name, f.signature⟩)

def shapeValid (parameters : List Parameter) (shape : ReturnShape) : Bool :=
  match shape with
  | .value | .static _ => true
  | .owned family _ => family != 0
  | .wholeViewed index writing =>
      match parameters[index]? with
      | some (.viewed canWrite) => !writing || canWrite
      | _ => false
  | .borrowed index offset count writing _ | .viewed index offset count writing =>
      match parameters[index]? with
      | some (.borrowed extent canWrite) | some (.optionalBorrowed extent canWrite) => offset + count ≤ extent && (!writing || canWrite)
      | _ => false

def signatureValid (signature : Signature) : Bool :=
  signature.parameters.all (fun p => match p with
    | .value | .released _ | .viewed _ | .static _ => true
    | .borrowed count _ | .optionalBorrowed count _ => count != 0
    | .owned _ family | .optionalOwned _ family => family != 0) &&
  shapeValid signature.parameters signature.result &&
  uniqueIds (signature.fields.map Prod.fst) &&
  signature.fields.all (fun (key, shape) => key < signature.parameters.length &&
    shapeValid signature.parameters shape) &&
  (signature.records.isEmpty || signature.result == .value) &&
  uniqueIds (signature.records.map Prod.fst) &&
  signature.records.all (fun (_, shape) =>
    (match shape with | .borrowed .. | .viewed .. | .wholeViewed .. | .static .. | .owned .. => true | _ => false) &&
    shapeValid signature.parameters shape)

def instantiateResult (inputs : List Nat) (shape : ReturnShape) : Option ResultSpec :=
  match shape with
  | .value => some .value
  | .static nullable => some (.static nullable)
  | .owned family nullable => some (.owned family nullable)
  | .borrowed index offset count writing nullable => do
      let root ← inputs[index]?
      pure (.borrowed ⟨root, offset, count⟩ writing nullable)
  | .viewed index offset count writing => do
      let root ← inputs[index]?
      pure (.viewed ⟨root, offset, count⟩ writing)
  | .wholeViewed index writing => do
      let root ← inputs[index]?
      pure (.viewed ⟨root, 0, 1⟩ writing)

def expectedResult (f : Function) : Option ResultSpec := instantiateResult f.inputs f.signature.result

def fieldAllowed (spec : ResultSpec) (result : FieldResult) : Bool :=
  match spec with
  | .static nullable => match result.region with
    | none => nullable
    | some r => r.root == 0 && !result.writing
  | .borrowed allowed writing nullable => match result.region with
    | none => nullable
    | some r => decide (allowed.Contains r) && result.writing == writing
  | .viewed allowed writing => result.region == some allowed && result.writing == writing
  | _ => false

def fieldsAllowed (f : Function) (s : State) : Bool :=
  s.fieldResults.length == f.signature.fields.length &&
  uniqueIds (s.fieldResults.map FieldResult.key) &&
  f.signature.fields.all (fun (key, shape) =>
    match instantiateResult f.inputs shape, s.fieldResults.find? (fun r => r.key == key) with
    | some spec, some result => fieldAllowed spec result
    | _, _ => false)

def recordsAllowed (f : Function) (s : State) : Bool :=
  s.recordResults.length + s.recordOwners.length == f.signature.records.length &&
  uniqueIds (s.recordResults.map FieldResult.key ++ s.recordOwners.map Prod.fst) &&
  f.signature.records.all (fun (key, shape) =>
    match instantiateResult f.inputs shape with
    | some (.owned family nullable) =>
        s.recordOwners.lookup key == some family ||
        (nullable && (s.recordResults.find? (fun r => r.key == key)).any (fun r => r.region.isNone && !r.writing))
    | some spec => (s.recordResults.find? (fun r => r.key == key)).any (fieldAllowed spec)
    | none => false)

def functionReturnAllowed (f : Function) (s : State) : Bool :=
  returnAllowed f.result s && fieldsAllowed f s && recordsAllowed f s

def inputsValid (f : Function) : Bool :=
  f.inputs.length == f.signature.parameters.length &&
  (f.signature.parameters.zip f.inputs).all (fun (p, id) => match p with
    | .value | .static _ => id == 0
    | .released _ => false
    | _ => id != 0) && uniqueIds (f.inputs.filter (· != 0)) &&
  uniqueIds (f.inputs.filter (· != 0) ++ f.ambient.map Prod.fst)

def inputRoot (f : Function) (id count : Nat) (mode : Mode) (origin : Origin) (family : Nat) : Bool :=
  (f.signature.parameters.zip f.inputs).any (fun (p, root) =>
    root == id && match p with
    | .borrowed extent writing | .optionalBorrowed extent writing => count == extent && mode == (if writing then .exclusive else .shared) &&
        origin == .input && family == 0
    | .owned extent brand | .optionalOwned extent brand => count == extent && mode == .exclusive && origin == .heap && family == brand
    | .viewed writing => count == 1 && mode == (if writing then .exclusive else .shared) && origin == .input && family == 0
    | _ => false) ||
  f.ambient.any (fun (root, extent) => root == id && count == extent && mode == .exclusive &&
    origin == .input && family == 0)

def wholeInput (f : Function) (root : Nat) : Bool :=
  (f.signature.parameters.zip f.inputs).any fun (p, id) =>
    id == root && match p with | .viewed _ => true | _ => false

/-- Abstract span units may be lent as a whole, but are never numeric byte
extents. In particular a possibly empty view cannot satisfy a one-byte call. -/
def wholeRegion (f : Function) (region : Region) : Bool :=
  !wholeInput f region.root || (region.first == 0 && region.count == 1)

def wholeArguments (f : Function) (s : State) (signature : Signature)
    (arguments : List Argument) : Bool :=
  arguments.zipIdx.all fun (arg, index) => match arg with
    | .loan id | .maybe id => match findLoan s id with
      | none => false
      | some l => !wholeInput f l.region.root ||
          match signature.parameters[index]? with | some (.viewed _) => true | _ => false
    | _ => true

def wholeAction (callables : List Callable) (f : Function) (s : State) : Action → Bool
  | .borrow _ _ region _ | .access _ region _ | .restrict _ region
  | .result _ region _ | .fieldResult _ _ region _ | .recordResult _ _ region _ =>
      wholeRegion f region
  | .view _ region bytes _ =>
      wholeRegion f region && (!wholeInput f region.root || bytes == 1)
  | .invoke name arguments =>
      (callables.find? fun c => c.name == name).any fun c => wholeArguments f s c.signature arguments
  | _ => true

def enabledCore (callables : List Callable) (f : Function) (s : State) (a : Action) : Option State :=
  match a with
  | .invoke name arguments => do
      let callee ← callables.find? fun c => c.name == name
      invoke callee.signature s arguments
  | .root id count mode origin family =>
      if origin == .input || f.inputs.contains id || (f.ambient.map Prod.fst).contains id then do
        require (inputRoot f id count mode origin family)
        apply s a
      else apply s a
  | _ => apply s a

def enabled (callables : List Callable) (f : Function) (s : State) (a : Action) : Option State := do
  require (wholeAction callables f s a)
  enabledCore callables f s a

theorem enabled_valid {callables : List Callable} {f : Function} {s after : State} {a : Action}
    (h : enabled callables f s a = some after) (valid : Valid s) : Valid after := by
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  cases a <;> simp only [enabledCore] at h <;> try exact apply_preserves_valid h valid
  case root id count mode origin family =>
    split at h
    · obtain ⟨_, _, rest⟩ := Option.bind_eq_some_iff.mp h
      exact apply_preserves_valid rest valid
    · exact apply_preserves_valid h valid
  case invoke name arguments =>
    obtain ⟨callee, _, rest⟩ := Option.bind_eq_some_iff.mp h
    exact invoke_preserves_valid rest valid

def admitFunction (callables : List Callable) (f : Function) : Bool :=
  f.ambient.isEmpty && !f.name.isEmpty && signatureValid f.signature && inputsValid f &&
  decide (expectedResult f = some f.result) &&
  callables.any (fun c => c.name == f.name && decide (c.signature = f.signature)) &&
  match PermissionFlow.check (enabled callables f) (functionReturnAllowed f) f.body initial with
  | none => false
  | some outputs => outputs.all fun exit =>
      (exit.kind == .normal || exit.kind == .returned) && functionReturnAllowed f exit.state

def admit (m : Module) : Bool :=
  !m.functions.isEmpty && m.names.Nodup &&
  m.foreign.all (fun f => !f.name.isEmpty && !f.obligation.isEmpty && signatureValid f.signature) &&
  m.functions.all (admitFunction m.callables)

/-- Join separately kernel-checked bodies without recomputing large plans. -/
theorem admit_of_checks {m : Module} (nonempty : m.functions ≠ []) (unique : m.names.Nodup)
    (foreignChecked : m.foreign.all (fun f => !f.name.isEmpty && !f.obligation.isEmpty && signatureValid f.signature) = true)
    (bodiesChecked : m.functions.all (admitFunction m.callables) = true) : admit m = true := by
  simp [admit, nonempty, unique, foreignChecked, bodiesChecked]

theorem admitted_function_checked {callables : List Callable} {f : Function}
    (h : admitFunction callables f = true) :
    ∃ outputs, PermissionFlow.check (enabled callables f) (functionReturnAllowed f) f.body initial = some outputs := by
  unfold admitFunction at h
  obtain ⟨_, h⟩ := Bool.and_eq_true_iff.mp h
  split at h
  · contradiction
  · rename_i outputs checked
    exact ⟨outputs, checked⟩

theorem admitted_has_no_ambient_authority {callables : List Callable} {f : Function}
    (admitted : admitFunction callables f = true) : f.ambient = [] := by
  cases stored : f.ambient with
  | nil => rfl
  | cons first rest => simp [admitFunction, stored] at admitted

theorem admitted_execution_safe {callables : List Callable} {f : Function}
    (admitted : admitFunction callables f = true) {outcome : Exit State}
    (execution : Execution (enabled callables f) f.body initial outcome) :
    outcome.kind ≠ .fault ∧ Valid outcome.state := by
  constructor
  · exact PermissionFlow.admitted_no_fault (admitted_function_checked admitted) execution
  · exact execution.invariant (fun _ _ _ h valid => enabled_valid h valid) initial_valid

theorem admitted_return_contract {callables : List Callable} {f : Function}
    (admitted : admitFunction callables f = true) {outcome : Exit State}
    (execution : Execution (enabled callables f) f.body initial outcome)
    (returned : outcome.kind = .returned) : returnAllowed f.result outcome.state = true := by
  obtain ⟨outputs, checked⟩ := admitted_function_checked admitted
  have h := PermissionFlow.checked_returns checked outcome
    (PermissionFlow.covers_execution execution checked) returned
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1

theorem admitted_field_postconditions {callables : List Callable} {f : Function}
    (admitted : admitFunction callables f = true) {outcome : Exit State}
    (execution : Execution (enabled callables f) f.body initial outcome)
    (returned : outcome.kind = .returned) : fieldsAllowed f outcome.state = true := by
  obtain ⟨outputs, checked⟩ := admitted_function_checked admitted
  have h := PermissionFlow.checked_returns checked outcome
    (PermissionFlow.covers_execution execution checked) returned
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2

/-- A returned reference-bearing value has every declared field, with its
original input lifetime and access rights. Cleanup alone cannot certify it. -/
theorem admitted_record_postconditions {callables : List Callable} {f : Function}
    (admitted : admitFunction callables f = true) {outcome : Exit State}
    (execution : Execution (enabled callables f) f.body initial outcome)
    (returned : outcome.kind = .returned) : recordsAllowed f outcome.state = true := by
  obtain ⟨outputs, checked⟩ := admitted_function_checked admitted
  have h := PermissionFlow.checked_returns checked outcome
    (PermissionFlow.covers_execution execution checked) returned
  exact (Bool.and_eq_true_iff.mp h).2

/-- A checked callee's non-null returned view can be substituted into the
caller without widening the loan or forgetting the caller's other aliases.
This is composition of recorded permission executions, not a claim that an
arbitrary native C function implements its recorded execution. -/
theorem admitted_borrowed_return_composes {callables : List Callable} {f : Function}
    (admitted : admitFunction callables f = true) {outcome : Exit State}
    (execution : Execution (enabled callables f) f.body initial outcome)
    (returned : outcome.kind = .returned) {root offset count extent id : Nat}
    {writing nullable : Bool}
    (contract : f.result = .borrowed ⟨root, offset, count⟩ writing nullable)
    (parameterBound : offset + count ≤ extent)
    (nonNull : outcome.state.nullResult = false) {caller after : State}
    (passed : passArgument caller (.borrowed extent writing) (.loan id) = some after) :
    ∃ view l, outcome.state.result = some view ∧ l ∈ caller.loans ∧ l.id = id ∧
      Access caller.loans id (instantiateView l.region view.first view.count) writing := by
  have checked := admitted_return_contract admitted execution returned
  rw [contract] at checked
  cases result : outcome.state.result with
  | none => simp [returnAllowed, nullOnly, nonNull, result] at checked
  | some view =>
      have bounded : (Region.mk root offset count).Contains view := by
        exact (show
          clean outcome.state = true ∧ outcome.state.ownedResult.isNone = true ∧
          outcome.state.resultWriting = writing ∧
          (Region.mk root offset count).Contains view from by
            simpa [returnAllowed, nullOnly, nonNull, result, and_assoc] using checked) |>.2.2.2
      have inside : view.first + view.count ≤ extent := by
        have := bounded.2.2
        simp only [Region.finish] at this
        omega
      obtain ⟨l, present, identity, access⟩ := typed_call_access_composition passed inside
      exact ⟨view, l, rfl, present, identity, access⟩

theorem admitted_view_return_exact {callables : List Callable} {f : Function}
    (admitted : admitFunction callables f = true) {outcome : Exit State}
    (execution : Execution (enabled callables f) f.body initial outcome)
    (returned : outcome.kind = .returned) {allowed : Region} {writing : Bool}
    (contract : f.result = .viewed allowed writing) :
    outcome.state.result = some allowed ∧ outcome.state.resultWriting = writing := by
  have checked := admitted_return_contract admitted execution returned
  rw [contract] at checked
  have facts : clean outcome.state = true ∧ outcome.state.nullResult = false ∧
      outcome.state.ownedResult.isNone = true ∧ outcome.state.resultWriting = writing ∧
      outcome.state.result = some allowed := by
    simpa [returnAllowed, and_assoc] using checked
  exact ⟨facts.2.2.2.2, facts.2.2.2.1⟩

namespace Controls

def scalarSignature : Signature := ⟨[], false, .value, [], []⟩
def scalar (name : String) (body : Plan Action) : Function :=
  ⟨name, scalarSignature, [], [], .value, body⟩
def scalarCallables (name : String) : List Callable := [⟨name, scalarSignature⟩]

def globalWriteBody : Plan Action :=
  .step (.root 1 4 .exclusive .input 0)
    (.step (.access 1 ⟨1, 0, 4⟩ true) (.step (.endLoan 1) .ret))

theorem ambient_global_write_refused :
    admitFunction (scalarCallables "ambient")
      { scalar "ambient" globalWriteBody with ambient := [(1, 4)] } = false := by decide

def globalSignature : Signature := ⟨[.borrowed 4 true], false, .value, [], []⟩

theorem explicit_global_write_admitted :
    admitFunction [⟨"explicit", globalSignature⟩]
      ⟨"explicit", globalSignature, [1], [], .value, globalWriteBody⟩ = true := by decide

def loopBody : Plan Action :=
  .step (.root 1 8 .exclusive .local 0)
    (.step (.borrow 2 1 ⟨1, 0, 4⟩ .exclusive)
      (.step (.access 2 ⟨1, 0, 4⟩ true)
        (.step (.endLoan 2) (.step (.endLoan 1) .continueLoop))))

theorem repeated_lexical_borrow_admitted :
    admitFunction (scalarCallables "loop") (scalar "loop" (.loop loopBody .ret)) = true := by decide

theorem leaking_loop_borrow_refused :
    admitFunction (scalarCallables "loop") (scalar "loop"
      (.loop (.step (.root 1 8 .exclusive .local 0) .continueLoop) .ret)) = false := by decide

theorem unhandled_foreign_call_refused : admitFunction (scalarCallables "call")
    (scalar "call" (.step (.invoke "unknown" []) .ret)) = false := by decide

theorem false_borrowed_result_refused : admitFunction (scalarCallables "escape")
    ⟨"escape", scalarSignature, [], [], .borrowed ⟨2, 0, 4⟩ false false,
      .step (.root 1 4 .exclusive .local 0)
        (.step (.result 1 ⟨1, 0, 4⟩ false) .ret)⟩ = false := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.Ownership
