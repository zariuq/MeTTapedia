import Mettapedia.Logic.ConstraintTypes.Contracts

/-!
# Ordered execution at a predicate-type boundary

Observations distinguish answers, effects and terminal faults. A result check
filters answers without re-running the body, reordering effects or swallowing
faults. Each result carries the world in which its membership check is entered;
the boundary does not snapshot a global type world.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes

inductive Trace (Answer Fault Effect : Type) where
  | done
  | answer (value : Answer) (rest : Trace Answer Fault Effect)
  | fault (error : Fault)
  | effect (event : Effect) (rest : Trace Answer Fault Effect)
  deriving DecidableEq, Repr

namespace Trace

variable {A B F E : Type}

def append : Trace A F E → Trace A F E → Trace A F E
  | .done, right => right
  | .answer a rest, right => .answer a (append rest right)
  | .fault error, _ => .fault error
  | .effect event rest, right => .effect event (append rest right)

def bind (trace : Trace A F E) (continuation : A → Trace B F E) : Trace B F E :=
  match trace with
  | .done => .done
  | .answer a rest => append (continuation a) (bind rest continuation)
  | .fault error => .fault error
  | .effect event rest => .effect event (bind rest continuation)

theorem append_done (trace : Trace A F E) : trace.append .done = trace := by
  induction trace <;> simp_all [append]

theorem bind_answer (value : A) (continuation : A → Trace B F E) :
    (Trace.answer value .done).bind continuation = continuation value := by
  simp [bind, append_done]

/-- Binding a computed answer and immediately returning it preserves the whole
execution, including effects, multiplicity and terminal faults. -/
theorem bind_return (trace : Trace A F E) :
    trace.bind (fun value => .answer value .done) = trace := by
  induction trace with
  | done | fault _ => rfl
  | answer value rest ih => simp [bind, append, ih]
  | effect event rest ih => simp [bind, ih]

def map (f : A → B) : Trace A F E → Trace B F E
  | .done => .done
  | .answer a rest => .answer (f a) (map f rest)
  | .fault error => .fault error
  | .effect event rest => .effect event (map f rest)

def filter (predicate : A → Bool) : Trace A F E → Trace A F E
  | .done => .done
  | .answer value rest =>
      if predicate value then .answer value (filter predicate rest) else filter predicate rest
  | .fault error => .fault error
  | .effect event rest => .effect event (filter predicate rest)

def filterMap (check : A → Option B) : Trace A F E → Trace B F E
  | .done => .done
  | .answer value rest => match check value with
      | none => filterMap check rest
      | some checked => .answer checked (filterMap check rest)
  | .fault error => .fault error
  | .effect event rest => .effect event (filterMap check rest)

def answers : Trace A F E → List A
  | .done | .fault _ => []
  | .answer value rest => value :: answers rest
  | .effect _ rest => answers rest

def effects : Trace A F E → List E
  | .done | .fault _ => []
  | .answer _ rest => effects rest
  | .effect event rest => event :: effects rest

def terminalFault : Trace A F E → Option F
  | .done => none
  | .fault error => some error
  | .answer _ rest | .effect _ rest => terminalFault rest

def AllAnswers (predicate : A → Bool) : Trace A F E → Prop
  | .done | .fault _ => True
  | .answer value rest => predicate value = true ∧ AllAnswers predicate rest
  | .effect _ rest => AllAnswers predicate rest

theorem answers_filter (predicate : A → Bool) (trace : Trace A F E) :
    (trace.filter predicate).answers = trace.answers.filter predicate := by
  induction trace with
  | done | fault _ => rfl
  | answer a rest ih => cases h : predicate a <;> simp [filter, answers, h, ih]
  | effect _ _ ih => exact ih

theorem answers_filterMap (check : A → Option B) (trace : Trace A F E) :
    (trace.filterMap check).answers = trace.answers.filterMap check := by
  induction trace with
  | done | fault _ => rfl
  | answer a rest ih => cases h : check a <;> simp [filterMap, answers, h, ih]
  | effect _ _ ih => exact ih

theorem effects_filterMap (check : A → Option B) (trace : Trace A F E) :
    (trace.filterMap check).effects = trace.effects := by
  induction trace with
  | done | fault _ => rfl
  | answer a rest ih => cases h : check a <;> simp [filterMap, effects, h, ih]
  | effect event rest ih => simp [filterMap, effects, ih]

theorem fault_filterMap (check : A → Option B) (trace : Trace A F E) :
    (trace.filterMap check).terminalFault = trace.terminalFault := by
  induction trace with
  | done | fault _ => rfl
  | answer a rest ih => cases h : check a <;> simp [filterMap, terminalFault, h, ih]
  | effect _ _ ih => exact ih

theorem filterMap_pure_check (predicate : A → Bool) (trace : Trace A F E) :
    trace.filterMap (fun a => if predicate a then some a else none) = trace.filter predicate := by
  induction trace with
  | done | fault _ => rfl
  | answer a rest ih => cases h : predicate a <;> simp [filterMap, filter, h, ih]
  | effect event rest ih => simp [filterMap, filter, ih]

/-- Output checks preserve answer order and never multiply evidence. -/
theorem answers_sublist (predicate : A → Bool) (trace : Trace A F E) :
    (trace.filter predicate).answers.Sublist trace.answers := by
  rw [answers_filter]
  exact List.filter_sublist

theorem effects_filter (predicate : A → Bool) (trace : Trace A F E) :
    (trace.filter predicate).effects = trace.effects := by
  induction trace with
  | done | fault _ => rfl
  | answer a rest ih => cases h : predicate a <;> simp [filter, effects, h, ih]
  | effect event rest ih => simp [filter, effects, ih]

theorem fault_filter (predicate : A → Bool) (trace : Trace A F E) :
    (trace.filter predicate).terminalFault = trace.terminalFault := by
  induction trace with
  | done | fault _ => rfl
  | answer a rest ih => cases h : predicate a <;> simp [filter, terminalFault, h, ih]
  | effect _ _ ih => exact ih

theorem filter_establishes (predicate : A → Bool) (trace : Trace A F E) :
    AllAnswers predicate (trace.filter predicate) := by
  induction trace with
  | done | fault _ => trivial
  | answer a rest ih => cases h : predicate a <;> simp [filter, AllAnswers, h, ih]
  | effect _ _ ih => exact ih

theorem filter_idempotent (predicate : A → Bool) (trace : Trace A F E) :
    (trace.filter predicate).filter predicate = trace.filter predicate := by
  induction trace with
  | done | fault _ => rfl
  | answer a rest ih => cases h : predicate a <;> simp [filter, h, ih]
  | effect event rest ih => simp [filter, ih]

/-- This is an optimization law under an established invariant, not permission
to erase a check based only on a type annotation. -/
theorem established_check_erasable (predicate : A → Bool) (trace : Trace A F E)
    (established : AllAnswers predicate trace) : trace.filter predicate = trace := by
  induction trace with
  | done | fault _ => rfl
  | answer a rest ih =>
      simp only [AllAnswers] at established
      simp [filter, established.1, ih established.2]
  | effect event rest ih => simp [filter, ih established]

theorem no_check (trace : Trace A F E) : trace.filter (fun _ => true) = trace :=
  established_check_erasable _ trace (by
    induction trace <;> simp_all [AllAnswers])

end Trace

namespace Boundary

variable {W Input Output Fault Effect : Type}

abbrev Body (W Input Output Fault Effect : Type) :=
  W → Input → Trace (Output × W) Fault Effect

structure Contract (W Input Output : Type) where
  input : W → Input → Bool
  result : W → Input → Output → Bool

def call (contract : Contract W Input Output) (body : Body W Input Output Fault Effect)
    (world : W) (args : Input) : Trace (Output × W) Fault Effect :=
  if contract.input world args then
    (body world args).filter fun result => contract.result result.2 args result.1
  else .done

theorem rejected_input_does_not_enter_body (contract : Contract W Input Output)
    (body : Body W Input Output Fault Effect) (world : W) (args : Input)
    (rejected : contract.input world args = false) : call contract body world args = .done := by
  simp [call, rejected]

theorem result_sound (contract : Contract W Input Output)
    (body : Body W Input Output Fault Effect) (world : W) (args : Input) :
    Trace.AllAnswers (fun result => contract.result result.2 args result.1)
      (call contract body world args) := by
  unfold call
  split
  · exact Trace.filter_establishes _ _
  · trivial

theorem results_sublist (contract : Contract W Input Output)
    (body : Body W Input Output Fault Effect) (world : W) (args : Input) :
    (call contract body world args).answers.Sublist (body world args).answers := by
  unfold call
  split
  · exact Trace.answers_sublist _ _
  · exact List.nil_sublist _

theorem accepted_input_preserves_effects (contract : Contract W Input Output)
    (body : Body W Input Output Fault Effect) (world : W) (args : Input)
    (admitted : contract.input world args = true) :
    (call contract body world args).effects = (body world args).effects := by
  simp only [call, admitted, if_true]
  exact Trace.effects_filter _ _

theorem accepted_input_preserves_faults (contract : Contract W Input Output)
    (body : Body W Input Output Fault Effect) (world : W) (args : Input)
    (admitted : contract.input world args = true) :
    (call contract body world args).terminalFault = (body world args).terminalFault := by
  simp only [call, admitted, if_true]
  exact Trace.fault_filter _ _

/-- Absence of a declaration emits the original body itself. This is a code
identity in the model, not a measurement of a Prolog implementation. -/
def install (contract : Option (Contract W Input Output))
    (body : Body W Input Output Fault Effect) : Body W Input Output Fault Effect :=
  match contract with
  | none => body
  | some contract => call contract body

theorem undeclared_body_unchanged (body : Body W Input Output Fault Effect) :
    install none body = body := rfl

end Boundary

namespace StatefulBoundary

variable {W Input Output Fault Effect : Type}

/-- Checks may post delayed constraints in the logical state. They neither emit
language effects nor generate alternative executions of the equation body. -/
structure Contract (W Input Output : Type) where
  enter : W → Input → Option W
  leave : W → Input → Output → Option W

def Contract.ofPredicate (contract : Boundary.Contract W Input Output) :
    Contract W Input Output where
  enter world args := if contract.input world args then some world else none
  leave world args out := if contract.result world args out then some world else none

def checkedResult (contract : Contract W Input Output) (args : Input)
    (result : Output × W) : Option (Output × W) :=
  (contract.leave result.2 args result.1).map fun checkedWorld => (result.1, checkedWorld)

def call (contract : Contract W Input Output)
    (body : Boundary.Body W Input Output Fault Effect) (world : W) (args : Input) :
    Trace (Output × W) Fault Effect :=
  match contract.enter world args with
  | none => .done
  | some enteredWorld => (body enteredWorld args).filterMap (checkedResult contract args)

theorem rejected_input_does_not_enter_body (contract : Contract W Input Output)
    (body : Boundary.Body W Input Output Fault Effect) (world : W) (args : Input)
    (rejected : contract.enter world args = none) : call contract body world args = .done := by
  simp [call, rejected]

theorem admitted_input_preserves_effects (contract : Contract W Input Output)
    (body : Boundary.Body W Input Output Fault Effect) (world enteredWorld : W) (args : Input)
    (admitted : contract.enter world args = some enteredWorld) :
    (call contract body world args).effects = (body enteredWorld args).effects := by
  simp only [call, admitted]
  exact Trace.effects_filterMap _ _

theorem admitted_input_preserves_faults (contract : Contract W Input Output)
    (body : Boundary.Body W Input Output Fault Effect) (world enteredWorld : W) (args : Input)
    (admitted : contract.enter world args = some enteredWorld) :
    (call contract body world args).terminalFault = (body enteredWorld args).terminalFault := by
  simp only [call, admitted]
  exact Trace.fault_filterMap _ _

/-- Every returned value came from one body answer and passed its result check
in that answer's world; only the logical checking state may be updated. -/
theorem returned_result_checked (contract : Contract W Input Output)
    (body : Boundary.Body W Input Output Fault Effect) (world enteredWorld : W) (args : Input)
    (admitted : contract.enter world args = some enteredWorld)
    (value : Output) (afterWorld : W)
    (returned : (value, afterWorld) ∈ (call contract body world args).answers) :
    ∃ resultWorld, (value, resultWorld) ∈ (body enteredWorld args).answers ∧
      contract.leave resultWorld args value = some afterWorld := by
  simp only [call, admitted, Trace.answers_filterMap] at returned
  obtain ⟨⟨sourceValue, sourceWorld⟩, hs, checked⟩ := List.mem_filterMap.1 returned
  change (contract.leave sourceWorld args sourceValue).map
    (fun checkedWorld => (sourceValue, checkedWorld)) = some (value, afterWorld) at checked
  cases hc : contract.leave sourceWorld args sourceValue with
  | none => simp [hc] at checked
  | some checkedWorld =>
      simp only [hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at checked
      obtain ⟨rfl, rfl⟩ := checked
      exact ⟨sourceWorld, hs, hc⟩

/-- Resolved-value contracts are the state-preserving special case of posting
constraints, so the two interfaces have exactly the same observations there. -/
theorem predicate_special_case (contract : Boundary.Contract W Input Output)
    (body : Boundary.Body W Input Output Fault Effect) (world : W) (args : Input) :
    call (.ofPredicate contract) body world args = Boundary.call contract body world args := by
  have same : checkedResult (.ofPredicate contract) args =
      (fun result : Output × W => if contract.result result.2 args result.1 then some result else none) := by
    funext result
    simp only [checkedResult, Contract.ofPredicate]
    split <;> rfl
  by_cases h : contract.input world args = true
  · simp only [call, Contract.ofPredicate, h, if_true, Boundary.call]
    change (body world args).filterMap (checkedResult (.ofPredicate contract) args) = _
    rw [same, Trace.filterMap_pure_check]
  · simp [call, Contract.ofPredicate, h, Boundary.call]

def install (contract : Option (Contract W Input Output))
    (body : Boundary.Body W Input Output Fault Effect) : Boundary.Body W Input Output Fault Effect :=
  match contract with
  | none => body
  | some contract => call contract body

theorem undeclared_body_unchanged (body : Boundary.Body W Input Output Fault Effect) :
    install none body = body := rfl

end StatefulBoundary

end Mettapedia.Logic.ConstraintTypes
