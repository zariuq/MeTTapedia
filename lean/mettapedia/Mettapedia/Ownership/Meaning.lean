import Mettapedia.Ownership.Frame

/-!
# What ownership admission guarantees

The guarantees of an admitted function and of an admitted module, stated as
definitions, and the theorems that admission gives them.

For an admitted function and every state its plan reaches from the initial
state (`Guarantees`):

* the state satisfies the separation invariant `Valid`;
* a write through one loan is disjoint from every access through another;
* every region a step names is static storage, only read; an input's storage,
  within the extent and the right its parameter declares; or an allocation of
  the function's own (`Frame.Reach`);
* no finished execution faults, and a returned one meets its result contract.

For an admitted module (`ModuleGuarantees`), every member has these guarantees,
and at every call of a member a caller loan the call does not lend is kept and
is disjoint from every callee region placed in the caller wherever either side
may write.

Admission is a statement about the plan. That a compiled run of the function
performs its storage operations as steps of its plan is `FollowsPlan`: a
definition, not a theorem of this model. It is the evidence of the native
checker, the C ABI and the compiler tests, and `follows_plan_reach` is how that
evidence composes with admission.
-/

set_option autoImplicit false

namespace Mettapedia.Ownership

open Mettapedia.Machines.CMemory.Borrowing
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.PermissionFlow
open Frame

/-- Every state an execution of `f`'s plan reaches from the initial state is
valid; admission is not needed, since every enabled step keeps the invariant. -/
theorem reachable_valid {callables : List Callable} {f : Function} {s : State}
    (path : Prefix (enabled callables f) f.body initial s) : Valid s :=
  path.invariant (fun _ _ _ step valid => enabled_valid step valid) initial_valid

/-- An enabled access is the access the loans allow, and changes nothing. -/
theorem enabled_access {callables : List Callable} {f : Function} {s next : State} {id : Nat}
    {x : Region} {writing : Bool} (step : enabled callables f s (.access id x writing) = some next) :
    Access s.loans id x writing ∧ next = s := by
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp step
  have moved := apply_transition (by simpa only [enabledCore] using h)
  obtain ⟨_, allowed, same⟩ := Option.bind_eq_some_iff.mp moved
  exact ⟨require_access allowed, (Option.some.inj same).symm⟩

/-- What admission guarantees for one function, at every state its plan reaches. -/
structure Guarantees (callables : List Callable) (f : Function) : Prop where
  /-- Every reachable state satisfies the separation invariant. -/
  valid : ∀ {s : State}, Prefix (enabled callables f) f.body initial s → Valid s
  /-- A write through one loan is disjoint from every access through another. -/
  writeAlone : ∀ {s next : State} {id other : Nat} {x y : Region} {writing : Bool},
    Prefix (enabled callables f) f.body initial s →
    enabled callables f s (.access id x true) = some next → id ≠ other →
    Access s.loans other y writing → x.Disjoint y
  /-- Every region a step names is within the function's reach. -/
  reach : ∀ {s next : State} {a : Action} {x : Region} {writing : Bool},
    Prefix (enabled callables f) f.body initial s → enabled callables f s a = some next →
    (x, writing) ∈ named a → Reach f s x writing
  /-- No finished execution faults. -/
  noFault : ∀ {outcome : Exit State}, Execution (enabled callables f) f.body initial outcome →
    outcome.kind ≠ .fault
  /-- A returned execution meets the function's result contract. -/
  returns : ∀ {outcome : Exit State}, Execution (enabled callables f) f.body initial outcome →
    outcome.kind = .returned → returnAllowed f.result outcome.state = true

theorem admitted_guarantees {callables : List Callable} {f : Function}
    (admitted : admitFunction callables f = true) : Guarantees callables f where
  valid := reachable_valid
  writeAlone := fun path step different reader =>
    exclusive_access_disjoint (reachable_valid path).ordered different (enabled_access step).1 reader
  reach := fun path step mem => admitted_reach admitted path step mem
  noFault := fun execution => (admitted_execution_safe admitted execution).1
  returns := fun execution returned => admitted_return_contract admitted execution returned

/-- What admission guarantees for a module: each member's guarantees, and the
caller-side frame at every call of a member. -/
structure ModuleGuarantees (m : Module) : Prop where
  members : ∀ {f : Function}, f ∈ m.functions → Guarantees m.callables f
  callFrame : ∀ {g f : Function}, f ∈ m.functions →
    ∀ {s after : State} {arguments : List Argument},
    Prefix (enabled m.callables g) g.body initial s →
    enabled m.callables g s (.invoke f.name arguments) = some after →
    ∀ {o : Loan}, o ∈ s.loans → o.id ∉ lentLoans arguments →
    o ∈ after.loans ∧
    ∀ {t : State}, Prefix (enabled m.callables f) f.body initial t →
      ∀ {l : Loan}, l ∈ t.loans → ∀ {placed : Region}, Placed f s arguments l.region placed →
        ∀ {R : Region} {writing : Bool}, Access s.loans o.id R writing →
          (l.mode = .exclusive ∨ writing = true) → placed.Disjoint R

theorem admitted_module_guarantees {m : Module} (admitted : admit m = true) :
    ModuleGuarantees m where
  members := fun member => admitted_guarantees (module_member_admitted admitted member)
  callFrame := by
    intro _ _ member _ _ _ reached step _ kept unpassed
    exact module_call_frame admitted member reached step kept unpassed

/-- The boundary of the model. A run of `f` follows its plan when each storage
operation it performs, read as an action, is enabled at a state the plan reaches.
Admission does not prove that a compiled run follows its plan; that is the
native checker's, the C ABI's and the compiler tests' evidence. -/
def FollowsPlan (callables : List Callable) (f : Function) (operations : List (State × Action)) :
    Prop :=
  ∀ operation ∈ operations, Prefix (enabled callables f) f.body initial operation.1 ∧
    (enabled callables f operation.1 operation.2).isSome

/-- With that evidence, every region a run of an admitted function touches is
within its reach. -/
theorem follows_plan_reach {callables : List Callable} {f : Function}
    (admitted : admitFunction callables f = true) {operations : List (State × Action)}
    (follows : FollowsPlan callables f operations) {operation : State × Action}
    (mem : operation ∈ operations) {x : Region} {writing : Bool}
    (touched : (x, writing) ∈ named operation.2) : Reach f operation.1 x writing := by
  obtain ⟨path, enabledThere⟩ := follows operation mem
  obtain ⟨next, step⟩ := Option.isSome_iff_exists.mp enabledThere
  exact (admitted_guarantees admitted).reach path step touched

end Mettapedia.Ownership
