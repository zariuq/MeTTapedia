import Mathlib.Data.List.Nodup

/-!
# Linked activation scopes

An activation writes its saved predecessor into the activated object's own
link. Leaving restores the saved top; it does not undo that link or any payload
updates. The active list is an independent specification of the reachable
chain. An object may be reused after leaving, but entering an already active
object is not a second activation record.

The finite traversal retains its cursor on exhaustion. A complete traversal
follows from the representation invariant, without imposing a runtime depth
bound. Payload ownership and physical pointer validity are separate contracts.
-/

set_option autoImplicit false

namespace Mettapedia.Machines

universe u

structure LinkedScopeStack (Identity : Type u) where
  top : Option Identity
  parent : Identity → Option Identity

namespace LinkedScopeStack

variable {Identity : Type u}

/-- Every active link names precisely the next active object. Links of
inactive objects are deliberately unconstrained. -/
def MatchesLinks (parent : Identity → Option Identity) : List Identity → Prop
  | [] => True
  | first :: rest => parent first = rest.head? ∧ MatchesLinks parent rest

structure Represents (stack : LinkedScopeStack Identity) (active : List Identity) : Prop where
  top : stack.top = active.head?
  distinct : active.Nodup
  links : MatchesLinks stack.parent active

theorem matchesLinks_congr {first second : Identity → Option Identity}
    {active : List Identity} (same : ∀ object ∈ active, first object = second object)
    (linked : MatchesLinks first active) : MatchesLinks second active := by
  induction active with
  | nil => trivial
  | cons object rest ih =>
      exact ⟨(same object List.mem_cons_self).symm.trans linked.1,
        ih (fun next member => same next (List.mem_cons_of_mem _ member)) linked.2⟩

def enter [DecidableEq Identity] (stack : LinkedScopeStack Identity)
    (object : Identity) : LinkedScopeStack Identity where
  top := some object
  parent := fun candidate => if candidate = object then stack.top else stack.parent candidate

def leave (stack : LinkedScopeStack Identity) (saved : Option Identity) :
    LinkedScopeStack Identity := { stack with top := saved }

theorem enter_represents [DecidableEq Identity]
    {stack : LinkedScopeStack Identity} {active : List Identity} {object : Identity}
    (represented : stack.Represents active) (fresh : object ∉ active) :
    (stack.enter object).Represents (object :: active) := by
  refine ⟨rfl, List.nodup_cons.mpr ⟨fresh, represented.distinct⟩, ?_⟩
  refine ⟨?_, matchesLinks_congr ?_ represented.links⟩
  · simp [enter, represented.top]
  · intro candidate member
    have different : candidate ≠ object := by
      intro same
      exact fresh (same ▸ member)
    simp [enter, different]

/-- A matching leave restores the original active chain, even though the
now inactive object's predecessor remains written. -/
theorem leave_enter_represents [DecidableEq Identity]
    {stack : LinkedScopeStack Identity} {active : List Identity} {object : Identity}
    (represented : stack.Represents active) (fresh : object ∉ active) :
    ((stack.enter object).leave stack.top).Represents active := by
  have pushed := enter_represents represented fresh
  exact ⟨represented.top, represented.distinct, pushed.links.2⟩

/-- A scope may leave its stack untouched. The independent list presentation
records an actual entry only when an object was selected. -/
def enterOptional [DecidableEq Identity] (stack : LinkedScopeStack Identity)
    (object : Option Identity) : LinkedScopeStack Identity :=
  match object with
  | none => stack
  | some identity => stack.enter identity

theorem enterOptional_represents [DecidableEq Identity]
    {stack : LinkedScopeStack Identity} {active : List Identity} (object : Option Identity)
    (represented : stack.Represents active)
    (fresh : ∀ identity, object = some identity → identity ∉ active) :
    (stack.enterOptional object).Represents (object.toList ++ active) := by
  cases object with
  | none => exact represented
  | some identity => exact enter_represents represented (fresh identity rfl)

/-- After a balanced body, restoring a saved top recovers the caller's active
chain. The body's inactive link writes remain in the implementation table. -/
theorem leave_after_body_represents [DecidableEq Identity]
    {caller after : LinkedScopeStack Identity} {active : List Identity} (object : Identity)
    (original : caller.Represents active)
    (balanced : after.Represents (object :: active)) :
    (after.leave caller.top).Represents active := by
  exact ⟨original.top, original.distinct, balanced.links.2⟩

/-- A bounded observation follows the links directly and retains the first
unvisited object. This is independent of the list specification. -/
def follow (parent : Identity → Option Identity) :
    Nat → Option Identity → List Identity × Option Identity
  | _, none => ([], none)
  | 0, some object => ([], some object)
  | fuel + 1, some object =>
      let rest := follow parent fuel (parent object)
      (object :: rest.1, rest.2)

theorem follow_of_matches {parent : Identity → Option Identity}
    {active : List Identity} (linked : MatchesLinks parent active) (extra : Nat) :
    follow parent (active.length + extra) active.head? = (active, none) := by
  induction active with
  | nil => cases extra <;> rfl
  | cons object rest ih =>
      have fuel : (object :: rest).length + extra = (rest.length + extra) + 1 := by
        simp only [List.length_cons]
        omega
      rw [fuel]
      simp only [List.head?_cons, follow]
      rw [linked.1, ih linked.2]

theorem follow_complete {stack : LinkedScopeStack Identity} {active : List Identity}
    (represented : stack.Represents active) (extra : Nat) :
    follow stack.parent (active.length + extra) stack.top = (active, none) := by
  rw [represented.top]
  exact follow_of_matches represented.links extra

theorem entering_top_makes_self_link [DecidableEq Identity]
    (stack : LinkedScopeStack Identity) (object : Identity)
    (active : stack.top = some object) :
    (stack.enter object).parent object = some object := by
  simp [enter, active]

theorem self_link_has_no_finite_representation
    {stack : LinkedScopeStack Identity} {object : Identity}
    (top : stack.top = some object) (self : stack.parent object = some object)
    (active : List Identity) : ¬ stack.Represents active := by
  intro represented
  cases active with
  | nil =>
      have impossible : (some object : Option Identity) = none :=
        top.symm.trans represented.top
      cases impossible
  | cons first rest =>
      have same : object = first := Option.some.inj (top.symm.trans represented.top)
      subst first
      have next : rest.head? = some object := represented.links.1.symm.trans self
      have member : object ∈ rest := by
        cases rest with
        | nil => simp at next
        | cons head tail =>
            have same : head = object := Option.some.inj next
            simp [same]
      exact (List.nodup_cons.mp represented.distinct).1 member

theorem reenter_top_refused [DecidableEq Identity]
    (stack : LinkedScopeStack Identity) (object : Identity)
    (active : stack.top = some object) (presentation : List Identity) :
    ¬ (stack.enter object).Represents presentation :=
  self_link_has_no_finite_representation rfl
    (entering_top_makes_self_link stack object active) presentation

theorem self_link_retains_cursor (parent : Identity → Option Identity)
    (object : Identity) (self : parent object = some object) (fuel : Nat) :
    follow parent fuel (some object) = (List.replicate fuel object, some object) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp [follow, self, ih, List.replicate_succ]

namespace Controls

def empty : LinkedScopeStack Nat := ⟨none, fun _ => none⟩

theorem empty_represents : empty.Represents [] := ⟨rfl, List.nodup_nil, trivial⟩

theorem nested_enter_and_leave :
    (((empty.enter 1).enter 2).leave (some 1)).Represents [1] := by
  exact leave_enter_represents (enter_represents empty_represents (by simp)) (by simp)

theorem retired_object_can_resume :
    ((((empty.enter 1).leave none).enter 1)).Represents [1] := by
  exact enter_represents (leave_enter_represents empty_represents (by simp)) (by simp)

theorem same_object_is_not_a_second_frame :
    ¬ ((empty.enter 1).enter 1).Represents [1, 1] := by
  exact reenter_top_refused (empty.enter 1) 1 rfl [1, 1]

theorem repeated_entry_never_completes (fuel : Nat) :
    follow ((empty.enter 1).enter 1).parent fuel (some 1) =
      (List.replicate fuel 1, some 1) :=
  self_link_retains_cursor ((empty.enter 1).enter 1).parent 1 (by simp [enter]) fuel

end Controls

namespace Activation

universe v w x

variable {Channel : Type u} {Identity : Channel → Type v}
variable {Context : Type w} {Store : Type x}

/-- Saved dynamic fields and persistent service state are separate. Each
channel has its own intrusive scope chain. The external depth is a collection
barrier; neither the depth nor the saved context is a storage lease. -/
structure State (Channel : Type u) (Identity : Channel → Type v)
    (Context : Type w) (Store : Type x) where
  context : Context
  scopes : (channel : Channel) → LinkedScopeStack (Identity channel)
  externalDepth : Nat
  store : Store

structure Guard (Channel : Type u) (Identity : Channel → Type v) (Context : Type w) where
  context : Context
  tops : (channel : Channel) → Option (Identity channel)
  selected : Channel → Bool

/-- The reference uses active lists, independently of physical predecessor
links. Its service state is the complete supplied store, not a cost erasure. -/
structure Reference (Channel : Type u) (Identity : Channel → Type v)
    (Context : Type w) (Store : Type x) where
  context : Context
  active : (channel : Channel) → List (Identity channel)
  externalDepth : Nat
  store : Store

structure Related (state : State Channel Identity Context Store)
    (reference : Reference Channel Identity Context Store) : Prop where
  context : state.context = reference.context
  scopes : ∀ channel, (state.scopes channel).Represents (reference.active channel)
  externalDepth : state.externalDepth = reference.externalDepth
  store : state.store = reference.store

def save (selected : (channel : Channel) → Option (Identity channel))
    (caller : State Channel Identity Context Store) : Guard Channel Identity Context where
  context := caller.context
  tops := fun channel => (caller.scopes channel).top
  selected := fun channel => (selected channel).isSome

def enter [∀ channel, DecidableEq (Identity channel)]
    (selected : (channel : Channel) → Option (Identity channel)) (context : Context)
    (caller : State Channel Identity Context Store) : State Channel Identity Context Store where
  context := context
  scopes := fun channel => (caller.scopes channel).enterOptional (selected channel)
  externalDepth := caller.externalDepth + 1
  store := caller.store

/-- Only entered channels restore a saved top. Persistent service state and
all predecessor tables come from the body poststate. -/
def leave (guard : Guard Channel Identity Context)
    (after : State Channel Identity Context Store) : State Channel Identity Context Store where
  context := guard.context
  scopes := fun channel => if guard.selected channel then
    (after.scopes channel).leave (guard.tops channel) else after.scopes channel
  externalDepth := after.externalDepth - 1
  store := after.store

def enterReference (selected : (channel : Channel) → Option (Identity channel))
    (context : Context) (caller : Reference Channel Identity Context Store) :
    Reference Channel Identity Context Store where
  context := context
  active := fun channel => (selected channel).toList ++ caller.active channel
  externalDepth := caller.externalDepth + 1
  store := caller.store

def leaveReference (selected : (channel : Channel) → Option (Identity channel))
    (caller after : Reference Channel Identity Context Store) :
    Reference Channel Identity Context Store where
  context := caller.context
  active := fun channel => if (selected channel).isSome then
    caller.active channel else after.active channel
  externalDepth := after.externalDepth - 1
  store := after.store

theorem enter_related [∀ channel, DecidableEq (Identity channel)]
    (selected : (channel : Channel) → Option (Identity channel)) (context : Context)
    {caller : State Channel Identity Context Store}
    {reference : Reference Channel Identity Context Store} (related : Related caller reference)
    (fresh : ∀ channel identity,
      selected channel = some identity → identity ∉ reference.active channel) :
    Related (enter selected context caller) (enterReference selected context reference) := by
  refine ⟨rfl, ?_, congrArg (· + 1) related.externalDepth, related.store⟩
  intro channel
  exact enterOptional_represents _ (related.scopes channel) (fresh channel)

/-- A body comparison supplies its own poststate. For an entered channel,
balanced scope nesting is required to recover the caller chain; no inactive
link equality or service-state rollback is assumed. -/
theorem leave_related [∀ channel, DecidableEq (Identity channel)]
    (selected : (channel : Channel) → Option (Identity channel))
    {caller after : State Channel Identity Context Store}
    {reference post : Reference Channel Identity Context Store}
    (original : Related caller reference) (body : Related after post)
    (balanced : ∀ channel identity, selected channel = some identity →
      post.active channel = identity :: reference.active channel) :
    Related (leave (save selected caller) after) (leaveReference selected reference post) := by
  refine ⟨original.context, ?_, congrArg (· - 1) body.externalDepth, body.store⟩
  intro channel
  cases choice : selected channel with
  | none => simpa [leave, save, leaveReference, choice] using body.scopes channel
  | some identity =>
      have inside : (after.scopes channel).Represents
          (identity :: reference.active channel) := by
        rw [← balanced channel identity choice]
        exact body.scopes channel
      simpa [leave, save, leaveReference, choice] using
        leave_after_body_represents identity (original.scopes channel) inside

theorem leave_keeps_poststore (guard : Guard Channel Identity Context)
    (after : State Channel Identity Context Store) : (leave guard after).store = after.store := rfl

/-- Depth restoration needs balanced body barriers. Merely entering a guard
does not license dropping a body-created barrier or acquiring storage. -/
theorem leave_balanced_depth (selected : (channel : Channel) → Option (Identity channel))
    (caller after : State Channel Identity Context Store)
    (balanced : after.externalDepth = caller.externalDepth + 1) :
    (leave (save selected caller) after).externalDepth = caller.externalDepth := by
  simp [leave, balanced]

def run [∀ channel, DecidableEq (Identity channel)] {Answer : Type*}
    (selected : (channel : Channel) → Option (Identity channel)) (context : Context)
    (body : State Channel Identity Context Store → Answer × State Channel Identity Context Store)
    (caller : State Channel Identity Context Store) : Answer × State Channel Identity Context Store :=
  let after := body (enter selected context caller)
  (after.1, leave (save selected caller) after.2)

def runReference {Answer : Type*}
    (selected : (channel : Channel) → Option (Identity channel)) (context : Context)
    (body : Reference Channel Identity Context Store →
      Answer × Reference Channel Identity Context Store)
    (caller : Reference Channel Identity Context Store) :
    Answer × Reference Channel Identity Context Store :=
  let after := body (enterReference selected context caller)
  (after.1, leaveReference selected caller after.2)

/-- This is a composition rule for separately compared bodies. Answers and
the complete poststore are retained. The entry comparison follows links;
the independent reference prepends lists. -/
theorem run_correspondence [∀ channel, DecidableEq (Identity channel)] {Answer : Type*}
    (selected : (channel : Channel) → Option (Identity channel)) (context : Context)
    (body : State Channel Identity Context Store → Answer × State Channel Identity Context Store)
    (referenceBody : Reference Channel Identity Context Store →
      Answer × Reference Channel Identity Context Store)
    {caller : State Channel Identity Context Store}
    {reference : Reference Channel Identity Context Store} (related : Related caller reference)
    (fresh : ∀ channel identity,
      selected channel = some identity → identity ∉ reference.active channel)
    (bodyComparison : ∀ state reference, Related state reference →
      (body state).1 = (referenceBody reference).1 ∧
        Related (body state).2 (referenceBody reference).2)
    (balanced : ∀ channel identity, selected channel = some identity →
      (referenceBody (enterReference selected context reference)).2.active channel =
        identity :: reference.active channel) :
    (run selected context body caller).1 = (runReference selected context referenceBody reference).1 ∧
      Related (run selected context body caller).2
        (runReference selected context referenceBody reference).2 := by
  have compared := bodyComparison _ _ (enter_related selected context related fresh)
  exact ⟨compared.1, leave_related selected related compared.2 balanced⟩

/-- A bounded post-return traversal sees the caller's active list, despite
retained writes to inactive objects. -/
theorem leave_follow [∀ channel, DecidableEq (Identity channel)]
    (selected : (channel : Channel) → Option (Identity channel))
    {caller after : State Channel Identity Context Store}
    {reference post : Reference Channel Identity Context Store}
    (original : Related caller reference) (body : Related after post)
    (balanced : ∀ channel identity, selected channel = some identity →
      post.active channel = identity :: reference.active channel)
    (channel : Channel) (extra : Nat) :
    let result := leave (save selected caller) after
    let expected := leaveReference selected reference post
    follow (result.scopes channel).parent ((expected.active channel).length + extra)
      (result.scopes channel).top = (expected.active channel, none) := by
  exact follow_complete ((leave_related selected original body balanced).scopes channel) extra

namespace Controls

abbrev TestState := State Bool (fun _ => Nat) (Option Nat) (List Nat)

def caller : TestState := ⟨some 7, fun _ => LinkedScopeStack.Controls.empty, 4, []⟩
def outer : Bool → Option Nat := fun channel => if channel then none else some 1
def inner : Bool → Option Nat := fun channel => if channel then some 3 else some 2
def recordContext (state : TestState) : Option Nat × TestState :=
  (state.context, { state with store := state.store ++ state.context.toList })

theorem nested_retains_effects_and_caller :
    let result := run outer (some 1)
      (fun active =>
        let first := recordContext active
        let middle := run inner (some 2) recordContext first.2
        recordContext middle.2) caller
    result.1 = some 1 ∧ result.2.context = caller.context ∧
      result.2.store = [1, 2, 1] ∧ result.2.externalDepth = 4 ∧
      (result.2.scopes false).top = none ∧ (result.2.scopes true).top = none := by
  decide

/-- Capturing an empty context replaces the ambient value. Interpreting empty
as an overlay would expose the caller instead. -/
theorem empty_capture_is_not_overlay :
    (run outer none recordContext caller).1 = none ∧
      (run outer (none.or caller.context) recordContext caller).1 = some 7 := by
  decide

theorem returned_links_are_not_rolled_back :
    let result := run outer (some 1)
      (fun active => run inner (some 2) recordContext active) caller
    (result.2.scopes false).parent 2 = some 1 ∧
      (caller.scopes false).parent 2 = none ∧ result.2.store = [2] := by
  decide

theorem rolling_back_store_loses_work :
    (run outer (some 1) recordContext caller).2.store ≠ caller.store := by decide

theorem unbalanced_barrier_is_visible :
    let result := run outer (some 1)
      (fun active => ((), { active with externalDepth := active.externalDepth + 1 })) caller
    result.2.externalDepth = 5 ∧ result.2.externalDepth ≠ caller.externalDepth := by decide

end Controls
end Activation
end LinkedScopeStack
end Mettapedia.Machines
