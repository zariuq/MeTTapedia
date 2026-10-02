import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Filter
import Mathlib.Data.List.Forall2
import Mathlib.Tactic

/-!
# Retained foreign state versus reconstructing constraint calls

The reference keeps an event history and reconstructs all compatible valuations
at each call. The retained machine incrementally filters its current finite
solution store and keeps attributes keyed by stable variable identity. These
are independently operational representations of a pure finite-domain fragment:
unary bindings, relational equality/disequality, and inert attribute data.

Rejected operations leave the old state intact. Checkpoints, branch creation,
rollback, cancellation and cleanup lift the proved relation to branch-owned
sessions. The delayed-relation example posts a relation before either variable
is bound. Negative controls cover variable aliasing, dropped attributes and a
shared mutable store incorrectly used for two independent branches.

This is not a proof of SWI, its attributed-variable hooks, propagation timing,
foreign handles, thread affinity, or C allocation. A native bridge must realize
this ownership protocol and separately qualify any additional solver effects.
No claim about arbitrary CLP(FD) solving complexity follows from this model.
Enumerating finite valuations is an executable specification, not a proposed
production solver. Observations are solution sets and inert attribute lookup;
answer multiplicity, search order and residual-goal syntax are outside this model.
Relational equality constrains valuations; it does not merge variable identities
or execute attributed-variable merge hooks. Delayed relations are modeled by
their later observations, not by a hook wakeup schedule.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IncrementalConformance.ForeignState

universe u v w b

inductive Goal (Var : Type u) (Val : Type v) where
  | bind (keyVar : Var) (value : Val)
  | equal (left right : Var)
  | different (left right : Var)
  deriving DecidableEq

inductive Event (Var : Type u) (Val : Type v) (Attr : Type w) where
  | post (goal : Goal Var Val)
  | putAttribute (keyVar : Var) (payload : Attr)
  deriving DecidableEq

variable {Var : Type u} {Val : Type v} {Attr : Type w}
  [DecidableEq Var] [DecidableEq Val] [Fintype Var] [Fintype Val]

abbrev Valuation (Var : Type u) (Val : Type v) := Var → Val

/-- Each goal constrains the same stable variable identifiers across calls. -/
def Goal.accepts : Goal Var Val → Valuation Var Val → Bool
  | .bind keyVar value, valuation => decide (valuation keyVar = value)
  | .equal left right, valuation => decide (valuation left = valuation right)
  | .different left right, valuation => decide (valuation left ≠ valuation right)

def Event.accepts : Event Var Val Attr → Valuation Var Val → Bool
  | .post goal, valuation => goal.accepts valuation
  | .putAttribute _ _, _ => true

/-- Newest events are at the head; constraints are interpreted conjunctively. -/
def referenceSolutions (history : List (Event Var Val Attr)) : Finset (Valuation Var Val) :=
  Finset.univ.filter fun valuation => ∀ event ∈ history, event.accepts valuation = true

/-- Last-write attribute semantics is independently read from the history. -/
def referenceAttribute : List (Event Var Val Attr) → Var → Option Attr
  | [], _ => none
  | .post _ :: history, keyVar => referenceAttribute history keyVar
  | .putAttribute key value :: history, keyVar =>
      if keyVar = key then some value else referenceAttribute history keyVar

structure Retained (Var : Type u) (Val : Type v) (Attr : Type w) where
  solutions : Finset (Valuation Var Val)
  attributes : Var → Option Attr

def initial : Retained Var Val Attr := ⟨Finset.univ, fun _ => none⟩

def advance (event : Event Var Val Attr) (state : Retained Var Val Attr) :
    Retained Var Val Attr :=
  { solutions := state.solutions.filter fun valuation => event.accepts valuation = true
    attributes := match event with
      | .post _ => state.attributes
      | .putAttribute keyVar value => Function.update state.attributes keyVar (some value) }

/-- Comparison is between an input log and an incrementally maintained domain. -/
def Related (history : List (Event Var Val Attr)) (state : Retained Var Val Attr) : Prop :=
  state.solutions = referenceSolutions history ∧
    state.attributes = referenceAttribute history

theorem referenceSolutions_cons (event : Event Var Val Attr)
    (history : List (Event Var Val Attr)) :
    referenceSolutions (event :: history) =
      (referenceSolutions history).filter fun valuation => event.accepts valuation = true := by
  ext valuation
  simp [referenceSolutions, and_comm]

theorem initial_related : Related ([] : List (Event Var Val Attr)) initial := by
  simp [Related, initial, referenceSolutions, referenceAttribute]

theorem advance_related (event : Event Var Val Attr)
    {history : List (Event Var Val Attr)} {state : Retained Var Val Attr}
    (related : Related history state) : Related (event :: history) (advance event state) := by
  constructor
  · simp only [advance, related.1, referenceSolutions_cons]
  · cases event with
    | post goal => exact related.2
    | putAttribute key value =>
      funext keyVar
      change Function.update state.attributes key (some value) keyVar = _
      rw [related.2]
      simp only [Function.update_apply, referenceAttribute]

/-- Native observation reads its retained store; the reference rebuilds it. -/
theorem observe_related {history : List (Event Var Val Attr)}
    {state : Retained Var Val Attr} (related : Related history state)
    (valuation : Valuation Var Val) :
    valuation ∈ state.solutions ↔ ∀ event ∈ history, event.accepts valuation = true := by
  simp [related.1, referenceSolutions]

theorem attribute_related {history : List (Event Var Val Attr)}
    {state : Retained Var Val Attr} (related : Related history state) (keyVar : Var) :
    state.attributes keyVar = referenceAttribute history keyVar :=
  congrFun related.2 keyVar

/-- Reference calls reconstruct the whole candidate history before accepting. -/
def referenceCall (event : Event Var Val Attr) (history : List (Event Var Val Attr)) :
    Bool × List (Event Var Val Attr) :=
  if referenceSolutions (event :: history) = ∅ then (false, history)
  else (true, event :: history)

/-- The retained call checks its incrementally computed candidate domain. -/
def retainedCall (event : Event Var Val Attr) (state : Retained Var Val Attr) :
    Bool × Retained Var Val Attr :=
  let candidate := advance event state
  if candidate.solutions = ∅ then (false, state) else (true, candidate)

/-- Both success and rejection agree; a failed call preserves the prior state. -/
theorem call_related (event : Event Var Val Attr)
    {history : List (Event Var Val Attr)} {state : Retained Var Val Attr}
    (related : Related history state) :
    (referenceCall event history).1 = (retainedCall event state).1 ∧
      Related (referenceCall event history).2 (retainedCall event state).2 := by
  have candidate := advance_related event related
  simp only [referenceCall, retainedCall, candidate.1]
  split_ifs
  · exact ⟨rfl, related⟩
  · exact ⟨rfl, candidate⟩

omit [Fintype Val] in
theorem rejected_call_preserves (event : Event Var Val Attr) (state : Retained Var Val Attr)
    (rejected : (retainedCall event state).1 = false) :
    (retainedCall event state).2 = state := by
  simp only [retainedCall] at *
  split_ifs at *
  rfl

/-- Accepted and rejected calls can be mixed without breaking the simulation. -/
def referenceCalls : List (Event Var Val Attr) → List (Event Var Val Attr) →
    List Bool × List (Event Var Val Attr)
  | [], history => ([], history)
  | event :: rest, history =>
      let result := referenceCall event history
      let later := referenceCalls rest result.2
      (result.1 :: later.1, later.2)

def retainedCalls : List (Event Var Val Attr) → Retained Var Val Attr →
    List Bool × Retained Var Val Attr
  | [], state => ([], state)
  | event :: rest, state =>
      let result := retainedCall event state
      let later := retainedCalls rest result.2
      (result.1 :: later.1, later.2)

theorem calls_related (events : List (Event Var Val Attr))
    {history : List (Event Var Val Attr)} {state : Retained Var Val Attr}
    (related : Related history state) :
    (referenceCalls events history).1 = (retainedCalls events state).1 ∧
      Related (referenceCalls events history).2 (retainedCalls events state).2 := by
  induction events generalizing history state with
  | nil => exact ⟨rfl, related⟩
  | cons event rest ih =>
      obtain ⟨same, next⟩ := call_related event related
      obtain ⟨sameRest, final⟩ := ih next
      exact ⟨congrArg₂ List.cons same sameRest, final⟩

/-! Branch state uses value snapshots. A C representation may share immutable
nodes, but a mutable foreign handle cannot stand for two independently advancing
snapshots. The controls below show why this ownership condition is necessary. -/

structure Frame (State : Type*) where
  current : State
  checkpoints : List State

def Frame.checkpoint {State : Type*} (frame : Frame State) : Frame State :=
  ⟨frame.current, frame.current :: frame.checkpoints⟩

def Frame.rollback {State : Type*} (frame : Frame State) : Frame State :=
  match frame.checkpoints with
  | [] => frame
  | saved :: rest => ⟨saved, rest⟩

def Frame.call {State : Type*} (call : State → Bool × State) (frame : Frame State) :
    Bool × Frame State :=
  let result := call frame.current
  (result.1, ⟨result.2, frame.checkpoints⟩)

def FramesRelated (reference : Frame (List (Event Var Val Attr)))
    (retained : Frame (Retained Var Val Attr)) : Prop :=
  Related reference.current retained.current ∧
    List.Forall₂ Related reference.checkpoints retained.checkpoints

theorem checkpoint_related {reference : Frame (List (Event Var Val Attr))}
    {retained : Frame (Retained Var Val Attr)} (related : FramesRelated reference retained) :
    FramesRelated reference.checkpoint retained.checkpoint :=
  ⟨related.1, List.Forall₂.cons related.1 related.2⟩

theorem rollback_related {reference : Frame (List (Event Var Val Attr))}
    {retained : Frame (Retained Var Val Attr)} (related : FramesRelated reference retained) :
    FramesRelated reference.rollback retained.rollback := by
  obtain ⟨current, checkpoints⟩ := related
  cases reference with | mk rc rs =>
    cases retained with | mk nc ns =>
      cases checkpoints with
      | nil => exact ⟨current, .nil⟩
      | cons saved rest => exact ⟨saved, rest⟩

theorem frame_call_related (event : Event Var Val Attr)
    {reference : Frame (List (Event Var Val Attr))}
    {retained : Frame (Retained Var Val Attr)} (related : FramesRelated reference retained) :
    (reference.call (referenceCall event)).1 = (retained.call (retainedCall event)).1 ∧
      FramesRelated (reference.call (referenceCall event)).2
        (retained.call (retainedCall event)).2 := by
  obtain ⟨same, next⟩ := call_related event related.1
  exact ⟨same, next, related.2⟩

theorem checkpoint_rollback {State : Type*} (frame : Frame State) :
    frame.checkpoint.rollback = frame := by
  cases frame
  rfl

abbrev Sessions (Owner State : Type*) := Owner → Option (Frame State)

def SessionsRelated {Owner : Type b}
    (reference : Sessions Owner (List (Event Var Val Attr)))
    (retained : Sessions Owner (Retained Var Val Attr)) : Prop :=
  ∀ owner, Option.Rel FramesRelated (reference owner) (retained owner)

variable {Owner : Type b} [DecidableEq Owner]

/-- Starting a branch takes a separate semantic snapshot. Overwriting a live
owner is not admitted by `fork`; the caller must supply a fresh owner. -/
def fork {State : Type*} (sessions : Sessions Owner State) (source target : Owner) :
    Sessions Owner State :=
  if sessions target = none then Function.update sessions target (sessions source) else sessions

/-- Cancellation invalidates this owner; immutable snapshots of siblings remain. -/
def cancel {State : Type*} (sessions : Sessions Owner State) (owner : Owner) :
    Sessions Owner State := Function.update sessions owner none

def cleanup {State : Type*} : Sessions Owner State := fun _ => none

theorem cancel_related
    {reference : Sessions Owner (List (Event Var Val Attr))}
    {retained : Sessions Owner (Retained Var Val Attr)}
    (related : SessionsRelated reference retained) (owner : Owner) :
    SessionsRelated (cancel reference owner) (cancel retained owner) := by
  intro other
  by_cases same : other = owner
  · subst other
    simp [cancel]
  · simpa [cancel, Function.update_apply, same] using related other

theorem cancel_preserves_sibling {State : Type*} (sessions : Sessions Owner State)
    (owner sibling : Owner) (different : sibling ≠ owner) :
    cancel sessions owner sibling = sessions sibling := by
  simp [cancel, different]

theorem cancel_invalidates {State : Type*} (sessions : Sessions Owner State) (owner : Owner) :
    cancel sessions owner owner = none := by simp [cancel]

omit [DecidableEq Owner] in
theorem cleanup_related : SessionsRelated
    (cleanup : Sessions Owner (List (Event Var Val Attr)))
    (cleanup : Sessions Owner (Retained Var Val Attr)) := by
  intro owner
  exact .none

theorem fork_related
    {reference : Sessions Owner (List (Event Var Val Attr))}
    {retained : Sessions Owner (Retained Var Val Attr)}
    (related : SessionsRelated reference retained) (source target : Owner) :
    SessionsRelated (fork reference source target) (fork retained source target) := by
  have empty : reference target = none ↔ retained target = none := by
    have h := related target
    generalize hr : reference target = r at h ⊢
    generalize hn : retained target = n at h ⊢
    cases h <;> simp
  unfold fork
  by_cases fresh : reference target = none
  · simp only [if_pos fresh, if_pos (empty.mp fresh)]
    intro owner
    by_cases same : owner = target
    · subst owner
      simpa using related source
    · simpa [Function.update_apply, same] using related owner
  · simp only [if_neg fresh, if_neg (fun h => fresh (empty.mpr h))]
    exact related

/-- A local operation updates exactly one owner, not every handle with shared data. -/
def modify {State : Type*} (sessions : Sessions Owner State) (owner : Owner)
    (operation : Frame State → Frame State) : Sessions Owner State :=
  Function.update sessions owner ((sessions owner).map operation)

theorem modify_preserves_sibling {State : Type*} (sessions : Sessions Owner State)
    (owner sibling : Owner) (operation : Frame State → Frame State)
    (different : sibling ≠ owner) :
    modify sessions owner operation sibling = sessions sibling := by
  simp [modify, different]

/-- This generic lifting lemma is used only with the operation relations proved
above; the entire foreign execution simulation is not supplied as a hypothesis. -/
theorem modify_related
    {reference : Sessions Owner (List (Event Var Val Attr))}
    {retained : Sessions Owner (Retained Var Val Attr)}
    (related : SessionsRelated reference retained) (owner : Owner)
    (refOperation : Frame (List (Event Var Val Attr)) → Frame (List (Event Var Val Attr)))
    (nativeOperation : Frame (Retained Var Val Attr) → Frame (Retained Var Val Attr))
    (preserves : ∀ r n, FramesRelated r n → FramesRelated (refOperation r) (nativeOperation n)) :
    SessionsRelated (modify reference owner refOperation) (modify retained owner nativeOperation) := by
  intro other
  by_cases same : other = owner
  · subst other
    simp only [modify, Function.update_self]
    have h := related owner
    generalize hr : reference owner = r at h ⊢
    generalize hn : retained owner = n at h ⊢
    cases h with
    | none => exact .none
    | some h => exact .some (preserves _ _ h)
  · simpa [modify, Function.update_apply, same] using related other

inductive Command (Owner : Type b) (Var : Type u) (Val : Type v) (Attr : Type w) where
  | call (owner : Owner) (event : Event Var Val Attr)
  | checkpoint (owner : Owner)
  | rollback (owner : Owner)
  | fork (source target : Owner)
  | cancel (owner : Owner)
  | cleanup

/-- The lifecycle operations are shared; only execution of a foreign call differs. -/
def sessionStep {State : Type*} (call : Event Var Val Attr → State → Bool × State)
    (command : Command Owner Var Val Attr) (sessions : Sessions Owner State) :
    Sessions Owner State :=
  match command with
  | .call owner event => modify sessions owner fun frame => (frame.call (call event)).2
  | .checkpoint owner => modify sessions owner Frame.checkpoint
  | .rollback owner => modify sessions owner Frame.rollback
  | .fork source target => fork sessions source target
  | .cancel owner => cancel sessions owner
  | .cleanup => cleanup

theorem sessionStep_related (command : Command Owner Var Val Attr)
    {reference : Sessions Owner (List (Event Var Val Attr))}
    {retained : Sessions Owner (Retained Var Val Attr)}
    (related : SessionsRelated reference retained) :
    SessionsRelated (sessionStep referenceCall command reference)
      (sessionStep retainedCall command retained) := by
  cases command with
  | call owner event =>
      exact modify_related related owner _ _ fun _ _ h => (frame_call_related event h).2
  | checkpoint owner =>
      exact modify_related related owner _ _ fun _ _ h => checkpoint_related h
  | rollback owner =>
      exact modify_related related owner _ _ fun _ _ h => rollback_related h
  | fork source target => exact fork_related related source target
  | cancel owner => exact cancel_related related owner
  | cleanup => exact cleanup_related

def sessionRun {State : Type*} (call : Event Var Val Attr → State → Bool × State) :
    List (Command Owner Var Val Attr) → Sessions Owner State → Sessions Owner State
  | [], sessions => sessions
  | command :: rest, sessions => sessionRun call rest (sessionStep call command sessions)

/-- Arbitrary finite interleavings of calls and lifecycle actions preserve every
owner's observable constraint domain, attributes and rollback snapshots. -/
theorem sessionRun_related (commands : List (Command Owner Var Val Attr))
    {reference : Sessions Owner (List (Event Var Val Attr))}
    {retained : Sessions Owner (Retained Var Val Attr)}
    (related : SessionsRelated reference retained) :
    SessionsRelated (sessionRun referenceCall commands reference)
      (sessionRun retainedCall commands retained) := by
  induction commands generalizing reference retained with
  | nil => exact related
  | cons command rest ih => exact ih (sessionStep_related command related)

/-! Executable positive and negative controls. -/

namespace Controls

abbrev E := Event Bool Bool Nat
abbrev S := Retained Bool Bool Nat

def delayed : E := .post (.equal false true)
def bindLeft : E := .post (.bind false true)
def impossible : E := .post (.bind true false)
def attributed : E := .putAttribute false 42

theorem delayed_relation_survives_later_binding :
    (retainedCalls [delayed, bindLeft] (initial : S)).2.solutions =
      {fun _ => true} := by decide

theorem attribute_survives_later_calls :
    (retainedCalls [attributed, delayed, bindLeft] (initial : S)).2.attributes false = some 42 := by
  decide

theorem contradiction_rejected_without_corruption :
    let before := (retainedCalls [delayed, bindLeft] (initial : S)).2
    (retainedCall impossible before).1 = false ∧
      (retainedCall impossible before).2.solutions = before.solutions ∧
      (retainedCall impossible before).2.attributes false = before.attributes false := by decide

theorem rollback_restores_attributes_and_domains :
    let frame : Frame S := ⟨initial, []⟩
    let changed := (frame.checkpoint.call (retainedCall attributed)).2
    changed.rollback.current.solutions = Finset.univ ∧
      changed.rollback.current.attributes false = none := by decide

/-- Dropping inert attributes on boundary return already breaks readback. -/
theorem dropping_attributes_changes_observation :
    (retainedCalls [attributed, bindLeft] (initial : S)).2.attributes false ≠
      (initial : S).attributes false := by decide

/-- Collapsing two variable identifiers turns a satisfiable goal into failure. -/
theorem variable_aliasing_changes_satisfiability :
    (retainedCall (.post (.different false true)) (initial : S)).1 = true ∧
      (retainedCall (.post (.different false false)) (initial : S)).1 = false := by decide

/-- Both owners point to one mutable slot in this deliberately wrong realization. -/
def aliasedOwners : Bool → Bool := fun _ => false

def sharedHeap : Bool → S := fun _ => initial

def badAdvance (heap : Bool → S) (owner : Bool) (event : E) : Bool → S :=
  Function.update heap (aliasedOwners owner)
    (retainedCall event (heap (aliasedOwners owner))).2

theorem shared_mutable_alias_corrupts_sibling :
    (badAdvance sharedHeap false bindLeft (aliasedOwners true)).solutions ≠
      (sharedHeap (aliasedOwners true)).solutions := by decide

end Controls

end Mettapedia.Machines.IncrementalConformance.ForeignState
