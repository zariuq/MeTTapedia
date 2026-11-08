import Mathlib.Data.List.Basic

/-!
# Effective scoped grammar updates

The state retains local boundaries, scoped registrations, active namespaces
and the effective value at every saved scope. Global updates reach saved
frames; local updates stop at the first explicit local boundary. Registering
a scoped entry and activating its namespace are separate operations.

An adapter supplies the entry interpretation. The reference activation policy
also exposes whether an existing scoped bucket establishes a local boundary;
that policy must be qualified for a host release.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ScopedGrammarState

universe u v w

structure Frame (Context : Type u) (Value : Type v) where
  value : Value
  context : Context
  delimitsLocal : Bool := true
  deriving DecidableEq, Repr

namespace Frames

variable {Context : Type u} {Value : Type v} {Entry : Type w}

def push : List (Frame Context Value) → List (Frame Context Value)
  | [] => []
  | top :: rest => { top with delimitsLocal := true } :: top :: rest

def pop : List (Frame Context Value) → List (Frame Context Value)
  | _ :: next :: rest => next :: rest
  | frames => frames

def setDelimits : Nat → List (Frame Context Value) → List (Frame Context Value)
  | 0, frames => frames
  | _ + 1, [] => []
  | count + 1, top :: rest => { top with delimitsLocal := false } :: setDelimits count rest

def localUpdate (add : Value → Entry → Value) (entry : Entry) :
    List (Frame Context Value) → List (Frame Context Value)
  | [] => []
  | top :: rest => { top with value := add top.value entry } ::
      (if top.delimitsLocal then rest else localUpdate add entry rest)

def globalUpdate (add : Value → Entry → Value) (entry : Entry) (frames : List (Frame Context Value)) :
    List (Frame Context Value) := frames.map fun frame => { frame with value := add frame.value entry }

theorem pop_push (frames : List (Frame Context Value)) : pop (push frames) = frames := by
  cases frames <;> rfl

theorem local_push_pop (add : Value → Entry → Value) (entry : Entry) (frames : List (Frame Context Value)) :
    pop (localUpdate add entry (push frames)) = frames := by
  cases frames <;> rfl

theorem global_push_pop (add : Value → Entry → Value) (entry : Entry) (frames : List (Frame Context Value)) :
    pop (globalUpdate add entry (push frames)) = globalUpdate add entry frames := by
  cases frames <;> rfl

theorem local_crosses_implicit (add : Value → Entry → Value) (entry : Entry)
    (top next : Frame Context Value) (rest : List (Frame Context Value))
    (implicit : top.delimitsLocal = false) :
    pop (localUpdate add entry (top :: next :: rest)) = localUpdate add entry (next :: rest) := by
  simp [localUpdate, implicit, pop]

theorem local_keeps_contexts (add : Value → Entry → Value) (entry : Entry)
    (frames : List (Frame Context Value)) :
    (localUpdate add entry frames).map (·.context) = frames.map (·.context) := by
  induction frames with
  | nil => rfl
  | cons top rest ih => cases boundary : top.delimitsLocal <;> simp [localUpdate, boundary, ih]

end Frames

inductive Entry (Namespace : Type u) (Rule : Type v) where
  | global (rule : Rule)
  | scoped (scopeName : Namespace) (rule : Rule)
  deriving DecidableEq, Repr

structure State (Namespace : Type u) (Rule : Type v) (Value : Type w) where
  frames : List (Frame (List Namespace) Value)
  registry : Namespace → Option (List Rule)
  published : List (Entry Namespace Rule) := []

variable {Namespace : Type u} {Rule : Type v} {Value : Type w} [DecidableEq Namespace]

def initial (value : Value) : State Namespace Rule Value :=
  ⟨[⟨value, [], true⟩], fun _ => none, []⟩

def active (scopeName : Namespace) (frame : Frame (List Namespace) Value) : Bool :=
  frame.context.any fun name => decide (name = scopeName)

theorem active_eq_membership (scopeName : Namespace) (frame : Frame (List Namespace) Value) :
    active scopeName frame = decide (scopeName ∈ frame.context) := by
  apply Bool.eq_iff_iff.mpr
  simp [active]

def register (add : Value → Rule → Value) (entry : Entry Namespace Rule)
    (state : State Namespace Rule Value) : State Namespace Rule Value :=
  match entry with
  | .global rule =>
      { state with
        frames := Frames.globalUpdate add rule state.frames
        published := state.published ++ [entry] }
  | .scoped scopeName rule =>
      let entries := (state.registry scopeName).getD [] ++ [rule]
      { state with
        frames := state.frames.map fun frame =>
          if active scopeName frame then { frame with value := add frame.value rule } else frame
        registry := fun name => if name = scopeName then some entries else state.registry name
        published := state.published ++ [entry] }

def localEntry (add : Value → Rule → Value) (rule : Rule)
    (state : State Namespace Rule Value) : State Namespace Rule Value :=
  { state with frames := Frames.localUpdate add rule state.frames }

def push (state : State Namespace Rule Value) : State Namespace Rule Value :=
  { state with frames := Frames.push state.frames }

def pop (state : State Namespace Rule Value) : State Namespace Rule Value :=
  { state with frames := Frames.pop state.frames }

def delimit (count : Nat) (state : State Namespace Rule Value) : State Namespace Rule Value :=
  { state with frames := Frames.setDelimits count state.frames }

/-- The policy is explicit because source implementations may reset the local
boundary when activation finds a registered bucket, including an empty one. -/
def activate (resetBoundary : Bool) (add : Value → Rule → Value) (scopeName : Namespace)
    (state : State Namespace Rule Value) : State Namespace Rule Value :=
  match state.frames with
  | [] => state
  | top :: rest =>
      if active scopeName top then state else
        let context := scopeName :: top.context
        let next := match state.registry scopeName with
          | none => { top with context }
          | some entries =>
              { value := entries.foldl add top.value, context,
                delimitsLocal := if resetBoundary then true else top.delimitsLocal }
        { state with frames := next :: rest }

def imports (finish : Value → Value) (add : Value → Rule → Value) (base : Value)
    (entries : List (Entry Namespace Rule)) : State Namespace Rule Value :=
  let installed := entries.foldl (fun state entry => register add entry state) (initial base)
  { installed with
    frames := installed.frames.map (fun frame => { frame with value := finish frame.value })
    published := [] }

omit [DecidableEq Namespace] in
theorem local_keeps_published (add : Value → Rule → Value) (rule : Rule)
    (state : State Namespace Rule Value) : (localEntry add rule state).published = state.published := rfl

omit [DecidableEq Namespace] in
theorem local_scope_restored (add : Value → Rule → Value) (rule : Rule)
    (state : State Namespace Rule Value) : pop (localEntry add rule (push state)) = state := by
  cases state
  simp [pop, localEntry, push, Frames.local_push_pop]

theorem global_survives_scope (add : Value → Rule → Value) (rule : Rule)
    (state : State Namespace Rule Value) :
    pop (register add (.global rule) (push state)) = register add (.global rule) state := by
  cases state
  simp [pop, register, push, Frames.global_push_pop]

theorem activate_idempotent (resetBoundary : Bool) (add : Value → Rule → Value) (scopeName : Namespace)
    (state : State Namespace Rule Value) :
    activate resetBoundary add scopeName (activate resetBoundary add scopeName state) =
      activate resetBoundary add scopeName state := by
  cases frames : state.frames with
  | nil => simp [activate, frames]
  | cons top rest =>
      cases enabled : active scopeName top
      · have missing : scopeName ∉ top.context := by simpa [active_eq_membership] using enabled
        cases found : state.registry scopeName <;> simp [activate, frames, found, active_eq_membership, missing]
      · simp [activate, frames, enabled]

namespace Controls

def add (values : List Nat) (entry : Nat) := values ++ [entry]
def base : State String Nat (List Nat) := initial []
def observe (state : State String Nat (List Nat)) : List (List Nat) := state.frames.map (·.value)

theorem local_does_not_enter_persistent_log :
    (localEntry add 7 base).published = base.published ∧ observe (localEntry add 7 base) ≠ observe base := by
  decide

theorem scoped_registration_waits_for_activation :
    observe (register add (.scoped "notation" 7) base) = [[]] ∧
    observe (activate true add "notation" (register add (.scoped "notation" 7) base)) = [[7]] := by
  decide

theorem later_scoped_entry_reaches_active_frame :
    observe (register add (.scoped "notation" 8)
      (activate true add "notation" (register add (.scoped "notation" 7) base))) = [[7, 8]] := by decide

theorem implicit_frame_does_not_hide_local_entry :
    observe (pop (localEntry add 7 (delimit 1 (push (push base))))) = [[7], []] := by decide

theorem explicit_outer_boundary_still_restores :
    observe (pop (pop (localEntry add 7 (delimit 1 (push (push base)))))) = [[]] := by decide

theorem imported_entries_are_effective_without_becoming_new_exports :
    let imported := imports id add ([] : List Nat) [.global 3, .scoped "notation" 7]
    imported.published = [] ∧ observe imported = [[3]] ∧
      observe (activate true add "notation" imported) = [[3, 7]] := by decide

theorem empty_bucket_has_a_distinct_activation_effect :
    let implicitState := delimit 1 (push base)
    let emptyRegistered := { implicitState with
      registry := fun name => if name = "notation" then some ([] : List Nat) else none }
    ((activate true add "notation" implicitState).frames.head?).map (·.delimitsLocal) = some false ∧
      ((activate true add "notation" emptyRegistered).frames.head?).map (·.delimitsLocal) = some true := by decide

end Controls

end Mettapedia.GSLT.Parsing.ScopedGrammarState
