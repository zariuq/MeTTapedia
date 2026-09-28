import Mettapedia.GSLT.Dynamics.RepresentationSwitching

/-!
# Context-indexed residual execution across representations

The general carrier is an immutable family of templates, a current store
indexed by full activation keys, an ordered frontier of occurrence identities,
and an output trace. No process calculus or MeTTa dialect defines it.

A prepared kernel supplies code and its independent executor. Its correctness
law is local to one context instantiation. The theorems below lift that law to
indexed cursors, environment changes, cancellation, and arbitrarily switching
Region/Hole execution. Pending values are never snapshotted: each occurrence
reads the current store when executed. Source templates and prepared code are
immutable during a route; replacing a program requires a new certified route.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ContextIndexedSwitching

open RegionHolePlan RepresentationSwitching OrderedOccurrenceBodyAlgebra
open Mettapedia.GraphTheory.Representation

/-- A staged implementation of one context family. The prepared inventory is
supplied before execution; an executor does not compile on each read. -/
structure Kernel (Coordinate Value : Type) where
  Code : Type
  source : Nat → (Coordinate → Value) → Value
  prepared : Nat → Code
  execute : Code → (Coordinate → Value) → Value
  correct : ∀ index env, execute (prepared index) env = source index env

variable {Coordinate Value : Type}

/-! ## Complete residual states -/

/-- Coordinates include a generation; a recycled handle alone is not an
activation identity. This mathematical key does not specify a bit packing. -/
structure ActivationKey where
  handle : Nat
  generation : Nat
  deriving DecidableEq, Repr

abbrev Store (Coordinate Value : Type) := ActivationKey → Coordinate → Value

structure Job where
  activation : ActivationKey
  template : Nat
  occurrence : Nat
  deriving DecidableEq, Repr

structure Published (Value : Type) where
  activation : ActivationKey
  occurrence : Nat
  value : Value
  deriving DecidableEq, Repr

structure TreeState (Coordinate Value : Type) where
  store : Store Coordinate Value
  pending : List Job
  published : List (Published Value)

structure IndexedState (Coordinate Value : Type) where
  store : Store Coordinate Value
  frontier : Array Job
  cursor : Nat
  published : List (Published Value)

def decode (state : IndexedState Coordinate Value) : TreeState Coordinate Value :=
  ⟨state.store, state.frontier.toList.drop state.cursor, state.published⟩

def encode (state : TreeState Coordinate Value) : IndexedState Coordinate Value :=
  ⟨state.store, state.pending.toArray, 0, state.published⟩

@[simp] theorem decode_encode (state : TreeState Coordinate Value) : decode (encode state) = state := by
  cases state
  simp [decode, encode]

/-- Release the consumed prefix when the ownership regime permits replacing
the frontier. This reconstructs a smaller array, not the original raw state. -/
def compact (state : IndexedState Coordinate Value) : IndexedState Coordinate Value :=
  encode (decode state)

@[simp] theorem decode_compact (state : IndexedState Coordinate Value) :
    decode (compact state) = decode state := decode_encode _

theorem compact_frontier_size (state : IndexedState Coordinate Value) :
    (compact state).frontier.size = state.frontier.size - state.cursor := by
  simp [compact, encode, decode]

/-- Source and destination coexist during a persistent frontier conversion.
The consumed prefix still occupies source cells until that source is released. -/
def compactPeak (state : IndexedState Coordinate Value) (temporary : Nat) : Nat :=
  persistentPeak state.frontier.size (compact state).frontier.size temporary

theorem compact_peak_exact (state : IndexedState Coordinate Value) (temporary : Nat) :
    compactPeak state temporary =
      state.frontier.size + (state.frontier.size - state.cursor) + temporary := by
  simp [compactPeak, persistentPeak, compact_frontier_size]

def treeStep (program : Kernel Coordinate Value) (state : TreeState Coordinate Value) : TreeState Coordinate Value :=
  match state.pending with
  | [] => state
  | job :: rest =>
      { state with pending := rest, published := state.published ++
          [⟨job.activation, job.occurrence,
            program.source job.template (state.store job.activation)⟩] }

def indexedStep (program : Kernel Coordinate Value) (state : IndexedState Coordinate Value) : IndexedState Coordinate Value :=
  match state.frontier[state.cursor]? with
  | none => state
  | some job =>
      { state with cursor := state.cursor + 1, published := state.published ++
          [⟨job.activation, job.occurrence,
            program.execute (program.prepared job.template) (state.store job.activation)⟩] }

theorem decode_indexedStep (program : Kernel Coordinate Value) (state : IndexedState Coordinate Value) :
    decode (indexedStep program state) = treeStep program (decode state) := by
  cases lookup : state.frontier[state.cursor]? with
  | none =>
      have exhausted : state.frontier.toList.drop state.cursor = [] := by
        apply List.drop_eq_nil_of_le
        have bound := Array.getElem?_eq_none_iff.mp lookup
        simpa using bound
      simp [indexedStep, lookup, treeStep, decode, exhausted]
  | some job =>
      have split : state.frontier.toList.drop state.cursor =
          job :: state.frontier.toList.drop (state.cursor + 1) := by
        have hit : state.frontier.toList[state.cursor]? = some job := by simpa using lookup
        obtain ⟨bound, value⟩ := List.getElem?_eq_some_iff.mp hit
        rw [List.drop_eq_getElem_cons bound, value]
      simp [indexedStep, lookup, program.correct, treeStep, decode, split]

/-! ## Regions and explicit observation boundaries -/

def repeats {State : Type} (step : State → State) : Nat → State → State
  | 0, state => state
  | n + 1, state => repeats step n (step state)

theorem repeats_add {State : Type} (step : State → State) (first second : Nat)
    (state : State) :
    repeats step (first + second) state = repeats step second (repeats step first state) := by
  induction first generalizing state with
  | zero => simp [repeats]
  | succ first ih => simpa [Nat.succ_add, repeats] using ih (step state)

theorem decode_repeats (program : Kernel Coordinate Value) (count : Nat) (state : IndexedState Coordinate Value) :
    decode (repeats (indexedStep program) count state) =
      repeats (treeStep program) count (decode state) := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => simp [repeats, ih, decode_indexedStep]

inductive Boundary (Coordinate Value : Type) where
  | environment (change : Store Coordinate Value → Store Coordinate Value)
  | cancel

def treeBoundary : Boundary Coordinate Value → TreeState Coordinate Value → TreeState Coordinate Value
  | .environment change, state => { state with store := change state.store }
  | .cancel, state => { state with pending := [] }

def indexedBoundary : Boundary Coordinate Value → IndexedState Coordinate Value → IndexedState Coordinate Value
  | .environment change, state => { state with store := change state.store }
  | .cancel, state => { state with cursor := state.frontier.size }

theorem decode_boundary (boundary : Boundary Coordinate Value) (state : IndexedState Coordinate Value) :
    decode (indexedBoundary boundary state) = treeBoundary boundary (decode state) := by
  cases boundary <;> simp [decode, treeBoundary, indexedBoundary]

def regionCategory : IndexedCategory Unit (fun _ _ : Unit => Nat) where
  identity _ := 0
  compose first second := first + second
  identity_compose := Nat.zero_add
  compose_identity := Nat.add_zero
  compose_assoc := Nat.add_assoc

def treeRealization (program : Kernel Coordinate Value) :
    Realization regionCategory (fun _ _ : Unit => Boundary Coordinate Value) functionCategory where
  objectMap _ := TreeState Coordinate Value
  mapRegion count := repeats (treeStep program) count
  mapHole := treeBoundary
  map_identity _ := rfl
  map_compose first second := by
    funext state
    exact repeats_add (treeStep program) first second state

def indexedRealization (program : Kernel Coordinate Value) :
    Realization regionCategory (fun _ _ : Unit => Boundary Coordinate Value) functionCategory where
  objectMap _ := IndexedState Coordinate Value
  mapRegion count := repeats (indexedStep program) count
  mapHole := indexedBoundary
  map_identity _ := rfl
  map_compose first second := by
    funext state
    exact repeats_add (indexedStep program) first second state

def indexedToTree (program : Kernel Coordinate Value) :
    RealizationTransformation (indexedRealization program) (treeRealization program) where
  component _ := decode
  region_naturality count := funext (decode_repeats program count)
  hole_naturality boundary := funext (decode_boundary boundary)

inductive Engine where
  | tree
  | indexed

def family (program : Kernel Coordinate Value) :
    Family regionCategory (fun _ _ : Unit => Boundary Coordinate Value) functionCategory Engine where
  reference := treeRealization program
  engine
    | .tree => treeRealization program
    | .indexed => indexedRealization program
  decode
    | .tree => RealizationTransformation.identity (treeRealization program)
    | .indexed => indexedToTree program

/-- The caller supplies a boundary-specific account, including any template
compilation. No constant conversion cost is claimed by the representation. -/
def enter (program : Kernel Coordinate Value) (charge : Resources) :
    Transfer (family program) .tree .indexed () where
  convert := encode
  commutes := funext decode_encode
  resources := charge

def leave (program : Kernel Coordinate Value) (charge : Resources) :
    Transfer (family program) .indexed .tree () where
  convert := decode
  commutes := rfl
  resources := charge

/-- This specializes the generic theorem to reference and prepared execution,
preserving residual jobs and environments as well as output. -/
theorem mixed_execution_exact (program : Kernel Coordinate Value)
    (execution : Execution (family program) .tree () .tree ())
    (initial : TreeState Coordinate Value) :
    execution.denote initial =
      Plan.denote (treeRealization program) execution.erase initial := by
  have square := congrFun (Execution.denote_decode execution) initial
  exact square

#print axioms decode_indexedStep
#print axioms decode_boundary
#print axioms mixed_execution_exact

end Mettapedia.GSLT.Dynamics.ContextIndexedSwitching
