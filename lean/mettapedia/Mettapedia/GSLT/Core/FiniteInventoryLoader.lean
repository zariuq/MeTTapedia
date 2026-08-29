import Mettapedia.GSLT.Core.GSLT

/-!
# Finite occurrence-preserving inventory loading

An emitted verifier or runtime may carry a finite ordered inventory of opaque
target values.  Loading that inventory is itself a small operational theory:
one step moves the next occurrence from the remaining suffix to the loaded
prefix.  The construction is independent of the values' internal syntax.

Lists are intentional.  Equal values at different positions are distinct
occurrences in the loading path even when the eventual runtime carrier is a
set.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.FiniteInventoryLoader

open Mettapedia.GSLT

variable {Value Source Target Result : Type}

/-- State of an ordered finite inventory loader. -/
structure State (Value : Type) where
  loaded : List Value
  remaining : List Value
deriving DecidableEq

namespace State

/-- The complete occurrence sequence represented by a loader state. -/
def inventory (state : State Value) : List Value :=
  state.loaded ++ state.remaining

/-- Map an opaque-value translation over both sides of the loader cursor. -/
def map (translation : Source → Target) (state : State Source) : State Target :=
  { loaded := state.loaded.map translation
    remaining := state.remaining.map translation }

@[simp] theorem inventory_map (translation : Source → Target)
    (state : State Source) :
    (state.map translation).inventory = state.inventory.map translation := by
  simp [inventory, map, List.map_append]

@[simp] theorem map_id (state : State Value) :
    state.map id = state := by
  cases state
  simp [map]

@[simp] theorem map_comp (earlier : Source → Target)
    (later : Target → Result) (state : State Source) :
    (state.map earlier).map later = state.map (later ∘ earlier) := by
  cases state
  simp [map, List.map_map]

end State

/-- One loader step consumes exactly the next occurrence. -/
inductive Step : State Value → State Value → Prop where
  | load (loaded : List Value) (next : Value) (remaining : List Value) :
      Step ⟨loaded, next :: remaining⟩
        ⟨loaded ++ [next], remaining⟩

/-- The native GSLT of ordered finite-inventory loading. -/
def gslt (Value : Type) : GSLT where
  Term := State Value
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- Initial state for an authored occurrence sequence. -/
def initial (inventory : List Value) : State Value :=
  ⟨[], inventory⟩

/-- Exact terminal state for the same occurrence sequence. -/
def terminal (inventory : List Value) : State Value :=
  ⟨inventory, []⟩

/-- State denoted by an occurrence cursor into an authored inventory. -/
def atCursor (inventory : List Value) (position : Nat) : State Value :=
  ⟨inventory.take position, inventory.drop position⟩

@[simp] theorem initial_inventory (inventory : List Value) :
    (initial inventory).inventory = inventory := by
  simp [initial, State.inventory]

@[simp] theorem terminal_inventory (inventory : List Value) :
    (terminal inventory).inventory = inventory := by
  simp [terminal, State.inventory]

@[simp] theorem atCursor_inventory (inventory : List Value) (position : Nat) :
    (atCursor inventory position).inventory = inventory := by
  exact List.take_append_drop position inventory

@[simp] theorem atCursor_zero (inventory : List Value) :
    atCursor inventory 0 = initial inventory := by
  rfl

@[simp] theorem atCursor_length (inventory : List Value) :
    atCursor inventory inventory.length = terminal inventory := by
  simp [atCursor, terminal]

/-- A loader step preserves the complete ordered occurrence sequence. -/
theorem step_preserves_inventory {source target : State Value}
    (step : Step source target) :
    target.inventory = source.inventory := by
  cases step
  simp [State.inventory, List.append_assoc]

/-- Every loader step advances the cursor by exactly one occurrence. -/
theorem step_decreases_remaining {source target : State Value}
    (step : Step source target) :
    target.remaining.length + 1 = source.remaining.length := by
  cases step
  simp

/-- Every in-bounds occurrence cursor advances by one loader step. -/
theorem atCursor_step (inventory : List Value) (position : Nat)
    (inBounds : position < inventory.length) :
    Step (atCursor inventory position) (atCursor inventory (position + 1)) := by
  unfold atCursor
  have sourceRemaining :
      inventory.drop position =
        inventory[position] :: inventory.drop (position + 1) :=
    List.drop_eq_getElem_cons inBounds
  have targetLoaded :
      inventory.take (position + 1) =
        inventory.take position ++ [inventory[position]] := by
    simpa only [List.concat_eq_append] using
      (List.take_concat_get inBounds).symm
  rw [sourceRemaining, targetLoaded]
  exact Step.load (inventory.take position) inventory[position]
    (inventory.drop (position + 1))

/-- Loading is deterministic at every nonterminal state. -/
theorem step_deterministic {source left right : State Value}
    (leftStep : Step source left) (rightStep : Step source right) :
    left = right := by
  cases leftStep
  cases rightStep
  rfl

/-- A state with no remaining occurrences is normal. -/
theorem terminalState_normal (loaded : List Value) :
    (gslt Value).IsNormalForm ⟨loaded, []⟩ := by
  rintro ⟨target, step⟩
  cases step

/-- Functorial action on loader steps: translating opaque values cannot alter
the cursor discipline. -/
theorem map_step (translation : Source → Target)
    {source target : State Source} (step : Step source target) :
    Step (source.map translation) (target.map translation) := by
  cases step
  simpa [State.map, List.map_append] using
    Step.load (List.map translation _) (translation _)
      (List.map translation _)

/-- Mapping opaque values transports a complete proof-relevant loader path. -/
def mapRewritePath (translation : Source → Target)
  {source target : State Source} :
    (gslt Source).RewritePath source target →
      (gslt Target).RewritePath (source.map translation)
        (target.map translation)
  | .nil state =>
      @GSLT.RewritePath.nil (gslt Target) (state.map translation)
  | .cons step rest =>
      .cons (map_step translation step) (mapRewritePath translation rest)

/-- Mapping opaque values transports multi-step loader execution. -/
def mapMultiStep (translation : Source → Target)
  {source target : State Source} :
    (gslt Source).MultiStep source target →
      (gslt Target).MultiStep (source.map translation)
        (target.map translation)
  | .refl state =>
      @GSLT.MultiStep.refl (gslt Target) (state.map translation)
  | .step step rest =>
      .step (map_step translation step) (mapMultiStep translation rest)

/-- Exact proof-relevant loading path from any prefix and remaining suffix. -/
def loadPath (loaded remaining : List Value) :
    (gslt Value).RewritePath ⟨loaded, remaining⟩
      ⟨loaded ++ remaining, []⟩ := by
  induction remaining generalizing loaded with
  | nil =>
      simpa using
        (@GSLT.RewritePath.nil (gslt Value) ⟨loaded, []⟩)
  | cons next tail induction =>
      refine .cons (Step.load loaded next tail) ?_
      simpa [List.append_assoc] using induction (loaded ++ [next])

/-- Every finite inventory reaches its exact terminal state. -/
def complete (inventory : List Value) :
    (gslt Value).RewritePath (initial inventory) (terminal inventory) :=
  loadPath [] inventory

/-- Every multi-step execution preserves the ordered occurrence sequence. -/
theorem multiStep_preserves_inventory {source target : State Value}
    (steps : (gslt Value).MultiStep source target) :
    target.inventory = source.inventory := by
  refine @GSLT.MultiStep.rec (gslt Value)
    (fun first last _ => last.inventory = first.inventory)
    ?_ ?_ source target steps
  · intro state
    rfl
  · intro first middle last firstStep _ induction
    exact induction.trans (step_preserves_inventory firstStep)

/-- A run reaching an empty suffix can neither invent nor discard a value. -/
theorem terminal_loaded_exact {inventory loaded : List Value}
    (steps : (gslt Value).MultiStep (initial inventory) ⟨loaded, []⟩) :
    loaded = inventory := by
  have preserved := multiStep_preserves_inventory steps
  simpa [State.inventory, initial] using preserved

/-- Negative control: two equal occurrences cannot collapse to one. -/
theorem duplicate_occurrences_do_not_collapse :
    ¬ (gslt Nat).MultiStep (initial [7, 7]) (terminal [7]) := by
  intro steps
  have exact : [7] = [7, 7] := by
    apply terminal_loaded_exact
    simpa [terminal] using steps
  simp at exact

#print axioms step_preserves_inventory
#print axioms step_decreases_remaining
#print axioms atCursor_step
#print axioms step_deterministic
#print axioms terminalState_normal
#print axioms map_step
#print axioms mapRewritePath
#print axioms mapMultiStep
#print axioms multiStep_preserves_inventory
#print axioms terminal_loaded_exact
#print axioms duplicate_occurrences_do_not_collapse

end Mettapedia.GSLT.FiniteInventoryLoader
