import Mettapedia.GSLT.Core.FiniteInventoryLoader
import Mettapedia.GSLT.Core.IndexedOperational
import Mettapedia.OSLF.Framework.IndexedModalFunctor

/-!
# Linked-row realization of finite inventory loading

An abstract finite inventory can be lowered to an occurrence-indexed linked
row stream.  The target is itself a GSLT: one step accepts only the row at the
current cursor, requires its successor to be exactly the next cursor, and
moves its opaque value into the loaded prefix.

This is the reusable semantic seam between presentation transformation and a
concrete set-valued runtime.  Runtime encoding and execution remain separate
realization obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LinkedInventoryLoader

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

variable {Value Source Target Result : Type}

/-- One occurrence-indexed opaque inventory row. -/
structure Row (Value : Type) where
  position : Nat
  successor : Nat
  value : Value
deriving DecidableEq

namespace Row

def map (translation : Source → Target) (row : Row Source) : Row Target :=
  { position := row.position
    successor := row.successor
    value := translation row.value }

@[simp] theorem map_position (translation : Source → Target)
    (row : Row Source) :
    (row.map translation).position = row.position := by
  rfl

@[simp] theorem map_successor (translation : Source → Target)
    (row : Row Source) :
    (row.map translation).successor = row.successor := by
  rfl

@[simp] theorem map_value (translation : Source → Target)
    (row : Row Source) :
    (row.map translation).value = translation row.value := by
  rfl

@[simp] theorem map_id (row : Row Value) : row.map id = row := by
  cases row
  rfl

@[simp] theorem map_comp (earlier : Source → Target) (later : Target → Result)
    (row : Row Source) :
    (row.map earlier).map later = row.map (later ∘ earlier) := by
  cases row
  rfl

end Row

/-- Encode a suffix beginning at an explicit occurrence cursor. -/
def rowsFrom : Nat → List Value → List (Row Value)
  | _, [] => []
  | position, value :: remaining =>
      { position := position
        successor := position + 1
        value := value } :: rowsFrom (position + 1) remaining

@[simp] theorem rowsFrom_nil (position : Nat) :
    rowsFrom (Value := Value) position [] = [] := by
  rfl

@[simp] theorem rowsFrom_cons (position : Nat) (value : Value)
    (remaining : List Value) :
    rowsFrom position (value :: remaining) =
      { position := position, successor := position + 1, value := value } ::
        rowsFrom (position + 1) remaining := by
  rfl

@[simp] theorem rowsFrom_length (position : Nat) (values : List Value) :
    (rowsFrom position values).length = values.length := by
  induction values generalizing position with
  | nil => rfl
  | cons value remaining induction =>
      simp [rowsFrom, induction]

theorem rowsFrom_map (translation : Source → Target) (position : Nat)
    (values : List Source) :
    (rowsFrom position values).map (Row.map translation) =
      rowsFrom position (values.map translation) := by
  induction values generalizing position with
  | nil => rfl
  | cons value remaining induction =>
    simp [rowsFrom, Row.map, induction]

/-! ## Reified occurrence-row transformation -/

/-- Decode one contiguous linked-row suffix.  The decoder checks both the
current occurrence position and its declared successor; it never recovers
order from container enumeration. -/
def decodeRowsFrom? (position : Nat) : List (Row Value) → Option (List Value)
  | [] => some []
  | row :: remaining =>
      if _positionMatches : row.position = position then
        if _successorMatches : row.successor = position + 1 then
          match decodeRowsFrom? (position + 1) remaining with
          | none => none
          | some values => some (row.value :: values)
        else
          none
      else
        none

/-- Reify a finite source inventory as contiguous occurrence-indexed target
rows beginning at zero.  This is the data-level companion of `lowering`:
`lowering` maps the native GSLTs, while `encodeInventory` emits their finite
target presentation. -/
def encodeInventory (values : List Value) : List (Row Value) :=
  rowsFrom 0 values

/-- Decode a complete reified inventory from its initial occurrence cursor. -/
def decodeInventory? (rows : List (Row Value)) : Option (List Value) :=
  decodeRowsFrom? 0 rows

/-- A reified transform result retains both input and emitted target rows,
with the exact transformation equation carried as data rather than inferred
from a caller-supplied name. -/
structure ReifiedArtifact (Value : Type) where
  source : List Value
  target : List (Row Value)
  exact : target = encodeInventory source

@[ext] theorem ReifiedArtifact.ext {left right : ReifiedArtifact Value}
    (source : left.source = right.source) (target : left.target = right.target) :
    left = right := by
  cases left
  cases right
  cases source
  cases target
  rfl

/-- Map an already reified inventory through an explicit opaque-value
transformation.  The row occurrence protocol is retained exactly. -/
def ReifiedArtifact.map (translation : Source → Target)
    (artifact : ReifiedArtifact Source) : ReifiedArtifact Target where
  source := artifact.source.map translation
  target := artifact.target.map (Row.map translation)
  exact := by
    rw [artifact.exact]
    exact rowsFrom_map translation 0 artifact.source

/-- Every finite inventory has a concrete linked-row transform artifact. -/
def reify (values : List Value) : ReifiedArtifact Value where
  source := values
  target := encodeInventory values
  exact := rfl

/-- The row decoder is a true section of the reified occurrence transform. -/
@[simp] theorem decodeRowsFrom?_rowsFrom (position : Nat)
    (values : List Value) :
    decodeRowsFrom? position (rowsFrom position values) = some values := by
  induction values generalizing position with
  | nil => rfl
  | cons value remaining induction =>
      simp [rowsFrom, decodeRowsFrom?, induction]

/-- The complete inventory codec is exact in the source-to-target direction. -/
@[simp] theorem decodeInventory?_encodeInventory (values : List Value) :
    decodeInventory? (encodeInventory values) = some values := by
  exact decodeRowsFrom?_rowsFrom 0 values

/-- The emitted artifact is also decodable back to its exact supplied source
inventory. -/
@[simp] theorem decodeInventory?_reify (values : List Value) :
    decodeInventory? (reify values).target = some values := by
  exact decodeInventory?_encodeInventory values

/-- Reified value translation commutes with decoding: the target rows still
determine the mapped source inventory exactly. -/
@[simp] theorem decodeInventory?_map (translation : Source → Target)
    (artifact : ReifiedArtifact Source) :
    decodeInventory? (artifact.map translation).target =
      some (artifact.source.map translation) := by
  change decodeInventory? (artifact.target.map (Row.map translation)) =
    some (artifact.source.map translation)
  rw [artifact.exact]
  change decodeInventory?
      ((rowsFrom 0 artifact.source).map (Row.map translation)) =
    some (artifact.source.map translation)
  rw [rowsFrom_map]
  exact decodeInventory?_encodeInventory (artifact.source.map translation)

/-- Reifying after an opaque-value translation has the same target rows as
mapping the rows of the original reified inventory. -/
@[simp] theorem reify_map (translation : Source → Target) (values : List Source) :
    (reify values).map translation = reify (values.map translation) := by
  apply ReifiedArtifact.ext
  · rfl
  · exact rowsFrom_map translation 0 values

/-- Reified value transformations compose in the same execution order as
their underlying value transformations. -/
@[simp] theorem ReifiedArtifact.map_comp (earlier : Source → Target)
    (later : Target → Result) (artifact : ReifiedArtifact Source) :
    (artifact.map earlier).map later = artifact.map (later ∘ earlier) := by
  apply ReifiedArtifact.ext <;>
    simp [ReifiedArtifact.map, List.map_map]

/-- The reified rows have one element per source occurrence. -/
@[simp] theorem encodeInventory_length (values : List Value) :
    (encodeInventory values).length = values.length := by
  exact rowsFrom_length 0 values

/-- `reify` preserves its actual input inventory, not merely its length or a
selected observation. -/
@[simp] theorem reify_source (values : List Value) :
    (reify values).source = values := by
  rfl

/-- A malformed successor cannot be decoded as an authored occurrence row. -/
@[simp] theorem decodeInventory?_wrong_successor_rejected (value : Value) :
    decodeInventory?
      [{ position := 0, successor := 2, value := value }] = none := by
  rfl

/-- Repeating the initial occurrence position cannot be decoded as a distinct
second source occurrence. -/
@[simp] theorem decodeInventory?_duplicate_position_rejected
    (first second : Value) :
    decodeInventory?
      [{ position := 0, successor := 1, value := first },
       { position := 0, successor := 1, value := second }] = none := by
  rfl

/-- State of the linked-row loader.  `terminal` is carried explicitly so the
end observation cannot be inferred from enumeration order. -/
structure State (Value : Type) where
  loaded : List Value
  cursor : Nat
  remaining : List (Row Value)
  terminal : Nat
deriving DecidableEq

namespace State

/-- Map opaque payloads while retaining the complete linked-row control
protocol.  This is the value-level action of the reusable target GSLT. -/
def map (translation : Source → Target) (state : State Source) : State Target :=
  { loaded := state.loaded.map translation
    cursor := state.cursor
    remaining := state.remaining.map (Row.map translation)
    terminal := state.terminal }

@[simp] theorem map_loaded (translation : Source → Target) (state : State Source) :
    (state.map translation).loaded = state.loaded.map translation := by
  rfl

@[simp] theorem map_cursor (translation : Source → Target) (state : State Source) :
    (state.map translation).cursor = state.cursor := by
  rfl

@[simp] theorem map_remaining (translation : Source → Target)
    (state : State Source) :
    (state.map translation).remaining = state.remaining.map (Row.map translation) := by
  rfl

@[simp] theorem map_terminal (translation : Source → Target) (state : State Source) :
    (state.map translation).terminal = state.terminal := by
  rfl

@[simp] theorem map_id (state : State Value) : state.map id = state := by
  cases state with
  | mk loaded cursor remaining terminal =>
      have remainingId : remaining.map (Row.map id) = remaining := by
        induction remaining with
        | nil => rfl
        | cons row remaining induction =>
            simp [induction]
      simp [map, remainingId]

@[simp] theorem map_comp (earlier : Source → Target) (later : Target → Result)
    (state : State Source) :
    (state.map earlier).map later = state.map (later ∘ earlier) := by
  cases state
  simp [map, Row.map, List.map_map]

end State

/-- One linked-row step consumes exactly the current row and rejects skipped
or rewound successors by construction. -/
inductive Step : State Value → State Value → Prop where
  | load (loaded : List Value) (cursor : Nat) (value : Value)
      (remaining : List (Row Value)) (terminal : Nat) :
      Step
        { loaded := loaded
          cursor := cursor
          remaining :=
            { position := cursor, successor := cursor + 1, value := value } ::
              remaining
          terminal := terminal }
        { loaded := loaded ++ [value]
          cursor := cursor + 1
          remaining := remaining
          terminal := terminal }

/-- Native GSLT of linked-row inventory loading. -/
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

/-- Opaque-value translation preserves one linked-row occurrence step without
changing its cursor, successor, or terminal boundary. -/
theorem map_step (translation : Source → Target)
    {source target : State Source} (step : Step source target) :
    Step (source.map translation) (target.map translation) := by
  cases step with
  | load loaded cursor value remaining terminal =>
      simpa [State.map, Row.map, List.map_append] using
        (Step.load (loaded.map translation) cursor (translation value)
          (remaining.map (Row.map translation)) terminal)

/-- Expose the exact consumed occurrence and successor state of an arbitrary
linked-row step.  This inversion lemma is used by reified transformations to
recover source ownership from behavior at an image state. -/
theorem step_decompose {source target : State Value} (step : Step source target) :
    ∃ value remaining,
      source.remaining =
        { position := source.cursor
          successor := source.cursor + 1
          value := value } :: remaining ∧
      target =
        { loaded := source.loaded ++ [value]
          cursor := source.cursor + 1
          remaining := remaining
          terminal := source.terminal } := by
  cases step
  exact ⟨_, _, rfl, rfl⟩

/-- No step can appear at an image state solely because opaque values were
translated: every such target step has the corresponding source occurrence. -/
theorem map_lift_step (translation : Source → Target)
    {source : State Source} {target : State Target}
    (step : Step (source.map translation) target) :
    ∃ sourceTarget,
      Step source sourceTarget ∧ sourceTarget.map translation = target := by
  obtain ⟨targetValue, targetRemaining, inputShape, targetShape⟩ :=
    step_decompose step
  rcases source with ⟨loaded, cursor, sourceRemaining, terminal⟩
  cases sourceRemaining with
  | nil =>
      simp [State.map] at inputShape
  | cons sourceRow sourceRemaining =>
      rcases sourceRow with ⟨position, successor, sourceValue⟩
      change
        { position := position
          successor := successor
          value := translation sourceValue } ::
          sourceRemaining.map (Row.map translation) =
        { position := cursor
          successor := cursor + 1
          value := targetValue } :: targetRemaining at inputShape
      injection inputShape with rowShape remainingShape
      injection rowShape with positionShape successorShape valueShape
      subst position
      subst successor
      subst targetValue
      subst targetRemaining
      refine
        ⟨{ loaded := loaded ++ [sourceValue]
           cursor := cursor + 1
           remaining := sourceRemaining
           terminal := terminal },
          Step.load loaded cursor sourceValue sourceRemaining terminal,
          ?_⟩
      simpa [State.map, Row.map, List.map_append] using targetShape.symm

/-- Exact GSLT-to-GSLT transport induced by mapping opaque inventory values.
The back condition is local to image states, so equal target values cannot
collapse distinct source occurrences. -/
def valueMapLowering (translation : Source → Target) :
    CoveredTranslation (gslt Source) (gslt Target) where
  mapTerm := State.map translation
  mapEquiv := by
    intro left right equal
    subst right
    rfl
  cover :=
    { mapStep := map_step translation
      liftStep := map_lift_step translation }

/-- The opaque-value GSLT transport has the same identity law as its reified
data artifact. -/
theorem valueMapLowering_id (Value : Type) :
    valueMapLowering (id : Value → Value) =
      CoveredTranslation.id (gslt Value) := by
  apply CoveredTranslation.ext
  funext state
  exact State.map_id state

/-- Successive value mappings compose as one exact GSLT-to-GSLT transport. -/
theorem valueMapLowering_comp (earlier : Source → Target)
    (later : Target → Result) :
    (valueMapLowering earlier).comp (valueMapLowering later) =
      valueMapLowering (later ∘ earlier) := by
  apply CoveredTranslation.ext
  funext state
  exact State.map_comp earlier later state

/-- OSLF sends the actual linked-loader GSLT arrow induced by an opaque-value
map to a contravariant native-modal map.  This is the semantic counterpart of
`ReifiedArtifact.map`: the latter changes finite data, while this definition
transports predicates over the loader's operational states.

Outgoing step coverage is exact, so possibility (`◇`) transport is exact.
An arbitrary value map is not claimed to cover target predecessors, therefore
the universal-predecessor component is deliberately only lax. -/
def valueMapNTT (translation : Source → Target) :
    Mettapedia.OSLF.Framework.IndexedModalFunctor.ForwardModalPredicateTheory.Hom
      (Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
        (gslt Target))
      (Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
        (gslt Source)) :=
  Mettapedia.OSLF.Framework.IndexedModalFunctor.OperationalTranslation.pullbackLax
    (valueMapLowering translation).toOperational

/-- The possibility modality of OSLF transports exactly along the linked
inventory value transform.  This is the no-invention law at mapped loader
states; it follows from `map_lift_step`, not from data serialization. -/
theorem valueMap_diamond_exact (translation : Source → Target)
    (predicate : Set (State Target)) :
    Set.preimage (State.map translation)
        (gsltDiamond (gslt Target) predicate) =
      gsltDiamond (gslt Source)
        (Set.preimage (State.map translation) predicate) :=
  Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor.CoveredTranslation.preimage_diamond
    (valueMapLowering translation) predicate

/-- OSLF reverses a chain of linked-inventory value transforms while retaining
the same execution order at the underlying GSLT level. -/
theorem valueMapNTT_comp (earlier : Source → Target)
    (later : Target → Result) :
    (valueMapNTT later).comp (valueMapNTT earlier) =
      valueMapNTT (later ∘ earlier) := by
  apply Mettapedia.OSLF.Framework.IndexedModalFunctor.ForwardModalPredicateTheory.Hom.ext
  apply CompleteLatticeHom.ext
  intro predicate
  ext state
  induction state using Quotient.inductionOn with
  | _ state =>
      change predicate (Quotient.mk _ ((state.map earlier).map later)) ↔
        predicate (Quotient.mk _ (state.map (later ∘ earlier)))
      rw [State.map_comp]

/-- Exact local reflection for opaque-value transport in the abstract
finite-inventory loader.  This is separate from the linked representation so
the representation square below is a genuine GSLT-to-GSLT square. -/
theorem finiteValueMap_lift_step (translation : Source → Target)
    {source : FiniteInventoryLoader.State Source}
    {target : FiniteInventoryLoader.State Target}
    (step : FiniteInventoryLoader.Step
      (FiniteInventoryLoader.State.map translation source) target) :
    ∃ sourceTarget,
      FiniteInventoryLoader.Step source sourceTarget ∧
        FiniteInventoryLoader.State.map translation sourceTarget = target := by
  rcases source with ⟨loaded, remaining⟩
  cases remaining with
  | nil =>
      change FiniteInventoryLoader.Step
        { loaded := loaded.map translation, remaining := [] } target at step
      cases step
  | cons value remaining =>
      cases step
      refine
        ⟨{ loaded := loaded ++ [value], remaining := remaining },
          FiniteInventoryLoader.Step.load loaded value remaining, ?_⟩
      simp [FiniteInventoryLoader.State.map, List.map_append]

/-- Exact GSLT-to-GSLT transport induced by mapping the opaque values of an
abstract finite inventory. -/
def finiteValueMapLowering (translation : Source → Target) :
    CoveredTranslation (FiniteInventoryLoader.gslt Source)
      (FiniteInventoryLoader.gslt Target) where
  mapTerm := FiniteInventoryLoader.State.map translation
  mapEquiv := by
    intro left right equal
    subst right
    rfl
  cover :=
    { mapStep := FiniteInventoryLoader.map_step translation
      liftStep := finiteValueMap_lift_step translation }

/-- Abstract finite-inventory value maps compose in execution order. -/
theorem finiteValueMapLowering_comp (earlier : Source → Target)
    (later : Target → Result) :
    (finiteValueMapLowering earlier).comp (finiteValueMapLowering later) =
      finiteValueMapLowering (later ∘ earlier) := by
  apply CoveredTranslation.ext
  funext state
  exact FiniteInventoryLoader.State.map_comp earlier later state

/-- OSLF's native-modal transport for the abstract inventory value map. -/
def finiteValueMapNTT (translation : Source → Target) :
    Mettapedia.OSLF.Framework.IndexedModalFunctor.ForwardModalPredicateTheory.Hom
      (Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
        (FiniteInventoryLoader.gslt Target))
      (Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
        (FiniteInventoryLoader.gslt Source)) :=
  Mettapedia.OSLF.Framework.IndexedModalFunctor.OperationalTranslation.pullbackLax
    (finiteValueMapLowering translation).toOperational

/-- Possibility transport along an abstract inventory value map is exact at
mapped states. -/
theorem finiteValueMap_diamond_exact (translation : Source → Target)
    (predicate : Set (FiniteInventoryLoader.State Target)) :
    Set.preimage (FiniteInventoryLoader.State.map translation)
        (gsltDiamond (FiniteInventoryLoader.gslt Target) predicate) =
      gsltDiamond (FiniteInventoryLoader.gslt Source)
        (Set.preimage (FiniteInventoryLoader.State.map translation) predicate) :=
  Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor.CoveredTranslation.preimage_diamond
    (finiteValueMapLowering translation) predicate

/-- OSLF reverses composition of abstract inventory value maps in the same
way as it reverses linked-row value maps. -/
theorem finiteValueMapNTT_comp (earlier : Source → Target)
    (later : Target → Result) :
    (finiteValueMapNTT later).comp (finiteValueMapNTT earlier) =
      finiteValueMapNTT (later ∘ earlier) := by
  apply Mettapedia.OSLF.Framework.IndexedModalFunctor.ForwardModalPredicateTheory.Hom.ext
  apply CompleteLatticeHom.ext
  intro predicate
  ext state
  induction state using Quotient.inductionOn with
  | _ state =>
      change predicate
          (Quotient.mk _
            ((FiniteInventoryLoader.State.map earlier state).map later)) ↔
        predicate
          (Quotient.mk _
            (FiniteInventoryLoader.State.map (later ∘ earlier) state))
      rw [FiniteInventoryLoader.State.map_comp]

/-- Map a proof-relevant linked-row path without erasing its occurrence
identity or administrative cursor states. -/
def mapPath (translation : Source → Target)
    {source target : State Source} :
    (gslt Source).RewritePath source target →
      (gslt Target).RewritePath (source.map translation)
        (target.map translation)
  | .nil state =>
      @GSLT.RewritePath.nil (gslt Target) (state.map translation)
  | .cons step rest =>
      .cons (map_step translation step) (mapPath translation rest)

@[simp] theorem mapPath_length (translation : Source → Target) :
    {source target : State Source} →
      (path : (gslt Source).RewritePath source target) →
        (mapPath translation path).length = path.length
  | _, _, .nil _ => rfl
  | _, _, .cons _ rest => by
      simp only [mapPath, GSLT.RewritePath.length]
      rw [mapPath_length translation rest]

/-- Lower one abstract loader state to its exact linked-row representation. -/
def lowerState
    (state : FiniteInventoryLoader.State Value) : State Value :=
  { loaded := state.loaded
    cursor := state.loaded.length
    remaining := rowsFrom state.loaded.length state.remaining
    terminal := state.loaded.length + state.remaining.length }

/-- Reifying then lowering commutes with opaque-value translation.  This is
the state-level square connecting the source inventory GSLT, the linked-row
target GSLT, and their reified presentations. -/
@[simp] theorem map_lowerState (translation : Source → Target)
    (state : FiniteInventoryLoader.State Source) :
    (lowerState state).map translation =
      lowerState (FiniteInventoryLoader.State.map translation state) := by
  rcases state with ⟨loaded, remaining⟩
  simp [lowerState, State.map, FiniteInventoryLoader.State.map,
    rowsFrom_map, List.length_map]

/-- The abstract and linked value maps commute with occurrence-preserving
lowering.  This is a real semantic square, not an equality of renderings. -/
theorem lowering_valueMap_commutes (translation : Source → Target) :
    (valueMapLowering translation).mapTerm ∘ lowerState =
      lowerState ∘ (finiteValueMapLowering translation).mapTerm := by
  funext state
  exact map_lowerState translation state

@[simp] theorem lowerState_initial (inventory : List Value) :
    lowerState (FiniteInventoryLoader.initial inventory) =
      { loaded := []
        cursor := 0
        remaining := rowsFrom 0 inventory
        terminal := inventory.length } := by
  simp [lowerState, FiniteInventoryLoader.initial]

@[simp] theorem lowerState_terminal (inventory : List Value) :
    lowerState (FiniteInventoryLoader.terminal inventory) =
      { loaded := inventory
        cursor := inventory.length
        remaining := []
        terminal := inventory.length } := by
  simp [lowerState, FiniteInventoryLoader.terminal]

/-- The reified row list is exactly the remaining component of the native
linked loader's initial state. -/
@[simp] theorem reify_target_eq_initial_remaining (values : List Value) :
    (reify values).target =
      (lowerState (FiniteInventoryLoader.initial values)).remaining := by
  rfl

/-- Every abstract occurrence transfer becomes exactly one linked-row step. -/
theorem lower_step
    {source target : FiniteInventoryLoader.State Value}
    (step : FiniteInventoryLoader.Step source target) :
    Step (lowerState source) (lowerState target) := by
  cases step with
  | load loaded value remaining =>
      have terminalEq :
          loaded.length + (value :: remaining).length =
            (loaded ++ [value]).length + remaining.length := by
        simp only [List.length_cons, List.length_append, List.length_nil]
        omega
      change Step
        { loaded := loaded
          cursor := loaded.length
          remaining := rowsFrom loaded.length (value :: remaining)
          terminal := loaded.length + (value :: remaining).length }
        { loaded := loaded ++ [value]
          cursor := (loaded ++ [value]).length
          remaining := rowsFrom (loaded ++ [value]).length remaining
          terminal := (loaded ++ [value]).length + remaining.length }
      rw [rowsFrom_cons, terminalEq]
      simpa only [List.length_append, List.length_singleton] using
        (Step.load loaded loaded.length value
          (rowsFrom (loaded.length + 1) remaining)
          ((loaded ++ [value]).length + remaining.length))

/-- Every linked-row step leaving a lowered state lifts to the unique abstract
occurrence transfer.  The target protocol cannot invent a skipped step. -/
theorem lift_step
    {source : FiniteInventoryLoader.State Value} {target : State Value}
    (step : Step (lowerState source) target) :
    ∃ sourceTarget,
      FiniteInventoryLoader.Step source sourceTarget ∧
        lowerState sourceTarget = target := by
  rcases source with ⟨loaded, remaining⟩
  cases remaining with
  | nil =>
      change Step
        { loaded := loaded, cursor := loaded.length, remaining := [],
          terminal := loaded.length + [].length } target at step
      cases step
  | cons value rest =>
      have targetEq :
          target = lowerState
            ({ loaded := loaded ++ [value], remaining := rest } :
              FiniteInventoryLoader.State Value) := by
        cases step
        simp [lowerState, List.length_append, Nat.add_comm]
      exact
        ⟨{ loaded := loaded ++ [value], remaining := rest },
          FiniteInventoryLoader.Step.load loaded value rest,
          targetEq.symm⟩

/-- The linked-row lowering is an exact local operational translation, not
only a row serializer. -/
def lowering :
    CoveredTranslation (FiniteInventoryLoader.gslt Value) (gslt Value) where
  mapTerm := lowerState
  mapEquiv := by
    intro left right equal
    subst right
    rfl
  cover :=
    { mapStep := lower_step
      liftStep := lift_step }

/-- OSLF's contravariant native-modal account of the actual abstract-loader
to linked-loader GSLT transformation.  This is the reusable semantic arrow
used when a finite verifier-rule inventory is lowered to occurrence-indexed
rows. -/
def loweringNTT (Value : Type) :
    Mettapedia.OSLF.Framework.IndexedModalFunctor.ForwardModalPredicateTheory.Hom
      (Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
        (gslt Value))
      (Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
        (FiniteInventoryLoader.gslt Value)) :=
  Mettapedia.OSLF.Framework.IndexedModalFunctor.OperationalTranslation.pullbackLax
    (lowering (Value := Value)).toOperational

/-- Possibility in the linked loader is exactly the possibility licensed by
the abstract inventory at every lowered state.  A row at an image state
therefore cannot manufacture a skipped abstract occurrence step. -/
theorem lowering_diamond_exact (Value : Type)
    (predicate : Set (State Value)) :
    Set.preimage lowerState (gsltDiamond (gslt Value) predicate) =
      gsltDiamond (FiniteInventoryLoader.gslt Value)
        (Set.preimage lowerState predicate) :=
  Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor.CoveredTranslation.preimage_diamond
    (lowering (Value := Value)) predicate

/-- Applying OSLF to the abstract-to-linked representation square gives the
corresponding contravariant naturality square of native-modal maps. -/
theorem loweringNTT_valueMap_naturality (translation : Source → Target) :
    (valueMapNTT translation).comp (loweringNTT Source) =
      (loweringNTT Target).comp (finiteValueMapNTT translation) := by
  apply Mettapedia.OSLF.Framework.IndexedModalFunctor.ForwardModalPredicateTheory.Hom.ext
  apply CompleteLatticeHom.ext
  intro predicate
  ext state
  induction state using Quotient.inductionOn with
  | _ state =>
      change predicate (Quotient.mk _ ((lowerState state).map translation)) ↔
        predicate
          (Quotient.mk _
            (lowerState (FiniteInventoryLoader.State.map translation state)))
      rw [map_lowerState]

/-- Lower a complete proof-relevant abstract path without erasing its
intermediate occurrence states. -/
def lowerPath :
    {source target : FiniteInventoryLoader.State Value} →
      (FiniteInventoryLoader.gslt Value).RewritePath source target →
        (gslt Value).RewritePath (lowerState source) (lowerState target)
  | _, _, .nil state =>
      @GSLT.RewritePath.nil (gslt Value) (lowerState state)
  | _, _, .cons step rest => .cons (lower_step step) (lowerPath rest)

@[simp] theorem lowerPath_length
    {source target : FiniteInventoryLoader.State Value} :
    (path : (FiniteInventoryLoader.gslt Value).RewritePath source target) →
      (lowerPath path).length = path.length
  | .nil _ => rfl
  | .cons _ rest => by
      simp only [lowerPath, GSLT.RewritePath.length]
      rw [lowerPath_length rest]

/-- Every finite inventory therefore has a complete linked-row path. -/
def complete (inventory : List Value) :
    (gslt Value).RewritePath
      (lowerState (FiniteInventoryLoader.initial inventory))
      (lowerState (FiniteInventoryLoader.terminal inventory)) :=
  lowerPath (FiniteInventoryLoader.complete inventory)

/-- Negative control: a row whose declared successor skips the next cursor
cannot take a linked-loader step. -/
theorem wrong_successor_cannot_load (loaded : List Value) (cursor wrong : Nat)
    (value : Value) (remaining : List (Row Value)) (terminal : Nat)
    (wrongSuccessor : wrong ≠ cursor + 1) :
    ¬ ∃ target, Step
      { loaded := loaded
        cursor := cursor
        remaining :=
          { position := cursor, successor := wrong, value := value } :: remaining
        terminal := terminal }
      target := by
  rintro ⟨target, step⟩
  cases step
  exact wrongSuccessor rfl

/-- Equal opaque values at different positions remain different rows. -/
theorem duplicate_values_keep_distinct_occurrences :
    rowsFrom 0 [7, 7] =
      [{ position := 0, successor := 1, value := 7 },
       { position := 1, successor := 2, value := 7 }] := by
  rfl

/-- A nontrivial value translation preserves the exact reified occurrence
inventory, including duplicate source values. -/
theorem reified_successor_map_keeps_duplicate_occurrences :
    decodeInventory? ((reify [7, 7]).map Nat.succ).target = some [8, 8] := by
  simpa using decodeInventory?_map Nat.succ (reify [7, 7])

/-- Even a value-collapsing translation preserves two separate linked-loader
steps; occurrence identity is carried by rows and cursors, not value equality. -/
theorem collapsed_values_keep_two_occurrence_steps :
    (mapPath (fun _ : Nat => 0) (complete [7, 8])).length = 2 := by
  rw [mapPath_length]
  rfl

#print axioms rowsFrom_map
#print axioms decodeRowsFrom?_rowsFrom
#print axioms decodeInventory?_encodeInventory
#print axioms decodeInventory?_reify
#print axioms decodeInventory?_map
#print axioms reify_map
#print axioms ReifiedArtifact.map_comp
#print axioms encodeInventory_length
#print axioms reify_source
#print axioms reify_target_eq_initial_remaining
#print axioms decodeInventory?_wrong_successor_rejected
#print axioms decodeInventory?_duplicate_position_rejected
#print axioms map_step
#print axioms step_decompose
#print axioms map_lift_step
#print axioms valueMapLowering
#print axioms valueMapLowering_id
#print axioms valueMapLowering_comp
#print axioms valueMapNTT
#print axioms valueMap_diamond_exact
#print axioms valueMapNTT_comp
#print axioms finiteValueMap_lift_step
#print axioms finiteValueMapLowering
#print axioms finiteValueMapLowering_comp
#print axioms finiteValueMapNTT
#print axioms finiteValueMap_diamond_exact
#print axioms finiteValueMapNTT_comp
#print axioms mapPath_length
#print axioms map_lowerState
#print axioms lowering_valueMap_commutes
#print axioms lower_step
#print axioms lift_step
#print axioms lowering
#print axioms loweringNTT
#print axioms lowering_diamond_exact
#print axioms loweringNTT_valueMap_naturality
#print axioms lowerPath_length
#print axioms wrong_successor_cannot_load
#print axioms duplicate_values_keep_distinct_occurrences
#print axioms reified_successor_map_keeps_duplicate_occurrences
#print axioms collapsed_values_keep_two_occurrence_steps

end Mettapedia.GSLT.LinkedInventoryLoader
