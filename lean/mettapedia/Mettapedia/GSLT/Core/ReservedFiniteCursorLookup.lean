import Mettapedia.GSLT.Core.FiniteOccurrenceLookup
import Mettapedia.GSLT.Core.OperationalRealizationOSLF

/-!
# Reserved finite cursor lookup

A runtime may reserve more cursor positions than are currently occupied.  A
compressed proof heap is the motivating example: the live heap has a precise
frontier, while later save actions need already-allocated successor rows.

This module separates those two quantities.  Lookup advances only across live
inventory occurrences and reports missing exactly at the live frontier.  A
nonzero reserve licenses further representation edges but cannot turn them
into live values.  The construction is independent of any atom syntax or
proof language.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ReservedFiniteCursorLookup

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.FiniteOccurrenceLookup
open Mettapedia.OSLF.Framework.IndexedModalFunctor
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

variable {Key Value : Type}

/-- An indexed lookup keeps the live inventory and the extra reserved cursor
capacity distinct. -/
inductive Control (Value : Type) where
  | scanning (cursor : Nat)
  | finished (observation : Observation Value)
deriving DecidableEq

structure State (Key Value : Type) where
  target : Key
  inventory : List (Entry Key Value)
  reserve : Nat
  control : Control Value
deriving DecidableEq

namespace State

def liveFrontier (state : State Key Value) : Nat := state.inventory.length

def capacity (state : State Key Value) : Nat :=
  state.inventory.length + state.reserve

end State

/-- Indexed target steps.  A successful probe is justified by `getElem?`.
Advance additionally records that the reserved cursor representation licenses
the next position.  Missing is an explicit equality with the live frontier,
not an absence-of-successor test. -/
inductive Step : State Key Value → State Key Value → Prop where
  | hit (target : Key) (inventory : List (Entry Key Value)) (reserve cursor : Nat)
      (entry : Entry Key Value)
      (found : inventory[cursor]? = some entry)
      (same : entry.key = target) :
      Step ⟨target, inventory, reserve, .scanning cursor⟩
        ⟨target, inventory, reserve, .finished (.found cursor entry.value)⟩
  | advance (target : Key) (inventory : List (Entry Key Value))
      (reserve cursor : Nat) (entry : Entry Key Value)
      (found : inventory[cursor]? = some entry)
      (different : entry.key ≠ target)
      (licensed : cursor < inventory.length + reserve) :
      Step ⟨target, inventory, reserve, .scanning cursor⟩
        ⟨target, inventory, reserve, .scanning (cursor + 1)⟩
  | miss (target : Key) (inventory : List (Entry Key Value)) (reserve : Nat) :
      Step ⟨target, inventory, reserve, .scanning inventory.length⟩
        ⟨target, inventory, reserve,
          .finished (.missing inventory.length)⟩

def gslt (Key Value : Type) : GSLT where
  Term := State Key Value
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

/-- The indexed cursor machine has at most one successor from every state.
In particular, a live hit, a mismatching advance, and the explicit frontier
cannot compete. -/
theorem step_deterministic {source left right : State Key Value}
    (first : Step source left) (second : Step source right) : left = right := by
  cases first <;> cases second <;> simp_all

/-- Retain the source query and inventory while replacing the visited/suffix
cursor by its occurrence number. -/
def mapState (reserve : Nat) :
    FiniteOccurrenceLookup.State Key Value → State Key Value
  | .scanning scan =>
      ⟨scan.target, scan.inventory, reserve, .scanning scan.position⟩
  | .finished target inventory observation =>
      ⟨target, inventory, reserve, .finished observation⟩

@[simp] theorem mapState_reserve (reserve : Nat)
    (state : FiniteOccurrenceLookup.State Key Value) :
    (mapState reserve state).reserve = reserve := by
  cases state <;> rfl

/-- Every semantic finite-lookup step lowers to one exact indexed target
step, for any reserved capacity. -/
theorem lower_step (reserve : Nat)
    {source target : FiniteOccurrenceLookup.State Key Value}
    (step : FiniteOccurrenceLookup.Step source target) :
    Step (mapState reserve source) (mapState reserve target) := by
  cases step with
  | hit target visited next remaining same =>
      simpa [mapState, Scan.inventory, Scan.position] using
        Step.hit target (visited ++ next :: remaining) reserve visited.length
          next (by simp) same
  | advance target visited next remaining different =>
      have licensed :
          visited.length < (visited ++ next :: remaining).length + reserve := by
        simp
        omega
      simpa [mapState, Scan.inventory, Scan.position, List.append_assoc] using
        Step.advance target (visited ++ next :: remaining) reserve
          visited.length next (by simp) different licensed
  | miss target visited =>
      simpa [mapState, Scan.inventory, Scan.position] using
        Step.miss target visited reserve

/-- The semantic finite scan is therefore an exact one-step GSLT
translation into the reserved indexed cursor machine. -/
def translation (reserve : Nat) :
    OperationalTranslation (FiniteOccurrenceLookup.gslt Key Value)
      (gslt Key Value) where
  mapTerm := mapState reserve
  mapEquiv := by
    intro left right equal
    subst right
    rfl
  mapStep := by
    intro source target step
    exact lower_step reserve step

/-- Every target step beginning at a translated semantic state lifts back to
one source lookup step.  This is the local no-invention direction; it relies
on the target's deterministic separation of hit, advance, and frontier. -/
theorem lift_step (reserve : Nat)
    {source : FiniteOccurrenceLookup.State Key Value}
    {target : State Key Value}
    (step : Step (mapState reserve source) target) :
    ∃ sourceTarget,
      FiniteOccurrenceLookup.Step source sourceTarget ∧
        mapState reserve sourceTarget = target := by
  cases source with
  | scanning scan =>
      cases scan with
      | mk query visited remaining =>
          cases remaining with
          | nil =>
              let sourceStep : FiniteOccurrenceLookup.Step
                  (.scanning ⟨query, visited, []⟩)
                  (.finished query visited (.missing visited.length)) :=
                FiniteOccurrenceLookup.Step.miss query visited
              refine ⟨_, sourceStep, ?_⟩
              exact step_deterministic (lower_step reserve sourceStep) step
          | cons next remaining =>
              by_cases same : next.key = query
              · let sourceStep : FiniteOccurrenceLookup.Step
                    (.scanning ⟨query, visited, next :: remaining⟩)
                    (.finished query (visited ++ next :: remaining)
                      (.found visited.length next.value)) :=
                  FiniteOccurrenceLookup.Step.hit query visited next remaining
                    same
                refine ⟨_, sourceStep, ?_⟩
                exact step_deterministic (lower_step reserve sourceStep) step
              · let sourceStep : FiniteOccurrenceLookup.Step
                    (.scanning ⟨query, visited, next :: remaining⟩)
                    (.scanning ⟨query, visited ++ [next], remaining⟩) :=
                  FiniteOccurrenceLookup.Step.advance query visited next
                    remaining same
                refine ⟨_, sourceStep, ?_⟩
                exact step_deterministic (lower_step reserve sourceStep) step
  | finished query inventory observation =>
      cases step

/-- Forward preservation plus `lift_step` make the indexed reservation an
outgoing-covered translation, not merely a simulation. -/
def coveredTranslation (reserve : Nat) :
    CoveredTranslation (FiniteOccurrenceLookup.gslt Key Value)
      (gslt Key Value) where
  mapTerm := mapState reserve
  mapEquiv := by
    intro left right equal
    subst right
    rfl
  cover :=
    { mapStep := lower_step reserve
      liftStep := lift_step reserve }

/-- Consequently OSLF's possibility modality commutes exactly across this
stage.  Incoming coverage, needed for exact box transport, is deliberately a
separate obligation. -/
theorem diamond_exact (reserve : Nat)
    (predicate : Set (State Key Value)) :
    Set.preimage (mapState reserve) (gsltDiamond (gslt Key Value) predicate) =
      gsltDiamond (FiniteOccurrenceLookup.gslt Key Value)
        (Set.preimage (mapState reserve) predicate) :=
  Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor.CoveredTranslation.preimage_diamond
    (coveredTranslation reserve) predicate

/-- A finite scan is determined by its target, complete inventory, and cursor
position. -/
theorem scan_ext_of_inventory_position
    {left right : Scan Key Value}
    (targetEqual : left.target = right.target)
    (inventoryEqual : left.inventory = right.inventory)
    (positionEqual : left.position = right.position) : left = right := by
  cases left with
  | mk leftTarget leftVisited leftRemaining =>
      cases right with
      | mk rightTarget rightVisited rightRemaining =>
          simp only [Scan.inventory, Scan.position] at targetEqual inventoryEqual positionEqual
          have visitedEqual : leftVisited = rightVisited := by
            calc
              leftVisited =
                  (leftVisited ++ leftRemaining).take leftVisited.length := by
                simp
              _ = (rightVisited ++ rightRemaining).take rightVisited.length := by
                rw [inventoryEqual, positionEqual]
              _ = rightVisited := by simp
          have remainingEqual : leftRemaining = rightRemaining := by
            calc
              leftRemaining =
                  (leftVisited ++ leftRemaining).drop leftVisited.length := by
                simp
              _ = (rightVisited ++ rightRemaining).drop rightVisited.length := by
                rw [inventoryEqual, positionEqual]
              _ = rightRemaining := by simp
          subst rightTarget
          subst rightVisited
          subst rightRemaining
          rfl

/-- The indexed image retains enough information to reconstruct the source
finite-scan state. -/
theorem mapState_injective (reserve : Nat) :
    Function.Injective (mapState (Key := Key) (Value := Value) reserve) := by
  intro left right equal
  cases left with
  | scanning leftScan =>
      cases right with
      | scanning rightScan =>
          apply congrArg FiniteOccurrenceLookup.State.scanning
          apply scan_ext_of_inventory_position
          · simpa [mapState] using congrArg State.target equal
          · simpa [mapState] using congrArg State.inventory equal
          · have controlEqual := congrArg State.control equal
            simpa [mapState] using Control.scanning.inj controlEqual
      | finished rightTarget rightInventory rightObservation =>
          have controlEqual := congrArg State.control equal
          simp [mapState] at controlEqual
  | finished leftTarget leftInventory leftObservation =>
      cases right with
      | scanning rightScan =>
          have controlEqual := congrArg State.control equal
          simp [mapState] at controlEqual
      | finished rightTarget rightInventory rightObservation =>
          have targetEqual : leftTarget = rightTarget := by
            simpa [mapState] using congrArg State.target equal
          have inventoryEqual : leftInventory = rightInventory := by
            simpa [mapState] using congrArg State.inventory equal
          have observationEqual : leftObservation = rightObservation := by
            have controlEqual := congrArg State.control equal
            simpa [mapState] using Control.finished.inj controlEqual
          subst rightTarget
          subst rightInventory
          subst rightObservation
          rfl

/-- An exact `getElem?` witness splits a list at that occurrence. -/
theorem splitAt_of_getElem?_eq_some
    {inventory : List (Entry Key Value)} {cursor : Nat}
    {entry : Entry Key Value} (found : inventory[cursor]? = some entry) :
    inventory = inventory.take cursor ++
      entry :: inventory.drop (cursor + 1) := by
  induction inventory generalizing cursor with
  | nil => simp at found
  | cons head tail induction =>
      cases cursor with
      | zero =>
          simp at found
          subst entry
          simp
      | succ cursor =>
          simp only [List.getElem?_cons_succ] at found
          have tailSplit := induction found
          simpa [Nat.succ_eq_add_one] using congrArg (List.cons head) tailSplit

/-- Every primitive indexed target step has source finite-scan endpoints.
This global representation lemma is stronger than local coverage at image
states and makes the later incoming proof independent of target-step
inversion tricks. -/
theorem step_has_source_preimage
    {targetSource targetTarget : State Key Value}
    (step : Step targetSource targetTarget) :
    ∃ sourceSource sourceTarget,
      FiniteOccurrenceLookup.Step sourceSource sourceTarget ∧
        mapState targetSource.reserve sourceSource = targetSource ∧
        mapState targetSource.reserve sourceTarget = targetTarget := by
  cases step with
  | hit target inventory reserve cursor entry found same =>
      have bound : cursor < inventory.length :=
        (List.getElem?_eq_some_iff.mp found).1
      have split := splitAt_of_getElem?_eq_some found
      let before : FiniteOccurrenceLookup.State Key Value :=
        .scanning
          ⟨target, inventory.take cursor,
            entry :: inventory.drop (cursor + 1)⟩
      let after : FiniteOccurrenceLookup.State Key Value :=
        .finished target
          (inventory.take cursor ++ entry :: inventory.drop (cursor + 1))
          (.found (inventory.take cursor).length entry.value)
      refine ⟨before, after, ?_, ?_, ?_⟩
      · exact FiniteOccurrenceLookup.Step.hit target _ entry _ same
      · simp only [before, mapState, Scan.inventory, Scan.position]
        rw [← split]
        simp [Nat.min_eq_left (Nat.le_of_lt bound)]
      · simp only [after, mapState]
        rw [← split]
        simp [Nat.min_eq_left (Nat.le_of_lt bound)]
  | advance target inventory reserve cursor entry found different licensed =>
      have bound : cursor < inventory.length :=
        (List.getElem?_eq_some_iff.mp found).1
      have split := splitAt_of_getElem?_eq_some found
      let before : FiniteOccurrenceLookup.State Key Value :=
        .scanning
          ⟨target, inventory.take cursor,
            entry :: inventory.drop (cursor + 1)⟩
      let after : FiniteOccurrenceLookup.State Key Value :=
        .scanning
          ⟨target, inventory.take cursor ++ [entry],
            inventory.drop (cursor + 1)⟩
      refine ⟨before, after, ?_, ?_, ?_⟩
      · exact FiniteOccurrenceLookup.Step.advance target _ entry _ different
      · simp only [before, mapState, Scan.inventory, Scan.position]
        rw [← split]
        simp [Nat.min_eq_left (Nat.le_of_lt bound)]
      · simp only [after, mapState, Scan.inventory, Scan.position]
        rw [List.append_assoc]
        simp only [List.singleton_append]
        rw [← split]
        simp [Nat.min_eq_left (Nat.le_of_lt bound)]
  | miss target inventory reserve =>
      refine ⟨.scanning ⟨target, inventory, []⟩,
        .finished target inventory (.missing inventory.length), ?_, ?_, ?_⟩
      · exact FiniteOccurrenceLookup.Step.miss target inventory
      · simp [mapState, Scan.inventory, Scan.position]
      · rfl

/-- Primitive indexed lookup preserves its allocation reserve exactly. -/
theorem step_preserves_reserve {source target : State Key Value}
    (step : Step source target) : target.reserve = source.reserve := by
  cases step <;> rfl

/-- Incoming target steps at image states lift to exact source predecessors.
This supplies the predecessor leg needed by OSLF's box modality. -/
theorem lift_incoming (reserve : Nat)
    {source : FiniteOccurrenceLookup.State Key Value}
    {targetPredecessor : State Key Value}
    (step : Step targetPredecessor (mapState reserve source)) :
    ∃ sourcePredecessor,
      FiniteOccurrenceLookup.Step sourcePredecessor source ∧
        mapState reserve sourcePredecessor = targetPredecessor := by
  obtain ⟨sourcePredecessor, sourceTarget, sourceStep,
      predecessorEqual, targetEqual⟩ := step_has_source_preimage step
  have reserveEqual : targetPredecessor.reserve = reserve := by
    rw [← mapState_reserve reserve source]
    exact (step_preserves_reserve step).symm
  have predecessorEqual' :
      mapState reserve sourcePredecessor = targetPredecessor := by
    simpa [reserveEqual] using predecessorEqual
  have targetEqual' :
      mapState reserve sourceTarget = mapState reserve source := by
    simpa [reserveEqual] using targetEqual
  have sourceTargetEqual : sourceTarget = source :=
    mapState_injective reserve targetEqual'
  subst sourceTarget
  exact ⟨sourcePredecessor, sourceStep, predecessorEqual'⟩

/-- The reserved cursor is bounded in both operational directions. -/
def modalTranslation (reserve : Nat) :
    Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor.ModalTranslation
      (FiniteOccurrenceLookup.gslt Key Value) (gslt Key Value) where
  toCoveredTranslation := coveredTranslation reserve
  liftIncoming := lift_incoming reserve

/-- Exact OSLF native-theory morphism of the primitive reserved-cursor
stage. -/
def exactNTT (reserve : Nat) :
    Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor.ModalPredicateTheory.Hom
      (Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor.oslfModalObject
        (gslt Key Value))
      (Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor.oslfModalObject
        (FiniteOccurrenceLookup.gslt Key Value)) :=
  (modalTranslation reserve).pullback

/-- Exact predecessor-universal transport is now earned rather than assumed. -/
theorem box_exact (reserve : Nat)
    (predicate : Set ((gslt Key Value).Term)) :
    (Set.preimage (mapState reserve)
        (gsltBox (gslt Key Value) predicate) :
      Set ((FiniteOccurrenceLookup.gslt Key Value).Term)) =
      gsltBox (FiniteOccurrenceLookup.gslt Key Value)
        (Set.preimage (mapState reserve) predicate) := by
  change
    Set.preimage (modalTranslation reserve).mapTerm
        (gsltBox (gslt Key Value) predicate) =
      gsltBox (FiniteOccurrenceLookup.gslt Key Value)
        (Set.preimage (modalTranslation reserve).mapTerm predicate)
  exact
    Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor.ModalTranslation.preimage_box
      (modalTranslation reserve) predicate

/-- Negative control: no target step entering an image state can have a
predecessor outside the image of every source state. -/
theorem no_incoming_image_escape (reserve : Nat)
    (source : FiniteOccurrenceLookup.State Key Value) :
    ¬ ∃ targetPredecessor,
      Step targetPredecessor (mapState reserve source) ∧
        ∀ sourcePredecessor,
          mapState reserve sourcePredecessor ≠ targetPredecessor := by
  rintro ⟨targetPredecessor, step, outside⟩
  obtain ⟨sourcePredecessor, _, equal⟩ := lift_incoming reserve step
  exact outside sourcePredecessor equal

/-- Positive incoming control: a concrete target hit reconstructs the exact
source scan predecessor. -/
theorem incoming_hit_lifts (reserve : Nat)
    (target : Key) (visited : List (Entry Key Value))
    (next : Entry Key Value) (remaining : List (Entry Key Value))
    (same : next.key = target) :
    ∃ sourcePredecessor,
      FiniteOccurrenceLookup.Step sourcePredecessor
          (.finished target (visited ++ next :: remaining)
            (.found visited.length next.value)) ∧
        mapState reserve sourcePredecessor =
          ⟨target, visited ++ next :: remaining, reserve,
            .scanning visited.length⟩ := by
  let targetStep : Step
      ⟨target, visited ++ next :: remaining, reserve,
        .scanning visited.length⟩
      (mapState reserve
        (.finished target (visited ++ next :: remaining)
          (.found visited.length next.value))) :=
    Step.hit target (visited ++ next :: remaining) reserve visited.length next
      (by simp) same
  exact lift_incoming reserve targetStep

/-- The strict translation is also available in the composable category of
path-valued GSLT realizations. -/
def realization (reserve : Nat) :
    OperationalRealization (FiniteOccurrenceLookup.gslt Key Value)
      (gslt Key Value) :=
  OperationalRealization.ofTranslation (translation reserve)

/-- OSLF derives the native modal transport of the reserved-cursor stage. -/
def reachabilityNTT (reserve : Nat) :
    ForwardModalPredicateTheory.Hom
      (oslfForwardModalObject (gslt Key Value).closure)
      (oslfForwardModalObject
        (FiniteOccurrenceLookup.gslt Key Value).closure) :=
  (realization (Key := Key) (Value := Value) reserve).closureOSLFPullback

/-- A source hit retains exactly its occurrence index and value in the
reserved target machine. -/
theorem hit_observation_exact (reserve : Nat)
    (target : Key) (visited : List (Entry Key Value))
    (next : Entry Key Value) (remaining : List (Entry Key Value))
    (same : next.key = target) :
    Step
      (mapState reserve (.scanning ⟨target, visited, next :: remaining⟩))
      (mapState reserve
        (.finished target (visited ++ next :: remaining)
          (.found visited.length next.value))) :=
  lower_step reserve
    (FiniteOccurrenceLookup.Step.hit target visited next remaining same)

/-- A reserve does not move the live missing frontier. -/
theorem missing_frontier_independent_of_reserve (reserve : Nat)
    (target : Key) (inventory : List (Entry Key Value)) :
    Step
      ⟨target, inventory, reserve, .scanning inventory.length⟩
      ⟨target, inventory, reserve,
        .finished (.missing inventory.length)⟩ :=
  Step.miss target inventory reserve

/-- Positive control: capacity may extend strictly past the live frontier. -/
theorem nonzero_reserve_extends_capacity (state : State Key Value)
    (positive : 0 < state.reserve) :
    state.liveFrontier < state.capacity := by
  simp [State.liveFrontier, State.capacity]
  omega

/-- Negative control: even with spare capacity, the only primitive missing
step begins at the live frontier. -/
theorem missing_cannot_begin_in_reserved_tail
    (target : Key) (inventory : List (Entry Key Value))
    (reserve cursor : Nat) (beyond : inventory.length < cursor) :
    ¬ Step ⟨target, inventory, reserve, .scanning cursor⟩
        ⟨target, inventory, reserve,
          .finished (.missing inventory.length)⟩ := by
  intro step
  cases step
  omega

#print axioms lower_step
#print axioms step_deterministic
#print axioms translation
#print axioms lift_step
#print axioms coveredTranslation
#print axioms diamond_exact
#print axioms scan_ext_of_inventory_position
#print axioms mapState_injective
#print axioms splitAt_of_getElem?_eq_some
#print axioms step_has_source_preimage
#print axioms step_preserves_reserve
#print axioms lift_incoming
#print axioms modalTranslation
#print axioms exactNTT
#print axioms box_exact
#print axioms no_incoming_image_escape
#print axioms incoming_hit_lifts
#print axioms realization
#print axioms reachabilityNTT
#print axioms hit_observation_exact
#print axioms missing_frontier_independent_of_reserve
#print axioms nonzero_reserve_extends_capacity
#print axioms missing_cannot_begin_in_reserved_tail

end Mettapedia.GSLT.ReservedFiniteCursorLookup
