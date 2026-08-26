import Mettapedia.GSLT.LanguageDef.AuthoritativeSlotTrailCompilation

/-!
# Scoped authoritative slots and exact environment reconstruction

An activation-local slot array must distinguish three states:

* a variable declared in the activation but still unbound;
* an alias to another activation slot;
* a concrete value.

In particular, a declared-but-unbound local variable shadows an outer binding.
It is not the same as a key outside the activation inventory.  This module
gives that distinction an explicit semantics, resolves aliases with bounded
fuel, fails closed on cyclic alias state, and reuses the authoritative undo
trail to prove exact rollback.

The boundary observation is `Option (Option Value)`: the outer `none` means
that the local frame is invalid and cannot be materialized, `some none` means
a valid declared-but-unbound variable, and `some (some value)` means a valid
bound value.
-/

namespace Mettapedia.GSLT.LanguageDef.ScopedAuthoritativeSlotCompilation

open FiniteEnvironmentCompilation
open AuthoritativeSlotTrailCompilation

universe uKey uValue

/-- The nonempty payload of one authoritative local slot.  Absence from the
dense cell array is the third state: declared but unbound. -/
inductive SlotPayload {Key : Type uKey} (inventory : Inventory Key)
    (Value : Type uValue) where
  | alias (target : inventory.Slot)
  | value (stored : Value)

/-- A complete activation-local cell array.  `none` is declared-unbound. -/
abbrev SlotEnvironment {Key : Type uKey} (inventory : Inventory Key)
    (Value : Type uValue) := DenseEnvironment inventory (SlotPayload inventory Value)

/-- The three valid lookup observations plus an explicit invalid state. -/
inductive LocalLookup (Value : Type uValue) where
  | declaredUnbound
  | value (stored : Value)
  | invalid
deriving Repr

/-- Resolve one slot through aliases.  Exhausted fuel detects a cyclic or
otherwise non-well-founded alias state. -/
def resolveLocal (slots : SlotEnvironment inventory Value) :
    Nat -> inventory.Slot -> LocalLookup Value
  | 0, _ => .invalid
  | fuel + 1, slot =>
      match slots slot with
      | none => .declaredUnbound
      | some (.value stored) => .value stored
      | some (.alias target) => resolveLocal slots fuel target

/-- One more step than the number of slots is sufficient for every acyclic
alias chain and still rejects every cycle. -/
def lookupLocal (slots : SlotEnvironment inventory Value)
    (slot : inventory.Slot) : LocalLookup Value :=
  resolveLocal slots (inventory.keys.length + 1) slot

/-- Whether one lookup is safe to publish. -/
def LocalLookup.valid : LocalLookup Value -> Bool
  | .invalid => false
  | _ => true

/-- A local frame is materializable exactly when every declared slot resolves
to an unbound variable or a value.  This is an executable admission check. -/
def frameValid (slots : SlotEnvironment inventory Value) : Bool :=
  (List.ofFn fun slot : inventory.Slot =>
    (lookupLocal slots slot).valid).all id

/-- Read a complete environment without hiding an invalid local frame.  Keys
outside the inventory are read from the outer environment. -/
def readBoundary [DecidableEq Key] (inventory : Inventory Key)
    (outer : SourceEnvironment Key Value)
    (slots : SlotEnvironment inventory Value) (key : Key) :
    Option (Option Value) :=
  match inventory.resolve? key with
  | none => some (outer key)
  | some slot =>
      match lookupLocal slots slot with
      | .declaredUnbound => some none
      | .value stored => some (some stored)
      | .invalid => none

/-- A checked escape materializes an ordinary finite-binding environment once.
An invalid alias state declines instead of manufacturing an environment. -/
def materialize? [DecidableEq Key]
    (inventory : Inventory Key) (outer : SourceEnvironment Key Value)
    (slots : SlotEnvironment inventory Value) :
    Option (SourceEnvironment Key Value) :=
  if frameValid slots then
    some fun key => (readBoundary inventory outer slots key).getD none
  else
    none

/-- A key outside the activation inventory is preserved exactly. -/
theorem readBoundary_outside [DecidableEq Key]
    (inventory : Inventory Key) (outer : SourceEnvironment Key Value)
    (slots : SlotEnvironment inventory Value) (key : Key)
    (outside : key ∉ inventory.keys) :
    readBoundary inventory outer slots key = some (outer key) := by
  have unresolved : inventory.resolve? key = none := by
    cases selected : inventory.resolve? key with
    | none => rfl
    | some slot =>
        exfalso
        exact outside
          ((inventory.exists_resolve?_eq_some_iff key).1
            ⟨slot, selected⟩)
  simp [readBoundary, unresolved]

/-- A declared-but-unbound key shadows the outer environment. -/
theorem readBoundary_declaredUnbound [DecidableEq Key]
    (inventory : Inventory Key) (outer : SourceEnvironment Key Value)
    (slots : SlotEnvironment inventory Value) (key : Key)
    (slot : inventory.Slot)
    (selected : inventory.resolve? key = some slot)
    (unbound : slots slot = none) :
    readBoundary inventory outer slots key = some none := by
  simp [readBoundary, selected, lookupLocal, resolveLocal, unbound]

/-- A local concrete value shadows the outer environment. -/
theorem readBoundary_value [DecidableEq Key]
    (inventory : Inventory Key) (outer : SourceEnvironment Key Value)
    (slots : SlotEnvironment inventory Value) (key : Key)
    (slot : inventory.Slot)
    (selected : inventory.resolve? key = some slot)
    (stored : Value) (present : slots slot = some (.value stored)) :
    readBoundary inventory outer slots key = some (some stored) := by
  simp [readBoundary, selected, lookupLocal, resolveLocal, present]

/-- A one-hop alias to a value has the same boundary observation as its target. -/
theorem readBoundary_alias_value [DecidableEq Key]
    (inventory : Inventory Key) (outer : SourceEnvironment Key Value)
    (slots : SlotEnvironment inventory Value) (key : Key)
    (source target : inventory.Slot)
    (selected : inventory.resolve? key = some source)
    (aliased : slots source = some (.alias target))
    (present : slots target = some (.value stored)) :
    readBoundary inventory outer slots key = some (some stored) := by
  have targetFuel : inventory.keys.length > 0 := by
    exact Nat.zero_lt_of_lt target.isLt
  obtain ⟨fuel, length_eq⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt targetFuel)
  simp [readBoundary, selected, lookupLocal, length_eq, resolveLocal,
    aliased, present]

/-- Physical validity makes checked materialization available. -/
theorem materialize?_of_valid [DecidableEq Key]
    (inventory : Inventory Key) (outer : SourceEnvironment Key Value)
    (slots : SlotEnvironment inventory Value)
    (valid : frameValid slots = true) :
    exists environment, materialize? inventory outer slots = some environment := by
  simp [materialize?, valid]

/-- Materialization reads every valid boundary observation exactly. -/
theorem materialize?_read [DecidableEq Key]
    (inventory : Inventory Key) (outer : SourceEnvironment Key Value)
    (slots : SlotEnvironment inventory Value)
    (valid : frameValid slots = true)
    (key : Key) (observed : Option Value)
    (read : readBoundary inventory outer slots key = some observed) :
    exists environment,
      materialize? inventory outer slots = some environment ∧
      environment key = observed := by
  refine ⟨fun candidate =>
    (readBoundary inventory outer slots candidate).getD none, ?_, ?_⟩
  · simp [materialize?, valid]
  · simp [read]

/-- A cyclic alias state is rejected at the boundary. -/
theorem readBoundary_invalid_of_lookup_invalid [DecidableEq Key]
    (inventory : Inventory Key) (outer : SourceEnvironment Key Value)
    (slots : SlotEnvironment inventory Value) (key : Key)
    (slot : inventory.Slot)
    (selected : inventory.resolve? key = some slot)
    (invalid : lookupLocal slots slot = .invalid) :
    readBoundary inventory outer slots key = none := by
  simp [readBoundary, selected, invalid]

/-- The existing complete-prior-cell trail restores alias, value, and
declared-unbound states exactly because `SlotPayload` is its value language. -/
theorem rollback_restores_scoped_state [DecidableEq Key]
    (inventory : Inventory Key)
    (state : State inventory (SlotPayload inventory Value))
    (updates : List (DenseWrite inventory (SlotPayload inventory Value))) :
    rollbackTo? inventory (mark state) (run inventory state updates) =
      some state :=
  rollbackTo?_run inventory state updates

/-! ## Positive and negative witnesses -/

private inductive Register where
  | local
  | outside
deriving DecidableEq

private def localInventory : Inventory Register where
  keys := [.local]
  nodup := by decide

private def outerEnvironment : SourceEnvironment Register Nat
  | .local => some 99
  | .outside => some 11

private def emptySlots : SlotEnvironment localInventory Nat :=
  emptyDenseEnvironment localInventory

/-- Positive shadowing witness: the local declaration is unbound even though
the outer environment contains a value under the same key. -/
example :
    readBoundary localInventory outerEnvironment emptySlots Register.local =
      some none := by
  apply readBoundary_declaredUnbound localInventory outerEnvironment
    emptySlots Register.local ⟨0, by decide⟩ rfl
  rfl

/-- A key not declared by the activation remains visible from outside. -/
example :
    readBoundary localInventory outerEnvironment emptySlots Register.outside =
      some (some 11) := by
  exact readBoundary_outside localInventory outerEnvironment emptySlots
    Register.outside (by decide)

private def selfAlias : SlotEnvironment localInventory Nat :=
  fun slot => some (.alias slot)

/-- Negative witness: a self-alias is not mistaken for an unbound variable. -/
example :
    readBoundary localInventory outerEnvironment selfAlias Register.local =
      none := by
  decide

/-- Invalid alias state fails the whole checked materialization admission. -/
example :
    materialize? localInventory outerEnvironment selfAlias = none := by
  decide

private def emptyState : State localInventory (SlotPayload localInventory Nat) :=
  { slots := emptySlots, trail := [] }

/-- A value write followed by rollback restores declared-unbound shadowing,
not the colliding outer value. -/
example :
    let slot : localInventory.Slot := ⟨0, by decide⟩
    let written := run localInventory emptyState [(slot, .value 7)]
    readBoundary localInventory outerEnvironment written.slots Register.local =
        some (some 7) ∧
      (rollbackTo? localInventory (mark emptyState) written).map
          (fun restored =>
            readBoundary localInventory outerEnvironment restored.slots
              Register.local) = some (some none) := by
  simp only
  constructor
  · decide
  · rw [rollbackTo?_run]
    decide

private inductive PairRegister where
  | left
  | right
deriving DecidableEq

private def pairInventory : Inventory PairRegister where
  keys := [.left, .right]
  nodup := by decide

private def pairOuter : SourceEnvironment PairRegister Nat := fun _ => none

private def aliasToValue : SlotEnvironment pairInventory Nat
  | ⟨0, _⟩ => some (.alias ⟨1, by decide⟩)
  | ⟨1, _⟩ => some (.value 5)

/-- Positive alias witness: a local alias resolves to the target value. -/
example :
    readBoundary pairInventory pairOuter aliasToValue PairRegister.left =
      some (some 5) := by
  decide

private def pairEmptyState :
    State pairInventory (SlotPayload pairInventory Nat) :=
  { slots := emptyDenseEnvironment pairInventory, trail := [] }

/-- Alias and value writes are both fully restored by the authoritative trail. -/
example :
    let left : pairInventory.Slot := ⟨0, by decide⟩
    let right : pairInventory.Slot := ⟨1, by decide⟩
    let written := run pairInventory pairEmptyState
      [(left, .alias right), (right, .value 5)]
    rollbackTo? pairInventory (mark pairEmptyState) written =
      some pairEmptyState := by
  simp only
  exact rollbackTo?_run pairInventory pairEmptyState
    [(⟨0, by decide⟩, .alias ⟨1, by decide⟩),
      (⟨1, by decide⟩, .value 5)]

#print axioms readBoundary_declaredUnbound
#print axioms readBoundary_alias_value
#print axioms materialize?_read
#print axioms rollback_restores_scoped_state

end Mettapedia.GSLT.LanguageDef.ScopedAuthoritativeSlotCompilation
