import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Granularity

/-!
# Steps at the grain of kinds

A location is a kind of atom in a space, and the state gives every kind its
multiplicity.  This module has the operations of a space as steps at that grain,
each an instance of a local rule (`FootprintedSpaceTransactions.LocalRule`), with
how it fires and what it reads and writes.

| Step | Fires when | Result | Reads | Writes |
|---|---|---|---|---|
| `addKind kind` | always | one more of `kind` | nothing | `kind` |
| `removeKind kind` | `kind` is there | one less of `kind` | nothing | `kind` |
| `seeKind kind` | `kind` is there | the state | `kind` | nothing |
| `addKindUnless kind watched` | `watched` is not there | one more of `kind` | `watched` | `kind` |
| `consumeKind kind guard` | the guard holds and `kind` is there | one less of `kind` | what the guard reads | `kind` |
| `replaceKind old new` | `old` is there | one less of `old`, one more of `new` | nothing | `old`, `new` |

`replaceKind` is the write of a cell at this grain: a cell that holds a value is
the kind of that value in the cell, present once.

The kind `kind` of a removal, a consumption or a replacement is also read: the
step fires only where it is present.  That read is not declared among the reads;
it is carried by what the rule consumes, and the written locations count as read
in every test of independence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.GSLT.SeparationAlgebra

universe u

variable {Location : Type u} [DecidableEq Location]

/-! ## Multiplicities of the empty bag and of one atom -/

theorem marking_zero : marking (0 : Multiset Location) = 0 :=
  funext fun _ => Multiset.count_zero _

theorem marking_singleton (kind : Location) :
    marking ({kind} : Multiset Location) = Pi.single kind 1 := by
  funext other
  show Multiset.count other {kind} = (Pi.single kind 1 : Location → ℕ) other
  rw [Multiset.count_singleton, Pi.single_apply]

/-! ## Rules -/

namespace KindRules

/-- A kind is present, at least once; nothing changes. -/
def present (kind : Location) : LocalRule Location ℕ where
  consumed := 0
  produced := 0
  guard state := 0 < state kind
  reads := {kind}
  writes := ∅
  consumed_outside _ _ := rfl
  produced_outside _ _ := rfl
  guard_local agrees holds := by
    rwa [← agrees kind (Finset.mem_union_left _ (Finset.mem_singleton_self _))]

/-- Add one occurrence of `kind` unless `watched` is present.  The guard asks for
an absence, and declares the kind it reads. -/
def addUnless (kind watched : Location) : LocalRule Location ℕ where
  consumed := 0
  produced := Pi.single kind 1
  guard state := state watched = 0
  reads := {watched}
  writes := {kind}
  consumed_outside _ _ := rfl
  produced_outside other outside := by
    have different : other ≠ kind := by simpa using outside
    simp [different]
  guard_local agrees holds := by
    rwa [← agrees watched (Finset.mem_union_left _ (Finset.mem_singleton_self _))]

/-- Remove one occurrence of `kind` when a guard holds.  The guard is a readout
of a proposition: it declares the kinds it reads. -/
def consume (kind : Location) (guard : Readout Location ℕ Prop) : LocalRule Location ℕ :=
  { markingRule {kind} 0 with
    guard := guard.value
    reads := guard.reads
    guard_local := fun agrees holds =>
      (guard.value_local (agreesOn_mono Finset.subset_union_left agrees)).mp holds }

end KindRules

/-! ## Steps -/

/-- Add one occurrence of a kind. -/
def addKind (kind : Location) : Step Location ℕ :=
  Step.ofCountRule (markingRule 0 {kind}) fun _ => isTrue trivial

/-- Remove one occurrence of a kind. -/
def removeKind (kind : Location) : Step Location ℕ :=
  Step.ofCountRule (markingRule {kind} 0) fun _ => isTrue trivial

/-- See that a kind is present, and leave it there. -/
def seeKind (kind : Location) : Step Location ℕ :=
  Step.ofCountRule (KindRules.present kind) fun state => Nat.decLt 0 (state kind)

/-- Add one occurrence of `kind` unless `watched` is present. -/
def addKindUnless (kind watched : Location) : Step Location ℕ :=
  Step.ofCountRule (KindRules.addUnless kind watched) fun state =>
    inferInstanceAs (Decidable (state watched = 0))

/-- Remove one occurrence of `kind` when a guard holds, as one step. -/
def consumeKind (kind : Location) (guard : Readout Location ℕ Prop)
    (decideGuard : DecidablePred guard.value) : Step Location ℕ :=
  Step.ofCountRule (KindRules.consume kind guard) decideGuard

/-- Take one occurrence of `old` and put one of `new`: the write of a cell. -/
def replaceKind (old new : Location) : Step Location ℕ :=
  Step.ofCountRule (markingRule {old} {new}) fun _ => isTrue trivial

/-! ## How they fire -/

/-- **Adding a kind fires on every state**, and adds one occurrence. -/
theorem fire_addKind (kind : Location) (state : Location → ℕ) :
    (addKind kind).fire state = some (state + Pi.single kind 1) :=
  (addKind kind).fire_eq_some_iff.mpr
    ⟨trivial, state, fun _ => trivial, fun _ => trivial,
      by show state = marking 0 + state; rw [marking_zero, zero_add],
      by show state + Pi.single kind 1 = marking {kind} + state; rw [marking_singleton, add_comm]⟩

/-- **Removing a kind fires exactly where it is present**, and the state is the
result with the occurrence put back. -/
theorem fire_removeKind_eq_some_iff (kind : Location) (state target : Location → ℕ) :
    (removeKind kind).fire state = some target ↔ state = target + Pi.single kind 1 := by
  rw [(removeKind kind).fire_eq_some_iff]
  constructor
  · rintro ⟨-, frame, -, -, sourceEq, targetEq⟩
    have same : target = frame := by
      rw [targetEq]
      show marking 0 + frame = frame
      rw [marking_zero, zero_add]
    rw [sourceEq, same]
    show marking {kind} + frame = frame + Pi.single kind 1
    rw [marking_singleton, add_comm]
  · rintro rfl
    exact ⟨trivial, target, fun _ => trivial, fun _ => trivial,
      by show target + Pi.single kind 1 = marking {kind} + target; rw [marking_singleton, add_comm],
      by show target = marking 0 + target; rw [marking_zero, zero_add]⟩

/-- Removing a kind that is not there does not fire. -/
theorem fire_removeKind_eq_none (kind : Location) {state : Location → ℕ}
    (absent : state kind = 0) : (removeKind kind).fire state = none := by
  cases fired : (removeKind kind).fire state with
  | none => rfl
  | some target =>
      have same := congrFun ((fire_removeKind_eq_some_iff kind state target).mp fired) kind
      rw [absent] at same
      simp at same

/-- **Seeing a kind fires exactly where it is present**, and changes nothing. -/
theorem fire_seeKind_eq_some_iff (kind : Location) (state target : Location → ℕ) :
    (seeKind kind).fire state = some target ↔ 0 < state kind ∧ target = state := by
  rw [(seeKind kind).fire_eq_some_iff]
  constructor
  · rintro ⟨present, frame, -, -, sourceEq, targetEq⟩
    refine ⟨present, ?_⟩
    rw [targetEq, sourceEq]
    rfl
  · rintro ⟨present, rfl⟩
    exact ⟨present, target, fun _ => trivial, fun _ => trivial, (zero_add target).symm,
      (zero_add target).symm⟩

/-- **The guarded addition fires exactly where the watched kind is absent.** -/
theorem fire_addKindUnless_eq_some_iff (kind watched : Location) (state target : Location → ℕ) :
    (addKindUnless kind watched).fire state = some target ↔
      state watched = 0 ∧ target = state + Pi.single kind 1 := by
  rw [(addKindUnless kind watched).fire_eq_some_iff]
  constructor
  · rintro ⟨absent, frame, -, -, sourceEq, targetEq⟩
    refine ⟨absent, ?_⟩
    have same : state = frame := sourceEq.trans (zero_add frame)
    rw [targetEq, same]
    exact add_comm _ _
  · rintro ⟨absent, rfl⟩
    exact ⟨absent, state, fun _ => trivial, fun _ => trivial, (zero_add state).symm,
      add_comm _ _⟩

/-- **The write of a cell fires exactly where the old value is present**: the
state is a frame with the old value, and the result is that frame with the new. -/
theorem fire_replaceKind_eq_some_iff (old new : Location) (state target : Location → ℕ) :
    (replaceKind old new).fire state = some target ↔
      ∃ frame : Location → ℕ,
        state = frame + Pi.single old 1 ∧ target = frame + Pi.single new 1 := by
  rw [(replaceKind old new).fire_eq_some_iff]
  constructor
  · rintro ⟨-, frame, -, -, sourceEq, targetEq⟩
    refine ⟨frame, ?_, ?_⟩
    · rw [sourceEq]
      show marking {old} + frame = frame + Pi.single old 1
      rw [marking_singleton, add_comm]
    · rw [targetEq]
      show marking {new} + frame = frame + Pi.single new 1
      rw [marking_singleton, add_comm]
  · rintro ⟨frame, rfl, rfl⟩
    exact ⟨trivial, frame, fun _ => trivial, fun _ => trivial,
      by show frame + Pi.single old 1 = marking {old} + frame; rw [marking_singleton, add_comm],
      by show frame + Pi.single new 1 = marking {new} + frame; rw [marking_singleton, add_comm]⟩

/-- **`consumeKind` is one step**: it fires exactly where its guard holds and the
kind is present. -/
theorem fire_consumeKind_eq_some_iff (kind : Location) (guard : Readout Location ℕ Prop)
    (decideGuard : DecidablePred guard.value) (state target : Location → ℕ) :
    (consumeKind kind guard decideGuard).fire state = some target ↔
      guard.value state ∧ (removeKind kind).fire state = some target := by
  rw [(consumeKind kind guard decideGuard).fire_eq_some_iff, (removeKind kind).fire_eq_some_iff]
  constructor
  · rintro ⟨guarded, frame, consumedSeparate, producedSeparate, sourceEq, targetEq⟩
    exact ⟨guarded, trivial, frame, consumedSeparate, producedSeparate, sourceEq, targetEq⟩
  · rintro ⟨guarded, -, frame, consumedSeparate, producedSeparate, sourceEq, targetEq⟩
    exact ⟨guarded, frame, consumedSeparate, producedSeparate, sourceEq, targetEq⟩

/-! ## What they read and write -/

theorem addKind_footprint (kind : Location) :
    (addKind kind).rule.reads = ∅ ∧ (addKind kind).rule.writes = {kind} := by
  refine ⟨rfl, ?_⟩
  show (0 : Multiset Location).toFinset ∪ ({kind} : Multiset Location).toFinset = {kind}
  simp

theorem removeKind_footprint (kind : Location) :
    (removeKind kind).rule.reads = ∅ ∧ (removeKind kind).rule.writes = {kind} := by
  refine ⟨rfl, ?_⟩
  show ({kind} : Multiset Location).toFinset ∪ (0 : Multiset Location).toFinset = {kind}
  simp

theorem seeKind_footprint (kind : Location) :
    (seeKind kind).rule.reads = {kind} ∧ (seeKind kind).rule.writes = ∅ :=
  ⟨rfl, rfl⟩

theorem addKindUnless_footprint (kind watched : Location) :
    (addKindUnless kind watched).rule.reads = {watched} ∧
      (addKindUnless kind watched).rule.writes = {kind} :=
  ⟨rfl, rfl⟩

theorem consumeKind_footprint (kind : Location) (guard : Readout Location ℕ Prop)
    (decideGuard : DecidablePred guard.value) :
    (consumeKind kind guard decideGuard).rule.reads = guard.reads ∧
      (consumeKind kind guard decideGuard).rule.writes = {kind} := by
  refine ⟨rfl, ?_⟩
  show ({kind} : Multiset Location).toFinset ∪ (0 : Multiset Location).toFinset = {kind}
  simp

theorem replaceKind_footprint (old new : Location) :
    (replaceKind old new).rule.reads = ∅ ∧ (replaceKind old new).rule.writes = {old, new} := by
  refine ⟨rfl, ?_⟩
  show ({old} : Multiset Location).toFinset ∪ ({new} : Multiset Location).toFinset = {old, new}
  ext location
  simp

/-! ## Controls -/

namespace KindControls

open AddOnly (Kind noKinds)

/-- One `a`. -/
def oneA : Kind → ℕ := Pi.single Kind.a 1

/-- At the two kinds of `Regions.Granularity`, adding a kind is the addition
defined there. -/
theorem addKind_eq_addOnly (kind : Kind) : addKind kind = AddOnly.addKind kind :=
  rfl

/-- **Positive**: adding fires on the empty state, and leaves one occurrence.
**Negative**: it does not leave the state as it was. -/
theorem addKind_fires :
    ((addKind Kind.a).fire noKinds).map (fun world => world .a) = some 1 ∧
      ((addKind Kind.a).fire noKinds).map (fun world => world .a) ≠ some 0 := by
  decide

/-- **Positive**: removing fires where the kind is.  **Negative**: and not where
it is not. -/
theorem removeKind_fires :
    ((removeKind Kind.a).fire oneA).map (fun world => world .a) = some 0 ∧
      ((removeKind Kind.a).fire noKinds).isSome = false := by
  decide

/-- **Positive**: seeing fires where the kind is.  **Negative**: and not where it
is not. -/
theorem seeKind_fires :
    ((seeKind Kind.a).fire oneA).isSome = true ∧
      ((seeKind Kind.a).fire noKinds).isSome = false := by
  decide

/-- **Positive**: the guarded addition fires where the watched kind is absent.
**Negative**: and not where it is present. -/
theorem addKindUnless_fires :
    ((addKindUnless Kind.b Kind.a).fire noKinds).map (fun world => world .b) = some 1 ∧
      ((addKindUnless Kind.b Kind.a).fire oneA).isSome = false := by
  decide

/-- **Positive**: the write of a cell fires where the old value is.  **Negative**:
and not where it is not. -/
theorem replaceKind_fires :
    ((replaceKind Kind.a Kind.b).fire oneA).map (fun world => (world .a, world .b)) =
        some (0, 1) ∧
      ((replaceKind Kind.a Kind.b).fire noKinds).isSome = false := by
  decide

/-- The proposition that a `b` is there, read at that kind. -/
def hasB : Readout Kind ℕ Prop :=
  ⟨{Kind.b}, fun state => 0 < state Kind.b,
    fun agrees => by rw [agrees Kind.b (Finset.mem_singleton_self _)]⟩

/-- Consume an `a` when a `b` is there. -/
def consumeAIfB : Step Kind ℕ :=
  consumeKind Kind.a hasB fun state => Nat.decLt 0 (state Kind.b)

/-- **Positive**: with the `b` there, the guarded consumption takes the `a`.
**Negative**: without it, it does not fire, although the `a` is there. -/
theorem consumeKind_fires :
    (consumeAIfB.fire (oneA + Pi.single Kind.b 1)).map (fun world => world .a) = some 0 ∧
      (consumeAIfB.fire oneA).isSome = false := by
  decide

end KindControls

#print axioms fire_addKind
#print axioms fire_removeKind_eq_some_iff
#print axioms fire_removeKind_eq_none
#print axioms fire_seeKind_eq_some_iff
#print axioms fire_addKindUnless_eq_some_iff
#print axioms fire_replaceKind_eq_some_iff
#print axioms fire_consumeKind_eq_some_iff
#print axioms addKind_footprint
#print axioms removeKind_footprint
#print axioms seeKind_footprint
#print axioms addKindUnless_footprint
#print axioms consumeKind_footprint
#print axioms replaceKind_footprint
#print axioms KindControls.addKind_eq_addOnly
#print axioms KindControls.addKind_fires
#print axioms KindControls.removeKind_fires
#print axioms KindControls.seeKind_fires
#print axioms KindControls.addKindUnless_fires
#print axioms KindControls.replaceKind_fires
#print axioms KindControls.consumeKind_fires

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
