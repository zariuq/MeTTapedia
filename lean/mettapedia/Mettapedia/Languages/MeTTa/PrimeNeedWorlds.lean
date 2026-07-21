import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Union

/-!
# Prime Need worlds: finite causal configurations

An answer dependency receipt is not merely a bag of observed values.  It is a
finite causal configuration: every recorded event brings its finite causal
support, and the resulting set must be conflict-free.  This module isolates the
small order-theoretic core needed by dependency-sensitive publication.

`FiniteCausalBasis.support e` is the already-transitively-closed finite support
of event `e`, including `e` itself.  Closing a finite dependency set takes the
union of those supports.  The closure is extensive, monotone, and idempotent.
Consequently it is the least causally closed set containing the dependencies.

A `Configuration` is a closed, conflict-free finite event set.  Two
configurations are compatible exactly when closing their union remains
conflict-free.  Compatible configurations have a least upper bound; incompatible
ones have no common configuration extension.

The final section recovers the simpler pure-cell fragment: observations are
`(cell, outcome)` pairs and conflict means two different outcomes for one cell.
Functionality is exactly conflict-freedom for that relation.  This fragment does
not claim to model effects, allocation, or all native cell-state transitions;
those become event labels and causal/conflict laws in an instantiated basis.
-/

namespace Mettapedia.Languages.MeTTa.PrimeNeedWorlds

section CausalClosure

variable {Event : Type*} [DecidableEq Event]

/-- A finite presentation of reflexive-transitive causal support. -/
structure FiniteCausalBasis (Event : Type*) [DecidableEq Event] where
  support : Event -> Finset Event
  self_mem : forall event, event ∈ support event
  hereditary : forall {event predecessor}, predecessor ∈ support event ->
    support predecessor ⊆ support event

namespace FiniteCausalBasis

/-- Add every causal predecessor of every event in `events`. -/
def close (basis : FiniteCausalBasis Event) (events : Finset Event) :
    Finset Event :=
  events.biUnion basis.support

theorem mem_close_iff (basis : FiniteCausalBasis Event)
    {events : Finset Event} {event : Event} :
    event ∈ basis.close events ↔
      ∃ source ∈ events, event ∈ basis.support source := by
  simp [close]

/-- Causal closure contains its generators. -/
theorem subset_close (basis : FiniteCausalBasis Event)
    (events : Finset Event) :
    events ⊆ basis.close events := by
  intro event hevent
  exact basis.mem_close_iff.mpr
    ⟨event, hevent, basis.self_mem event⟩

/-- Causal closure is monotone. -/
theorem close_mono (basis : FiniteCausalBasis Event)
    {left right : Finset Event} (h : left ⊆ right) :
    basis.close left ⊆ basis.close right := by
  intro event hevent
  rcases basis.mem_close_iff.mp hevent with
    ⟨source, hsource, hsupport⟩
  exact basis.mem_close_iff.mpr
    ⟨source, h hsource, hsupport⟩

/-- Support is already transitive, so closing twice changes nothing. -/
theorem close_idempotent (basis : FiniteCausalBasis Event)
    (events : Finset Event) :
    basis.close (basis.close events) = basis.close events := by
  apply Finset.Subset.antisymm
  · intro event hevent
    rcases basis.mem_close_iff.mp hevent with
      ⟨middle, hmiddle, heventMiddle⟩
    rcases basis.mem_close_iff.mp hmiddle with
      ⟨source, hsource, hmiddleSource⟩
    exact basis.mem_close_iff.mpr
      ⟨source, hsource, basis.hereditary hmiddleSource heventMiddle⟩
  · exact basis.subset_close (basis.close events)

/-- A finite event set contains the causal support of all its events. -/
def Closed (basis : FiniteCausalBasis Event) (events : Finset Event) : Prop :=
  basis.close events = events

theorem close_closed (basis : FiniteCausalBasis Event)
    (events : Finset Event) :
    basis.Closed (basis.close events) :=
  basis.close_idempotent events

/-- `close dependencies` is the least causally closed set containing the
dependencies.  Unlike bare set containment, this includes all causal support. -/
theorem close_least (basis : FiniteCausalBasis Event)
    {dependencies world : Finset Event}
    (hDependencies : dependencies ⊆ world)
    (hWorld : basis.Closed world) :
    basis.close dependencies ⊆ world := by
  have hClosedSubset : basis.close dependencies ⊆ basis.close world :=
    basis.close_mono hDependencies
  simpa [Closed] using hWorld ▸ hClosedSubset

/-- A discrete event basis, useful when there are no causal predecessors beyond
the event itself. -/
def discrete : FiniteCausalBasis Event where
  support event := {event}
  self_mem event := Finset.mem_singleton_self event
  hereditary := by
    intro event predecessor h
    have : predecessor = event := Finset.mem_singleton.mp h
    subst predecessor
    exact Finset.Subset.rfl

end FiniteCausalBasis

variable (conflict : Event -> Event -> Prop)

/-- No two events in the set conflict. -/
def ConflictFree (events : Finset Event) : Prop :=
  ∀ ⦃left right⦄, left ∈ events -> right ∈ events -> ¬ conflict left right

omit [DecidableEq Event] in
theorem ConflictFree.mono {conflict : Event -> Event -> Prop}
    {small large : Finset Event}
    (hLarge : ConflictFree conflict large) (h : small ⊆ large) :
    ConflictFree conflict small := by
  intro left right hleft hright
  exact hLarge (h hleft) (h hright)

/-- A finite, causally closed, conflict-free event configuration. -/
structure Configuration (basis : FiniteCausalBasis Event)
    (conflict : Event -> Event -> Prop) where
  events : Finset Event
  closed : basis.Closed events
  consistent : ConflictFree conflict events

namespace Configuration

variable {conflict : Event -> Event -> Prop}
variable {basis : FiniteCausalBasis Event}

instance : LE (Configuration basis conflict) where
  le left right := left.events ⊆ right.events

theorem le_def {left right : Configuration basis conflict} :
    left ≤ right ↔ left.events ⊆ right.events :=
  Iff.rfl

/-- Compatibility includes causal closure: all causal support introduced by the
union must also remain conflict-free. -/
def Compatible (left right : Configuration basis conflict) : Prop :=
  ConflictFree conflict (basis.close (left.events ∪ right.events))

/-- The join of compatible configurations. -/
def join (left right : Configuration basis conflict)
    (h : Compatible left right) : Configuration basis conflict where
  events := basis.close (left.events ∪ right.events)
  closed := basis.close_closed _
  consistent := h

theorem left_le_join (left right : Configuration basis conflict)
    (h : Compatible left right) :
    left ≤ join left right h := by
  exact Finset.Subset.trans
    (Finset.subset_union_left : left.events ⊆ left.events ∪ right.events)
    (basis.subset_close _)

theorem right_le_join (left right : Configuration basis conflict)
    (h : Compatible left right) :
    right ≤ join left right h := by
  exact Finset.Subset.trans
    (Finset.subset_union_right : right.events ⊆ left.events ∪ right.events)
    (basis.subset_close _)

/-- The compatible join is the least common configuration extension. -/
theorem join_least (left right upper : Configuration basis conflict)
    (hLeft : left ≤ upper) (hRight : right ≤ upper)
    (hCompatible : Compatible left right) :
    join left right hCompatible ≤ upper := by
  apply basis.close_least
  · exact Finset.union_subset hLeft hRight
  · exact upper.closed

/-- Compatibility is exactly existence of a common configuration extension. -/
theorem compatible_iff_common_extension
    (left right : Configuration basis conflict) :
    Compatible left right ↔
      ∃ upper : Configuration basis conflict,
        left ≤ upper ∧ right ≤ upper := by
  constructor
  · intro h
    exact ⟨join left right h, left_le_join left right h,
      right_le_join left right h⟩
  · rintro ⟨upper, hLeft, hRight⟩
    have hClosedSubset :
        basis.close (left.events ∪ right.events) ⊆ upper.events :=
      basis.close_least (Finset.union_subset hLeft hRight) upper.closed
    exact upper.consistent.mono hClosedSubset

end Configuration

/-! ## Dependency receipts and least publication -/

/-- The events directly observed while producing one answer.  Causal support
is deliberately not duplicated in the receipt: publication computes it through
the independently supplied causal basis. -/
structure DependencyReceipt (Event : Type*) where
  roots : Finset Event

namespace DependencyReceipt

variable {conflict : Event -> Event -> Prop}
variable {basis : FiniteCausalBasis Event}

/-- Publish a receipt by adding exactly its causal support.  The validity
premise is substantive: conflicting closed receipts cannot be published. -/
def publish (receipt : DependencyReceipt Event)
    (valid : ConflictFree conflict (basis.close receipt.roots)) :
    Configuration basis conflict where
  events := basis.close receipt.roots
  closed := basis.close_closed _
  consistent := valid

/-- Every directly observed dependency is present in its publication. -/
theorem roots_subset_publish (receipt : DependencyReceipt Event)
    (valid : ConflictFree conflict (basis.close receipt.roots)) :
    receipt.roots ⊆ (receipt.publish valid).events :=
  basis.subset_close _

/-- Publication is the least valid world containing every directly observed
dependency.  The theorem has causal content because `close` may add events not
present in `receipt.roots`. -/
theorem publish_least (receipt : DependencyReceipt Event)
    (valid : ConflictFree conflict (basis.close receipt.roots))
    (world : Configuration basis conflict)
    (containsRoots : receipt.roots ⊆ world.events) :
    receipt.publish valid ≤ world :=
  basis.close_least containsRoots world.closed

end DependencyReceipt

/-! ## Native-facing receipt event shape -/

/-- A semantic receipt distinguishes observations of Need cells from explicit
effect dependencies.  Runtime handles and effect capabilities are encoded into
the parameters by a separate correspondence layer; they are not defined to be
C pointers here. -/
inductive ReceiptEvent (Cell Outcome Effect : Type*) where
  | observation (cell : Cell) (outcome : Outcome)
  | effect (event : Effect)
deriving DecidableEq

/-- Cell observations conflict when one cell has two outcomes.  Effect
conflicts are supplied by the instantiated effect algebra; the two event sorts
do not conflict merely because they co-occur. -/
def ReceiptConflict {Cell Outcome Effect : Type*}
    (effectConflict : Effect -> Effect -> Prop) :
    ReceiptEvent Cell Outcome Effect ->
      ReceiptEvent Cell Outcome Effect -> Prop
  | .observation leftCell leftOutcome,
      .observation rightCell rightOutcome =>
      leftCell = rightCell ∧ leftOutcome ≠ rightOutcome
  | .effect left, .effect right => effectConflict left right
  | _, _ => False

/-- The cell-observation projection of a receipt is functional. -/
def ReceiptObservationsFunctional
    {Cell Outcome Effect : Type*}
    (events : Finset (ReceiptEvent Cell Outcome Effect)) : Prop :=
  ∀ ⦃cell outcome other⦄,
    ReceiptEvent.observation cell outcome ∈ events ->
    ReceiptEvent.observation cell other ∈ events ->
    outcome = other

/-- Conflict-freedom for the full receipt event relation entails functionality
of its cell observations, independently of the chosen effect-conflict law. -/
theorem ConflictFree.receiptObservationsFunctional
    {Cell Outcome Effect : Type*}
    [DecidableEq Cell] [DecidableEq Outcome] [DecidableEq Effect]
    {effectConflict : Effect -> Effect -> Prop}
    {events : Finset (ReceiptEvent Cell Outcome Effect)}
    (hFree : ConflictFree (ReceiptConflict effectConflict) events) :
    ReceiptObservationsFunctional events := by
  intro cell outcome other hOutcome hOther
  by_contra hDifferent
  exact hFree hOutcome hOther ⟨rfl, hDifferent⟩

/-! ## Kernel-checked causal examples -/

/-- A two-stage basis: `true` causally depends on `false`. -/
def twoStageBasis : FiniteCausalBasis Bool where
  support
    | false => {false}
    | true => {false, true}
  self_mem := by
    intro event
    cases event <;> simp
  hereditary := by
    intro event predecessor h
    cases event <;> cases predecessor <;> simp at h ⊢

/-- Positive: publishing an observation also publishes its causal predecessor. -/
example : twoStageBasis.close {true} = {false, true} := by
  ext event
  cases event <;> simp [FiniteCausalBasis.close, twoStageBasis]

/-- Negative: `{true}` alone is not a causally closed world. -/
example : ¬ twoStageBasis.Closed {true} := by
  intro h
  have hFalse : false ∈ twoStageBasis.close {true} := by
    simp [FiniteCausalBasis.close, twoStageBasis]
  rw [h] at hFalse
  simp at hFalse

end CausalClosure

/-! ## Pure independent-cell observation fragment -/

section CellObservations

variable {Cell Outcome : Type*} [DecidableEq Cell] [DecidableEq Outcome]

abbrev CellWorld (Cell Outcome : Type*) := Finset (Cell × Outcome)

/-- One observed outcome per cell. -/
def Functional (world : CellWorld Cell Outcome) : Prop :=
  ∀ ⦃cell outcome other⦄,
    (cell, outcome) ∈ world -> (cell, other) ∈ world -> outcome = other

/-- Pure cell observations conflict exactly when one cell has two outcomes. -/
def CellConflict (left right : Cell × Outcome) : Prop :=
  left.1 = right.1 ∧ left.2 ≠ right.2

omit [DecidableEq Cell] in
theorem functional_iff_conflictFree (world : CellWorld Cell Outcome) :
    Functional world ↔ ConflictFree CellConflict world := by
  constructor
  · intro hFunctional left right hLeft hRight hConflict
    rcases left with ⟨leftCell, leftOutcome⟩
    rcases right with ⟨rightCell, rightOutcome⟩
    rcases hConflict with ⟨hCell, hOutcome⟩
    change leftCell = rightCell at hCell
    subst rightCell
    exact hOutcome (hFunctional hLeft hRight)
  · intro hFree cell outcome other hOutcome hOther
    by_contra hDifferent
    exact hFree hOutcome hOther ⟨rfl, hDifferent⟩

/-- Two cell worlds agree wherever they both observe the same cell. -/
def CompatibleCellWorlds (left right : CellWorld Cell Outcome) : Prop :=
  ∀ ⦃cell leftOutcome rightOutcome⦄,
    (cell, leftOutcome) ∈ left ->
    (cell, rightOutcome) ∈ right ->
    leftOutcome = rightOutcome

/-- Compatible functional cell worlds have a functional union. -/
theorem Functional.union {left right : CellWorld Cell Outcome}
    (hLeft : Functional left) (hRight : Functional right)
    (hCompatible : CompatibleCellWorlds left right) :
    Functional (left ∪ right) := by
  intro cell outcome other hOutcome hOther
  simp only [Finset.mem_union] at hOutcome hOther
  rcases hOutcome with hOutcome | hOutcome <;>
    rcases hOther with hOther | hOther
  · exact hLeft hOutcome hOther
  · exact hCompatible hOutcome hOther
  · exact (hCompatible hOther hOutcome).symm
  · exact hRight hOutcome hOther

/-- Positive: observations of different cells are functional. -/
example : Functional ({(0, true), (1, false)} : CellWorld Nat Bool) := by
  intro cell outcome other hOutcome hOther
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hOutcome hOther
  rcases hOutcome with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    rcases hOther with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp_all

/-- Negative: two outcomes for one cell are not functional. -/
example : ¬ Functional ({(0, true), (0, false)} : CellWorld Nat Bool) := by
  intro h
  have hEqual : true = false := @h 0 true false (by simp) (by simp)
  exact Bool.noConfusion hEqual

end CellObservations

end Mettapedia.Languages.MeTTa.PrimeNeedWorlds
