import Mettapedia.GSLT.LanguageDef.DelayedBindingStoreRefinement
import Mettapedia.GSLT.LanguageDef.DemandSynchronizedIndexCompilation

/-!
# Append/rollback builder product refinement

The live binding builder is not only a substitution.  Its observable state is
the product of an ordered binding sequence, an ordered constraint sequence,
and optional occurrence-local effect state.  Its physical state additionally
contains derived caches, monotone revision clocks, owner identity, rollback
checkpoints, and an observer-free-region marker.

This module states that decomposition without claiming that Lean has verified
the C source.  It proves the generic append/checkpoint/rollback and clone laws
that a field-by-field C refinement must instantiate.  Derived data are erased
from denotation but receive an explicit validity interface; ownership roots
include effect state retained by rollback checkpoints.

The older substitution-only and assignment-plus-equality projections remain
useful local lemmas.  Negative controls below prove that neither projection is
the complete builder meaning.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.AppendRollbackBuilderProductRefinement

open DelayedSourceBindingCompilation
open CompiledPlanTermSemantics
open CompiledPlanOpenActivationViewCompilation

universe uPhysicalBinding uLogicalBinding uConstraint uPrime uDerived
  uReceipt uOwnerId uRoot uAlpha uKey uOwner uRevision uVariable

variable {PhysicalBinding : Type uPhysicalBinding}
  {LogicalBinding : Type uLogicalBinding}
  {Constraint : Type uConstraint} {Prime : Type uPrime}
  {Derived : Type uDerived} {Receipt : Type uReceipt}
  {OwnerId : Type uOwnerId} {Root : Type uRoot}
  {α : Type uAlpha} {Key : Type uKey}
  {Owner : Type uOwner} {Revision : Type uRevision}
  {Variable : Type uVariable}

/-! ## Semantic and physical products -/

/-- Complete logical observation of the append/rollback builder.  Constraints
and occurrence-local effect state are independent semantic coordinates, not
derived properties of the substitution. -/
structure LogicalCurrent
    (LogicalBinding : Type uLogicalBinding)
    (Constraint : Type uConstraint) (Prime : Type uPrime) where
  bindings : List LogicalBinding
  constraints : List Constraint
  prime : Option Prime
  deriving DecidableEq, Repr

/-- Physical current state.  `derived` stands for cycle knowledge,
conservative variable summaries, exact classified counts, and the lagging
lookup-index certificate.  Capacity is deliberately absent because it neither
changes meaning nor rollback reachability. -/
structure PhysicalCurrent
    (PhysicalBinding : Type uPhysicalBinding)
    (Constraint : Type uConstraint) (Prime : Type uPrime)
    (Derived : Type uDerived) where
  bindings : List PhysicalBinding
  constraints : List Constraint
  prime : Option Prime
  derived : Derived
  deriving DecidableEq, Repr

/-- Denotation maps only physical binding values.  Constraints and Prime
occurrence state are already authoritative logical coordinates. -/
def denoteCurrent
    (denoteBinding : PhysicalBinding → LogicalBinding)
    (current : PhysicalCurrent PhysicalBinding Constraint Prime Derived) :
    LogicalCurrent LogicalBinding Constraint Prime where
  bindings := current.bindings.map denoteBinding
  constraints := current.constraints
  prime := current.prime

/-- One decoded checkpoint.  A concrete realization may factor
`previousPrime` into a compact presence bit, an index, and a cold Prime trail;
that physical factoring owes a separate representation theorem. -/
structure Checkpoint (Prime : Type uPrime) (Receipt : Type uReceipt) where
  bindingCount : Nat
  constraintCount : Nat
  previousPrime : Option Prime
  derivedReceipt : Receipt
  deriving DecidableEq, Repr

def checkpoint
    (receipt : Derived → Receipt)
    (current : PhysicalCurrent PhysicalBinding Constraint Prime Derived) :
    Checkpoint Prime Receipt where
  bindingCount := current.bindings.length
  constraintCount := current.constraints.length
  previousPrime := current.prime
  derivedReceipt := receipt current.derived

/-- Append one finite batch in authored order.  Prime state is supplied as an
independent next coordinate because a merge can change it without adding a
binding or constraint. -/
def extend
    (current : PhysicalCurrent PhysicalBinding Constraint Prime Derived)
    (newBindings : List PhysicalBinding)
    (newConstraints : List Constraint)
    (nextPrime : Option Prime) (nextDerived : Derived) :
    PhysicalCurrent PhysicalBinding Constraint Prime Derived where
  bindings := current.bindings ++ newBindings
  constraints := current.constraints ++ newConstraints
  prime := nextPrime
  derived := nextDerived

/-- Restore the authoritative list prefixes and Prime coordinate.  Derived
state is rebuilt from its compact receipt and the restored authorities. -/
def restore
    (restoreDerived : Receipt → List PhysicalBinding → List Constraint → Derived)
    (current : PhysicalCurrent PhysicalBinding Constraint Prime Derived)
    (saved : Checkpoint Prime Receipt) :
    PhysicalCurrent PhysicalBinding Constraint Prime Derived :=
  let bindings := current.bindings.take saved.bindingCount
  let constraints := current.constraints.take saved.constraintCount
  { bindings
    constraints
    prime := saved.previousPrime
    derived := restoreDerived saved.derivedReceipt bindings constraints }

/-- Appending an arbitrary batch and restoring the entrance checkpoint
recovers the exact complete logical product, independently of physical cache
reconstruction. -/
theorem denote_restore_extend
    (denoteBinding : PhysicalBinding → LogicalBinding)
    (receipt : Derived → Receipt)
    (restoreDerived : Receipt → List PhysicalBinding → List Constraint → Derived)
    (current : PhysicalCurrent PhysicalBinding Constraint Prime Derived)
    (newBindings : List PhysicalBinding)
    (newConstraints : List Constraint)
    (nextPrime : Option Prime) (nextDerived : Derived) :
    denoteCurrent denoteBinding
        (restore restoreDerived
          (extend current newBindings newConstraints nextPrime nextDerived)
          (checkpoint receipt current)) =
      denoteCurrent denoteBinding current := by
  cases current
  simp [denoteCurrent, restore, extend, checkpoint]

/-! ## Builder coordinates, clocks, regions, and clone -/

/-- Observer-free checkpoint coalescing is physical protocol state.  It is
not inherited by a cloned owner. -/
structure RegionState where
  active : Bool
  hasCheckpoint : Bool
  entryMark : Nat
  deriving DecidableEq, Repr

def RegionState.closed : RegionState :=
  { active := false, hasCheckpoint := false, entryMark := 0 }

def RegionState.afterRollback (region : RegionState) : RegionState :=
  { region with hasCheckpoint := false }

/-- Newest-first checkpoint order is a proof representation of the live
array prefix.  It is not a claim about the in-memory direction of the C array. -/
structure Builder
    (PhysicalBinding : Type uPhysicalBinding)
    (Constraint : Type uConstraint) (Prime : Type uPrime)
    (Derived : Type uDerived) (Receipt : Type uReceipt)
    (OwnerId : Type uOwnerId) where
  current : PhysicalCurrent PhysicalBinding Constraint Prime Derived
  trail : List (Checkpoint Prime Receipt)
  growthClock : Nat
  rollbackClock : Nat
  ownerId : OwnerId
  region : RegionState
  deriving DecidableEq, Repr

def denoteBuilder
    (denoteBinding : PhysicalBinding → LogicalBinding)
    (builder : Builder PhysicalBinding Constraint Prime Derived Receipt OwnerId) :
    LogicalCurrent LogicalBinding Constraint Prime :=
  denoteCurrent denoteBinding builder.current

/-- Push an append transaction and its decoded entrance checkpoint.  Growth
counts logical binding and constraint appends; Prime-only changes remain a
separate semantic coordinate. -/
def pushExtension
    (receipt : Derived → Receipt)
    (builder : Builder PhysicalBinding Constraint Prime Derived Receipt OwnerId)
    (newBindings : List PhysicalBinding)
    (newConstraints : List Constraint)
    (nextPrime : Option Prime) (nextDerived : Derived) :
    Builder PhysicalBinding Constraint Prime Derived Receipt OwnerId where
  current := extend builder.current newBindings newConstraints nextPrime nextDerived
  trail := checkpoint receipt builder.current :: builder.trail
  growthClock :=
    builder.growthClock + newBindings.length + newConstraints.length
  rollbackClock := builder.rollbackClock
  ownerId := builder.ownerId
  region :=
    if builder.region.active then
      { builder.region with hasCheckpoint := true }
    else builder.region

/-- Roll back one physical checkpoint.  Empty-trail rollback fails closed. -/
def rollbackOne?
    (restoreDerived : Receipt → List PhysicalBinding → List Constraint → Derived)
    (builder : Builder PhysicalBinding Constraint Prime Derived Receipt OwnerId) :
    Option (Builder PhysicalBinding Constraint Prime Derived Receipt OwnerId) :=
  match builder.trail with
  | [] => none
  | saved :: rest =>
      some
        { current := restore restoreDerived builder.current saved
          trail := rest
          growthClock := builder.growthClock
          rollbackClock := builder.rollbackClock + 1
          ownerId := builder.ownerId
          region := builder.region.afterRollback }

/-- The complete logical product is restored after one arbitrary append
transaction. -/
theorem rollbackOne?_pushExtension_exact
    (denoteBinding : PhysicalBinding → LogicalBinding)
    (receipt : Derived → Receipt)
    (restoreDerived : Receipt → List PhysicalBinding → List Constraint → Derived)
    (builder : Builder PhysicalBinding Constraint Prime Derived Receipt OwnerId)
    (newBindings : List PhysicalBinding)
    (newConstraints : List Constraint)
    (nextPrime : Option Prime) (nextDerived : Derived) :
    (rollbackOne? restoreDerived
      (pushExtension receipt builder newBindings newConstraints
        nextPrime nextDerived)).map (denoteBuilder denoteBinding) =
      some (denoteBuilder denoteBinding builder) := by
  simp [rollbackOne?, pushExtension, denoteBuilder,
    denote_restore_extend]

theorem rollbackOne?_pushExtension_preserves_growth
    (receipt : Derived → Receipt)
    (restoreDerived : Receipt → List PhysicalBinding → List Constraint → Derived)
    (builder : Builder PhysicalBinding Constraint Prime Derived Receipt OwnerId)
    (newBindings : List PhysicalBinding)
    (newConstraints : List Constraint)
    (nextPrime : Option Prime) (nextDerived : Derived) :
    (rollbackOne? restoreDerived
      (pushExtension receipt builder newBindings newConstraints
        nextPrime nextDerived)).map Builder.growthClock =
      some (builder.growthClock + newBindings.length + newConstraints.length) := by
  rfl

theorem rollbackOne?_pushExtension_increments_rollback
    (receipt : Derived → Receipt)
    (restoreDerived : Receipt → List PhysicalBinding → List Constraint → Derived)
    (builder : Builder PhysicalBinding Constraint Prime Derived Receipt OwnerId)
    (newBindings : List PhysicalBinding)
    (newConstraints : List Constraint)
    (nextPrime : Option Prime) (nextDerived : Derived) :
    (rollbackOne? restoreDerived
      (pushExtension receipt builder newBindings newConstraints
        nextPrime nextDerived)).map Builder.rollbackClock =
      some (builder.rollbackClock + 1) := by
  rfl

/-- A clone has identical meaning and checkpoint history but a fresh physical
owner and no inherited observer-free region. -/
def cloneWith
    (newOwnerId : OwnerId)
    (builder : Builder PhysicalBinding Constraint Prime Derived Receipt OwnerId) :
    Builder PhysicalBinding Constraint Prime Derived Receipt OwnerId :=
  { builder with ownerId := newOwnerId, region := .closed }

@[simp] theorem denoteBuilder_cloneWith
    (denoteBinding : PhysicalBinding → LogicalBinding)
    (newOwnerId : OwnerId)
    (builder : Builder PhysicalBinding Constraint Prime Derived Receipt OwnerId) :
    denoteBuilder denoteBinding (cloneWith newOwnerId builder) =
      denoteBuilder denoteBinding builder := rfl

@[simp] theorem cloneWith_region_closed
    (newOwnerId : OwnerId)
    (builder : Builder PhysicalBinding Constraint Prime Derived Receipt OwnerId) :
    (cloneWith newOwnerId builder).region = RegionState.closed := rfl

/-- Revision-bound accelerators need all three coordinates.  Growth does not
decrease on rollback, so rollback is an independent part of the key. -/
structure RevisionKey (OwnerId : Type uOwnerId) where
  ownerId : OwnerId
  growth : Nat
  rollback : Nat
  deriving DecidableEq, Repr

def revisionKey
    (builder : Builder PhysicalBinding Constraint Prime Derived Receipt OwnerId) :
    RevisionKey OwnerId :=
  ⟨builder.ownerId, builder.growthClock, builder.rollbackClock⟩

theorem clone_revisionKey_ne
    (newOwnerId : OwnerId)
    (builder : Builder PhysicalBinding Constraint Prime Derived Receipt OwnerId)
    (fresh : newOwnerId ≠ builder.ownerId) :
    revisionKey (cloneWith newOwnerId builder) ≠ revisionKey builder := by
  intro equal
  exact fresh (congrArg RevisionKey.ownerId equal)

/-! ## Explicit derived-cache validity -/

/-- A physical cache family must state which authoritative list pair makes it
valid and provide a cold rebuild.  Denotational erasure alone is not evidence
that lookup through the cache is exact. -/
structure DerivedDiscipline
    (PhysicalBinding : Type uPhysicalBinding)
    (Constraint : Type uConstraint) (Derived : Type uDerived) where
  Valid : List PhysicalBinding → List Constraint → Derived → Prop
  rebuild : List PhysicalBinding → List Constraint → Derived
  rebuild_valid : ∀ bindings constraints,
    Valid bindings constraints (rebuild bindings constraints)

def refreshDerived
    (discipline : DerivedDiscipline PhysicalBinding Constraint Derived)
    (current : PhysicalCurrent PhysicalBinding Constraint Prime Derived) :
    PhysicalCurrent PhysicalBinding Constraint Prime Derived :=
  { current with
    derived := discipline.rebuild current.bindings current.constraints }

@[simp] theorem denoteCurrent_refreshDerived
    (denoteBinding : PhysicalBinding → LogicalBinding)
    (discipline : DerivedDiscipline PhysicalBinding Constraint Derived)
    (current : PhysicalCurrent PhysicalBinding Constraint Prime Derived) :
    denoteCurrent denoteBinding (refreshDerived discipline current) =
      denoteCurrent denoteBinding current := rfl

theorem refreshDerived_valid
    (discipline : DerivedDiscipline PhysicalBinding Constraint Derived)
    (current : PhysicalCurrent PhysicalBinding Constraint Prime Derived) :
    discipline.Valid
      (refreshDerived discipline current).bindings
      (refreshDerived discipline current).constraints
      (refreshDerived discipline current).derived :=
  discipline.rebuild_valid current.bindings current.constraints

def BuilderDerivedValid
    (discipline : DerivedDiscipline PhysicalBinding Constraint Derived)
    (builder : Builder PhysicalBinding Constraint Prime Derived Receipt OwnerId) :
    Prop :=
  discipline.Valid builder.current.bindings builder.current.constraints
    builder.current.derived

def refreshBuilderDerived
    (discipline : DerivedDiscipline PhysicalBinding Constraint Derived)
    (builder : Builder PhysicalBinding Constraint Prime Derived Receipt OwnerId) :
    Builder PhysicalBinding Constraint Prime Derived Receipt OwnerId :=
  { builder with current := refreshDerived discipline builder.current }

@[simp] theorem denoteBuilder_refreshDerived
    (denoteBinding : PhysicalBinding → LogicalBinding)
    (discipline : DerivedDiscipline PhysicalBinding Constraint Derived)
    (builder : Builder PhysicalBinding Constraint Prime Derived Receipt OwnerId) :
    denoteBuilder denoteBinding (refreshBuilderDerived discipline builder) =
      denoteBuilder denoteBinding builder := rfl

theorem refreshBuilderDerived_valid
    (discipline : DerivedDiscipline PhysicalBinding Constraint Derived)
    (builder : Builder PhysicalBinding Constraint Prime Derived Receipt OwnerId) :
    BuilderDerivedValid discipline (refreshBuilderDerived discipline builder) :=
  discipline.rebuild_valid builder.current.bindings builder.current.constraints

/-- Exact classified counts are one concrete derived-cache discipline. -/
structure ExactCounts where
  bindings : Nat
  constraints : Nat
  deriving DecidableEq, Repr

def exactCountDiscipline :
    DerivedDiscipline PhysicalBinding Constraint ExactCounts where
  Valid bindings constraints counts :=
    counts = ⟨bindings.length, constraints.length⟩
  rebuild bindings constraints := ⟨bindings.length, constraints.length⟩
  rebuild_valid _ _ := rfl

/-! ### Compact count receipts -/

def classifiedCount (selected : α → Bool) (values : List α) : Nat :=
  (values.filter selected).length

/-- The live compact trail stores whether an exact classified count was
nonzero, then recomputes the exact count only on that cold rollback path. -/
def countNonzeroReceipt (selected : α → Bool) (values : List α) : Bool :=
  classifiedCount selected values != 0

def restoreClassifiedCount
    (selected : α → Bool) (values : List α) (wasNonzero : Bool) : Nat :=
  if wasNonzero then classifiedCount selected values else 0

theorem restoreClassifiedCount_exact
    (selected : α → Bool) (values : List α) :
    restoreClassifiedCount selected values
        (countNonzeroReceipt selected values) =
      classifiedCount selected values := by
  unfold restoreClassifiedCount countNonzeroReceipt
  by_cases zero : classifiedCount selected values = 0
  · simp [zero]
  · simp [zero]

/-! ### Conservative support summaries -/

def rootsOfList [DecidableEq Root]
    (roots : α → Finset Root) : List α → Finset Root
  | [] => ∅
  | value :: values => roots value ∪ rootsOfList roots values

theorem rootsOfList_take_subset [DecidableEq Root]
    (roots : α → Finset Root) (values : List α) (count : Nat) :
    rootsOfList roots (values.take count) ⊆ rootsOfList roots values := by
  induction values generalizing count with
  | nil => simp [rootsOfList]
  | cons value values inductionHypothesis =>
      cases count with
      | zero => simp [rootsOfList]
      | succ count =>
          simp only [List.take_succ_cons, rootsOfList]
          exact Finset.union_subset_union (Finset.Subset.rfl)
            (inductionHypothesis count)

abbrev supportOfList [DecidableEq Variable]
    (support : PhysicalBinding → Finset Variable)
    (bindings : List PhysicalBinding) : Finset Variable :=
  rootsOfList support bindings

theorem rootsOfList_append [DecidableEq Root]
    (roots : α → Finset Root) (left right : List α) :
    rootsOfList roots (left ++ right) =
      rootsOfList roots left ∪ rootsOfList roots right := by
  induction left with
  | nil => simp [rootsOfList]
  | cons value left inductionHypothesis =>
      simp [rootsOfList, inductionHypothesis, Finset.union_assoc]

def SupportSummaryValid [DecidableEq Variable]
    (support : PhysicalBinding → Finset Variable)
    (bindings : List PhysicalBinding) (cached : Finset Variable) : Prop :=
  supportOfList support bindings ⊆ cached

def appendSupportSummary [DecidableEq Variable]
    (support : PhysicalBinding → Finset Variable)
    (cached : Finset Variable) (newBindings : List PhysicalBinding) :
    Finset Variable :=
  cached ∪ supportOfList support newBindings

/-- Fresh append extends the conservative summary without false negatives. -/
theorem appendSupportSummary_valid [DecidableEq Variable]
    (support : PhysicalBinding → Finset Variable)
    (bindings newBindings : List PhysicalBinding)
    (cached : Finset Variable)
    (valid : SupportSummaryValid support bindings cached) :
    SupportSummaryValid support (bindings ++ newBindings)
      (appendSupportSummary support cached newBindings) := by
  rw [SupportSummaryValid, supportOfList, rootsOfList_append]
  exact Finset.union_subset_union valid Finset.Subset.rfl

/-- Suffix rollback may retain false positives, but cannot create a false
negative because the restored authoritative sequence is a prefix. -/
theorem rollbackSupportSummary_valid [DecidableEq Variable]
    (support : PhysicalBinding → Finset Variable)
    (bindings : List PhysicalBinding) (cached : Finset Variable)
    (count : Nat) (valid : SupportSummaryValid support bindings cached) :
    SupportSummaryValid support (bindings.take count) cached :=
  Finset.Subset.trans (rootsOfList_take_subset support bindings count) valid

/-! ### Cycle knowledge and the demand-synchronized lookup index -/

inductive CycleKnowledge where
  | unknown
  | acyclic
  | cyclic
  deriving DecidableEq, Repr

def CycleKnowledge.Valid
    (hasCycle : List PhysicalBinding → Prop)
    (bindings : List PhysicalBinding) : CycleKnowledge → Prop
  | .unknown => True
  | .acyclic => ¬ hasCycle bindings
  | .cyclic => hasCycle bindings

/-- The lookup-index coordinate already has an independent exactness theorem:
after any suffix rollback, demand synchronization agrees with authoritative
source-order lookup. -/
theorem laggingLookup_rollback_exact
    {IndexKey IndexValue : Type}
    [BEq IndexKey] [Hashable IndexKey]
    [LawfulBEq IndexKey] [LawfulHashable IndexKey]
    (state : DemandSynchronizedIndexCompilation.LaggingState
      IndexKey IndexValue)
    (length : Nat) (query : IndexKey) :
    DemandSynchronizedIndexCompilation.demandLookup
        (DemandSynchronizedIndexCompilation.rollbackSuffix state length) query =
      MonotoneUniqueIndexCompilation.sourceLookup query
        (state.entries.take length) :=
  DemandSynchronizedIndexCompilation.demandLookup_rollbackSuffix
    state length query

/-! ## Ownership roots -/

def optionRoots [DecidableEq Root]
    (roots : α → Finset Root) : Option α → Finset Root
  | none => ∅
  | some value => roots value

structure RootDiscipline
    (PhysicalBinding : Type uPhysicalBinding)
    (Constraint : Type uConstraint) (Prime : Type uPrime)
    (Root : Type uRoot) [DecidableEq Root] where
  bindingRoots : PhysicalBinding → Finset Root
  constraintRoots : Constraint → Finset Root
  primeRoots : Prime → Finset Root

def currentRoots [DecidableEq Root]
    (discipline : RootDiscipline PhysicalBinding Constraint Prime Root)
    (current : PhysicalCurrent PhysicalBinding Constraint Prime Derived) :
    Finset Root :=
  (rootsOfList discipline.bindingRoots current.bindings ∪
      rootsOfList discipline.constraintRoots current.constraints) ∪
    optionRoots discipline.primeRoots current.prime

def checkpointRoots [DecidableEq Root]
    (discipline : RootDiscipline PhysicalBinding Constraint Prime Root)
    (saved : Checkpoint Prime Receipt) : Finset Root :=
  optionRoots discipline.primeRoots saved.previousPrime

def trailRoots [DecidableEq Root]
    (discipline : RootDiscipline PhysicalBinding Constraint Prime Root) :
    List (Checkpoint Prime Receipt) → Finset Root
  | [] => ∅
  | saved :: rest => checkpointRoots discipline saved ∪ trailRoots discipline rest

/-- Admission roots include the current logical payload and Prime state kept
only for rollback.  Compact scalar cache receipts carry no atom roots. -/
def admissionRoots [DecidableEq Root]
    (discipline : RootDiscipline PhysicalBinding Constraint Prime Root)
    (builder : Builder PhysicalBinding Constraint Prime Derived Receipt OwnerId) :
    Finset Root :=
  currentRoots discipline builder.current ∪ trailRoots discipline builder.trail

theorem checkpointRoots_subset_trailRoots_of_mem [DecidableEq Root]
    (discipline : RootDiscipline PhysicalBinding Constraint Prime Root)
    (saved : Checkpoint Prime Receipt)
    (trail : List (Checkpoint Prime Receipt)) (member : saved ∈ trail) :
    checkpointRoots discipline saved ⊆ trailRoots discipline trail := by
  induction trail with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp member with same | member
      · subst head
        exact Finset.subset_union_left
      · exact Finset.Subset.trans (inductionHypothesis member)
          Finset.subset_union_right

theorem restore_roots_subset [DecidableEq Root]
    (discipline : RootDiscipline PhysicalBinding Constraint Prime Root)
    (restoreDerived : Receipt → List PhysicalBinding → List Constraint → Derived)
    (current : PhysicalCurrent PhysicalBinding Constraint Prime Derived)
    (saved : Checkpoint Prime Receipt) :
    currentRoots discipline (restore restoreDerived current saved) ⊆
      currentRoots discipline current ∪ checkpointRoots discipline saved := by
  apply Finset.union_subset
  · apply Finset.Subset.trans
      (Finset.union_subset_union
        (rootsOfList_take_subset (Root := Root) discipline.bindingRoots
          current.bindings saved.bindingCount)
        (rootsOfList_take_subset (Root := Root) discipline.constraintRoots
          current.constraints saved.constraintCount))
    exact Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  · exact Finset.subset_union_right

theorem restore_roots_subset_admission [DecidableEq Root]
    (discipline : RootDiscipline PhysicalBinding Constraint Prime Root)
    (restoreDerived : Receipt → List PhysicalBinding → List Constraint → Derived)
    (builder : Builder PhysicalBinding Constraint Prime Derived Receipt OwnerId)
    (saved : Checkpoint Prime Receipt) (member : saved ∈ builder.trail) :
    currentRoots discipline (restore restoreDerived builder.current saved) ⊆
      admissionRoots discipline builder := by
  apply Finset.Subset.trans
    (restore_roots_subset discipline restoreDerived builder.current saved)
  apply Finset.union_subset
  · exact Finset.subset_union_left
  · exact Finset.Subset.trans
      (checkpointRoots_subset_trailRoots_of_mem discipline saved
        builder.trail member)
      Finset.subset_union_right

/-! ## Delayed-binding specialization -/

abbrev DelayedBinding
    (Key : Type uKey) (Owner : Type uOwner) (Revision : Type uRevision) :=
  Key × BindingValue Owner Revision

def denoteDelayedBinding
    (binding : DelayedBinding Key Owner Revision) : Key × OpenTerm :=
  (binding.1, binding.2.denote)

/-! ## Positive and negative controls -/

namespace Canaries

private def logicalBindingsOnly : LogicalCurrent Bool Bool Bool :=
  { bindings := [true], constraints := [], prime := none }

private def logicalWithConstraint : LogicalCurrent Bool Bool Bool :=
  { bindings := [true], constraints := [false], prime := none }

private def logicalWithPrime : LogicalCurrent Bool Bool Bool :=
  { bindings := [true], constraints := [], prime := some true }

/-- A substitution-only observer cannot recover the constraint coordinate. -/
example :
    logicalBindingsOnly.bindings = logicalWithConstraint.bindings ∧
      logicalBindingsOnly ≠ logicalWithConstraint := by decide

/-- Bindings plus constraints still cannot recover occurrence-local Prime
state. -/
example :
    (logicalBindingsOnly.bindings, logicalBindingsOnly.constraints) =
        (logicalWithPrime.bindings, logicalWithPrime.constraints) ∧
      logicalBindingsOnly ≠ logicalWithPrime := by decide

private def noRegion : RegionState := RegionState.closed

private def base : Builder Bool Bool Bool Nat Nat Nat :=
  { current :=
      { bindings := [], constraints := [], prime := none, derived := 0 }
    trail := []
    growthClock := 0
    rollbackClock := 0
    ownerId := 7
    region := noRegion }

private def extended : Builder Bool Bool Bool Nat Nat Nat :=
  pushExtension id base [true] [false] (some true) 2

private def restoreNat (receipt : Nat) (_ : List Bool) (_ : List Bool) : Nat :=
  receipt

/-- Rollback restores all three semantic coordinates while retaining the work
clock and advancing the rollback clock. -/
example :
    (rollbackOne? restoreNat extended).map (denoteBuilder id) =
        some (denoteBuilder id base) ∧
      (rollbackOne? restoreNat extended).map Builder.growthClock = some 2 ∧
      (rollbackOne? restoreNat extended).map Builder.rollbackClock = some 1 := by
  decide

private def boolSupport : Bool → Finset Nat
  | false => {0}
  | true => {1}

/-- A conservative support cache may retain false positives across rollback. -/
example : SupportSummaryValid boolSupport [false] ({0, 9} : Finset Nat) := by
  simp [SupportSummaryValid, supportOfList, rootsOfList, boolSupport]

/-- It may not omit a variable read by a live binding. -/
example : ¬ SupportSummaryValid boolSupport [true] (∅ : Finset Nat) := by
  simp [SupportSummaryValid, supportOfList, rootsOfList, boolSupport]

/-- Append and suffix rollback preserve the conservative support contract. -/
example :
    SupportSummaryValid boolSupport ([false] ++ [true])
      (appendSupportSummary boolSupport {0} [true]) ∧
    SupportSummaryValid boolSupport (([false, true] : List Bool).take 1)
      ({0, 1} : Finset Nat) := by
  constructor
  · exact appendSupportSummary_valid boolSupport [false] [true] {0} (by
      simp [SupportSummaryValid, supportOfList, rootsOfList, boolSupport])
  · exact rollbackSupportSummary_valid boolSupport [false, true] {0, 1} 1 (by
      simp [SupportSummaryValid, supportOfList, rootsOfList, boolSupport])

private def boolHasCycle (bindings : List Bool) : Prop := true ∈ bindings

/-- Unknown cycle knowledge is always safe; positive and negative claims must
be justified by the authoritative bindings. -/
example :
    CycleKnowledge.Valid boolHasCycle [true] .unknown ∧
      CycleKnowledge.Valid boolHasCycle [true] .cyclic ∧
      ¬ CycleKnowledge.Valid boolHasCycle [true] .acyclic := by
  simp [CycleKnowledge.Valid, boolHasCycle]

private def laggingIndex :
    DemandSynchronizedIndexCompilation.LaggingState Nat Bool where
  entries := [(1, true), (2, false)]
  syncedLen := 1
  syncedLen_le := by decide

/-- Demand lookup after suffix rollback observes the authoritative prefix and
cannot return the removed suffix. -/
example :
    DemandSynchronizedIndexCompilation.demandLookup
        (DemandSynchronizedIndexCompilation.rollbackSuffix laggingIndex 1) 1 =
        some true ∧
      DemandSynchronizedIndexCompilation.demandLookup
        (DemandSynchronizedIndexCompilation.rollbackSuffix laggingIndex 1) 2 =
        none := by
  constructor
  · rw [laggingLookup_rollback_exact]
    rfl
  · rw [laggingLookup_rollback_exact]
    rfl

/-- Growth alone cannot identify a revision after rollback: the logical state
changes but the growth clock deliberately does not. -/
example :
    (rollbackOne? restoreNat extended).map Builder.growthClock =
        some extended.growthClock ∧
      (rollbackOne? restoreNat extended).map (denoteBuilder id) ≠
        some (denoteBuilder id extended) := by decide

private def rootDiscipline : RootDiscipline Unit Unit Nat Nat where
  bindingRoots _ := ∅
  constraintRoots _ := ∅
  primeRoots value := {value}

private def rootBuilder : Builder Unit Unit Nat Unit Unit Unit :=
  { current :=
      { bindings := [], constraints := [], prime := some 2, derived := () }
    trail :=
      [{ bindingCount := 0, constraintCount := 0,
         previousPrime := some 1, derivedReceipt := () }]
    growthClock := 0
    rollbackClock := 0
    ownerId := ()
    region := .closed }

/-- Current-only scanning misses Prime state that rollback can resurrect; the
complete admission root set retains it. -/
example :
    (1 : Nat) ∉ currentRoots rootDiscipline rootBuilder.current ∧
      (1 : Nat) ∈ admissionRoots rootDiscipline rootBuilder := by
  norm_num [currentRoots, admissionRoots, trailRoots, checkpointRoots,
    optionRoots, rootsOfList, rootDiscipline, rootBuilder]

/-- Derived refresh changes no logical coordinate and produces a valid exact
count cache. -/
example :
    let current : PhysicalCurrent Bool Bool Bool ExactCounts :=
      { bindings := [true, false], constraints := [true], prime := some false,
        derived := ⟨0, 0⟩ }
    denoteCurrent id (refreshDerived exactCountDiscipline current) =
        denoteCurrent id current ∧
      (refreshDerived exactCountDiscipline current).derived = ⟨2, 1⟩ := by
  decide

end Canaries

#print axioms denote_restore_extend
#print axioms rollbackOne?_pushExtension_exact
#print axioms rollbackOne?_pushExtension_preserves_growth
#print axioms rollbackOne?_pushExtension_increments_rollback
#print axioms denoteBuilder_cloneWith
#print axioms clone_revisionKey_ne
#print axioms refreshDerived_valid
#print axioms restoreClassifiedCount_exact
#print axioms appendSupportSummary_valid
#print axioms rollbackSupportSummary_valid
#print axioms laggingLookup_rollback_exact
#print axioms rootsOfList_take_subset
#print axioms restore_roots_subset
#print axioms restore_roots_subset_admission

end Mettapedia.GSLT.LanguageDef.AppendRollbackBuilderProductRefinement
