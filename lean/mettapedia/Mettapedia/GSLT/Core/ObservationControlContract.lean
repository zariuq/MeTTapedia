import Mettapedia.GSLT.Core.ObservationDemandControl
import Mettapedia.GSLT.Core.ObservationIndexedPruning

/-!
# Observation contracts for evaluator control

An evaluator may choose a control strategy only after two independent pieces
of meaning have been fixed:

* a completion demand says how much output the consumer requests; and
* an observer says which distinctions in the retained occurrences matter.

The observer is the semantic boundary for reordering, filtering, aggregation,
and pruning.  A proposed change is an optimization only when it preserves that
observer.  The completion demand is the boundary for stopping.  Neither a
guard, a score, nor a concrete scheduling discipline supplies either
authority.

Bulk activation additionally consumes proof that the authored batch is
serializable at the declared observer.  Thus a complete bag may use a fused
implementation, while an ordered stream or an uncertified bag remains under
controlled activation.  The strategy name and physical continuation layout
remain outside the contract.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ObservationControlContract

open Mettapedia.Cybernetics
open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Core.ObservationIndexedPruning

universe uItem uGuard uView uOtherView uReceipt

/-- The semantic information needed before selecting evaluator control.

`observer` is deliberately a function on retained occurrences rather than a
tag such as `bag` or `stream`: user-defined quotients receive the same exact
lawfulness criterion as built-in observations. -/
structure Contract (Item : Type uItem) (Guard : Type uGuard)
    (View : Type uView) where
  observer : Observer (List Item) View
  demand : ObservationDemand Guard

namespace Contract

variable {Item : Type uItem} {Guard : Type uGuard} {View : Type uView}
variable {OtherView : Type uOtherView}

/-- Forget additional observation detail without changing completion demand
or the semantic guard. -/
def postcompose (contract : Contract Item Guard View)
    (summarize : View -> OtherView) : Contract Item Guard OtherView where
  observer := contract.observer.postcompose summarize
  demand := contract.demand

@[simp] theorem postcompose_observe
    (contract : Contract Item Guard View) (summarize : View -> OtherView)
    (items : List Item) :
    (contract.postcompose summarize).observer.observe items =
      summarize (contract.observer.observe items) :=
  rfl

@[simp] theorem postcompose_demand
    (contract : Contract Item Guard View) (summarize : View -> OtherView) :
    (contract.postcompose summarize).demand = contract.demand :=
  rfl

/-- Add an independent observation axis to the same consuming frame.  Both
axes inspect the same occurrence list and share one completion demand. -/
def addAxis (contract : Contract Item Guard View)
    (axis : Observer (List Item) OtherView) :
    Contract Item Guard (View × OtherView) where
  observer :=
    { observe := fun items =>
        (contract.observer.observe items, axis.observe items) }
  demand := contract.demand

@[simp] theorem addAxis_observe
    (contract : Contract Item Guard View)
    (axis : Observer (List Item) OtherView) (items : List Item) :
    (contract.addAxis axis).observer.observe items =
      (contract.observer.observe items, axis.observe items) :=
  rfl

@[simp] theorem addAxis_demand
    (contract : Contract Item Guard View)
    (axis : Observer (List Item) OtherView) :
    (contract.addAxis axis).demand = contract.demand :=
  rfl

/-- A proposed control transformation is licensed exactly at the observer
declared by this contract. -/
def Preserves {Receipt : Type uReceipt} (contract : Contract Item Guard View)
    (change : Change Item Receipt) : Prop :=
  LawfulAt contract.observer change

/-- A transformation preserves a product observation exactly when it
preserves each axis. -/
theorem preserves_addAxis_iff {Receipt : Type uReceipt}
    (contract : Contract Item Guard View)
    (axis : Observer (List Item) OtherView)
    (change : Change Item Receipt) :
    (contract.addAxis axis).Preserves change <->
      contract.Preserves change /\ LawfulAt axis change := by
  constructor
  · intro preserves
    exact
      ⟨congrArg Prod.fst preserves, congrArg Prod.snd preserves⟩
  · rintro ⟨preservesContract, preservesAxis⟩
    exact Prod.ext preservesContract preservesAxis

/-- A partial, receipt-carrying optimization checker indexed by this exact
contract observer. -/
abbrev OptimizationGuard (contract : Contract Item Guard View)
    (Receipt : Type uReceipt) :=
  ObservationIndexedPruning.Guard contract.observer Receipt

/-- Preservation at a finer observer implies preservation after forgetting
observation detail. -/
theorem preserves_postcompose {Receipt : Type uReceipt}
    (contract : Contract Item Guard View) (summarize : View -> OtherView)
    {change : Change Item Receipt} (preserves : contract.Preserves change) :
    (contract.postcompose summarize).Preserves change := by
  exact lawfulAt_postcompose contract.observer summarize preserves

/-- A sound optimization guard remains sound at every coarser observation. -/
def OptimizationGuard.postcompose {Receipt : Type uReceipt}
    (contract : Contract Item Guard View)
    (guard : contract.OptimizationGuard Receipt)
    (summarize : View -> OtherView) :
    (contract.postcompose summarize).OptimizationGuard Receipt where
  accepts := guard.accepts
  sound := by
    intro change accepted
    exact contract.preserves_postcompose summarize (guard.sound change accepted)

/-! ## Certified activation -/

/-- Evidence available at one activation boundary.  The serializable case
retains the proof; a Boolean flag cannot manufacture bulk authority. -/
inductive BatchEvidence (contract : Contract Item Guard View)
    (step : List Item -> Item -> List Item) (initial batch : List Item) where
  | singletonOnly
  | serializable
      (proof : SerializableAt contract.observer.observe step initial batch)

namespace BatchEvidence

variable {contract : Contract Item Guard View}
variable {step : List Item -> Item -> List Item}
variable {initial batch : List Item}

/-- Erase proof evidence only at the existing strategy-neutral dispatcher
boundary. -/
def authority (evidence : BatchEvidence contract step initial batch) :
    BatchAuthority :=
  match evidence with
  | .singletonOnly => .singletonOnly
  | .serializable _ => .serializable

/-- Serializability at a fine observer remains valid at any postcomposition. -/
theorem serializable_postcompose
    (proof : SerializableAt contract.observer.observe step initial batch)
    (summarize : View -> OtherView) :
    SerializableAt
      (contract.postcompose summarize).observer.observe step initial batch := by
  intro ordering permutation
  exact congrArg summarize (proof ordering permutation)

/-- Transport activation evidence to a coarser observation without changing
the batch, state transition, or completion demand. -/
def postcompose (evidence : BatchEvidence contract step initial batch)
    (summarize : View -> OtherView) :
    BatchEvidence (contract.postcompose summarize) step initial batch :=
  match evidence with
  | .singletonOnly => .singletonOnly
  | .serializable proof =>
      .serializable (serializable_postcompose proof summarize)

end BatchEvidence

/-- Dispatch using only certified batch evidence.  Concrete choices such as
FIFO, DFS, work stealing, or arena ownership are deliberately absent. -/
def dispatchCertified (contract : Contract Item Guard View)
    (branchAuthority : BranchAuthority)
    {step : List Item -> Item -> List Item} {initial batch : List Item}
    (evidence : BatchEvidence contract step initial batch) : Plan :=
  dispatch contract.demand branchAuthority evidence.authority

/-- Certified dispatch remains within the exact authority supplied by the
contract and evidence. -/
theorem dispatchCertified_lawful (contract : Contract Item Guard View)
    (branchAuthority : BranchAuthority)
    {step : List Item -> Item -> List Item} {initial batch : List Item}
    (evidence : BatchEvidence contract step initial batch) :
    PlanLawful contract.demand branchAuthority evidence.authority
      (dispatchCertified contract branchAuthority evidence) :=
  dispatch_lawful contract.demand branchAuthority evidence.authority

/-- Every bulk result has a complete-bag demand. -/
theorem bulk_requires_completeBag (contract : Contract Item Guard View)
    (branchAuthority : BranchAuthority)
    {step : List Item -> Item -> List Item} {initial batch : List Item}
    (evidence : BatchEvidence contract step initial batch)
    (bulk : (dispatchCertified contract branchAuthority evidence).activation =
      .bulk) :
    contract.demand.completion = .completeBag := by
  have lawful := dispatchCertified_lawful contract branchAuthority evidence
  have activationLawful :
      ActivationLawful contract.demand branchAuthority evidence.authority
        (dispatchCertified contract branchAuthority evidence).activation :=
    lawful.2
  rw [bulk] at activationLawful
  exact activationLawful.2.1

/-- Every bulk result also carries a serializability proof for the declared
observer. -/
theorem bulk_requires_serializable (contract : Contract Item Guard View)
    (branchAuthority : BranchAuthority)
    {step : List Item -> Item -> List Item} {initial batch : List Item}
    (evidence : BatchEvidence contract step initial batch)
    (bulk : (dispatchCertified contract branchAuthority evidence).activation =
      .bulk) :
    SerializableAt contract.observer.observe step initial batch := by
  cases evidence with
  | singletonOnly =>
      have lawful := dispatchCertified_lawful contract branchAuthority
        (BatchEvidence.singletonOnly (contract := contract)
          (step := step) (initial := initial) (batch := batch))
      have activationLawful :
          ActivationLawful contract.demand branchAuthority
            (BatchEvidence.singletonOnly (contract := contract)
              (step := step) (initial := initial) (batch := batch)).authority
            (dispatchCertified contract branchAuthority
              (BatchEvidence.singletonOnly (contract := contract)
                (step := step) (initial := initial) (batch := batch))).activation :=
        lawful.2
      rw [bulk] at activationLawful
      cases activationLawful.2.2
  | serializable proof => exact proof

/-- A complete bag with genuine serializability evidence uses bulk activation
whenever more than one live path is possible. -/
theorem completeBag_serializable_dispatches_bulk
    (contract : Contract Item Guard View)
    (complete : contract.demand.completion = .completeBag)
    {step : List Item -> Item -> List Item} {initial batch : List Item}
    (proof : SerializableAt contract.observer.observe step initial batch) :
    (dispatchCertified contract .general
      (BatchEvidence.serializable proof)).activation = .bulk := by
  rcases contract with ⟨observer, demand⟩
  rcases demand with ⟨completion, guard⟩
  simp only at complete
  subst completion
  rfl

/-- Without a serializability certificate, no completion mode can produce
bulk activation. -/
theorem singletonEvidence_never_dispatches_bulk
    (contract : Contract Item Guard View)
    (branchAuthority : BranchAuthority)
    {step : List Item -> Item -> List Item} {initial batch : List Item} :
    (dispatchCertified contract branchAuthority
      (BatchEvidence.singletonOnly (contract := contract)
        (step := step) (initial := initial) (batch := batch))).activation ≠
      .bulk := by
  intro bulk
  have lawful := dispatchCertified_lawful contract branchAuthority
    (BatchEvidence.singletonOnly (contract := contract)
      (step := step) (initial := initial) (batch := batch))
  have activationLawful :
      ActivationLawful contract.demand branchAuthority
        (BatchEvidence.singletonOnly (contract := contract)
          (step := step) (initial := initial) (batch := batch)).authority
        (dispatchCertified contract branchAuthority
          (BatchEvidence.singletonOnly (contract := contract)
            (step := step) (initial := initial) (batch := batch))).activation :=
    lawful.2
  rw [bulk] at activationLawful
  cases activationLawful.2.2

end Contract

/-! ## Discriminating examples -/

namespace Canary

open Contract

def appendStep {Item : Type uItem} (state : List Item) (item : Item) :
    List Item :=
  state ++ [item]

def natBagObserver : Observer (List Nat) (Multiset Nat) where
  observe := fun items => (items : Multiset Nat)

def natStreamObserver : Observer (List Nat) (List Nat) :=
  Observer.identity (List Nat)

def completeNatBag : Contract Nat Unit (Multiset Nat) where
  observer := natBagObserver
  demand := { completion := .completeBag }

def orderedNatStream : Contract Nat Unit (List Nat) where
  observer := natStreamObserver
  demand := { completion := .orderedStream }

/-- A complete commutative bag with append activation admits fused bulk
execution. -/
theorem complete_bag_uses_bulk (initial batch : List Nat) :
    (completeNatBag.dispatchCertified .general
      (Contract.BatchEvidence.serializable
        (append_is_serializable_for_bag initial batch))).activation = .bulk :=
  completeNatBag.completeBag_serializable_dispatches_bulk rfl
    (append_is_serializable_for_bag initial batch)

/-- The same two authored activations cannot provide serializability evidence
to the ordered-stream contract. -/
theorem ordered_stream_refuses_swapped_append :
    Not (SerializableAt orderedNatStream.observer.observe
      appendStep [] [1, 2]) :=
  append_not_serializable_for_stream

/-! ### Semantic filtering is observer-relative -/

def rawBoolBagObserver : Observer (List Bool) (Multiset Bool) where
  observe := fun items => (items : Multiset Bool)

def trueOnlyBagObserver : Observer (List Bool) (Multiset Bool) where
  observe := fun items => (items.filter (fun item => item = true) : Multiset Bool)

def rawBoolBag : Contract Bool Bool (Multiset Bool) where
  observer := rawBoolBagObserver
  demand := { completion := .completeBag, guard := some true }

def trueOnlyBag : Contract Bool Unit (Multiset Bool) where
  observer := trueOnlyBagObserver
  demand := { completion := .completeBag }

def dropFalse : Change Bool Unit where
  source := [true, false]
  target := [true]
  receipt := ()

/-- Dropping a rejected value is lawful when filtering is part of the
declared semantic observation. -/
theorem dropFalse_lawful_at_trueOnlyBag : trueOnlyBag.Preserves dropFalse := by
  change
    (([true, false].filter (fun item => item = true) : List Bool) :
        Multiset Bool) =
      (([true].filter (fun item => item = true) : List Bool) : Multiset Bool)
  rfl

/-- A semantic guard or score does not silently turn a raw bag into a
filtered bag. -/
theorem dropFalse_not_lawful_at_guardedRawBag :
    Not (rawBoolBag.Preserves dropFalse) := by
  change Not ((([true, false] : List Bool) : Multiset Bool) =
    (([true] : List Bool) : Multiset Bool))
  decide

def trueOnlyOptimizationGuard : trueOnlyBag.OptimizationGuard Unit where
  accepts := fun change => change = dropFalse
  sound := by
    intro change accepted
    subst change
    exact dropFalse_lawful_at_trueOnlyBag

/-! ### Multiplicity and provenance are independent dials -/

structure Occurrence where
  identity : Nat
  value : Bool
deriving DecidableEq, Repr

def firstTrue : Occurrence := ⟨0, true⟩
def secondTrue : Occurrence := ⟨1, true⟩

def occurrenceBagObserver :
    Observer (List Occurrence) (Multiset Occurrence) where
  observe := fun occurrences => (occurrences : Multiset Occurrence)

def valueBagObserver : Observer (List Occurrence) (Multiset Bool) where
  observe := fun occurrences =>
    (occurrences.map Occurrence.value : Multiset Bool)

def valueSetObserver : Observer (List Occurrence) (Finset Bool) where
  observe := fun occurrences =>
    (occurrences.map Occurrence.value).toFinset

def occurrenceBag : Contract Occurrence Unit (Multiset Occurrence) where
  observer := occurrenceBagObserver
  demand := { completion := .completeBag }

def valueBag : Contract Occurrence Unit (Multiset Bool) where
  observer := valueBagObserver
  demand := { completion := .completeBag }

def valueSet : Contract Occurrence Unit (Finset Bool) where
  observer := valueSetObserver
  demand := { completion := .completeBag }

/-- One consuming frame which observes both values and occurrence identity. -/
def valueAndOccurrence :
    Contract Occurrence Unit (Multiset Bool × Multiset Occurrence) :=
  valueBag.addAxis occurrenceBagObserver

/-- Replace one occurrence by another with the same value. -/
def forgetIdentity : Change Occurrence Unit where
  source := [firstTrue]
  target := [secondTrue]
  receipt := ()

/-- Remove one of two equal-valued but distinct occurrences. -/
def collapseDuplicateValue : Change Occurrence Unit where
  source := [firstTrue, secondTrue]
  target := [firstTrue]
  receipt := ()

theorem identity_erasure_lawful_at_valueBag :
    valueBag.Preserves forgetIdentity := by
  change ((([firstTrue].map Occurrence.value : List Bool) : Multiset Bool) =
    (([secondTrue].map Occurrence.value : List Bool) : Multiset Bool))
  rfl

theorem identity_erasure_not_lawful_at_occurrenceBag :
    Not (occurrenceBag.Preserves forgetIdentity) := by
  change Not ((([firstTrue] : List Occurrence) : Multiset Occurrence) =
    (([secondTrue] : List Occurrence) : Multiset Occurrence))
  decide

/-- Adding a provenance axis prevents a value-only optimization from being
misapplied to the richer client. -/
theorem identity_erasure_not_lawful_at_valueAndOccurrence :
    Not (valueAndOccurrence.Preserves forgetIdentity) := by
  change Not ((valueBag.addAxis occurrenceBagObserver).Preserves forgetIdentity)
  rw [Contract.preserves_addAxis_iff]
  simp only [identity_erasure_lawful_at_valueBag, true_and]
  exact identity_erasure_not_lawful_at_occurrenceBag

/-- Explicit projection to the value-only coordinate recovers the coarser
contract and its lawful identity erasure. -/
theorem value_projection_unlocks_identity_erasure :
    (valueAndOccurrence.postcompose Prod.fst).Preserves forgetIdentity := by
  exact identity_erasure_lawful_at_valueBag

/-- Set observation licenses duplicate collapse. -/
theorem duplicate_collapse_lawful_at_valueSet :
    valueSet.Preserves collapseDuplicateValue := by
  change ([firstTrue, secondTrue].map Occurrence.value).toFinset =
    ([firstTrue].map Occurrence.value).toFinset
  decide

/-- Bag observation still sees multiplicity and refuses the same collapse. -/
theorem duplicate_collapse_not_lawful_at_valueBag :
    Not (valueBag.Preserves collapseDuplicateValue) := by
  change Not ((([firstTrue, secondTrue].map Occurrence.value : List Bool) :
      Multiset Bool) =
    (([firstTrue].map Occurrence.value : List Bool) : Multiset Bool))
  decide

/-- Provenance-sensitive occurrence bags refuse the collapse as well. -/
theorem duplicate_collapse_not_lawful_at_occurrenceBag :
    Not (occurrenceBag.Preserves collapseDuplicateValue) := by
  change Not ((([firstTrue, secondTrue] : List Occurrence) :
      Multiset Occurrence) =
    (([firstTrue] : List Occurrence) : Multiset Occurrence))
  decide

end Canary

/-! ## Axiom audit -/

#print axioms Contract.preserves_postcompose
#print axioms Contract.preserves_addAxis_iff
#print axioms Contract.OptimizationGuard.postcompose
#print axioms Contract.BatchEvidence.serializable_postcompose
#print axioms Contract.dispatchCertified_lawful
#print axioms Contract.bulk_requires_completeBag
#print axioms Contract.bulk_requires_serializable
#print axioms Contract.completeBag_serializable_dispatches_bulk
#print axioms Contract.singletonEvidence_never_dispatches_bulk
#print axioms Canary.complete_bag_uses_bulk
#print axioms Canary.ordered_stream_refuses_swapped_append
#print axioms Canary.dropFalse_lawful_at_trueOnlyBag
#print axioms Canary.dropFalse_not_lawful_at_guardedRawBag
#print axioms Canary.identity_erasure_not_lawful_at_occurrenceBag
#print axioms Canary.identity_erasure_not_lawful_at_valueAndOccurrence
#print axioms Canary.value_projection_unlocks_identity_erasure
#print axioms Canary.duplicate_collapse_lawful_at_valueSet
#print axioms Canary.duplicate_collapse_not_lawful_at_valueBag

end Mettapedia.GSLT.Core.ObservationControlContract
