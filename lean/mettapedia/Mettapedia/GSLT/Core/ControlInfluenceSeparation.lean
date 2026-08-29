import Mettapedia.GSLT.Core.ObservationControlContract
import Mettapedia.GSLT.Core.PolicyFamilySufficiency

/-!
# Semantic and operational interpretations of control influence

A candidate-local grade or annotation does not have one predetermined
meaning.  This module keeps three readings separate.

* A control-only interpretation changes activation or traversal.  A pure
  permutation is invisible to complete finite-bag observation, but can become
  visible to a finite-prefix or explicitly ordered-stream consumer.
* A semantic interpretation filters or otherwise transforms the observed
  candidates.  It may change even a complete bag and therefore belongs to the
  authored language meaning rather than to an evaluator hint.
* An enriched interpretation retains grades for a declared resolution
  algebra.  Erasing that enrichment recovers the ordinary candidate bag;
  observing it retains strictly more information.

Temporary activation partitions retain deferred occurrences.  Permanent
pruning remains a third operation and requires the existing observer-relative
admission proof.  No interpretation is selected here for any particular
language.

An annotation can drive a family of policies exactly when those decisions
factor through the annotation readout.  This criterion does not privilege
scalar weights: evidence states, structural features, learned vectors, and
orders are all possible readouts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ControlInfluenceSeparation

open Mettapedia.Cybernetics
open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ObservationIndexedPruning

universe uItem uReceipt uState uPolicy uResult uReadout uView uGrade

/-! ## Observer-relative relevance -/

/-- An influence is inert when the declared observer cannot distinguish its
output from its input. -/
def InertAt {Item : Type uItem} {View : Type uView}
    (observer : Observer (List Item) View)
    (influence : List Item → List Item) : Prop :=
  ∀ items, observer.observe (influence items) = observer.observe items

/-- An influence is relevant when some input is distinguishable after it. -/
def RelevantAt {Item : Type uItem} {View : Type uView}
    (observer : Observer (List Item) View)
    (influence : List Item → List Item) : Prop :=
  ∃ items, observer.observe (influence items) ≠ observer.observe items

/-- An observer-inert influence cannot also be relevant to that observer. -/
theorem InertAt.not_relevantAt {Item : Type uItem} {View : Type uView}
    {observer : Observer (List Item) View}
    {influence : List Item → List Item}
    (inert : InertAt observer influence) :
    ¬ RelevantAt observer influence := by
  rintro ⟨items, distinguishable⟩
  exact distinguishable (inert items)

/-- Relevance supplies a witness refuting observer-relative inertness. -/
theorem RelevantAt.not_inertAt {Item : Type uItem} {View : Type uView}
    {observer : Observer (List Item) View}
    {influence : List Item → List Item}
    (relevant : RelevantAt observer influence) :
    ¬ InertAt observer influence := by
  intro inert
  exact inert.not_relevantAt relevant

/-- A control-only reordering retains every occurrence and its multiplicity. -/
def PermutationOnly {Item : Type uItem}
    (influence : List Item → List Item) : Prop :=
  ∀ items, (influence items).Perm items

/-- Complete finite-bag semantics makes every pure reordering inert. -/
theorem permutationOnly_inertAt_bag {Item : Type uItem}
    {influence : List Item → List Item}
    (complete : PermutationOnly influence) :
    InertAt
      ({ observe := fun items : List Item => (items : Multiset Item) } :
        Observer (List Item) (Multiset Item)) influence := by
  intro items
  exact Quot.sound (complete items)

/-- A finite-prefix observation makes only the requested prefix semantic. -/
def prefixObserver (limit : Nat) (Item : Type uItem) :
    Observer (List Item) (List Item) where
  observe := List.take limit

/-- Exact stream observation is an explicit strengthening over bag
observation. -/
def streamObserver (Item : Type uItem) : Observer (List Item) (List Item) :=
  Observer.identity (List Item)

/-! ## Distinct readings of a grade -/

/-- The candidate-local grade vector offered to a control policy. -/
def gradeReadout {Item : Type uItem} {Grade : Type uGrade}
    (grade : Item → Grade) : List Item → List Grade :=
  List.map grade

/-- A grade supports a requested control family when all its decisions can be
reconstructed from candidate-local grades. -/
def SupportsControl {Item : Type uItem} {Grade : Type uGrade}
    (family : PolicyFamily.{uItem, uPolicy, uResult} (List Item))
    (grade : Item → Grade) : Prop :=
  family.SupportsReadout (gradeReadout grade)

/-- Semantic filtering is a distinct interpretation: rejected candidates are
removed from the denotation presented to the observer. -/
def semanticFilterByGrade {Item : Type uItem} {Grade : Type uGrade}
    (grade : Item → Grade) (accept : Grade → Bool) :
    List Item → List Item :=
  List.filter (fun item => accept (grade item))

/-! ## Enriched resolution and erasure -/

/-- Attach a candidate-local grade without yet deciding how a contention set
is resolved. -/
def attachGrades {Item : Type uItem} {Grade : Type uGrade}
    (grade : Item → Grade) : List Item → List (Item × Grade) :=
  List.map (fun item => (item, grade item))

/-- Ordinary bag observation forgets the enrichment but retains candidate
occurrences and multiplicity. -/
def eraseGradeBagObserver (Item : Type uItem) (Grade : Type uGrade) :
    Observer (List (Item × Grade)) (Multiset Item) where
  observe := fun candidates => (candidates.map Prod.fst : Multiset Item)

/-- A richer observer retains candidate-local grades.  A resolution algebra
may subsequently aggregate or normalize this information. -/
def gradedBagObserver (Item : Type uItem) (Grade : Type uGrade) :
    Observer (List (Item × Grade)) (Multiset (Item × Grade)) where
  observe := fun candidates => (candidates : Multiset (Item × Grade))

/-- Merely attaching grades is invisible after erasing the enrichment. -/
theorem eraseGradeBag_attachGrades {Item : Type uItem} {Grade : Type uGrade}
    (grade : Item → Grade) (items : List Item) :
    (eraseGradeBagObserver Item Grade).observe (attachGrades grade items) =
      (items : Multiset Item) := by
  simp [eraseGradeBagObserver, attachGrades, Function.comp_def]

/-- Support filtering is not implicit in enrichment: it is the separate
decision to retain only grades accepted by the chosen resolution reading. -/
def supportByGrade {Item : Type uItem} {Grade : Type uGrade}
    (accept : Grade → Bool) : List (Item × Grade) → List Item :=
  fun candidates =>
    (candidates.filter (fun candidate => accept candidate.2)).map Prod.fst

/-- Filtering after attaching grades is exactly the semantic-filter
interpretation above. -/
theorem supportByGrade_attachGrades {Item : Type uItem} {Grade : Type uGrade}
    (grade : Item → Grade) (accept : Grade → Bool) (items : List Item) :
    supportByGrade accept (attachGrades grade items) =
      semanticFilterByGrade grade accept items := by
  simp only [supportByGrade, attachGrades, semanticFilterByGrade]
  induction items with
  | nil => rfl
  | cons item tail inductionHypothesis =>
      cases gradeResult : accept (grade item) <;>
        simp [gradeResult, inductionHypothesis]

/-! ## Temporary activation -/

/-- A temporary activation partition.  `active` may run now; `deferred`
remains live.  The certificate prevents an activation policy from silently
becoming a semantic filter. -/
structure ActivationPartition (Item : Type uItem) (Receipt : Type uReceipt) where
  source : List Item
  active : List Item
  deferred : List Item
  receipt : Receipt
  complete : source.Perm (active ++ deferred)

namespace ActivationPartition

variable {Item : Type uItem} {Receipt : Type uReceipt}

/-- Recombining active and deferred work preserves the exact occurrence bag. -/
theorem recombinedBag (partition : ActivationPartition Item Receipt) :
    ((partition.active ++ partition.deferred : List Item) : Multiset Item) =
      (partition.source : Multiset Item) := by
  exact Quot.sound partition.complete.symm

/-- Activation partitions conserve occurrence count. -/
theorem length_eq (partition : ActivationPartition Item Receipt) :
    partition.active.length + partition.deferred.length =
      partition.source.length := by
  simpa using partition.complete.length_eq.symm

end ActivationPartition

/-! ## Open annotation-to-policy equipment -/

/-- A readout together with the exact advisory policies it can execute.

The policy family may contain heterogeneous decisions.  Its realization is
the executable factorization certificate: every decision made from the
readout agrees with the decision on the retained state. -/
structure AdvisoryReadout (State : Type uState) where
  family : PolicyFamily.{uState, uPolicy, uResult} State
  Readout : Type uReadout
  readout : State → Readout
  realization : family.ReadoutRealization readout

namespace AdvisoryReadout

variable {State : Type uState}

/-- Execute one declared policy using only the admitted readout. -/
def run (advisory : AdvisoryReadout.{uState, uPolicy, uResult, uReadout} State)
    (policy : advisory.family.Policy) (state : State) :
    advisory.family.Result policy :=
  advisory.realization.run policy (advisory.readout state)

/-- Advisory execution agrees with the policy on the retained state. -/
theorem run_agrees
    (advisory : AdvisoryReadout.{uState, uPolicy, uResult, uReadout} State)
    (policy : advisory.family.Policy) (state : State) :
    advisory.run policy state = advisory.family.decide policy state :=
  advisory.realization.agrees policy state

/-- Restricting the requested policy family preserves the same readout. -/
def reindex
    (advisory : AdvisoryReadout.{uState, uPolicy, uResult, uReadout} State)
    {RequestedPolicy : Type*}
    (select : RequestedPolicy → advisory.family.Policy) :
    AdvisoryReadout State where
  family := advisory.family.reindex select
  Readout := advisory.Readout
  readout := advisory.readout
  realization := advisory.realization.reindex select

end AdvisoryReadout

/-! ## Positive and negative controls -/

namespace Canary

def reverseInfluence : List Nat → List Nat := List.reverse

/-- Reversal is a control-only permutation on every finite candidate list. -/
theorem reverse_permutationOnly : PermutationOnly reverseInfluence := by
  intro items
  exact items.reverse_perm

/-- Under ordinary complete-bag observation, reversal has no semantic effect. -/
theorem reverse_inertAt_completeBag :
    InertAt
      ({ observe := fun items : List Nat => (items : Multiset Nat) } :
        Observer (List Nat) (Multiset Nat)) reverseInfluence :=
  permutationOnly_inertAt_bag reverse_permutationOnly

/-- The same influence becomes relevant when a consumer requests the first
candidate. -/
theorem reverse_relevantAt_first :
    RelevantAt (prefixObserver 1 Nat) reverseInfluence := by
  refine ⟨[1, 2], ?_⟩
  decide

/-- Exact stream semantics also makes the reordering observable. -/
theorem reverse_relevantAt_stream :
    RelevantAt (streamObserver Nat) reverseInfluence := by
  refine ⟨[1, 2], ?_⟩
  decide

def evenGrade (candidate : Nat) : Bool := candidate % 2 == 0

def eligibilityVectorPolicy : PolicyFamily (List Nat) where
  Policy := Unit
  Result := fun _ => List Bool
  decide := fun _ candidates => candidates.map evenGrade

/-- A grade has control meaning for a policy which requests exactly its
candidate-local eligibility vector. -/
theorem evenGrade_supports_eligibilityVectorPolicy :
    SupportsControl eligibilityVectorPolicy evenGrade := by
  refine ⟨{
    run := fun _ grades => grades
    agrees := ?_ }⟩
  intro policy candidates
  rfl

def constantGrade (_ : Nat) : Unit := ()

/-- A readout which erases the relevant distinction cannot drive the same
control policy. -/
theorem constantGrade_does_not_support_eligibilityVectorPolicy :
    Not (SupportsControl eligibilityVectorPolicy constantGrade) := by
  apply eligibilityVectorPolicy.not_supportsReadout_of_policy_collision
    (gradeReadout constantGrade)
    (first := [1]) (second := [2])
    (by rfl)
    ()
  change [false] ≠ [true]
  decide

def evenSemanticInfluence : List Nat → List Nat :=
  semanticFilterByGrade evenGrade id

/-- Interpreting the same grade as a semantic filter changes a complete bag. -/
theorem evenSemanticInfluence_relevantAt_completeBag :
    RelevantAt
      ({ observe := fun items : List Nat => (items : Multiset Nat) } :
        Observer (List Nat) (Multiset Nat)) evenSemanticInfluence := by
  refine ⟨[1, 2], ?_⟩
  decide

def unitGrade (_ : Nat) : Nat := 1

def variedGrade (candidate : Nat) : Nat := candidate

/-- Nonzero quantitative grades disappear under ordinary bag erasure. -/
theorem variedGrade_erases_to_completeBag :
    (eraseGradeBagObserver Nat Nat).observe
        (attachGrades variedGrade [1, 2]) =
      (([1, 2] : List Nat) : Multiset Nat) :=
  eraseGradeBag_attachGrades variedGrade [1, 2]

/-- The same quantitative distinction is visible to the enriched observer. -/
theorem variedGrade_visible_when_reified :
    (gradedBagObserver Nat Nat).observe (attachGrades variedGrade [1, 2]) ≠
      (gradedBagObserver Nat Nat).observe (attachGrades unitGrade [1, 2]) := by
  decide

def zeroFirstGrade (candidate : Nat) : Nat := if candidate = 1 then 0 else 1

def acceptNonzero (grade : Nat) : Bool := grade != 0

/-- Reading zero as absent support changes ordinary nondeterministic meaning. -/
theorem zeroGrade_filters_completeBag :
    ((supportByGrade acceptNonzero
        (attachGrades zeroFirstGrade [1, 2]) : List Nat) : Multiset Nat) ≠
      (([1, 2] : List Nat) : Multiset Nat) := by
  decide

def temporaryEvenActivation : ActivationPartition Nat Unit where
  source := [1, 2]
  active := [2]
  deferred := [1]
  receipt := ()
  complete := by decide

/-- Temporarily inactive work remains accounted for. -/
theorem temporary_activation_recombines :
    ((temporaryEvenActivation.active ++ temporaryEvenActivation.deferred :
        List Nat) : Multiset Nat) =
      (temporaryEvenActivation.source : Multiset Nat) :=
  temporaryEvenActivation.recombinedBag

/-- Publishing only the active part would change raw bag semantics; deferred
work is operational state, not a rejected result. -/
theorem active_part_is_not_completeBag :
    ((temporaryEvenActivation.active : List Nat) : Multiset Nat) ≠
      (temporaryEvenActivation.source : Multiset Nat) := by
  decide

def rawBagContract : Contract Nat Unit (Multiset Nat) where
  observer := { observe := fun items => (items : Multiset Nat) }
  demand := { completion := .completeBag }

def dropUnselected : Change Nat Unit where
  source := [1, 2]
  target := [1]
  receipt := ()

/-- A usable control readout still grants no permission to delete an
occurrence from raw-bag semantics. -/
theorem control_readout_does_not_grant_pruning :
    ¬ rawBagContract.Preserves dropUnselected := by
  change Not ((([1, 2] : List Nat) : Multiset Nat) =
    (([1] : List Nat) : Multiset Nat))
  decide

def evenBagContract : Contract Nat Unit (Multiset Nat) where
  observer :=
    { observe := fun items =>
        (items.filter (fun item => item % 2 = 0) : Multiset Nat) }
  demand := { completion := .completeBag }

def dropOdd : Change Nat Unit where
  source := [1, 2]
  target := [2]
  receipt := ()

/-- The same physical deletion is lawful when filtering is part of the
declared semantic observation. -/
theorem semantic_filter_grants_exact_drop :
    evenBagContract.Preserves dropOdd := by
  change
    (([1, 2].filter (fun item : Nat => item % 2 = 0) : List Nat) :
      Multiset Nat) =
    (([2].filter (fun item : Nat => item % 2 = 0) : List Nat) :
      Multiset Nat)
  decide

end Canary

#print axioms permutationOnly_inertAt_bag
#print axioms InertAt.not_relevantAt
#print axioms RelevantAt.not_inertAt
#print axioms ActivationPartition.recombinedBag
#print axioms ActivationPartition.length_eq
#print axioms AdvisoryReadout.run_agrees
#print axioms Canary.reverse_inertAt_completeBag
#print axioms Canary.reverse_relevantAt_first
#print axioms Canary.reverse_relevantAt_stream
#print axioms Canary.evenGrade_supports_eligibilityVectorPolicy
#print axioms Canary.constantGrade_does_not_support_eligibilityVectorPolicy
#print axioms Canary.evenSemanticInfluence_relevantAt_completeBag
#print axioms eraseGradeBag_attachGrades
#print axioms supportByGrade_attachGrades
#print axioms Canary.variedGrade_erases_to_completeBag
#print axioms Canary.variedGrade_visible_when_reified
#print axioms Canary.zeroGrade_filters_completeBag
#print axioms Canary.temporary_activation_recombines
#print axioms Canary.active_part_is_not_completeBag
#print axioms Canary.control_readout_does_not_grant_pruning
#print axioms Canary.semantic_filter_grants_exact_drop

end Mettapedia.GSLT.Core.ControlInfluenceSeparation
