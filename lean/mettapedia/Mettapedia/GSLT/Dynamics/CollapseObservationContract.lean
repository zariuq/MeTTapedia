import Mettapedia.GSLT.Core.ObservationControlContract
import Mettapedia.GSLT.Dynamics.CollapseAlgebra

/-!
# Collapse algebras as observation-control contracts

`CollapseAlgebra` says which distinctions a consumer retains.  An
`ObservationDemand` independently says how much of the producer must be
observed.  This module joins those interfaces without identifying them.

The distinction is load-bearing.  Counting needs a complete multiplicity
observation but not occurrence order.  Existence may stop after the first
positive occurrence, while an empty result still requires source closure.
Exact collection retains order and cannot use either relaxation.

The implementation boundary is `DirectFold`.  Its source type is abstract,
so a frontend may change its evaluator representation while reusing the same
fold through `pullback`.  A direct backend fold earns admission only by
proving equality with the materialized algebra; the interface itself does not
manufacture that proof.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.CollapseObservationContract

open Mettapedia.Cybernetics
open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ObservationIndexedPruning
open Mettapedia.GSLT.Dynamics.Collapse

universe uEvent uGuard uSource uOtherSource uReceipt

/-! ## From an algebra to an observation contract -/

/-- Project execution events to the observations consumed by an algebra. -/
def collapseObserver {Event : Type uEvent} {O R Result : Type}
    (project : Event → O) (algebra : CollapseAlgebra O R Result) :
    Observer (List Event) Result where
  observe events := collapseWith algebra (events.map project)

/-- A collapse observer paired with an independent completion demand. -/
def contract {Event : Type uEvent} {O R Result : Type} {Guard : Type uGuard}
    (project : Event → O) (algebra : CollapseAlgebra O R Result)
    (demand : ObservationDemand Guard) : Contract Event Guard Result where
  observer := collapseObserver project algebra
  demand := demand

@[simp] theorem contract_observe {Event : Type uEvent}
    {O R Result : Type}
    {Guard : Type uGuard} (project : Event → O)
    (algebra : CollapseAlgebra O R Result)
    (demand : ObservationDemand Guard) (events : List Event) :
    (contract project algebra demand).observer.observe events =
      collapseWith algebra (events.map project) :=
  rfl

@[simp] theorem contract_demand {Event : Type uEvent}
    {O R Result : Type}
    {Guard : Type uGuard} (project : Event → O)
    (algebra : CollapseAlgebra O R Result)
    (demand : ObservationDemand Guard) :
    (contract project algebra demand).demand = demand :=
  rfl

/-- Two physical accumulator representations implement the same observer
when every completed observation list receives the same result. -/
def Equivalent {O R S Result : Type}
    (left : CollapseAlgebra O R Result)
    (right : CollapseAlgebra O S Result) : Prop :=
  ∀ observations, collapseWith left observations =
    collapseWith right observations

/-- Equivalent algebra realizations admit exactly the same occurrence-list
changes at the observation boundary. -/
theorem preserves_iff_of_equivalent {Event : Type uEvent}
    {O R S Result : Type}
    {Guard : Type uGuard} {Receipt : Type uReceipt}
    (project : Event → O)
    (left : CollapseAlgebra O R Result)
    (right : CollapseAlgebra O S Result)
    (equivalent : Equivalent left right)
    (demand : ObservationDemand Guard)
    (change : Change Event Receipt) :
    (contract project left demand).Preserves change ↔
      (contract project right demand).Preserves change := by
  change
    collapseWith left (change.source.map project) =
        collapseWith left (change.target.map project) ↔
      collapseWith right (change.source.map project) =
        collapseWith right (change.target.map project)
  rw [equivalent (change.source.map project),
    equivalent (change.target.map project)]

/-- Changing only the contraction algebra cannot change dispatch.  Branch and
batch authority remain separate inputs. -/
theorem dispatch_independent_of_algebra {Event : Type uEvent}
    {O R S LeftResult RightResult : Type}
    {Guard : Type uGuard}
    (project : Event → O)
    (left : CollapseAlgebra O R LeftResult)
    (right : CollapseAlgebra O S RightResult)
    (demand : ObservationDemand Guard)
    (branch : BranchAuthority) (batch : BatchAuthority) :
    dispatch (contract project left demand).demand branch batch =
      dispatch (contract project right demand).demand branch batch :=
  rfl

/-! ## Completion adequacy is algebra-relative -/

/-- The finite readout represented by one completion demand.  Complete bags
may reorder but retain every occurrence; ordered and undetermined whole
observations retain the reference stream literally. -/
def CompletionPermits {O : Type}
    (demand : CompletionDemand) (source observed : List O) : Prop :=
  match demand with
  | .first => observed = source.take 1
  | .finitePrefix count => observed = source.take count
  | .completeBag => observed.Perm source
  | .orderedStream => observed = source
  | .undetermined => observed = source

/-- A demand is adequate for an algebra on one source exactly when every
readout it permits has the same collapse result as the complete source. -/
def AdequateOn {O R Result : Type} (algebra : CollapseAlgebra O R Result)
    (demand : CompletionDemand) (source : List O) : Prop :=
  ∀ observed, CompletionPermits demand source observed →
    collapseWith algebra observed = collapseWith algebra source

theorem orderedStream_adequate {O R Result : Type}
    (algebra : CollapseAlgebra O R Result) (source : List O) :
    AdequateOn algebra .orderedStream source := by
  intro observed permitted
  simpa [CompletionPermits] using congrArg (collapseWith algebra) permitted

theorem undetermined_whole_adequate {O R Result : Type}
    (algebra : CollapseAlgebra O R Result) (source : List O) :
    AdequateOn algebra .undetermined source := by
  intro observed permitted
  simpa [CompletionPermits] using congrArg (collapseWith algebra) permitted

/-- A complete-bag readout is adequate exactly when the algebra has the
monoid and commutativity laws needed to ignore the permitted reordering. -/
theorem completeBag_adequate {O R Result : Type}
    (algebra : CollapseAlgebra O R Result)
    (monoid : MonoidCert algebra) (commutative : CommCert algebra)
    (source : List O) : AdequateOn algebra .completeBag source := by
  intro observed permitted
  exact congrArg algebra.finish
    (fold_perm algebra monoid commutative permitted)

/-- A sufficient first-result law: every admitted first row emits the same
absorbing accumulator.  Empty sources still fold through `zero`. -/
theorem first_adequate_of_absorbing_emissions
    {O R Result : Type} (algebra : CollapseAlgebra O R Result)
    (admitted : O → Prop) (done : R)
    (absorbing : AbsorbingCert algebra done)
    (emitsDone : ∀ observation, admitted observation →
      algebra.emit observation = done)
    (source : List O)
    (sourceAdmitted : ∀ observation, observation ∈ source →
      admitted observation) :
    AdequateOn algebra .first source := by
  intro observed permitted
  rw [show observed = source.take 1 from permitted]
  cases source with
  | nil => rfl
  | cons first rest =>
      have firstAdmitted : admitted first :=
        sourceAdmitted first (by simp)
      simp only [List.take, collapseWith, foldStream_cons]
      rw [emitsDone first firstAdmitted]
      simp only [absorbing.absorb]

theorem bag_completeBag_adequate {Answer Receipt : Type}
    (source : List (Obs Answer Receipt)) :
    AdequateOn (BagAlg Answer Receipt) .completeBag source :=
  completeBag_adequate _ bag_monoid bag_comm source

theorem count_comm {Answer Receipt : Type} :
    CommCert (CountAlg Answer Receipt) where
  comm := by intro left right; simp [CountAlg, Nat.add_comm]

theorem count_completeBag_adequate {Answer Receipt : Type}
    (source : List (Obs Answer Receipt)) :
    AdequateOn (CountAlg Answer Receipt) .completeBag source :=
  completeBag_adequate _ count_monoid count_comm source

/-! ### A two-class count for error-suppressing observations -/

/-- Sufficient statistic for an observation policy which prefers one class
of answers, but retains the fallback class when no preferred answer exists.
Both coordinates preserve occurrence multiplicity. -/
structure PreferredFallbackCount where
  preferred : Nat
  fallback : Nat
deriving DecidableEq, Repr

namespace PreferredFallbackCount

/-- Parallel producer fragments combine componentwise. -/
def combine (left right : PreferredFallbackCount) : PreferredFallbackCount :=
  ⟨left.preferred + right.preferred,
    left.fallback + right.fallback⟩

/-- Preferred occurrences hide fallback occurrences exactly when at least one
preferred occurrence was produced. -/
def observe (total : PreferredFallbackCount) : Nat :=
  if total.preferred = 0 then total.fallback else total.preferred

end PreferredFallbackCount

/-- Count answers without materializing them when the observation boundary
suppresses fallback answers precisely when at least one preferred answer is
present.  The classifier is an interface parameter: a dialect may use it for
errors, provisional results, or another explicitly observed answer class. -/
def PreferCountAlg {Answer Receipt : Type}
    (isFallback : Answer → Bool) :
    CollapseAlgebra (Obs Answer Receipt) PreferredFallbackCount Nat where
  zero := ⟨0, 0⟩
  emit observation :=
    if isFallback observation.answer then
      ⟨0, observation.multiplicity⟩
    else
      ⟨observation.multiplicity, 0⟩
  combine := PreferredFallbackCount.combine
  finish := PreferredFallbackCount.observe

theorem preferCount_monoid {Answer Receipt : Type}
    (isFallback : Answer → Bool) :
    MonoidCert (PreferCountAlg (Receipt := Receipt) isFallback) where
  zero_combine := by
    intro total
    cases total
    simp [PreferCountAlg, PreferredFallbackCount.combine]
  combine_zero := by
    intro total
    cases total
    simp [PreferCountAlg, PreferredFallbackCount.combine]
  assoc := by
    intro left middle right
    cases left
    cases middle
    cases right
    simp [PreferCountAlg, PreferredFallbackCount.combine, Nat.add_assoc]

theorem preferCount_comm {Answer Receipt : Type}
    (isFallback : Answer → Bool) :
    CommCert (PreferCountAlg (Receipt := Receipt) isFallback) where
  comm := by
    intro left right
    cases left
    cases right
    simp [PreferCountAlg, PreferredFallbackCount.combine, Nat.add_comm]

/-- A complete occurrence bag is sufficient because the two-class summary is
commutative; neither answer order nor producer scheduling enters the result. -/
theorem preferCount_completeBag_adequate {Answer Receipt : Type}
    (isFallback : Answer → Bool)
    (source : List (Obs Answer Receipt)) :
    AdequateOn (PreferCountAlg (Receipt := Receipt) isFallback)
      .completeBag source :=
  completeBag_adequate _
    (preferCount_monoid isFallback)
    (preferCount_comm isFallback) source

/-! ### A bounded physical presentation

The semantic algebra uses unbounded natural numbers.  A runtime with a fixed
integer representation may implement the same fold by returning failure
before an addition or multiplication would exceed its declared maximum. -/

namespace BoundedCount

/-- Checked addition in a bounded physical count representation. -/
def add? (maximum total amount : Nat) : Option Nat :=
  if total + amount ≤ maximum then some (total + amount) else none

/-- Checked multiplication in a bounded physical count representation. -/
def multiply? (maximum left right : Nat) : Option Nat :=
  if left * right ≤ maximum then some (left * right) else none

inductive Channel where
  | preferred
  | fallback
deriving DecidableEq, Repr

/-- Present one positive weighted occurrence to the two-bin summary. -/
def present? (maximum : Nat) (summary : PreferredFallbackCount)
    (channel : Channel) (multiplicity : Nat) :
    Option PreferredFallbackCount :=
  if multiplicity = 0 then none
  else
    match channel with
    | .preferred =>
        (add? maximum summary.preferred multiplicity).map fun next =>
          ⟨next, summary.fallback⟩
    | .fallback =>
        (add? maximum summary.fallback multiplicity).map fun next =>
          ⟨summary.preferred, next⟩

theorem add?_eq_some_iff (maximum total amount result : Nat) :
    add? maximum total amount = some result ↔
      total + amount ≤ maximum ∧ result = total + amount := by
  simp [add?, eq_comm]

theorem multiply?_eq_some_iff (maximum left right result : Nat) :
    multiply? maximum left right = some result ↔
      left * right ≤ maximum ∧ result = left * right := by
  simp [multiply?, eq_comm]

/-- A successful preferred presentation is exactly componentwise addition. -/
theorem present?_preferred_refines
    (maximum multiplicity : Nat) (summary next : PreferredFallbackCount)
    (success : present? maximum summary .preferred multiplicity = some next) :
    next = summary.combine ⟨multiplicity, 0⟩ := by
  simp only [present?] at success
  split at success <;> simp_all [add?, PreferredFallbackCount.combine]

/-- A successful fallback presentation is exactly componentwise addition. -/
theorem present?_fallback_refines
    (maximum multiplicity : Nat) (summary next : PreferredFallbackCount)
    (success : present? maximum summary .fallback multiplicity = some next) :
    next = summary.combine ⟨0, multiplicity⟩ := by
  simp only [present?] at success
  split at success <;> simp_all [add?, PreferredFallbackCount.combine]

/-- Overflow is a refusal, not a wrapped or invented count. -/
theorem add?_overflow_refuses (maximum total amount : Nat)
    (overflow : maximum < total + amount) :
    add? maximum total amount = none := by
  simp [add?, Nat.not_le.mpr overflow]

/-- Zero does not denote a physical occurrence and is therefore refused. -/
theorem present?_zero_refuses (maximum : Nat)
    (summary : PreferredFallbackCount) (channel : Channel) :
    present? maximum summary channel 0 = none := by
  simp [present?]

end BoundedCount

/-- Match and query cursors emit positive rows.  On that source class,
existence is exactly a first-result demand. -/
theorem any_first_adequate {Answer Receipt : Type}
    (source : List (Obs Answer Receipt))
    (positive : ∀ observation, observation ∈ source →
      observation.multiplicity ≠ 0) :
    AdequateOn (AnyAlg Answer Receipt) .first source := by
  apply first_adequate_of_absorbing_emissions
      (AnyAlg Answer Receipt) (fun observation => observation.multiplicity ≠ 0)
      true any_absorbing
  · intro observation nonzero
    simp [AnyAlg, nonzero]
  · exact positive

/-! ## An implementation interface independent of source representation -/

/-- A semantic producer exposes the completed observation list used by the
reference meaning.  Its physical cursor, trie, evaluator, or continuation
representation is intentionally absent. -/
structure Producer (Source : Type uSource) (O : Type) where
  materialize : Source → List O

namespace Producer

/-- A producer excludes the fallback class when every observation in every
completed materialization is classified as preferred.  This is an admission
certificate supplied by a frontend or compiled plan; the producer interface
does not infer it from answer syntax. -/
def ExcludesFallback {Source : Type uSource} {Answer Receipt : Type}
    (producer : Producer Source (Obs Answer Receipt))
    (isFallback : Answer → Bool) : Prop :=
  ∀ source observation, observation ∈ producer.materialize source →
    isFallback observation.answer = false

/-- Re-present a producer through a source translation. -/
def pullback {Source : Type uSource} {OtherSource : Type uOtherSource}
    {O : Type} (producer : Producer Source O)
    (translate : OtherSource → Source) : Producer OtherSource O where
  materialize source := producer.materialize (translate source)

@[simp] theorem pullback_materialize
    {Source : Type uSource} {OtherSource : Type uOtherSource}
    {O : Type} (producer : Producer Source O)
    (translate : OtherSource → Source) (source : OtherSource) :
    (producer.pullback translate).materialize source =
      producer.materialize (translate source) :=
  rfl

/-- Excluding fallback observations is stable under a change of source
presentation.  The new evaluator need only translate its source into one for
which the certificate has already been proved. -/
theorem ExcludesFallback.pullback
    {Source : Type uSource} {OtherSource : Type uOtherSource}
    {Answer Receipt : Type}
    {producer : Producer Source (Obs Answer Receipt)}
    {isFallback : Answer → Bool}
    (excludes : producer.ExcludesFallback isFallback)
    (translate : OtherSource → Source) :
    (producer.pullback translate).ExcludesFallback isFallback := by
  intro source observation member
  exact excludes (translate source) observation member

/-- A physical source presentation denotes semantic sources and presents the
same completed observations.  Equality is required only at the declared
observation boundary; the two source types and their evaluators may otherwise
be unrelated. -/
structure Presentation {Source : Type uSource}
    {OtherSource : Type uOtherSource} {O : Type}
    (semantic : Producer Source O) (physical : Producer OtherSource O) where
  denote : OtherSource → Source
  exact : ∀ source, physical.materialize source =
    semantic.materialize (denote source)

/-- Functional pullback is the canonical exact presentation, but not the only
one accepted by the interface. -/
def pullbackPresentation {Source : Type uSource}
    {OtherSource : Type uOtherSource} {O : Type}
    (producer : Producer Source O) (denote : OtherSource → Source) :
    Presentation producer (producer.pullback denote) where
  denote := denote
  exact _ := rfl

end Producer

/-! ### Refining a plain count under an exclusion certificate -/

/-- On a completed observation list containing no fallback rows, the
preferred/fallback policy is exactly ordinary occurrence counting. -/
theorem preferCount_eq_count_of_excludesFallback
    {Answer Receipt : Type}
    (isFallback : Answer → Bool)
    (observations : List (Obs Answer Receipt))
    (excludes : ∀ observation, observation ∈ observations →
      isFallback observation.answer = false) :
    collapseWith (PreferCountAlg isFallback) observations =
      collapseWith (CountAlg Answer Receipt) observations := by
  have fold_eq :
      foldStream (PreferCountAlg isFallback) observations =
        ⟨foldStream (CountAlg Answer Receipt) observations, 0⟩ := by
    induction observations with
    | nil => rfl
    | cons observation rest ih =>
        have headPreferred : isFallback observation.answer = false :=
          excludes observation (by simp)
        have restPreferred : ∀ item, item ∈ rest →
            isFallback item.answer = false := by
          intro item member
          exact excludes item (by simp [member])
        rw [foldStream_cons, foldStream_cons, ih restPreferred]
        simp [PreferCountAlg, PreferredFallbackCount.combine,
          CountAlg, headPreferred]
  unfold collapseWith
  rw [fold_eq]
  change
    (if foldStream (CountAlg Answer Receipt) observations = 0 then 0
      else foldStream (CountAlg Answer Receipt) observations) =
    foldStream (CountAlg Answer Receipt) observations
  split
  · next zero => exact zero.symm
  · rfl

/-- A physical direct fold together with its refinement to the reference
materialized observation.  This is an admission obligation, not an assumed
property of every backend. -/
structure DirectFold {Source : Type uSource} {O R Result : Type}
    (producer : Producer Source O)
    (algebra : CollapseAlgebra O R Result) where
  run : Source → Result
  refines : ∀ source, run source =
    collapseWith algebra (producer.materialize source)

namespace DirectFold

/-- A native implementation over a physically different producer.  Its code
need only agree with the semantic fold after denotation; it need not execute
that denotation. -/
structure PresentationImplementation
    {Source : Type uSource} {OtherSource : Type uOtherSource}
    {O R Result : Type}
    {producer : Producer Source O} {physical : Producer OtherSource O}
    {algebra : CollapseAlgebra O R Result}
    (fold : DirectFold producer algebra)
    (presentation : Producer.Presentation producer physical) where
  run : OtherSource → Result
  agrees : ∀ source, run source = fold.run (presentation.denote source)

/-- Transport a fold across an observation-exact presentation while retaining
the physical presentation's native implementation. -/
def present {Source : Type uSource} {OtherSource : Type uOtherSource}
    {O R Result : Type}
    {producer : Producer Source O} {physical : Producer OtherSource O}
    {algebra : CollapseAlgebra O R Result}
    (fold : DirectFold producer algebra)
    (presentation : Producer.Presentation producer physical)
    (implementation : PresentationImplementation fold presentation) :
    DirectFold physical algebra where
  run := implementation.run
  refines source := by
    rw [implementation.agrees, fold.refines, presentation.exact]

@[simp] theorem present_run
    {Source : Type uSource} {OtherSource : Type uOtherSource}
    {O R Result : Type}
    {producer : Producer Source O} {physical : Producer OtherSource O}
    {algebra : CollapseAlgebra O R Result}
    (fold : DirectFold producer algebra)
    (presentation : Producer.Presentation producer physical)
    (implementation : PresentationImplementation fold presentation)
    (source : OtherSource) :
    (fold.present presentation implementation).run source =
      implementation.run source :=
  rfl

/-- A source-presentation change may have its own native implementation of a
direct fold.  `agrees` is the sole transport obligation: the physical `run`
need not construct the old source representation or invoke its evaluator. -/
structure RebaseImplementation
    {Source : Type uSource} {OtherSource : Type uOtherSource}
    {O R Result : Type}
    {producer : Producer Source O} {algebra : CollapseAlgebra O R Result}
    (fold : DirectFold producer algebra) (denote : OtherSource → Source) where
  run : OtherSource → Result
  agrees : ∀ source, run source = fold.run (denote source)

/-- Rebase a proved fold onto a native source implementation.  The semantic
map `denote` occurs only in the proof boundary; execution is exactly
`implementation.run`. -/
def rebase {Source : Type uSource} {OtherSource : Type uOtherSource}
    {O R Result : Type}
    {producer : Producer Source O} {algebra : CollapseAlgebra O R Result}
    (fold : DirectFold producer algebra) (denote : OtherSource → Source)
    (implementation : RebaseImplementation fold denote) :
    DirectFold (producer.pullback denote) algebra :=
  fold.present (producer.pullbackPresentation denote) {
    run := implementation.run
    agrees := implementation.agrees
  }

@[simp] theorem rebase_run
    {Source : Type uSource} {OtherSource : Type uOtherSource}
    {O R Result : Type}
    {producer : Producer Source O} {algebra : CollapseAlgebra O R Result}
    (fold : DirectFold producer algebra) (denote : OtherSource → Source)
    (implementation : RebaseImplementation fold denote)
    (source : OtherSource) :
    (fold.rebase denote implementation).run source =
      implementation.run source :=
  rfl

/-- The materializing reference implementation. -/
def reference {Source : Type uSource} {O R Result : Type}
    (producer : Producer Source O)
    (algebra : CollapseAlgebra O R Result) : DirectFold producer algebra where
  run source := collapseWith algebra (producer.materialize source)
  refines _ := rfl

/-- A proved direct fold survives a change of source representation by
precomposition.  No scheduler or dialect fact is needed. -/
def pullback {Source : Type uSource} {OtherSource : Type uOtherSource}
    {O R Result : Type}
    {producer : Producer Source O} {algebra : CollapseAlgebra O R Result}
    (fold : DirectFold producer algebra) (translate : OtherSource → Source) :
    DirectFold (producer.pullback translate) algebra :=
  fold.rebase translate {
    run := fun source => fold.run (translate source)
    agrees := fun _ => rfl
  }

/-- Reuse an exact plain counter for a preferred/fallback observer when the
producer certifies that this source class cannot emit fallback rows.  The
physical implementation is unchanged; only its observation proof is lifted. -/
def preferCountOfExcludesFallback
    {Source : Type uSource} {Answer Receipt : Type}
    {producer : Producer Source (Obs Answer Receipt)}
    (isFallback : Answer → Bool)
    (fold : DirectFold producer (CountAlg Answer Receipt))
    (excludes : producer.ExcludesFallback isFallback) :
    DirectFold producer (PreferCountAlg isFallback) where
  run := fold.run
  refines source := by
    rw [fold.refines]
    exact (preferCount_eq_count_of_excludesFallback isFallback
      (producer.materialize source)
      (fun observation member => excludes source observation member)).symm

@[simp] theorem preferCountOfExcludesFallback_run
    {Source : Type uSource} {Answer Receipt : Type}
    {producer : Producer Source (Obs Answer Receipt)}
    (isFallback : Answer → Bool)
    (fold : DirectFold producer (CountAlg Answer Receipt))
    (excludes : producer.ExcludesFallback isFallback)
    (source : Source) :
    (fold.preferCountOfExcludesFallback isFallback excludes).run source =
      fold.run source :=
  rfl

@[simp] theorem pullback_run
    {Source : Type uSource} {OtherSource : Type uOtherSource}
    {O R Result : Type}
    {producer : Producer Source O} {algebra : CollapseAlgebra O R Result}
    (fold : DirectFold producer algebra) (translate : OtherSource → Source)
    (source : OtherSource) :
    (fold.pullback translate).run source = fold.run (translate source) :=
  rfl

end DirectFold

/-! ## Multiplicity as the scalar action of a count observer -/

/-- Repeat a completed continuation stream once for every indistinguishable
producer occurrence.  This is the materialized reference meaning of a ground
match followed by a continuation. -/
def repeatObservations {O : Type} (copies : Nat)
    (observations : List O) : List O :=
  (List.replicate copies observations).flatten

/-- Counting a repeated continuation multiplies its count.  This is the
semiring law used by a ground conjunction leg: occurrence alternatives add,
while sequential conjunction multiplies. -/
theorem collapse_count_repeatObservations
    {Answer Receipt : Type} (copies : Nat)
    (observations : List (Obs Answer Receipt)) :
    collapseWith (CountAlg Answer Receipt)
        (repeatObservations copies observations) =
      copies * collapseWith (CountAlg Answer Receipt) observations := by
  change foldStream (CountAlg Answer Receipt)
      (repeatObservations copies observations) =
    copies * foldStream (CountAlg Answer Receipt) observations
  induction copies with
  | zero => simp [repeatObservations, CountAlg]
  | succ copies ih =>
      rw [show repeatObservations (Nat.succ copies) observations =
          observations ++ repeatObservations copies observations by
        simp [repeatObservations, List.replicate_succ]]
      rw [foldStream_append _ count_monoid, ih]
      change foldStream (CountAlg Answer Receipt) observations +
          copies * foldStream (CountAlg Answer Receipt) observations =
        Nat.succ copies *
          foldStream (CountAlg Answer Receipt) observations
      rw [Nat.succ_mul]
      exact Nat.add_comm _ _

/-- A count observer is answer-blind: one weighted witness represents an
entire completed stream with the same total multiplicity. -/
theorem collapse_count_single_weighted_witness
    {Answer Receipt : Type} (answer : Answer) (receipt : Receipt)
    (observations : List (Obs Answer Receipt)) :
    collapseWith (CountAlg Answer Receipt) observations =
      collapseWith (CountAlg Answer Receipt)
        [⟨answer,
          collapseWith (CountAlg Answer Receipt) observations,
          receipt⟩] := by
  simp [collapseWith, foldStream, CountAlg]

/-- **Ground-guard multiplication.**  Repeating a continuation `copies`
times may be replaced by one witness whose multiplicity is the product of the
ground match count and the continuation count. -/
theorem collapse_count_repeat_as_weight
    {Answer Receipt : Type} (copies : Nat) (answer : Answer)
    (receipt : Receipt) (continuation : List (Obs Answer Receipt)) :
    collapseWith (CountAlg Answer Receipt)
        (repeatObservations copies continuation) =
      collapseWith (CountAlg Answer Receipt)
        [⟨answer,
          copies * collapseWith (CountAlg Answer Receipt) continuation,
          receipt⟩] := by
  rw [collapse_count_repeatObservations]
  simp [collapseWith, foldStream, CountAlg]

/-! ## Discriminating canaries -/

namespace Canary

def firstRow : Obs Nat Unit := ⟨0, 1, ()⟩
def secondRow : Obs Nat Unit := ⟨1, 1, ()⟩
def zeroRow : Obs Nat Unit := ⟨0, 0, ()⟩

def oddIsFallback (answer : Nat) : Bool := answer % 2 = 1

/-- A preferred answer suppresses fallback occurrences, independently of
their order in the completed bag. -/
theorem preferCount_mixed_uses_preferred :
    collapseWith (PreferCountAlg oddIsFallback)
      [⟨1, 7, ()⟩, ⟨2, 3, ()⟩, ⟨3, 5, ()⟩] = 3 := by
  decide

/-- When every answer is fallback, their full multiplicity remains visible. -/
theorem preferCount_all_fallback_remains_visible :
    collapseWith (PreferCountAlg oddIsFallback)
      [⟨1, 7, ()⟩, ⟨3, 5, ()⟩] = 12 := by
  decide

/-- Ordinary counting is not an implementation of the preference policy on
a mixed answer bag; the two-coordinate accumulator is load-bearing. -/
theorem plainCount_does_not_implement_preference :
    collapseWith (CountAlg Nat Unit)
        [⟨1, 7, ()⟩, ⟨2, 3, ()⟩, ⟨3, 5, ()⟩] ≠
      collapseWith (PreferCountAlg oddIsFallback)
        [⟨1, 7, ()⟩, ⟨2, 3, ()⟩, ⟨3, 5, ()⟩] := by
  decide

/-- Counting cannot use a first-result demand. -/
theorem count_refuses_first :
    ¬ AdequateOn (CountAlg Nat Unit) .first [firstRow, secondRow] := by
  intro adequate
  have contradiction := adequate [firstRow] (by
    simp [CompletionPermits, firstRow, secondRow])
  simp [collapseWith, foldStream, CountAlg, firstRow, secondRow] at contradiction

/-- Exact collection cannot accept complete-bag reordering. -/
theorem collect_refuses_completeBag :
    ¬ AdequateOn (Collect Nat Unit) .completeBag [firstRow, secondRow] := by
  intro adequate
  have contradiction := adequate [secondRow, firstRow] (by
    exact List.Perm.swap firstRow secondRow [])
  simp [collapseWith, foldStream, Collect, firstRow, secondRow] at contradiction

/-- Positivity is load-bearing for existence: a zero-multiplicity physical
row before a real row cannot discharge first-result demand. -/
theorem any_first_requires_positive_rows :
    ¬ AdequateOn (AnyAlg Nat Unit) .first [zeroRow, secondRow] := by
  intro adequate
  have contradiction := adequate [zeroRow] (by
    simp [CompletionPermits, zeroRow, secondRow])
  simp [collapseWith, foldStream, AnyAlg, zeroRow, secondRow] at contradiction

def replaceAnswer : Change (Obs Nat Unit) Unit where
  source := [firstRow]
  target := [secondRow]
  receipt := ()

def exactRows : Observer (List (Obs Nat Unit)) (List (Obs Nat Unit)) :=
  Observer.identity (List (Obs Nat Unit))

def anyFirst : Contract (Obs Nat Unit) Unit Bool :=
  contract id (AnyAlg Nat Unit) { completion := .first }

/-- Existence forgets which answer supplied the witness. -/
theorem replaceAnswer_preserves_any : anyFirst.Preserves replaceAnswer := by
  rfl

/-- Adding an exact occurrence axis prevents existence-only contraction from
silently erasing answer identity. -/
theorem replaceAnswer_refused_with_exact_axis :
    ¬ (anyFirst.addAxis exactRows).Preserves replaceAnswer := by
  rw [Contract.preserves_addAxis_iff]
  simp only [replaceAnswer_preserves_any, true_and]
  change ¬ [firstRow] = [secondRow]
  intro equal
  have answersEqual := congrArg (List.map Obs.answer) equal
  simp [firstRow, secondRow] at answersEqual

/-- Existence demand does not manufacture a single-path execution policy. -/
theorem any_first_remains_strategy_neutral :
    dispatch anyFirst.demand .general .singletonOnly =
      { readout := .first, activation := .controlled } :=
  rfl

def oneRowProducer : Producer Unit (Obs Nat Unit) where
  materialize _ := [firstRow]

def preferredRowsProducer : Producer Unit (Obs Nat Unit) where
  materialize _ := [⟨2, 2, ()⟩, ⟨4, 3, ()⟩]

def mixedRowsProducer : Producer Unit (Obs Nat Unit) where
  materialize _ := [⟨2, 2, ()⟩, ⟨3, 3, ()⟩]

def unaryMultiplicityProducer : Producer Nat (Obs Nat Unit) where
  materialize multiplicity := [⟨7, multiplicity + 1, ()⟩]

def listLengthDenotation (physical : List Unit) : Nat := physical.length

def unaryMultiplicityCount :
    DirectFold unaryMultiplicityProducer (CountAlg Nat Unit) where
  run multiplicity := multiplicity + 1
  refines multiplicity := by
    simp [unaryMultiplicityProducer, collapseWith, foldStream, CountAlg]

def nativeListLengthImplementation :
    DirectFold.RebaseImplementation unaryMultiplicityCount
      listLengthDenotation where
  run physical := physical.length + 1
  agrees _ := rfl

theorem preferredRows_exclude_fallback :
    preferredRowsProducer.ExcludesFallback oddIsFallback := by
  intro source observation member
  simp [preferredRowsProducer] at member
  rcases member with rfl | rfl
  · decide
  · decide

/-- The exclusion certificate lifts a plain exact counter to the two-class
observer without changing its implementation. -/
theorem certified_plain_count_refines_preference :
    (DirectFold.preferCountOfExcludesFallback oddIsFallback
      (DirectFold.reference preferredRowsProducer (CountAlg Nat Unit))
      preferredRows_exclude_fallback).run () = 5 := by
  decide

/-- A producer containing a fallback occurrence cannot manufacture the
exclusion certificate needed to reuse a plain counter. -/
theorem mixed_rows_refuse_exclusion :
    ¬ mixedRowsProducer.ExcludesFallback oddIsFallback := by
  intro excludes
  have classified := excludes () (⟨3, 3, ()⟩ : Obs Nat Unit) (by
    simp [mixedRowsProducer])
  simp [oddIsFallback] at classified

/-- A physically different source can compute the fold natively.  The
semantic denotation is used to prove adequacy but is absent from `run`. -/
theorem native_rebase_uses_physical_run (physical : List Unit) :
    (unaryMultiplicityCount.rebase listLengthDenotation
      nativeListLengthImplementation).run physical = physical.length + 1 :=
  rfl

/-- A constant-zero native implementation cannot satisfy the presentation
interface for a physical source denoting one observation. -/
theorem constantZero_cannot_rebase_nonempty_source :
    ¬ (∀ physical : List Unit,
      (0 : Nat) = unaryMultiplicityCount.run
        (listLengthDenotation physical)) := by
  intro claimed
  have contradiction := claimed []
  simp [unaryMultiplicityCount, listLengthDenotation] at contradiction

/-- Count compression is observer-relative: exact collection distinguishes
two different answers from one anonymous weighted witness. -/
theorem collect_refuses_answer_blind_weighting :
    collapseWith (Collect Nat Unit)
        [⟨1, 1, ()⟩, ⟨2, 1, ()⟩] ≠
      collapseWith (Collect Nat Unit) [⟨0, 2, ()⟩] := by
  decide

/-- A constant-zero count does not satisfy the direct-fold interface for a
producer that emits one occurrence. -/
theorem constantZero_is_not_a_count_refinement :
    ¬ (∀ source, (0 : Nat) =
      collapseWith (CountAlg Nat Unit)
        (oneRowProducer.materialize source)) := by
  intro claimed
  have contradiction := claimed ()
  simp [oneRowProducer, firstRow, collapseWith, foldStream, CountAlg] at contradiction

end Canary

/-! ## Axiom audit -/

#print axioms preserves_iff_of_equivalent
#print axioms dispatch_independent_of_algebra
#print axioms completeBag_adequate
#print axioms first_adequate_of_absorbing_emissions
#print axioms bag_completeBag_adequate
#print axioms count_completeBag_adequate
#print axioms preferCount_completeBag_adequate
#print axioms BoundedCount.add?_eq_some_iff
#print axioms BoundedCount.multiply?_eq_some_iff
#print axioms BoundedCount.present?_preferred_refines
#print axioms BoundedCount.present?_fallback_refines
#print axioms BoundedCount.add?_overflow_refuses
#print axioms BoundedCount.present?_zero_refuses
#print axioms any_first_adequate
#print axioms Producer.ExcludesFallback.pullback
#print axioms Producer.pullbackPresentation
#print axioms preferCount_eq_count_of_excludesFallback
#print axioms DirectFold.pullback
#print axioms DirectFold.rebase
#print axioms DirectFold.present
#print axioms DirectFold.preferCountOfExcludesFallback
#print axioms collapse_count_repeatObservations
#print axioms collapse_count_single_weighted_witness
#print axioms collapse_count_repeat_as_weight
#print axioms Canary.count_refuses_first
#print axioms Canary.collect_refuses_completeBag
#print axioms Canary.any_first_requires_positive_rows
#print axioms Canary.preferCount_mixed_uses_preferred
#print axioms Canary.preferCount_all_fallback_remains_visible
#print axioms Canary.plainCount_does_not_implement_preference
#print axioms Canary.replaceAnswer_refused_with_exact_axis
#print axioms Canary.any_first_remains_strategy_neutral
#print axioms Canary.constantZero_is_not_a_count_refinement
#print axioms Canary.certified_plain_count_refines_preference
#print axioms Canary.mixed_rows_refuse_exclusion
#print axioms Canary.native_rebase_uses_physical_run
#print axioms Canary.constantZero_cannot_rebase_nonempty_source
#print axioms Canary.collect_refuses_answer_blind_weighting

end Mettapedia.GSLT.Dynamics.CollapseObservationContract
