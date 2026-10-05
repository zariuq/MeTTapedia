import Mettapedia.GSLT.Distinction.GradedCongruence
import Mettapedia.GSLT.Logic.PrivilegedView
import Mettapedia.GSLT.Dynamics.MemoizationObserver
import Mettapedia.GSLT.Dynamics.CacheCoherence
import Mettapedia.GSLT.Dynamics.OrderedDemand
import Mettapedia.GSLT.Distinction.ProductiveBlocksControls

/-!
# Two dictionary entries: privileged views and discernibility

* **The observational end is the privileged view's bubble**
  (`continuationTolerance_indistinguishable_iff_wordBehaviour`).  For a monoid
  of contexts and declared consumers, two terms are indistinguishable for the
  greatest graded congruence protecting the consumers
  (`Cybernetics.DistinctionCalculus.continuationTolerance`) exactly when their
  word behaviours coincide, with the contexts as inputs and the consumer
  profile as the evaluation (`GSLT.PrivilegedView.wordBehaviour`): the
  coarsest view stable under every context that keeps the profile.
* **Discernibility grades** (Quine; Saunders, *Physics and Leibniz's
  principles*; Muller and Saunders, *Discerning fermions*).  Two points are
  absolutely discernible by a family of monadic observers when one of them
  separates the points (`AbsolutelyDiscernible`), and weakly discernible by a
  tolerance when they are apart, an irreflexive symmetric relation
  (`Tolerance.Apart`).  Points exchanged by a symmetry are absolutely
  indiscernible by every invariant observer
  (`not_absolutelyDiscernible_of_symmetry`); on two points at distance one
  that a symmetry of the observer exchanges, the tolerance discerns weakly
  while no invariant monadic observer discerns absolutely (`weak_not_absolute`).
  A tolerance is symmetric, so it never discerns relatively; relative
  discernibility needs a directed kernel, such as one-sided route grades.
* **Coarsening of crisp observers is descent** (`ofReport_extends_iff_soundKey`).
  The crisp observer of a report `key` extends to the crisp observer of `obs`
  exactly when `obs` descends along `key`: a sound memo key
  (`MemoizationObserver.SoundKey`), which is constancy on the fibres of
  `NonFactorization` (`Consolidation.soundKey_iff_constantOnFibers`).  A
  `NonTrivialFiber` refutes the coarsening (`not_ofReport_extends_of_fiber`).

## The d-calc reading of the lane modules

Each row names a theorem, or a `NonTrivialFiber` witnessing a difference.  The
entries marked *here* are proved in this module; the others are cited where they
are proved.

| d-calc | GSLT / OSLF | Lean |
|---|---|---|
| coarsening of crisp observers | sound memo key, constancy on fibres | `ofReport_extends_iff_soundKey` (here) |
| a strict coarsening | a non-trivial fibre | `not_ofReport_extends_of_fiber` (here) |
| the observer of validated captured readings refines the authorized answer | `CacheCoherence.soundKey_readingKey` | `readingKey_extends_authorized` (here) |
| the ordered effect-aware observer refines the answer bag | `OrderedDemand.Observation`, `answerBag` | `trace_extends_answerBag` (here) |
| the answer bag forgets order | — | `answerBag_forgets_order` (here, fibre) |
| ordered sharing licence refines the bag licence | `OrderedDemand.bag_agreement_of_ordered` | cited; converse refuted by `OrderedDemand.Controls.unused_effect_control` |
| completion and live frontier are two observers | `HE.OrderedEffectObservation` | `completion_ne_live_frontier` (cited) |
| zero kernel of the block observer | block bisimilarity of `ProductiveBlocks.Machine.reading` | `blocks_forget_status` (here, fibre against the status atoms) |
| an external classification is an observer restriction | `ProductiveBlocks.Machine.readingOutside` | `ProductiveBlocks.Controls.external_erases_callback` (cited) |
| preservation grade zero of a relocation on live objects | `LiveRelocation` | `LiveRelocation.aliases_iff` (cited); no session splits a shared world, `RelocationControls.split_world_has_two_images` |
| history interleaving needs independence | `HistoryIndependence.Concurrent` | `HistoryIndependence.run_swap`; `HistoryIndependence.interleavings_differ_not_concurrent` (cited) |
| a ledger in a noncommutative monoid | declared account in path order | `CausalGluing.Occurrences.account_tile_iff_commute`, `ProductionLicences.eager_eq_lazy_iff_commute_denote`, both from `Algebra.OrderedProductCommutation.prod_cons_eq_prod_concat_iff` |
| equal payload, different history | provenance store | `CausalGluing.Controls.payload_store_fiber` (cited, fibre) |
| the observer of futures | forward observation of a span | `SpanTransport.Controls.Passed.forward_observer_fiber` (cited, fibre against the past) |
| Livšic exactness | replay by endpoints | `LevelAccounts.exact_replay`; `LevelAccounts.work_replay_not_by_endpoints` (cited) |
| span of a schedule | not a path cost | `LevelAccounts.span_not_path_function` (cited, fibre) |
| observer weights | not semantic coefficients | `ProductionLicences.answers_coefficient_erasure`; `ProductionLicences.Controls.coefficient_not_a_weight` (cited) |
| graded observer at depth `n` over a value scale | the `n`-step approximant | `Constructive.PresentedSystem.depthBound_eq_zero_iff_approx`; the classical distance is the supremum of the depth bounds, `Constructive.PresentedSystem.logicalDistance_eq_iSup_depthBound` (cited) |
| a minimal alphabet relative to its predicates | consumer letters | `PrioritizedSpans.merge_breaks_label` (cited, fibre) |
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Dictionary

open Mettapedia.Cybernetics.DistinctionCalculus
open Mettapedia.GSLT.PrivilegedView

universe u v w

/-! ## The observational end and the privileged view -/

section Privileged

variable {C : Type v} {V : Type u} (M : ContextMonoid C V) {J : Type w} (F : ConsumerFamily J V)

/-- The consumer profile of a term. -/
def profile (term : V) : J → ℚ := fun consumer => F.value consumer term

/-- Running a word of contexts acts by one context. -/
theorem foldl_act (word : List C) :
    ∃ context, ∀ term, word.foldl (fun state input => M.act input state) term =
      M.act context term := by
  induction word with
  | nil => exact ⟨M.unit, fun term => (M.act_unit term).symm⟩
  | cons input rest inductionHypothesis =>
      obtain ⟨context, acts⟩ := inductionHypothesis
      refine ⟨M.mul context input, fun term => ?_⟩
      rw [List.foldl_cons, acts, M.act_mul]

variable [Fintype C] [Fintype J] [Nonempty J]

/-- **The zero kernel of the observational end is the bubble of the privileged
view**: the word behaviour with the contexts as inputs and the consumer profile
as evaluation. -/
theorem continuationTolerance_indistinguishable_iff_wordBehaviour (left right : V) :
    (continuationTolerance M F).Indistinguishable left right ↔
      wordBehaviour (fun state input => M.act input state) (profile F) left =
        wordBehaviour (fun state input => M.act input state) (profile F) right := by
  rw [continuationTolerance_indistinguishable_iff]
  constructor
  · intro same
    funext word
    obtain ⟨context, acts⟩ := foldl_act M word
    funext consumer
    change F.value consumer (word.foldl _ left) = F.value consumer (word.foldl _ right)
    rw [acts, acts]
    exact same context consumer
  · intro same context consumer
    have := congrFun (congrFun same [context]) consumer
    exact this

end Privileged

/-! ## Discernibility -/

section Discernibility

variable {V : Type u} {W : Type v}

/-- **Absolute discernibility** by a family of monadic observers: some observer
gives the two points different values. -/
def AbsolutelyDiscernible {ι : Sort w} (observers : ι → V → W) (first second : V) : Prop :=
  ∃ index, observers index first ≠ observers index second

/-- **Points exchanged by a symmetry are absolutely indiscernible** by every
observer invariant under it. -/
theorem not_absolutelyDiscernible_of_symmetry {ι : Sort w} (symmetry : V → V)
    (observers : ι → V → W) (invariant : ∀ index point, observers index (symmetry point) =
      observers index point) {first second : V} (exchanges : symmetry first = second) :
    ¬ AbsolutelyDiscernible observers first second := by
  rintro ⟨index, different⟩
  apply different
  rw [← exchanges, invariant]

/-- **Weakly but not absolutely discernible.** The two Booleans at distance
one: negation is a symmetry of the observer, the observer puts them apart, and
no monadic observer invariant under negation tells them apart. -/
theorem weak_not_absolute :
    (∀ first second : Bool, (Tolerance.ofReport (id : Bool → Bool)).similarity (!first) (!second) =
        (Tolerance.ofReport (id : Bool → Bool)).similarity first second) ∧
      (Tolerance.ofReport (id : Bool → Bool)).Apart true false ∧
      ∀ {ι : Sort w} (observers : ι → Bool → W),
        (∀ index point, observers index (!point) = observers index point) →
          ¬ AbsolutelyDiscernible observers true false := by
  refine ⟨?_, ?_, fun observers invariant =>
    not_absolutelyDiscernible_of_symmetry (fun point => !point) observers invariant rfl⟩
  · intro first second
    cases first <;> cases second <;> rfl
  · norm_num [Tolerance.Apart, Tolerance.distance, Tolerance.ofReport]

end Discernibility

/-! ## Coarsening of crisp observers is descent -/

section Coarsening

open Mettapedia.GSLT.Dynamics.MemoizationObserver (SoundKey)
open Mettapedia.GSLT.Core.NonFactorization (NonTrivialFiber)

variable {X : Type u} {K : Type v} {O : Type w}

/-- **Coarsening of crisp observers is descent.**  Every similarity of the
crisp observer of `key` is at most that of the crisp observer of `obs` exactly
when `obs` descends along `key`. -/
theorem ofReport_extends_iff_soundKey [DecidableEq K] [DecidableEq O] (key : X → K)
    (obs : X → O) :
    (Tolerance.ofReport key).Extends (Tolerance.ofReport obs) ↔ SoundKey key obs := by
  constructor
  · intro coarser x y sameKey
    by_contra different
    have bound := coarser x y
    simp [Tolerance.ofReport, sameKey, different] at bound
    exact absurd bound (by norm_num)
  · intro sound x y
    by_cases sameKey : key x = key y
    · simp [Tolerance.ofReport, sameKey, sound x y sameKey]
    · by_cases sameObs : obs x = obs y <;> simp [Tolerance.ofReport, sameKey, sameObs]

/-- **A non-trivial fibre refutes the coarsening.** -/
theorem not_ofReport_extends_of_fiber [DecidableEq K] [DecidableEq O] {key : X → K}
    {obs : X → O} (fiber : NonTrivialFiber key obs) :
    ¬ (Tolerance.ofReport key).Extends (Tolerance.ofReport obs) := fun coarser =>
  fiber.differentValue ((ofReport_extends_iff_soundKey key obs).1 coarser _ _ fiber.sameShadow)

end Coarsening

/-! ## Validated captured readings -/

section Captured

open Mettapedia.GSLT.Dynamics.CacheCoherence (ReadsDetermine readingKey soundKey_readingKey)

variable {Dep Reading Query Answer : Type} [DecidableEq Dep] [DecidableEq Reading]
  [DecidableEq Query] [DecidableEq Answer]

/-- **The observer of validated captured readings refines the authorized
answer**: the query with its consulted stores and their readings is a crisp
observer at least as fine as the authorized answer, when the readings determine
it. -/
theorem readingKey_extends_authorized
    {authorized : Mettapedia.Machines.RevisionEnvironment Dep Reading → Query → Answer}
    {consults : Mettapedia.Machines.RevisionEnvironment Dep Reading → Query → List Dep}
    (determines : ReadsDetermine authorized consults) :
    (Tolerance.ofReport (readingKey consults)).Extends
      (Tolerance.ofReport fun point => authorized point.1 point.2) :=
  (ofReport_extends_iff_soundKey _ _).2 (soundKey_readingKey determines)

end Captured

/-! ## Ordered observation against the answer bag -/

section Ordered

open Mettapedia.GSLT.Dynamics.OrderedDemand (Trace answerBag)
open Mettapedia.GSLT.Core.NonFactorization (NonTrivialFiber)

/-- **The ordered effect-aware observer refines the answer bag.** -/
theorem trace_extends_answerBag {A E F : Type} [DecidableEq A] [DecidableEq E] [DecidableEq F] :
    (Tolerance.ofReport (id : Trace A E F → Trace A E F)).Extends
      (Tolerance.ofReport (answerBag : Trace A E F → Multiset A)) :=
  (ofReport_extends_iff_soundKey _ _).2 fun _ _ same => congrArg answerBag same

/-- **The answer bag forgets order**: two runs with one answer bag and different
ordered traces. -/
def answerBag_forgets_order :
    NonTrivialFiber (answerBag : Trace ℕ Unit Unit → Multiset ℕ) id where
  left := [.answer 1, .answer 2]
  right := [.answer 2, .answer 1]
  sameShadow := Mettapedia.GSLT.Dynamics.OrderedDemand.Controls.reordering_control.1
  differentValue := Mettapedia.GSLT.Dynamics.OrderedDemand.Controls.reordering_control.2

/-- The answer bag is strictly coarser than the ordered trace. -/
theorem answerBag_not_extends_trace :
    ¬ (Tolerance.ofReport (answerBag : Trace ℕ Unit Unit → Multiset ℕ)).Extends
      (Tolerance.ofReport (id : Trace ℕ Unit Unit → Trace ℕ Unit Unit)) :=
  not_ofReport_extends_of_fiber answerBag_forgets_order

end Ordered

/-! ## Blocks against completion status -/

section Blocks

open Mettapedia.GSLT.Distinction.ProductiveBlocks.Controls
  (Wedge wedgeMachine blocks_cannot_separate wedge_observations)
open Mettapedia.GSLT.Core.NonFactorization (NonTrivialFiber)

/-- **The zero kernel of the block observer forgets completion status.**
Finishing and an infinite silent loop are bisimilar as blocks, so they have one
class in the quotient by block bisimilarity, while their status differs. -/
def blocks_forget_status :
    NonTrivialFiber (Quot.mk wedgeMachine.reading.blockSystem.Bisimilar)
      (fun state : Wedge => (wedgeMachine.observe 1 state).status) where
  left := .done
  right := .spinning
  sameShadow := Quot.sound (blocks_cannot_separate .done .spinning)
  differentValue := by
    rw [(wedge_observations 0).1, (wedge_observations 1).2.1]
    nofun

end Blocks

end Mettapedia.GSLT.Distinction.Dictionary
