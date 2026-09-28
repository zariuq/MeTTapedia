import Mettapedia.GSLT.Causality.EventConcurrency
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Tactic.Abel

/-!
# Interaction on a bag of resources: linear consumption and persistent reads

A rule instance consumes a bag of resources, reads a second bag without
consuming it, and adds a third. Rho's communication consumes an output and an
input. An equation in a MeTTa space is read by every call it answers, and the
call is consumed. The calculi differ in which resources are linear.

Two firings are concurrent when their consumptions fit together, each beside
the other's reads. Concurrent firings commute. A resource present once and
consumed by both firings puts them in conflict: after either, the other is
disabled. A read resource is shared, so firings that read it in common are
concurrent.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.GSLT.Causality.EventConcurrency

universe uRes uRule

/-- Rule instances over resources `R`: each consumes, reads and produces a bag. -/
structure System (R : Type uRes) where
  Site : Type uRule
  Instance : Site → Type uRule
  consume : ∀ {site : Site}, Instance site → Multiset R
  read : ∀ {site : Site}, Instance site → Multiset R
  produce : ∀ {site : Site}, Instance site → Multiset R

namespace System

variable {R : Type uRes} (S : System.{uRes, uRule} R)

/-- An instance is enabled when its consumption and its reads are both present. -/
def Enables (M : Multiset R) {site : S.Site} (i : S.Instance site) : Prop :=
  S.consume i + S.read i ≤ M

/-- Both consumptions fit together in the bag, each beside either read. -/
def Concurrent (M : Multiset R) {site₁ site₂ : S.Site} (i : S.Instance site₁)
    (j : S.Instance site₂) : Prop :=
  S.consume i + S.consume j + S.read i ≤ M ∧ S.consume i + S.consume j + S.read j ≤ M

theorem concurrent_symm {M : Multiset R} {site₁ site₂ : S.Site} {i : S.Instance site₁}
    {j : S.Instance site₂} (h : S.Concurrent M i j) : S.Concurrent M j i := by
  obtain ⟨hi, hj⟩ := h
  refine ⟨?_, ?_⟩
  · rw [add_comm (S.consume j)]
    exact hj
  · rw [add_comm (S.consume j)]
    exact hi

/-- **A read resource is shared.** Instances whose consumptions fit together
beside one bag of reads are concurrent, however much of it they both read. -/
theorem concurrent_of_shared_read (M : Multiset R) {site₁ site₂ : S.Site}
    (i : S.Instance site₁) (j : S.Instance site₂) (reads : Multiset R)
    (readI : S.read i ≤ reads) (readJ : S.read j ≤ reads)
    (fits : S.consume i + S.consume j + reads ≤ M) : S.Concurrent M i j :=
  ⟨le_trans (add_le_add le_rfl readI) fits, le_trans (add_le_add le_rfl readJ) fits⟩

variable [DecidableEq R]

/-- Firing removes the consumption and adds the production; reads remain. -/
def fire (M : Multiset R) {site : S.Site} (i : S.Instance site) : Multiset R :=
  M - S.consume i + S.produce i

/-- The rewrite theory of a resource system: configurations are bags. -/
def theory : GSLT where
  Term := Multiset R
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := fun M N => ∃ site, ∃ i : S.Instance site, S.Enables M i ∧ N = S.fire M i
  rewrites_resp_left := by
    intro M M' N equal step
    exact ⟨N, equal ▸ step, rfl⟩
  rewrites_resp_right := by
    intro M N N' step equal
    exact equal ▸ step

/-- Events are enabled instances, one site per rule. -/
def presentation : InteractionPresentation S.theory where
  Site := S.Site
  Event := fun site M N => {i : S.Instance site // S.Enables M i ∧ N = S.fire M i}
  sound := fun {site} _ _ event => ⟨site, event.val, event.property.1, event.property.2⟩

/-- The instance an enabled event fires. -/
def inst {M : Multiset R} (e : S.presentation.Enabled M) : S.Instance e.site :=
  e.evidence.val

theorem enables_inst {M : Multiset R} (e : S.presentation.Enabled M) :
    S.Enables M (S.inst e) :=
  e.evidence.property.1

theorem target_inst {M : Multiset R} (e : S.presentation.Enabled M) :
    e.target = S.fire M (S.inst e) :=
  e.evidence.property.2

/-- The event firing an enabled instance. -/
def event (M : Multiset R) {site : S.Site} (i : S.Instance site) (enabled : S.Enables M i) :
    S.presentation.Enabled M where
  site := site
  target := S.fire M i
  evidence := ⟨i, enabled, rfl⟩

/-! ## Concurrency -/

/-- After one of two concurrent instances fires, the other is still enabled. -/
theorem enables_fire {M : Multiset R} {site₁ site₂ : S.Site} {i : S.Instance site₁}
    {j : S.Instance site₂} (h : S.Concurrent M i j) : S.Enables (S.fire M i) j := by
  have fits : S.consume j + S.read j ≤ M - S.consume i := by
    apply le_tsub_of_add_le_left
    rw [← add_assoc]
    exact h.2
  exact le_trans fits (Multiset.le_add_right _ _)

/-- Firing two concurrent instances in either order reaches one bag. -/
theorem fire_comm {M : Multiset R} {site₁ site₂ : S.Site} {i : S.Instance site₁}
    {j : S.Instance site₂} (h : S.Concurrent M i j) :
    S.fire (S.fire M i) j = S.fire (S.fire M j) i := by
  have both : S.consume i + S.consume j ≤ M :=
    le_trans (Multiset.le_add_right _ _) h.1
  have ji : S.consume j ≤ M - S.consume i := le_tsub_of_add_le_left both
  have ij : S.consume i ≤ M - S.consume j := by
    apply le_tsub_of_add_le_left
    rw [add_comm]
    exact both
  unfold fire
  rw [← tsub_add_eq_add_tsub ji, ← tsub_add_eq_add_tsub ij, tsub_tsub, tsub_tsub,
    add_comm (S.consume j) (S.consume i)]
  exact add_right_comm _ _ _

/-- **Concurrent firings are independent events.** The residual of either is the
same instance, and the two orders meet. -/
def concurrency : Concurrency S.presentation where
  Independent := fun {M} a b => S.Concurrent M (S.inst a) (S.inst b)
  symm := fun h => S.concurrent_symm h
  residual := fun {_} {a} {b} h =>
    S.event a.target (S.inst b) (by rw [S.target_inst a]; exact S.enables_fire h)
  residual_site := fun _ => rfl
  close := by
    intro M a b h
    change S.fire a.target (S.inst b) = S.fire b.target (S.inst a)
    rw [S.target_inst a, S.target_inst b]
    exact S.fire_comm h

/-! ## Conflict and sharing -/

/-- **A linear resource present once is a conflict.** Two instances that both
consume it are not concurrent. -/
theorem not_concurrent_of_shared_consumption (M : Multiset R) {site₁ site₂ : S.Site}
    (i : S.Instance site₁) (j : S.Instance site₂) (r : R) (inI : r ∈ S.consume i)
    (inJ : r ∈ S.consume j) (once : M.count r ≤ 1) : ¬ S.Concurrent M i j := by
  intro h
  have fits := Multiset.count_le_of_le r (le_trans (Multiset.le_add_right _ _) h.1)
  rw [Multiset.count_add] at fits
  have countI := Multiset.count_pos.mpr inI
  have countJ := Multiset.count_pos.mpr inJ
  omega

/-- **After either conflicting firing, the other is disabled**, unless the first
puts the resource back. -/
theorem disabled_after (M : Multiset R) {site₁ site₂ : S.Site} (i : S.Instance site₁)
    (j : S.Instance site₂) (r : R) (inI : r ∈ S.consume i) (inJ : r ∈ S.consume j)
    (once : M.count r ≤ 1) (notBack : r ∉ S.produce i) :
    ¬ S.Enables (S.fire M i) j := by
  intro h
  have fits := Multiset.count_le_of_le r (le_trans (Multiset.le_add_right _ _) h)
  rw [fire, Multiset.count_add, Multiset.count_sub, Multiset.count_eq_zero.mpr notBack]
    at fits
  have countI := Multiset.count_pos.mpr inI
  have countJ := Multiset.count_pos.mpr inJ
  omega

end System

/-! ## Controls: a rho receiver and a MeTTa space

A rho input is consumed by the message it takes. Two messages on one channel,
with one input, are in conflict: a run takes one of them. A replicated input
is read instead, and both messages are taken.

An equation of a MeTTa space is read by the call it answers, and the call is
consumed. Two equations for one call are conflicting alternatives: each run
takes one, and an all-answer search collects both. Two calls answered by one
equation are concurrent: they are two firings of one rule instance. -/

namespace Controls

/-- Messages on one channel, a receiver, and received values. -/
inductive Res where
  | message (value : ℕ)
  | receiver
  | received (value : ℕ)
  deriving DecidableEq

/-- An input consumed by the message it takes. -/
def linearReceiver : System Res where
  Site := Unit
  Instance := fun _ => ℕ
  consume := fun value => {Res.message value, Res.receiver}
  read := fun _ => 0
  produce := fun value => {Res.received value}

/-- A replicated input: read by every message it takes. -/
def persistentReceiver : System Res where
  Site := Unit
  Instance := fun _ => ℕ
  consume := fun value => {Res.message value}
  read := fun _ => {Res.receiver}
  produce := fun value => {Res.received value}

/-- Two messages and one receiver. -/
def twoMessages : Multiset Res := {Res.message 1, Res.message 2, Res.receiver}

/-- Taking message `value`. -/
def take (value : ℕ) : linearReceiver.Instance () := value

/-- Taking message `value` with the replicated input. -/
def takeAgain (value : ℕ) : persistentReceiver.Instance () := value

/-- **One input, two messages: a conflict.** -/
theorem linear_receiver_conflict : ¬ linearReceiver.Concurrent twoMessages (take 1) (take 2) :=
  linearReceiver.not_concurrent_of_shared_consumption twoMessages (take 1) (take 2) Res.receiver
    (by decide) (by decide) (by decide)

/-- **After one message is taken, the other cannot be.** -/
theorem linear_receiver_takes_one :
    linearReceiver.Enables twoMessages (take 1) ∧
      ¬ linearReceiver.Enables (linearReceiver.fire twoMessages (take 1)) (take 2) :=
  ⟨by unfold System.Enables; decide,
    linearReceiver.disabled_after twoMessages (take 1) (take 2) Res.receiver
      (by decide) (by decide) (by decide) (by decide)⟩

/-- **A replicated input takes both messages, in either order.** -/
theorem persistent_receiver_concurrent :
    persistentReceiver.Concurrent twoMessages (takeAgain 1) (takeAgain 2) :=
  persistentReceiver.concurrent_of_shared_read twoMessages (takeAgain 1) (takeAgain 2)
    {Res.receiver} le_rfl le_rfl (by decide)

/-- Calls, equations and answers of a space. -/
inductive SpaceRes where
  | call
  | equation (index : ℕ)
  | answer (index : ℕ)
  deriving DecidableEq

/-- Equation `index` answers the call. The equation is read; the call is
consumed. -/
def space : System SpaceRes where
  Site := Unit
  Instance := fun _ => ℕ
  consume := fun _ => {SpaceRes.call}
  read := fun index => {SpaceRes.equation index}
  produce := fun index => {SpaceRes.answer index}

/-- Answer the call by equation `index`. -/
def answerBy (index : ℕ) : space.Instance () := index

/-- One call and two equations for it. -/
def oneCallTwoEquations : Multiset SpaceRes :=
  {SpaceRes.call, SpaceRes.equation 1, SpaceRes.equation 2}

/-- Two calls and one equation. -/
def twoCallsOneEquation : Multiset SpaceRes :=
  {SpaceRes.call, SpaceRes.call, SpaceRes.equation 1}

/-- **Two equations for one call are alternatives.** Each run answers by one;
the other is then disabled. -/
theorem equations_are_alternatives :
    ¬ space.Concurrent oneCallTwoEquations (answerBy 1) (answerBy 2) ∧
      ¬ space.Enables (space.fire oneCallTwoEquations (answerBy 1)) (answerBy 2) :=
  ⟨space.not_concurrent_of_shared_consumption oneCallTwoEquations (answerBy 1) (answerBy 2)
      SpaceRes.call (by decide) (by decide) (by decide),
    space.disabled_after oneCallTwoEquations (answerBy 1) (answerBy 2) SpaceRes.call
      (by decide) (by decide) (by decide) (by decide)⟩

/-- **Two calls share one equation.** The same rule instance fires twice,
concurrently. -/
theorem calls_share_equation :
    space.Concurrent twoCallsOneEquation (answerBy 1) (answerBy 1) :=
  space.concurrent_of_shared_read twoCallsOneEquation (answerBy 1) (answerBy 1)
    {SpaceRes.equation 1} le_rfl le_rfl (by decide)

/-- The two answers of the shared equation are one trace. -/
def sharedPair : space.concurrency.Pair twoCallsOneEquation where
  first := space.event twoCallsOneEquation (answerBy 1) (by unfold System.Enables; decide)
  second := space.event twoCallsOneEquation (answerBy 1) (by unfold System.Enables; decide)
  independent := calls_share_equation

theorem shared_answers_commute :
    Trace.mk (T := space.concurrency.tiles) (sharedPair.route space.concurrency) =
      Trace.mk (sharedPair.swapped space.concurrency) :=
  Trace.mk_sound (.tile (T := space.concurrency.tiles) sharedPair)

end Controls

#print axioms System.fire_comm
#print axioms System.not_concurrent_of_shared_consumption
#print axioms System.disabled_after
#print axioms Controls.linear_receiver_takes_one
#print axioms Controls.persistent_receiver_concurrent
#print axioms Controls.equations_are_alternatives
#print axioms Controls.shared_answers_commute

end Mettapedia.GSLT.Causality.ResourceInteraction
