import Mettapedia.GSLT.Causality.ResourceRuns

/-!
# Complementary guarded assays with linear messages

Each session installs two receivers, one for each Boolean guard, and accepts
one addressed message. Rule instances retain the authored receiver origin,
payload and guard evidence. The independently formed resource system consumes
the message and the selected receiver and emits a verdict carrying that data.

Theorems concern actual enabled instances and occurrence paths. Having an
enabled receiver does not assert that an unfinished schedule has fired it.
These are operational resource rules, without a claim of lowering a guarded
rho language or implementing an arbitrary predicate decider.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ComplementaryAssay

open ResourceInteraction
open OccurrenceHistory

universe u v

inductive Verdict where
  | confirm
  | refute
  deriving DecidableEq

def Verdict.bit : Verdict → Bool
  | .confirm => true
  | .refute => false

def Verdict.other : Verdict → Verdict
  | .confirm => .refute
  | .refute => .confirm

def verdictOf : Bool → Verdict
  | true => .confirm
  | false => .refute

@[simp] theorem verdictOf_bit (value : Bool) : (verdictOf value).bit = value := by
  cases value <;> rfl

theorem verdict_eq_of_bit {first second : Verdict} (same : first.bit = second.bit) :
    first = second := by
  cases first <;> cases second <;> simp_all [Verdict.bit]

inductive Resource (X : Type u) (Origins : Type v) where
  | message (session : Nat) (value : X)
  | receiver (session : Nat) (branch : Verdict) (origin : Origins)
  | result (session : Nat) (branch : Verdict) (origin : Origins) (value : X)
  deriving DecidableEq

structure Firing {X : Type u} (Origins : Type v) (test : X → Bool) (branch : Verdict) where
  session : Nat
  origin : Origins
  value : X
  guard : test value = branch.bit

variable {X : Type u} {Origins : Type v}

def system (test : X → Bool) : System.{max u v, max u v} (Resource X Origins) where
  Site := ULift.{max u v} Verdict
  Instance := fun branch => Firing Origins test branch.down
  consume := fun {branch} firing =>
    {Resource.message firing.session firing.value,
      Resource.receiver firing.session branch.down firing.origin}
  read := fun _ => 0
  produce := fun {branch} firing =>
    {Resource.result firing.session branch.down firing.origin firing.value}

def selected (test : X → Bool) (session : Nat) (origin : Origins) (value : X) :
    (system (Origins := Origins) test).Instance ⟨verdictOf (test value)⟩ :=
  ⟨session, origin, value, (verdictOf_bit _).symm⟩

def pending (session : Nat) (origin : Origins) : Multiset (Resource X Origins) :=
  {Resource.receiver session .confirm origin, Resource.receiver session .refute origin}

def ready (session : Nat) (origin : Origins) (value : X) : Multiset (Resource X Origins) :=
  {Resource.message session value} + pending session origin

def finished (test : X → Bool) (session : Nat) (origin : Origins) (value : X) :
    Multiset (Resource X Origins) :=
  {Resource.receiver session (verdictOf (test value)).other origin,
    Resource.result session (verdictOf (test value)) origin value}

theorem ready_split (test : X → Bool) (session : Nat) (origin : Origins) (value : X) :
    ready session origin value =
      {Resource.message session value, Resource.receiver session (verdictOf (test value)) origin} +
        {Resource.receiver session (verdictOf (test value)).other origin} := by
  cases verdictOf (test value) with
  | confirm =>
    simp only [ready, pending, Verdict.other, Multiset.insert_eq_cons, ← Multiset.singleton_add]
    rw [add_assoc]
  | refute =>
    simp only [ready, pending, Verdict.other, Multiset.insert_eq_cons, ← Multiset.singleton_add]
    rw [add_assoc, add_comm ({Resource.receiver session .refute origin} : Multiset (Resource X Origins))
      {Resource.receiver session .confirm origin}]

theorem branch_of_guard (test : X → Bool) {branch : Verdict}
    (firing : (system (Origins := Origins) test).Instance ⟨branch⟩) :
    branch = verdictOf (test firing.value) :=
  verdict_eq_of_bit (firing.guard.symm.trans (verdictOf_bit _).symm)

theorem selected_enabled (test : X → Bool) (session : Nat) (origin : Origins) (value : X) :
    (system test).Enables (ready session origin value) (selected test session origin value) := by
  change ({Resource.message session value,
    Resource.receiver session (verdictOf (test value)) origin} : Multiset (Resource X Origins)) + 0 ≤
      ready session origin value
  rw [add_zero, ready_split test]
  exact Multiset.le_add_right _ _

theorem enabled_fields (test : X → Bool) {session : Nat} {origin : Origins} {value : X}
    {branch : Verdict} (firing : (system test).Instance ⟨branch⟩)
    (enabled : (system test).Enables (ready session origin value) firing) :
    firing.session = session ∧ firing.origin = origin ∧ firing.value = value ∧
      branch = verdictOf (test value) := by
  have messagePresent : Resource.message firing.session firing.value ∈ ready session origin value :=
    Multiset.mem_of_le enabled (by simp [system])
  have messageSame : firing.session = session ∧ firing.value = value := by
    simpa [ready, pending] using messagePresent
  have receiverPresent : Resource.receiver firing.session branch firing.origin ∈
      ready session origin value :=
    Multiset.mem_of_le enabled (by simp [system])
  have receiverSame : firing.session = session ∧ firing.origin = origin := by
    cases branch <;> simpa [ready, pending] using receiverPresent
  exact ⟨messageSame.1, receiverSame.2, messageSame.2,
    (branch_of_guard test firing).trans (congrArg (fun x => verdictOf (test x)) messageSame.2)⟩

theorem no_pending_enabled (test : X → Bool) (session : Nat) (origin : Origins)
    {branch : Verdict} (firing : (system (X := X) test).Instance ⟨branch⟩) :
    ¬ (system test).Enables (pending session origin) firing := by
  intro enabled
  have present := Multiset.mem_of_le enabled
    (show Resource.message firing.session firing.value ∈
      (system test).consume firing + (system test).read firing by simp [system])
  simp [pending] at present

theorem no_finished_enabled (test : X → Bool) (session : Nat) (origin : Origins) (value : X)
    {branch : Verdict} (firing : (system test).Instance ⟨branch⟩) :
    ¬ (system test).Enables (finished test session origin value) firing := by
  intro enabled
  have present := Multiset.mem_of_le enabled
    (show Resource.message firing.session firing.value ∈
      (system test).consume firing + (system test).read firing by simp [system])
  simp [finished] at present

section DecidableResources

variable [DecidableEq X] [DecidableEq Origins]

theorem selected_fire (test : X → Bool) (session : Nat) (origin : Origins) (value : X) :
    (system test).fire (ready session origin value) (selected test session origin value) =
      finished test session origin value := by
  change ready session origin value -
    {Resource.message session value, Resource.receiver session (verdictOf (test value)) origin} +
      {Resource.result session (verdictOf (test value)) origin value} = _
  rw [ready_split test, add_tsub_cancel_left]
  rfl

theorem enabled_fire (test : X → Bool) {session : Nat} {origin : Origins} {value : X}
    {branch : Verdict} (firing : (system test).Instance ⟨branch⟩)
    (enabled : (system test).Enables (ready session origin value) firing) :
    (system test).fire (ready session origin value) firing =
      finished test session origin value := by
  obtain ⟨sameSession, sameOrigin, sameValue, sameBranch⟩ := enabled_fields test firing enabled
  cases firing with
  | mk firingSession firingOrigin firingValue guard =>
    simp only at sameSession sameOrigin sameValue
    subst firingSession
    subst firingOrigin
    subst firingValue
    subst branch
    exact selected_fire test session origin value

/-- The emitted data are read from resources, independently of firing selection. -/
def outputs (resources : Multiset (Resource X Origins)) :
    Multiset (Nat × Verdict × Origins × X) :=
  resources.filterMap fun resource => match resource with
    | .result session branch origin value => some (session, branch, origin, value)
    | _ => none

omit [DecidableEq X] [DecidableEq Origins] in
@[simp] theorem outputs_pending (session : Nat) (origin : Origins) :
    outputs (pending (X := X) session origin) = 0 := rfl

omit [DecidableEq X] [DecidableEq Origins] in
@[simp] theorem outputs_ready (session : Nat) (origin : Origins) (value : X) :
    outputs (ready session origin value) = 0 := rfl

omit [DecidableEq X] [DecidableEq Origins] in
@[simp] theorem outputs_finished (test : X → Bool) (session : Nat) (origin : Origins) (value : X) :
    outputs (finished test session origin value) =
      { (session, verdictOf (test value), origin, value) } := rfl

/-- A real firing, retaining its occurrence and the exact completed endpoint. -/
def run (test : X → Bool) (session : Nat) (origin : Origins) (value : X) :
    OccurrencePath (system test).presentation (ready session origin value)
      (finished test session origin value) :=
  .cons ⟨⟨verdictOf (test value)⟩,
    ⟨selected test session origin value, selected_enabled test session origin value,
      (selected_fire test session origin value).symm⟩⟩ (.refl _)

theorem run_entries (test : X → Bool) (session : Nat) (origin : Origins) (value : X) :
    (system test).pathEntries (run test session origin value) =
      [⟨⟨verdictOf (test value)⟩, selected test session origin value⟩] := rfl

end DecidableResources

end Mettapedia.GSLT.Causality.ComplementaryAssay
