import Mettapedia.Machines.CollectionOfferScheduling

/-!
# Collection policy through an early due gate

The source policy requests collection at every eligible visit in eager mode;
otherwise it uses the existing growth/release or counting-candidate thresholds.
The target installs zero thresholds for eager universes, so callers can keep
their existing cheap due predicate. Both that caller gate and the safe-point
collector's gate agree with the source policy, while off mode and unsafe scopes win.

The trace join uses the maintained interleaved-owner scheduling algorithm.
Heap roots, finite native counters, concrete scope tracking and collector
correctness remain separate obligations. The ordinary production floor is
parameterized and is not changed by this result.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CollectionTriggerPolicy

inductive Mode where
  | off | shadow | reclaim
  deriving DecidableEq, Repr

structure Policy where
  mode : Mode
  eager : Bool
  counting : Bool
  live : Nat
  roots : Nat
  backoff : Nat
  growthFloor : Nat
  countingFloor : Nat
  releaseFloor : Nat
  deriving DecidableEq, Repr

structure Work where
  growth : Nat
  released : Nat
  zeroCount : Nat
  deriving DecidableEq, Repr

def countingThreshold (policy : Policy) : Nat :=
  max (max (max policy.countingFloor (policy.roots * 2)) (policy.live / 64)) policy.backoff

def normalDue (policy : Policy) (work : Work) : Bool :=
  if policy.counting then decide (countingThreshold policy ≤ work.growth + work.zeroCount)
  else decide (max policy.live policy.growthFloor ≤ work.growth) ||
    decide (max (policy.live / 8) policy.releaseFloor ≤ work.released)

def required (policy : Policy) (work : Work) : Bool :=
  policy.mode != .off && (policy.eager || normalDue policy work)

structure Thresholds where
  made : Nat
  released : Option Nat
  deriving DecidableEq, Repr

def install (policy : Policy) : Thresholds :=
  if policy.eager then ⟨0, some 0⟩
  else if policy.counting then ⟨countingThreshold policy, none⟩
  else ⟨max policy.live policy.growthFloor, some (max (policy.live / 8) policy.releaseFloor)⟩

def earlyDue (policy : Policy) (work : Work) : Bool :=
  let thresholds := install policy
  if policy.mode = .off then false
  else if policy.counting then decide (thresholds.made ≤ work.growth + work.zeroCount)
  else decide (thresholds.made ≤ work.growth) ||
    thresholds.released.any fun limit => decide (limit ≤ work.released)

theorem early_due_refines (policy : Policy) (work : Work) :
    earlyDue policy work = required policy work := by
  cases mode : policy.mode <;> cases eager : policy.eager <;>
    cases counting : policy.counting <;>
    simp [earlyDue, required, install, normalDue, mode, eager, counting]

theorem eager_thresholds_zero (policy : Policy) (eager : policy.eager = true) :
    install policy = ⟨0, some 0⟩ := by simp [install, eager]

theorem off_not_due (policy : Policy) (work : Work) (off : policy.mode = .off) :
    earlyDue policy work = false := by simp [earlyDue, off]

theorem eager_due (policy : Policy) (work : Work)
    (enabled : policy.mode ≠ .off) (eager : policy.eager = true) :
    earlyDue policy work = true := by
  rw [early_due_refines]
  simp [required, enabled, eager]

theorem ordinary_due_unchanged (policy : Policy) (work : Work)
    (enabled : policy.mode ≠ .off) (ordinary : policy.eager = false) :
    earlyDue policy work = normalDue policy work := by
  rw [early_due_refines]
  simp [required, enabled, ordinary]

/-- Safe-point collector entry retains off-mode priority. -/
def collectorGate (policy : Policy) (work : Work) : Bool :=
  policy.mode != .off && (policy.eager || earlyDue policy work)

theorem collector_gate_refines (policy : Policy) (work : Work) :
    collectorGate policy work = required policy work := by
  rw [collectorGate, early_due_refines]
  cases mode : policy.mode <;> cases eager : policy.eager <;>
    simp [required, mode, eager]

def targetOffer (policy : Policy) (work : Work) (safe quiescent inhibited : Bool) : Bool :=
  safe && quiescent && !inhibited && earlyDue policy work && collectorGate policy work

def sourceOffer (policy : Policy) (work : Work) (safe quiescent inhibited : Bool) : Bool :=
  safe && quiescent && !inhibited && required policy work

theorem two_stage_offer_refines (policy : Policy) (work : Work)
    (safe quiescent inhibited : Bool) :
    targetOffer policy work safe quiescent inhibited = sourceOffer policy work safe quiescent inhibited := by
  rw [targetOffer, sourceOffer, early_due_refines, collector_gate_refines]
  cases safe <;> cases quiescent <;> cases inhibited <;>
    cases required policy work <;> rfl

theorem inhibited_omits (policy : Policy) (work : Work) (safe quiescent : Bool) :
    targetOffer policy work safe quiescent true = false := by
  simp [targetOffer]

theorem unsafe_omits (policy : Policy) (work : Work) (quiescent inhibited : Bool) :
    targetOffer policy work false quiescent inhibited = false := by
  rfl

theorem active_scope_omits (policy : Policy) (work : Work) (safe inhibited : Bool) :
    targetOffer policy work safe false inhibited = false := by
  simp [targetOffer]

structure Visit (Owner : Type) where
  owner : Owner
  policy : Policy
  work : Work
  safe : Bool
  quiescent : Bool
  inhibited : Bool
  sourcePermitted : Bool

def lower {Owner : Type} (visit : Visit Owner) : CollectionOfferScheduling.Visit Owner :=
  ⟨visit.owner, visit.safe, visit.quiescent && !visit.inhibited,
    earlyDue visit.policy visit.work && collectorGate visit.policy visit.work,
    visit.sourcePermitted⟩

def reference {Owner : Type} (visits : List (Visit Owner)) : List Owner :=
  visits.filterMap fun visit =>
    if sourceOffer visit.policy visit.work visit.safe visit.quiescent visit.inhibited then some visit.owner else none

theorem lowered_visit_exact {Owner : Type} (visit : Visit Owner) :
    CollectionOfferScheduling.eligible (lower visit) =
      sourceOffer visit.policy visit.work visit.safe visit.quiescent visit.inhibited := by
  rw [← two_stage_offer_refines]
  simp [CollectionOfferScheduling.eligible, lower, targetOffer, Bool.and_assoc]

theorem trace_refines {Owner : Type} (visits : List (Visit Owner)) :
    CollectionOfferScheduling.offers (visits.map lower) = reference visits := by
  rw [CollectionOfferScheduling.offers_exact]
  simp only [CollectionOfferScheduling.reference, List.filterMap_map,
    Function.comp_def, reference]
  congr 1
  funext visit
  rw [lowered_visit_exact]
  rfl

namespace Controls

def tiny : Policy := ⟨.reclaim, true, false, 4, 0, 0, 65536, 4096, 4096⟩
def noGrowth : Work := ⟨0, 0, 0⟩

theorem tiny_eager_reaches_collection :
    targetOffer tiny noGrowth true true false = true := by decide

/-- Bypassing only the inner gate cannot repair a false caller gate. -/
theorem legacy_small_threshold_filters_eager :
    (decide ((64 : Nat) ≤ noGrowth.growth) || decide ((16 : Nat) ≤ noGrowth.released)) = false ∧
      collectorGate tiny noGrowth = true := by decide

theorem disabling_still_wins :
    targetOffer {tiny with mode := .off} noGrowth true true false = false := by decide

end Controls

end Mettapedia.Machines.CollectionTriggerPolicy
