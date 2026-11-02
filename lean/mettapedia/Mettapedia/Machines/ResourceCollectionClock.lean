import Mathlib.Tactic

/-!
# An operation-paced clock for retained resource roots

The clock measures explicitly classified resource-root charges, not all arena
metadata and not the transitive physical heap. A full collection resets its
threshold to `max floor (2 * survivors)`. Other collections may happen earlier;
an unrelated syntax-only decline does not reset this clock.

The transition permits releases as well as allocation. Its input charge can
grow by at most the operation's charged allocation. Collection must preserve
the required owners, an obligation separate from this scheduling model.

`run_bounds` and `prepoll_bound` give bounds independent of execution length,
assuming a uniform bound on measured survivors and on charged allocation
between polls. An optional typed-survival-certified decline has a fourfold
local wait bound. The native initial policy need not implement this extension.

A physical-memory bound additionally needs a bound on the resource graph
protected by those roots. Mixed syntax copying needs its own work account.
The negative controls show why neither follows from the root clock alone.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ResourceCollectionClock

open scoped BigOperators

def threshold (floor survivors : Nat) : Nat := max floor (2 * survivors)

structure Clock where
  resources : Nat
  nextAt : Nat
  deriving DecidableEq, Repr

def afterCollection (floor survivors : Nat) : Clock :=
  ⟨survivors, threshold floor survivors⟩

/-- An operation may release existing owners. Its retained charge can increase
by at most the charged allocation made before the next poll. -/
abbrev Change (allocation : Nat) := (previous : Nat) → Fin (previous + allocation + 1)

/-- A full collection cannot retain more root charge than was available. -/
abbrev Observe := (available : Nat) → Fin (available + 1)

def advance (floor allocation : Nat) (change : Change allocation)
    (observe : Observe) (forced : Bool) (state : Clock) : Clock :=
  let available := (change state.resources).val
  if forced = true ∨ state.nextAt ≤ available then
    afterCollection floor (observe available).val
  else
    { state with resources := available }

def run (floor initial : Nat) (allocation : Nat → Nat)
    (change : (t : Nat) → Change (allocation t)) (observe : Nat → Observe)
    (forced : Nat → Bool) : Nat → Clock
  | 0 => afterCollection floor initial
  | t + 1 => advance floor (allocation t) (change t) (observe t) (forced t)
      (run floor initial allocation change observe forced t)

theorem threshold_mono (floor : Nat) {left right : Nat} (included : left ≤ right) :
    threshold floor left ≤ threshold floor right := by
  exact max_le_max (le_refl _) (by omega)

/-- Reaching the doubled survivor threshold pays a scan of the charged
resource roots from new retained charges, even if some old roots were
released. `newCharges` counts acquisitions since the previous full collection. -/
theorem resource_scan_paid (floor survivors current newCharges : Nat)
    (due : threshold floor survivors ≤ current)
    (growth : current ≤ survivors + newCharges) : current ≤ 2 * newCharges := by
  dsimp only [threshold] at due
  have doubled := le_max_right floor (2 * survivors)
  omega

/-- This pays only the resource part. An unrelated syntax traversal remains
an explicit additive cost and cannot be erased from the account. -/
theorem mixed_scan_account (floor survivors current newCharges syntaxWork unitCost work : Nat)
    (due : threshold floor survivors ≤ current)
    (growth : current ≤ survivors + newCharges)
    (cost : work ≤ syntaxWork + unitCost * current) :
    work ≤ syntaxWork + 2 * unitCost * newCharges := by
  have paid := resource_scan_paid floor survivors current newCharges due growth
  nlinarith

theorem afterCollection_bounds (floor bound survivors : Nat) (positive : 0 < floor)
    (bounded : survivors ≤ bound) :
    (afterCollection floor survivors).resources < threshold floor bound ∧
      (afterCollection floor survivors).nextAt ≤ threshold floor bound := by
  have floorLe := le_max_left floor (2 * bound)
  have twiceLe := le_max_right floor (2 * bound)
  exact ⟨by dsimp [afterCollection, threshold]; omega, threshold_mono floor bounded⟩

theorem advance_bounds (floor bound allocation : Nat) (positive : 0 < floor)
    (change : Change allocation) (observe : Observe) (forced : Bool) (state : Clock)
    (thresholdBound : state.nextAt ≤ threshold floor bound)
    (survivorsBound : ∀ available, (observe available).val ≤ bound) :
    (advance floor allocation change observe forced state).resources < threshold floor bound ∧
      (advance floor allocation change observe forced state).nextAt ≤ threshold floor bound := by
  dsimp only [advance]
  split_ifs with due
  · exact afterCollection_bounds floor bound _ positive (survivorsBound _)
  · have before := not_or.mp due
    exact ⟨by dsimp; omega, thresholdBound⟩

/-- Post-poll root retention and the next threshold are uniformly bounded,
even when the loop runs forever or syntax collections are interleaved. -/
theorem run_bounds (floor bound initial : Nat) (positive : 0 < floor)
    (initialBound : initial ≤ bound) (allocation : Nat → Nat)
    (change : (t : Nat) → Change (allocation t)) (observe : Nat → Observe)
    (forced : Nat → Bool)
    (survivorsBound : ∀ t available, (observe t available).val ≤ bound) (t : Nat) :
    (run floor initial allocation change observe forced t).resources < threshold floor bound ∧
      (run floor initial allocation change observe forced t).nextAt ≤ threshold floor bound := by
  induction t with
  | zero => exact afterCollection_bounds floor bound initial positive initialBound
  | succ t ih =>
      exact advance_bounds floor bound (allocation t) positive (change t) (observe t)
        (forced t) _ ih.2 (survivorsBound t)

/-- A poll need not interrupt an allocation. The largest charge made between
polls is therefore an additive term in the instantaneous retention bound. -/
theorem prepoll_bound (floor bound initial burst : Nat) (positive : 0 < floor)
    (initialBound : initial ≤ bound) (allocation : Nat → Nat)
    (change : (t : Nat) → Change (allocation t)) (observe : Nat → Observe)
    (forced : Nat → Bool)
    (survivorsBound : ∀ t available, (observe t available).val ≤ bound)
    (burstBound : ∀ t, allocation t ≤ burst) (t : Nat) :
    (change t (run floor initial allocation change observe forced t).resources).val <
      threshold floor bound + burst := by
  have retained := (run_bounds floor bound initial positive initialBound allocation change
    observe forced survivorsBound t).1
  have growth := (change t (run floor initial allocation change observe forced t).resources).isLt
  have allocationBound := burstBound t
  omega

inductive DeclineScale where
  | twice
  | fourfold
  deriving DecidableEq, Repr

def DeclineScale.factor : DeclineScale → Nat
  | .twice => 2
  | .fourfold => 4

def declineThreshold (floor sampledCharge : Nat) (scale : DeclineScale) : Nat :=
  max floor (scale.factor * sampledCharge)

theorem decline_local_bound (floor sampledCharge : Nat) (scale : DeclineScale) :
    declineThreshold floor sampledCharge scale ≤ max floor (4 * sampledCharge) := by
  cases scale <;> dsimp [declineThreshold, DeclineScale.factor] <;> omega

/-- A decline based on typed-resource survival can be bounded by the same
typed survivor account. Mixed syntax survival supplies no such certificate. -/
theorem certified_decline_bound (floor sampledCharge survivors : Nat)
    (scale : DeclineScale) (highSurvival : 3 * sampledCharge ≤ 4 * survivors) :
    declineThreshold floor sampledCharge scale ≤ max floor (8 * survivors) := by
  have sampledBound : sampledCharge ≤ 2 * survivors := by omega
  exact (decline_local_bound floor sampledCharge scale).trans
    (max_le_max (le_refl _) (by omega))

section ResourceGraph

variable {Owner Resource : Type*} [DecidableEq Owner] [DecidableEq Resource]

def rootCharge (owners : Finset Owner) (charge : Owner → Nat) : Nat :=
  ∑ owner ∈ owners, charge owner

/-- `footprint owner` is the finite transitive set protected by that owner.
Shared resources contribute once to physical retention. -/
def physicalCost (owners : Finset Owner) (footprint : Owner → Finset Resource)
    (bytes : Resource → Nat) : Nat :=
  ∑ resource ∈ owners.biUnion footprint, bytes resource

private theorem weighted_union_le (left right : Finset Resource) (bytes : Resource → Nat) :
    (∑ resource ∈ left ∪ right, bytes resource) ≤
      (∑ resource ∈ left, bytes resource) + ∑ resource ∈ right, bytes resource := by
  have equality := Finset.sum_union_inter (s₁ := left) (s₂ := right) (f := bytes)
  omega

theorem physicalCost_le_owner_sum (owners : Finset Owner)
    (footprint : Owner → Finset Resource) (bytes : Resource → Nat) :
    physicalCost owners footprint bytes ≤
      ∑ owner ∈ owners, ∑ resource ∈ footprint owner, bytes resource := by
  induction owners using Finset.induction_on with
  | empty => simp [physicalCost]
  | @insert owner owners absent ih =>
      simp only [physicalCost, Finset.biUnion_insert, Finset.sum_insert absent]
      exact (weighted_union_le _ _ bytes).trans (Nat.add_le_add_left ih _)

/-- A root-charge bound becomes a physical-memory bound only after each
owner's protected graph is bounded in terms of its charge. This permits
overlap; charging overlapping graphs twice remains a safe overestimate. -/
theorem physical_amplification_bound (owners : Finset Owner)
    (footprint : Owner → Finset Resource) (bytes : Resource → Nat)
    (charge : Owner → Nat) (amplification : Nat)
    (covered : ∀ owner ∈ owners,
      (∑ resource ∈ footprint owner, bytes resource) ≤ amplification * charge owner) :
    physicalCost owners footprint bytes ≤ amplification * rootCharge owners charge := by
  calc
    physicalCost owners footprint bytes ≤
        ∑ owner ∈ owners, ∑ resource ∈ footprint owner, bytes resource :=
      physicalCost_le_owner_sum owners footprint bytes
    _ ≤ ∑ owner ∈ owners, amplification * charge owner := Finset.sum_le_sum covered
    _ = amplification * rootCharge owners charge := by
      simp only [rootCharge, Finset.mul_sum]

end ResourceGraph

namespace Controls

def appendCharge (allocation : Nat) : Change allocation :=
  fun previous => ⟨previous + allocation, by omega⟩

def emptyAfter : Observe := fun _ => ⟨0, by omega⟩

example : (run 4 0 (fun _ => 1) (fun _ => appendCharge 1)
    (fun _ => emptyAfter) (fun _ => false) 12).resources = 0 := by decide

example : (run 4 0 (fun _ => 1) (fun _ => appendCharge 1)
    (fun _ => emptyAfter) (fun t => decide (t % 2 = 1)) 11).resources = 1 := by decide

/-- One indivisible allocation can exceed the threshold before its poll. -/
example : (appendCharge 100 0).val > threshold 4 0 := by decide

/-- A mixed generation may pass a three-quarter live-byte test while its
resource part is all garbage and arbitrarily exceeds a chosen bound. -/
theorem mixed_survival_does_not_bound_resources (bound : Nat) :
    ∃ syntaxBytes resources : Nat,
      3 * (syntaxBytes + resources) ≤ 4 * syntaxBytes ∧ bound < resources := by
  refine ⟨4 * (bound + 1), bound + 1, ?_, ?_⟩ <;> omega

/-- Copying a mixed generation cannot have a uniform cost ratio to its
typed-resource charge without separately accounting for live syntax. -/
theorem mixed_copy_not_paid_by_resource_charge (factor : Nat) :
    ∃ syntaxBytes : Nat, factor * 2 < syntaxBytes + 2 := by
  exact ⟨2 * factor + 1, by omega⟩

/-- Distinct roots can share one physical resource. -/
example : physicalCost ({false, true} : Finset Bool)
      (fun _ => ({0} : Finset Nat)) (fun _ => 7) = 7 ∧
    rootCharge ({false, true} : Finset Bool) (fun _ => 4) = 8 := by decide

/-- One small root can retain an arbitrarily wide graph. No universal
physical amplification constant follows from its charge alone. -/
theorem one_root_unbounded_graph (bound : Nat) :
    ∃ footprint : Unit → Finset Nat,
      bound * rootCharge ({()} : Finset Unit) (fun _ => 1) <
        physicalCost {()} footprint (fun _ => 1) := by
  refine ⟨fun _ => Finset.range (bound + 1), ?_⟩
  simp [rootCharge, physicalCost]

end Controls

#print axioms run_bounds
#print axioms prepoll_bound
#print axioms resource_scan_paid
#print axioms certified_decline_bound
#print axioms physical_amplification_bound

end Mettapedia.Machines.ResourceCollectionClock
