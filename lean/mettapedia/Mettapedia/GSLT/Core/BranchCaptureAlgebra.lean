import Mettapedia.GSLT.Core.WeightedOccurrenceControl

/-!
# Algebraic admission for branch capture

Semantic expansion may authorize alternatives independently of how a runtime
stores them.  This file classifies only the physical capture required by a
frontier realization:

* `inlineOnly` keeps execution in the current dynamic extent;
* `oneShot` permits an exclusive choice point that is consumed on resume;
* `multiShot` permits owned branch images that may coexist in a portable
  frontier.

A branch image contains several state components.  Components compose by
their weakest capture capacity, so adding an effect can never make a branch
more portable.  A controller request that is not admitted is refused
explicitly.  Storage admission never substitutes another controller or
traversal policy.

Scheduling priority remains orthogonal.  KBO, an authored valuation, or a
learned ranker may order work inside any admitted storage realization without
changing the capture capacity itself.
-/

namespace Mettapedia.GSLT.Core.BranchCaptureAlgebra

/-- Maximum physical capture supported by one component of branch state. -/
inductive CaptureCapacity where
  | inlineOnly
  | oneShot
  | multiShot
deriving DecidableEq, Repr

namespace CaptureCapacity

/-- Numeric presentation of the capture-strength chain. -/
def rank : CaptureCapacity → Nat
  | .inlineOnly => 0
  | .oneShot => 1
  | .multiShot => 2

/-- One capacity admits another exactly when it is at least as strong. -/
def Admits (available required : CaptureCapacity) : Prop :=
  required.rank ≤ available.rank

instance (available required : CaptureCapacity) :
    Decidable (available.Admits required) := by
  unfold Admits
  infer_instance

/-- Composition of branch-state components is governed by the weakest one. -/
def weakest : CaptureCapacity → CaptureCapacity → CaptureCapacity
  | .inlineOnly, _ => .inlineOnly
  | _, .inlineOnly => .inlineOnly
  | .oneShot, _ => .oneShot
  | _, .oneShot => .oneShot
  | .multiShot, .multiShot => .multiShot

@[simp] theorem weakest_inlineOnly_left (capacity : CaptureCapacity) :
    weakest .inlineOnly capacity = .inlineOnly := by
  cases capacity <;> rfl

@[simp] theorem weakest_inlineOnly_right (capacity : CaptureCapacity) :
    weakest capacity .inlineOnly = .inlineOnly := by
  cases capacity <;> rfl

@[simp] theorem weakest_multiShot_left (capacity : CaptureCapacity) :
    weakest .multiShot capacity = capacity := by
  cases capacity <;> rfl

@[simp] theorem weakest_multiShot_right (capacity : CaptureCapacity) :
    weakest capacity .multiShot = capacity := by
  cases capacity <;> rfl

theorem weakest_comm (first second : CaptureCapacity) :
    weakest first second = weakest second first := by
  cases first <;> cases second <;> rfl

theorem weakest_assoc (first second third : CaptureCapacity) :
    weakest (weakest first second) third =
      weakest first (weakest second third) := by
  cases first <;> cases second <;> cases third <;> rfl

theorem weakest_idem (capacity : CaptureCapacity) :
    weakest capacity capacity = capacity := by
  cases capacity <;> rfl

theorem weakest_eq_multiShot_iff (first second : CaptureCapacity) :
    weakest first second = .multiShot ↔
      first = .multiShot ∧ second = .multiShot := by
  cases first <;> cases second <;> decide

theorem weakest_left_comm (first second third : CaptureCapacity) :
    weakest first (weakest second third) =
      weakest second (weakest first third) := by
  cases first <;> cases second <;> cases third <;> rfl

/-- The weakest component never exceeds either input component. -/
theorem weakest_rank_le_left (first second : CaptureCapacity) :
    (weakest first second).rank ≤ first.rank := by
  cases first <;> cases second <;> decide

theorem weakest_rank_le_right (first second : CaptureCapacity) :
    (weakest first second).rank ≤ second.rank := by
  cases first <;> cases second <;> decide

end CaptureCapacity

/-- Capacity of a whole branch-state profile.  The empty profile is fully
portable; every declared component may reduce that capacity. -/
def profileCapacity (components : List CaptureCapacity) : CaptureCapacity :=
  components.foldr CaptureCapacity.weakest .multiShot

@[simp] theorem profileCapacity_nil : profileCapacity [] = .multiShot := rfl

@[simp] theorem profileCapacity_cons
    (component : CaptureCapacity) (components : List CaptureCapacity) :
    profileCapacity (component :: components) =
      CaptureCapacity.weakest component (profileCapacity components) := rfl

theorem profileCapacity_append
    (first second : List CaptureCapacity) :
    profileCapacity (first ++ second) =
      CaptureCapacity.weakest
        (profileCapacity first) (profileCapacity second) := by
  induction first with
  | nil => simp
  | cons component components inductionHypothesis =>
      simp [inductionHypothesis, CaptureCapacity.weakest_assoc]

/-- Capture admission depends on the multiset of component capacities, not on
the order in which the implementation happened to enumerate them. -/
theorem profileCapacity_perm {first second : List CaptureCapacity}
    (same : first.Perm second) :
    profileCapacity first = profileCapacity second := by
  induction same with
  | nil => rfl
  | cons component _ inductionHypothesis =>
      simp [inductionHypothesis]
  | swap first second rest =>
      simp [CaptureCapacity.weakest_left_comm]
  | trans _ _ firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis

/-- Adding a component cannot increase branch portability. -/
theorem profileCapacity_cons_rank_le
    (component : CaptureCapacity) (components : List CaptureCapacity) :
    (profileCapacity (component :: components)).rank ≤
      (profileCapacity components).rank :=
  CaptureCapacity.weakest_rank_le_right _ _

theorem profile_all_multiShot_iff (components : List CaptureCapacity) :
    profileCapacity components = .multiShot ↔
      ∀ component ∈ components, component = .multiShot := by
  induction components with
  | nil => simp
  | cons component components inductionHypothesis =>
      simp [CaptureCapacity.weakest_eq_multiShot_iff,
        inductionHypothesis]

/-- Physical frontier storage requested by a controller.  Rankers and readouts
are intentionally absent from this type. -/
inductive StorageMode where
  | inline
  | exclusiveOneShot
  | ownedMultiShot
deriving DecidableEq, Repr

namespace StorageMode

def requiredCapacity : StorageMode → CaptureCapacity
  | .inline => .inlineOnly
  | .exclusiveOneShot => .oneShot
  | .ownedMultiShot => .multiShot

end StorageMode

def Admitted (available : CaptureCapacity) (mode : StorageMode) : Prop :=
  available.Admits mode.requiredCapacity

instance (available : CaptureCapacity) (mode : StorageMode) :
    Decidable (Admitted available mode) := by
  unfold Admitted
  infer_instance

/-- Admit exactly the requested realization.  A failed admission does not
select a different controller or storage policy. -/
def admitStorage (available : CaptureCapacity)
    (requested : StorageMode) : Option StorageMode :=
  if Admitted available requested then some requested else none

/-- An explicit admission result retains the requested mode and either that
exact realization or refusal. -/
structure StorageAdmission where
  requested : StorageMode
  realized : Option StorageMode
deriving DecidableEq, Repr

namespace StorageAdmission

def honored (decision : StorageAdmission) : Prop :=
  decision.realized = some decision.requested

instance (decision : StorageAdmission) : Decidable decision.honored := by
  unfold honored
  infer_instance

end StorageAdmission

def storageAdmission (available : CaptureCapacity)
    (requested : StorageMode) : StorageAdmission :=
  ⟨requested, admitStorage available requested⟩

theorem storageAdmission_realized_admitted
    (available : CaptureCapacity) (requested : StorageMode) :
    ∀ realized,
      (storageAdmission available requested).realized = some realized →
      Admitted available realized := by
  cases available <;> cases requested <;> decide

theorem storageAdmission_honored_iff
    (available : CaptureCapacity) (requested : StorageMode) :
    (storageAdmission available requested).honored ↔
      Admitted available requested := by
  cases available <;> cases requested <;> decide

theorem admitStorage_admitted
    (available : CaptureCapacity) (requested : StorageMode) :
    ∀ realized,
      admitStorage available requested = some realized →
      Admitted available realized := by
  cases available <;> cases requested <;> decide

theorem admitStorage_eq_requested_of_admitted
    {available : CaptureCapacity} {requested : StorageMode}
    (admitted : Admitted available requested) :
    admitStorage available requested = some requested := by
  simp [admitStorage, admitted]

/-- A one-shot profile cannot be mislabeled as an owned multi-shot frontier. -/
theorem oneShot_rejects_ownedMultiShot :
    ¬ Admitted .oneShot .ownedMultiShot := by
  decide

/-- A one-shot profile refuses an owned frontier; admission does not silently
substitute exclusive depth-first execution. -/
theorem oneShot_ownedMultiShot_is_refused :
    admitStorage .oneShot .ownedMultiShot = none := by
  decide

theorem oneShot_ownedMultiShot_is_explicitly_refused :
    (storageAdmission .oneShot .ownedMultiShot).realized = none ∧
      ¬ (storageAdmission .oneShot .ownedMultiShot).honored := by
  decide

/-- An inline-only component prevents construction of either kind of stored
choice point. -/
theorem inlineOnly_rejects_choice_points :
    ¬ Admitted .inlineOnly .exclusiveOneShot ∧
      ¬ Admitted .inlineOnly .ownedMultiShot := by
  decide

namespace Canaries

/-! These canaries classify concrete state realizations, not semantic
components in isolation.  In particular, ABT bindings remain the single
logical authority in both binding cases below: a mutable mark/trail is
one-shot, while an independently owned ABT image is multi-shot. -/
inductive Component where
  | pureGoal
  | rollbackBindingTrail
  | ownedBindingImage
  | linearTransaction
  | borrowedForeignState
deriving DecidableEq, Repr

def capacity : Component → CaptureCapacity
  | .pureGoal => .multiShot
  | .rollbackBindingTrail => .oneShot
  | .ownedBindingImage => .multiShot
  | .linearTransaction => .oneShot
  | .borrowedForeignState => .inlineOnly

def pureProfile : List CaptureCapacity :=
  [capacity .pureGoal]

def rollbackTrailProfile : List CaptureCapacity :=
  [capacity .pureGoal, capacity .rollbackBindingTrail]

def ownedBindingProfile : List CaptureCapacity :=
  [capacity .pureGoal, capacity .ownedBindingImage]

def transactionProfile : List CaptureCapacity :=
  [capacity .pureGoal, capacity .ownedBindingImage,
    capacity .linearTransaction]

def borrowedProfile : List CaptureCapacity :=
  [capacity .pureGoal, capacity .borrowedForeignState]

theorem pure_profile_admits_owned_multiShot :
    Admitted (profileCapacity pureProfile) .ownedMultiShot := by
  decide

theorem rollback_trail_profile_admits_only_exclusive_choice :
    Admitted (profileCapacity rollbackTrailProfile) .exclusiveOneShot ∧
      ¬ Admitted (profileCapacity rollbackTrailProfile) .ownedMultiShot := by
  decide

/-- Positive control: changing only the physical binding realization from a
rollback trail to an independently owned ABT image admits a multi-shot
frontier without introducing another binding authority. -/
theorem owned_binding_image_admits_owned_multiShot :
    Admitted (profileCapacity ownedBindingProfile) .ownedMultiShot := by
  decide

/-- Negative control: adding a linear transaction to an otherwise portable
profile cannot manufacture multi-shot ownership. -/
theorem linear_transaction_blocks_owned_multiShot :
    profileCapacity transactionProfile = .oneShot ∧
      admitStorage (profileCapacity transactionProfile) .ownedMultiShot =
        none := by
  decide

/-- Negative control: borrowed state that cannot outlive the current dynamic
extent refuses an owned frontier without selecting a replacement policy. -/
theorem borrowed_state_refuses_owned_multiShot :
    profileCapacity borrowedProfile = .inlineOnly ∧
      admitStorage (profileCapacity borrowedProfile) .ownedMultiShot =
        none := by
  decide

end Canaries

#print axioms CaptureCapacity.weakest_comm
#print axioms CaptureCapacity.weakest_assoc
#print axioms profileCapacity_append
#print axioms profileCapacity_perm
#print axioms profile_all_multiShot_iff
#print axioms admitStorage_admitted
#print axioms storageAdmission_realized_admitted
#print axioms storageAdmission_honored_iff
#print axioms oneShot_rejects_ownedMultiShot
#print axioms oneShot_ownedMultiShot_is_refused
#print axioms oneShot_ownedMultiShot_is_explicitly_refused
#print axioms Canaries.pure_profile_admits_owned_multiShot
#print axioms Canaries.rollback_trail_profile_admits_only_exclusive_choice
#print axioms Canaries.owned_binding_image_admits_owned_multiShot
#print axioms Canaries.linear_transaction_blocks_owned_multiShot
#print axioms Canaries.borrowed_state_refuses_owned_multiShot

end Mettapedia.GSLT.Core.BranchCaptureAlgebra
