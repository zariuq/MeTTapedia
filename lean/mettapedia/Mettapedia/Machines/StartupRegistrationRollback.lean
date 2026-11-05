import Mettapedia.GSLT.Dynamics.StoreReachability
import Std

/-!
# Canceling an unpublished root-registration prefix

The reference installs an observer and two providers together, or leaves the
old semantic registries intact. The target attempts each registration in order,
then removes its fresh owner's partial prefix on refusal. Only an empty,
unpublished holder justifies restoring the preceding collection mode; a live
legacy holder stops instead. Observer refusal itself need not disable the mode.

Existing indexed-registry and finite-resource models supply separate background.
This protocol reuses StoreReachability directly, without a second heap model.
The list carrier describes semantic entries, not vector capacity, diagnostics,
hash indexes or callback allocation. Native append/swap-removal coherence,
fresh complete callback/context identity, discovery of every strong root,
synchronization and the empty-constructor invariant remain native obligations.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.StartupRegistrationRollback

open Mettapedia.GSLT.Dynamics.StoreReachability
variable {Owner Cell : Type} [DecidableEq Owner]

inductive Role where
  | observer | counted | ordinary
  deriving DecidableEq, Repr

inductive Mode where
  | off | shadow | reclaim
  deriving DecidableEq, Repr

inductive Outcome where
  | accepted | cancelled | stopped
  deriving DecidableEq, Repr

structure Registry (Owner : Type) where
  observers : List Owner
  providers : List (Owner × Role)
  mode : Mode
  deriving DecidableEq, Repr

structure Holder (Owner Cell : Type) where
  owner : Owner
  owned : List Cell
  published : Bool

def Holder.emptyUnpublished (holder : Holder Owner Cell) : Bool :=
  holder.owned.isEmpty && !holder.published

def Fresh (owner : Owner) (registry : Registry Owner) : Prop :=
  owner ∉ registry.observers ∧ ∀ entry ∈ registry.providers, entry.1 ≠ owner

structure Plan where
  observer : Bool
  counted : Bool
  ordinary : Bool
  deriving DecidableEq, Repr

def Plan.allow (plan : Plan) : Role → Bool
  | .observer => plan.observer
  | .counted => plan.counted
  | .ordinary => plan.ordinary

def Plan.all (plan : Plan) : Bool := plan.observer && plan.counted && plan.ordinary

structure Result (Owner : Type) where
  registry : Registry Owner
  outcome : Outcome
  deriving DecidableEq, Repr

namespace Reference

def start (plan : Plan) (holder : Holder Owner Cell) (before : Registry Owner) : Result Owner :=
  if plan.all then
    ⟨⟨before.observers ++ [holder.owner],
      before.providers ++ [(holder.owner, .counted), (holder.owner, .ordinary)], before.mode⟩, .accepted⟩
  else if holder.emptyUnpublished then ⟨before, .cancelled⟩
  else ⟨{before with mode := if plan.observer then .off else before.mode}, .stopped⟩

end Reference

namespace Native

def add (owner : Owner) (role : Role) (registry : Registry Owner) : Registry Owner :=
  match role with
  | .observer => {registry with observers := registry.observers ++ [owner]}
  | .counted | .ordinary => {registry with providers := registry.providers ++ [(owner, role)]}

def refused (role : Role) (registry : Registry Owner) : Registry Owner :=
  match role with
  | .observer => registry
  | .counted | .ordinary => {registry with mode := .off}

structure Prefix (Owner : Type) where
  registry : Registry Owner
  accepted : Bool
  attempts : List Role

def attempt (allow : Role → Bool) (owner : Owner) : List Role → Registry Owner → Prefix Owner
  | [], registry => ⟨registry, true, []⟩
  | role :: rest, registry =>
      if allow role then
        let later := attempt allow owner rest (add owner role registry)
        ⟨later.registry, later.accepted, role :: later.attempts⟩
      else ⟨refused role registry, false, [role]⟩

def cancel (owner : Owner) (registry : Registry Owner) : Registry Owner :=
  { registry with
    observers := registry.observers.filter (fun other => decide (other ≠ owner))
    providers := registry.providers.filter (fun entry => decide (entry.1 ≠ owner)) }

def start (plan : Plan) (holder : Holder Owner Cell) (before : Registry Owner) : Result Owner :=
  let attempted := attempt plan.allow holder.owner [.observer, .counted, .ordinary] before
  if attempted.accepted then ⟨attempted.registry, .accepted⟩ else
    let removed := cancel holder.owner attempted.registry
    if holder.emptyUnpublished then ⟨{removed with mode := before.mode}, .cancelled⟩
    else ⟨removed, .stopped⟩

end Native

theorem cancel_add (owner : Owner) (role : Role) (registry : Registry Owner) :
    Native.cancel owner (Native.add owner role registry) = Native.cancel owner registry := by
  cases role <;> simp [Native.cancel, Native.add, List.filter_append]

theorem cancel_fresh (owner : Owner) (registry : Registry Owner) (fresh : Fresh owner registry) :
    Native.cancel owner registry = registry := by
  obtain ⟨absent, providers⟩ := fresh
  have observers : registry.observers.filter (fun other => decide (other ≠ owner)) = registry.observers := by
    apply List.filter_eq_self.mpr
    intro other member
    simp only [decide_eq_true_eq]
    intro same
    exact absent (same ▸ member)
  have providerList : registry.providers.filter (fun entry => decide (entry.1 ≠ owner)) = registry.providers := by
    exact List.filter_eq_self.mpr (fun entry member => by simpa using providers entry member)
  unfold Native.cancel
  rw [observers, providerList]

/-- Any partial attempt, including refusal after an arbitrary accepted prefix,
can be canceled without changing an earlier semantic entry. Mode is separate. -/
theorem cancel_attempt_entries (allow : Role → Bool) (owner : Owner) (roles : List Role)
    (registry : Registry Owner) :
    let after := Native.cancel owner (Native.attempt allow owner roles registry).registry
    after.observers = (Native.cancel owner registry).observers ∧
      after.providers = (Native.cancel owner registry).providers := by
  induction roles generalizing registry with
  | nil => exact ⟨rfl, rfl⟩
  | cons role rest ih =>
      cases allowed : allow role with
      | true => simpa only [Native.attempt, allowed, if_true, cancel_add] using ih (Native.add owner role registry)
      | false =>
          simp only [Native.attempt, allowed, Bool.false_eq_true, if_false]
          cases role <;> exact ⟨rfl, rfl⟩

theorem startup_refines (plan : Plan) (holder : Holder Owner Cell) (before : Registry Owner)
    (fresh : Fresh holder.owner before) : Native.start plan holder before = Reference.start plan holder before := by
  have cancelled := cancel_fresh holder.owner before fresh
  have observers := congrArg Registry.observers cancelled
  have providers := congrArg Registry.providers cancelled
  simp only [Native.cancel, decide_not] at observers providers
  rcases plan with ⟨observer, counted, ordinary⟩
  cases observer <;> cases counted <;> cases ordinary <;>
    cases empty : holder.emptyUnpublished <;>
      simp [Native.start, Native.attempt, Native.add, Native.refused, Native.cancel,
        Reference.start, Plan.allow, Plan.all, empty, List.filter_append, observers, providers]

theorem empty_failure_restores (plan : Plan) (holder : Holder Owner Cell) (before : Registry Owner)
    (fresh : Fresh holder.owner before) (empty : holder.emptyUnpublished = true) (failure : plan.all = false) :
    Native.start plan holder before = ⟨before, .cancelled⟩ := by
  rw [startup_refines plan holder before fresh]
  simp [Reference.start, failure, empty]

theorem live_failure_stops (plan : Plan) (holder : Holder Owner Cell) (before : Registry Owner)
    (fresh : Fresh holder.owner before) (live : holder.emptyUnpublished = false) (failure : plan.all = false) :
    (Native.start plan holder before).outcome = .stopped := by
  rw [startup_refines plan holder before fresh]
  simp [Reference.start, failure, live]

theorem existing_entries_exact_after_refusal (plan : Plan) (holder : Holder Owner Cell) (before : Registry Owner)
    (fresh : Fresh holder.owner before) (failure : plan.all = false) :
    (Native.start plan holder before).registry.observers = before.observers ∧
      (Native.start plan holder before).registry.providers = before.providers := by
  rw [startup_refines plan holder before fresh]
  cases empty : holder.emptyUnpublished <;> simp [Reference.start, failure, empty]

def CanCollect (result : Result Owner) : Prop := result.outcome ≠ .stopped ∧ result.registry.mode ≠ .off

theorem empty_refusal_preserves_collection_eligibility (plan : Plan) (holder : Holder Owner Cell)
    (before : Registry Owner) (fresh : Fresh holder.owner before)
    (empty : holder.emptyUnpublished = true) (failure : plan.all = false) :
    CanCollect (Native.start plan holder before) ↔ before.mode ≠ .off := by
  rw [empty_failure_restores plan holder before fresh empty failure]
  simp [CanCollect]

theorem live_refusal_never_collects (plan : Plan) (holder : Holder Owner Cell) (before : Registry Owner)
    (fresh : Fresh holder.owner before) (live : holder.emptyUnpublished = false) (failure : plan.all = false) :
    ¬CanCollect (Native.start plan holder before) := by
  simp [CanCollect, live_failure_stops plan holder before fresh live failure]

/-- Provider callbacks are interpreted when roots are observed, not cached at
registration. Observer entries are separately preserved by the rollback law. -/
def rootStore (registry : Registry Owner) (enumerate : Owner × Role → Cell → Prop)
    (outside : Cell → Prop) (pointsTo : Cell → Cell → Prop) : Store Cell where
  root cell := outside cell ∨ ∃ provider ∈ registry.providers, enumerate provider cell
  pointsTo := pointsTo

theorem refusal_preserves_root_store (plan : Plan) (holder : Holder Owner Cell) (before : Registry Owner)
    (fresh : Fresh holder.owner before) (failure : plan.all = false)
    (enumerate : Owner × Role → Cell → Prop) (outside : Cell → Prop) (pointsTo : Cell → Cell → Prop) :
    rootStore (Native.start plan holder before).registry enumerate outside pointsTo =
      rootStore before enumerate outside pointsTo := by
  unfold rootStore
  rw [(existing_entries_exact_after_refusal plan holder before fresh failure).2]

theorem refusal_preserves_collected_reach (plan : Plan) (holder : Holder Owner Cell) (before : Registry Owner)
    (fresh : Fresh holder.owner before) (failure : plan.all = false)
    (enumerate : Owner × Role → Cell → Prop) (outside : Cell → Prop)
    (pointsTo : Cell → Cell → Prop) (cell : Cell) :
    Reach (collect (rootStore (Native.start plan holder before).registry enumerate outside pointsTo)) cell ↔
      Reach (rootStore before enumerate outside pointsTo) cell := by
  rw [refusal_preserves_root_store plan holder before fresh failure enumerate outside pointsTo]
  exact reach_collect _ _

omit [DecidableEq Owner] in
theorem empty_holder_adds_no_required_roots (holder : Holder Owner Cell) (empty : holder.emptyUnpublished = true) :
    holder.owned = [] ∧ holder.published = false := by
  simpa [Holder.emptyUnpublished] using empty

/-- Empty cancellation is safe for the holder's complete required-root set,
not merely for the roots that happened to register before refusal. -/
theorem empty_refusal_preserves_required_reach (plan : Plan) (holder : Holder Owner Cell)
    (before : Registry Owner) (fresh : Fresh holder.owner before)
    (empty : holder.emptyUnpublished = true) (failure : plan.all = false)
    (enumerate : Owner × Role → Cell → Prop) (outside : Cell → Prop)
    (pointsTo : Cell → Cell → Prop) (cell : Cell) :
    Reach (collect (rootStore (Native.start plan holder before).registry enumerate outside pointsTo)) cell ↔
      Reach (rootStore before enumerate (fun id => outside id ∨ id ∈ holder.owned) pointsTo) cell := by
  have noNewRoots := (empty_holder_adds_no_required_roots holder empty).1
  simpa [noNewRoots] using
    refusal_preserves_collected_reach plan holder before fresh failure enumerate outside pointsTo cell

namespace Controls

def before : Registry Nat := ⟨[10, 20], [(10, .counted), (10, .ordinary), (20, .counted), (20, .ordinary)], .reclaim⟩
def freshHolder : Holder Nat Nat := ⟨30, [], false⟩
def liveHolder : Holder Nat Nat := ⟨30, [9], true⟩
def refuseObserver : Plan := ⟨false, true, true⟩
def refuseCounted : Plan := ⟨true, false, true⟩
def refuseOrdinary : Plan := ⟨true, true, false⟩

theorem observer_provider_and_final_provider_refusals_restore :
    Native.start refuseObserver freshHolder before = ⟨before, .cancelled⟩ ∧
      Native.start refuseCounted freshHolder before = ⟨before, .cancelled⟩ ∧
        Native.start refuseOrdinary freshHolder before = ⟨before, .cancelled⟩ := by decide

theorem refusal_never_attempts_a_later_registration :
    (Native.attempt refuseCounted.allow 30 [.observer, .counted, .ordinary] before).attempts = [.observer, .counted] ∧
      (Native.attempt refuseObserver.allow 30 [.observer, .counted, .ordinary] before).attempts = [.observer] := by decide

theorem accepted_startup_appends_exactly_its_own_entries :
    Native.start ⟨true, true, true⟩ freshHolder before =
      ⟨⟨[10, 20, 30], [(10, .counted), (10, .ordinary), (20, .counted), (20, .ordinary),
        (30, .counted), (30, .ordinary)], .reclaim⟩, .accepted⟩ := by decide

theorem dropping_cancel_leaves_a_partial_observer :
    (Native.attempt refuseCounted.allow 30 [.observer, .counted, .ordinary] before).registry.observers ≠
      (Native.start refuseCounted freshHolder before).registry.observers := by decide

theorem omitting_mode_restore_preserves_entries_but_disables_collection :
    let attempted := Native.attempt refuseCounted.allow 30 [.observer, .counted, .ordinary] before
    let cancelled := Native.cancel 30 attempted.registry
    cancelled.observers = before.observers ∧ cancelled.providers = before.providers ∧
      cancelled.mode = .off ∧ (Native.start refuseCounted freshHolder before).registry.mode = .reclaim ∧
        ¬CanCollect ⟨cancelled, .cancelled⟩ ∧ CanCollect (Native.start refuseCounted freshHolder before) := by
  unfold CanCollect
  decide

theorem nonfresh_owner_would_delete_an_existing_provider :
    (Native.cancel 10 before).providers ≠ before.providers := by decide

def enumerate (provider : Nat × Role) (cell : Nat) : Prop :=
  provider.1 = 10 ∧ cell = 7 ∨ provider.1 = 20 ∧ cell = 8

def noEdges : Nat → Nat → Prop := fun _ _ => False
def noOutside : Nat → Prop := fun _ => False

def chain (parent child : Nat) : Prop := parent = 7 ∧ child = 70 ∨ parent = 70 ∧ child = 700

theorem existing_descendants_survive_rollback_and_collection :
    Reach (collect (rootStore (Native.start refuseOrdinary freshHolder before).registry
      enumerate noOutside chain)) 700 := by
  apply (refusal_preserves_collected_reach refuseOrdinary freshHolder before
    (by simp [Fresh, freshHolder, before]) (by decide) enumerate noOutside chain 700).mpr
  apply Reach.step (c := 70)
  · apply Reach.step (c := 7)
    · exact .root (Or.inr ⟨(10, .ordinary), by decide, Or.inl ⟨rfl, rfl⟩⟩)
    · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

theorem live_missing_root_is_unreachable :
    ¬Reach (rootStore before enumerate noOutside noEdges) 9 := by
  intro live
  cases live with
  | root rooted => simp [rootStore, enumerate, before, noOutside] at rooted
  | step _ edge => exact edge.elim

/-- This mutant treats a live holder as a safely cancelable empty startup. -/
def unsafeRestore (plan : Plan) (holder : Holder Nat Nat) (registry : Registry Nat) : Result Nat :=
  let attempted := Native.attempt plan.allow holder.owner [.observer, .counted, .ordinary] registry
  let removed := Native.cancel holder.owner attempted.registry
  ⟨{removed with mode := registry.mode}, .cancelled⟩

theorem restoring_for_a_live_unregistered_holder_is_unsafe :
    Reach (rootStore before enumerate (fun cell => cell ∈ liveHolder.owned) noEdges) 9 ∧
      CanCollect (unsafeRestore refuseCounted liveHolder before) ∧
      ¬Reach (collect (rootStore (unsafeRestore refuseCounted liveHolder before).registry
        enumerate noOutside noEdges)) 9 ∧
        (Native.start refuseCounted liveHolder before).outcome = .stopped := by
  refine ⟨.root (Or.inl (by decide)), by unfold CanCollect; decide, ?_, by decide⟩
  change ¬Reach (collect (rootStore before enumerate noOutside noEdges)) 9
  exact fun live => live_missing_root_is_unreachable ((reach_collect _ _).mp live)

end Controls
end Mettapedia.Machines.StartupRegistrationRollback
