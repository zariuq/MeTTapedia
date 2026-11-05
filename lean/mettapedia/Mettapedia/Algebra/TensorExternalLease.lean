import Mettapedia.Algebra.TensorOwnership
import Mettapedia.Algebra.TensorStrides

/-!
# An external owner lease shared by immutable tensor views

The reference names the distinct published descriptors. The implementation
uses the maintained TensorOwnership.Owner counter, at the storage-descriptor
layer, with no extra pin class. Internal construction temporaries are not
published descriptors. Validation and allocation precede the one external
retain; sharing descriptors does not acquire another external lease.

Valid action traces express the native caller's live-pointer and fresh-result
obligations. Tensor-handle aliases, atomic/refcount overflow, pointer identity,
allocation, callback behavior, immutability and NumPy lifetime remain native.
The module does not introduce another heap or a general ownership framework.
-/

set_option autoImplicit false
namespace Mettapedia.Algebra.TensorExternalLease

open TensorOwnership

variable {Context View : Type}

structure Admission where
  allocation : Bool
  bounds : Bool
  booleanValues : Bool
  deriving DecidableEq, Repr

def Admission.accepted (checks : Admission) : Bool :=
  checks.allocation && checks.bounds && checks.booleanValues

inductive Action (Context View : Type) where
  | construct (context : Context) (seed : View) (checks : Admission)
  | share (source fresh : View) (ready : Bool)
  | drop (view : View)
  deriving DecidableEq, Repr

inductive Event (Context View : Type) where
  | retained (context : Context)
  | released (context : Context)
  | published (view : View)
  | dropped (view : View)
  | refused
  | protocolFault
  deriving DecidableEq, Repr

structure Transition (State Context View : Type) where
  next : State
  events : List (Event Context View)

namespace Reference

inductive State (Context View : Type) where
  | fresh
  | live (context : Context) (descriptors : List View)
  | retired
  deriving DecidableEq, Repr

def Permitted [DecidableEq View] (state : State Context View) : Action Context View → Prop
  | .construct _ _ _ => match state with | .fresh => True | _ => False
  | .share source fresh _ => match state with
      | .live _ descriptors => source ∈ descriptors ∧ fresh ∉ descriptors
      | _ => False
  | .drop view => match state with | .live _ descriptors => view ∈ descriptors | _ => False

def step [DecidableEq View] (state : State Context View) :
    Action Context View → Transition (State Context View) Context View
  | .construct context seed checks => match state with
      | .fresh => if checks.accepted then
          ⟨.live context [seed], [.retained context, .published seed]⟩
        else ⟨state, [.refused]⟩
      | _ => ⟨state, [.protocolFault]⟩
  | .share source fresh ready => match state with
      | .live context descriptors =>
          if source ∈ descriptors ∧ fresh ∉ descriptors then
            if ready then ⟨.live context (fresh :: descriptors), [.published fresh]⟩
            else ⟨state, [.refused]⟩
          else ⟨state, [.protocolFault]⟩
      | _ => ⟨state, [.protocolFault]⟩
  | .drop view => match state with
      | .live context descriptors =>
          if view ∈ descriptors then
            let remaining := descriptors.erase view
            if remaining.isEmpty then ⟨.retired, [.dropped view, .released context]⟩
            else ⟨.live context remaining, [.dropped view]⟩
          else ⟨state, [.protocolFault]⟩
      | _ => ⟨state, [.protocolFault]⟩

def ValidTrace [DecidableEq View] : State Context View → List (Action Context View) → Prop
  | _, [] => True
  | state, action :: rest => Permitted state action ∧ ValidTrace (step state action).next rest

end Reference

namespace Native

inductive State (Context : Type) where
  | fresh
  | live (context : Context) (references : Owner)
  | retired
  deriving DecidableEq, Repr

def step (state : State Context) : Action Context View → Transition (State Context) Context View
  | .construct context seed checks => match state with
      | .fresh =>
          if !checks.allocation then ⟨state, [.refused]⟩
          else if !checks.bounds then ⟨state, [.refused]⟩
          else if !checks.booleanValues then ⟨state, [.refused]⟩
          else ⟨.live context ⟨1, 0⟩, [.retained context, .published seed]⟩
      | _ => ⟨state, [.protocolFault]⟩
  | .share _ fresh ready => match state with
      | .live context references =>
          if references.holders == 0 then ⟨state, [.protocolFault]⟩
          else if ready then ⟨.live context (retain references), [.published fresh]⟩
          else ⟨state, [.refused]⟩
      | _ => ⟨state, [.protocolFault]⟩
  | .drop view => match state with
      | .live context references =>
          if references.holders == 0 then ⟨state, [.protocolFault]⟩
          else if references.holders == 1 then ⟨.retired, [.dropped view, .released context]⟩
          else ⟨.live context (dropHolder references), [.dropped view]⟩
      | _ => ⟨state, [.protocolFault]⟩

end Native

def Represents : Reference.State Context View → Native.State Context → Prop
  | .fresh, .fresh | .retired, .retired => True
  | .live context descriptors, .live actual references =>
      actual = context ∧ descriptors.Nodup ∧ descriptors ≠ [] ∧
        references.holders = descriptors.length ∧ references.pins = 0
  | _, _ => False

theorem step_refines [DecidableEq View] (reference : Reference.State Context View)
    (native : Native.State Context) (represented : Represents reference native)
    (action : Action Context View) (permitted : Reference.Permitted reference action) :
    Represents (Reference.step reference action).next (Native.step native action).next ∧
      (Reference.step reference action).events = (Native.step native action).events := by
  cases reference with
  | fresh =>
      cases native with
      | fresh =>
          cases action with
          | construct context seed checks =>
              rcases checks with ⟨allocation, bounds, booleanValues⟩
              cases allocation <;> cases bounds <;> cases booleanValues <;>
                simp [Reference.step, Native.step, Admission.accepted, Represents]
          | share source fresh ready => cases permitted
          | drop view => cases permitted
      | live context references => cases represented
      | retired => cases represented
  | live context descriptors =>
      cases native with
      | live actual references =>
          change actual = context ∧ descriptors.Nodup ∧ descriptors ≠ [] ∧
            references.holders = descriptors.length ∧ references.pins = 0 at represented
          obtain ⟨rfl, distinct, nonempty, count, pins⟩ := represented
          have positive : 0 < references.holders := by
            have : 0 < descriptors.length := List.length_pos_iff.mpr nonempty
            omega
          cases action with
          | construct context seed checks => cases permitted
          | share source fresh ready =>
              change source ∈ descriptors ∧ fresh ∉ descriptors at permitted
              obtain ⟨present, unused⟩ := permitted
              have nextDistinct : (fresh :: descriptors).Nodup := List.nodup_cons.mpr ⟨unused, distinct⟩
              cases ready <;>
                simp [Reference.step, Native.step, present, unused, Represents,
                  retain, count, pins, distinct, nonempty, nextDistinct]
          | drop view =>
              change view ∈ descriptors at permitted
              have shorter := List.length_erase_of_mem permitted
              have nextDistinct := distinct.erase view
              by_cases last : (descriptors.erase view).isEmpty = true
              · have empty : descriptors.erase view = [] := List.isEmpty_iff.mp last
                have one : references.holders = 1 := by simp [empty] at shorter; omega
                simp [Reference.step, Native.step, permitted, last, one, Represents]
              · have remains : descriptors.erase view ≠ [] := by
                  intro empty
                  exact last (by simp [empty])
                have notOne : references.holders ≠ 1 := by
                  have : 0 < (descriptors.erase view).length := List.length_pos_iff.mpr remains
                  omega
                have notOneLength : descriptors.length ≠ 1 := by omega
                simp [Reference.step, Native.step, permitted, last,
                  notOneLength, Represents, dropHolder, shorter, count, pins, nextDistinct, remains,
                  nonempty]
      | fresh => cases represented
      | retired => cases represented
  | retired => cases action <;> cases permitted

def run {State : Type} (step : State → Action Context View → Transition State Context View) :
    State → List (Action Context View) → Transition State Context View
  | state, [] => ⟨state, []⟩
  | state, action :: rest =>
      let first := step state action
      let later := run step first.next rest
      ⟨later.next, first.events ++ later.events⟩

theorem valid_trace_refines [DecidableEq View] (reference : Reference.State Context View)
    (native : Native.State Context) (represented : Represents reference native)
    (actions : List (Action Context View)) (valid : Reference.ValidTrace reference actions) :
    Represents (run Reference.step reference actions).next (run Native.step native actions).next ∧
      (run Reference.step reference actions).events = (run Native.step native actions).events := by
  induction actions generalizing reference native with
  | nil => exact ⟨represented, rfl⟩
  | cons action rest ih =>
      obtain ⟨allowed, remaining⟩ := valid
      obtain ⟨next, events⟩ := step_refines reference native represented action allowed
      obtain ⟨final, later⟩ := ih _ _ next remaining
      exact ⟨final, by simp only [run, events, later]⟩

theorem constructor_checks_precede_external_retain (context : Context) (seed : View)
    (checks : Admission) :
    Native.step .fresh (.construct context seed checks) =
      if checks.accepted then
        ⟨.live context ⟨1, 0⟩, [.retained context, .published seed]⟩
      else ⟨.fresh, [.refused]⟩ := by
  rcases checks with ⟨allocation, bounds, booleanValues⟩
  cases allocation <;> cases bounds <;> cases booleanValues <;> rfl

theorem final_descriptor_releases_external_owner (context : Context) (view : View) :
    Native.step (.live context ⟨1, 0⟩) (.drop view) =
      ⟨.retired, [.dropped view, .released context]⟩ := rfl

theorem sharing_does_not_retain_external_owner (context : Context) (source fresh : View)
    (references : Owner) (live : 0 < references.holders) :
    Native.step (.live context references) (.share source fresh true) =
      ⟨.live context (retain references), [.published fresh]⟩ := by
  simp [Native.step, Nat.ne_of_gt live]

def releaseCount (events : List (Event Context View)) : Nat :=
  events.countP fun event => match event with | .released _ => true | _ => false

theorem releaseCount_append (first second : List (Event Context View)) :
    releaseCount (first ++ second) = releaseCount first + releaseCount second := by
  simp [releaseCount]

theorem retired_trace_has_no_release (actions : List (Action Context View)) :
    releaseCount (run Native.step .retired actions).events = 0 := by
  induction actions with
  | nil => rfl
  | cons action rest ih =>
      cases action <;> simpa [run, Native.step, releaseCount] using ih

theorem step_release_retires (state : Native.State Context) (action : Action Context View) :
    releaseCount (Native.step state action).events ≤ 1 ∧
      (releaseCount (Native.step state action).events ≠ 0 → (Native.step state action).next = .retired) := by
  cases state with
  | fresh =>
      cases action with
      | construct context seed checks =>
          rw [constructor_checks_precede_external_retain]
          cases checks.accepted <;> simp [releaseCount]
      | share source fresh ready => simp [Native.step, releaseCount]
      | drop view => simp [Native.step, releaseCount]
  | live context references =>
      cases action with
      | construct newContext seed checks => simp [Native.step, releaseCount]
      | share source fresh ready =>
          by_cases empty : references.holders = 0 <;> cases ready <;>
            simp [Native.step, empty, releaseCount]
      | drop view =>
          by_cases empty : references.holders = 0 <;>
            by_cases last : references.holders = 1 <;> simp [Native.step, empty, last, releaseCount]
  | retired => cases action <;> simp [Native.step, releaseCount]

/-- After the one final release, no later permitted descriptor action can
release this storage session's external owner a second time. -/
theorem external_release_at_most_once (state : Native.State Context)
    (actions : List (Action Context View)) : releaseCount (run Native.step state actions).events ≤ 1 := by
  induction actions generalizing state with
  | nil => simp [run, releaseCount]
  | cons action rest ih =>
      have first := step_release_retires state action
      by_cases noneHere : releaseCount (Native.step state action).events = 0
      · simpa only [run, releaseCount_append, noneHere, Nat.zero_add] using ih (Native.step state action).next
      · have done := first.2 noneHere
        simp only [run, releaseCount_append, done, retired_trace_has_no_release, Nat.add_zero]
        exact first.1

/-- Geometric validation is supplied by the maintained checked-stride
algorithm. Boolean-content and allocation success remain independent gates. -/
theorem admitted_geometry_and_lease (maximum storage offset : Nat)
    (axes : List TensorStrides.Axis) (bounds : TensorStrides.Bounds)
    (success : TensorStrides.Checked.view maximum storage offset axes = some bounds)
    (context : Context) (seed : View) :
    TensorStrides.ReferenceSafe storage offset axes ∧
      (Native.step .fresh (.construct context seed
        ⟨true, (TensorStrides.Checked.view maximum storage offset axes).isSome, true⟩)).events =
          [.retained context, .published seed] := by
  refine ⟨(TensorStrides.Checked.view_success maximum storage offset axes bounds success).1, ?_⟩
  simp [Native.step, success]

namespace Controls

def accepted : Admission := ⟨true, true, true⟩

theorem refused_bounds_or_boolean_validation_calls_no_owner_hook :
    (Native.step (.fresh : Native.State Nat) (.construct 7 0 ⟨true, false, true⟩)).events = [.refused] ∧
      (Native.step .fresh (.construct 7 0 ⟨true, true, false⟩)).events = [.refused] := by decide

theorem allocation_refusal_does_not_acquire_external_owner :
    (Native.step .fresh (.construct 7 0 ⟨false, true, true⟩)).events = [.refused] := by decide

theorem empty_tensor_still_has_a_real_storage_lease :
    TensorStrides.Checked.view 127 0 0 [⟨0, -1⟩] = some ⟨0, 0⟩ ∧
      (Native.step .fresh (.construct 7 0 accepted)).events = [.retained 7, .published 0] := by decide

theorem sibling_views_keep_the_same_one_external_lease :
    let result := run Native.step (.fresh : Native.State Nat)
      [.construct 7 0 accepted, .share 0 1 true, .share 1 2 true, .drop 0, .drop 2]
    result.next = .live 7 ⟨1, 0⟩ ∧ releaseCount result.events = 0 ∧
      result.events = [.retained 7, .published 0, .published 1, .published 2, .dropped 0, .dropped 2] := by decide

theorem final_view_releases_exactly_once :
    let result := run Native.step (.fresh : Native.State Nat)
      [.construct 7 0 accepted, .share 0 1 true, .share 1 2 true, .drop 0, .drop 2, .drop 1]
    result.next = .retired ∧ releaseCount result.events = 1 := by decide

theorem reference_allows_arbitrary_valid_release_order :
    Reference.ValidTrace (.fresh : Reference.State Nat Nat)
      [.construct 7 0 accepted, .share 0 1 true, .share 1 2 true, .drop 1, .drop 0, .drop 2] := by
  simp [Reference.ValidTrace, Reference.Permitted, Reference.step, accepted, Admission.accepted]

theorem refused_new_view_changes_no_hold :
    Native.step (.live 7 ⟨1, 0⟩) (.share 0 1 false) =
      (⟨.live 7 ⟨1, 0⟩, [.refused]⟩ : Transition (Native.State Nat) Nat Nat) := rfl

/-- A missing storage hold would let the original descriptor's release
free the external owner while a sibling view still exists. -/
theorem omitted_view_hold_releases_too_early :
    let correct := (Native.step (.live 7 ⟨1, 0⟩) (.share 0 1 true)).next
    let faulty : Native.State Nat := .live 7 ⟨1, 0⟩
    (Native.step correct (.drop 0)).next = .live 7 ⟨1, 0⟩ ∧
      (Native.step faulty (.drop 0)).next = .retired := by decide

/-- Retain/release before refusal may have zero net count, but still causes
observable owner callbacks. The constructor owes neither callback. -/
theorem early_owner_callbacks_are_not_an_equivalent_refusal :
    (Native.step .fresh (.construct 7 0 ⟨true, true, false⟩)).events = [.refused] ∧
      ([Event.retained 7, Event.released 7, Event.refused] : List (Event Nat Nat)) ≠ [.refused] := by decide

end Controls

end Mettapedia.Algebra.TensorExternalLease
