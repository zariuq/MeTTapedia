import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RepresentedPaths
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PreparedPublicationsControls

/-!
# Complete represented runs and a missing-branch control

Natural-number codes represent arbitrarily long stores of genuine Boolean
equations. Both candidate labels perform the existing tell operation, so the
state changes while the event word distinguishes equal-endpoint branches.
The full representation covers every admitted run. A false-only candidate
representation remains closed under preparation but fails coverage, precisely
because the omitted true event has the same effect and a different identity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.RepresentedPathsControls

open Presentation.Controls
open PublicationTransportControls

abbrev P := program permissive
abbrev E := P.effectCore
abbrev allow : E.Admission := P.eventAdmission

def store (length : Nat) : Store := List.replicate length (true, false)

def representation : E.Representation Nat (fun _ => Bool) where
  state := store
  firing label := label
  preparedResult {length} _ _ := length + 1
  result_eq {length} _ _ := by
    change List.replicate (length + 1) (true, false) = List.replicate length (true, false) ++ [(true, false)]
    exact List.replicate_succ'

theorem coverage : representation.Covers allow := fun _ label _ _ => ⟨label, rfl⟩

theorem faithful (length : Nat) : Function.Injective (representation.firing (s := length)) :=
  fun _ _ same => same

abbrev Object := EffectCore.EventObject representation.effect (representation.admission allow)

def event (length : Nat) (label : Bool) :
    representation.effect.Event (representation.admission allow) length (length + 1) :=
  ⟨label, prepares (store length) (), ⟨prepares (store length) (), trivial⟩, rfl⟩

def run (length : Nat) : List Bool → @Quiver.PathStar Object _ length
  | [] => ⟨length, .nil⟩
  | label :: labels =>
      let later := run (length + 1) labels
      ⟨later.1, ((@Quiver.Path.nil Object _ length).cons (event length label)).comp later.2⟩

theorem run_last (length : Nat) (labels : List Bool) :
    ((run length labels).1 : Nat) = length + labels.length := by
  induction labels generalizing length with
  | nil => simp [run]
  | cons label labels ih =>
      change (run (length + 1) labels).1 = _
      rw [ih]
      simp [Nat.add_comm, Nat.add_left_comm]

def labelsObserver : EventObserver (EffectCore.EventObject E allow) where
  Data _ := List Bool
  update event record := record ++ [event.firing]

theorem run_labels (length : Nat) (labels record : List Bool) :
    (representation.observer allow labelsObserver).evaluate (run length labels).2 record = record ++ labels := by
  induction labels generalizing length record with
  | nil => simp [run, EventObserver.evaluate]
  | cons label labels ih =>
      change (representation.observer allow labelsObserver).evaluate
        (((@Quiver.Path.nil Object _ length).cons (event length label)).comp (run (length + 1) labels).2) record = _
      rw [EventObserver.evaluate_comp, ih]
      simp [EffectCore.Representation.observer, EventObserver.comap,
        EffectCore.Representation.mapEvents, EffectCore.Representation.mapEvent,
        labelsObserver, EventObserver.evaluate, List.append_assoc]
      rfl

theorem arbitrary_run_unique (length : Nat)
    (path : @Quiver.PathStar (EffectCore.EventObject E allow) _ (store length)) :
    ∃! lifted : @Quiver.PathStar Object _ length,
      (representation.mapEvents allow).pathStar length lifted = path :=
  representation.unique_path_lift allow coverage faithful length path

theorem equal_endpoint_labels_distinct :
    (run 0 [false]).1 = (run 0 [true]).1 ∧ run 0 [false] ≠ run 0 [true] := by
  refine ⟨rfl, ?_⟩
  intro same
  have read := congrArg
    (fun path : @Quiver.PathStar Object _ (0 : Nat) =>
      (representation.observer allow labelsObserver).evaluate (s := (0 : Nat)) (t := path.1) path.2 []) same
  rw [run_labels, run_labels] at read
  simp at read

def falseOnly : E.Representation Nat (fun _ => Unit) where
  state := store
  firing _ := false
  preparedResult {length} _ _ := length + 1
  result_eq {length} _ _ := by
    change List.replicate (length + 1) (true, false) = List.replicate length (true, false) ++ [(true, false)]
    exact List.replicate_succ'

theorem missing_candidate_not_covered : ¬ falseOnly.Covers allow := by
  intro covers
  obtain ⟨selected, same⟩ := covers 0 true (prepares (store 0) ()) ⟨prepares (store 0) (), trivial⟩
  exact Bool.noConfusion same

theorem missed_event_same_endpoint :
    E.preparedResult (s := store 0) false (prepares (store 0) ()) =
      E.preparedResult (s := store 0) true (prepares (store 0) ()) ∧
    (representation.mapEvent (event 0 false)).firing ≠
      (representation.mapEvent (event 0 true)).firing := by
  exact ⟨rfl, Bool.false_ne_true⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.RepresentedPathsControls
