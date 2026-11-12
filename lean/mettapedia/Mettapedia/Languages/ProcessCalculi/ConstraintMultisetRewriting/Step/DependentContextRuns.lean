import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentContextPlacement
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CandidateReindexing

/-!
# Context placement along complete dependent runs

The grade checks the local resource and query conditions at every actual
intermediate state. Its composition law follows the execution boundary.
Placed runs retain the complete firing word, endpoint state and contextual
refinement map. No grade is assigned to a trace class by this construction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O]

def RunSafe (extra : Finset O) : {state : State rules O} → (helperStep levels O).toStep.Run state → Prop
  | _, .nil _ => True
  | _, .cons candidate _ rest => Safe extra candidate ∧ RunSafe extra rest

def placeRun (extra : Finset O) : {state : State rules O} →
    (run : (helperStep levels O).toStep.Run state) → RunSafe extra run →
      (helperStep levels O).toStep.Run (place extra state)
  | _, .nil state, _ => .nil (place extra state)
  | _, .cons candidate accepted rest, safe =>
      .cons (firing extra candidate) (admits extra candidate accepted safe.1.fresh safe.1.queries)
        ((result extra candidate accepted safe.1).symm ▸ placeRun extra rest safe.2)

theorem placeRun_last (extra : Finset O) : ∀ {state : State rules O}
    (run : (helperStep levels O).toStep.Run state) (safe : RunSafe extra run),
    (placeRun extra run safe).last = place extra run.last
  | _, .nil _, _ => rfl
  | _, .cons candidate accepted rest, safe => by
      simp only [placeRun, Step.Run.last, Step.Run.last_cast]
      exact placeRun_last extra rest safe.2

def placeEvent (extra : Finset O) (event : Σ state : State rules O, HelperFiring levels O state) :
    Σ state : State rules O, HelperFiring levels O state :=
  ⟨place extra event.1, firing extra event.2⟩

theorem placeRun_word (extra : Finset O) : ∀ {state : State rules O}
    (run : (helperStep levels O).toStep.Run state) (safe : RunSafe extra run),
    (placeRun extra run safe).word = run.word.map (placeEvent extra)
  | _, .nil _, _ => rfl
  | _, .cons candidate accepted rest, safe => by
      simp only [placeRun, Step.Run.word, Step.Run.word_cast, List.map_cons]
      exact congrArg (List.cons _) (placeRun_word extra rest safe.2)

theorem runSafe_append (extra : Finset O) : ∀ {state : State rules O}
    (early : (helperStep levels O).toStep.Run state)
    (later : (helperStep levels O).toStep.Run early.last),
    RunSafe extra (early.append later) ↔ RunSafe extra early ∧ RunSafe extra later
  | _, .nil _, _ => ⟨fun safe => ⟨True.intro, safe⟩, fun safe => safe.2⟩
  | _, .cons _ _ rest, later =>
      (and_congr Iff.rfl (runSafe_append extra rest later)).trans and_assoc.symm

def refinement {state : State rules O} (run : (helperStep levels O).toStep.Run state) :
    Σ target : Context rules, target ⟶ state.frame := ⟨run.last.frame, run.toLast⟩

theorem refinement_cast {source target : State rules O} (same : source = target)
    (run : (helperStep levels O).toStep.Run source) :
    HEq (refinement (same ▸ run)) (refinement run) := by
  cases same
  rfl

theorem placeRun_refinement (extra : Finset O) : ∀ {state : State rules O}
    (run : (helperStep levels O).toStep.Run state) (safe : RunSafe extra run),
    refinement (placeRun extra run safe) = refinement run
  | _, .nil _, _ => rfl
  | _, .cons candidate accepted rest, safe => by
      have castMap := eq_of_heq (refinement_cast (result extra candidate accepted safe.1).symm
        (placeRun extra rest safe.2))
      have tailMap := castMap.trans (placeRun_refinement extra rest safe.2)
      exact congrArg (fun data : Σ target : Context rules, target ⟶ candidate.helpers.frame =>
        (⟨data.1, data.2 ≫ (helperStep levels O).along candidate accepted⟩ :
          Σ target : Context rules, target ⟶ _)) tailMap

theorem placeRun_event_count (extra : Finset O) {state : State rules O}
    (run : (helperStep levels O).toStep.Run state) (safe : RunSafe extra run) :
    (placeRun extra run safe).word.length = run.word.length := by
  rw [placeRun_word, List.length_map]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement.placeRun_last
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement.placeRun_refinement
