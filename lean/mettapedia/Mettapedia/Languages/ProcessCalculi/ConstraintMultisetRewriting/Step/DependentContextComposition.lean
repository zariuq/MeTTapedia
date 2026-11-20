import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentContextRuns

/-!
# Composition of licensed occurrence contexts

Two successive context licenses derive the license for their union. The
placed complete run is exactly the sequentially placed run after aligning
the initial states. Query predicates may be nonmonotone, so a license for
the combined context alone is not asserted to license each intermediate one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O]

theorem place_comp (first second : Finset O) (state : State rules O) :
    place second (place first state) = place (first ∪ second) state := by
  simp only [place, Finset.union_assoc]

theorem queryStable_comp (first second : Finset O) {state : State rules O}
    (candidate : HelperFiring levels O state) (one : QueryStable first candidate)
    (two : QueryStable second (firing first candidate)) : QueryStable (first ∪ second) candidate := by
  intro observer solution solved query member holds
  have final := two observer solution solved query member (one observer solution solved query member holds)
  change query.Holds ((state.present ∪ first) ∪ second) candidate.toFiring.row solution at final
  simpa only [Finset.union_assoc] using final

theorem safe_comp (first second : Finset O) {state : State rules O}
    (candidate : HelperFiring levels O state) (one : Safe first candidate)
    (two : Safe second (firing first candidate)) : Safe (first ∪ second) candidate :=
  ⟨Finset.disjoint_union_right.mpr ⟨one.retained, two.retained⟩,
    Finset.disjoint_union_right.mpr ⟨one.fresh, two.fresh⟩,
    queryStable_comp first second candidate one.queries two.queries⟩

theorem runSafe_cast (extra : Finset O) {source target : State rules O} (same : source = target)
    (run : (helperStep levels O).toStep.Run source) : RunSafe extra (same ▸ run) ↔ RunSafe extra run := by
  cases same
  rfl

theorem runSafe_comp (first second : Finset O) :
    ∀ {state : State rules O} (run : (helperStep levels O).toStep.Run state) (one : RunSafe first run),
      RunSafe second (placeRun first run one) → RunSafe (first ∪ second) run
  | _, .nil _, _, _ => True.intro
  | _, .cons candidate accepted rest, one, two =>
      ⟨safe_comp first second candidate one.1 two.1,
        runSafe_comp first second rest one.2
          ((runSafe_cast second (result first candidate accepted one.1).symm (placeRun first rest one.2)).mp two.2)⟩

theorem placeEvent_comp (first second : Finset O)
    (event : Σ state : State rules O, HelperFiring levels O state) :
    placeEvent second (placeEvent first event) = placeEvent (first ∪ second) event := by
  rcases event with ⟨state, candidate⟩
  exact congrArg (fun present : Finset O =>
    (⟨{state with present := present}, ⟨candidate.helpers, candidate.data⟩⟩ :
      Σ state : State rules O, HelperFiring levels O state)) (Finset.union_assoc state.present first second)

theorem placeRun_comp (first second : Finset O) {state : State rules O}
    (run : (helperStep levels O).toStep.Run state) (one : RunSafe first run)
    (two : RunSafe second (placeRun first run one)) :
    place_comp first second state ▸ placeRun second (placeRun first run one) two =
      placeRun (first ∪ second) run (runSafe_comp first second run one two) := by
  apply Step.Run.eq_of_word_eq
  rw [Step.Run.word_cast, placeRun_word, placeRun_word, placeRun_word, List.map_map]
  apply List.map_congr_left
  intro event member
  exact placeEvent_comp first second event

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement.runSafe_comp
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement.placeRun_comp
