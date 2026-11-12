import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentRunContextQueries
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentStateGroupoid

/-!
# Placing an actual dependent helper firing in a larger occurrence context

The state's typed label map supplies the rows of the added occurrences.
Already present rows may be shared. A sufficient placement license separates
fresh outputs, resources that the context retains, and newly matching query
rows. Admission and the complete resulting state are derived from those local
conditions. No admission conclusion is a field of the license.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open MeTTaCalculus.OccurrenceCommits (fire fire_union_frame)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O]

def place (extra : Finset O) (state : State rules O) : State rules O :=
  { state with present := state.present ∪ extra }

def firing (extra : Finset O) {state : State rules O} (candidate : HelperFiring levels O state) :
    HelperFiring levels O (place extra state) := ⟨candidate.helpers, candidate.data⟩

def QueryClear (extra : Finset O) {state : State rules O} (candidate : HelperFiring levels O state) : Prop :=
  ∀ (observer : Context rules) (solution : observer ⟶ candidate.helpers.frame),
    (frames levels).Models solution candidate.toFiring.information →
      ∀ query ∈ candidate.toFiring.queries,
        ContextQueries.NewClear query state.present extra candidate.toFiring.row solution

structure Safe (extra : Finset O) {state : State rules O} (candidate : HelperFiring levels O state) : Prop where
  retained : Disjoint candidate.toFiring.taken.toFinset extra
  fresh : Disjoint candidate.toFiring.made.toFinset extra
  queries : QueryClear extra candidate

theorem information_kept (extra : Finset O) {state : State rules O}
    (candidate : HelperFiring levels O state) :
    (firing extra candidate).toFiring.information = candidate.toFiring.information := rfl

theorem admits (extra : Finset O) {state : State rules O} (candidate : HelperFiring levels O state)
    (accepted : (helperStep levels O).Admits candidate)
    (fresh : Disjoint candidate.toFiring.made.toFinset extra) (clear : QueryClear extra candidate) :
    (helperStep levels O).Admits (firing extra candidate) := by
  obtain ⟨shapes, enabled, solvable, holds⟩ := accepted
  refine ⟨shapes, ?_, solvable, ?_⟩
  · exact enabled.frame_of_positive rfl fresh
  · intro observer solution solved
    obtain ⟨guards, queries⟩ := holds observer solution solved
    refine ⟨guards, fun query member => ?_⟩
    exact (ContextQueries.holds_union_iff (clear observer solution solved query member)).mpr
      (queries query member)

theorem result (extra : Finset O) {state : State rules O} (candidate : HelperFiring levels O state)
    (accepted : (helperStep levels O).Admits candidate) (safe : Safe extra candidate) :
    (helperStep levels O).result (firing extra candidate) (admits extra candidate accepted safe.fresh safe.queries) =
      place extra ((helperStep levels O).result candidate accepted) := by
  change (⟨candidate.helpers.frame, candidate.toFiring.information,
    fire (state.present ∪ extra) (candidate.toFiring.selection.commit (T := Unit)),
    relabel candidate.toFiring.row candidate.toFiring.makes accepted.1.2.2.2.2⟩ : State rules O) =
      ⟨candidate.helpers.frame, candidate.toFiring.information,
        fire state.present (candidate.toFiring.selection.commit (T := Unit)) ∪ extra,
        relabel candidate.toFiring.row candidate.toFiring.makes accepted.1.2.2.2.2⟩
  rw [fire_union_frame safe.retained]

def placeIso (extra : Finset O) {source target : State rules O} (comparison : PlainIso levels source target) :
    PlainIso levels (place extra source) (place extra target) where
  frame := comparison.frame
  knowledge := comparison.knowledge
  present := congrArg (· ∪ extra) comparison.present
  label := comparison.label

theorem placeIso_refl (extra : Finset O) (state : State rules O) :
    placeIso extra (PlainIso.refl (levels := levels) state) = PlainIso.refl (place extra state) := by
  apply RunStateGroupoid.iso_ext
  rfl

theorem placeIso_trans (extra : Finset O) {source middle target : State rules O}
    (first : PlainIso levels source middle) (second : PlainIso levels middle target) :
    placeIso extra (first.trans second) = (placeIso extra first).trans (placeIso extra second) := by
  apply RunStateGroupoid.iso_ext
  rfl

theorem safe_empty {state : State rules O} (candidate : HelperFiring levels O state) :
    Safe ∅ candidate := by
  refine ⟨Finset.disjoint_empty_right _, Finset.disjoint_empty_right _, ?_⟩
  intro observer solution solved query member occurrence inside
  exact False.elim (Finset.notMem_empty occurrence inside)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement.admits
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement.result
