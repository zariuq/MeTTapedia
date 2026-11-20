import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationRunTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.StepSpan

/-!
# OSLF observations of actual transported typed publications

Contextual state isomorphisms form a bisimulation for the publication step
containing all certified source applications. Both directions use the actual
application transport and its derived result comparison. The projections
from its relation graph are therefore open by the existing OSLF theorem.

Possibility and successor necessity are preserved for invariant observations.
Neither raw-code invariance, counts of candidate presentations, predecessor
lifting, nor closure of an arbitrary restricted program is inferred here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.CoherenceModal

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open LogicOverTheStep LogicOverTheStep.StepSpan LogicOverTheStep.ModalComparison
open FragmentsOfTheStep.TransitionMaps
open Mettapedia.OSLF.Framework.DerivedModalities

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  (levels : LevelModel rules L) (O : Type) [DecidableEq O]

def Related (source target : State rules O) : Prop := Nonempty (PlainIso levels source target)

theorem bisimulation : IsBisimulation
    (Succ (realizationStep levels O)) (Succ (realizationStep levels O)) (Related levels O) := by
  constructor
  · rintro source target result ⟨comparison⟩ ⟨candidate, accepted, rfl⟩
    let moved := RunTransport.application comparison candidate
    let valid := (RunTransport.admits comparison candidate).mpr accepted
    exact ⟨(realizationStep levels O).result moved valid, ⟨moved, valid, rfl⟩,
      ⟨RunTransport.after comparison candidate accepted⟩⟩
  · rintro source target result ⟨comparison⟩ ⟨candidate, accepted, rfl⟩
    let moved := RunTransport.application comparison.symm candidate
    let valid := (RunTransport.admits comparison.symm candidate).mpr accepted
    exact ⟨(realizationStep levels O).result moved valid, ⟨moved, valid, rfl⟩,
      ⟨(RunTransport.after comparison.symm candidate accepted).symm⟩⟩

theorem projections_open :
    FunctionalBisimulation
      (graphStep (Succ (realizationStep levels O)) (Succ (realizationStep levels O)) (Related levels O))
      (Succ (realizationStep levels O)) (fun pair => pair.val.1) ∧
    FunctionalBisimulation
      (graphStep (Succ (realizationStep levels O)) (Succ (realizationStep levels O)) (Related levels O))
      (Succ (realizationStep levels O)) (fun pair => pair.val.2) :=
  isBisimulation_iff_projections_open.mp (bisimulation levels O)

variable {levels O}

theorem possibility {source target : State rules O} (comparison : PlainIso levels source target)
    (observation : State rules O → Prop)
    (invariant : ∀ {first second : State rules O}, PlainIso levels first second →
      (observation first ↔ observation second)) :
    derivedDiamond (firingSpan (realizationStep levels O)) observation source ↔
      derivedDiamond (firingSpan (realizationStep levels O)) observation target := by
  rw [firing_diamond_eq]
  exact diamond_iff_of_bisimulation (bisimulation levels O)
    (fun _ _ related => by obtain ⟨witness⟩ := related; exact invariant witness) ⟨comparison⟩

theorem successor_necessity {source target : State rules O} (comparison : PlainIso levels source target)
    (observation : State rules O → Prop)
    (invariant : ∀ {first second : State rules O}, PlainIso levels first second →
      (observation first ↔ observation second)) :
    derivedForwardBox (firingSpan (realizationStep levels O)) observation source ↔
      derivedForwardBox (firingSpan (realizationStep levels O)) observation target := by
  rw [firing_forwardBox_eq]
  exact forwardBox_iff_of_bisimulation (bisimulation levels O)
    (fun _ _ related => by obtain ⟨witness⟩ := related; exact invariant witness) ⟨comparison⟩

omit [DecidableEq O] in
theorem occurrence_invariant (occurrence : O) {source target : State rules O}
    (comparison : PlainIso levels source target) :
    occurrence ∈ source.present ↔ occurrence ∈ target.present := by rw [comparison.present]

theorem occurrence_possible {source target : State rules O} (comparison : PlainIso levels source target)
    (occurrence : O) :
    derivedDiamond (firingSpan (realizationStep levels O)) (fun state => occurrence ∈ state.present) source ↔
      derivedDiamond (firingSpan (realizationStep levels O)) (fun state => occurrence ∈ state.present) target :=
  possibility comparison _ (occurrence_invariant occurrence)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.CoherenceModal

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.CoherenceModal.bisimulation
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.CoherenceModal.projections_open
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.CoherenceModal.possibility
