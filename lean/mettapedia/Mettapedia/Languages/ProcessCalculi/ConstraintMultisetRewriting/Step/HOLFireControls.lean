import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFireSpecialization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFrameEncodingControls

/-! # A loaded update consumes one occurrence and creates another

The same constructed model also supplies the frame and knowledge contracts.
Returning the original store is rejected, and the raw sentinel remains absent.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLFireControls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Logic.HOL.IndexedCarrier.Controls (family)
open HOLFrameEncoding.Controls (frame maps)
open HOLOccurrenceCoding
open MeTTaCalculus.OccurrenceCommits (Commit fire)

def commit : Commit Nat Unit := { taken := {0}, kept := ∅, made := {1}, queries := [] }

theorem actual_update : fire ({0} : Finset Nat) commit = {1} := by decide +kernel

theorem loaded_controls (other : TypeFamilySemantics.OperatorFamilies.{0})
    (prior : TypeFamilySemantics.Assignment.{0}) :
    ∃ (actual : HOL.HenkinModel.{0,0,1} AtomicTy Symbol)
      (frames : HOLFrameCoding.Coding actual Bool family maps) (occurrences : Coding actual Nat),
      HOLExactSpecialization.Agreement actual frame frames ∧
      actual.constDen HOLLoadedFire.symbol (finiteValue actual occurrences {0})
        (finiteValue actual occurrences {0}) (finiteValue actual occurrences {1}) = finiteValue actual occurrences {1} ∧
      actual.constDen HOLLoadedFire.symbol (finiteValue actual occurrences {0})
        (finiteValue actual occurrences {0}) (finiteValue actual occurrences {1}) ≠ finiteValue actual occurrences {0} ∧
      ¬(actual.constDen HOLLoadedFire.symbol (finiteValue actual occurrences {0})
        (finiteValue actual occurrences {0}) (finiteValue actual occurrences {1}) (occurrences.symm none)).down := by
  obtain ⟨actual, same, full, equations⟩ := HOLFrameDomains.loaded_model_exists Bool family maps Nat other prior
  let frames := (HOLFrameCoding.initialCoding (Obj := Bool) (Tm := family) (Hom := maps) Nat other prior).changeModel actual same
  let occurrences := changeModel (initialCoding Bool family maps Nat other prior) actual same
  have image := HOLFireSpecialization.fire_function actual occurrences full equations ({0} : Finset Nat) commit
  rw [actual_update] at image
  refine ⟨actual, frames, occurrences,
    HOLExactSpecialization.agreement_of_cache actual frame frames full equations, image, ?_, ?_⟩
  · intro wrong
    have sets := finiteValue_injective actual occurrences (image.symm.trans wrong)
    have member : 1 ∈ ({0} : Finset Nat) := sets ▸ (Finset.mem_singleton_self 1)
    simp at member
  · intro claimed
    have point := congrArg ULift.down (congrFun image (occurrences.symm none))
    exact invalid_absent actual occurrences {1} ((iff_of_eq point).mp claimed)

#print axioms actual_update
#print axioms loaded_controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLFireControls
