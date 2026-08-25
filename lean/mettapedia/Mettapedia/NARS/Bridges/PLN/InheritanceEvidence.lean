import Mettapedia.NARS.Bridges.PLN.EvidenceTranslation
import Mettapedia.NARS.Logic.Inheritance
import Mettapedia.PLN.Evidence.EvidenceQuantale

/-!
# PLN evidence readout for NARS dual inheritance

The NARS inheritance room retains four finite witness sets: positive and
negative, extensional and intensional.  This bridge maps their cardinalities
to PLN `BinaryEvidence`, and then to the shared numerical NARS truth-value
view.  The four witness sets remain primary; the two counts are a readout.
-/

namespace Mettapedia.NARS.Bridges.PLN.InheritanceEvidence

open Mettapedia.NARS.Logic.Inheritance
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.NARS.TruthFunctions
open scoped ENNReal

universe u v w

variable {Atom : Type u} {Obj : Type v} {Attr : Type w}
variable [DecidableEq Obj] [DecidableEq Attr]

/-- Binary-evidence readout for a NARS inheritance statement. -/
def evidence
    (frame : Frame Atom Obj Attr) (subject predicate : Term Atom) : BinaryEvidence where
  pos :=
    (((frame.positiveExtensionalWitnesses subject predicate).card
        + (frame.positiveIntensionalWitnesses subject predicate).card : ℕ) : ℝ≥0∞)
  neg :=
    (((frame.negativeExtensionalWitnesses subject predicate).card
        + (frame.negativeIntensionalWitnesses subject predicate).card : ℕ) : ℝ≥0∞)

/-- Numerical NARS truth-value view induced by the binary-evidence readout. -/
noncomputable def truthValue
    (frame : Frame Atom Obj Attr) (subject predicate : Term Atom) : TV :=
  Mettapedia.NARS.Bridges.PLN.EvidenceTranslation.BinaryEvidence.toNARSTV
    (evidence frame subject predicate)

theorem evidence_neg_eq_zero_of_inherits
    (frame : Frame Atom Obj Attr) {subject predicate : Term Atom}
    (inherits : frame.Inherits subject predicate) :
    (evidence frame subject predicate).neg = 0 := by
  have extensional :
      frame.negativeExtensionalWitnesses subject predicate = ∅ :=
    frame.negativeExtensionalWitnesses_eq_empty_of_extensionalInherits inherits.1
  have intensional :
      frame.negativeIntensionalWitnesses subject predicate = ∅ :=
    frame.negativeIntensionalWitnesses_eq_empty_of_intensionalInherits inherits.2
  simp [evidence, extensional, intensional]

theorem evidence_pos_eq_two_of_reflexive_atom
    (frame : Frame Atom Obj Attr) (atom : Atom)
    (extensionSingleton : (frame.atomExtension atom).card = 1)
    (intensionSingleton : (frame.atomIntension atom).card = 1) :
    (evidence frame (.atom atom) (.atom atom)).pos = 2 := by
  simp [evidence, Frame.positiveExtensionalWitnesses,
    Frame.positiveIntensionalWitnesses, Finset.inter_self]
  rw [extensionSingleton, intensionSingleton]
  norm_num

namespace Examples

open Mettapedia.NARS.Logic.Inheritance.Examples

theorem penguin_to_bird_negative_evidence_zero :
    (evidence ontologyFrame penguin bird).neg = 0 :=
  evidence_neg_eq_zero_of_inherits ontologyFrame penguin_inherits_bird

theorem bird_to_flyer_negative_evidence_is_two :
    (evidence ontologyFrame bird flyer).neg = 2 := by
  have extensional :
      ontologyFrame.negativeExtensionalWitnesses bird flyer = {Creature.pingu} := by
    decide
  have intensional :
      ontologyFrame.negativeIntensionalWitnesses bird flyer = {Feature.flies} := by
    decide
  simp [evidence, extensional, intensional]

end Examples

#print axioms evidence_neg_eq_zero_of_inherits
#print axioms Examples.bird_to_flyer_negative_evidence_is_two

end Mettapedia.NARS.Bridges.PLN.InheritanceEvidence
