import Mettapedia.Logic.AbstractInheritancePLNBridge
import Mettapedia.Logic.AbstractInheritanceOverlap
import Mettapedia.Logic.AbstractInheritanceStampedWitness
import Mettapedia.Logic.ConceptOntology.Examples

/-!
# Abstract Inheritance Paired Canaries

These canaries exercise one ontology fragment through both sides of the new
inheritance architecture:

- the WM-PLN crisp extensional view
- the abstract interpretation induced from that view
- the finite NARS frame rebuilt from the same abstract interpretation
-/

namespace Mettapedia.Logic.AbstractInheritanceCanary

open Mettapedia.Logic
open Mettapedia.Logic.ConceptOntology
open Mettapedia.Logic.ConceptOntology.Examples
open Mettapedia.Logic.AbstractInheritance
open Mettapedia.Logic.NARSInheritance

instance : Fintype Creature where
  elems := {Creature.tweety, Creature.pingu, Creature.plane}
  complete x := by
    cases x <;> simp

instance : Fintype Concept where
  elems := {Concept.bird, Concept.penguin, Concept.fly}
  complete x := by
    cases x <;> simp

/-- The abstract inheritance interpretation induced by the WM-PLN example. -/
noncomputable def wmInterpretation : Interpretation Concept Creature Concept :=
  MembershipQueryBuilder.abstractInterpretationAt
    (State := ToyState) gate toyWM membershipBuilder

/-- The finite NARS frame reconstructed from the same abstract interpretation. -/
noncomputable def wmNARSFrame : NARSInheritance.Frame Concept Creature Concept :=
  wmInterpretation.toNARSFrame

theorem wm_penguin_bird_inherits :
    wmInterpretation.Inherits Concept.penguin Concept.bird := by
  exact (MembershipQueryBuilder.abstractInterpretationAt_inherits_iff
    (State := ToyState) (Obj := Creature) (Con := Concept)
    (Srt := ToySort) (Query := ToyQueryFamily)
    gate toyWM membershipBuilder Concept.penguin Concept.bird).2
      penguin_extensionally_inherits_bird

theorem wm_bird_fly_not_inherits :
    ¬ wmInterpretation.Inherits Concept.bird Concept.fly := by
  intro h
  exact bird_not_extensionally_inherits_fly <|
    (MembershipQueryBuilder.abstractInterpretationAt_inherits_iff
      (State := ToyState) (Obj := Creature) (Con := Concept)
      (Srt := ToySort) (Query := ToyQueryFamily)
      gate toyWM membershipBuilder Concept.bird Concept.fly).1 h

theorem wmNARS_penguin_bird_inherits :
    wmNARSFrame.Inherits (.atom Concept.penguin) (.atom Concept.bird) := by
  simpa [wmNARSFrame, wmInterpretation] using
    (Interpretation.toNARSFrame_inherits_atom_iff
      (I := wmInterpretation) Concept.penguin Concept.bird).2
      wm_penguin_bird_inherits

theorem wmNARS_bird_fly_not_inherits :
    ¬ wmNARSFrame.Inherits (.atom Concept.bird) (.atom Concept.fly) := by
  intro h
  exact wm_bird_fly_not_inherits <|
    (Interpretation.toNARSFrame_inherits_atom_iff
      (I := wmInterpretation) Concept.bird Concept.fly).1
      (by simpa [wmNARSFrame, wmInterpretation] using h)

theorem wm_penguin_bird_abstract_negative_evidence_zero :
    (wmInterpretation.finiteInheritanceEvidence Concept.penguin Concept.bird).neg = 0 := by
  simpa [wmInterpretation,
    MembershipQueryBuilder.abstractFiniteInheritanceEvidenceAt] using
    (MembershipQueryBuilder.abstractFiniteInheritanceEvidenceAt_neg_eq_zero_of_crispExtensionalInherits
      (State := ToyState) (Obj := Creature) (Con := Concept)
      (Srt := ToySort) (Query := ToyQueryFamily)
      gate toyWM membershipBuilder
      (c := Concept.penguin) (d := Concept.bird)
      penguin_extensionally_inherits_bird)

theorem wmNARS_penguin_bird_evidence_eq_abstract :
    wmNARSFrame.inheritanceEvidence (.atom Concept.penguin) (.atom Concept.bird) =
      wmInterpretation.finiteInheritanceEvidence Concept.penguin Concept.bird := by
  simpa [wmNARSFrame, wmInterpretation] using
    (Interpretation.toNARSFrame_inheritanceEvidence_atom_eq_finiteInheritanceEvidence
      (I := wmInterpretation) Concept.penguin Concept.bird)

theorem wmNARS_penguin_bird_negative_evidence_zero :
    (wmNARSFrame.inheritanceEvidence (.atom Concept.penguin) (.atom Concept.bird)).neg = 0 := by
  rw [wmNARS_penguin_bird_evidence_eq_abstract]
  exact wm_penguin_bird_abstract_negative_evidence_zero

theorem wmNARS_penguin_bird_stampedEvidence_eq_abstract :
    wmNARSFrame.inheritanceStampedEvidence (.atom Concept.penguin) (.atom Concept.bird) =
      wmInterpretation.finiteInheritanceStampedEvidence Concept.penguin Concept.bird := by
  simpa [wmNARSFrame, wmInterpretation] using
    (Interpretation.toNARSFrame_inheritanceStampedEvidence_atom_eq_finiteInheritanceStampedEvidence
      (I := wmInterpretation) Concept.penguin Concept.bird)

theorem wmNARS_bird_fly_stampedEvidence_eq_abstract :
    wmNARSFrame.inheritanceStampedEvidence (.atom Concept.bird) (.atom Concept.fly) =
      wmInterpretation.finiteInheritanceStampedEvidence Concept.bird Concept.fly := by
  simpa [wmNARSFrame, wmInterpretation] using
    (Interpretation.toNARSFrame_inheritanceStampedEvidence_atom_eq_finiteInheritanceStampedEvidence
      (I := wmInterpretation) Concept.bird Concept.fly)

theorem wm_penguin_bird_negative_stamp_empty :
    (DualConcept.negativeStampedEvidence
      (wmInterpretation.meaning Concept.penguin)
      (wmInterpretation.meaning Concept.bird)).stamp = ∅ := by
  exact Interpretation.finiteInheritanceStampedEvidence_negative_stamp_eq_empty_of_inherits
    (I := wmInterpretation) wm_penguin_bird_inherits

theorem wm_bird_fly_positive_negative_stampDisjoint :
    StampedBinaryEvidence.StampDisjoint
      (DualConcept.positiveStampedEvidence
        (wmInterpretation.meaning Concept.bird)
        (wmInterpretation.meaning Concept.fly))
      (DualConcept.negativeStampedEvidence
        (wmInterpretation.meaning Concept.bird)
        (wmInterpretation.meaning Concept.fly)) := by
  exact DualConcept.positive_negative_stampDisjoint
    (wmInterpretation.meaning Concept.bird)
    (wmInterpretation.meaning Concept.fly)

theorem wm_penguin_bird_overlap_merge_eq_stampedEvidence :
    DualConcept.correctedMerge
      (DualConcept.positiveStampedEvidence
        (wmInterpretation.meaning Concept.penguin)
        (wmInterpretation.meaning Concept.bird))
      (DualConcept.negativeStampedEvidence
        (wmInterpretation.meaning Concept.penguin)
        (wmInterpretation.meaning Concept.bird)) =
      wmInterpretation.finiteInheritanceStampedEvidence
        Concept.penguin Concept.bird := by
  simpa [wmInterpretation,
    Interpretation.finiteInheritanceStampedEvidence] using
    (DualConcept.correctedMerge_positive_negative_eq_finiteInheritanceStampedEvidence
      (wmInterpretation.meaning Concept.penguin)
      (wmInterpretation.meaning Concept.bird))

theorem wm_penguin_bird_overlap_merge_evidence_eq_abstract :
    (DualConcept.correctedMerge
      (DualConcept.positiveStampedEvidence
        (wmInterpretation.meaning Concept.penguin)
        (wmInterpretation.meaning Concept.bird))
      (DualConcept.negativeStampedEvidence
        (wmInterpretation.meaning Concept.penguin)
        (wmInterpretation.meaning Concept.bird))).evidence =
      wmInterpretation.finiteInheritanceEvidence
        Concept.penguin Concept.bird := by
  simpa [wmInterpretation,
    Interpretation.finiteInheritanceEvidence] using
    (DualConcept.correctedMerge_positive_negative_evidence_eq_finiteInheritanceEvidence
      (wmInterpretation.meaning Concept.penguin)
      (wmInterpretation.meaning Concept.bird))

theorem penguin_bird_same_fact_through_wm_and_nars :
    MembershipQueryBuilder.crispExtensionalInheritsAt
        (State := ToyState) gate toyWM membershipBuilder
        Concept.penguin Concept.bird ∧
      wmInterpretation.Inherits Concept.penguin Concept.bird ∧
      wmNARSFrame.Inherits (.atom Concept.penguin) (.atom Concept.bird) := by
  exact ⟨penguin_extensionally_inherits_bird, wm_penguin_bird_inherits,
    wmNARS_penguin_bird_inherits⟩

theorem bird_fly_same_noninheritance_through_wm_and_nars :
    ¬ MembershipQueryBuilder.crispExtensionalInheritsAt
        (State := ToyState) gate toyWM membershipBuilder
        Concept.bird Concept.fly ∧
      ¬ wmInterpretation.Inherits Concept.bird Concept.fly ∧
      ¬ wmNARSFrame.Inherits (.atom Concept.bird) (.atom Concept.fly) := by
  exact ⟨bird_not_extensionally_inherits_fly, wm_bird_fly_not_inherits,
    wmNARS_bird_fly_not_inherits⟩

end Mettapedia.Logic.AbstractInheritanceCanary
