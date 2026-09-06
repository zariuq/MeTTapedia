import Mettapedia.GSLT.LanguageDef.BiformTheory
import Mettapedia.GSLT.LanguageDef.BiformCertificateBoundary
import Mettapedia.GSLT.LanguageDef.InstitutionConsequence
import Mettapedia.GSLT.LanguageDef.ClosedTheorySemanticTarget
import Mettapedia.Logic.HOL.HenkinInstitutionCanary

/-!
# A nontrivial Henkin/GSLT biform-theory discriminator

The same retained Boolean transition is paired with two native Henkin
theories.  A signature map collapses two source constants to one target
constant, and a biform route proves that the event meaning commutes with this
logical translation.

The negative control keeps the executable transition but removes the source
axiom.  The proposed meaning assignment is then unsound, because the source
equation has a separating Henkin model.  Execution therefore does not
manufacture mathematical admission.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.HOLHenkinBiformCanary

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.InstitutionConsequence
open Mettapedia.GSLT.LanguageDef.BiformTheory
open Mettapedia.GSLT.LanguageDef.BiformCertificateBoundary
open Mettapedia.GSLT.LanguageDef.ClosedTheorySemanticTarget
open Mettapedia.Logic
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.HenkinInstitution
open Mettapedia.Logic.HOL.HenkinInstitution.Canary

/-! ## One proof-relevant executable event -/

/-- A tiny machine whose sole primitive event changes `false` to `true`. -/
def booleanGSLT : GSLT where
  Term := Bool
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := fun source target => source = false ∧ target = true
  rewrites_resp_left := by
    intro source source' target equivalent step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equivalent
    subst target'
    exact step

/-- The retained occurrence type has exactly one constructor. -/
inductive BooleanEvidence : Bool → Bool → Type where
  | advance : BooleanEvidence false true

def booleanStepEvidence : StepEvidence booleanGSLT where
  Evidence := BooleanEvidence
  erases_iff := by
    intro source target
    constructor
    · rintro ⟨evidence⟩
      cases evidence
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨BooleanEvidence.advance⟩

def booleanAlgorithm : ProofRelevantGSLT :=
  ⟨booleanGSLT, booleanStepEvidence⟩

def advanceEvent : booleanAlgorithm.Event :=
  ⟨false, true, BooleanEvidence.advance⟩

theorem advanceEvent_erases_to_step :
    booleanGSLT.Step advanceEvent.source advanceEvent.target :=
  booleanStepEvidence.erase advanceEvent.evidence

/-! ## Native logical theories and their meaning assignments -/

abbrev henkinConsequence := consequenceProjection (institution Unit)

def sourceLogical : PiInstitution.TheoryObject henkinConsequence :=
  PiInstitution.generatedTheory henkinConsequence sourceSignature
    {sourceEquation}

def targetLogical : PiInstitution.TheoryObject henkinConsequence :=
  PiInstitution.generatedTheory henkinConsequence targetSignature ∅

def sourceMeaning (_event : booleanAlgorithm.Event) :
    ClosedFormula TwoConstants :=
  sourceEquation

def targetMeaning (_event : booleanAlgorithm.Event) :
    ClosedFormula OneConstant :=
  targetEquation

theorem sourceMeaning_sound :
    MeaningSound henkinConsequence sourceLogical booleanAlgorithm
      sourceMeaning := by
  intro event
  exact PiInstitution.derives_of_mem henkinConsequence sourceSignature
    (Set.mem_singleton sourceEquation)

theorem targetMeaning_sound :
    MeaningSound henkinConsequence targetLogical booleanAlgorithm
      targetMeaning := by
  intro event
  exact targetEquation_valid

def sourceBiform : BiformTheory henkinConsequence where
  logical := sourceLogical
  algorithm := booleanAlgorithm
  meaning := sourceMeaning
  meaning_sound := sourceMeaning_sound

def targetBiform : BiformTheory henkinConsequence where
  logical := targetLogical
  algorithm := booleanAlgorithm
  meaning := targetMeaning
  meaning_sound := targetMeaning_sound

/-! ## A meaning-preserving biform route -/

/-- Semantic consequence transports the whole generated source theory, not
only its generating axiom. -/
def collapseLogical :
    PiInstitution.TheoryHom sourceLogical targetLogical where
  mapSignature := collapse
  preserves := by
    intro formula theoremhood
    change formula ∈
      henkinConsequence.consequence sourceSignature {sourceEquation} at theoremhood
    have translated := henkinConsequence.translation collapse
      {sourceEquation}
      (Set.mem_image_of_mem
        (henkinConsequence.sentence.map collapse) theoremhood)
    have premiseImage :
        Set.image (henkinConsequence.sentence.map collapse)
            {sourceEquation} = {targetEquation} := by
      ext translatedFormula
      simp only [Set.mem_image]
      constructor
      · rintro ⟨sourceFormula, rfl, rfl⟩
        exact translate_sourceEquation
      · rintro rfl
        exact ⟨sourceEquation, rfl, translate_sourceEquation⟩
    rw [premiseImage] at translated
    have targetEquationTheorem :
        targetEquation ∈
          henkinConsequence.consequence targetSignature ∅ :=
      targetEquation_valid
    have singletonSubset :
        ({targetEquation} : Set (ClosedFormula OneConstant)) ⊆
          henkinConsequence.consequence targetSignature ∅ := by
      intro formula member
      rw [Set.mem_singleton_iff] at member
      subst formula
      exact targetEquationTheorem
    have expanded := PiInstitution.derives_mono henkinConsequence
      targetSignature singletonSubset translated
    exact PiInstitution.derives_cut henkinConsequence targetSignature expanded

/-- The event survives operationally and its native meaning commutes with the
non-injective logical signature map. -/
def collapseBiform : BiformTheory.Hom sourceBiform targetBiform where
  logical := collapseLogical
  operational := Translation.id booleanAlgorithm
  meaning_natural := by
    intro event
    change henkinConsequence.sentence.map collapse sourceEquation =
      targetEquation
    exact translate_sourceEquation

theorem translated_advance_meaning_is_admitted :
    targetBiform.meaning
        (collapseBiform.operational.mapEvent advanceEvent) ∈
      targetBiform.logical.theory.1 :=
  BiformTheory.Hom.mapped_event_meaning collapseBiform advanceEvent

/-! ## Negative control: an algorithm cannot certify its own meaning -/

def emptySourceLogical : PiInstitution.TheoryObject henkinConsequence :=
  PiInstitution.generatedTheory henkinConsequence sourceSignature ∅

/-- The machine still runs when the proposed native meaning is not a theorem. -/
theorem executable_but_source_meaning_not_sound :
    ¬MeaningSound henkinConsequence emptySourceLogical booleanAlgorithm
      sourceMeaning := by
  intro sound
  apply sourceEquation_not_valid
  exact sound advanceEvent

/-! ## Theoremhood does not determine proof identity -/

/-- The canonical thin calculus collapses the proof fibre of the target
equation to at most one inhabitant. -/
theorem targetEquation_thinProofFibre_subsingleton :
    Subsingleton
      (ProofFibre (thinDiscipline targetLogical) targetEquation) :=
  thinProofFibre_subsingleton targetLogical targetEquation

/-- The proof-relevant tagged calculus retains two distinct witnesses of the
same independently valid target equation. -/
theorem targetEquation_taggedProofs_distinct :
    taggedFalseProof targetLogical targetEquation targetEquation_valid ≠
      taggedTrueProof targetLogical targetEquation targetEquation_valid :=
  taggedProofs_distinct targetLogical targetEquation targetEquation_valid

/-- The concrete retained event therefore has a native tagged proof of its
Henkin meaning before any executable certificate representation is chosen. -/
theorem advanceEvent_targetMeaningProofFibre_nonempty :
    Nonempty (EventMeaningProofFibre targetBiform
      (PiInstitution.ProofCalculus.tagged henkinConsequence) advanceEvent) :=
  eventMeaningProofFibre_nonempty targetBiform
    (PiInstitution.ProofCalculus.tagged henkinConsequence) advanceEvent

/-- No checker with a single raw token can exactly retain the two native
proofs of the concrete target equation. -/
theorem targetEquation_unit_certificate_boundary_is_empty
    (checker : KernelAuthority.Checker (ClosedFormula OneConstant) Unit) :
    IsEmpty (CertificateEquivalence checker
      ((taggedDiscipline targetLogical).proofSystem ())) :=
  no_unit_certificate_equivalence_for_tagged_theorem
    targetLogical targetEquation targetEquation_valid checker

#print axioms advanceEvent_erases_to_step
#print axioms sourceMeaning_sound
#print axioms targetMeaning_sound
#print axioms collapseLogical
#print axioms translated_advance_meaning_is_admitted
#print axioms executable_but_source_meaning_not_sound
#print axioms targetEquation_thinProofFibre_subsingleton
#print axioms targetEquation_taggedProofs_distinct
#print axioms advanceEvent_targetMeaningProofFibre_nonempty
#print axioms targetEquation_unit_certificate_boundary_is_empty

end Mettapedia.GSLT.LanguageDef.HOLHenkinBiformCanary
