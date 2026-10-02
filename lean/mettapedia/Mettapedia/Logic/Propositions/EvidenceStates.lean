import Mettapedia.Logic.Propositions.InformationStates
import Mettapedia.Logic.Propositions.Comparison
import Mettapedia.PLN.WorldModel.WorldModelAdditive

/-!
# Evidence for sentences from observed scenarios

An information state leaves scenarios open and so settles sentences or leaves
them open.  A graded version counts instead: each observed scenario is one unit
of evidence for a sentence it verifies and one unit against a sentence it does
not.  This is the additive world model of PLN
(`Mettapedia.PLN.WorldModel.WorldModelAdditive`) over bags of observed
scenarios, with `BinaryEvidence` as the pair of positive and negative support.

* `Interpretation.observation`, `Interpretation.evidence`: the evidence one
  observed scenario, and a bag of them, gives for a sentence.
  `Interpretation.evidenceWorldModel` is the resulting PLN world model, and
  pooling observations adds evidence (`evidence_add`).
* **Evidence attaches to senses**: the evidence for a sentence is a function of
  its primary intension (`factors_primary_evidence`), hence of its Fregean
  proposition (`factors_fregean_evidence`).  This is the graded form of
  Chalmers's argument that the objects of credence must be as fine as senses
  ("Frege's Puzzle and the Objects of Credence", *Mind* 120, 2011).  The
  morning-star example shows that evidence is not a function of the Russellian
  proposition (`MorningStar.evidence_not_factors_russellian`).
* **Settled means no evidence against**: the evidence against a sentence is
  zero exactly when every observed scenario verifies it
  (`neg_evidence_eq_zero_iff`), which is what the information state of the
  observed scenarios settles (`settledTrue_iff_neg_evidence_eq_zero`).
* **A priori consequences are never counted against**: if the observed
  scenarios verify a base, a sentence scrutable from the base receives no
  negative evidence (`neg_evidence_eq_zero_of_scrutableFrom`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Propositions

open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.WorldModel.PLNWorldModelAdditive
open Mettapedia.GSLT.Core.NonFactorization
open scoped Classical

universe uS uW uD uN uP

/-- One unit of evidence for or against, according to whether the scenario is
in the set. -/
noncomputable def unitEvidence {S : Type uS} (scenario : S) (intension : Set S) : BinaryEvidence :=
  if scenario ∈ intension then ⟨1, 0⟩ else ⟨0, 1⟩

/-- The evidence a bag of observed scenarios gives for a set of scenarios. -/
noncomputable def evidenceForIntension {S : Type uS} (observed : Multiset S) (intension : Set S) :
    BinaryEvidence :=
  additiveExtension unitEvidence observed intension

namespace Interpretation

variable {S : Type uS} {W : Type uW} {D : Type uD} {N : Type uN} {P : Type uP}
variable (I : Interpretation S W D N P)

/-- The evidence one observed scenario gives for a sentence. -/
noncomputable def observation (scenario : S) (sentence : Sentence N P) : BinaryEvidence :=
  unitEvidence scenario (I.primary sentence)

/-- The evidence a bag of observed scenarios gives for a sentence. -/
noncomputable def evidence (observed : Multiset S) (sentence : Sentence N P) : BinaryEvidence :=
  additiveExtension I.observation observed sentence

/-- The PLN world model of observed scenarios. -/
@[instance_reducible]
noncomputable def evidenceWorldModel :
    letI : EvidenceType (Multiset S) := multisetEvidenceType S
    BinaryWorldModel (Multiset S) (Sentence N P) :=
  worldModelOfAtomicEvidence I.observation

/-- Pooling observations adds evidence. -/
theorem evidence_add (first second : Multiset S) (sentence : Sentence N P) :
    I.evidence (first + second) sentence = I.evidence first sentence + I.evidence second sentence :=
  additiveExtension_add I.observation first second sentence

theorem evidence_cons (scenario : S) (observed : Multiset S) (sentence : Sentence N P) :
    I.evidence (scenario ::ₘ observed) sentence =
      I.observation scenario sentence + I.evidence observed sentence :=
  genAdditiveExtension_cons I.observation scenario observed sentence

theorem evidence_eq_evidenceForIntension (observed : Multiset S) (sentence : Sentence N P) :
    I.evidence observed sentence = evidenceForIntension observed (I.primary sentence) :=
  rfl

/-- **Evidence attaches to senses.** -/
theorem factors_primary_evidence (observed : Multiset S) :
    Factors I.primary (I.evidence observed) :=
  ⟨evidenceForIntension observed, fun _ => rfl⟩

theorem factors_fregean_evidence (observed : Multiset S) :
    Factors I.fregean (I.evidence observed) :=
  Factors.of_coarsening (fine := I.fregean) (coarsen := FregeanProposition.scenarios)
    (fun sentence => (I.scenarios_fregean sentence).symm) (I.factors_primary_evidence observed)

theorem neg_observation_eq_zero_iff (scenario : S) (sentence : Sentence N P) :
    (I.observation scenario sentence).neg = 0 ↔ scenario ∈ I.primary sentence := by
  unfold observation unitEvidence
  by_cases verifies : scenario ∈ I.primary sentence
  · simp [verifies]
  · simp [verifies]

/-- **No evidence against means every observed scenario verifies the
sentence.** -/
theorem neg_evidence_eq_zero_iff (observed : Multiset S) (sentence : Sentence N P) :
    (I.evidence observed sentence).neg = 0 ↔
      ∀ scenario ∈ observed, scenario ∈ I.primary sentence := by
  induction observed using Multiset.induction_on with
  | empty =>
    have zero : I.evidence 0 sentence = 0 := additiveExtension_zero I.observation sentence
    simp [zero]
  | cons scenario rest ih =>
    rw [I.evidence_cons, BinaryEvidence.hplus_def]
    simp only [add_eq_zero, Multiset.mem_cons, forall_eq_or_imp]
    rw [I.neg_observation_eq_zero_iff, ih]

/-- The information state of the observed scenarios settles a sentence exactly
when there is no evidence against it. -/
theorem settledTrue_iff_neg_evidence_eq_zero (observed : Multiset S) (sentence : Sentence N P) :
    (I.informationWorldModel.extract {scenario | scenario ∈ observed} sentence).settledTrue ↔
      (I.evidence observed sentence).neg = 0 :=
  (I.neg_evidence_eq_zero_iff observed sentence).symm

/-- **A priori consequences are never counted against.** -/
theorem neg_evidence_eq_zero_of_scrutableFrom {base : Set (Sentence N P)}
    {sentence : Sentence N P} (scrutable : I.ScrutableFrom base sentence)
    {observed : Multiset S}
    (verifiesBase : ∀ scenario ∈ observed, ∀ member ∈ base, scenario ∈ I.primary member) :
    (I.evidence observed sentence).neg = 0 :=
  (I.neg_evidence_eq_zero_iff observed sentence).mpr fun scenario inObserved =>
    I.scrutableFrom_iff.mp scrutable scenario (verifiesBase scenario inObserved)

end Interpretation

end Mettapedia.Logic.Propositions
