import Mettapedia.OSLF.Framework.GauthierOEISModKPruning
import Mettapedia.OSLF.Framework.GSLTWorldModel
import Mettapedia.OSLF.Framework.InferenceQuantale

/-!
# Gauthier WM-PLN Neural Spine

This file connects the certified Gauthier OEIS analyses to the generic
GSLT/WM-PLN evidence layer, and states the decoder-mask theorem used by the
symbolic-neural interface.
-/

namespace Mettapedia.OSLF.Framework.GauthierWMPLNNeuralSpine

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierProperties
open Mettapedia.OSLF.Framework.GauthierOEISPruningSoundness
open Mettapedia.OSLF.Framework.GauthierOEISModKPruning
open Mettapedia.OSLF.Framework.GSLTEvidence
open Mettapedia.OSLF.Framework.GSLTWorldModel
open Mettapedia.OSLF.Framework.InferenceQuantale
open Mettapedia.PLN.Evidence.EvidenceQuantale

abbrev PLNEvidence := Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence

/-! ## Certified properties as WM-PLN evidence queries -/

/-- The certified semantic properties currently exported to the neural search
interface.  The `modk` constructor is configurable; parity is the `k = 2`
instance but remains listed separately because the sealed sign/parity analyzer
already feeds the Lane A runtime. -/
inductive CertifiedPropertyKind where
  | sign
  | parity
  | modk (k : Nat)

/-- A certified property query is tied to one observed target term. -/
structure CertifiedPropertyQuery where
  kind : CertifiedPropertyKind
  obs : ObservedTerm

namespace CertifiedPropertyQuery

def sign (obs : ObservedTerm) : CertifiedPropertyQuery :=
  ⟨.sign, obs⟩

def parity (obs : ObservedTerm) : CertifiedPropertyQuery :=
  ⟨.parity, obs⟩

def modk (k : Nat) (obs : ObservedTerm) : CertifiedPropertyQuery :=
  ⟨.modk k, obs⟩

/-- The semantic predicate that a certified property query asks about a
candidate program. -/
def holds (q : CertifiedPropertyQuery) (p : Prog) : Prop :=
  match q.kind with
  | .sign => SignCompatible p q.obs
  | .parity => ParityCompatible p q.obs
  | .modk k => ModKCompatible k p q.obs

end CertifiedPropertyQuery

/-- Classical decidability packages certified properties as `DecProp` queries
for the generic GSLT world-model layer. -/
noncomputable def certifiedPropertyDecProp (q : CertifiedPropertyQuery) : DecProp Prog where
  property := q.holds
  dec := Classical.decPred q.holds

/-- The WM-PLN evidence assignment for certified properties of Gauthier
program ensembles. -/
noncomputable def certifiedPropertyEvidence
    (W : Multiset Prog) (q : CertifiedPropertyQuery) : PLNEvidence := by
  classical
  exact ⟨↑(Multiset.countP q.holds W),
         ↑(Multiset.countP (fun p => ¬ q.holds p) W)⟩

theorem certifiedPropertyEvidence_add
    (W₁ W₂ : Multiset Prog) (q : CertifiedPropertyQuery) :
    certifiedPropertyEvidence (W₁ + W₂) q =
      certifiedPropertyEvidence W₁ q + certifiedPropertyEvidence W₂ q := by
  classical
  apply Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.ext'
  · simp [certifiedPropertyEvidence,
      Multiset.countP_add,
      Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.hplus_def]
  · simp [certifiedPropertyEvidence,
      Multiset.countP_add,
      Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.hplus_def]

theorem certifiedPropertyEvidence_zero (q : CertifiedPropertyQuery) :
    certifiedPropertyEvidence (0 : Multiset Prog) q = 0 := by
  classical
  apply Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.ext' <;>
    simp [certifiedPropertyEvidence]

noncomputable def certifiedPropertyEvidenceAssignment :
    GSLTEvidenceAssignment (Multiset Prog) CertifiedPropertyQuery PLNEvidence where
  extract := certifiedPropertyEvidence
  extract_add := certifiedPropertyEvidence_add
  extract_zero := certifiedPropertyEvidence_zero

/-- The same assignment viewed through the inference-quantale shadow interface. -/
noncomputable def certifiedPropertyEvidenceShadow :
    GSLTEvidenceAssignment (Multiset Prog) CertifiedPropertyQuery PLNEvidence :=
  shadow certifiedPropertyEvidenceAssignment (AddMonoidHom.id PLNEvidence)

theorem certifiedPropertyEvidenceShadow_id
    (W : Multiset Prog) (q : CertifiedPropertyQuery) :
    certifiedPropertyEvidenceShadow.extract W q =
      certifiedPropertyEvidenceAssignment.extract W q :=
  shadow_id certifiedPropertyEvidenceAssignment W q

/-- Every certified property evidence assignment factors through the canonical
profile object supplied by `GSLTEvidence`. -/
theorem certifiedPropertyEvidence_factors_through_profile
    (W : Multiset Prog) (q : CertifiedPropertyQuery) :
    certifiedPropertyEvidenceAssignment.extract W q =
      (canonicalAssignment CertifiedPropertyQuery PLNEvidence).extract
        (certifiedPropertyEvidenceAssignment.toProfileHom W) q :=
  factors_through_canonical certifiedPropertyEvidenceAssignment W q

theorem certifiedPropertyEvidence_singleton_of_holds
    {p : Prog} {q : CertifiedPropertyQuery} (h : q.holds p) :
    certifiedPropertyEvidenceAssignment.extract ({p} : Multiset Prog) q = ⟨1, 0⟩ := by
  classical
  apply Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.ext' <;>
    simp [certifiedPropertyEvidenceAssignment, certifiedPropertyEvidence, ← Multiset.cons_zero, h]

theorem certifiedPropertyEvidence_singleton_of_refutes
    {p : Prog} {q : CertifiedPropertyQuery} (h : ¬ q.holds p) :
    certifiedPropertyEvidenceAssignment.extract ({p} : Multiset Prog) q = ⟨0, 1⟩ := by
  classical
  apply Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.ext' <;>
    simp [certifiedPropertyEvidenceAssignment, certifiedPropertyEvidence, ← Multiset.cons_zero, h]

/-- A proof-carrying PLN truth-value/evidence object for a certified semantic
property.  Its carrier is the existing `BinaryEvidence`; the proof records that
this singleton query contributes one positive and no negative evidence. -/
structure CertifiedPropertyTruthValue where
  evidence : PLNEvidence
  certain : evidence = ⟨1, 0⟩

noncomputable def certifiedPropertyTruthValue
    {p : Prog} {q : CertifiedPropertyQuery} (h : q.holds p) :
    CertifiedPropertyTruthValue where
  evidence := certifiedPropertyEvidenceAssignment.extract ({p} : Multiset Prog) q
  certain := certifiedPropertyEvidence_singleton_of_holds h

theorem reproducesAt_sign_evidence_certain {p : Prog} {obs : ObservedTerm}
    (h : ReproducesAt p obs) :
    certifiedPropertyEvidenceAssignment.extract ({p} : Multiset Prog)
      (CertifiedPropertyQuery.sign obs) = ⟨1, 0⟩ := by
  apply certifiedPropertyEvidence_singleton_of_holds
  rcases h with ⟨fuel, st', heval⟩
  exact Seal.certified_sign_sound obs.seed_nonneg heval

theorem reproducesAt_parity_evidence_certain {p : Prog} {obs : ObservedTerm}
    (h : ReproducesAt p obs) :
    certifiedPropertyEvidenceAssignment.extract ({p} : Multiset Prog)
      (CertifiedPropertyQuery.parity obs) = ⟨1, 0⟩ := by
  apply certifiedPropertyEvidence_singleton_of_holds
  rcases h with ⟨fuel, st', heval⟩
  exact Seal.certified_parity_sound heval

theorem reproducesAt_modk_evidence_certain {k : Nat} {p : Prog} {obs : ObservedTerm}
    (h : ReproducesAt p obs) :
    certifiedPropertyEvidenceAssignment.extract ({p} : Multiset Prog)
      (CertifiedPropertyQuery.modk k obs) = ⟨1, 0⟩ := by
  apply certifiedPropertyEvidence_singleton_of_holds
  rcases h with ⟨fuel, st', heval⟩
  exact certified_modk_sound (k := k) heval

/-! ## Consolidated certified semantic decoder mask -/

/-- A candidate is semantically incompatible with the target if sign/parity or
one requested mod-k residue check excludes at least one observed target term. -/
def CertifiedSemanticIncompatible
    (ks : List Nat) (p : Prog) (target : List ObservedTerm) : Prop :=
  AnalysisIncompatible p target ∨ ∃ k, k ∈ ks ∧ ModKIncompatible k p target

/-- The real certified semantic decoder mask: candidates are kept exactly
when the certified sign/parity/mod-k checks do not exclude them. -/
def CertifiedSemanticDecoderMask
    (ks : List Nat) (target : List ObservedTerm) (p : Prog) : Prop :=
  ¬ CertifiedSemanticIncompatible ks p target

/-- Soundness of the certified semantic decoder mask: any program that truly
reproduces the target is kept by the constrained hypothesis space. -/
theorem certified_semantic_decoder_mask_sound
    {ks : List Nat} {target : List ObservedTerm} {p : Prog}
    (hrep : Reproduces p target) :
    CertifiedSemanticDecoderMask ks target p := by
  intro hbad
  rcases hbad with hsp | hmod
  · exact (certified_property_pruning_admissible hsp) hrep
  · rcases hmod with ⟨k, _hmem, hbadk⟩
    exact (certified_modk_pruning_admissible (k := k) hbadk) hrep

/-! ## Non-vacuity canaries -/

theorem one_not_analysis_incompatible :
    ¬ AnalysisIncompatible oneProg oneTarget := by
  intro hbad
  rcases hbad with ⟨obs, hmem, hobs⟩
  simp [oneTarget] at hmem
  subst obs
  rcases hobs with hsign | hparity
  · exact hsign one_sign_compatible_with_one_observation
  · exact hparity one_parity_compatible_with_one_observation

theorem one_not_mod3_incompatible :
    ¬ ModKIncompatible 3 oneProg oneTarget := by
  intro hbad
  rcases hbad with ⟨obs, hmem, hobs⟩
  simp [oneTarget] at hmem
  subst obs
  exact hobs one_mod3_compatible_with_one_observation

theorem zero_masked_by_certifiedSemanticMask :
    ¬ CertifiedSemanticDecoderMask [3] oneTarget zeroProg := by
  intro hmask
  apply hmask
  exact Or.inl
    ⟨observedOneAt0, by simp [oneTarget], Or.inr zero_incompatible_with_one_observation⟩

theorem one_kept_by_certifiedSemanticMask :
    CertifiedSemanticDecoderMask [3] oneTarget oneProg := by
  intro hbad
  rcases hbad with hsp | hmod
  · exact one_not_analysis_incompatible hsp
  · rcases hmod with ⟨k, hmem, hbadk⟩
    simp at hmem
    subst k
    exact one_not_mod3_incompatible hbadk

end Mettapedia.OSLF.Framework.GauthierWMPLNNeuralSpine
