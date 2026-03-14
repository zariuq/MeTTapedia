import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Semantics
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.MeTTaIL.DeclReduces
import Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Types
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Soundness
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine
import Mettapedia.OSLF.Framework.RewriteSystem
import Mettapedia.OSLF.Framework.RhoInstance
import Mettapedia.OSLF.Framework.DerivedModalities
import Mettapedia.OSLF.Framework.CategoryBridge
import Mettapedia.OSLF.Framework.FULLStatus
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.GeneratedTyping
import Mettapedia.OSLF.Framework.SynthesisBridge
import Mettapedia.OSLF.Framework.ToposReduction
import Mettapedia.OSLF.Framework.LambdaInstance
import Mettapedia.OSLF.Framework.PetriNetInstance
import Mettapedia.OSLF.Framework.TinyMLInstance
import Mettapedia.OSLF.Framework.MeTTaMinimalInstance
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.ConstructorFibration
import Mettapedia.OSLF.Framework.ModalEquivalence
import Mettapedia.OSLF.Framework.ObservationalQuotient
import Mettapedia.OSLF.Framework.DerivedTyping
import Mettapedia.OSLF.Framework.PLNSelectorGSLT
import Mettapedia.OSLF.Framework.BeckChevalleyOSLF
import Mettapedia.OSLF.Framework.ToposTOGLBridge
import Mettapedia.OSLF.Framework.NTTClaimTracker
import Mettapedia.OSLF.Framework.PaperSection12Examples
import Mettapedia.OSLF.NativeType.Construction
import Mettapedia.Languages.MeTTa.OSLFCore.Premises
import Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef
import Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageTests
import Mettapedia.OSLF.Framework.MeTTaFullLegacyInstance
import Mettapedia.OSLF.Framework.MeTTaLegacyToNTT
import Mettapedia.OSLF.Framework.OSLFNTTWMBridge
import Mettapedia.OSLF.Framework.OSLFNTTTheoryClosure
import Mettapedia.OSLF.Framework.ModalSubobjectBridge
import Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure
import Mettapedia.OSLF.Framework.IdentityEvidenceTransfer
import Mettapedia.OSLF.Framework.QuantaleCoherence
import Mettapedia.OSLF.Framework.WMProbabilityEmbedding
import Mettapedia.OSLF.Framework.HypercubeTemporalGSLTFunctor
import Mettapedia.OSLF.Formula
import Mettapedia.OSLF.Decidability
import Mettapedia.OSLF.QuantifiedFormula
import Mettapedia.OSLF.QuantifiedFormula2
import Mettapedia.Logic.OSLFDistinctionGraph
import Mettapedia.Logic.OSLFDistinctionGraphWeighted
import Mettapedia.Logic.OSLFDistinctionGraphWM
import Mettapedia.Logic.OSLFDistinctionGraphEntropy
import Mettapedia.Logic.OSLFKripkeBridge
import Mettapedia.Logic.OSLFImageFinite
import Mettapedia.OSLF.Framework.PiRhoCanonicalBridge
import Mettapedia.OSLF.Framework.SubstitutabilityTheorem1
import Mettapedia.OSLF.PathMap

/-!
# OSLF Core Entry Point

Sorry-free core entry point for OSLF + GSLT + premise-aware rewriting pipeline.

This file keeps the core stack and re-exports one canonical π→ρ pred-domain
endpoint for downstream OSLF consumers.
-/

namespace Mettapedia.OSLF

export Mettapedia.Languages.MeTTa.OSLFCore.Premises (
  space0Atomspace
  space0EqEntries
  space0TypeEntries
  space0Entries
  mkCanonicalSpace
  space0Pattern
  spaceEntriesOfPattern?
  atomspaceOfPattern?
  eqnLookupTuples
  noEqnLookupTuples
  neqTuples
  typeOfTuples
  notTypeOfTuples
  castTuples
  notCastTuples
  groundedCallTuples
  noGroundedCallTuples
)

export Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef (
  mettaFullLegacy
  mettaFullLegacyOSLF
  mettaFullLegacyGalois
  mettaFullLegacyRelEnv
  mettaFull
  mettaFullOSLF
  mettaFullGalois
  mettaFullRelEnv
)

export Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageTests (
  coded_string_concat_normalForm_shape
)

export Mettapedia.OSLF.Framework.MeTTaFullInstance (
  mettaFullLegacy_pathOrder
  mettaFullLegacy_checker_sat_to_pathSemClosed_commDi_bc_graph
  mettaFullLegacy_checker_sat_to_pathSemClosed_commDi_bc_graph_auto
  mettaFullLegacySpecAtomCheck
  mettaFullLegacySpecAtomSem
  mettaFullLegacy_checkLangUsing_sat_sound_specAtoms
  mettaFullLegacy_checkLang_sat_sound_specAtoms
  mettaFull_pathOrder
  mettaFull_checker_sat_to_pathSemClosed_commDi_bc_graph
  mettaFull_checker_sat_to_pathSemClosed_commDi_bc_graph_auto
  mettaFullSpecAtomCheck
  mettaFullSpecAtomSem
  mettaFull_checkLangUsing_sat_sound_specAtoms
  mettaFull_checkLang_sat_sound_specAtoms
)

export Mettapedia.OSLF.Framework.MeTTaToNTT (
  mettaEvidenceToNT
  mettaEvidenceToNT_hom
  mettaSemE
  mettaSemE_atom
  mettaSemE_atom_revision
  mettaFormulaToNT
  mettaFormulaToNT_snd
  mettaFormulaToNT_atom
  mettaFormulaToNT_hom
)

export Mettapedia.OSLF.Framework.OSLFNTTWMBridge (
  oslf_atom_ntt_wm_triangle
  oslf_atom_ntt_wm_triangle_categorical
  oslf_formula_ntt_evidence_component
  oslf_dia_formula_graph_witness_transport
  oslf_dia_formula_ntt_graph_witness_transport
  oslf_formula_ntt_graph_triangle
  oslf_formula_ntt_graph_triangle_categorical
)

export Mettapedia.OSLF.Framework.OSLFNTTTheoryClosure (
  OSLFTheoryStep
  OSLFTheoryStepStar
  FormulaEndpointBridge
  formulaEndpointBridge_of_oslf_formula_ntt_graph_triangle
  FormulaCategoricalEndpointBridge
  formulaCategoricalEndpointBridge_of_oslf_formula_ntt_graph_triangle
  WMEvidenceObligation
  WMEvidenceConsequenceRuleOn
  OSLFNTTWMEvidenceInterface
  OSLFNTTWMEvidenceInterface.stepStar_sound
  OSLFNTTWMEvidenceInterface.to_strengthInterface
  WMStrengthObligation
  OSLFNTTWMInterface
  OSLFNTTWMInterface.stepStar_sound
  wmConsequenceRuleOn_of_oslfTheoryStep
  wmConsequenceRuleOn_of_oslfTheoryStepStar
  wmEvidenceConsequenceRuleOn_of_oslfTheoryStep
  wmEvidenceConsequenceRuleOn_of_oslfTheoryStepStar
  StepEvidenceMonotoneFragment
  StepEvidenceMonotoneControlledFragment
  ControlledStepPolicy
  StepEvidenceControlledByPolicy
  StepEvidenceControlledByPolicy.toAssumptionFragment
  semE_step_mono_of_atom_step_mono
  semE_step_mono_imp_of
  semE_step_mono_dia_of_successor_inclusion
  semE_step_mono_box_of_predecessor_inclusion
  semE_step_mono_controlled_of_atom_step_mono
  semE_step_mono_of_policy
  semEState
  semEState_step_evidence_mono
  semEFragmentEvidenceInterface
  semEPolicyEvidenceInterface
  semE_fragment_formulaCategoricalEndpoint_step
  semE_fragment_formulaCategoricalEndpoint_stepStar
  semE_fragment_formulaCategoricalEndpoint_stepStar_of_policy
  semE_fragment_evidenceRuleOn_of_formulaCategoricalEndpoint_stepStar
  semE_fragment_evidenceRuleOn_of_formulaCategoricalEndpoint_stepStar_of_policy
)

export Mettapedia.OSLF.Framework.ModalSubobjectBridge (
  modalFiberOfPatternPred
  modalSubobjectOfPatternPred
  modalSubobjectAsFiber
  modalSubobjectAsFiber_eq_modalFiber
  modalFiber_mem_iff
  modalSubobject_mem_iff
  modalFiber_map_mem
  modalSubobject_subst_map_mem
  ModalSubobjectControlledPolicy
  modalSubobject_commDi_bc_graph_endpoint_of_policy
  modalSubobject_policy_semE_step_mono
  modalSubobject_commDi_beckChevalley_of_pathSemLiftPkg
  modalSubobject_commDi_bc_graph_endpoint_of_pathSemLiftPkg
  mettaFullLegacy_modalSubobject_commDi_bc_graph_endpoint
  mettaFull_modalSubobject_commDi_bc_graph_endpoint
)

export Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure (
  CanonicalClosureContext
  CanonicalModalSquare
  CanonicalHyperSquare
  CanonicalFormulaArgs
  CanonicalGoalArgs
  CanonicalTransportGoalArgs
  oslf_ntt_wm_step_sound
  oslf_ntt_wm_star_sound
  canonicalEvidenceObligation_compact
  canonicalEvidenceConsequenceRuleOn_compact
  canonicalEvidenceConsequenceRuleOn_compact_of_goal
  canonicalEvidenceConsequenceRuleOn_compact_of_goal_canary
  canonicalConsequenceRuleOn_compact
  canonicalConsequenceRuleOn_compact_of_goal
  canonicalConsequenceRuleOn_compact_fixpoint
  canonicalConsequenceRuleOn_compact_fixpoint_of_goal
  canonical_rulePack_transport_pack_and_fixpoint_endpoint_compact
  canonical_rulePack_transport_pack_and_fixpoint_endpoint_of_goal
  canonical_prop12_transport_pack_and_fixpoint_endpoint_compact
  canonical_prop12_transport_pack_and_fixpoint_endpoint_of_goal
  canonical_rulePack_transport_pack_and_fixpoint_endpoint_of_transportGoal
  canonical_prop12_transport_pack_and_fixpoint_endpoint_of_transportGoal
  canonical_rulePack_transport_piSigma_and_fixpoint_of_transportGoal
  canonical_prop12_transport_piSigma_and_fixpoint_of_transportGoal
)

export Mettapedia.OSLF.Framework.PiRhoCanonicalBridge (
  piRho_coreMain_canonical_contract_end_to_end
  rhoCoreCanonicalSCQuotRelOn
  rhoDerivedCanonicalSCQuotRelOn
  imageFinite_rhoCoreCanonicalSCQuotRelOn
  predFinite_rhoCoreCanonicalSCQuotRelOn
  imageFinite_rhoDerivedCanonicalSCQuotRelOn
  predFinite_rhoDerivedCanonicalSCQuotRelOn
  hm_iff_fullBisim_rhoCoreCanonicalSCQuotRelOn
  hm_iff_fullBisim_rhoDerivedCanonicalSCQuotRelOn
  hm_iff_fullBisim_rhoCoreCanonicalSCQuotRelOn_pair_canary
  hm_iff_fullBisim_rhoDerivedCanonicalSCQuotRelOn_pair_canary
  hm_scoped_coreSC_edge_preservation_canary
  hm_scoped_derivedSC_edge_preservation_canary
)

export Mettapedia.OSLF.Framework.PaperSection12Examples (
  section12_worked_examples_bundle
)

export Mettapedia.OSLF.Framework.IdentityEvidenceTransfer (
  IdentityAtomLayerConfig
  atomSemBase
  atomSemWithIdentity
  sem_withIdentity_disabled_iff
  checkLangUsing_sat_sound_withIdentity_unused
  identity_semantic_transfer_endpoint
)

export Mettapedia.OSLF.Framework.QuantaleCoherence (
  sourceWeight
  targetWeight
  map_weakness_sourceWeight
  map_weakness_targetWeight
  mapTerm_reachable_of_reachable
  language_quantale_coherence_bundle
  language_quantale_coherence_bundle_atom
  hypercube_forward_quantale_coherence_bundle
)

/-- CoreMain-facing canonical π→ρ semantic contract endpoint. -/
abbrev coreMain_piRho_canonical_contract :=
  @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.piRho_coreMain_canonical_contract_end_to_end

/-- Canonical projection API for downstream users: consume the contract record
and project endpoint/HM capabilities directly. -/
theorem coreMain_piRho_contract_projection_api
    {N : Finset String}
    (x : Mettapedia.Languages.ProcessCalculi.PiCalculus.Name)
    (P : Mettapedia.Languages.ProcessCalculi.PiCalculus.Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Mettapedia.Languages.ProcessCalculi.PiCalculus.Name)
    (Pr : Mettapedia.Languages.ProcessCalculi.PiCalculus.Process)
    (n v : String)
    (hobs : N ⊆ P.freeNames)
    (hfresh : Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingFresh P) :
    Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.CalcPreludeLanguageMorphismSemanticTransferParamAtomPredDomain
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh
    ∧
    (∃
      _ :
        Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
          Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.FiniteSubrelation
            Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoCoreStarRel,
      True)
    ∧
    (∃
      _ :
        Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
          Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.FiniteSubrelation
            Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoDerivedStarRel,
      True)
    ∧
    (∀
      (S :
        Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.FiniteSubrelation
          Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoCoreStarRel)
      (I : Mettapedia.OSLF.Formula.AtomSem)
      {p q : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      Mettapedia.Logic.OSLFKSUnificationSketch.OSLFObsEq S.rel I p q →
      Mettapedia.Logic.OSLFKSUnificationSketch.Bisimilar S.rel p q)
    ∧
    (∀ (I : Mettapedia.OSLF.Formula.AtomSem)
      {p q : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      Mettapedia.Logic.OSLFKSUnificationSketch.OSLFObsEq
        Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoCoreCanonicalRel I p q →
      Mettapedia.Logic.OSLFKSUnificationSketch.Bisimilar
        Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoCoreCanonicalRel p q) := by
  let C :=
    coreMain_piRho_canonical_contract
      (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hobs hfresh
  exact ⟨C.endpoint, ⟨C.reachable_coreStar_subrel, trivial⟩,
    ⟨C.reachable_derivedStar_subrel, trivial⟩, C.hm_converse_coreStar_subrel,
    C.hm_converse_coreCanonical⟩

/-- CoreMain-facing canonical category/topos bridge endpoint alias. -/
abbrev coreMain_hypercube_fuzzy_bridge :=
  @Mettapedia.OSLF.Framework.CategoryBridge.hypercube_fuzzy_canonical_bridge

/-- Strict NTT theorem-number parity unresolved-count endpoint.
Use this instead of OSLF-facing parity counters when making NTT-paper claims. -/
abbrev coreMain_ntt_strict_parity_remaining_count :=
  Mettapedia.OSLF.Framework.NTTClaimTracker.nttRemainingCount

/-- Full NTT-paper parity is closed in the strict theorem-number keyed tracker. -/
theorem coreMain_ntt_strict_parity_closed :
    coreMain_ntt_strict_parity_remaining_count = 0 := by
  exact Mettapedia.OSLF.Framework.NTTClaimTracker.nttRemainingCount_zero

/-- CoreMain-facing canonical Native Type translation endpoint for Π/Ω
preservation across theory morphisms. -/
theorem coreMain_nativeType_piOmega_translation_endpoint
    {L₁ L₂ : Mettapedia.CategoryTheory.LambdaTheories.LambdaTheory}
    (F : Mettapedia.OSLF.NativeType.TheoryMorphism L₁ L₂)
    (S : L₁.Obj)
    (types : Set (L₁.fibration.Sub S)) :
    F.mapPred (Mettapedia.OSLF.NativeType.piType L₁ S types) =
      Mettapedia.OSLF.NativeType.piType L₂ (F.mapSort S) (F.mapPred '' types)
    ∧
    (F.mapNatType (Mettapedia.OSLF.NativeType.NatType.full (L := L₁) S)).pred =
      (Mettapedia.OSLF.NativeType.NatType.full (L := L₂) (F.mapSort S)).pred := by
  exact F.piOmega_translation_endpoint S types

/-- CoreMain-facing Native Type translation endpoint for Π/Ω/Prop implication
preservation across theory morphisms. -/
theorem coreMain_nativeType_piOmegaProp_translation_endpoint
    {L₁ L₂ : Mettapedia.CategoryTheory.LambdaTheories.LambdaTheory}
    (F : Mettapedia.OSLF.NativeType.TheoryMorphism L₁ L₂)
    (S : L₁.Obj)
    (types : Set (L₁.fibration.Sub S))
    (φ ψ : L₁.fibration.Sub S) :
    F.mapPred (Mettapedia.OSLF.NativeType.piType L₁ S types) =
      Mettapedia.OSLF.NativeType.piType L₂ (F.mapSort S) (F.mapPred '' types)
    ∧
    (F.mapNatType (Mettapedia.OSLF.NativeType.NatType.full (L := L₁) S)).pred =
      (Mettapedia.OSLF.NativeType.NatType.full (L := L₂) (F.mapSort S)).pred
    ∧
    F.mapPred (Mettapedia.OSLF.NativeType.implType L₁ S φ ψ) =
      Mettapedia.OSLF.NativeType.implType L₂ (F.mapSort S) (F.mapPred φ) (F.mapPred ψ) := by
  exact F.piOmegaProp_translation_endpoint S types φ ψ

/-- CoreMain-facing Native Type translation endpoint for Π/Σ/Ω/Prop implication
preservation across theory morphisms. -/
theorem coreMain_nativeType_piSigmaOmegaProp_translation_endpoint
    {L₁ L₂ : Mettapedia.CategoryTheory.LambdaTheories.LambdaTheory}
    (F : Mettapedia.OSLF.NativeType.TheoryMorphism L₁ L₂)
    (S : L₁.Obj)
    (types : Set (L₁.fibration.Sub S))
    (φ ψ : L₁.fibration.Sub S) :
    F.mapPred (Mettapedia.OSLF.NativeType.piType L₁ S types) =
      Mettapedia.OSLF.NativeType.piType L₂ (F.mapSort S) (F.mapPred '' types)
    ∧
    F.mapPred (Mettapedia.OSLF.NativeType.sigmaType L₁ S types) =
      Mettapedia.OSLF.NativeType.sigmaType L₂ (F.mapSort S) (F.mapPred '' types)
    ∧
    (F.mapNatType (Mettapedia.OSLF.NativeType.NatType.full (L := L₁) S)).pred =
      (Mettapedia.OSLF.NativeType.NatType.full (L := L₂) (F.mapSort S)).pred
    ∧
    F.mapPred (Mettapedia.OSLF.NativeType.implType L₁ S φ ψ) =
      Mettapedia.OSLF.NativeType.implType L₂ (F.mapSort S) (F.mapPred φ) (F.mapPred ψ) := by
  exact F.piSigmaOmegaProp_translation_endpoint S types φ ψ

/-- CoreMain-facing bundled endpoint: Π/Ω/Prop translation together with
nontrivial constructor-category cross-sort transport composition. -/
theorem coreMain_nativeType_piOmegaProp_constructor_transport_bundle
    {L₁ L₂ : Mettapedia.CategoryTheory.LambdaTheories.LambdaTheory}
    (F : Mettapedia.OSLF.NativeType.TheoryMorphism L₁ L₂)
    (S : L₁.Obj)
    (types : Set (L₁.fibration.Sub S))
    (φ ψ : L₁.fibration.Sub S)
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    {A B C : Mettapedia.OSLF.NativeType.ConstructorNatType lang}
    (f : Mettapedia.OSLF.NativeType.ConstructorNatTypeHom lang A B)
    (g : Mettapedia.OSLF.NativeType.ConstructorNatTypeHom lang B C) :
    (F.mapPred (Mettapedia.OSLF.NativeType.piType L₁ S types) =
      Mettapedia.OSLF.NativeType.piType L₂ (F.mapSort S) (F.mapPred '' types))
    ∧
    ((F.mapNatType (Mettapedia.OSLF.NativeType.NatType.full (L := L₁) S)).pred =
      (Mettapedia.OSLF.NativeType.NatType.full (L := L₂) (F.mapSort S)).pred)
    ∧
    (F.mapPred (Mettapedia.OSLF.NativeType.implType L₁ S φ ψ) =
      Mettapedia.OSLF.NativeType.implType L₂ (F.mapSort S) (F.mapPred φ) (F.mapPred ψ))
    ∧
    Nonempty (Mettapedia.OSLF.NativeType.ConstructorNatTypeHom lang A C) := by
  exact F.piOmegaProp_with_constructor_transport_bundle S types φ ψ lang f g

/-- CoreMain-facing composition-stability endpoint for the bundled
Π/Ω/Prop + constructor transport contract. -/
theorem coreMain_nativeType_comp_piOmegaProp_constructor_transport_bundle
    {L₁ L₂ L₃ : Mettapedia.CategoryTheory.LambdaTheories.LambdaTheory}
    (F : Mettapedia.OSLF.NativeType.TheoryMorphism L₁ L₂)
    (G : Mettapedia.OSLF.NativeType.TheoryMorphism L₂ L₃)
    (S : L₁.Obj)
    (types : Set (L₁.fibration.Sub S))
    (φ ψ : L₁.fibration.Sub S)
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    {A B C : Mettapedia.OSLF.NativeType.ConstructorNatType lang}
    (f : Mettapedia.OSLF.NativeType.ConstructorNatTypeHom lang A B)
    (g : Mettapedia.OSLF.NativeType.ConstructorNatTypeHom lang B C) :
    (((Mettapedia.OSLF.NativeType.TheoryMorphism.comp G F).mapPred
      (Mettapedia.OSLF.NativeType.piType L₁ S types)) =
      Mettapedia.OSLF.NativeType.piType L₃
        ((Mettapedia.OSLF.NativeType.TheoryMorphism.comp G F).mapSort S)
        (((Mettapedia.OSLF.NativeType.TheoryMorphism.comp G F).mapPred '' types)))
    ∧
    ((((Mettapedia.OSLF.NativeType.TheoryMorphism.comp G F).mapNatType
      (Mettapedia.OSLF.NativeType.NatType.full (L := L₁) S)).pred =
      (Mettapedia.OSLF.NativeType.NatType.full (L := L₃)
        ((Mettapedia.OSLF.NativeType.TheoryMorphism.comp G F).mapSort S)).pred))
    ∧
    (((Mettapedia.OSLF.NativeType.TheoryMorphism.comp G F).mapPred
      (Mettapedia.OSLF.NativeType.implType L₁ S φ ψ)) =
      Mettapedia.OSLF.NativeType.implType L₃
        ((Mettapedia.OSLF.NativeType.TheoryMorphism.comp G F).mapSort S)
        ((Mettapedia.OSLF.NativeType.TheoryMorphism.comp G F).mapPred φ)
        ((Mettapedia.OSLF.NativeType.TheoryMorphism.comp G F).mapPred ψ))
    ∧
    Nonempty (Mettapedia.OSLF.NativeType.ConstructorNatTypeHom lang A C) := by
  exact F.comp_piOmegaProp_with_constructor_transport_bundle G S types φ ψ lang f g

/-- CoreMain-facing canonical colax/lax Π/Prop rule-set endpoint for theory
translations. -/
theorem coreMain_nativeType_piProp_colax_rules_endpoint
    {L₁ L₂ : Mettapedia.CategoryTheory.LambdaTheories.LambdaTheory}
    (F : Mettapedia.OSLF.NativeType.TheoryMorphism L₁ L₂)
    (S : L₁.Obj) :
    F.PiPropColaxRuleSet S := by
  exact F.piProp_colax_rules S

/-- CoreMain-facing canonical colax/lax Π/Σ/Prop rule-set endpoint for theory
translations. -/
theorem coreMain_nativeType_piSigmaProp_colax_rules_endpoint
    {L₁ L₂ : Mettapedia.CategoryTheory.LambdaTheories.LambdaTheory}
    (F : Mettapedia.OSLF.NativeType.TheoryMorphism L₁ L₂)
    (S : L₁.Obj) :
    F.PiSigmaPropColaxRuleSet S := by
  exact F.piSigmaProp_colax_rules S

/-- CoreMain-facing identity-canary for the Native Type Π/Ω endpoint. -/
theorem coreMain_nativeType_id_piOmega_canary
    (L : Mettapedia.CategoryTheory.LambdaTheories.LambdaTheory)
    (S : L.Obj)
    (types : Set (L.fibration.Sub S)) :
    ((Mettapedia.OSLF.NativeType.TheoryMorphism.id L).mapPred
      (Mettapedia.OSLF.NativeType.piType L S types) =
        Mettapedia.OSLF.NativeType.piType L
          ((Mettapedia.OSLF.NativeType.TheoryMorphism.id L).mapSort S)
          ((Mettapedia.OSLF.NativeType.TheoryMorphism.id L).mapPred '' types))
    ∧
    (((Mettapedia.OSLF.NativeType.TheoryMorphism.id L).mapNatType
      (Mettapedia.OSLF.NativeType.NatType.full (L := L) S)).pred =
      (Mettapedia.OSLF.NativeType.NatType.full (L := L)
        ((Mettapedia.OSLF.NativeType.TheoryMorphism.id L).mapSort S)).pred) := by
  simpa using Mettapedia.OSLF.NativeType.TheoryMorphism.id_piOmega_translation_endpoint L S types

/-- CoreMain-facing identity-canary for the Native Type Π/Σ/Ω/Prop endpoint. -/
theorem coreMain_nativeType_id_piSigmaOmegaProp_canary
    (L : Mettapedia.CategoryTheory.LambdaTheories.LambdaTheory)
    (S : L.Obj)
    (types : Set (L.fibration.Sub S))
    (φ ψ : L.fibration.Sub S) :
    ((Mettapedia.OSLF.NativeType.TheoryMorphism.id L).mapPred
      (Mettapedia.OSLF.NativeType.piType L S types) =
        Mettapedia.OSLF.NativeType.piType L
          ((Mettapedia.OSLF.NativeType.TheoryMorphism.id L).mapSort S)
          ((Mettapedia.OSLF.NativeType.TheoryMorphism.id L).mapPred '' types))
    ∧
    ((Mettapedia.OSLF.NativeType.TheoryMorphism.id L).mapPred
      (Mettapedia.OSLF.NativeType.sigmaType L S types) =
        Mettapedia.OSLF.NativeType.sigmaType L
          ((Mettapedia.OSLF.NativeType.TheoryMorphism.id L).mapSort S)
          ((Mettapedia.OSLF.NativeType.TheoryMorphism.id L).mapPred '' types))
    ∧
    (((Mettapedia.OSLF.NativeType.TheoryMorphism.id L).mapNatType
      (Mettapedia.OSLF.NativeType.NatType.full (L := L) S)).pred =
      (Mettapedia.OSLF.NativeType.NatType.full (L := L)
        ((Mettapedia.OSLF.NativeType.TheoryMorphism.id L).mapSort S)).pred)
    ∧
    ((Mettapedia.OSLF.NativeType.TheoryMorphism.id L).mapPred
      (Mettapedia.OSLF.NativeType.implType L S φ ψ)) =
      Mettapedia.OSLF.NativeType.implType L
        ((Mettapedia.OSLF.NativeType.TheoryMorphism.id L).mapSort S)
        ((Mettapedia.OSLF.NativeType.TheoryMorphism.id L).mapPred φ)
        ((Mettapedia.OSLF.NativeType.TheoryMorphism.id L).mapPred ψ) := by
  simpa using
    Mettapedia.OSLF.NativeType.TheoryMorphism.id_piSigmaOmegaProp_translation_endpoint
      L S types φ ψ

/-- CoreMain-facing canonical representable Π/Σ transport endpoint routed
through the Prop-12 ΠΣ predicate-rule pack. -/
theorem coreMain_representable_patternPred_piSigma_transport_via_rulePack
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    (s : Mettapedia.OSLF.Framework.ConstructorCategory.LangSort lang)
    (seed : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (φ : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (hNat :
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
        lang s seed φ)
    (hPiSigmaPack :
      Mettapedia.OSLF.NativeType.PiSigmaPredicateRulePack
        (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang))
    {D : CategoryTheory.Functor
      (Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)) Type}
    (f :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s) ⟶ D)
    (χ ψ : CategoryTheory.Subfunctor D) :
    ((((Mettapedia.GSLT.Topos.presheafChangeOfBase
        (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)).directImage f)
        ((Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
          lang s seed φ hNat :
          CategoryTheory.Subfunctor
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj lang s)))
      ≤ ψ)
      ↔
      ((show CategoryTheory.Subfunctor
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj lang s)
          from Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
            lang s seed φ hNat)
      ≤ ((Mettapedia.GSLT.Topos.presheafChangeOfBase
        (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)).pullback f) ψ))
    ∧
    ((((Mettapedia.GSLT.Topos.presheafChangeOfBase
        (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)).pullback f) χ
      ≤
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
        lang s seed φ hNat)
      ↔
      (χ ≤
        ((Mettapedia.GSLT.Topos.presheafChangeOfBase
          (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)).universalImage f)
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
            lang s seed φ hNat))) := by
  exact
    Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_via_rulePack
      (lang := lang) (s := s) (seed := seed) (φ := φ) (hNat := hNat)
      (hPiSigmaPack := hPiSigmaPack)
      (f := f) (χ := χ) (ψ := ψ)

/-- CoreMain-facing canonical representable Π/Σ transport endpoint routed
through the Prop-12 ΠΣ predicate-rule pack. -/
theorem coreMain_representable_patternPred_piSigma_transport_via_prop12_pack
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    (s : Mettapedia.OSLF.Framework.ConstructorCategory.LangSort lang)
    (seed : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (φ : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (hNat :
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
        lang s seed φ)
    {D : CategoryTheory.Functor
      (Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)) Type}
    (f :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s) ⟶ D)
    (χ ψ : CategoryTheory.Subfunctor D) :
    ((((Mettapedia.GSLT.Topos.presheafChangeOfBase
        (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)).directImage f)
        ((Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
          lang s seed φ hNat :
          CategoryTheory.Subfunctor
            (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj lang s)))
      ≤ ψ)
      ↔
      ((show CategoryTheory.Subfunctor
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj lang s)
          from Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
            lang s seed φ hNat)
      ≤ ((Mettapedia.GSLT.Topos.presheafChangeOfBase
        (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)).pullback f) ψ))
    ∧
    ((((Mettapedia.GSLT.Topos.presheafChangeOfBase
        (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)).pullback f) χ
      ≤
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
        lang s seed φ hNat)
      ↔
      (χ ≤
        ((Mettapedia.GSLT.Topos.presheafChangeOfBase
          (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)).universalImage f)
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
            lang s seed φ hNat))) := by
  exact
    Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_via_prop12_pack
      (lang := lang) (s := s) (seed := seed) (φ := φ) (hNat := hNat)
      (f := f) (χ := χ) (ψ := ψ)

/-- CoreMain-facing packaged representable Π/Σ transport API (Σ-BC + Σ/Π
transport), routed through the Prop-12 predicate-fibration rule exports. -/
theorem coreMain_representable_patternPred_piSigma_transport_pack_via_rulePack
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    (s : Mettapedia.OSLF.Framework.ConstructorCategory.LangSort lang)
    (seed : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (φ : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (hNat :
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
        lang s seed φ)
    (hPiSigmaPack :
      Mettapedia.OSLF.NativeType.PiSigmaPredicateRulePack
        (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang))
    {D : CategoryTheory.Functor
      (Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)) Type}
    (f :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s) ⟶ D) :
    Mettapedia.OSLF.Framework.BeckChevalleyOSLF.RepresentablePiSigmaTransportPack
      (lang := lang) (s := s) (seed := seed) (φ := φ) (hNat := hNat) (f := f) := by
  exact
    Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_pack_via_rulePack
      (lang := lang) (s := s) (seed := seed) (φ := φ) (hNat := hNat)
      (hPiSigmaPack := hPiSigmaPack) (f := f)

/-- CoreMain-facing packaged representable Π/Σ transport API (Σ-BC + Σ/Π
transport), routed through the Prop-12 predicate-fibration rule exports. -/
theorem coreMain_representable_patternPred_piSigma_transport_pack
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    (s : Mettapedia.OSLF.Framework.ConstructorCategory.LangSort lang)
    (seed : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (φ : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (hNat :
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
        lang s seed φ)
    {D : CategoryTheory.Functor
      (Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)) Type}
    (f :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s) ⟶ D) :
    Mettapedia.OSLF.Framework.BeckChevalleyOSLF.RepresentablePiSigmaTransportPack
      (lang := lang) (s := s) (seed := seed) (φ := φ) (hNat := hNat) (f := f) := by
  exact
    Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_pack_via_prop12
      (lang := lang) (s := s) (seed := seed) (φ := φ) (hNat := hNat)
      (f := f)

/-- CoreMain-facing compact canonical endpoint:
rule-pack transport package + WM star-to-fixpoint closure. -/
abbrev coreMain_canonical_rulePack_transport_pack_and_fixpoint_endpoint_compact :=
  @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonical_rulePack_transport_pack_and_fixpoint_endpoint_compact

/-- CoreMain-facing compact canonical endpoint via Prop-12 compatibility
instantiation. -/
abbrev coreMain_canonical_prop12_transport_pack_and_fixpoint_endpoint_compact :=
  @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonical_prop12_transport_pack_and_fixpoint_endpoint_compact

/-- CoreMain-facing compact canonical fixpoint canary for WM consequence-rule
consumption. -/
abbrev coreMain_canonicalConsequenceRuleOn_compact_fixpoint :=
  @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonicalConsequenceRuleOn_compact_fixpoint

/-- CoreMain-facing constructor-category cross-sort native transport endpoint
(identity morphism). -/
abbrev coreMain_nativeType_constructor_transport_endpoint :=
  @Mettapedia.OSLF.NativeType.constructorNatTypeTransport_endpoint

/-- CoreMain-facing constructor-category cross-sort native transport endpoint
(composition). -/
abbrev coreMain_nativeType_constructor_transport_crossSort_comp :=
  @Mettapedia.OSLF.NativeType.constructorNatTypeTransport_crossSort_comp

/-- CoreMain-facing rhoCalc roundtrip canary for constructor-category
cross-sort native transport. -/
abbrev coreMain_nativeType_constructor_roundtrip_canary :=
  @Mettapedia.OSLF.NativeType.rho_roundtrip_constructorNatTypeHom

/-- CoreMain-facing concrete Mathlib Grothendieck endpoint over constructor sorts. -/
abbrev coreMain_nativeType_constructor_grothendieck_endpoint :=
  @Mettapedia.OSLF.NativeType.constructorPredFiberFunctorDual

/-- CoreMain-facing scoped roundtrip endpoint:
constructor transport -> Grothendieck morphism -> constructor transport. -/
theorem coreMain_nativeType_constructor_groth_roundtrip
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    {A B : Mettapedia.OSLF.NativeType.ConstructorNatType lang}
    (h : Mettapedia.OSLF.NativeType.ConstructorNatTypeHom lang A B) :
    Mettapedia.OSLF.NativeType.grothHom_to_constructorNatTypeHom
      (Mettapedia.OSLF.NativeType.constructorNatTypeHom_to_grothHom h) = h := by
  exact Mettapedia.OSLF.NativeType.constructorNatTypeHom_groth_roundtrip h

/-- CoreMain-facing end-to-end package:
Π/Ω/Prop translation plus constructor-transport/Grothendieck roundtrip. -/
theorem coreMain_nativeType_piOmegaProp_grothendieck_package
    {L₁ L₂ : Mettapedia.CategoryTheory.LambdaTheories.LambdaTheory}
    (F : Mettapedia.OSLF.NativeType.TheoryMorphism L₁ L₂)
    (S : L₁.Obj)
    (types : Set (L₁.fibration.Sub S))
    (φ ψ : L₁.fibration.Sub S)
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    {A B : Mettapedia.OSLF.NativeType.ConstructorNatType lang}
    (h : Mettapedia.OSLF.NativeType.ConstructorNatTypeHom lang A B) :
    (F.mapPred (Mettapedia.OSLF.NativeType.piType L₁ S types) =
      Mettapedia.OSLF.NativeType.piType L₂ (F.mapSort S) (F.mapPred '' types))
    ∧
    (F.mapNatType (Mettapedia.OSLF.NativeType.NatType.full (L := L₁) S)).pred =
      (Mettapedia.OSLF.NativeType.NatType.full (L := L₂) (F.mapSort S)).pred
    ∧
    (F.mapPred (Mettapedia.OSLF.NativeType.implType L₁ S φ ψ) =
      Mettapedia.OSLF.NativeType.implType L₂ (F.mapSort S) (F.mapPred φ) (F.mapPred ψ))
    ∧
    (Mettapedia.OSLF.NativeType.grothHom_to_constructorNatTypeHom
      (Mettapedia.OSLF.NativeType.constructorNatTypeHom_to_grothHom h) = h) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact F.preserves_piType S types
  · exact F.preserves_fullNatType_pred S
  · exact F.preserves_propImp S φ ψ
  · exact Mettapedia.OSLF.NativeType.constructorNatTypeHom_groth_roundtrip h

/-- CoreMain-facing scoped full-presheaf morphism endpoint. -/
abbrev coreMain_nativeType_full_presheaf_morphism_endpoint :=
  @Mettapedia.OSLF.NativeType.ScopedConstructorPredHom.toFullGrothHom

/-- CoreMain-facing composition law for scoped full-presheaf morphisms. -/
theorem coreMain_nativeType_full_presheaf_morphism_comp
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    {A B C : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang}
    (f : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang A B)
    (g : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang B C) :
    (Mettapedia.OSLF.NativeType.ScopedConstructorPredHom.comp f g).toFullGrothHom =
      Mettapedia.OSLF.NativeType.FullPresheafGrothendieckHom.comp
        f.toFullGrothHom g.toFullGrothHom := by
  exact Mettapedia.OSLF.NativeType.ScopedConstructorPredHom.toFullGrothHom_comp f g

/-- CoreMain-facing scoped comparison package between constructor and
full-presheaf endpoints. -/
theorem coreMain_nativeType_scoped_full_constructor_comparison_package
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    (A : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang)
    {B C : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang}
    (f : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang A B)
    (g : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang B C) :
    Mettapedia.OSLF.NativeType.grothObj_to_constructorNatType
      (Mettapedia.OSLF.NativeType.constructorNatType_toGrothObj A.toConstructorNatType) =
      A.toConstructorNatType
    ∧
    Opposite.unop (A.toFullGrothObj.base) =
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj lang A.sort
    ∧
    (Mettapedia.OSLF.NativeType.ScopedConstructorPredHom.comp f g).toFullGrothHom =
      Mettapedia.OSLF.NativeType.FullPresheafGrothendieckHom.comp
        f.toFullGrothHom g.toFullGrothHom := by
  exact Mettapedia.OSLF.NativeType.scoped_full_constructor_comparison_package A f g

/-- CoreMain-facing canonical category/topos package endpoint. -/
theorem coreMain_category_topos_package
    {σ : Mettapedia.CategoryTheory.Hypercube.Slot →
        Mettapedia.CategoryTheory.Hypercube.HSort}
    (hσ : Mettapedia.CategoryTheory.Hypercube.isEquationallyAdmissible σ)
    (a b c : Mettapedia.CategoryTheory.FuzzyFrame.UnitInterval) :
    σ Mettapedia.CategoryTheory.Hypercube.Slot.result =
      Mettapedia.CategoryTheory.Hypercube.HSort.star ∧
      (a * b ≤ c ↔ b ≤ Mettapedia.CategoryTheory.FuzzyFrame.UnitInterval.productImp a c) ∧
      a * b ≤ a ⊓ b :=
  coreMain_hypercube_fuzzy_bridge hσ a b c

/-- CoreMain-facing topos/internal-language bridge package:
fiber-membership/satisfies equivalence, conjunction/disjunction
internalization, and graph-object `◇`/`□` characterizations. -/
abbrev coreMain_topos_internal_language_bridge_package :=
  @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_internal_language_bridge_package

/-- CoreMain-facing TOGL-style graph/modal bridge package:
`∃/∀` reduction formulations are equivalent to edge-based graph-object
formulations. -/
abbrev coreMain_togl_graph_modal_bridge_package :=
  @Mettapedia.OSLF.Framework.ToposTOGLBridge.togl_graph_modal_bridge_package

/-- CoreMain-facing stronger topos/internal-language family with explicit
full presheaf-native route restriction/equivalence packaging. -/
abbrev coreMain_topos_internal_language_full_route_family :=
  @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_internal_language_full_route_family

/-- CoreMain-facing TOGL correspondence layer above graph-modal equivalence:
internal-subfunctor and graph-object edge characterizations coincide. -/
abbrev coreMain_togl_internal_graph_correspondence_layer :=
  @Mettapedia.OSLF.Framework.ToposTOGLBridge.togl_internal_graph_correspondence_layer

/-- CoreMain-facing canonical framework-level identity semantic transfer endpoint. -/
abbrev coreMain_identity_semantic_transfer_endpoint :=
  @Mettapedia.OSLF.Framework.IdentityEvidenceTransfer.identity_semantic_transfer_endpoint

/-- CoreMain-facing canonical OSLF paper §12 worked-example endpoint. -/
abbrev coreMain_section12_worked_examples :=
  @Mettapedia.OSLF.Framework.PaperSection12Examples.section12_worked_examples_bundle

/-- CoreMain-facing dependent/parametric generated-typing extension endpoint. -/
abbrev coreMain_dependent_parametric_generated_typing :=
  @Mettapedia.OSLF.Framework.GeneratedTyping.dependent_parametric_generated_type_system_extension

/-- CoreMain-facing canonical Theorem-1 contract:
forward substitutability plus the scoped image-finite equivalence endpoint. -/
structure CoreMainTheorem1CanonicalContract
    (R : Mettapedia.OSLF.Framework.Pat → Mettapedia.OSLF.Framework.Pat → Prop)
    (I : Mettapedia.OSLF.Formula.AtomSem) : Prop where
  forward :
    ∀ {p q : Mettapedia.OSLF.Framework.Pat},
      Mettapedia.OSLF.Framework.theorem1_behaviorEq R I p q →
      Mettapedia.OSLF.Framework.theorem1_sameNativeTypes R I p q
  imageFinite_iff :
    (∀ p : Mettapedia.OSLF.Framework.Pat, Set.Finite {q : Mettapedia.OSLF.Framework.Pat | R p q}) →
    (∀ p : Mettapedia.OSLF.Framework.Pat, Set.Finite {q : Mettapedia.OSLF.Framework.Pat | R q p}) →
    Mettapedia.OSLF.Framework.Theorem1SubstitutabilityEquiv R I

/-- CoreMain-facing canonical Theorem-1 contract constructor. -/
theorem coreMain_theorem1_canonical_contract
    (R : Mettapedia.OSLF.Framework.Pat → Mettapedia.OSLF.Framework.Pat → Prop)
    (I : Mettapedia.OSLF.Formula.AtomSem) :
    CoreMainTheorem1CanonicalContract R I := by
  refine ⟨?_, ?_⟩
  · intro p q h
    exact Mettapedia.OSLF.Framework.theorem1_substitutability_forward h
  · intro hImageFinite hPredFinite
    exact Mettapedia.OSLF.Framework.theorem1_substitutability_imageFinite hImageFinite hPredFinite

/-- CoreMain-facing Theorem-1 forward endpoint (projection from the canonical
contract field). -/
theorem coreMain_theorem1_substitutability_forward
    {R : Mettapedia.OSLF.Framework.Pat → Mettapedia.OSLF.Framework.Pat → Prop}
    {I : Mettapedia.OSLF.Formula.AtomSem}
    {p q : Mettapedia.OSLF.Framework.Pat} :
    Mettapedia.OSLF.Framework.theorem1_behaviorEq R I p q →
    Mettapedia.OSLF.Framework.theorem1_sameNativeTypes R I p q := by
  exact (coreMain_theorem1_canonical_contract (R := R) (I := I)).forward

/-- CoreMain-facing Theorem-1 scoped full equivalence endpoint (projection from
the canonical contract field). -/
theorem coreMain_theorem1_substitutability_imageFinite
    {R : Mettapedia.OSLF.Framework.Pat → Mettapedia.OSLF.Framework.Pat → Prop}
    {I : Mettapedia.OSLF.Formula.AtomSem}
    (hImageFinite : ∀ p : Mettapedia.OSLF.Framework.Pat,
      Set.Finite {q : Mettapedia.OSLF.Framework.Pat | R p q})
    (hPredFinite : ∀ p : Mettapedia.OSLF.Framework.Pat,
      Set.Finite {q : Mettapedia.OSLF.Framework.Pat | R q p}) :
    Mettapedia.OSLF.Framework.Theorem1SubstitutabilityEquiv R I := by
  exact (coreMain_theorem1_canonical_contract (R := R) (I := I)).imageFinite_iff
    hImageFinite hPredFinite

/-- CoreMain-facing canonical Theorem-1 equivalence endpoint on the default
`langReduces` relation:
the forward image-finite side is discharged concretely; only predecessor
finiteness remains as an explicit assumption. -/
theorem coreMain_theorem1_langReduces_imageFinite
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (hPredFinite : ∀ p : Mettapedia.OSLF.Framework.Pat,
      Set.Finite {q : Mettapedia.OSLF.Framework.Pat |
        Mettapedia.OSLF.Framework.TypeSynthesis.langReduces lang q p}) :
    Mettapedia.OSLF.Framework.Theorem1SubstitutabilityEquiv
      (Mettapedia.OSLF.Framework.TypeSynthesis.langReduces lang) I := by
  exact coreMain_theorem1_substitutability_imageFinite
    (R := Mettapedia.OSLF.Framework.TypeSynthesis.langReduces lang)
    (I := I)
    (hImageFinite := Mettapedia.Logic.OSLFImageFinite.imageFinite_langReduces lang)
    hPredFinite

/-- CoreMain-facing global-vs-scoped HM endpoint map for canonical π→ρ
relations.

- Global canonical core/derived endpoints require explicit predecessor
  image-finiteness assumptions.
- Scoped SC-quotiented canonical core/derived endpoints are assumption-free
  (both image-finiteness directions discharged internally for the selected
  relation family). -/
structure CoreMainHMEndpointMap : Prop where
  global_core :
    ∀ (I : Mettapedia.OSLF.Formula.AtomSem)
      (_hPredFinite : ∀ p : Mettapedia.OSLF.Framework.Pat,
        Set.Finite {q : Mettapedia.OSLF.Framework.Pat |
          Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoCoreCanonicalRel q p})
      (p q : Mettapedia.OSLF.Framework.Pat),
      Mettapedia.Logic.OSLFDistinctionGraph.indistObs
        Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoCoreCanonicalRel I p q
      ↔
      Mettapedia.Logic.OSLFDistinctionGraph.FullBisimilar
        Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoCoreCanonicalRel I p q
  global_derived :
    ∀ (I : Mettapedia.OSLF.Formula.AtomSem)
      (_hPredFinite : ∀ p : Mettapedia.OSLF.Framework.Pat,
        Set.Finite {q : Mettapedia.OSLF.Framework.Pat |
          Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoDerivedCanonicalRel q p})
      (p q : Mettapedia.OSLF.Framework.Pat),
      Mettapedia.Logic.OSLFDistinctionGraph.indistObs
        Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoDerivedCanonicalRel I p q
      ↔
      Mettapedia.Logic.OSLFDistinctionGraph.FullBisimilar
        Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoDerivedCanonicalRel I p q
  scoped_scquot_core :
    ∀ (I : Mettapedia.OSLF.Formula.AtomSem)
      (carrier : Finset Mettapedia.OSLF.Framework.Pat)
      (p q : Mettapedia.OSLF.Framework.Pat),
      Mettapedia.Logic.OSLFDistinctionGraph.indistObs
        (Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoCoreCanonicalSCQuotRelOn carrier)
        I p q
      ↔
      Mettapedia.Logic.OSLFDistinctionGraph.FullBisimilar
        (Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoCoreCanonicalSCQuotRelOn carrier)
        I p q
  scoped_scquot_derived :
    ∀ (I : Mettapedia.OSLF.Formula.AtomSem)
      (carrier : Finset Mettapedia.OSLF.Framework.Pat)
      (p q : Mettapedia.OSLF.Framework.Pat),
      Mettapedia.Logic.OSLFDistinctionGraph.indistObs
        (Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoDerivedCanonicalSCQuotRelOn carrier)
        I p q
      ↔
      Mettapedia.Logic.OSLFDistinctionGraph.FullBisimilar
        (Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoDerivedCanonicalSCQuotRelOn carrier)
        I p q

/-- CoreMain-facing canonical HM endpoint recommendation package:
keep global wrappers when predecessor-finiteness is available, otherwise use
the scoped SC-quotiented endpoint family for assumption-free iff theorems. -/
theorem coreMain_hm_endpoint_recommendation_map :
    CoreMainHMEndpointMap := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro I hPredFinite p q
    exact Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.hm_iff_fullBisim_rhoCoreCanonicalRel
      I hPredFinite p q
  · intro I hPredFinite p q
    exact Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.hm_iff_fullBisim_rhoDerivedCanonicalRel
      I hPredFinite p q
  · intro I carrier p q
    exact Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.hm_iff_fullBisim_rhoCoreCanonicalSCQuotRelOn
      I carrier p q
  · intro I carrier p q
    exact Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.hm_iff_fullBisim_rhoDerivedCanonicalSCQuotRelOn
      I carrier p q

/-- CoreMain-facing paper-parity theorem package:
projects Theorem-1 canonical contract, fragment-parametric reachable full-route
comparison, and TOGL graph-composition laws. -/
theorem coreMain_paper_parity_theorem_package
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    (R : Mettapedia.OSLF.Framework.Pat → Mettapedia.OSLF.Framework.Pat → Prop)
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (A : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang)
    (Frag : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang → Prop)
    (hClosed : ∀ {X Y : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang},
      Frag X → Mettapedia.OSLF.NativeType.ScopedReachable X Y → Frag Y) :
    CoreMainTheorem1CanonicalContract R I
    ∧
    (∀ {B C : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang},
      Frag A →
      Mettapedia.OSLF.NativeType.ScopedReachable A B →
      Mettapedia.OSLF.NativeType.ScopedReachable B C →
      Frag B
      ∧
      Frag C
      ∧
      ∃ f : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang A B,
        ∃ g : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang B C,
          Mettapedia.OSLF.NativeType.FullRouteRestrictionEquivalence lang A
          ∧
          f.toFullGrothHom.base = CategoryTheory.yoneda.map f.base
          ∧
          g.toFullGrothHom.base = CategoryTheory.yoneda.map g.base
          ∧
          (Mettapedia.OSLF.NativeType.ScopedConstructorPredHom.comp f g).toFullGrothHom =
            Mettapedia.OSLF.NativeType.FullPresheafGrothendieckHom.comp
              f.toFullGrothHom g.toFullGrothHom)
    ∧
    (∀ {relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv}
      {C : Type _} [CategoryTheory.Category C]
      {X : Opposite C}
      (p r : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern),
      Mettapedia.OSLF.Framework.ToposTOGLBridge.graphChain2
        (lang := lang) (relEnv := relEnv) (C := C) (X := X) p r
      ↔
      ∃ q,
        Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv lang p q
        ∧
        Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv lang q r) := by
  refine ⟨coreMain_theorem1_canonical_contract (R := R) (I := I), ?_, ?_⟩
  · intro B C hA hAB hBC
    exact Mettapedia.OSLF.NativeType.full_presheaf_comparison_bundle_reachable_fragment
      (Frag := Frag) (hClosed := hClosed) (A := A) (B := B) (C := C) hA hAB hBC
  · intro relEnv C _ X p r
    simpa using
      (Mettapedia.OSLF.Framework.ToposTOGLBridge.togl_graph_composition_reductionGraphObj_family
        (lang := lang) (relEnv := relEnv) (C := C) (X := X) (p := p) (r := r))

/-- CoreMain-facing paper-parity theorem package specialized to the canonical
relation `langReduces`:
returns Theorem-1 equivalence on the canonical relation plus the existing
fragment and TOGL composition endpoint fields. -/
theorem coreMain_paper_parity_theorem_package_langReduces
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (A : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang)
    (Frag : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang → Prop)
    (hClosed : ∀ {X Y : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang},
      Frag X → Mettapedia.OSLF.NativeType.ScopedReachable X Y → Frag Y)
    (hPredFinite : ∀ p : Mettapedia.OSLF.Framework.Pat,
      Set.Finite {q : Mettapedia.OSLF.Framework.Pat |
        Mettapedia.OSLF.Framework.TypeSynthesis.langReduces lang q p}) :
    Mettapedia.OSLF.Framework.Theorem1SubstitutabilityEquiv
      (Mettapedia.OSLF.Framework.TypeSynthesis.langReduces lang) I
    ∧
    (∀ {B C : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang},
      Frag A →
      Mettapedia.OSLF.NativeType.ScopedReachable A B →
      Mettapedia.OSLF.NativeType.ScopedReachable B C →
      Frag B
      ∧
      Frag C
      ∧
      ∃ f : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang A B,
        ∃ g : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang B C,
          Mettapedia.OSLF.NativeType.FullRouteRestrictionEquivalence lang A
          ∧
          f.toFullGrothHom.base = CategoryTheory.yoneda.map f.base
          ∧
          g.toFullGrothHom.base = CategoryTheory.yoneda.map g.base
          ∧
          (Mettapedia.OSLF.NativeType.ScopedConstructorPredHom.comp f g).toFullGrothHom =
            Mettapedia.OSLF.NativeType.FullPresheafGrothendieckHom.comp
              f.toFullGrothHom g.toFullGrothHom)
    ∧
    (∀ {relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv}
      {C : Type _} [CategoryTheory.Category C]
      {X : Opposite C}
      (p r : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern),
      Mettapedia.OSLF.Framework.ToposTOGLBridge.graphChain2
        (lang := lang) (relEnv := relEnv) (C := C) (X := X) p r
      ↔
      ∃ q,
        Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv lang p q
        ∧
        Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv lang q r) := by
  rcases coreMain_paper_parity_theorem_package
      (lang := lang)
      (R := Mettapedia.OSLF.Framework.TypeSynthesis.langReduces lang)
      (I := I) (A := A) (Frag := Frag) hClosed with
    ⟨hContract, hFrag, hTogl⟩
  refine ⟨?_, hFrag, hTogl⟩
  exact hContract.imageFinite_iff
    (Mettapedia.Logic.OSLFImageFinite.imageFinite_langReduces lang) hPredFinite

/-- Canonical CoreMain paper-parity contract record:
packages the `langReduces` Theorem-1 endpoint, fragment-parametric full-route
comparison, and TOGL graph-composition law in one field-based API. -/
structure CoreMainPaperParityCanonicalPackage
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (A : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang)
    (Frag : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang → Prop) : Prop where
  theorem1_langReduces_imageFinite :
    (∀ p : Mettapedia.OSLF.Framework.Pat,
      Set.Finite {q : Mettapedia.OSLF.Framework.Pat |
        Mettapedia.OSLF.Framework.TypeSynthesis.langReduces lang q p}) →
      Mettapedia.OSLF.Framework.Theorem1SubstitutabilityEquiv
        (Mettapedia.OSLF.Framework.TypeSynthesis.langReduces lang) I
  full_presheaf_fragment :
    ∀ {B C : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang},
      Frag A →
      Mettapedia.OSLF.NativeType.ScopedReachable A B →
      Mettapedia.OSLF.NativeType.ScopedReachable B C →
      Frag B
      ∧
      Frag C
      ∧
      ∃ f : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang A B,
        ∃ g : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang B C,
          Mettapedia.OSLF.NativeType.FullRouteRestrictionEquivalence lang A
          ∧
          f.toFullGrothHom.base = CategoryTheory.yoneda.map f.base
          ∧
          g.toFullGrothHom.base = CategoryTheory.yoneda.map g.base
          ∧
          (Mettapedia.OSLF.NativeType.ScopedConstructorPredHom.comp f g).toFullGrothHom =
            Mettapedia.OSLF.NativeType.FullPresheafGrothendieckHom.comp
              f.toFullGrothHom g.toFullGrothHom
  togl_graph_composition :
    ∀ {relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv}
      {C : Type _} [CategoryTheory.Category C]
      {X : Opposite C}
      (p r : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern),
      Mettapedia.OSLF.Framework.ToposTOGLBridge.graphChain2
        (lang := lang) (relEnv := relEnv) (C := C) (X := X) p r
      ↔
      ∃ q,
        Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv lang p q
        ∧
        Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv lang q r

/-- CoreMain-facing canonical paper-parity package endpoint:
builds the field-based contract from the existing specialized theorem package. -/
theorem coreMain_paper_parity_canonical_package
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (A : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang)
    (Frag : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang → Prop)
    (hClosed : ∀ {X Y : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang},
      Frag X → Mettapedia.OSLF.NativeType.ScopedReachable X Y → Frag Y) :
    CoreMainPaperParityCanonicalPackage lang I A Frag := by
  refine ⟨?_, ?_, ?_⟩
  · intro hPredFinite
    exact coreMain_theorem1_langReduces_imageFinite
      (lang := lang) (I := I) hPredFinite
  · intro B C hA hAB hBC
    exact Mettapedia.OSLF.NativeType.full_presheaf_comparison_bundle_reachable_fragment
      (Frag := Frag) (hClosed := hClosed) (A := A) (B := B) (C := C) hA hAB hBC
  · intro relEnv C _ X p r
    simpa using
      (Mettapedia.OSLF.Framework.ToposTOGLBridge.togl_graph_composition_reductionGraphObj_family
        (lang := lang) (relEnv := relEnv) (C := C) (X := X) (p := p) (r := r))

/-- Extended paper-parity package: adds M1–M4 milestones on top of the canonical package.
This bundles:
- M1: Category instance for full presheaf Grothendieck
- M2: Equivalence at representable objects (scoped ↔ full roundtrip)
- M3: Full internal logic bridge (⊤/⊥/∧/∨/→/¬, Π/Σ)
- M4: TOGL complete bridge (2-step + n-step + modal iteration) -/
theorem coreMain_paper_parity_full_package
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (A : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang)
    (Frag : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang → Prop)
    (hClosed : ∀ {X Y : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang},
      Frag X → Mettapedia.OSLF.NativeType.ScopedReachable X Y → Frag Y)
    {B C : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang}
    (f : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang A B)
    (g : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang B C) :
    -- Base canonical package
    CoreMainPaperParityCanonicalPackage lang I A Frag
    ∧
    -- M1: Category instance witness
    (∃ _ : CategoryTheory.Category.{0, 1}
      (Mettapedia.OSLF.NativeType.FullPresheafGrothendieckObj lang), True)
    ∧
    -- M2: Scoped ↔ full roundtrip at representable objects
    (Mettapedia.OSLF.NativeType.fullGrothObj_to_scopedConstructorPred_at_representable
      A.toFullGrothObj A.sort A.seed A.pred A.naturality
      (Mettapedia.OSLF.NativeType.scoped_fullGroth_base_eq_representable A)
      rfl = A)
    ∧
    -- M2: Full route restriction equivalence
    Mettapedia.OSLF.NativeType.FullRouteRestrictionEquivalence lang A
    ∧
    -- M2: Composition preservation
    ((Mettapedia.OSLF.NativeType.ScopedConstructorPredHom.comp f g).toFullGrothHom =
      Mettapedia.OSLF.NativeType.FullPresheafGrothendieckHom.comp
        f.toFullGrothHom g.toFullGrothHom)
    ∧
    -- M4: N-step graph chain ↔ relational composition
    (∀ {relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv}
        {Ct : Type _} [CategoryTheory.Category Ct]
        {X : Opposite Ct}
        (n : Nat) (p r : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern),
      Mettapedia.OSLF.Framework.ToposTOGLBridge.graphChainN
        (lang := lang) (relEnv := relEnv) (C := Ct) (X := X) n p r
        ↔
      Mettapedia.OSLF.Framework.ToposTOGLBridge.relCompN lang relEnv n p r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact coreMain_paper_parity_canonical_package lang I A Frag hClosed
  · exact ⟨Mettapedia.OSLF.NativeType.fullPresheafGrothendieckCategory lang, trivial⟩
  · exact Mettapedia.OSLF.NativeType.scoped_full_scoped_obj_roundtrip A
  · exact (Mettapedia.OSLF.NativeType.full_route_restriction_equivalence_package
      (A := A) f g).1
  · exact (Mettapedia.OSLF.NativeType.full_route_restriction_equivalence_package
      (A := A) f g).2
  · intro relEnv Ct _ X n p r
    exact Mettapedia.OSLF.Framework.ToposTOGLBridge.graphChainN_iff_relCompN
      lang relEnv Ct (X := X) n p r

#check @coreMain_paper_parity_full_package

#check Mettapedia.OSLF.Framework.FULLStatus.remaining_eq_nil
#check Mettapedia.OSLF.Framework.FULLStatus.remainingCount_eq_zero
#check Mettapedia.OSLF.Framework.FULLStatus.strictRemaining_eq_nil
#check Mettapedia.OSLF.Framework.FULLStatus.strictRemainingCount_eq_zero
#check Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef.mettaFull
#check Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef.mettaFullOSLF
#check Mettapedia.Logic.OSLFImageFinite.imageFinite_langReduces
#check Mettapedia.Logic.OSLFImageFinite.hm_converse_langReduces
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.piRho_coreMain_canonical_contract_end_to_end
#check @coreMain_piRho_canonical_contract
#check @coreMain_piRho_contract_projection_api
#check @coreMain_hypercube_fuzzy_bridge
#check @coreMain_identity_semantic_transfer_endpoint
#check @coreMain_nativeType_piOmega_translation_endpoint
#check @coreMain_nativeType_piOmegaProp_translation_endpoint
#check @coreMain_nativeType_piSigmaOmegaProp_translation_endpoint
#check @coreMain_nativeType_piOmegaProp_constructor_transport_bundle
#check @coreMain_nativeType_comp_piOmegaProp_constructor_transport_bundle
#check @coreMain_nativeType_piProp_colax_rules_endpoint
#check @coreMain_nativeType_piSigmaProp_colax_rules_endpoint
#check @coreMain_nativeType_id_piOmega_canary
#check @coreMain_nativeType_id_piSigmaOmegaProp_canary
#check @coreMain_representable_patternPred_piSigma_transport_via_rulePack
#check @coreMain_representable_patternPred_piSigma_transport_via_prop12_pack
#check @coreMain_representable_patternPred_piSigma_transport_pack_via_rulePack
#check @coreMain_representable_patternPred_piSigma_transport_pack
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.CanonicalClosureContext
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.CanonicalModalSquare
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.CanonicalHyperSquare
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.CanonicalFormulaArgs
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.CanonicalGoalArgs
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.CanonicalTransportGoalArgs
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonicalEvidenceObligation_compact
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonicalEvidenceConsequenceRuleOn_compact
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonicalEvidenceConsequenceRuleOn_compact_of_goal
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonicalEvidenceConsequenceRuleOn_compact_of_goal_canary
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonicalConsequenceRuleOn_compact
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonicalConsequenceRuleOn_compact_of_goal
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonicalConsequenceRuleOn_compact_fixpoint
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonicalConsequenceRuleOn_compact_fixpoint_of_goal
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonical_rulePack_transport_pack_and_fixpoint_endpoint_compact
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonical_rulePack_transport_pack_and_fixpoint_endpoint_of_goal
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonical_prop12_transport_pack_and_fixpoint_endpoint_compact
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonical_prop12_transport_pack_and_fixpoint_endpoint_of_goal
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonical_rulePack_transport_pack_and_fixpoint_endpoint_of_transportGoal
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonical_prop12_transport_pack_and_fixpoint_endpoint_of_transportGoal
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonical_rulePack_transport_piSigma_and_fixpoint_of_transportGoal
#check @Mettapedia.OSLF.Framework.OSLFNTTWMCanonicalClosure.canonical_prop12_transport_piSigma_and_fixpoint_of_transportGoal
#check @coreMain_canonical_rulePack_transport_pack_and_fixpoint_endpoint_compact
#check @coreMain_canonical_prop12_transport_pack_and_fixpoint_endpoint_compact
#check @coreMain_canonicalConsequenceRuleOn_compact_fixpoint
#check @coreMain_nativeType_constructor_transport_endpoint
#check @coreMain_nativeType_constructor_transport_crossSort_comp
#check @coreMain_nativeType_constructor_roundtrip_canary
#check @coreMain_nativeType_constructor_grothendieck_endpoint
#check @coreMain_nativeType_constructor_groth_roundtrip
#check @coreMain_nativeType_piOmegaProp_grothendieck_package
#check @coreMain_nativeType_full_presheaf_morphism_endpoint
#check @coreMain_nativeType_full_presheaf_morphism_comp
#check @coreMain_nativeType_scoped_full_constructor_comparison_package
#check @coreMain_category_topos_package
#check @coreMain_topos_internal_language_bridge_package
#check @coreMain_togl_graph_modal_bridge_package
#check @coreMain_topos_internal_language_full_route_family
#check @coreMain_togl_internal_graph_correspondence_layer
#check @coreMain_section12_worked_examples
#check @coreMain_dependent_parametric_generated_typing
#check @coreMain_theorem1_canonical_contract
#check @coreMain_theorem1_substitutability_forward
#check @coreMain_theorem1_substitutability_imageFinite
#check @coreMain_theorem1_langReduces_imageFinite
#check @coreMain_paper_parity_theorem_package
#check @coreMain_paper_parity_theorem_package_langReduces
#check @CoreMainPaperParityCanonicalPackage
#check @coreMain_paper_parity_canonical_package
-- Category LambdaTheory (Thm 23 upgrade)
#check @Mettapedia.OSLF.NativeType.lambdaTheoryCategoryStruct
#check @Mettapedia.OSLF.NativeType.lambdaTheoryCategory
#check @Mettapedia.OSLF.NativeType.lambdaTheory_id_eq
#check @Mettapedia.OSLF.NativeType.lambdaTheory_comp_eq
-- Layer 2: LambdaTheory ⥤ Cat functor
#check @Mettapedia.OSLF.NativeType.natTypePreorder
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.mapPred_mono
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.mapNatType_monotone
#check @Mettapedia.OSLF.NativeType.theoryMorphismNatTypeFunctor
#check @Mettapedia.OSLF.NativeType.nativeTypeFunctor
-- Simulation maps preserve modal semantics
#check @Mettapedia.OSLF.Framework.SimulationPreservation.forward_sim_preserves_positive
#check @Mettapedia.OSLF.Framework.SimulationPreservation.bisimulation_map_preserves_sem
#check @Mettapedia.OSLF.Framework.SimulationPreservation.bisimulation_map_preserves_indistObs

end Mettapedia.OSLF
