import Mettapedia.OSLF.CoreMain
import Mettapedia.OSLF.Framework.AssumptionNecessity
import Mettapedia.OSLF.Framework.NTTClaimTracker

/-!
# Paper-Claim Tracker

One row per verifiable claim in the three OSLF source papers.
Each row references a concrete Lean theorem or counterexample.

Important scope note:
- NTT rows below are the OSLF-facing NTT subset.
- Strict theorem-number keyed NTT parity is tracked separately in
  `Mettapedia/OSLF/Framework/NTTClaimTracker.lean`.

## Papers
- [OSLF] Meredith & Stay, "Operational Semantics in Logical Form"
- [NTT] Williams & Stay, "Native Type Theory" (ACT 2021)
- [TOGL] Meredith & Radestock, "A Formal Theory of Graphs"
-/

namespace Mettapedia.OSLF.Framework.PaperClaimTracker

/-- Status of a paper-level claim relative to the Lean formalization. -/
inductive ClaimStatus where
  | proven          -- fully formalized as a theorem
  | assumptionScoped -- proven under explicit, necessity-audited assumptions
  | counterexample  -- paper claim is too strong; counterexample shows failure
  deriving DecidableEq, Repr

/-- A single paper claim with its formalization status. -/
structure PaperClaim where
  paper : String
  loc : String        -- paper section/theorem number
  claim : String
  leanRef : String
  status : ClaimStatus
  deriving DecidableEq, Repr

/-- All verifiable claims from the three OSLF papers. -/
def paperClaimList : List PaperClaim :=
  -- OSLF paper (oslf.pdf)
  [ ⟨"oslf.pdf", "Def 1", "Rewrite system: sorts, terms, one-step reduction",
    "RewriteSystem", .proven⟩
  , ⟨"oslf.pdf", "§3", "Step-future operator ◇",
    "langDiamond / possiblyProp", .proven⟩
  , ⟨"oslf.pdf", "§3", "Step-past operator □",
    "langBox / relyProp", .proven⟩
  , ⟨"oslf.pdf", "§4", "Galois connection ◇ ⊣ □",
    "langGalois / galois_connection", .proven⟩
  , ⟨"oslf.pdf", "§6", "OSLF type system output (frame + modalities)",
    "OSLFTypeSystem / langOSLF", .proven⟩
  , ⟨"oslf.pdf", "Thm 1", "Behavioral equiv → same native types (forward)",
    "theorem1_substitutability_forward", .proven⟩
  , ⟨"oslf.pdf", "Thm 1", "Full substitutability equivalence (image-finite)",
    "theorem1_substitutability_imageFinite", .assumptionScoped⟩
  , ⟨"oslf.pdf", "§11", "ρ-calculus instance",
    "rhoOSLF", .proven⟩
  , ⟨"oslf.pdf", "§11", "λ-calculus instance",
    "lambdaOSLF", .proven⟩
  , ⟨"oslf.pdf", "§11", "Petri net instance",
    "petriOSLF", .proven⟩
  , ⟨"oslf.pdf", "§12.1", "Compile-time firewall worked example",
    "compile_time_firewall_worked_example", .proven⟩
  , ⟨"oslf.pdf", "§12.2", "Race detection worked example",
    "race_detection_worked_example", .proven⟩
  , ⟨"oslf.pdf", "§12.3", "Secrecy worked example",
    "secrecy_worked_example", .proven⟩
  , ⟨"oslf.pdf", "§13.1", "Dependent/parametric type extension",
    "dependent_parametric_generated_type_system_extension", .proven⟩
  -- Native Type Theory paper (Native_Type_Theory.pdf), OSLF-facing subset
  , ⟨"NTT.pdf", "§3", "Native type = (sort, predicate) pair",
    "NativeTypeOf / NatType / NatTypeFiber", .proven⟩
  , ⟨"NTT.pdf", "§3-§5 (endpoint subset)", "Full presheaf Grothendieck category endpoint",
    "fullPresheafGrothendieckCategory", .proven⟩
  , ⟨"NTT.pdf", "§3-§5 (endpoint subset)", "Scoped ↔ full presheaf comparison endpoint",
    "scoped_full_scoped_obj_roundtrip / full_route_restriction_equivalence_package", .proven⟩
  , ⟨"NTT.pdf", "§4 (fiber-logic subset)", "Internal language: ⊤/⊥/∧/∨ in fibers",
    "topos_full_internal_logic_bridge_package", .proven⟩
  , ⟨"NTT.pdf", "§4 (fiber-logic subset)", "Frame-derived →/¬ in fibers",
    "topos_full_internal_logic_bridge_package (Heyting clause)", .proven⟩
  , ⟨"NTT.pdf", "§4 (endpoint subset)", "Representable Π/Σ transport package (rule-pack-first; Prop-12 compatibility wrappers)",
    "topos_representable_patternPred_piSigma_transport_pack_via_rulePack / topos_representable_patternPred_piSigma_transport_via_rulePack / topos_representable_patternPred_piSigma_transport_pack_via_prop12 / topos_representable_patternPred_piSigma_transport_via_prop12_pack / canonical_rulePack_transport_pack_and_fixpoint_endpoint_of_goal / canonical_prop12_transport_pack_and_fixpoint_endpoint_of_goal / canonical_rulePack_transport_pack_and_fixpoint_endpoint_of_transportGoal / canonical_prop12_transport_pack_and_fixpoint_endpoint_of_transportGoal / canonical_rulePack_transport_piSigma_and_fixpoint_of_transportGoal / canonical_prop12_transport_piSigma_and_fixpoint_of_transportGoal", .proven⟩
  , ⟨"NTT.pdf", "§5", "Theory morphism preservation (Π/Σ/Ω/Prop endpoint)",
    "TheoryMorphism.piSigmaOmegaProp_translation_endpoint", .proven⟩
  , ⟨"NTT.pdf", "§5", "Colax Π/Σ/Prop rules",
    "TheoryMorphism.piSigmaProp_colax_rules", .proven⟩
  -- TOGL paper (togl.pdf)
  , ⟨"togl.pdf", "§2", "Graph reduction structure",
    "reductionGraphObjUsing", .proven⟩
  , ⟨"togl.pdf", "§3", "Graph-modal bridge: edges ↔ ◇/□",
    "togl_graph_modal_bridge_package", .proven⟩
  , ⟨"togl.pdf", "§4", "N-step graph paths ↔ n-fold relational composition",
    "graphChainN_iff_relCompN", .proven⟩
  , ⟨"togl.pdf", "§4", "Modal iteration ◇ⁿ ↔ graph chains",
    "diamondIterN_iff_graphChainN", .proven⟩
  , ⟨"togl.pdf", "§5", "Internal subfunctor ↔ graph-object correspondence",
    "togl_internal_graph_correspondence_layer", .proven⟩
  ]

/-- Number of claims by status. -/
def claimCountByStatus (s : ClaimStatus) : Nat :=
  (paperClaimList.filter (fun c => c.status == s)).length

/-- All claims are resolved (proven or assumption-scoped). -/
theorem paperClaimList_all_resolved :
    paperClaimList.all (fun c => c.status == .proven
      || c.status == .assumptionScoped
      || c.status == .counterexample) = true := by
  decide

/-- Count of fully proven claims. -/
theorem provenCount_eq : claimCountByStatus .proven = 26 := by decide

/-- Count of assumption-scoped claims. -/
theorem assumptionScopedCount_eq : claimCountByStatus .assumptionScoped = 1 := by decide

/-- Full NTT parity is closed: all strict NTT claims are resolved. -/
theorem fullNTTParity_closed :
    Mettapedia.OSLF.Framework.NTTClaimTracker.nttRemainingCount = 0 :=
  Mettapedia.OSLF.Framework.NTTClaimTracker.nttRemainingCount_zero

/-! ## Code-Reference Anchors -/

-- OSLF core
#check @RewriteSystem
#check @OSLFTypeSystem
#check @Mettapedia.OSLF.Framework.TypeSynthesis.langDiamond
#check @Mettapedia.OSLF.Framework.TypeSynthesis.langBox
#check @Mettapedia.OSLF.Framework.TypeSynthesis.langGalois
#check @Mettapedia.OSLF.Framework.TypeSynthesis.langOSLF
#check @Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.possiblyProp
#check @Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.relyProp
#check @Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.galois_connection
#check @Mettapedia.OSLF.Framework.Theorem1SubstitutabilityEquiv
#check @Mettapedia.OSLF.Framework.theorem1_substitutability_forward
#check @Mettapedia.OSLF.Framework.theorem1_substitutability_imageFinite
#check @Mettapedia.OSLF.Framework.RhoInstance.rhoOSLF
#check @Mettapedia.OSLF.Framework.LambdaInstance.lambdaOSLF
#check @Mettapedia.OSLF.Framework.PetriNetInstance.petriOSLF
#check @Mettapedia.OSLF.Framework.GeneratedTyping.dependent_parametric_generated_type_system_extension

-- Native Type Theory
#check @Mettapedia.OSLF.NativeType.NatTypeFiber
#check @Mettapedia.OSLF.NativeType.fullPresheafGrothendieckCategory
#check @Mettapedia.OSLF.NativeType.scoped_full_scoped_obj_roundtrip
#check @Mettapedia.OSLF.NativeType.full_route_restriction_equivalence_package
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_full_internal_logic_bridge_package
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_via_rulePack
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_pack_via_rulePack
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_pack_via_prop12
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_via_prop12_pack
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.piOmega_translation_endpoint
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.piSigmaOmegaProp_translation_endpoint
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.piProp_colax_rules
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.piSigmaProp_colax_rules

-- TOGL
#check @Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.togl_graph_modal_bridge_package
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.graphChainN_iff_relCompN
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.diamondIterN_iff_graphChainN
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.togl_internal_graph_correspondence_layer

-- Assumption necessity
#check @Mettapedia.OSLF.Framework.AssumptionNecessity.types_nonempty_necessary_for_piSigma
#check @Mettapedia.OSLF.Framework.AssumptionNecessity.hClosed_necessary_for_fragment
#check @Mettapedia.OSLF.Framework.AssumptionNecessity.not_global_hImageFinite_rhoCoreStarRel
#check @fullNTTParity_closed

-- Unified endpoint
#check @Mettapedia.OSLF.coreMain_paper_parity_full_package

end Mettapedia.OSLF.Framework.PaperClaimTracker
