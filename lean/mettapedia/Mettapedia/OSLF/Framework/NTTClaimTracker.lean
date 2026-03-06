import Mettapedia.OSLF.NativeType.CodomainFibration
import Mettapedia.OSLF.Framework.ToposTOGLBridge
import Mettapedia.OSLF.Framework.CategoryBridge
import Mettapedia.OSLF.Framework.AssumptionNecessity
import Mettapedia.OSLF.Framework.BeckChevalleyOSLF

/-!
# Native Type Theory Strict Claim Tracker

This tracker is keyed to endpoint-claim anchors in:
`/home/zar/claude/literature/Hyperon Study Materials/Rho and OSLF/Native_Type_Theory.pdf`.

It tracks theorem-level endpoint anchors only. Semantic adequacy of the
operational modal route is tracked separately in canonical bridge modules
(`ModalSubobjectBridge`, `OSLFNTTWMBridge`); endpoint closure here must not be
read as "all semantic layers are closed."
-/

namespace Mettapedia.OSLF.Framework.NTTClaimTracker

/-- Resolution status for one NTT-paper claim. -/
inductive NTTClaimStatus where
  | proven
  | assumptionScoped
  | partiallyFormalized
  | notFormalized
  deriving DecidableEq, Repr

/-- One strict claim row tied to the Native Type Theory paper. -/
structure NTTClaim where
  loc : String
  claim : String
  leanRef : String
  status : NTTClaimStatus
  deriving DecidableEq, Repr

/-- Strict NTT endpoint-claim surface (paper keyed). -/
def nttClaimList : List NTTClaim :=
  [ ⟨"Def 11", "Predicate fibration piOmega over the base category",
      "CategoryBridge.predFibration / CategoryBridge.oslf_fibration", .proven⟩
  , ⟨"Sec 3", "Native type as (sort, predicate) pair",
      "NativeType.NatType / NativeType.NatTypeFiber", .proven⟩
  , ⟨"Prop 12", "Indexed adjoints (exists_f dashv Omega^f dashv forall_f) with Beck-Chevalley",
      "NativeType.prop12_package / NativeType.prop12_beckChevalley", .proven⟩
  , ⟨"Prop 14", "Fibered internal logic structure (cosmic-style package) for predicate fibers",
      "NativeType.prop14_cosmicFibration", .proven⟩
  , ⟨"Prop 17", "Reification right adjoint layer",
      "NativeType.prop17_reification", .proven⟩
  , ⟨"Def 21", "Codomain fibration piDelta + Cartesian lifts via pullbacks",
      "NativeType.def21_codomainFibration / def21_cartesianLift_proj / def21_cartesianLift_universal_comp", .proven⟩
  , ⟨"Sec 4", "Image-comprehension adjunction i dashv c (full iff characterization)",
      "NativeType.imageComprehensionAdjunction (with iff_characterization) / imageComprehension_iff", .proven⟩
  , ⟨"Thm 23", "Internal language functor L : Topos -> HDT_Sigma + functorial laws",
      "NativeType.thm23_internalLanguagePackage / thm23_functorialLaws", .proven⟩
  , ⟨"Sec 5", "Theory morphism preservation for Pi/Sigma/Omega translation",
      "TheoryMorphism.piSigmaOmegaProp_translation_endpoint", .proven⟩
  , ⟨"Sec 5", "Colax Pi/Sigma/Prop translation rule set",
      "TheoryMorphism.piSigmaProp_colax_rules", .proven⟩
  , ⟨"Sec 5", "Representable Pi/Sigma transport package (rule-pack-first endpoint; Prop-12 wrappers for compatibility)",
      "ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_pack_via_rulePack / ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_via_rulePack / ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_pack_via_prop12 / ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_via_prop12_pack / OSLFNTTWMCanonicalClosure.canonical_rulePack_transport_pack_and_fixpoint_endpoint_of_goal / OSLFNTTWMCanonicalClosure.canonical_prop12_transport_pack_and_fixpoint_endpoint_of_goal / OSLFNTTWMCanonicalClosure.canonical_rulePack_transport_pack_and_fixpoint_endpoint_of_transportGoal / OSLFNTTWMCanonicalClosure.canonical_prop12_transport_pack_and_fixpoint_endpoint_of_transportGoal / OSLFNTTWMCanonicalClosure.canonical_rulePack_transport_piSigma_and_fixpoint_of_transportGoal / OSLFNTTWMCanonicalClosure.canonical_prop12_transport_piSigma_and_fixpoint_of_transportGoal",
      .proven⟩
  , ⟨"Sec 5", "Necessity audit for nonempty-family guard in Pi/Sigma package",
      "AssumptionNecessity.types_nonempty_necessary_for_piSigma", .proven⟩
  ]

/-- Count strict NTT claims by status. -/
def countByStatus (s : NTTClaimStatus) : Nat :=
  (nttClaimList.filter (fun c => c.status = s)).length

/-- Claims that are not resolved at full theorem level. -/
def nttRemaining : List NTTClaim :=
  nttClaimList.filter (fun c =>
    c.status = .partiallyFormalized || c.status = .notFormalized)

/-- Number of unresolved strict NTT claims. -/
def nttRemainingCount : Nat :=
  nttRemaining.length

/-- No unresolved endpoint claims remain in this tracker. -/
theorem nttRemaining_empty : nttRemaining = [] := by
  decide

/-- Endpoint unresolved count is zero for this tracker surface. -/
theorem nttRemainingCount_zero : nttRemainingCount = 0 := by
  decide

/-- Resolved endpoint claims currently classified as `proven`.
    This is an endpoint-surface count only. -/
theorem provenCount_eq : countByStatus .proven = 12 := by
  decide

/-- No strict endpoint remains `assumptionScoped` in this tracker. -/
theorem assumptionScopedCount_eq : countByStatus .assumptionScoped = 0 := by
  decide

/-- No partially formalized claims remain. -/
theorem partialCount_eq : countByStatus .partiallyFormalized = 0 := by
  decide

/-- No missing claims remain. -/
theorem missingCount_eq : countByStatus .notFormalized = 0 := by
  decide

/-- Endpoint parity surface in this tracker is closed. -/
theorem fullNTTParity_closed : nttRemainingCount = 0 :=
  nttRemainingCount_zero

/-! ## Anchor checks -/

#check @Mettapedia.OSLF.NativeType.NatType
#check @Mettapedia.OSLF.Framework.CategoryBridge.predFibration
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_full_internal_logic_bridge_package
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_via_rulePack
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_pack_via_rulePack
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_pack_via_prop12
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_via_prop12_pack
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.piOmega_translation_endpoint
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.piSigmaOmegaProp_translation_endpoint
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.piProp_colax_rules
#check @Mettapedia.OSLF.NativeType.TheoryMorphism.piSigmaProp_colax_rules
#check @Mettapedia.OSLF.Framework.AssumptionNecessity.types_nonempty_necessary_for_piSigma

-- NTT endpoints (CodomainFibration.lean)
#check @Mettapedia.OSLF.NativeType.prop12_package
#check @Mettapedia.OSLF.NativeType.prop12_beckChevalley
#check @Mettapedia.OSLF.NativeType.prop12_piSigmaPredicateRulePack
#check @Mettapedia.OSLF.NativeType.prop12_piEta_presheaf
#check @Mettapedia.OSLF.NativeType.prop12_sigmaEta_presheaf
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.RepresentablePiSigmaTransportPack
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_patternPred_piSigma_transport_pack_via_rulePack
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_patternPred_piSigma_transport_pack_via_prop12
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_patternPred_piSigma_transport_via_rulePack
#check @Mettapedia.OSLF.NativeType.prop14_cosmicFibration
#check @Mettapedia.OSLF.NativeType.prop17_reification
#check @Mettapedia.OSLF.NativeType.def21_codomainFibration
#check @Mettapedia.OSLF.NativeType.imageComprehensionAdjunction
#check @Mettapedia.OSLF.NativeType.thm23_internalLanguagePackage

-- Strengthened endpoints (Phase 1-3)
#check @Mettapedia.OSLF.NativeType.def21_cartesianLift_proj
#check @Mettapedia.OSLF.NativeType.def21_cartesianLift_universal_comp
#check @Mettapedia.OSLF.NativeType.imageComprehension_iff
#check @Mettapedia.OSLF.NativeType.thm23_functorialLaws

end Mettapedia.OSLF.Framework.NTTClaimTracker
