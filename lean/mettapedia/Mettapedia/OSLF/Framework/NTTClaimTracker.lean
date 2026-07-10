import Mettapedia.OSLF.NativeType.CodomainFibration
import Mettapedia.OSLF.Framework.ToposTOGLBridge
import Mettapedia.OSLF.Framework.CategoryBridge
import Mettapedia.OSLF.Framework.AssumptionNecessity
import Mettapedia.OSLF.Framework.BeckChevalleyOSLF
import Mettapedia.OSLF.MeTTaIL.LPRelationEnvBridge

/-!
# Native Type Theory Strict Claim Tracker

This tracker is keyed to endpoint-claim anchors in the Native Type Theory
paper.

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

/-- Strict NTT endpoint-claim inventory (paper keyed). -/
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
  , ⟨"Thm 23", "Internal language package with functorial laws (identity/composition)",
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

/-! ## HOL kernel-profile OSLF/NTT claim ledger

This is a separate ledger from the strict NTT-paper endpoint list above.  The
endpoint list remains closed; the rows below track the newer HOL-kernel-profile
work and explicitly separate what is available from what is still an O3
obligation.
-/

/-- HOL-kernel profile claims and obligations. -/
def holKernelClaimList : List NTTClaim :=
  [ ⟨"HOL-Light profile",
      "HOL Light equality-kernel profile exists as a distinct LanguageDef with fusion.ml primitive-rule names and guarded executable reduction witnesses",
      "GSLT.LanguageDef.HOLKernelProfiles.holLightEqKernel / holLightReflWitness",
      .partiallyFormalized⟩
  , ⟨"HOL4 profile",
      "HOL4 LCF profile exists as a distinct LanguageDef with primitive DISCH/MP/SUBST/INST_TYPE rule names and guarded executable DISCH/MP differential witnesses",
      "GSLT.LanguageDef.HOLKernelProfiles.hol4LcfKernel / hol4DischWitness / hol4MPWitness",
      .partiallyFormalized⟩
  , ⟨"HOL profile curriculum witness",
      "run_all exercises the new GSLT/OSLF profile differentials and recursive proof articles through a Lean curriculum witness, separate from the older Notation/09 lambda-Pi bridge",
      "MettaKernel.Curriculum.HOL.HOLKernelProfilesWitness / oracle_cases.tsv HOL-GSLT-profile-differential",
      .partiallyFormalized⟩
  , ⟨"HOL profile proof-article checker",
      "Generic executable ProofArticle checker has a proved Boolean/Prop contract: accepted nodes perform a local reduction, export the claimed payload, and consume checked child payloads",
      "Mettapedia.OSLF.MeTTaIL.Engine.checkProofArticleWithEnv_eq_true_iff_accepted / HOLKernelProfiles.hol4SelfMPArticle / HOLKernelProfiles.holLightSelfImpArticle / oracle_cases.tsv HOL-GSLT-proof-article-checker",
      .partiallyFormalized⟩
  , ⟨"HOL logic Datalog-closure bridge",
      "Finite Datalog closure over LanguageDef.logic is lowered generically to RelationEnv tuples, has step support and trace theorems, preserves nullary-constructor tuple shape through derived closure rows, proves successful atom matches and whole satisfied body premises ground to matched tuple constants at the arity-preserving LP GroundAtom level, proves recursive executable-closure soundness into the arity-preserving LP least model, and is consumed by HOL profile relationQuery premises",
      "Mettapedia.OSLF.MeTTaIL.LogicSemantics.mem_datalogClosureStep_iff_supported / mem_datalogClosureWithFuel_iff_trace / datalogClosureTuples_allNullaryConst / logicDatalogRelationEnv_tuples_allNullaryConst / matchDatalogAtomOnTuple?_grounds_terms / satisfyDatalogAtom_mem_ground_terms / satisfyDatalogBody_mem_ground_terms / satisfyDatalogBody_mem_arity_ground_atom / datalogClauseToGroundFactTuple?_groundAtom_in_leastModel / deriveDatalogClauseTuples_in_leastModel / datalogClosureWithFuel_in_leastModel / datalogClosureTuples_in_leastModel / logicDatalogRelationEnv_tuples_in_leastModel / unsafeVariableFactAtom_in_leastModel / unsafeVariableFactTuple_not_in_executable_closure / mem_logicDatalogRelationEnv_tuples_iff / datalogClauseToArityLPClause / langDefArity_clause_head_in_leastModel / LPRelationEnvBridge.leastHerbrandModelRelEnv_sound / TypeSynthesis.langOSLFWithLogic / HOLKernelProfiles.hol4LogicRelationEnv / oracle_cases.tsv HOL-GSLT-logic-crux",
      .partiallyFormalized⟩
  , ⟨"HOL4 external calibration",
      "Representative HOL4 primitive-rule examples REFL, DISCH/ASSUME, and BETA_CONV build under the local Holmake curriculum script",
      "MettaKernel.Curriculum.HOL.HOL06_lcf_kernelScript / oracle_cases.tsv HOL4-real-lcf-kernel-smoke",
      .partiallyFormalized⟩
  , ⟨"HOL Light external calibration",
      "Runnable HOL Light SELF_IMP calibration via equality-kernel derivation rather than primitive DISCH",
      "MettaKernel.Curriculum.HOL.HOLLightSelfImpSmoke / oracle_cases.tsv HOL-light-real-eq-kernel-self-imp",
      .partiallyFormalized⟩
  , ⟨"HOL Light SELF_IMP profile replay",
      "HOLLightEqKernel has a bounded A ==> A replay through HOL Light equality-kernel definitions and rejects the primitive-DISCH shortcut",
      "HOLKernelProfiles.holLightSelfImpWitness / HOLKernelProfilesWitness / oracle_cases.tsv HOL-GSLT-HOLLight-self-imp-profile",
      .partiallyFormalized⟩
  , ⟨"HOL Light generic definition replay",
      "Generic replay of HOL Light bool.ml derived rules across arbitrary boolean terms, rather than the bounded A ==> A spine",
      "open: bounded SELF_IMP profile replay is checked; generic CONJ/CONJUNCT1/DISCH/MP definition replay is not compiled from source definitions yet",
      .notFormalized⟩
  , ⟨"O3 logic-to-checker",
      "Generic compilation of LanguageDef.logic declarations into a proof checker consumed by langOSLF/langRewriteSystem",
      "open: finite Datalog closure is consumed through logicDatalogRelationEnv with support/trace theorems, nullary-constructor tuple preservation, atom-match grounding to tuple constants, body-premise grounding for final successful bindings at the arity-preserving LP GroundAtom level, and recursive executable-closure soundness into the arity-preserving LP least model; an unsafe variable fact counterexample proves unrestricted converse completeness is false; proof-article checker acceptance has an internal contract theorem; ruleText compilation, safe-program completeness, and external-kernel checker adequacy are not compiled yet",
      .notFormalized⟩
  , ⟨"HOL replay equivalence",
      "Machine-checked replay evidence that HOL Light and HOL4 prove the same theorem set for the shared HOL/STT fragment",
      "open: no replay theorem or cross-kernel proof-article equivalence is claimed here",
      .notFormalized⟩
  ]

def holKernelCountByStatus (s : NTTClaimStatus) : Nat :=
  (holKernelClaimList.filter (fun c => c.status = s)).length

def holKernelOpenClaims : List NTTClaim :=
  holKernelClaimList.filter (fun c =>
    c.status = .partiallyFormalized || c.status = .notFormalized)

def holKernelOpenCount : Nat :=
  holKernelOpenClaims.length

/-- HOL-kernel generic adequacy is explicitly still open. -/
theorem holKernelOpenCount_eq : holKernelOpenCount = 11 := by
  decide

/-- No HOL-kernel row is currently classified as fully proven. -/
theorem holKernelProvenCount_eq : holKernelCountByStatus .proven = 0 := by
  decide

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

/-- Endpoint unresolved count is zero for this tracker inventory. -/
theorem nttRemainingCount_zero : nttRemainingCount = 0 := by
  decide

/-- Resolved endpoint claims currently classified as `proven`.
    This is an endpoint-inventory count only. -/
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

/-- Endpoint parity inventory in this tracker is closed. -/
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
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.mem_datalogClosureStep_iff_supported
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.mem_datalogClosureWithFuel_iff_trace
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.datalogClosureStep_preserves_allNullaryConst
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.datalogClosureWithFuel_preserves_allNullaryConst
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.datalogClosureTuples_allNullaryConst
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.logicDatalogRelationEnv_tuples_allNullaryConst
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.matchDatalogAtomOnTuple?_grounds_terms
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.satisfyDatalogAtom_mem_ground_terms
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.satisfyDatalogBody_mem_ground_terms
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.satisfyDatalogBody_mem_arity_ground_atom
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.datalogClauseToGroundFactTuple?_groundAtom_in_leastModel
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.deriveDatalogClauseTuples_in_leastModel
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.datalogClosureWithFuel_in_leastModel
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.datalogClosureTuples_in_leastModel
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.logicDatalogRelationEnv_tuples_in_leastModel
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.unsafeVariableFactAtom_in_leastModel
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.unsafeVariableFactTuple_not_in_executable_closure
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.unsafeVariableFactLang_validate_rejects
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.mem_logicDatalogRelationEnv_tuples_iff
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.datalogClauseToArityLPClause
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.langDefArity_clause_head_in_leastModel
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.langDefArity_groundFactTuple_head_in_leastModel
#check @Mettapedia.OSLF.MeTTaIL.LPRelationEnvBridge.leastHerbrandModelRelEnv_complete
#check @Mettapedia.OSLF.MeTTaIL.LPRelationEnvBridge.leastHerbrandModelRelEnv_sound
#check Mettapedia.OSLF.MeTTaIL.Engine.checkProofArticleWithEnv_eq_true_iff_accepted
#print axioms Mettapedia.OSLF.MeTTaIL.LogicSemantics.mem_datalogClosureWithFuel_iff_trace
#print axioms Mettapedia.OSLF.MeTTaIL.LogicSemantics.datalogClosureTuples_allNullaryConst
#print axioms Mettapedia.OSLF.MeTTaIL.LogicSemantics.logicDatalogRelationEnv_tuples_allNullaryConst
#print axioms Mettapedia.OSLF.MeTTaIL.LogicSemantics.matchDatalogAtomOnTuple?_grounds_terms
#print axioms Mettapedia.OSLF.MeTTaIL.LogicSemantics.satisfyDatalogAtom_mem_ground_terms
#print axioms Mettapedia.OSLF.MeTTaIL.LogicSemantics.satisfyDatalogBody_mem_ground_terms
#print axioms Mettapedia.OSLF.MeTTaIL.LogicSemantics.satisfyDatalogBody_mem_arity_ground_atom
#print axioms Mettapedia.OSLF.MeTTaIL.LogicSemantics.deriveDatalogClauseTuples_in_leastModel
#print axioms Mettapedia.OSLF.MeTTaIL.LogicSemantics.datalogClosureTuples_in_leastModel
#print axioms Mettapedia.OSLF.MeTTaIL.LogicSemantics.logicDatalogRelationEnv_tuples_in_leastModel
#print axioms Mettapedia.OSLF.MeTTaIL.LogicSemantics.unsafeVariableFactAtom_in_leastModel
#print axioms Mettapedia.OSLF.MeTTaIL.LogicSemantics.unsafeVariableFactTuple_not_in_executable_closure
#print axioms Mettapedia.OSLF.MeTTaIL.LogicSemantics.mem_logicDatalogRelationEnv_tuples_iff
#print axioms Mettapedia.OSLF.MeTTaIL.LogicSemantics.langDefArity_clause_head_in_leastModel
#print axioms Mettapedia.OSLF.MeTTaIL.LogicSemantics.langDefArity_groundFactTuple_head_in_leastModel
#print axioms Mettapedia.OSLF.MeTTaIL.LPRelationEnvBridge.leastHerbrandModelRelEnv_sound
#print axioms Mettapedia.OSLF.MeTTaIL.Engine.checkProofArticleWithEnv_eq_true_iff_accepted

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
