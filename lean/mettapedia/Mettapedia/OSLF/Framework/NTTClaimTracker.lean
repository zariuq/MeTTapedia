import Mettapedia.OSLF.PresheafNativeType.InternalLanguage
import Mettapedia.OSLF.PresheafNativeType.TheoryRestriction
import Mettapedia.OSLF.Framework.ToposTOGLBridge
import Mettapedia.OSLF.Framework.CategoryBridge
import Mettapedia.OSLF.Framework.AssumptionNecessity
import Mettapedia.OSLF.Framework.BeckChevalleyOSLF
import Mettapedia.OSLF.MeTTaIL.LPRelationEnvBridge
import Mettapedia.GSLT.Topos.PresheafPredicateProjection
import Mettapedia.GSLT.Topos.PresheafFunctionPredicateJudgments
import Mettapedia.OSLF.Bridges.TypeTheory.DependentNativeTypes
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambdaControls
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingMonadic

/-!
# Native Type Theory Strict Claim Tracker

This tracker is keyed to endpoint-claim anchors in the Native Type Theory
paper (ACT 2021 numbering). It includes the categorical core, generated syntax,
the behavior-rule comparison and the explicit translation of Proposition 32.
Examples and external applications require their own adequacy checks.

It records endpoint anchors and remaining source obligations. Declaration
existence and metadata counts do not certify statement fidelity. Semantic
adequacy of the operational modal route is tracked separately in bridge modules.
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
  [ ⟨"Def 1 / Def 6", "Cartesian closed theories with pullbacks, lex closed translations and their structured 2-categories",
      "GSLT.Core.LambdaTheoryWithEquality packages the category; LambdaTheoryMorphism currently records finite limits but not exponential preservation. The source 2-category and structured coslice/arrow 2-categories are not assembled", .partiallyFormalized⟩
  , ⟨"Def 3 / Thm 4", "Internal behavior rules compared with deterministic GSOS laws, with the admitted rule format explicit",
      "Binding signatures and free rule-local firing models exist in OSLF.Syntax; a translation of the authored behavior-rule format to GSOS distributive laws and its converse have not been proved. The first-order result cannot be applied to arbitrary binding LanguageDefs without further hypotheses", .notFormalized⟩
  , ⟨"Def 11", "Predicate fibration piOmega on presheaves over any small category, with presheaf values in the same universe",
      "Topos.presheafPredicateFunctor / predicateReindex_identity / predicateReindex_composition / PresheafPredicateTotal / presheafPredicateProjection / predicateTotalHomEquiv / predicateLift_stronglyCartesian / predicateLift_factorization / presheafPredicateProjection_fibered: actual Grothendieck total category with source-shaped morphisms and unique factorization; predicateLift_original_pullback connects the original subfunctor preimage operations", .proven⟩
  , ⟨"Sec 3", "Native type as (sort, predicate) pair",
      "NativeType.NativeType / NativeType.NativeTypeFiber", .proven⟩
  , ⟨"Prop 12", "Indexed adjoints (exists_f dashv Omega^f dashv forall_f) with Beck-Chevalley",
      "NativeType.prop12_package / NativeType.prop12_beckChevalley", .proven⟩
  , ⟨"Prop 14", "Cartesian closed total predicate category and cartesian closed projection, for presheaves in the common universe",
      "Topos.PredicateCartesianClosed.cartesian / closed / exponentialAdjunction / projectionClosed: actual Mathlib category and functor instances, using the existing expHomEquiv; projection_expComparison proves the canonical comparison invertible", .proven⟩
  , ⟨"Def 15", "Yoneda-restricted predicate theory is a lambda theory fibered over the source lambda theory",
      "Topos.yonedaReindex_id / yonedaReindex_comp / yonedaReindex_himp / yonedaExpPredicate supply indexed operations. The exponential representability witness is still an argument, and the cartesian closed restricted total category is not assembled", .partiallyFormalized⟩
  , ⟨"Prop 17", "Function-object reification right adjoint to curried evaluation",
      "NativeType.prop17_reification supplies only a same-fiber infimum with monotonicity and a one-sided bound. The function-object adjunction is now built: Topos.applyPred is curried evaluation on predicates (the direct image along evaluation of argument-and-function), Topos.reifyPred is its reification, and Topos.reify_adjunction is the adjunction as a biconditional, with Topos.applyPred_reifyPred_le and Topos.le_reifyPred_applyPred as counit and unit derived from it. Topos.reifyPred_unique proves any operation satisfying the same biconditional is this one, so it is an adjoint rather than a bound that happens to hold. Topos.reifyPred_le_expPredicate is the typed comparison with the exponential predicate, and Topos.mem_expPredicate gives the stagewise reading on generalized elements. The transformer argument is an arbitrary function between predicate fibres; monotonicity is not assumed. Naturality in the object arguments is not established", .proven⟩
  , ⟨"Prop 18", "Total predicate category has small limits and colimits, preserved by its projection",
      "Topos.PredicateLimits.liftedIsLimit / liftedIsColimit / hasLimitsOfSize / hasColimitsOfSize / projectionPreservesLimits / projectionPreservesColimits: explicit cone and cocone universal properties over the existing projection", .proven⟩
  , ⟨"Prop 19", "Higher-order predicate fibration with cosmic total category",
      "Topos.PredicateCartesianClosed and PredicateLimits supply the cosmic total structure. SubobjectClassifier supplies natTransEquivSubfunctor and presheafCategoryHasClassifier. The generic higher-order-fibration structure and its compatibility with the chosen total fibration remain to be assembled", .partiallyFormalized⟩
  , ⟨"Prop 20", "Dependent slice pseudofunctor with logical pullback functors, dependent sums/products and Beck-Chevalley",
      "TypeTheory.DisplayedPresheafSlice.equivalence and SliceSubstitution.substitutionIso identify the existing family CwF with actual presheaf slices. PresheafDependentAdjunction supplies Sigma/pullback/Pi adjunctions, beta/eta, identity and composition comparisons; PresheafDependentBaseChange.piBaseChange supplies Beck-Chevalley with evaluation and transpose laws. DisplayedPresheafSlicePi/Sigma compare the existing indexed formers. The full logical slice pseudofunctor, including coherence of its chosen structure, remains to be assembled", .partiallyFormalized⟩
  , ⟨"Def 21", "Codomain fibration piDelta + Cartesian lifts via pullbacks",
      "NativeType.def21_cartesianLift_universal_unique / def21_cartesianLift_stronglyCartesian / codomain_fibered: the existing pullback construction now satisfies unique Cartesian factorization and Mathlib IsFibered", .proven⟩
  , ⟨"Prop 22", "Codomain fibration is a closed comprehension category with cosmic total category",
      "NativeType.codomain_fibered supplies Cartesian lifts; Topos.ImageComprehension supplies the image/comprehension adjunction. Bridges.TypeTheory.DependentNativeTypes identifies native Cartesian lifts with the proof-relevant CwF, its dependent adjoints and its support observation. TypeTheory.DisplayedPresheafPi supplies CwF formation, abstraction, application and beta/eta; PiSubstitution connects natural-context substitution. The source's full closed comprehension and cosmic codomain structure is not yet packaged", .partiallyFormalized⟩
  , ⟨"Sec 4 (adjunction)", "Image-comprehension adjunction between the actual total predicate and dependent-type categories",
      "Topos.ImageComprehension.imageFunctor / comprehensionFunctor / homEquiv / adjunction / comprehensionFullyFaithful; Controls.image_not_faithful shows the image functor forgets witness distinctions", .proven⟩
  , ⟨"Thm 23", "Internal-language 2-functor, including its categorical action and coherence",
      "NativeType.thm23_internalLanguagePackage now uses one presheaf level consistently. Topos.LogicalTransport supplies actual restriction functors on both total categories, the predicateTranslationFunctor on theory natural transformations, horizontal whiskering, and image/comprehension unit/counit compatibility. The all-toposes domain, the HDT-Sigma target 2-category and dependent-fibre coherence are not constructed", .partiallyFormalized⟩
  , ⟨"Sec 4 (syntax)", "Generated higher-order dependent native syntax, with substitution coherence and its interpretation",
      "Semantic operations are constructed; raw modal syntax is initial as an algebra in Framework.InitialModalSchema. Neither that raw initiality nor the image/comprehension adjunction establishes the dependent syntax classifying universal property. Equality and quotient syntax are also excluded by the paper itself", .partiallyFormalized⟩
  , ⟨"Sec 5", "Theory translation by presheaf precomposition, with Pi/Omega preservation requiring additional hypotheses",
      "Topos.LogicalTransport.restrictPredicates / restrictDependentTypes / predicateTranslationFunctor / restrictPredicate_preimage establish actual presheaf precomposition and substitution compatibility. Predicate implication and universal quantification are preserved under LiftsRestrictions. This does not yet establish the full dependent-Pi and classifier comparison", .partiallyFormalized⟩
  , ⟨"Sec 5", "Colax Pi/Sigma/Prop translation for the source theory-translation action",
      "Topos.LogicalTransport.restrict_implication_le / restrict_forall_le give the actual predicate comparisons; restrictPredicate_image gives exact existential transport. PresheafPosetRestriction.restrict_implication_iff_liftsRestrictions gives an exact criterion for poset contexts; TheoryRestriction.context_closure_discriminates gives positive and negative controls. Dependent-type Pi comparison and its coherence remain open", .partiallyFormalized⟩
  , ⟨"Sec 5", "Representable Pi/Sigma transport package; canonical closure/fixpoint wrappers retain their own strength and transport hypotheses, not a general evidence-to-strength theorem",
      "ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_pack_via_rulePack / ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_via_rulePack / ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_pack_via_prop12 / ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_via_prop12_pack / OSLFNTTWMCanonicalClosure.canonical_rulePack_transport_pack_and_fixpoint_endpoint_of_goal / OSLFNTTWMCanonicalClosure.canonical_prop12_transport_pack_and_fixpoint_endpoint_of_goal / OSLFNTTWMCanonicalClosure.canonical_rulePack_transport_pack_and_fixpoint_endpoint_of_transportGoal / OSLFNTTWMCanonicalClosure.canonical_prop12_transport_pack_and_fixpoint_endpoint_of_transportGoal / OSLFNTTWMCanonicalClosure.canonical_rulePack_transport_piSigma_and_fixpoint_of_transportGoal / OSLFNTTWMCanonicalClosure.canonical_prop12_transport_piSigma_and_fixpoint_of_transportGoal", .proven⟩
  , ⟨"Sec 5", "Necessity audit for nonempty-family guard in Pi/Sigma package",
      "AssumptionNecessity.types_nonempty_necessary_for_piSigma", .proven⟩
  , ⟨"Prop 32", "The displayed name-passing lambda to polyadic pi translation is a morphism of the presented theories",
      "PolyadicPi.Bridges.NamePassingLambda implements all five displayed clauses with name-substitution/target-renaming coherence. NamePassingEnvironment completes the nonrecursive active environment dynamics with persistent definitions and consumed carriers. The scoped interpretation includes extrusion and binder exchange. NamePassingEnvironmentNative and NamePassingMonadic compose actual supplied endpoints, retained source origins, native finite-reachability observations and communication bounds through the private-session unary protocol. AuthoredCommunication.authoredStep_iff compares supplied schema events with independent communication. AuthoredNativeTypes independently compares the target equations and active operations with the intrinsically scoped classified presentation. NamePassingSpine composes actual scoped polyadic pi, unary protocol and core rho execution in both directions through every related phase; supplied prefixes retain endpoints and work accounts, public returned-function native observations and strong normalization agree. NamePassingObserverAdequacy proves contextual adequacy for admitted independently authored protocol clients executed through the actual rho compiler; NamePassingObserverFunctor makes context translation a functor and compilation a natural transformation. NamePassingContextMetric preserves the authored client-budget distance, with separate per-event polyadic and weak rho logical metrics. RhoUnarySpatial retains spatial cuts and duplicate occurrences throughout actual runtime phases; unrestricted separating implication has a checked counterexample. Full recursive source/static laws, the complete Proposition 32 classifying-theory morphism, unrestricted contextual observations and dependent native evidence transport remain open", .partiallyFormalized⟩
  ]

/-! ## HOL kernel-profile OSLF/NTT claim ledger

This is a separate ledger from the strict NTT-paper endpoint list above.  The
endpoint list has its own remaining source obligations; the rows below track
HOL-kernel-profile work separately.
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
  , ⟨"HOL profile article-consistency checker",
      "The bounded ProofArticle checker has a proved Boolean/Prop contract for local reduction, export, and every supplied child; children may be omitted and are not matched to exact ordered rule-premise slots, so it is not a proof-calculus checker or complete premise-provenance certificate",
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
      "open: finite Datalog closure is consumed through logicDatalogRelationEnv with support/trace theorems, nullary-constructor tuple preservation, atom-match grounding to tuple constants, body-premise grounding for final successful bindings at the arity-preserving LP GroundAtom level, and recursive executable-closure soundness into the arity-preserving LP least model; an unsafe variable fact counterexample proves unrestricted converse completeness is false; the legacy article checker has only its weak internal consistency contract and does not require exact premise provenance; ruleText compilation, safe-program completeness, and external-kernel checker adequacy are not compiled yet",
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

/-- Source anchors whose full obligations are not established by the packages. -/
theorem nttRemaining_locations : nttRemaining.map (·.loc) =
    ["Def 1 / Def 6", "Def 3 / Thm 4", "Def 15", "Prop 19", "Prop 20", "Prop 22", "Thm 23", "Sec 4 (syntax)", "Sec 5", "Sec 5", "Prop 32"] := by
  decide

/-- Exact unresolved count in the recorded inventory. -/
theorem nttRemainingCount_eq : nttRemainingCount = 11 := by
  decide

/-- Resolved endpoint claims currently classified as `proven`.
    This is an endpoint-inventory count only. -/
theorem provenCount_eq : countByStatus .proven = 10 := by
  decide

/-- No strict endpoint remains `assumptionScoped` in this tracker. -/
theorem assumptionScopedCount_eq : countByStatus .assumptionScoped = 0 := by
  decide

/-- Source claims with constructions that do not yet establish the complete claim. -/
theorem partialCount_eq : countByStatus .partiallyFormalized = 10 := by
  decide

/-- Source claims for which the required comparison theorem is not yet formalized. -/
theorem missingCount_eq : countByStatus .notFormalized = 1 := by
  decide

/-- The recorded source-obligation inventory is not closed. This is a metadata
statement, not a theorem that the remaining mathematics is impossible. -/
theorem fullNTTParity_open : nttRemainingCount ≠ 0 := by
  decide

/-! ## Anchor checks -/

#check @Mettapedia.GSLT.Topos.PredicateCartesianClosed.projectionClosed
#check @Mettapedia.GSLT.Topos.PredicateLimits.liftedIsLimit
#check @Mettapedia.GSLT.Topos.PredicateLimits.liftedIsColimit
#check @Mettapedia.GSLT.Topos.ImageComprehension.adjunction
#check @Mettapedia.GSLT.Topos.LogicalTransport.predicateTranslationFunctor
#check @Mettapedia.GSLT.Topos.LogicalTransport.restrict_implication_iff_liftsRestrictions
#check @Mettapedia.OSLF.PresheafNativeType.codomain_fibered


#check @Mettapedia.OSLF.PresheafNativeType.NativeType
#check @Mettapedia.OSLF.Framework.CategoryBridge.predFibration
#check @Mettapedia.GSLT.Topos.predicateTotalHomEquiv
#check @Mettapedia.GSLT.Topos.predicateLift_factorization
#check @Mettapedia.GSLT.Topos.presheafPredicateProjection_fibered
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_full_internal_logic_bridge_package
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_via_rulePack
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_pack_via_rulePack
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_pack_via_prop12
#check @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_representable_patternPred_piSigma_transport_via_prop12_pack
#check @Mettapedia.OSLF.PresheafNativeType.TheoryMorphism.piOmega_translation_endpoint
#check @Mettapedia.OSLF.PresheafNativeType.TheoryMorphism.piSigmaOmegaProp_translation_endpoint
#check @Mettapedia.OSLF.PresheafNativeType.TheoryMorphism.piProp_colax_rules
#check @Mettapedia.OSLF.PresheafNativeType.TheoryMorphism.piSigmaProp_colax_rules
#check Mettapedia.OSLF.PresheafNativeType.TheoryTranslationCounterexample.actual_precomposition_does_not_preserve_implication
#check Mettapedia.OSLF.PresheafNativeType.TheoryTranslationCounterexample.restrict_top
#check Mettapedia.OSLF.PresheafNativeType.TheoryTranslationCounterexample.selectTerminal_monoidalClosed
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
#check Mettapedia.OSLF.MeTTaIL.LogicSemantics.unsafeVariableFactProgram_admission_rejects
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
#check @Mettapedia.OSLF.PresheafNativeType.prop12_package
#check @Mettapedia.OSLF.PresheafNativeType.prop12_beckChevalley
#check @Mettapedia.OSLF.PresheafNativeType.prop12_piSigmaPredicateRulePack
#check @Mettapedia.OSLF.PresheafNativeType.prop12_piEta_presheaf
#check @Mettapedia.OSLF.PresheafNativeType.prop12_sigmaEta_presheaf
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.RepresentablePiSigmaTransportPack
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_patternPred_piSigma_transport_pack_via_rulePack
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_patternPred_piSigma_transport_pack_via_prop12
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_patternPred_piSigma_transport_via_rulePack
#check @Mettapedia.OSLF.PresheafNativeType.prop14_cosmicFibration
#check @Mettapedia.OSLF.PresheafNativeType.prop17_reification
#check @Mettapedia.OSLF.PresheafNativeType.def21_codomainFibration
#check @Mettapedia.OSLF.PresheafNativeType.imageComprehensionAdjunction
#check @Mettapedia.OSLF.PresheafNativeType.thm23_internalLanguagePackage

-- Strengthened endpoints (Phase 1-3)
#check @Mettapedia.OSLF.PresheafNativeType.def21_cartesianLift_proj
#check @Mettapedia.OSLF.PresheafNativeType.def21_cartesianLift_universal_comp
#check @Mettapedia.OSLF.PresheafNativeType.imageComprehension_iff
#check @Mettapedia.OSLF.PresheafNativeType.thm23_functorialLaws

end Mettapedia.OSLF.Framework.NTTClaimTracker
