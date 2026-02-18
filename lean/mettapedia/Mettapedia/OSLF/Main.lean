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
import Mettapedia.OSLF.Framework.DerivedTyping
import Mettapedia.OSLF.Framework.PLNSelectorGSLT
import Mettapedia.OSLF.Framework.PLNSelectorLanguageDef
import Mettapedia.OSLF.Framework.BeckChevalleyOSLF
import Mettapedia.OSLF.MeTTaCore.Premises
import Mettapedia.OSLF.MeTTaCore.FullLanguageDef
import Mettapedia.OSLF.Framework.MeTTaFullInstance
import Mettapedia.OSLF.Framework.MeTTaToNTT
import Mettapedia.OSLF.Formula
import Mettapedia.OSLF.Decidability
import Mettapedia.OSLF.QuantifiedFormula
import Mettapedia.OSLF.QuantifiedFormula2
import Mettapedia.Logic.OSLFDistinctionGraph
import Mettapedia.Logic.OSLFDistinctionGraphWeighted
import Mettapedia.Logic.OSLFDistinctionGraphWM
import Mettapedia.Logic.OSLFDistinctionGraphEntropy
import Mettapedia.Logic.OSLFKripkeBridge
-- SpecIndex.lean imports Main (not vice versa) — no cycle

/-!
# Operational Semantics in Logical Form (OSLF)

Re-exports for the OSLF formalization, connecting MeTTaIL language definitions
to categorical semantics via the OSLF algorithm.

## Module Structure

```
OSLF/
├── Main.lean                -- This file (re-exports)
├── Framework/
│   ├── RewriteSystem.lean         -- Abstract OSLF: RewriteSystem -> OSLFTypeSystem
│   ├── RhoInstance.lean           -- ρ-calculus instance (proven Galois connection)
│   ├── DerivedModalities.lean     -- Derived ◇/□ from adjoint triple (0 sorries)
│   ├── CategoryBridge.lean        -- Categorical lift: GaloisConnection → Adjunction
│   ├── FULLStatus.lean            -- FULL-OSLF done/missing tracker
│   ├── TypeSynthesis.lean         -- LanguageDef → OSLFTypeSystem (auto Galois)
│   ├── GeneratedTyping.lean       -- Generated typing rules from grammar
│   ├── SynthesisBridge.lean       -- Bridge: generated ↔ hand-written types
│   ├── LambdaInstance.lean        -- Lambda calculus OSLF instance (2nd example)
│   ├── PetriNetInstance.lean      -- Petri net OSLF instance (3rd, binder-free)
│   ├── TinyMLInstance.lean        -- CBV λ-calculus + booleans/pairs/thunks (4th, multi-sort)
│   ├── MeTTaMinimalInstance.lean  -- MeTTa state client (eval/unify/chain/collapse/superpose/return)
│   ├── ConstructorCategory.lean   -- Sort quiver + free category from LanguageDef
│   ├── ConstructorFibration.lean  -- SubobjectFibration + ChangeOfBase over constructors
│   ├── ModalEquivalence.lean      -- Constructor change-of-base ↔ OSLF modalities
│   ├── DerivedTyping.lean         -- Generic typing rules from categorical structure
│   ├── PLNSelectorGSLT.lean       -- Core PLN selector rules as OSLF/GSLT rewrite system
│   └── BeckChevalleyOSLF.lean    -- Substitution ↔ change-of-base (Beck-Chevalley)
├── MeTTaIL/
│   ├── Syntax.lean          -- LanguageDef AST (types, terms, equations, rewrites)
│   ├── Semantics.lean       -- InterpObj, pattern interpretation
│   ├── Substitution.lean    -- Capture-avoiding substitution
│   ├── Match.lean           -- Generic pattern matching (multiset, locally nameless)
│   ├── Engine.lean          -- Generic rewrite engine for any LanguageDef
│   ├── DeclReduces.lean     -- Declarative reduction (proven ↔ engine)
│   └── MatchSpec.lean       -- Relational matching spec (proven ↔ executable)
├── Languages/ProcessCalculi/RhoCalculus/
│   ├── Types.lean           -- Namespaces, codespaces, bisimulation
│   ├── Reduction.lean       -- COMM/DROP/PAR, modal operators, Galois connection
│   ├── Soundness.lean       -- Substitutability, progress, type preservation
│   ├── StructuralCongruence.lean
│   ├── CommRule.lean
│   ├── SpiceRule.lean
│   ├── PresentMoment.lean
│   └── Engine.lean         -- Executable rewrite engine (reduceStep, proven sound)
├── Formula.lean             -- Formula AST + bounded model checker (proven sound)
└── NativeType/
    └── Construction.lean    -- NT as (sort, pred) pairs, type formation rules
```

## Architecture

The formalization has two layers:

### Abstract Layer (Framework/)
- `RewriteSystem`: sorts + terms + reduction (INPUT to OSLF)
- `OSLFTypeSystem`: predicates + Frame + diamond/box + Galois connection (OUTPUT)
- `NativeTypeOf`: native type = (sort, predicate) pair

### Concrete Layer (RhoCalculus/)
- `Reduces`: COMM, DROP, PAR, EQUIV rules (Type-valued)
- `possiblyProp` / `relyProp`: modal operators on `Pattern -> Prop`
- `galois_connection`: proven diamond -| box
- `HasType`: Typing judgment with substitutability and progress

The concrete layer and abstract framework (`rhoOSLF`) instantiate the general
OSLF construction for ρ-calculus, lifting the proven Galois connection.

## References

- Williams & Stay, "Native Type Theory" (ACT 2021)
- Meredith & Stay, "Operational Semantics in Logical Form"
-/

namespace Mettapedia.OSLF

-- Re-export MeTTaIL modules
export Mettapedia.OSLF.MeTTaIL.Syntax (
  CollType
  TypeExpr
  TermParam
  SyntaxItem
  GrammarRule
  Pattern
  FreshnessCondition
  Premise
  Equation
  RewriteRule
  LanguageDef
  rhoCalc
  rhoCalcSetExt
)

export Mettapedia.OSLF.MeTTaIL.Semantics (
  InterpObj
  WellFormedLanguage
)

export Mettapedia.OSLF.MeTTaIL.Substitution (
  SubstEnv
  applySubst
  freeVars
  isFresh
  commSubst
)

export Mettapedia.OSLF.MeTTaIL.Match (
  matchPattern
  matchBag
  matchArgs
  applyBindings
  applyRule
  rewriteStep
)

export Mettapedia.OSLF.MeTTaIL.Engine (
  rewriteStepNoPremises
  rewriteWithContextNoPremises
  rewriteWithContext
  RelationEnv
  premiseHoldsWithEnv
  premisesHoldWithEnv
  applyRuleWithPremisesUsing
  rewriteStepWithPremisesUsing
  rewriteWithContextWithPremisesUsing
  fullRewriteToNormalFormWithPremisesUsing
  premiseHolds
  premisesHold
  applyRuleWithPremises
  rewriteStepWithPremises
  rewriteWithContextWithPremises
  fullRewriteToNormalForm
  fullRewriteToNormalFormWithPremises
)

export Mettapedia.OSLF.MeTTaIL.DeclReduces (
  DeclReduces
  engine_sound
  engine_complete
  declReduces_iff_langReduces
)

export Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises (
  DeclReducesWithPremises
  engineWithPremisesUsing_sound
  engineWithPremisesUsing_complete
  engineWithPremises_sound
  engineWithPremises_complete
  declReducesWithPremises_iff_langReducesWithPremisesUsing
  declReducesWithPremises_iff_langReducesWithPremises
)

export Mettapedia.OSLF.MeTTaIL.MatchSpec (
  MatchRel
  MatchArgsRel
  MatchBagRel
  matchPattern_sound
  matchArgs_sound
  matchBag_sound
  matchRel_complete
  matchArgsRel_complete
  matchBagRel_complete
  matchPattern_iff_matchRel
  DeclReducesRel
  declReducesRel_iff_declReduces
  engine_sound_rel
  engine_complete_rel
)

-- Re-export RhoCalculus modules
export Mettapedia.Languages.ProcessCalculi.RhoCalculus (
  ProcObj
  NameObj
  NamePred
  ProcPred
  BarbedParams
  BarbedRelation
  ProcEquiv
)

export Mettapedia.Languages.ProcessCalculi.RhoCalculus.Soundness (
  NativeType
  TypingContext
  HasType
  substitutability
  comm_preserves_type
  quoteDropEmpty_irreducible
)

export Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction (
  Reduces
  possiblyProp
  relyProp
  galois_connection
  ioCount
  ioCount_SC
  redWeight
  redWeight_SC
  redWeight_pos_of_reduces
  emptyBag_SC_irreducible
)

-- Re-export Engine module
export Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine (
  reduceStep
  reduceToNormalForm
  reduceAll
  emptyBag_reduceStep_nil
  reduceStep_sound
)

-- Re-export Framework modules
export Mettapedia.OSLF.Framework (
  RewriteSystem
  OSLFTypeSystem
  NativeTypeOf
  Substitutability
)

export Mettapedia.OSLF.Framework.RhoInstance (
  RhoSort
  rhoRewriteSystem
  rhoOSLF
  rho_mathlib_galois
)

export Mettapedia.OSLF.Framework.DerivedModalities (
  ReductionSpan
  derivedDiamond
  derivedBox
  derived_galois
  rhoSpan
  derived_diamond_eq_possiblyProp
  derived_box_eq_relyProp
  rho_galois_from_span
)

export Mettapedia.OSLF.Framework.TypeSynthesis (
  langReducesExecUsing
  langReducesUsing
  langReduces
  langReducesUsing_iff_execUsing
  langReducesUsing_to_exec
  exec_to_langReducesUsing
  langRewriteSystemUsing
  langRewriteSystem
  langSpanUsing
  langSpan
  langDiamondUsing
  langDiamond
  langBoxUsing
  langBox
  langGaloisUsing
  langGalois
  langDiamondUsing_spec
  langOSLF
  langBoxUsing_spec
  langDiamond_spec
  langBox_spec
  langNativeType
  rhoCalc_emptyBag_rewrite_nil
  rhoCalc_emptyBag_langReduces_irreducible
  rhoCalc_soundBridge_restricted
  rhoCalc_SC_emptyBag_reduceStep_irreducible
  rhoCalc_SC_emptyBag_langReduces_false_of_reduceStep
  rhoCalc_SC_emptyBag_langReduces_irreducible_of_soundBridge
  rhoCalc_SC_emptyBag_no_diamondTop_of_soundBridge
)

export Mettapedia.OSLF.Framework.ToposReduction (
  InternalReductionGraph
  ReductionGraphObj
  patternConstPresheaf
  pairConstPresheaf
  reductionSubfunctorUsing
  reductionSubfunctor
  reductionSourceUsing
  reductionTargetUsing
  reductionGraphUsing
  reductionGraph
  reductionGraphObjUsing
  reductionGraphObj
  mem_reductionSubfunctorUsing_iff
  reductionGraphUsing_edge_endpoints_iff
  langDiamondUsing_iff_exists_graphStep
  langBoxUsing_iff_forall_graphIncoming
  langDiamondUsing_iff_exists_graphObjStep
  langBoxUsing_iff_forall_graphObjIncoming
  langDiamondUsing_iff_exists_internalStep
  langBoxUsing_iff_forall_internalStep
  langDiamond_iff_exists_graphStep
  langBox_iff_forall_graphIncoming
  langDiamond_iff_exists_internalStep
  langBox_iff_forall_internalStep
  exec_mem_reductionSubfunctorUsing
  reductionSubfunctorUsing_mem_exec
)

export Mettapedia.OSLF.Framework.GeneratedTyping (
  GenNativeType
  GenTypingContext
  GenHasType
  topPred
)

export Mettapedia.OSLF.Framework.SynthesisBridge (
  langDiamond_implies_possibly_at
  possibly_implies_langDiamond_at
  specialized_possibly
  specialized_rely_check
  specialized_can_reduce
  specialized_soundBridge_at
  nativeToGen
  ctxToGen
)

export Mettapedia.OSLF.Framework.CategoryBridge (
  langDiamond_monotone
  langBox_monotone
  PredLattice
  langGaloisL
  langModalAdjunction
  rhoModalAdjunction
  SortCategoryInterface
  defaultSortCategoryInterface
  lambdaTheorySortInterface
  typeSortsRewriteSystem
  typeSortsOSLF
  typeSortsLambdaTheory
  typeSortsLambdaInterface
  SortCategory
  SortPresheafCategory
  predFibrationSortApprox
  predFibrationUsing
  predFibration
  predFibration_presheafSortApprox_agreement
  oslf_fibrationSortApprox
  oslf_fibrationUsing
  oslf_fibration
  typeSortsPredFibrationViaLambdaInterface
  typeSortsOSLFFibrationViaLambdaInterface
  typeSortsOSLFFiberFamily
  typeSortsOSLFFibrationUsing_presheafAgreement
  langOSLFFiberFamily
  langOSLFFibrationUsing_presheafAgreement
  rhoLangOSLFFiberFamily
  rhoLangOSLFFibrationUsing_presheafAgreement
  languagePresheafObj
  languagePresheafLambdaTheory
  languageSortRepresentableObj
  languageSortFiber
  languageSortPredNaturality
  commDiPred
  commDiWitnessLifting
  PathSemClosedPred
  CommDiPathSemLiftPkg
  commDiPathSemLiftPkg_of_liftEq
  commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
  commDiWitnessLifting_of_pathSemLiftPkg
  languageSortPredNaturality_commDi_pathSemClosed_of_pkg
  pathSem_commSubst
  pathSemClosedPred_closed
  languageSortPredNaturality_commDi
  commDiWitnessLifting_of_pathSemClosed
  languageSortPredNaturality_commDi_pathSemClosed
  commDiWitnessLifting_of_lift
  commDiWitnessLifting_of_pathSemLift
  languageSortFiber_ofPatternPred
  languageSortFiber_ofPatternPred_map_mem
  languageSortFiber_ofPatternPred_subobject
  languageSortFiber_ofPatternPred_characteristicMap
  languageSortFiber_ofPatternPred_characteristicMap_spec
  languageSortFiber_ofPatternPred_mem_iff
  languageSortFiber_ofPatternPred_mem_iff_satisfies
  rhoProc_langOSLF_predicate_to_fiber_mem_iff
  rho_proc_pathSemLift_pkg
  rho_proc_commDiWitnessLifting_of_pkg
  rhoProcOSLFUsingPred
  rhoProcOSLFUsingPred_to_languageSortFiber
  rhoProcOSLFUsingPred_to_languageSortFiber_mem_iff
  languageSortFiber_characteristicEquiv
  languageSortPredicateFibration
  rhoProcRepresentableObj
  rhoProcSortFiber
  rhoProcSortFiber_characteristicEquiv
  rhoSortPredicateFibration
)

export Mettapedia.OSLF.Framework.FULLStatus (
  MilestoneStatus
  Milestone
  tracker
  countBy
  remaining
)

export Mettapedia.OSLF.Framework.LambdaInstance (
  lambdaCalc
  lambdaOSLF
  lambdaGalois
)

export Mettapedia.OSLF.Framework.PetriNetInstance (
  petriNet
  petriOSLF
  petriGalois
)

export Mettapedia.OSLF.Framework.TinyMLInstance (
  tinyML
  tinyMLOSLF
  tinyMLGalois
  tinyML_crossings
  tinyExprObj
  tinyValObj
  injectArrow
  thunkArrow
  injectMor
  thunkMor
  inject_di_pb_adj
  thunk_di_pb_adj
  thunk_is_quoting
  inject_is_reflecting
  thunk_action_eq_diamond
  inject_action_eq_box
  tinyML_typing_action_galois
  tinyML_commDiPathSemLiftPkg_of_liftEq
  tinyML_checker_sat_to_pathSemClosed_commDi_bc_graph
  tinyML_checker_sat_to_pathSemClosed_commDi_bc_graph_of_liftEq
)

export Mettapedia.OSLF.Framework.MeTTaMinimalInstance (
  mettaMinimal
  mettaMinimalOSLF
  mettaMinimalGalois
  mettaState
  mettaMinimal_pathOrder
  mettaMinimal_commDiPathSemLiftPkg_of_liftEq
  mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph
  mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph_of_liftEq
  mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph_auto
  mettaSpecAtomCheck
  mettaSpecAtomSem
  mettaMinimal_checkLangUsing_sat_sound_specAtoms
  mettaMinimal_checkLang_sat_sound_specAtoms
)

export Mettapedia.OSLF.MeTTaCore.Premises (
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

export Mettapedia.OSLF.MeTTaCore.FullLanguageDef (
  mettaFull
  mettaFullOSLF
  mettaFullGalois
  mettaFullRelEnv
)

export Mettapedia.OSLF.Framework.MeTTaFullInstance (
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

export Mettapedia.OSLF.Framework.ConstructorCategory (
  LangSort
  baseSortOf
  unaryCrossings
  SortArrow
  SortPath
  ConstructorObj
  constructorCategory
  arrowSem
  pathSem
  pathSem_comp
  liftFunctor
  lift_map_unique
)

export Mettapedia.OSLF.Framework.ConstructorFibration (
  constructorFibration
  constructorPullback
  constructorDirectImage
  constructorUniversalImage
  constructorChangeOfBase
)

export Mettapedia.OSLF.Framework.ModalEquivalence (
  nquoteTypingAction
  pdropTypingAction
  typing_action_galois
  diamondAction
  boxAction
  action_galois
)

export Mettapedia.OSLF.Framework.DerivedTyping (
  ConstructorRole
  classifyArrow
  typingAction
  DerivedHasType
  nquote_is_quoting
  pdrop_is_reflecting
  nquote_action_eq_diamond
  pdrop_action_eq_box
)

export Mettapedia.OSLF.Framework.PLNSelectorGSLT (
  PLNSelectorSort
  PLNSelectorExpr
  PLNSelectorExpr.Reduces
  PLNSelectorExpr.reduces_sound_strength
  PLNSelectorExpr.rtc_reduces_sound_strength
  plnSelectorRewriteSystem
  plnSelectorOSLF
  oslf_diamond_extBayes2
  oslf_diamond_extBayesFamily
)

export Mettapedia.OSLF.Framework.PLNSelectorLanguageDef (
  plnSelectorLanguageDef
  plnSelectorLangReduces
  NormalizeFiniteNonzero
  EncodeInjective
  reduces_to_langReduces_exists
  langReduces_to_reduces_exists_of_normalizeFinite
  langReduces_exists_iff_reduces_exists_of_normalizeFinite
  langReduces_encode_to_encode_reduces_of_encodeInjective
  langReduces_encode_to_encode_reduces_of_atomFree
  plnSelector_checkLangUsing_sat_sound
  plnSelector_checkLangUsing_sat_sound_graph
)

export Mettapedia.OSLF.Framework.BeckChevalleyOSLF (
  presheafPrimary_beckChevalley_transport
  presheaf_beckChevalley_square_direct
  representable_patternPred_beckChevalley
  representable_commDi_patternPred_beckChevalley
  representable_commDi_patternPred_beckChevalley_of_lifting
  representable_commDi_patternPred_beckChevalley_of_pathSemLift
  representable_commDi_patternPred_beckChevalley_of_pathSemClosed
  representable_commDi_patternPred_beckChevalley_of_pathSemLiftPkg
  representable_commDi_bc_and_graphDiamond
  representable_commDi_bc_and_graphDiamond_of_lifting
  representable_commDi_bc_and_graphDiamond_of_pathSemLift
  representable_commDi_bc_and_graphDiamond_of_pathSemClosed
  representable_commDi_bc_and_graphDiamond_of_pathSemLiftPkg
  rhoProc_commDi_bc_and_graphDiamond_of_pathSemLift_pkg
  langDiamondUsing_graph_transport
  langBoxUsing_graph_transport
  commDi_diamond_graph_step_iff
  commDi_diamond_graphObj_square
  commDi_diamond_graphObj_square_direct
  galoisConnection_comp
  commMap
  commPb
  commDi
  commUi
  comm_di_pb_adj
  comm_pb_ui_adj
  diamond_commDi_galois
  commDi_diamond_galois
  typedAt
  substitutability_pb
  substitutability_di
  comm_beck_chevalley
  commSubst_eq_open_constructorSem
  strong_bc_fails
)

-- Re-export Formula module (OSLF output artifact)
export Mettapedia.OSLF.Formula (
  OSLFFormula
  sem
  sem_dia_eq_langDiamondUsing
  sem_dia_eq_graphStepUsing
  sem_box_eq_graphIncomingUsing
  sem_box_eq_graphObjIncomingUsing
  sem_box_eq_graphIncoming
  sem_dia_eq_langDiamond
  sem_box_eq_langBoxUsing
  sem_box_eq_langBox
  formula_galoisUsing
  formula_galois
  rhoCalc_SC_empty_sem_diaTop_unsat_reduceStep
  rhoCalc_SC_empty_sem_diaTop_unsat_langReduces_of_reduceStep
  CheckResult
  check
  checkLangUsing
  checkLang
  check_sat_sound
  checkLangUsing_sat_sound
  checkLangUsing_sat_sound_sort_fiber
  checkLangUsing_sat_sound_sort_fiber_mem_iff
  checkLangUsing_sat_sound_proc_fiber
  checkLangUsing_sat_sound_proc_fiber_using
  checkLangUsing_sat_sound_proc_fiber_using_mem_iff
  checkLang_sat_sound_proc_fiber
  checkLang_sat_sound_proc_fiber_using
  checkLangUsing_sat_sound_graph
  checkLangUsing_sat_sound_graph_box
  checkLang_sat_sound
  aggregateBox
  aggregateBox_sat
  checkWithPred
  checkWithPred_sat_sound
  checkLangUsingWithPred
  checkLangWithPred
  checkLangUsingWithPred_sat_sound
  checkLangUsingWithPred_sat_sound_graph_box
  checkLangUsingWithPred_sat_sound_graphObj_dia
  checkLangUsingWithPred_sat_sound_graphObj_box
  checkLangWithPred_sat_sound
  rhoAtoms
  rhoAtomSem
  rhoAtoms_sound
)

end Mettapedia.OSLF
