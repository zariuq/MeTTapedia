import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Semantics
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.MeTTaIL.DeclReduces
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.OSLF.RhoCalculus.Types
import Mettapedia.OSLF.RhoCalculus.Soundness
import Mettapedia.OSLF.RhoCalculus.Reduction
import Mettapedia.OSLF.RhoCalculus.Engine
import Mettapedia.OSLF.PiCalculus.Main
import Mettapedia.OSLF.Framework.RewriteSystem
import Mettapedia.OSLF.Framework.RhoInstance
import Mettapedia.OSLF.Framework.DerivedModalities
import Mettapedia.OSLF.Framework.CategoryBridge
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.GeneratedTyping
import Mettapedia.OSLF.Framework.SynthesisBridge
import Mettapedia.OSLF.Framework.LambdaInstance
import Mettapedia.OSLF.Framework.PetriNetInstance
import Mettapedia.OSLF.Framework.TinyMLInstance
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.ConstructorFibration
import Mettapedia.OSLF.Framework.ModalEquivalence
import Mettapedia.OSLF.Framework.DerivedTyping
import Mettapedia.OSLF.Framework.BeckChevalleyOSLF
import Mettapedia.OSLF.Formula
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
│   ├── TypeSynthesis.lean         -- LanguageDef → OSLFTypeSystem (auto Galois)
│   ├── GeneratedTyping.lean       -- Generated typing rules from grammar
│   ├── SynthesisBridge.lean       -- Bridge: generated ↔ hand-written types
│   ├── LambdaInstance.lean        -- Lambda calculus OSLF instance (2nd example)
│   ├── PetriNetInstance.lean      -- Petri net OSLF instance (3rd, binder-free)
│   ├── TinyMLInstance.lean        -- CBV λ-calculus + booleans/pairs/thunks (4th, multi-sort)
│   ├── ConstructorCategory.lean   -- Sort quiver + free category from LanguageDef
│   ├── ConstructorFibration.lean  -- SubobjectFibration + ChangeOfBase over constructors
│   ├── ModalEquivalence.lean      -- Constructor change-of-base ↔ OSLF modalities
│   ├── DerivedTyping.lean         -- Generic typing rules from categorical structure
│   └── BeckChevalleyOSLF.lean    -- Substitution ↔ change-of-base (Beck-Chevalley)
├── MeTTaIL/
│   ├── Syntax.lean          -- LanguageDef AST (types, terms, equations, rewrites)
│   ├── Semantics.lean       -- InterpObj, pattern interpretation
│   ├── Substitution.lean    -- Capture-avoiding substitution
│   ├── Match.lean           -- Generic pattern matching (multiset, locally nameless)
│   ├── Engine.lean          -- Generic rewrite engine for any LanguageDef
│   ├── DeclReduces.lean     -- Declarative reduction (proven ↔ engine)
│   └── MatchSpec.lean       -- Relational matching spec (proven ↔ executable)
├── RhoCalculus/
│   ├── Types.lean           -- Namespaces, codespaces, bisimulation
│   ├── Reduction.lean       -- COMM/DROP/PAR, modal operators, Galois connection
│   ├── Soundness.lean       -- Substitutability, progress, type preservation
│   ├── StructuralCongruence.lean
│   ├── CommRule.lean
│   ├── SpiceRule.lean
│   ├── PresentMoment.lean
│   └── Engine.lean         -- Executable rewrite engine (reduceStep, proven sound)
├── Formula.lean             -- Formula AST + bounded model checker (proven sound)
├── PiCalculus/              -- π-calculus and ρ-encoding
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

The concrete layer is fully proven (0 sorries). The abstract framework
(`rhoOSLF`) instantiates the general OSLF construction for ρ-calculus,
lifting the proven Galois connection.

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
  rewriteWithContext
  fullRewriteToNormalForm
)

export Mettapedia.OSLF.MeTTaIL.DeclReduces (
  DeclReduces
  engine_sound
  engine_complete
  declReduces_iff_langReduces
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
export Mettapedia.OSLF.RhoCalculus (
  ProcObj
  NameObj
  NamePred
  ProcPred
  BarbedParams
  BarbedRelation
  ProcEquiv
)

export Mettapedia.OSLF.RhoCalculus.Soundness (
  NativeType
  TypingContext
  HasType
  substitutability
  comm_preserves_type
)

export Mettapedia.OSLF.RhoCalculus.Reduction (
  Reduces
  possiblyProp
  relyProp
  galois_connection
)

-- Re-export Engine module
export Mettapedia.OSLF.RhoCalculus.Engine (
  reduceStep
  reduceToNormalForm
  reduceAll
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
  langReduces
  langRewriteSystem
  langSpan
  langDiamond
  langBox
  langGalois
  langOSLF
  langNativeType
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
  SortCategory
  predFibration
  oslf_fibration
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

export Mettapedia.OSLF.Framework.BeckChevalleyOSLF (
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
  sem_dia_eq_langDiamond
  sem_box_eq_langBox
  formula_galois
  CheckResult
  check
  check_sat_sound
  aggregateBox
  aggregateBox_sat
  checkWithPred
  checkWithPred_sat_sound
  rhoAtoms
  rhoAtomSem
  rhoAtoms_sound
)

end Mettapedia.OSLF
