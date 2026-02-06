import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Semantics
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.OSLF.RhoCalculus.Types
import Mettapedia.OSLF.RhoCalculus.Soundness
import Mettapedia.OSLF.RhoCalculus.Reduction
import Mettapedia.OSLF.PiCalculus.Main
import Mettapedia.OSLF.Framework.RewriteSystem
import Mettapedia.OSLF.Framework.RhoInstance
import Mettapedia.OSLF.Framework.CategoryBridge

/-!
# Operational Semantics in Logical Form (OSLF)

Re-exports for the OSLF formalization, connecting MeTTaIL language definitions
to categorical semantics via the OSLF algorithm.

## Module Structure

```
OSLF/
├── Main.lean                -- This file (re-exports)
├── Framework/
│   ├── RewriteSystem.lean   -- Abstract OSLF: RewriteSystem -> OSLFTypeSystem
│   ├── RhoInstance.lean     -- ρ-calculus instance (proven Galois connection)
│   └── CategoryBridge.lean  -- Bridge to GSLT categorical infrastructure
├── MeTTaIL/
│   ├── Syntax.lean          -- LanguageDef AST (types, terms, equations, rewrites)
│   ├── Semantics.lean       -- InterpObj, pattern interpretation
│   └── Substitution.lean    -- Capture-avoiding substitution
├── RhoCalculus/
│   ├── Types.lean           -- Namespaces, codespaces, bisimulation
│   ├── Reduction.lean       -- COMM/DROP/PAR, modal operators, Galois connection
│   ├── Soundness.lean       -- Substitutability, progress, type preservation
│   ├── StructuralCongruence.lean
│   ├── CommRule.lean
│   ├── SpiceRule.lean
│   └── PresentMoment.lean
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

end Mettapedia.OSLF
