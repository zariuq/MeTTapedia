import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Semantics
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.OSLF.RhoCalculus.Types
import Mettapedia.OSLF.RhoCalculus.Soundness
import Mettapedia.OSLF.RhoCalculus.Reduction
import Mettapedia.OSLF.PiCalculus.Main

/-!
# Operational Semantics in Logical Form (OSLF)

Re-exports for the OSLF formalization, connecting MeTTaIL language definitions
to categorical semantics via λ-theories.

## Module Structure

```
OSLF/
├── Main.lean              -- This file (re-exports)
├── MeTTaIL/
│   ├── Syntax.lean        -- LanguageDef AST (types, terms, equations, rewrites)
│   ├── Semantics.lean     -- Interpretation into LambdaTheory
│   └── Substitution.lean  -- Capture-avoiding substitution
└── RhoCalculus/           -- (Future) ρ-calculus application
    ├── Syntax.lean        -- ρ-calculus LanguageDef
    └── Types.lean         -- Namespaces, codespaces, bisimulation
```

## Main Components

### MeTTaIL DSL (Phase 3)

- `LanguageDef`: Complete language definition structure
- `TypeExpr`: Type expressions (base, arrow, collection)
- `Pattern`: Pattern terms with collection support
- `GrammarRule`: Constructor definitions with syntax
- `Equation`: Bidirectional equality rules
- `RewriteRule`: Directional rewrite rules

### Categorical Semantics

- `InterpObj`: Objects of the interpreted λ-theory
- `interpLambdaTheory`: Convert LanguageDef to LambdaTheory
- `rhoCalcTheory`: The ρ-calculus as a λ-theory

### Substitution

- `SimpleTerm`: De Bruijn indexed terms
- `SubstEnv`: Environment-based substitution
- `applySubst`: Capture-avoiding substitution
- `commSubst`: COMM rule substitution for ρ-calculus

## References

- Williams & Stay, "Native Type Theory" (ACT 2021)
- Meredith & Stay, "Operational Semantics in Logical Form"
- `/home/zar/claude/hyperon/mettail-rust/` - Rust implementation
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
  interpLambdaTheory
  rhoCalcTheory
)

export Mettapedia.OSLF.MeTTaIL.Substitution (
  SimpleTerm
  SubstEnv
  applySubst
  freeVars
  isFresh
  commSubst
)

export Mettapedia.OSLF.RhoCalculus (
  RhoTheory
  ProcObj
  NameObj
  NamePred
  ProcPred
  BarbedParams
  BarbedRelation
  ProcEquiv
  possibly
  rely
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

end Mettapedia.OSLF
