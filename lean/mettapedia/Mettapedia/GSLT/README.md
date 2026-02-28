# GSLT module

GSLT is Graph-Structured Lambda Theories in Mettapedia.
This README specifies the formal GSLT contract that OSLF consumes.

## Formal spec status

- The formal specification is the GSLT module family and OSLF MeTTaIL syntax modules.

- `Mettapedia/GSLT.lean`
- `Mettapedia/GSLT/Core/LambdaTheoryCategory.lean`
- `Mettapedia/GSLT/Core/ChangeOfBase.lean`
- `Mettapedia/GSLT/Topos/SubobjectClassifier.lean`
- `Mettapedia/GSLT/Topos/PredicateFibration.lean`

## Category-theoretic definition

- The core GSLT object is a lambda theory with equality and fibration structure.
- SubobjectFibration is a Sub fiber over each object with frame structure.
- LambdaTheoryWithEquality is a categorical object with cartesian closed structure, finite limits, and attached fibration.
- ChangeOfBase is pullback and quantifier images with adjunctions exists_f left f* left forall_f.
- Beck-Chevalley is substitution and quantification compatibility on pullback squares.
- LambdaTheoryWithFibration is the bundled core object consumed by later semantics.

## Grammar operational interface

- LanguageDef is the operational front-end for OSLF synthesis.
- TypeExpr, CollType, GrammarRule, and TermParam are the grammar layer.
- Pattern is the equation and rewrite pattern language with binders and collections.
- Premise is freshness, congruence, and relationQuery constraints.
- LanguageDef is name, types, terms, equations, rewrites, and congruence collection defaults.

## OSLF interface

- TypeSynthesis entry points are langRewriteSystem, langDiamond, langBox, langGalois, and langOSLF.
- The practical contract is LanguageDef plus optional RelationEnv maps to langOSLF.

- `langRewriteSystemUsing / langRewriteSystem`
- `langDiamondUsing / langDiamond`
- `langBoxUsing / langBox`
- `langGaloisUsing / langGalois`
- `langOSLF`

## New language workflow

- A new language spec requires sort declarations and a process sort designation.
- A new language spec requires constructor terms for syntax and state.
- A new language spec requires equations for structural equality and normalization.
- A new language spec requires small-step rewrite rules.
- A new language spec requires premise constraints where needed.
- RelationEnv is optional unless relationQuery premises are used.

```lean
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.MeTTaIL.Engine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.MeTTaIL.Engine

def myLang : LanguageDef := { ... }
def myRelEnv : RelationEnv := RelationEnv.empty

def myOSLF := langOSLF myLang "Proc"
def myDiamond := langDiamondUsing myRelEnv myLang
def myBox := langBoxUsing myRelEnv myLang
```

## Any language interface

- The interface is any language encoded as small-step rewrites over structured states.
- Functional languages are typically encoded by term-reduction rules.
- Imperative languages are typically encoded as rewrites over machine states.
- Concurrent languages are typically encoded as rewrites over process and message networks.

## Practical examples

- The codebase is TinyML, MeTTa, and premise-aware demos to copy.

- `Mettapedia/OSLF/Framework/TinyMLInstance.lean`
- `Mettapedia/OSLF/Framework/MeTTaMinimalInstance.lean`
- `Mettapedia/OSLF/Framework/MeTTaFullInstance.lean`
- `Mettapedia/OSLF/MeTTaIL/DeclReducesWithPremises.lean`
- `Mettapedia/OSLF/Tools/ExportTinyMLSmokeRoundTrip.lean`

## Relation to topos spec

- LanguageDef is the executable ingestion layer, while GSLT Topos modules provide categorical semantics.

## Native Type Theory connection

- The GSLT presheaf layer is the direct infrastructure for Native Type Theory formalization.
- PredicateFibration.lean is presheaf change-of-base, frame fibers, and Beck-Chevalley components used by NTT.
- NTTClaimTracker.lean is the authoritative strict claim tracker for counts and assumption-scoped items.
- Paper-parity status is tracked in NTTClaimTracker, PaperClaimTracker, and FULLStatus modules.

- `Mettapedia/OSLF/Framework/NTTClaimTracker.lean`
- `Mettapedia/OSLF/Framework/PaperClaimTracker.lean`
- `Mettapedia/OSLF/Framework/FULLStatus.lean`
