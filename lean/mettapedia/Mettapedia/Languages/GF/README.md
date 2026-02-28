# GF Lean formalization

This project formalizes Grammatical Framework in Lean 4.
It includes an abstract syntax.
It includes two concrete grammars for Czech and English.
It includes a semantic bridge.

## Authorship

- The primary author is Oruzi (AI).
- The human lead editor is Zar.

## Scope

This formalization covers a strict subset.
This formalization doesn't port the full RGL.

- The abstract syntax includes 170 core GF RGL function signatures.
- The Czech concrete grammar includes an engine.
- The Czech linearization is partial.
- The English concrete grammar includes morphology and clause construction.
- The English syntactic coverage is broader than Czech.
- The semantic bridge targets OSLF evidence semantics.

- This profile doesn't include the PGF runtime.
- This profile doesn't include PMCFG parsing.
- This profile doesn't include chart parsing.
- This profile doesn't include full conjunction linearization.
- This profile doesn't include full English numeral linearization.

## Proof status

The codebase doesn't contain sorries.
The codebase doesn't contain axioms.
Every theorem is proven.

## Architecture

```
Core.lean            GF categories (112), AbstractTree, ConcreteForm, Grammar
Abstract.lean        Core RGL function signatures and abstract nodes
Concrete.lean        Inflection tables and morphophonological operations
Typing.lean          GF-to-OSLF type checking and compositionality
OSLFBridge.lean      GF abstract syntax as OSLF LanguageDef
WorldModelSem.lean   Evidence-valued denotational semantics for GF trees
English/             English morphology and clause construction
Czech/               Czech morphology engine
Examples/            End-to-end pipeline examples
```

### Typed-symbol patterns

- Tree to pattern bridge: `GF_tree -> Pattern`
- Pattern to formula bridge: `Pattern -> QFormula`
- Pipeline composition: `GF_tree -> Pattern -> Store -> QFormula -> Evidence`

## Key results

- Kernel confluence is proven.
- Cross-linguistic invariance is proven.
- Roundtrip regression shows zero failures across 36 corpus entries.
- Worked examples prove the end-to-end pipeline.

## References

- Aarne Ranta 2004 is the core GF reference.
- Meredith and Stay are a core OSLF reference.
- The GF RGL source is https://github.com/GrammaticalFramework/gf-rgl.
