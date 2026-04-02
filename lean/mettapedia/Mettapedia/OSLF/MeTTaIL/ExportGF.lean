import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# ExportGF — Render LanguageDef to GF Abstract Syntax

Generates a GF abstract syntax module (`.gf` file content) from a `LanguageDef`.
This closes the **Lean → GF** arrow in the bijective triangle:

```
GF (.gf)  ←renderGFAbstract─  Lean (LanguageDef)  ─renderLanguage→  Rust (language!)
    │                              ↑                                    ↑
    └─── GFCore.check ────────────┘                                    │
                                    └──── languageDef! macro ──────────┘
```

## Mapping

- `LanguageDef.types` → `cat S ;` declarations
- `LanguageDef.terms` → `fun PredVP : NP -> VP -> Cl ;` declarations
- `LanguageDef.equations` → `-- equation: UseNIdentity` comments (GF has no equations)
- `LanguageDef.rewrites` → `-- rewrite: UseNElim` comments (GF has no rewrites)

GF abstract syntax has categories (`cat`) and functions (`fun`). It does not have
equations or rewrites — those are semantic extensions provided by the OSLF layer.
The generated `.gf` file faithfully represents the structural (types + terms) content
and documents the semantic rules as comments.

## References

- GF Reference Manual: http://www.grammaticalframework.org/doc/gf-refman.html
-/

namespace Mettapedia.OSLF.MeTTaIL.ExportGF

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Render a TypeExpr as a GF type string.
    `base "NP"` → `"NP"`, `arrow A B` → `"A -> B"`. -/
def renderGFTypeExpr : TypeExpr → String
  | .base s => s
  | .arrow a b => renderGFTypeExpr a ++ " -> " ++ renderGFTypeExpr b
  | .collection _ t => "List" ++ renderGFTypeExpr t
  | .multiBinder t => renderGFTypeExpr t

/-- Render a GrammarRule as a GF `fun` declaration.
    `{ label := "PredVP", category := "Cl", params := [("np", base "NP"), ("vp", base "VP")] }`
    → `"  fun PredVP : NP -> VP -> Cl ;"` -/
def renderGFFunction (rule : GrammarRule) : String :=
  let paramTypes := rule.params.map fun p =>
    match p with
    | .simple _ t => renderGFTypeExpr t
    | .abstractionNamed _ _ t => renderGFTypeExpr t
    | .multiAbstractionNamed _ _ t => renderGFTypeExpr t
  let arrow := if paramTypes.isEmpty then rule.category
    else String.intercalate " -> " (paramTypes ++ [rule.category])
  s!"  fun {rule.label} : {arrow} ;"

/-- Render a full LanguageDef as a GF abstract syntax module.

    The output is a valid GF abstract syntax file that can be loaded
    by the GF compiler. Categories become `cat` declarations, terms
    become `fun` declarations. Equations and rewrites are documented
    as comments (GF has no operational semantics). -/
def renderGFAbstract (lang : LanguageDef) : String :=
  let header := s!"-- Generated from LanguageDef \"{lang.name}\"\n" ++
    s!"-- Types: {lang.types.length}, Terms: {lang.terms.length}\n" ++
    s!"-- Equations: {lang.equations.length}, Rewrites: {lang.rewrites.length}\n\n"
  let catLines := lang.types.map fun t => s!"  cat {t.name} ;"
  let funLines := lang.terms.map renderGFFunction
  let eqComments := lang.equations.map fun eq => s!"  -- equation: {eq.name}"
  let rwComments := lang.rewrites.map fun rw => s!"  -- rewrite: {rw.name}"
  header ++
  s!"abstract {lang.name} = \{\n\n" ++
  (if catLines.isEmpty then "" else
    "  -- Categories\n" ++ String.intercalate "\n" catLines ++ "\n\n") ++
  (if funLines.isEmpty then "" else
    "  -- Functions\n" ++ String.intercalate "\n" funLines ++ "\n\n") ++
  (if eqComments.isEmpty then "" else
    "  -- Semantic equations (OSLF extension, not native GF)\n" ++
    String.intercalate "\n" eqComments ++ "\n\n") ++
  (if rwComments.isEmpty then "" else
    "  -- Semantic rewrites (OSLF extension, not native GF)\n" ++
    String.intercalate "\n" rwComments ++ "\n\n") ++
  "}"

end Mettapedia.OSLF.MeTTaIL.ExportGF
