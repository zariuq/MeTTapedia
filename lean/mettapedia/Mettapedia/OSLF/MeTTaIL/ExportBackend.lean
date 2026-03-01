import Mettapedia.OSLF.MeTTaIL.PremiseDatalog
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Export
import Mettapedia.OSLF.MeTTaCore.FullPremises
import Mettapedia.OSLF.MeTTaCore.FullLanguageDef

/-!
# Backend Renderers for PremiseProgram

Compile a `PremiseProgram` (backend-agnostic datalog IR) into backend-specific
code. Currently supports Ascent (Rust datalog macro); MORK/ZAM planned.

## Full Pipeline

```
renderLanguageFull(lang, premises) =
  language! {
    name: ...
    types { ... }           -- from renderLanguage (Export.lean)
    terms { ... }           -- from renderLanguage
    equations { ... }       -- from renderLanguage
    rewrites { ... }        -- from renderLanguage
    logic {
      // Domain extraction  -- auto from lang.terms
      // Query scoping      -- auto from lang.rewrites premises
      // Premise rules      -- from PremiseProgram IR
    }
  }
```
-/

namespace Mettapedia.OSLF.MeTTaIL.ExportBackend

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PremiseDatalog
open Mettapedia.OSLF.MeTTaIL.Export (renderLanguage)

/-- Zip a list with 0-based indices. -/
private def zipWithIdx {α : Type} (xs : List α) : List (Nat × α) :=
  (List.range xs.length).zipWith (fun a b => (a, b)) xs

/-! ## 1. Ascent Expression Rendering -/

/-- Render a PExpr as an Ascent expression (Rust code). -/
partial def renderAscentExpr (atomTy : String := "Atom") : PExpr → String
  | .var name => name
  | .ctor ctorName args =>
      let argStrs := args.map (renderAscentExpr atomTy)
      s!"{atomTy}::C_{ctorName}({", ".intercalate argStrs})"
  | .literal pat => renderAscentPattern atomTy pat
  | .call fnName args =>
      let argStrs := args.map (renderAscentExpr atomTy)
      s!"{fnName}({", ".intercalate argStrs})"
  | .wild => "_"
where
  renderAscentPattern (atomTy : String) : Pattern → String
    | .apply name [] => s!"{atomTy}::C_{name}"
    | .apply name args =>
        let argStrs := args.map (renderAscentPattern atomTy)
        s!"{atomTy}::C_{name}({", ".intercalate argStrs})"
    | .fvar x => x
    | .bvar n => s!"_b{n}"
    | _ => "/* unsupported pattern */"

/-! ## 2. Ascent Guard Rendering -/

def renderAscentGuard (prog : PremiseProgram) (atomTy : String := "Atom")
    : PGuard → List String
  | .eq lhs rhs =>
      [s!"if {renderAscentExpr atomTy lhs} == {renderAscentExpr atomTy rhs}"]
  | .neq lhs rhs =>
      [s!"if {renderAscentExpr atomTy lhs} != {renderAscentExpr atomTy rhs}"]
  | .deconstruct expr ctorName fieldNames =>
      let exprStr := renderAscentExpr atomTy expr
      let fields := fieldNames.map fun n =>
        if n == "_" || n.startsWith "_" then "_" else s!"ref {n}0"
      let bindings := fieldNames.filterMap fun n =>
        if n == "_" || n.startsWith "_" then none
        else some s!"let {n} = (**{n}0).clone()"
      [s!"if let {atomTy}::C_{ctorName}({", ".intercalate fields}) = {exprStr}"]
        ++ bindings
  | .compute fnName args result =>
      let hint := prog.hintFor fnName "ascent"
      match hint with
      | some template =>
          let argStrs := args.map (renderAscentExpr atomTy)
          let filled := (zipWithIdx argStrs).foldl (fun s (i, a) =>
            s.replace s!"\{{i}}" a) template
          [s!"if let Some({result}) = {filled}"]
      | none =>
          let argStrs := args.map (renderAscentExpr atomTy)
          [s!"if let Some({result}) = {fnName}({", ".intercalate argStrs})"]
  | .notIn rel args =>
      let argStrs := args.map (renderAscentExpr atomTy)
      [s!"!{rel}({", ".intercalate argStrs})"]
  | .relQuery rel args =>
      let argStrs := args.map (renderAscentExpr atomTy)
      [s!"{rel}({", ".intercalate argStrs})"]
  | .collIter _expr _ct _elem =>
      ["/* collIter: not yet supported in Ascent backend */"]
  | .trueGuard => []

/-! ## 3. Ascent Rule Rendering -/

def renderAscentRule (prog : PremiseProgram) (rule : PRule)
    (atomTy : String := "Atom") : String :=
  let headArgs := rule.headArgs.map (renderAscentExpr atomTy)
  let head := s!"{rule.headRel}({", ".intercalate headArgs})"
  let bodyParts := rule.body.flatMap (renderAscentGuard prog atomTy)
  let comment := match rule.clauseName with
    | some name => s!"// {name}\n        "
    | none => ""
  if bodyParts.isEmpty then
    s!"{comment}{head};"
  else
    let bodyStr := ",\n            ".intercalate bodyParts
    s!"{comment}{head} <--\n            {bodyStr};"

def renderAscentRelDecls (prog : PremiseProgram)
    (atomTy : String := "Atom") : String :=
  let decls := prog.relations.map fun decl =>
    let params := decl.paramTypes.map fun _ => atomTy
    s!"relation {decl.name}({", ".intercalate params});"
  "\n        ".intercalate decls

def renderAscentPremiseRules (prog : PremiseProgram)
    (atomTy : String := "Atom") : String :=
  let relDecls := renderAscentRelDecls prog atomTy
  let rules := prog.rules.map (renderAscentRule prog · atomTy)
  let rulesStr := "\n\n        ".intercalate rules
  s!"        // ═══ Premise relation declarations ═══
        {relDecls}

        // ═══ Premise rules (generated from PremiseProgram IR) ═══
        {rulesStr}"

/-! ## 4. Domain Extraction (Auto-derived from LanguageDef)

For each field of the state constructor → extract into domain relation.
For each instruction variant → extract each Atom-typed field.

These seed the Ascent relations so premise rules can bind values. -/

/-- Get the category type of a TermParam. -/
private def paramCategory : TermParam → String
  | .simple _ ty | .abstraction _ ty | .multiAbstraction _ ty =>
      match ty with | .base c => c | _ => ""

/-- Find the state constructor (category == first type in lang.types). -/
private def findStateRule (lang : LanguageDef) : Option GrammarRule :=
  match lang.types with
  | stateType :: _ => lang.terms.find? (·.category == stateType)
  | _ => none

/-- Find all instruction-category constructors. -/
private def findInstrRules (lang : LanguageDef) : List GrammarRule :=
  match lang.types with
  | _ :: instrType :: _ => lang.terms.filter (·.category == instrType)
  | _ => []

/-- Type names for state, instr, atom from lang.types. -/
private def langTypeNames (lang : LanguageDef) : String × String × String :=
  match lang.types with
  | st :: instr :: atom :: _ => (st, instr, atom)
  | st :: instr :: _ => (st, instr, "Atom")
  | st :: _ => (st, "Instr", "Atom")
  | _ => ("State", "Instr", "Atom")

/-- Generate domain extraction rules for the state constructor fields. -/
private def renderStateDomainRules (lang : LanguageDef) : List String :=
  let (stateType, instrType, _atomType) := langTypeNames lang
  match findStateRule lang with
  | none => []
  | some stateRule =>
      let total := stateRule.params.length
      (zipWithIdx stateRule.params).filterMap fun (idx, param) =>
        let cat := paramCategory param
        -- For the Instr field, we don't extract it as atom; it's used via nested matching
        if cat == instrType || cat == _atomType then
          let pattern := (List.range total).map fun i =>
            if i == idx then "ref f0" else "_"
          let patStr := ", ".intercalate pattern
          if cat == _atomType then
            some s!"atom(a) <--
            state(st),
            if let {stateType}::C_{stateRule.label}({patStr}) = st,
            let a = (**f0).clone();"
          else none
        else none

/-- Generate domain extraction rules for Space field of state (if present). -/
private def renderSpaceDomainRule (lang : LanguageDef) : List String :=
  let (stateType, _, _) := langTypeNames lang
  match findStateRule lang with
  | none => []
  | some stateRule =>
      let total := stateRule.params.length
      (zipWithIdx stateRule.params).filterMap fun (idx, param) =>
        let cat := paramCategory param
        if cat == "Space" then
          let pattern := (List.range total).map fun i =>
            if i == idx then "ref f0" else "_"
          let patStr := ", ".intercalate pattern
          some s!"space(sp) <--
            state(st),
            if let {stateType}::C_{stateRule.label}({patStr}) = st,
            let sp = (**f0).clone();"
        else none

/-- Generate domain extraction rules for each Atom-typed field of each Instr variant. -/
private def renderInstrAtomDomainRules (lang : LanguageDef) : List String :=
  let (stateType, instrType, atomType) := langTypeNames lang
  let instrRules := findInstrRules lang
  -- Find which state field is the Instr (for the nested match pattern)
  match findStateRule lang with
  | none => []
  | some stateRule =>
      let stateTotal := stateRule.params.length
      let instrIdx := (zipWithIdx stateRule.params).find?
        (fun (_, p) => paramCategory p == instrType)
      match instrIdx with
      | none => []
      | some (iIdx, _) =>
          let statePattern := (List.range stateTotal).map fun i =>
            if i == iIdx then "ref instr" else "_"
          let statePatStr := ", ".intercalate statePattern
          instrRules.flatMap fun rule =>
            let params := rule.params
            let total := params.length
            (zipWithIdx params).filterMap fun (idx, param) =>
              let cat := paramCategory param
              if cat == atomType then
                let pattern := (List.range total).map fun i =>
                  if i == idx then "ref f0" else "_"
                let patStr := ", ".intercalate pattern
                some s!"atom(a) <--
            state(st),
            if let {stateType}::C_{stateRule.label}({statePatStr}) = st,
            if let {instrType}::C_{rule.label}({patStr}) = &**instr,
            let a = (**f0).clone();"
              else none

/-- Render complete domain extraction section. -/
def renderDomainExtraction (lang : LanguageDef) : String :=
  let spaceRules := renderSpaceDomainRule lang
  let stateAtomRules := renderStateDomainRules lang
  let instrRules := renderInstrAtomDomainRules lang
  let allRules := spaceRules ++ stateAtomRules ++ instrRules
  if allRules.isEmpty then ""
  else
    let header := "        // ═══ Domain extraction (auto-generated from LanguageDef.terms) ═══\n"
    let decls := "        relation space(Space);\n        relation atom(Atom);\n\n"
    header ++ decls ++ "        " ++ "\n\n        ".intercalate allRules

/-! ## 5. Query Scoping (Auto-derived from RewriteRule premises)

For each relation R referenced in any rewrite rule's premises, we generate
a query-scoping rule that restricts R to the actual arguments from the
instruction that triggers it. This prevents materialization explosion. -/

/-- Collect all (relation, arity, triggering-instruction-patterns) from rewrites. -/
private def collectPremiseQueries (lang : LanguageDef) :
    List (String × Nat × String) :=
  lang.rewrites.flatMap fun rw =>
    rw.premises.filterMap fun
      | .relationQuery rel args =>
          -- Find which instruction pattern this rewrite matches
          match rw.left with
          | .apply "State" (.apply instrLabel _ :: _) =>
              some (rel, args.length, instrLabel)
          | _ => some (rel, args.length, "unknown")
      | _ => none

/-- Generate query-scoping relation declarations and rules.
    For each unique (relation, instruction) pair, generates a scoping rule
    that extracts the query arguments from the matching instruction. -/
def renderQueryScoping (lang : LanguageDef) : String :=
  let queries := collectPremiseQueries lang
  if queries.isEmpty then ""
  else
    let (stateType, instrType, _) := langTypeNames lang
    -- Group by relation name
    let relNames := (queries.map (·.1)).eraseDups
    let lines := relNames.flatMap fun rel =>
      let relQueries := queries.filter (·.1 == rel)
      -- Generate a query relation: relQuery(args...) <-- state(st), if let Instr::C_X(fields..) = instr
      let queryRelName := s!"{rel}Query"
      relQueries.filterMap fun (_, arity, instrLabel) =>
        -- Find the instruction rule to get its parameter structure
        let instrRule := lang.terms.find? (·.label == instrLabel)
        match instrRule with
        | none => none
        | some rule =>
            let stateRule := findStateRule lang
            match stateRule with
            | none => none
            | some sr =>
                let stateTotal := sr.params.length
                let instrIdx := (zipWithIdx sr.params).find?
                  (fun (_, p) => paramCategory p == instrType)
                match instrIdx with
                | none => none
                | some (iIdx, _) =>
                    let statePattern := (List.range stateTotal).map fun i =>
                      if i == iIdx then "ref instr" else
                        -- Also extract space if the relation needs it
                        let cat := match sr.params[i]? with
                  | some p => paramCategory p
                  | none => ""
                        if cat == "Space" then "ref sp0" else "_"
                    let statePatStr := ", ".intercalate statePattern
                    let instrParams := rule.params
                    let instrTotal := instrParams.length
                    let instrFields := (List.range instrTotal).map fun i =>
                      s!"ref arg{i}0"
                    let instrPatStr := ", ".intercalate instrFields
                    let bindings := (List.range instrTotal).map fun i =>
                      s!"let arg{i} = (**arg{i}0).clone()"
                    -- Build the query tuple: space + instruction args (up to arity)
                    let spBinding := "let sp = (**sp0).clone()"
                    let allBindings := [spBinding] ++ bindings
                    let queryArgs := if arity > instrTotal + 1
                      then ["sp"] ++ (List.range instrTotal).map (s!"arg{·}")
                      else ["sp"] ++ (List.range (min (arity - 1) instrTotal)).map (s!"arg{·}")
                    let queryHead := s!"{queryRelName}({", ".intercalate queryArgs})"
                    let bodyLines := [
                      "state(st)",
                      s!"if let {stateType}::C_{sr.label}({statePatStr}) = st",
                      s!"if let {instrType}::C_{instrLabel}({instrPatStr}) = &**instr"
                    ] ++ allBindings
                    let bodyStr := ",\n            ".intercalate bodyLines
                    some s!"{queryHead} <--\n            {bodyStr};"
    if lines.isEmpty then ""
    else
      let header := "\n\n        // ═══ Query scoping (auto-generated from rewrite premises) ═══\n"
      header ++ "        " ++ "\n\n        ".intercalate lines

/-! ## 6. Full Pipeline -/

inductive Backend where
  | ascent : Backend
  | mork : Backend
  | zam : Backend
deriving Repr, Inhabited

/-- Render the complete logic section for an Ascent-backed language. -/
def renderAscentLogicFull (lang : LanguageDef) (prog : PremiseProgram) : String :=
  let domain := renderDomainExtraction lang
  let scoping := renderQueryScoping lang
  let premises := renderAscentPremiseRules prog
  "    logic {\n" ++ domain ++ scoping ++ "\n\n" ++ premises ++ "\n    }"

/-- Render a complete `language! { ... }` block with logic section.

This is the top-level entry point for full language generation.
It takes the output of `renderLanguage` (types/terms/equations/rewrites)
and inserts the generated logic section before the closing `}`. -/
def renderLanguageFull (lang : LanguageDef) (prog : PremiseProgram)
    (backend : Backend := .ascent) : String :=
  match backend with
  | .ascent =>
      let base := renderLanguage lang
      -- Insert logic section before the final "}"
      let logicSection := renderAscentLogicFull lang prog
      -- Find and replace the trailing "}" with logic + "}"
      -- renderLanguage ends with "\n}"
      if base.endsWith "}" then
        base.dropRight 1 ++ "\n" ++ logicSection ++ "\n}"
      else
        base ++ "\n\n" ++ logicSection ++ "\n}"
  | .mork => "/* MORK backend not yet implemented */"
  | .zam => "/* ZAM backend not yet implemented */"

/-- Write the fully rendered language to a file. -/
def writeLanguageFull (path : System.FilePath)
    (lang : LanguageDef) (prog : PremiseProgram)
    (backend : Backend := .ascent) : IO Unit := do
  IO.FS.writeFile path (renderLanguageFull lang prog backend ++ "\n")

/-! ## Smoke Checks -/

-- Render just the premise rules for mettaFullPremises
#eval! do
  let output := renderAscentPremiseRules
    Mettapedia.OSLF.MeTTaCore.FullPremises.mettaFullPremises
  IO.println s!"=== Premise rules ({output.length} chars) ==="

-- Render domain extraction for mettaFull
#eval! do
  let output := renderDomainExtraction
    Mettapedia.OSLF.MeTTaCore.FullLanguageDef.mettaFull
  IO.println output

-- Render query scoping for mettaFull
#eval! do
  let output := renderQueryScoping
    Mettapedia.OSLF.MeTTaCore.FullLanguageDef.mettaFull
  IO.println output

end Mettapedia.OSLF.MeTTaIL.ExportBackend
