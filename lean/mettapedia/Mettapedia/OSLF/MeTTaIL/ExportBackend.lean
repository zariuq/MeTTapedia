import Mettapedia.OSLF.MeTTaIL.PremiseDatalog
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Export
import Mettapedia.Languages.MeTTa.OSLFCore.FullPremises
import Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef

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

/-- Local list flatMap helper (keeps compatibility across Lean versions). -/
private def listFlatMap {α β : Type} (xs : List α) (f : α → List β) : List β :=
  xs.foldr (fun x acc => f x ++ acc) []

private def ctorCategoryFor (lang : LanguageDef) (ctorName : String) : Option String :=
  (lang.terms.find? (fun t => t.label == ctorName)).map (·.category)

private def lookupVarSubst (subst : List (String × PExpr)) (name : String) : Option PExpr :=
  (subst.find? (fun (n, _) => n == name)).map (·.2)

private partial def substExpr (subst : List (String × PExpr)) : PExpr → PExpr
  | .var n =>
      match lookupVarSubst subst n with
      | some e => e
      | none => .var n
  | .ctor c args => .ctor c (args.map (substExpr subst))
  | .literal p => .literal p
  | .call fn args => .call fn (args.map (substExpr subst))
  | .wild => .wild

private inductive WitnessCall where
  | one (fnName : String) (args : List PExpr)
  | many (fnName : String) (args : List PExpr)

private def computeWitnessEmptyGuard? (prog : PremiseProgram) (rel : String)
    (negArgs : List PExpr) : Option WitnessCall := do
  -- Expected witness shape:
  --   hasRel(head...) :- relQuery rawRel(head..., _)
  let witnessRules := prog.rulesFor rel
  let witnessRule ← witnessRules.head?
  guard (witnessRules.tail.isEmpty)
  let .relQuery rawRel _rawArgs ← witnessRule.body.head?
    | none
  guard (witnessRule.body.tail.isEmpty)
  guard (witnessRule.headArgs.length == negArgs.length)
  -- Bind witness head vars to the concrete negation args.
  let subst : List (String × PExpr) :=
    (witnessRule.headArgs.zip negArgs).filterMap fun
      | (.var n, arg) => some (n, arg)
      | _ => none
  -- Raw relation shape:
  --   rawRel(..., result) :- compute(fn, computeArgs, result)
  -- or
  --   rawRel(..., result) :- computeMany(fn, computeArgs, result)
  let rawRules := prog.rulesFor rawRel
  let rawRule ← rawRules.head?
  guard (rawRules.tail.isEmpty)
  let rawHead ← rawRule.body.head?
  guard (rawRule.body.tail.isEmpty)
  let loweredArgs := match rawHead with
    | .compute _ computeArgs _ => computeArgs.map (substExpr subst)
    | .computeMany _ computeArgs _ => computeArgs.map (substExpr subst)
    | _ => []
  match rawHead with
  | .compute fnName _ _ =>
      some (.one fnName loweredArgs)
  | .computeMany fnName _ _ =>
      some (.many fnName loweredArgs)
  | _ =>
      none

/-! ## 1. Ascent Expression Rendering -/

/-- Render a PExpr as an Ascent expression (Rust code). -/
partial def renderAscentExpr (lang : LanguageDef) (atomTy : String := "Atom") : PExpr → String
  | .var name => name
  | .ctor ctorName args =>
      let ctorTy := (ctorCategoryFor lang ctorName).getD atomTy
      let argStrs := args.map (renderAscentExpr lang atomTy)
      if argStrs.isEmpty then
        s!"{ctorTy}::C_{ctorName}"
      else
        s!"{ctorTy}::C_{ctorName}({", ".intercalate argStrs})"
  | .literal pat => renderAscentPattern lang atomTy pat
  | .call fnName args =>
      let argStrs := args.map (renderAscentExpr lang atomTy)
      s!"{fnName}({", ".intercalate argStrs})"
  | .wild => "_"
where
  renderAscentPattern (lang : LanguageDef) (atomTy : String) : Pattern → String
    | .apply name [] =>
        let ctorTy := (ctorCategoryFor lang name).getD atomTy
        s!"{ctorTy}::C_{name}"
    | .apply name args =>
        let ctorTy := (ctorCategoryFor lang name).getD atomTy
        let argStrs := args.map (renderAscentPattern lang atomTy)
        s!"{ctorTy}::C_{name}({", ".intercalate argStrs})"
    | .fvar x => x
    | .bvar n => s!"_b{n}"
    | _ => "/* unsupported pattern */"

/-! ## 2. Ascent Guard Rendering -/

def renderAscentGuard (lang : LanguageDef) (prog : PremiseProgram)
    (atomTy : String := "Atom")
    : PGuard → List String
  | .eq lhs rhs =>
      [s!"if {renderAscentExpr lang atomTy lhs} == {renderAscentExpr lang atomTy rhs}"]
  | .neq lhs rhs =>
      [s!"if {renderAscentExpr lang atomTy lhs} != {renderAscentExpr lang atomTy rhs}"]
  | .deconstruct expr ctorName fieldNames =>
      let exprStr := renderAscentExpr lang atomTy expr
      let ctorTy := (ctorCategoryFor lang ctorName).getD atomTy
      let fields := fieldNames.map fun n =>
        if n == "_" || n.startsWith "_" then "_" else s!"ref {n}0"
      let bindings := fieldNames.filterMap fun n =>
        if n == "_" || n.startsWith "_" then none
        else some s!"let {n} = (**{n}0).clone()"
      [s!"if let {ctorTy}::C_{ctorName}({", ".intercalate fields}) = {exprStr}"]
        ++ bindings
  | .compute fnName args result =>
      let hint := prog.hintFor fnName "ascent"
      match hint with
      | some template =>
          let argStrs := args.map (renderAscentExpr lang atomTy)
          let filled := (zipWithIdx argStrs).foldl (fun s (i, a) =>
            s.replace s!"\{{i}}" a) template
          [s!"if let Some({result}) = {filled}"]
      | none =>
          let argStrs := args.map (renderAscentExpr lang atomTy)
          [s!"if let Some({result}) = {fnName}({", ".intercalate argStrs})"]
  | .computeMany fnName args result =>
      let hint := prog.hintFor fnName "ascent"
      match hint with
      | some template =>
          let argStrs := args.map (renderAscentExpr lang atomTy)
          let filled := (zipWithIdx argStrs).foldl (fun s (i, a) =>
            s.replace s!"\{{i}}" a) template
          [s!"for {result} in {filled}.into_iter()"]
      | none =>
          let argStrs := args.map (renderAscentExpr lang atomTy)
          [s!"for {result} in {fnName}({", ".intercalate argStrs}).into_iter()"]
  | .notIn rel args =>
      match computeWitnessEmptyGuard? prog rel args with
      | some call =>
          let loweredArgs := match call with
            | .one _ loweredArgs => loweredArgs
            | .many _ loweredArgs => loweredArgs
          let fnName := match call with
            | .one fnName _ => fnName
            | .many fnName _ => fnName
          let hint := prog.hintFor fnName "ascent"
          let argStrs := loweredArgs.map (renderAscentExpr lang atomTy)
          let filled := match hint with
            | some template =>
                (zipWithIdx argStrs).foldl (fun (s : String) (ia : Nat × String) =>
                  let (i, a) := ia
                  String.replace s s!"\{{i}}" a) template
            | none =>
                s!"{fnName}({", ".intercalate argStrs})"
          match call with
          | .many _ _ =>
              [s!"if {filled}.into_iter().next().is_none()"]
          | .one _ _ =>
              [s!"if {filled}.is_none()"]
      | none =>
          let argStrs := args.map (renderAscentExpr lang atomTy)
          [s!"!{rel}({", ".intercalate argStrs})"]
  | .relQuery rel args =>
      let argStrs := args.map (renderAscentExpr lang atomTy)
      [s!"{rel}({", ".intercalate argStrs})"]
  | .collIter _expr _ct _elem =>
      ["/* collIter: not yet supported in Ascent backend */"]
  | .trueGuard => []

/-! ## 3. Ascent Rule Rendering -/

private partial def varsInExpr : PExpr → List String
  | .var n => [n]
  | .ctor _ args | .call _ args => listFlatMap args varsInExpr
  | .literal pat => varsInPattern pat
  | .wild => []
where
  varsInPattern : Pattern → List String
    | .apply _ args => listFlatMap args varsInPattern
    | .fvar x => [x]
    | _ => []

private def varsUsedInGuard : PGuard → List String
  | .eq l r | .neq l r => varsInExpr l ++ varsInExpr r
  | .deconstruct e _ _ => varsInExpr e
  | .compute _ args _ | .computeMany _ args _ =>
      listFlatMap args varsInExpr
  | .notIn _ args =>
      listFlatMap args varsInExpr
  | .relQuery _ _ =>
      []
  | .collIter e _ _ => varsInExpr e
  | .trueGuard => []

private def varsIntroducedByGuard : PGuard → List String
  | .deconstruct _ _ fields =>
      fields.filter (fun n => n != "_" && !n.startsWith "_")
  | .relQuery _ args =>
      (listFlatMap args varsInExpr).filter (fun n => n != "_" && !n.startsWith "_")
  | .compute _ _ result | .computeMany _ _ result =>
      [result]
  | .collIter _ _ elem =>
      [elem]
  | _ => []

private def headVarTypes (prog : PremiseProgram) (rule : PRule) : List (String × String) :=
  let declTy : List String :=
    match prog.relations.find? (fun d => d.name == rule.headRel) with
    | some d => d.paramTypes
    | none => []
  (rule.headArgs.zip declTy).filterMap fun (arg, ty) =>
    match arg with
    | .var n => some (n, ty)
    | _ => none

private def atomOrSpaceBinder (varTyMap : List (String × String)) (v : String) : String :=
  let ty? := (varTyMap.find? (fun (n, _) => n == v)).map (·.2)
  match ty? with
  | some "Space" => s!"space({v})"
  | some _ => s!"atom({v})"
  | none =>
      if v.startsWith "sp" then s!"space({v})" else s!"atom({v})"

def renderAscentRule (lang : LanguageDef) (prog : PremiseProgram) (rule : PRule)
    (atomTy : String := "Atom") : String :=
  let headArgs := rule.headArgs.map (renderAscentExpr lang atomTy)
  let head := s!"{rule.headRel}({", ".intercalate headArgs})"
  let headVars := listFlatMap rule.headArgs varsInExpr
  let isValidVar := fun (v : String) => v != "_" && !v.startsWith "_"
  let step := fun (acc : List String × List String) (g : PGuard) =>
    let introduced := acc.1
    let needed := acc.2
    let usedNow := (varsUsedInGuard g).filter (fun v => isValidVar v && !(List.contains introduced v))
    let introducedNow := (varsIntroducedByGuard g).filter isValidVar
    let introduced' := List.eraseDups (introduced ++ introducedNow)
    (introduced', needed ++ usedNow)
  let (introducedByBody, neededByBody) := rule.body.foldl step ([], [])
  let headNeeds := headVars.filter (fun v => isValidVar v && !(List.contains introducedByBody v))
  let needsBind := List.eraseDups (neededByBody ++ headNeeds)
  let varTyMap := headVarTypes prog rule
  let binders := List.map (atomOrSpaceBinder varTyMap ·) needsBind
  let bodyParts := binders ++ (rule.body.flatMap (renderAscentGuard lang prog atomTy))
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
    let params := decl.paramTypes.map fun ty =>
      if ty.isEmpty then atomTy else ty
    s!"relation {decl.name}({", ".intercalate params});"
  "\n        ".intercalate decls

def renderAscentPremiseRules (lang : LanguageDef) (prog : PremiseProgram)
    (atomTy : String := "Atom") : String :=
  let relDecls := renderAscentRelDecls prog atomTy
  let rules := prog.rules.map (renderAscentRule lang prog · atomTy)
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
  match LanguageDef.typeNames lang with
  | stateType :: _ => lang.terms.find? (·.category == stateType)
  | _ => none

/-- Find all instruction-category constructors. -/
private def findInstrRules (lang : LanguageDef) : List GrammarRule :=
  match LanguageDef.typeNames lang with
  | _ :: instrType :: _ => lang.terms.filter (·.category == instrType)
  | _ => []

/-- Type names for state, instr, atom from lang.types. -/
private def langTypeNames (lang : LanguageDef) : String × String × String :=
  match LanguageDef.typeNames lang with
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
    let entries := queries.filterMap fun (rel, arity, instrLabel) =>
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
                      let cat := match sr.params[i]? with
                        | some p => paramCategory p
                        | none => ""
                      if cat == "Space" then "ref sp0" else "_"
                  let statePatStr := ", ".intercalate statePattern
                  let instrParams := rule.params
                  let instrTotal := instrParams.length
                  let instrFields := (List.range instrTotal).map fun i => s!"ref arg{i}0"
                  let instrPatStr := ", ".intercalate instrFields
                  let bindings := (List.range instrTotal).map fun i => s!"let arg{i} = (**arg{i}0).clone()"
                  -- Build the query tuple: space + instruction args (up to relation arity)
                  let spBinding := "let sp = (**sp0).clone()"
                  let allBindings := [spBinding] ++ bindings
                  let queryArgs := if arity > instrTotal + 1
                    then ["sp"] ++ (List.range instrTotal).map (s!"arg{·}")
                    else ["sp"] ++ (List.range (min (arity - 1) instrTotal)).map (s!"arg{·}")
                  let qArity := queryArgs.length
                  let queryRelName := s!"{rel}Query{qArity}"
                  let declTys := if qArity == 0 then []
                    else ["Space"] ++ List.replicate (qArity - 1) "Atom"
                  let decl := s!"relation {queryRelName}({", ".intercalate declTys});"
                  let queryHead := s!"{queryRelName}({", ".intercalate queryArgs})"
                  let bodyLines := [
                    "state(st)",
                    s!"if let {stateType}::C_{sr.label}({statePatStr}) = st",
                    s!"if let {instrType}::C_{instrLabel}({instrPatStr}) = &**instr"
                  ] ++ allBindings
                  let bodyStr := ",\n            ".intercalate bodyLines
                  let ruleLine := s!"{queryHead} <--\n            {bodyStr};"
                  some (decl, ruleLine)
    if entries.isEmpty then ""
    else
      let header := "\n\n        // ═══ Query scoping (auto-generated from rewrite premises) ═══\n"
      let declLines := (entries.map (·.1)).eraseDups
      let ruleLines := entries.map (·.2)
      let declBlock := "        " ++ "\n        ".intercalate declLines
      let ruleBlock := "        " ++ "\n\n        ".intercalate ruleLines
      header ++ declBlock ++ "\n\n" ++ ruleBlock

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
  let premises := renderAscentPremiseRules lang prog
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
        (base.dropEnd 1).toString ++ "\n" ++ logicSection ++ "\n}"
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
    Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef.mettaFull
    Mettapedia.Languages.MeTTa.OSLFCore.FullPremises.mettaFullPremises
  IO.println s!"=== Premise rules ({output.length} chars) ==="

-- Render domain extraction for mettaFull
#eval! do
  let output := renderDomainExtraction
    Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef.mettaFull
  IO.println output

-- Render query scoping for mettaFull
#eval! do
  let output := renderQueryScoping
    Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef.mettaFull
  IO.println output

end Mettapedia.OSLF.MeTTaIL.ExportBackend
