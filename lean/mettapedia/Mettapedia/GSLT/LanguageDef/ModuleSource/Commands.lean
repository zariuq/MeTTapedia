import Mettapedia.GSLT.LanguageDef.ModuleSource.Elaborate
import Mettapedia.GSLT.LanguageDef.ModuleSource.Printer
import Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

/-!
# `.module` text in Lean

The `.module` format is Lean syntax here, as in Adam Dingle's Natural Lean: its declarations are
scoped syntax categories, and a module written in a Lean file, or read from a `.module` file, elaborates
to `ModuleSource.Module` data and to its `LanguageDef`. Rows inside blocks are the rows of
`languageDef!`, written the same way.

- `Module X { … }` in a Lean file defines `X.module`, `X.library` and `X.language`;
- `#module import "…" as u Module X { … }` does the same for a module with imports;
- `#module_file "path/X.module"` reads a file, `import` lines included, and defines the same;
- `import "UnivAlg.module" as u` makes `u.T` name the theory `T` of the module `UnivAlg`, which
  must already be defined, in Lean or by `#module_file`.

The words of the format (`Module`, `Theory`, `Types`, …) are not reserved, so names such as
Mathlib's `Module` keep working in files that import this one.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.Commands

open Lean Elab Command Term Meta
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

declare_syntax_cat moduleSortRow
declare_syntax_cat moduleExport
declare_syntax_cat moduleReplacement
declare_syntax_cat moduleEquation
declare_syntax_cat moduleRewrite
declare_syntax_cat moduleBlock
declare_syntax_cat moduleExpr
declare_syntax_cat moduleParam
declare_syntax_cat moduleTheory
declare_syntax_cat moduleImport
declare_syntax_cat moduleEntry
declare_syntax_cat moduleFile
declare_syntax_cat moduleInductiveTerm
declare_syntax_cat moduleInductiveBinder
declare_syntax_cat moduleInductiveConstructor
declare_syntax_cat moduleInductiveFamily

scoped syntax:max ident : moduleInductiveTerm
scoped syntax:max "Type" : moduleInductiveTerm
scoped syntax:max "(" moduleInductiveTerm ")" : moduleInductiveTerm
scoped syntax:70 moduleInductiveTerm:70 moduleInductiveTerm:71 : moduleInductiveTerm
scoped syntax:30 moduleInductiveTerm:31 "->" moduleInductiveTerm:30 : moduleInductiveTerm
scoped syntax ident ":" moduleInductiveTerm : moduleInductiveBinder
scoped syntax ident "(" moduleInductiveBinder,* ")" ":" moduleInductiveTerm ";" : moduleInductiveConstructor
scoped syntax ident "parameters" "(" moduleInductiveBinder,* ")"
  "indices" "(" moduleInductiveBinder,* ")" ":" moduleInductiveTerm
  "{" moduleInductiveConstructor* "}" : moduleInductiveFamily
scoped syntax "Inductives" "{" moduleInductiveFamily* "}" : moduleBlock

scoped syntax ident ";" : moduleExport
scoped syntax ident "=>" ident ";" : moduleExport

scoped syntax ident "=>" langDefTermDecl : moduleReplacement

scoped syntax langDefPattern "==" langDefPattern ";" : moduleEquation
scoped syntax "if" sepBy1(langDefPremise, ",") "then" langDefPattern "==" langDefPattern ";" : moduleEquation

scoped syntax ident ":" langDefPattern "~>" langDefPattern ";" : moduleRewrite
scoped syntax ident ":" "if" sepBy1(langDefPremise, ",") "then" langDefPattern "~>" langDefPattern ";" : moduleRewrite
scoped syntax langDefRewriteDecl : moduleRewrite
scoped syntax langDefEquationDecl : moduleEquation

scoped syntax ident ";" : moduleSortRow
scoped syntax ident "=" ident ";" : moduleSortRow

scoped syntax "Types" "{" moduleSortRow* "}" : moduleBlock
scoped syntax "Exports" "{" moduleExport* "}" : moduleBlock
scoped syntax "Terms" "{" langDefTermDecl* "}" : moduleBlock
scoped syntax "Replacements" "{" moduleReplacement* "}" : moduleBlock
scoped syntax "Equations" "{" moduleEquation* "}" : moduleBlock
scoped syntax "Rewrites" "{" moduleRewrite* "}" : moduleBlock

scoped syntax:max ident : moduleExpr
scoped syntax:max ident "(" moduleExpr,* ")" : moduleExpr
scoped syntax:max "{" moduleExpr "}" : moduleExpr
scoped syntax:max "(" moduleExpr ")" : moduleExpr
scoped syntax:max moduleBlock+ : moduleExpr
scoped syntax:50 moduleExpr:50 moduleBlock+ : moduleExpr
scoped syntax:10 moduleExpr:10 " \\/ " moduleExpr:11 : moduleExpr
scoped syntax:0 "let" ident "=" moduleExpr "in" moduleExpr : moduleExpr

scoped syntax ident ":" ident : moduleParam
scoped syntax "Theory" ident "(" moduleParam,* ")" "{" moduleExpr "}" : moduleTheory
scoped syntax "import" str "as" ident : moduleImport
scoped syntax "theory" ident "(" moduleExpr,* ")" : moduleEntry
scoped syntax moduleImport* "Module" ident "{" moduleTheory* (moduleEntry)? "}" : moduleFile

/-! ## From syntax to data -/

private def str (text : String) : Term := ⟨Syntax.mkStrLit text⟩

private def pathOf (qualified : Name) : List String := qualified.components.map (·.toString (escape := false))

private def pathTerm (qualified : Name) : MacroM Term := do
  let parts := (pathOf qualified).map str
  `([$(parts.toArray),*])

private def listTerm (items : Array Term) : MacroM Term := `([$items,*])

/-- The label of a constructor row declared bare, `![bare]` among its words. -/
private def declaredBareLabel : TSyntax `langDefTermDecl → Option String
  | `(langDefTermDecl| $label:str . $_:langDefTermParam,* |- $_:langDefSyntaxAtom* : $_:ident
      ![ $words:ident,* $[$_:str]? ] ;) =>
      if words.getElems.any (·.getId.toString == "bare") then some label.getString else none
  | `(langDefTermDecl| $label:ident . $_:langDefTermParam,* |- $_:langDefSyntaxAtom* : $_:ident
      ![ $words:ident,* $[$_:str]? ] ;) =>
      if words.getElems.any (·.getId.toString == "bare") then some (label.getId.toString (escape := false)) else none
  | _ => none

/-- The rows of one fragment, through `languageDef!`. -/
private def fragment (termRows : Array (TSyntax `langDefTermDecl)) (equationRows : Array (TSyntax `langDefEquationDecl))
    (rewriteRows : Array (TSyntax `langDefRewriteDecl)) : MacroM Term :=
  `(languageDef! {
      name : "fragment"
      types { }
      terms { $termRows:langDefTermDecl* }
      equations { $equationRows:langDefEquationDecl* }
      rewrites { $rewriteRows:langDefRewriteDecl* }
    })

/-- Equations are numbered within their theory. -/
abbrev Expand := StateT (String × Nat) MacroM

private def nextEquation : Expand Ident := do
  let (owner, count) ← get
  set (owner, count + 1)
  pure (mkIdent (Name.mkSimple s!"{owner}:equation:{count}"))

private def equationRow : TSyntax `moduleEquation → Expand (TSyntax `langDefEquationDecl)
  | `(moduleEquation| $left:langDefPattern == $right:langDefPattern ;) => do
      let label ← nextEquation
      `(langDefEquationDecl| $label:ident . |- $left:langDefPattern = $right:langDefPattern ;)
  | `(moduleEquation| if $premises:langDefPremise,* then $left:langDefPattern == $right:langDefPattern ;) => do
      let label ← nextEquation
      `(langDefEquationDecl| $label:ident . $[$premises.getElems:langDefPremise],* |-
          $left:langDefPattern = $right:langDefPattern ;)
  | `(moduleEquation| $row:langDefEquationDecl) => pure row
  | other => Macro.throwErrorAt other "unsupported equation"

private def rewriteRow : TSyntax `moduleRewrite → MacroM (TSyntax `langDefRewriteDecl)
  | `(moduleRewrite| $label:ident : $left:langDefPattern ~> $right:langDefPattern ;) =>
      `(langDefRewriteDecl| $label:ident . |- $left:langDefPattern ~> $right:langDefPattern ;)
  | `(moduleRewrite| $label:ident : if $premises:langDefPremise,* then $left:langDefPattern ~> $right:langDefPattern ;) =>
      `(langDefRewriteDecl| $label:ident . $[$premises.getElems:langDefPremise],* |-
          $left:langDefPattern ~> $right:langDefPattern ;)
  | `(moduleRewrite| $row:langDefRewriteDecl) => pure row
  | other => Macro.throwErrorAt other "unsupported rewrite"

/-- A type row: a sort of the abstract syntax, or a sort with a carrier. The builtin carriers are named as
CeTTa's core names them (`String`, `Int`, `Bool`), the token carriers as `languageDef!` names them. -/
private def sortRow : TSyntax `moduleSortRow → MacroM Term
  | `(moduleSortRow| $sort:ident ;) => `(TypeDecl.mk $(str sort.getId.toString) CarrierKind.ast)
  | `(moduleSortRow| $sort:ident = $carrier:ident ;) => do
      let kind ← match carrier.getId.toString with
        | "String" => `(CarrierKind.builtinString)
        | "Int" => `(CarrierKind.builtinInt)
        | "Bool" => `(CarrierKind.builtinBool)
        | "label" => `(CarrierKind.tokenLabel)
        | "raw" => `(CarrierKind.tokenRaw)
        | "proofTok" => `(CarrierKind.tokenProof)
        | "path" => `(CarrierKind.tokenPath)
        | other => Macro.throwErrorAt carrier s!"the carrier `{other}` needs an explicit interpretation"
      `(TypeDecl.mk $(str sort.getId.toString) $kind)
  | other => Macro.throwErrorAt other "unsupported type row"

private def exportRow : TSyntax `moduleExport → MacroM Term
  | `(moduleExport| $sort:ident ;) => `(ModuleSource.mkExport $(str sort.getId.toString) none)
  | `(moduleExport| $sort:ident => $target:ident ;) =>
      `(ModuleSource.mkExport $(str sort.getId.toString) (some $(str target.getId.toString)))
  | other => Macro.throwErrorAt other "unsupported export"

private def replacementRow : TSyntax `moduleReplacement → MacroM Term
  | `(moduleReplacement| $old:ident => $declaration:langDefTermDecl) => do
      let rows ← fragment #[declaration] #[] #[]
      `(ModuleSource.mkReplacement $(str old.getId.toString) (ModuleSource.singleRule (LanguageDef.terms $rows)))
  | other => Macro.throwErrorAt other "unsupported replacement"

private partial def inductiveTerm : TSyntax `moduleInductiveTerm → MacroM Term
  | `(moduleInductiveTerm| Type) => `(InductiveSyntax.Term.name "Type")
  | `(moduleInductiveTerm| $label:ident) => `(InductiveSyntax.Term.name $(str label.getId.toString))
  | `(moduleInductiveTerm| ($inner:moduleInductiveTerm)) => inductiveTerm inner
  | `(moduleInductiveTerm| $domain:moduleInductiveTerm -> $codomain:moduleInductiveTerm) => do
      `(InductiveSyntax.Term.arrow $(← inductiveTerm domain) $(← inductiveTerm codomain))
  | `(moduleInductiveTerm| $function:moduleInductiveTerm $argument:moduleInductiveTerm) => do
      `(InductiveSyntax.Term.app $(← inductiveTerm function) $(← inductiveTerm argument))
  | other => Macro.throwErrorAt other "unsupported inductive term"

private def inductiveBinder : TSyntax `moduleInductiveBinder → MacroM Term
  | `(moduleInductiveBinder| $label:ident : $type:moduleInductiveTerm) => do
      `(InductiveSyntax.Binder.mk $(str label.getId.toString) $(← inductiveTerm type))
  | other => Macro.throwErrorAt other "unsupported inductive binder"

private def inductiveConstructor : TSyntax `moduleInductiveConstructor → MacroM Term
  | `(moduleInductiveConstructor| $label:ident ($fields:moduleInductiveBinder,*) : $result:moduleInductiveTerm ;) => do
      `(InductiveSyntax.Constructor.mk $(str label.getId.toString)
        $(← listTerm (← fields.getElems.mapM inductiveBinder)) $(← inductiveTerm result))
  | other => Macro.throwErrorAt other "unsupported inductive constructor"

private def inductiveFamily : TSyntax `moduleInductiveFamily → MacroM Term
  | `(moduleInductiveFamily| $label:ident parameters ($params:moduleInductiveBinder,*)
      indices ($ix:moduleInductiveBinder,*) : $sort:moduleInductiveTerm
      { $constructors:moduleInductiveConstructor* }) => do
      `(InductiveSyntax.Family.mk $(str label.getId.toString)
        $(← listTerm (← params.getElems.mapM inductiveBinder))
        $(← listTerm (← ix.getElems.mapM inductiveBinder)) $(← inductiveTerm sort)
        $(← listTerm (← constructors.mapM inductiveConstructor)))
  | other => Macro.throwErrorAt other "unsupported inductive family"

private def blockTerm : TSyntax `moduleBlock → Expand Term
  | `(moduleBlock| Inductives { $families:moduleInductiveFamily* }) => do
      `(Block.inductives $(← listTerm (← families.mapM fun family => (inductiveFamily family : MacroM _))))
  | `(moduleBlock| Types { $rows:moduleSortRow* }) => do
      let declarations ← listTerm (← rows.mapM fun row => (sortRow row : MacroM _))
      `(Block.types $declarations)
  | `(moduleBlock| Exports { $rows:moduleExport* }) => do
      let rows ← listTerm (← rows.mapM fun row => (exportRow row : MacroM _))
      `(Block.exports $rows)
  | `(moduleBlock| Terms { $rows:langDefTermDecl* }) => do
      let built ← fragment rows #[] #[]
      let bare ← listTerm ((rows.filterMap declaredBareLabel).map str)
      `(Block.terms (LanguageDef.terms $built) $bare)
  | `(moduleBlock| Replacements { $rows:moduleReplacement* }) => do
      let rows ← listTerm (← rows.mapM fun row => (replacementRow row : MacroM _))
      `(Block.replacements $rows)
  | `(moduleBlock| Equations { $rows:moduleEquation* }) => do
      let built ← fragment #[] (← rows.mapM equationRow) #[]
      `(Block.equations (LanguageDef.equations $built))
  | `(moduleBlock| Rewrites { $rows:moduleRewrite* }) => do
      let built ← fragment #[] #[] (← rows.mapM fun row => (rewriteRow row : MacroM _))
      `(Block.rewrites (LanguageDef.rewrites $built))
  | other => Macro.throwErrorAt other "unsupported block"

private partial def exprTerm : TSyntax `moduleExpr → Expand Term
  | `(moduleExpr| $ref:ident) =>
      if ref.getId == `Empty then `(Expr.extend none [])
      else `(Expr.ref $(str ref.getId.toString))
  | `(moduleExpr| $target:ident ( $args:moduleExpr,* )) => do
      let args ← listTerm (← args.getElems.mapM exprTerm)
      `(Expr.apply $(← pathTerm target.getId) $args)
  | `(moduleExpr| { $inner:moduleExpr }) => exprTerm inner
  | `(moduleExpr| ( $inner:moduleExpr )) => exprTerm inner
  | `(moduleExpr| $blocks:moduleBlock*) => do
      let blocks ← listTerm (← blocks.mapM blockTerm)
      `(Expr.extend none $blocks)
  | `(moduleExpr| $base:moduleExpr $blocks:moduleBlock*) => do
      let base ← exprTerm base
      let blocks ← listTerm (← blocks.mapM blockTerm)
      `(Expr.extend (some $base) $blocks)
  | `(moduleExpr| $left:moduleExpr \/ $right:moduleExpr) => do
      `(Expr.join $(← exprTerm left) $(← exprTerm right))
  | `(moduleExpr| let $bound:ident = $value:moduleExpr in $body:moduleExpr) => do
      `(Expr.letIn $(str bound.getId.toString) $(← exprTerm value) $(← exprTerm body))
  | other => Macro.throwErrorAt other "unsupported theory expression"

private def theoryTerm : TSyntax `moduleTheory → MacroM Term
  | `(moduleTheory| Theory $theoryId:ident ( $params:moduleParam,* ) { $body:moduleExpr }) => do
      let params ← params.getElems.mapM fun param => match param with
        | `(moduleParam| $p:ident : $t:ident) => do
            `(ModuleSource.mkParam $(str p.getId.toString) $(← pathTerm t.getId))
        | other => Macro.throwErrorAt other "unsupported parameter"
      let paramList ← listTerm params
      let (body, _) ← (exprTerm body).run (theoryId.getId.toString, 0)
      `(ModuleSource.mkTheory $(str theoryId.getId.toString) $paramList $body)
  | other => Macro.throwErrorAt other "unsupported theory"

/-- A module file's data, and the modules it imports by file. -/
private def moduleTerm (file : TSyntax `moduleFile) : MacroM (Name × Term × List (String × Name)) := do
  match file with
  | `(moduleFile| $imports:moduleImport* Module $moduleId:ident { $theories:moduleTheory* $[$entry:moduleEntry]? }) =>
      let imported ← imports.toList.mapM fun item => match item with
        | `(moduleImport| import $path:str as $qualifier:ident) =>
            pure (path.getString, qualifier.getId.toString)
        | other => Macro.throwErrorAt other "unsupported import"
      let importTerms ← listTerm (← imported.toArray.mapM fun (path, qualifier) =>
        `(ModuleSource.mkImport $(str path) $(str qualifier)))
      let theoryTerms ← listTerm (← theories.mapM theoryTerm)
      let entryTerm ← match entry with
        | some stx => match stx with
          | `(moduleEntry| theory $target:ident ( $args:moduleExpr,* )) => do
              let (args, _) ← (args.getElems.mapM exprTerm).run ("entry", 0)
              `(some ($(← pathTerm target.getId), $(← listTerm args)))
          | other => Macro.throwErrorAt other "unsupported entry"
        | none => `(none)
      let data ← `(ModuleSource.mkModule $importTerms $(str moduleId.getId.toString) $theoryTerms $entryTerm)
      let dependencies := imported.map fun (path, _) =>
        (path, Name.mkSimple ((path.splitOn "/").getLast!.replace ".module" ""))
      pure (moduleId.getId, data, dependencies)
  | other => Macro.throwErrorAt other "unsupported module file"

/-- Define `X.module`, `X.library` and `X.language` for a parsed module file. -/
def elabModuleFile (file : TSyntax `moduleFile) : CommandElabM Unit := do
  let (base, data, dependencies) ← liftMacroM (moduleTerm file)
  let moduleId := mkIdent (base ++ `module)
  let libraryId := mkIdent (base ++ `library)
  let languageId := mkIdent (base ++ `language)
  let own ← dependencies.toArray.mapM fun (path, dependency) =>
    `(term| [($(str path), $(mkIdent (dependency ++ `module)))] ++ $(mkIdent (dependency ++ `library)))
  let library ← own.foldlM (fun acc item => `(term| $acc ++ $item)) (← `(term| []))
  elabCommand (← `(def $moduleId : ModuleSource.ModuleData := $data))
  elabCommand (← `(def $libraryId : List (String × ModuleSource.ModuleData) := $library))
  elabCommand (← `(def $languageId : Except ModuleSource.Error LanguageDef :=
    ModuleSource.elaborate $libraryId $moduleId))

/-- `Module X { … }` directly in a Lean file. -/
scoped syntax (name := moduleCommand) "Module" ident "{" moduleTheory* (moduleEntry)? "}" : command

@[command_elab moduleCommand] def elabModuleCommand : CommandElab := fun stx => do
  match stx with
  | `(Module $moduleId:ident { $theories:moduleTheory* $[$entry:moduleEntry]? }) =>
      elabModuleFile (← `(moduleFile| Module $moduleId:ident { $theories:moduleTheory* $[$entry:moduleEntry]? }))
  | _ => throwUnsupportedSyntax

/-- `#module <module file>`: a module with its `import` lines, directly in a Lean file. -/
scoped syntax (name := moduleTextCommand) "#module " moduleFile : command

@[command_elab moduleTextCommand] def elabModuleTextCommand : CommandElab := fun stx => do
  match stx with
  | `(#module $file:moduleFile) => elabModuleFile file
  | _ => throwUnsupportedSyntax

/-- Drop `{- … -}` comments, which the format uses and Lean does not. Nested comments nest. -/
partial def stripBlockComments (text : String) : String :=
  let rec go (chars : List Char) (depth : Nat) (out : List Char) : List Char :=
    match chars with
    | [] => out.reverse
    | '{' :: '-' :: rest => go rest (depth + 1) out
    | '-' :: '}' :: rest => if depth > 0 then go rest (depth - 1) out else go rest depth ('}' :: '-' :: out)
    | c :: rest => if depth > 0 then go rest depth (if c == '\n' then c :: out else out) else go rest depth (c :: out)
  String.ofList (go text.toList 0 [])

/-- `#module_file "path"`: read a `.module` file and define its module. The path is relative to
the directory of the current Lean file. Like `open`, it makes the format's syntax and the row
syntax of `languageDef!` available in the rest of the file. -/
scoped syntax (name := moduleFileCommand) "#module_file " str : command

@[command_elab moduleFileCommand] def elabModuleFileCommand : CommandElab := fun stx => do
  match stx with
  | `(#module_file $path:str) => do
      let here := (← getFileName)
      let base := (System.FilePath.mk here).parent.getD "."
      let target := base / path.getString
      let text ← IO.FS.readFile target
      -- The format's syntax and the row syntax of `languageDef!`, as an `open` would.
      activateScoped `Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
      activateScoped `Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
      let env ← getEnv
      match Parser.runParserCategory env `moduleFile (stripBlockComments text) target.toString with
      | .ok parsed => elabModuleFile ⟨parsed⟩
      | .error message => throwError "{target}: {message}"
  | _ => throwUnsupportedSyntax

/-- `#module_roundtrip X`: print `X.module`, read the text back with the same syntax, and check
that the module data is unchanged. -/
scoped syntax (name := moduleRoundtripCommand) "#module_roundtrip " ident : command

/-- **The module a `.module` text reads as**, with the format's syntax, without its imports' modules. -/
unsafe def readModuleText (text : String) (source : String := "<text>") : CommandElabM ModuleSource.ModuleData := do
  activateScoped `Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
  activateScoped `Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
  match Parser.runParserCategory (← getEnv) `moduleFile (stripBlockComments text) source with
  | .error message => throwError "{source} does not read: {message}\n{text}"
  | .ok parsed =>
      let (_, data, _) ← liftMacroM (moduleTerm ⟨parsed⟩)
      liftTermElabM do
        let term ← elabTermEnsuringType data (some (Lean.mkConst ``ModuleSource.ModuleData))
        synthesizeSyntheticMVarsNoPostponing
        let term ← instantiateMVars term
        Lean.Meta.evalExpr ModuleSource.ModuleData (Lean.mkConst ``ModuleSource.ModuleData) term

@[command_elab moduleRoundtripCommand] unsafe def elabModuleRoundtrip : CommandElab := fun stx => do
  match stx with
  | `(#module_roundtrip $base:ident) => do
      let constant ← liftCoreM (realizeGlobalConstNoOverload (mkIdent (base.getId ++ `module)))
      let original ← liftTermElabM (evalConst ModuleSource.ModuleData constant)
      let text := ModuleSource.Printer.print original
      let reread ← readModuleText text "the printed module"
      if reprStr reread == reprStr original then
        logInfo m!"{base.getId}: printed and read back unchanged ({text.length} characters)"
      else
        throwError "{base.getId}: the module changed in the round trip\n{text}"
  | _ => throwUnsupportedSyntax

end Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
