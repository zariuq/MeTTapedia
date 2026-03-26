import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Generic `language!`-Style DSL for Any `LanguageDef`

This module provides reusable notation and builders for authoring
`Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef` values.

Positive example:
- a language module can use `T!`, `N!`, `P!`, `App!`, `Rel!` and `mkLang`
  without defining local one-off syntax helpers.

Negative example:
- this is only authoring sugar and does not make semantics stronger by itself;
  semantic completeness still depends on explicit rewrites/premises/equations.
-/

namespace Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

open Lean
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Token / Parameter / Pattern Macros -/

scoped syntax "T!" str : term
scoped syntax "N!" str : term
scoped syntax "Sep!" str : term
scoped syntax "Delim!" str str : term
scoped syntax "P!" str ":" str : term
scoped syntax "AParam!" str ":" str : term
scoped syntax "MParam!" str ":" str : term
scoped syntax "Var!" str : term
scoped syntax "App!" str "[" term,* "]" : term
scoped syntax "Rel!" str "[" term,* "]" : term
scoped syntax "relation" str "[" term,* "]" : term
scoped syntax "rule" str : term
scoped syntax "external" str "[" term,* "]" "->" term : term
scoped syntax "languageDef!" "{"
  "name" ":" term ","
  "types" ":" term ","
  "terms" ":" term ","
  "equations" ":" term ","
  "rewrites" ":" term ","
  "logic" ":" term ","
  "oracles" ":" term ","
  "congruenceCollections" ":" term
  "}" : term

/-! ## Parsed `language!`-Style Surface Syntax -/

declare_syntax_cat langDefTypeExpr
declare_syntax_cat langDefTypeAtom
declare_syntax_cat langDefTypeDecl
declare_syntax_cat langDefTermParam
declare_syntax_cat langDefSyntaxAtom
declare_syntax_cat langDefSyntaxOp
declare_syntax_cat langDefSyntaxOpSource
declare_syntax_cat langDefPattern
declare_syntax_cat langDefPatternOp
declare_syntax_cat langDefPatternOpSource
declare_syntax_cat langDefRestVar
declare_syntax_cat langDefTypeBinding
declare_syntax_cat langDefPremise
declare_syntax_cat langDefTermDecl
declare_syntax_cat langDefEquationDecl
declare_syntax_cat langDefRewriteDecl
declare_syntax_cat langDefLogicDecl
declare_syntax_cat langDefOracleDecl

scoped syntax ident : langDefTypeAtom
scoped syntax ident "(" langDefTypeExpr ")" : langDefTypeAtom
scoped syntax "(" langDefTypeExpr ")" : langDefTypeAtom
scoped syntax langDefTypeAtom : langDefTypeExpr
scoped syntax langDefTypeAtom "->" langDefTypeExpr : langDefTypeExpr
scoped syntax ident "*" "->" langDefTypeExpr : langDefTypeExpr

scoped syntax ident : langDefTypeDecl
scoped syntax "![" ident "]" "as" ident : langDefTypeDecl

scoped syntax ident ":" langDefTypeExpr : langDefTermParam
scoped syntax "^" ident "." ident ":" "[" langDefTypeExpr "]" : langDefTermParam
scoped syntax "^" ident ":" "[" langDefTypeExpr "]" : langDefTermParam
scoped syntax "^[" ident,* "]" "." ident ":" "[" langDefTypeExpr "]" : langDefTermParam

scoped syntax str : langDefSyntaxAtom
scoped syntax ident : langDefSyntaxAtom
scoped syntax ident ".*sep(" str ")" : langDefSyntaxAtom
scoped syntax ident ".*delim(" str "," str ")" : langDefSyntaxAtom
scoped syntax langDefSyntaxOp : langDefSyntaxAtom

scoped syntax ident : langDefSyntaxOpSource
scoped syntax langDefSyntaxOp : langDefSyntaxOpSource
scoped syntax "*" "sep(" ident "," str ")" : langDefSyntaxOp
scoped syntax "*" "zip(" ident "," ident ")" : langDefSyntaxOp
scoped syntax "*" "map(" langDefSyntaxOpSource "," "|" ident,* "|" langDefSyntaxAtom* ")" : langDefSyntaxOp
scoped syntax "*" "opt(" langDefSyntaxAtom* ")" : langDefSyntaxOp
scoped syntax ident ".*sep(" str ")" : langDefSyntaxOp
scoped syntax langDefSyntaxOp ".*sep(" str ")" : langDefSyntaxOp
scoped syntax ident ".*map(" "|" ident,* "|" langDefSyntaxAtom* ")" : langDefSyntaxOp
scoped syntax langDefSyntaxOp ".*map(" "|" ident,* "|" langDefSyntaxAtom* ")" : langDefSyntaxOp

scoped syntax ident : langDefPatternOpSource
scoped syntax langDefPatternOp : langDefPatternOpSource
scoped syntax "*" "zip(" langDefPatternOpSource "," langDefPatternOpSource ")" : langDefPatternOp
scoped syntax "*" "map(" langDefPatternOpSource "," "|" ident,* "|" langDefPattern ")" : langDefPatternOp
scoped syntax ident ".*map(" "|" ident,* "|" langDefPattern ")" : langDefPatternOp
scoped syntax langDefPatternOp ".*map(" "|" ident,* "|" langDefPattern ")" : langDefPatternOp

scoped syntax "#" num : langDefPattern
scoped syntax str : langDefPattern
scoped syntax ident : langDefPattern
scoped syntax langDefPatternOp : langDefPattern
scoped syntax "..." ident : langDefPattern
scoped syntax num : langDefPattern
scoped syntax "-" num : langDefPattern
scoped syntax "eval(" langDefPattern "," langDefPattern ")" : langDefPattern
scoped syntax "(" "eval" ident langDefPattern ")" : langDefPattern
scoped syntax "(" "eval" langDefPattern langDefPattern ")" : langDefPattern
scoped syntax str "(" langDefPattern,* ")" : langDefPattern
scoped syntax ident "(" langDefPattern,* ")" : langDefPattern
scoped syntax ident langDefPattern+ : langDefPattern
scoped syntax "(" ident langDefPattern+ ")" : langDefPattern
scoped syntax "(" langDefPattern ")" : langDefPattern
scoped syntax "^" ident "." langDefPattern : langDefPattern
scoped syntax "^" ident ".(" langDefPattern ")" : langDefPattern
scoped syntax "^" ident "." "(" langDefPattern ")" : langDefPattern
scoped syntax "^" ident : langDefPattern
scoped syntax "^[" ident,* "]" "." langDefPattern : langDefPattern
scoped syntax "^[" ident,* "]" ".(" langDefPattern ")" : langDefPattern
scoped syntax "^[" ident,* "]" "." "(" langDefPattern ")" : langDefPattern
scoped syntax "..." ident : langDefRestVar
scoped syntax "{" langDefRestVar "}" : langDefPattern
scoped syntax "{" langDefPattern,+ "," langDefRestVar "}" : langDefPattern
scoped syntax "{" langDefPattern,* "}" : langDefPattern

scoped syntax ident ":" langDefTypeExpr : langDefTypeBinding

scoped syntax ident "#" "..." ident : langDefPremise
scoped syntax ident "#" langDefRestVar : langDefPremise
scoped syntax ident "#" langDefPattern : langDefPremise
scoped syntax langDefPattern "~>" langDefPattern : langDefPremise
scoped syntax ident "(" langDefPattern,* ")" : langDefPremise
scoped syntax ident ".*map(" "|" ident "|" langDefPremise ")" : langDefPremise
scoped syntax "forAll(" ident "," ident "," langDefPremise ")" : langDefPremise

scoped syntax ident "." langDefTermParam,* "|-" langDefSyntaxAtom* ":" ident ";" : langDefTermDecl
scoped syntax ident "." langDefTypeBinding,* "|-" langDefPattern "=" langDefPattern ";" : langDefEquationDecl
scoped syntax ident "." langDefPremise,* "|-" langDefPattern "=" langDefPattern ";" : langDefEquationDecl
scoped syntax ident "." langDefTypeBinding,* "|" langDefPremise,* "|-" langDefPattern "=" langDefPattern ";" : langDefEquationDecl
scoped syntax ident "." langDefTypeBinding,* "|-" langDefPattern "~>" langDefPattern ";" : langDefRewriteDecl
scoped syntax ident "." langDefPremise,* "|-" langDefPattern "~>" langDefPattern ";" : langDefRewriteDecl
scoped syntax ident "." langDefTypeBinding,* "|" langDefPremise,* "|-" langDefPattern "~>" langDefPattern ";" : langDefRewriteDecl
scoped syntax "relation" ident "(" langDefTypeExpr,* ")" ";" : langDefLogicDecl
scoped syntax "rule" str ";" : langDefLogicDecl
scoped syntax "external" ident "(" langDefTypeExpr,* ")" "->" langDefTypeExpr ";" : langDefOracleDecl

private def mkStrTerm (s : String) : TSyntax `term :=
  ⟨Syntax.mkStrLit s⟩

private def splitCompactBinderIdent (ident : Lean.Name) : MacroM (String × String) := do
  match ident.toString.splitOn "." with
  | [binderName, bodyName] =>
      pure (binderName, bodyName)
  | _ =>
      Macro.throwError s!"unsupported compact binder form `{ident}`; expected `^x.p`"

private def carrierTerm (carrier : CarrierKind) : TSyntax `term :=
  ⟨mkIdent <|
    match carrier with
    | .ast => ``CarrierKind.ast
    | .tokenLabel => ``CarrierKind.tokenLabel
    | .tokenRaw => ``CarrierKind.tokenRaw
    | .tokenProof => ``CarrierKind.tokenProof
    | .tokenPath => ``CarrierKind.tokenPath
    | .builtinInt => ``CarrierKind.builtinInt
    | .builtinString => ``CarrierKind.builtinString
    | .builtinBool => ``CarrierKind.builtinBool
  ⟩

private def collTerm (ct : CollType) : TSyntax `term :=
  ⟨mkIdent <|
    match ct with
    | .vec => ``CollType.vec
    | .hashBag => ``CollType.hashBag
    | .hashSet => ``CollType.hashSet
  ⟩

private def resolveCarrierName (stx : Syntax) : MacroM CarrierKind := do
  let carrierName := stx.getId.toString
  match carrierName with
  | "label" => pure .tokenLabel
  | "raw" => pure .tokenRaw
  | "proofTok" => pure .tokenProof
  | "path" => pure .tokenPath
  | "i64" => pure .builtinInt
  | "str" => pure .builtinString
  | "bool" => pure .builtinBool
  | other =>
      Macro.throwErrorAt stx s!"unsupported carrier `{other}`"

private def resolveCollName (stx : Syntax) : MacroM CollType := do
  let collName := stx.getId.toString
  match collName with
  | "vec" => pure .vec
  | "Vec" => pure .vec
  | "hashBag" => pure .hashBag
  | "HashBag" => pure .hashBag
  | "hashSet" => pure .hashSet
  | "HashSet" => pure .hashSet
  | other =>
      Macro.throwErrorAt stx s!"unsupported congruence collection `{other}`"

private structure ExpandedPattern where
  term : TSyntax `term
  surface : String
  restName? : Option String := none
deriving Inhabited

private structure ExpandedPremise where
  term : TSyntax `term
  surface : String
deriving Inhabited

private def mkExpandedPattern (term : TSyntax `term) (surface : String)
    (restName? : Option String := none) : ExpandedPattern :=
  { term := term, surface := surface, restName? := restName? }

private def renderSurfaceStringLit (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

private def restVarName (stx : TSyntax `langDefRestVar) : MacroM String := do
  match stx with
  | `(langDefRestVar| ... $rest:ident) => pure rest.getId.toString
  | _ => Macro.throwErrorAt stx "unsupported collection rest variable"

private def sepSyntaxToList (node : Syntax) : List Syntax :=
  ((@Syntax.SepArray.mk "," node.getArgs) : Array Syntax).toList

private partial def normalizeChoiceSyntax (stx : Syntax) : Syntax :=
  if stx.isOfKind choiceKind && stx.getNumArgs > 0 then
    normalizeChoiceSyntax stx[0]
  else
    stx

private def flattenLists (xs : List (List α)) : List α :=
  xs.foldr List.append []

private def mkTermList : List (TSyntax `term) → MacroM (TSyntax `term)
  | [] => `([])
  | x :: xs => do
      let xs' ← mkTermList xs
      `($x :: $xs')

private partial def expandTypeExpr : TSyntax `langDefTypeExpr → MacroM (TSyntax `term)
  | `(langDefTypeExpr| $atom:langDefTypeAtom) => expandTypeAtom atom
  | `(langDefTypeExpr| $dom:langDefTypeAtom -> $cod:langDefTypeExpr) => do
      let dom' ← expandTypeAtom dom
      let cod' ← expandTypeExpr cod
      `(TypeExpr.arrow $dom' $cod')
  | `(langDefTypeExpr| $base:ident * -> $cod:langDefTypeExpr) => do
      let cod' ← expandTypeExpr cod
      `(TypeExpr.arrow (TypeExpr.multiBinder (TypeExpr.base $(mkStrTerm base.getId.toString))) $cod')
  | stx => Macro.throwErrorAt stx "unsupported type expression"
where
  expandTypeAtom : TSyntax `langDefTypeAtom → MacroM (TSyntax `term)
    | `(langDefTypeAtom| $nm:ident) =>
        `(TypeExpr.base $(mkStrTerm nm.getId.toString))
    | `(langDefTypeAtom| $coll:ident($inner:langDefTypeExpr)) => do
        let inner' ← expandTypeExpr inner
        let collType ← resolveCollName coll
        `(TypeExpr.collection $(collTerm collType) $inner')
    | `(langDefTypeAtom| ($inner:langDefTypeExpr)) =>
        expandTypeExpr inner
    | stx => Macro.throwErrorAt stx "unsupported type atom"

private def expandTypeDecl : TSyntax `langDefTypeDecl → MacroM (TSyntax `term)
  | `(langDefTypeDecl| $nm:ident) =>
      `(TypeDecl.mk $(mkStrTerm nm.getId.toString) CarrierKind.ast)
  | `(langDefTypeDecl| ![$carrier:ident] as $nm:ident) => do
      let carrierKind ← resolveCarrierName carrier
      `(TypeDecl.mk $(mkStrTerm nm.getId.toString) $(carrierTerm carrierKind))
  | stx => Macro.throwErrorAt stx "unsupported type declaration"

private def expandTermParam : TSyntax `langDefTermParam → MacroM (TSyntax `term)
  | `(langDefTermParam| $nm:ident:$ty:langDefTypeExpr) => do
      let ty' ← expandTypeExpr ty
      `(TermParam.simple $(mkStrTerm nm.getId.toString) $ty')
  | `(langDefTermParam| ^ $binder:ident . $body:ident : [ $ty:langDefTypeExpr ]) => do
      let ty' ← expandTypeExpr ty
      `(TermParam.abstractionWithBinder
          $(mkStrTerm binder.getId.toString)
          $(mkStrTerm body.getId.toString)
          $ty')
  | `(langDefTermParam| ^ $binderAndBody:ident : [ $ty:langDefTypeExpr ]) => do
      let (binderName, bodyName) ← splitCompactBinderIdent binderAndBody.getId
      let ty' ← expandTypeExpr ty
      `(TermParam.abstractionWithBinder
          $(mkStrTerm binderName)
          $(mkStrTerm bodyName)
          $ty')
  | `(langDefTermParam| ^[ $binders:ident,* ] . $body:ident : [ $ty:langDefTypeExpr ]) => do
      let binderTerms ← binders.getElems.toList.mapM (fun binder =>
        pure (mkStrTerm binder.getId.toString))
      let binderList ← mkTermList binderTerms
      let ty' ← expandTypeExpr ty
      `(TermParam.multiAbstractionWithBinders
          $binderList
          $(mkStrTerm body.getId.toString)
          $ty')
  | stx => Macro.throwErrorAt stx "unsupported term parameter"

mutual

private partial def expandSyntaxOpSource : TSyntax `langDefSyntaxOpSource → MacroM (TSyntax `term)
  | `(langDefSyntaxOpSource| $nm:ident) =>
      `(SyntaxPatternOp.var $(mkStrTerm nm.getId.toString))
  | `(langDefSyntaxOpSource| $op:langDefSyntaxOp) =>
      expandSyntaxOp op
  | stx => Macro.throwErrorAt stx "unsupported syntax op source"

private partial def expandSyntaxOp : TSyntax `langDefSyntaxOp → MacroM (TSyntax `term)
  | `(langDefSyntaxOp| *sep($nm:ident, $sep:str)) =>
      `(SyntaxPatternOp.sep $(mkStrTerm nm.getId.toString) $sep none)
  | `(langDefSyntaxOp| $nm:ident.*sep($sep:str)) =>
      `(SyntaxPatternOp.sep $(mkStrTerm nm.getId.toString) $sep none)
  | `(langDefSyntaxOp| $src:langDefSyntaxOp.*sep($sep:str)) => do
      let src' ← expandSyntaxOp src
      `(SyntaxPatternOp.sep "__chain__" $sep (some $src'))
  | `(langDefSyntaxOp| *zip($left:ident, $right:ident)) =>
      `(SyntaxPatternOp.zip $(mkStrTerm left.getId.toString) $(mkStrTerm right.getId.toString))
  | `(langDefSyntaxOp| *map($src:langDefSyntaxOpSource, | $params:ident,* | $body:langDefSyntaxAtom*)) => do
      let src' ← expandSyntaxOpSource src
      let paramTerms ← params.getElems.toList.mapM (fun p => pure (mkStrTerm p.getId.toString))
      let bodyItems ← body.toList.mapM expandSyntaxAtomAsItem
      let paramsTerm ← mkTermList paramTerms
      let bodyTerm ← mkTermList bodyItems
      `(SyntaxPatternOp.map $src' $paramsTerm $bodyTerm)
  | `(langDefSyntaxOp| $src:ident.*map(| $params:ident,* | $body:langDefSyntaxAtom*)) => do
      let src' : TSyntax `term := ← `(SyntaxPatternOp.var $(mkStrTerm src.getId.toString))
      let paramTerms ← params.getElems.toList.mapM (fun p => pure (mkStrTerm p.getId.toString))
      let bodyItems ← body.toList.mapM expandSyntaxAtomAsItem
      let paramsTerm ← mkTermList paramTerms
      let bodyTerm ← mkTermList bodyItems
      `(SyntaxPatternOp.map $src' $paramsTerm $bodyTerm)
  | `(langDefSyntaxOp| $src:langDefSyntaxOp.*map(| $params:ident,* | $body:langDefSyntaxAtom*)) => do
      let src' ← expandSyntaxOp src
      let paramTerms ← params.getElems.toList.mapM (fun p => pure (mkStrTerm p.getId.toString))
      let bodyItems ← body.toList.mapM expandSyntaxAtomAsItem
      let paramsTerm ← mkTermList paramTerms
      let bodyTerm ← mkTermList bodyItems
      `(SyntaxPatternOp.map $src' $paramsTerm $bodyTerm)
  | `(langDefSyntaxOp| *opt($body:langDefSyntaxAtom*)) => do
      let bodyItems ← body.toList.mapM expandSyntaxAtomAsItem
      let bodyTerm ← mkTermList bodyItems
      `(SyntaxPatternOp.opt $bodyTerm)
  | stx => Macro.throwErrorAt stx "unsupported syntax operator"

private partial def expandSyntaxAtomAsItem (atom : TSyntax `langDefSyntaxAtom) : MacroM (TSyntax `term) := do
  match atom with
  | `(langDefSyntaxAtom| $op:langDefSyntaxOp) => do
      let op' ← expandSyntaxOp op
      `(SyntaxItem.op $op')
  | _ =>
      let arr ← expandSyntaxAtom atom
      match Array.size arr with
      | 1 => pure arr[0]!
      | _ => Macro.throwErrorAt atom "metasyntax bodies require single syntax items"

private partial def expandSyntaxAtom : TSyntax `langDefSyntaxAtom → MacroM (Array (TSyntax `term))
  | `(langDefSyntaxAtom| $tok:str) => do
      let item ← `(SyntaxItem.terminal $tok)
      pure #[item]
  | `(langDefSyntaxAtom| $nm:ident) => do
      let item ← `(SyntaxItem.nonTerminal $(mkStrTerm nm.getId.toString))
      pure #[item]
  | `(langDefSyntaxAtom| $nm:ident.*sep($sep:str)) => do
      let op ← `(SyntaxItem.op
        (SyntaxPatternOp.sep $(mkStrTerm nm.getId.toString) $sep none))
      pure #[op]
  | `(langDefSyntaxAtom| $nm:ident.*delim($l:str, $r:str)) =>
      do
        let nt ← `(SyntaxItem.nonTerminal $(mkStrTerm nm.getId.toString))
        let delim ← `(SyntaxItem.delimiter $l $r)
        pure #[nt, delim]
  | `(langDefSyntaxAtom| $op:langDefSyntaxOp) => do
      let op' ← expandSyntaxOp op
      let item ← `(SyntaxItem.op $op')
      pure #[item]
  | stx => Macro.throwErrorAt stx "unsupported syntax atom"

end

mutual

private partial def expandPatternOpSourceInfo
    : TSyntax `langDefPatternOpSource → MacroM ExpandedPattern
  | `(langDefPatternOpSource| $nm:ident) => do
      let raw := nm.getId.toString
      let term ← `(Pattern.fvar $(mkStrTerm raw))
      pure (mkExpandedPattern term raw)
  | `(langDefPatternOpSource| $op:langDefPatternOp) =>
      expandPatternOpInfo op
  | stx => Macro.throwErrorAt stx "unsupported pattern op source"

private partial def expandPatternOpInfo
    : TSyntax `langDefPatternOp → MacroM ExpandedPattern
  | `(langDefPatternOp| *zip($left:langDefPatternOpSource, $right:langDefPatternOpSource)) => do
      let left' ← expandPatternOpSourceInfo left
      let right' ← expandPatternOpSourceInfo right
      let leftTerm := left'.term
      let rightTerm := right'.term
      let term ← `(Pattern.zip $leftTerm $rightTerm)
      pure (mkExpandedPattern term s!"*zip({left'.surface}, {right'.surface})")
  | `(langDefPatternOp| *map($src:langDefPatternOpSource, | $params:ident,* | $body:langDefPattern)) => do
      let src' ← expandPatternOpSourceInfo src
      let body' ← expandPatternInfo body
      let paramNames := params.getElems.toList.map (fun p => p.getId.toString)
      let paramTerms ← params.getElems.toList.mapM (fun p => pure (mkStrTerm p.getId.toString))
      let paramList ← mkTermList paramTerms
      let srcTerm := src'.term
      let bodyTerm := body'.term
      let term ← `(Pattern.map $srcTerm $paramList $bodyTerm)
      let renderedParams := String.intercalate ", " paramNames
      pure (mkExpandedPattern term s!"*map({src'.surface}, |{renderedParams}| {body'.surface})")
  | `(langDefPatternOp| $src:ident.*map(| $params:ident,* | $body:langDefPattern)) => do
      let src' : ExpandedPattern :=
        { term := ← `(Pattern.fvar $(mkStrTerm src.getId.toString)), surface := src.getId.toString }
      let body' ← expandPatternInfo body
      let paramNames := params.getElems.toList.map (fun p => p.getId.toString)
      let paramTerms ← params.getElems.toList.mapM (fun p => pure (mkStrTerm p.getId.toString))
      let paramList ← mkTermList paramTerms
      let srcTerm := src'.term
      let bodyTerm := body'.term
      let term ← `(Pattern.map $srcTerm $paramList $bodyTerm)
      let renderedParams := String.intercalate ", " paramNames
      pure (mkExpandedPattern term s!"{src'.surface}.*map(|{renderedParams}| {body'.surface})")
  | `(langDefPatternOp| $src:langDefPatternOp.*map(| $params:ident,* | $body:langDefPattern)) => do
      let src' ← expandPatternOpInfo src
      let body' ← expandPatternInfo body
      let paramNames := params.getElems.toList.map (fun p => p.getId.toString)
      let paramTerms ← params.getElems.toList.mapM (fun p => pure (mkStrTerm p.getId.toString))
      let paramList ← mkTermList paramTerms
      let srcTerm := src'.term
      let bodyTerm := body'.term
      let term ← `(Pattern.map $srcTerm $paramList $bodyTerm)
      let renderedParams := String.intercalate ", " paramNames
      pure (mkExpandedPattern term s!"{src'.surface}.*map(|{renderedParams}| {body'.surface})")
  | stx => Macro.throwErrorAt stx "unsupported pattern operator"

private partial def splitPrefixPatternArgs (stx : TSyntax `langDefPattern) :
    MacroM (List (TSyntax `langDefPattern)) := do
  let stx : TSyntax `langDefPattern := ⟨normalizeChoiceSyntax stx.raw⟩
  match stx with
  | `(langDefPattern| $head:ident $args*) => do
      let headPat ← `(langDefPattern| $head:ident)
      let tailArgs ← args.toList.mapM (fun arg => splitPrefixPatternArgs ⟨arg⟩)
      pure (headPat :: flattenLists tailArgs)
  | `(langDefPattern| $head:ident($args:langDefPattern,*)) => do
      let headPat ← `(langDefPattern| $head:ident)
      let argPats := args.getElems.toList.map (fun arg => ⟨normalizeChoiceSyntax arg⟩)
      pure (headPat :: argPats)
  | _ =>
      pure [stx]

private partial def expandPatternInfo (stx0 : TSyntax `langDefPattern) : MacroM ExpandedPattern := do
  let stx : TSyntax `langDefPattern := ⟨normalizeChoiceSyntax stx0.raw⟩
  match stx with
  | `(langDefPattern| #$n:num) => do
      let term ← `(Pattern.bvar $(quote n.getNat))
      pure (mkExpandedPattern term s!"#{n.getNat}")
  | `(langDefPattern| $nm:str) => do
      let term ← `(Pattern.apply $nm [])
      pure (mkExpandedPattern term (renderSurfaceStringLit nm.getString))
  | `(langDefPattern| $ctor:ident $args*) => do
      let argSyntax ← args.toList.mapM (fun arg => splitPrefixPatternArgs ⟨arg⟩)
      let args' ← (flattenLists argSyntax).mapM expandPatternInfo
      let argsTerm ← mkTermList (args'.map (·.term))
      let ctorName := ctor.getId.toString
      let surfaceArgs := String.intercalate " " (args'.map (·.surface))
      let term ← `(Pattern.apply $(mkStrTerm ctorName) $argsTerm)
      pure (mkExpandedPattern term s!"{ctorName} {surfaceArgs}")
  | `(langDefPattern| $nm:ident) => do
      let raw := nm.getId.toString
      let term ← `(Pattern.fvar $(mkStrTerm raw))
      pure (mkExpandedPattern term raw)
  | `(langDefPattern| $op:langDefPatternOp) =>
      expandPatternOpInfo op
  | `(langDefPattern| ... $rest:ident) => do
      let restName := rest.getId.toString
      let term ← `(Pattern.collection CollType.hashBag [] (some $(mkStrTerm restName)))
      pure (mkExpandedPattern term ("..." ++ restName) (some restName))
  | `(langDefPattern| $n:num) => do
      let raw := toString n.getNat
      let term ← `(Pattern.apply $(mkStrTerm raw) [])
      pure (mkExpandedPattern term raw)
  | `(langDefPattern| -$n:num) => do
      let raw := s!"-{n.getNat}"
      let term ← `(Pattern.apply $(mkStrTerm raw) [])
      pure (mkExpandedPattern term raw)
  | `(langDefPattern| $ctor:str($args:langDefPattern,*)) => do
      let args' ← args.getElems.toList.mapM expandPatternInfo
      let argsTerm ← mkTermList (args'.map (·.term))
      let ctorName := renderSurfaceStringLit ctor.getString
      let surfaceArgs := String.intercalate ", " (args'.map (·.surface))
      let term ← `(Pattern.apply $ctor $argsTerm)
      pure (mkExpandedPattern term s!"{ctorName}({surfaceArgs})")
  | `(langDefPattern| $ctor:ident($args:langDefPattern,*)) => do
      let args' ← args.getElems.toList.mapM expandPatternInfo
      let argsTerm ← mkTermList (args'.map (·.term))
      let ctorName := ctor.getId.toString
      let surfaceArgs := String.intercalate ", " (args'.map (·.surface))
      let term ← `(Pattern.apply $(mkStrTerm ctorName) $argsTerm)
      pure (mkExpandedPattern term s!"{ctorName}({surfaceArgs})")
  | `(langDefPattern| ($inner:langDefPattern)) => do
      let inner' ← expandPatternInfo inner
      pure (mkExpandedPattern inner'.term s!"({inner'.surface})")
  | `(langDefPattern| eval($scope:langDefPattern, $repl:langDefPattern)) => do
      let scope' ← expandPatternInfo scope
      let repl' ← expandPatternInfo repl
      let scopeTerm := scope'.term
      let replTerm := repl'.term
      let term ← `(Pattern.eval $scopeTerm $replTerm)
      pure (mkExpandedPattern term s!"eval({scope'.surface}, {repl'.surface})")
  | `(langDefPattern| (eval $scope:ident $repl:langDefPattern)) => do
      let repl' ← expandPatternInfo repl
      let scopeName := scope.getId.toString
      let scopeTerm ← `(Pattern.fvar $(mkStrTerm scopeName))
      let replTerm := repl'.term
      let term ← `(Pattern.eval $scopeTerm $replTerm)
      pure (mkExpandedPattern term s!"(eval {scopeName} {repl'.surface})")
  | `(langDefPattern| (eval $scope:langDefPattern $repl:langDefPattern)) => do
      let scope' ← expandPatternInfo scope
      let repl' ← expandPatternInfo repl
      let scopeTerm := scope'.term
      let replTerm := repl'.term
      let term ← `(Pattern.eval $scopeTerm $replTerm)
      pure (mkExpandedPattern term s!"(eval {scope'.surface} {repl'.surface})")
  | `(langDefPattern| ^ $binder:ident . $body:langDefPattern) => do
      let body' ← expandPatternInfo body
      let bodyTerm := body'.term
      let binderName := mkStrTerm binder.getId.toString
      let term ← `(Pattern.lambda (some $binderName) $bodyTerm)
      pure (mkExpandedPattern term s!"^{binder.getId.toString}.{body'.surface}")
  | `(langDefPattern| ^ $binder:ident .( $body:langDefPattern )) => do
      let body' ← expandPatternInfo body
      let bodyTerm := body'.term
      let binderName := mkStrTerm binder.getId.toString
      let term ← `(Pattern.lambda (some $binderName) $bodyTerm)
      pure (mkExpandedPattern term s!"^{binder.getId.toString}.({body'.surface})")
  | `(langDefPattern| ^ $binder:ident . ($body:langDefPattern)) => do
      let body' ← expandPatternInfo body
      let bodyTerm := body'.term
      let binderName := mkStrTerm binder.getId.toString
      let term ← `(Pattern.lambda (some $binderName) $bodyTerm)
      pure (mkExpandedPattern term s!"^{binder.getId.toString}.({body'.surface})")
  | `(langDefPattern| ^ $binderAndBody:ident) => do
      let (binderName, bodyName) ← splitCompactBinderIdent binderAndBody.getId
      let bodyTerm ← `(Pattern.fvar $(mkStrTerm bodyName))
      let binderTerm := mkStrTerm binderName
      let term ← `(Pattern.lambda (some $binderTerm) $bodyTerm)
      pure (mkExpandedPattern term s!"^{binderName}.{bodyName}")
  | `(langDefPattern| ^[ $binders:ident,* ] . $body:langDefPattern) => do
      let body' ← expandPatternInfo body
      let binderNames := binders.getElems.toList.map (·.getId.toString)
      let renderedBinders := String.intercalate ", " binderNames
      let bodyTerm := body'.term
      let binderTerms ← binders.getElems.toList.mapM (fun b =>
        pure (mkStrTerm b.getId.toString))
      let binderList ← mkTermList binderTerms
      let term ← `(Pattern.multiLambda $(quote binders.getElems.size) $binderList $bodyTerm)
      pure (mkExpandedPattern term s!"^[{renderedBinders}].{body'.surface}")
  | `(langDefPattern| ^[ $binders:ident,* ] .( $body:langDefPattern )) => do
      let body' ← expandPatternInfo body
      let binderNames := binders.getElems.toList.map (·.getId.toString)
      let renderedBinders := String.intercalate ", " binderNames
      let bodyTerm := body'.term
      let binderTerms ← binders.getElems.toList.mapM (fun b =>
        pure (mkStrTerm b.getId.toString))
      let binderList ← mkTermList binderTerms
      let term ← `(Pattern.multiLambda $(quote binders.getElems.size) $binderList $bodyTerm)
      pure (mkExpandedPattern term s!"^[{renderedBinders}].({body'.surface})")
  | `(langDefPattern| ^[ $binders:ident,* ] . ($body:langDefPattern)) => do
      let body' ← expandPatternInfo body
      let binderNames := binders.getElems.toList.map (·.getId.toString)
      let renderedBinders := String.intercalate ", " binderNames
      let bodyTerm := body'.term
      let binderTerms ← binders.getElems.toList.mapM (fun b =>
        pure (mkStrTerm b.getId.toString))
      let binderList ← mkTermList binderTerms
      let term ← `(Pattern.multiLambda $(quote binders.getElems.size) $binderList $bodyTerm)
      pure (mkExpandedPattern term s!"^[{renderedBinders}].({body'.surface})")
  | `(langDefPattern| { $elems:langDefPattern,* }) => do
      let elems' ← elems.getElems.toList.mapM expandPatternInfo
      let trailingRest? := elems'.reverse.findSome? (·.restName?)
      let concreteElems :=
        match trailingRest? with
        | some _ => elems'.dropLast
        | none => elems'
      if concreteElems.any (fun elem => elem.restName?.isSome) then
        Macro.throwError "collection rest `...rest` may only appear once at the end of a collection pattern"
      let elemsTerm ← mkTermList (concreteElems.map (·.term))
      let surfaceElems := String.intercalate ", " (concreteElems.map (·.surface))
      let term ←
        match trailingRest? with
        | some restName =>
            `(Pattern.collection CollType.hashBag $elemsTerm (some $(mkStrTerm restName)))
        | none =>
            `(Pattern.collection CollType.hashBag $elemsTerm none)
      let surface :=
        match trailingRest? with
        | some restName =>
            if concreteElems.isEmpty then
              "{..." ++ restName ++ "}"
            else
              "{" ++ surfaceElems ++ ", ..." ++ restName ++ "}"
        | none =>
            "{" ++ surfaceElems ++ "}"
      pure (mkExpandedPattern term surface)
  | `(langDefPattern| ($ctor:ident $args:langDefPattern*)) => do
      let argSyntax ← args.toList.mapM (fun arg => splitPrefixPatternArgs ⟨arg⟩)
      let args' ← (flattenLists argSyntax).mapM expandPatternInfo
      let argsTerm ← mkTermList (args'.map (·.term))
      let ctorName := ctor.getId.toString
      let surfaceArgs := String.intercalate " " (args'.map (·.surface))
      let term ← `(Pattern.apply $(mkStrTerm ctorName) $argsTerm)
      pure (mkExpandedPattern term s!"({ctorName} {surfaceArgs})")
  | stx => do
      let args := stx.raw.getArgs
      match args.size with
      | 3 =>
          try
            let restName ← restVarName ⟨args[1]!⟩
            let term ← `(Pattern.collection CollType.hashBag [] (some $(mkStrTerm restName)))
            pure (mkExpandedPattern term ("{..." ++ restName ++ "}"))
          catch _ =>
            Macro.throwErrorAt stx "unsupported pattern syntax"
      | 5 =>
          try
            let elems' ← (sepSyntaxToList args[1]!).mapM (fun s => expandPatternInfo ⟨s⟩)
            let elemsTerm ← mkTermList (elems'.map (·.term))
            let restName ← restVarName ⟨args[3]!⟩
            let surfaceElems := String.intercalate ", " (elems'.map (·.surface))
            let term ← `(Pattern.collection CollType.hashBag $elemsTerm (some $(mkStrTerm restName)))
            pure (mkExpandedPattern term ("{" ++ surfaceElems ++ ", ..." ++ restName ++ "}"))
          catch _ =>
            Macro.throwErrorAt stx "unsupported pattern syntax"
      | _ =>
          Macro.throwErrorAt stx "unsupported pattern syntax"

end

private partial def expandPattern (stx : TSyntax `langDefPattern) : MacroM (TSyntax `term) := do
  return (← expandPatternInfo stx).term

private def expandTypeBinding : TSyntax `langDefTypeBinding → MacroM (TSyntax `term)
  | `(langDefTypeBinding| $nm:ident:$ty:langDefTypeExpr) => do
      let ty' ← expandTypeExpr ty
      `(($(mkStrTerm nm.getId.toString), $ty'))
  | stx => Macro.throwErrorAt stx "unsupported type binding"

private partial def expandPremiseInfo (stx0 : TSyntax `langDefPremise) : MacroM ExpandedPremise := do
  let stx : TSyntax `langDefPremise := ⟨normalizeChoiceSyntax stx0.raw⟩
  match stx with
  | `(langDefPremise| $nm:ident # ... $rest:ident) => do
      let varName := nm.getId.toString
      let restName := rest.getId.toString
      let term ← `(Premise.freshness
          (FreshnessCondition.mk
            $(mkStrTerm varName)
            (Pattern.collection CollType.hashBag [] (some $(mkStrTerm restName)))))
      pure ⟨term, varName ++ " # ..." ++ restName⟩
  | `(langDefPremise| $nm:ident # $rest:langDefRestVar) => do
      let varName := nm.getId.toString
      let restName ← restVarName rest
      let term ← `(Premise.freshness
          (FreshnessCondition.mk
            $(mkStrTerm varName)
            (Pattern.collection CollType.hashBag [] (some $(mkStrTerm restName)))))
      pure ⟨term, varName ++ " # ..." ++ restName⟩
  | `(langDefPremise| $nm:ident # $pat:langDefPattern) => do
      let pat' ← expandPatternInfo pat
      let varName := nm.getId.toString
      let patTerm := pat'.term
      let term ← `(Premise.freshness (FreshnessCondition.mk $(mkStrTerm varName) $patTerm))
      pure ⟨term, s!"{varName} # {pat'.surface}"⟩
  | `(langDefPremise| $lhs:langDefPattern ~> $rhs:langDefPattern) => do
      let lhs' ← expandPatternInfo lhs
      let rhs' ← expandPatternInfo rhs
      let lhsTerm := lhs'.term
      let rhsTerm := rhs'.term
      let term ← `(Premise.congruence $lhsTerm $rhsTerm)
      pure ⟨term, s!"{lhs'.surface} ~> {rhs'.surface}"⟩
  | `(langDefPremise| $rel:ident($args:langDefPattern,*)) => do
      let args' ← args.getElems.toList.mapM expandPatternInfo
      let argsTerm ← mkTermList (args'.map (·.term))
      let relName := rel.getId.toString
      let surfaceArgs := String.intercalate ", " (args'.map (·.surface))
      let term ← `(Premise.relationQuery $(mkStrTerm relName) $argsTerm)
      pure ⟨term, s!"{relName}({surfaceArgs})"⟩
  | `(langDefPremise| $collection:ident.*map(| $param:ident | $body:langDefPremise)) => do
      let body' ← expandPremiseInfo body
      let collectionName := collection.getId.toString
      let paramName := param.getId.toString
      let bodyTerm := body'.term
      let term ← `(Premise.forAll $(mkStrTerm collectionName) $(mkStrTerm paramName) $bodyTerm)
      pure ⟨term, s!"{collectionName}.*map(|{paramName}| {body'.surface})"⟩
  | `(langDefPremise| forAll($collection:ident, $param:ident, $body:langDefPremise)) => do
      let body' ← expandPremiseInfo body
      let collectionName := collection.getId.toString
      let paramName := param.getId.toString
      let bodyTerm := body'.term
      let term ← `(Premise.forAll $(mkStrTerm collectionName) $(mkStrTerm paramName) $bodyTerm)
      pure ⟨term, s!"forAll({collectionName}, {paramName}, {body'.surface})"⟩
  | stx => Macro.throwErrorAt stx "unsupported premise syntax"

private partial def expandPremise (stx : TSyntax `langDefPremise) : MacroM (TSyntax `term) := do
  return (← expandPremiseInfo stx).term

private def expandTypeBindings (ctx : List (TSyntax `langDefTypeBinding)) : MacroM (TSyntax `term) := do
  let ctx' ← ctx.mapM expandTypeBinding
  mkTermList ctx'

private def expandPremisesInfo (premises : List (TSyntax `langDefPremise)) :
    MacroM (List ExpandedPremise) :=
  premises.mapM expandPremiseInfo

private def expandPremises (premises : List (TSyntax `langDefPremise)) : MacroM (TSyntax `term) := do
  let premises' ← expandPremisesInfo premises
  mkTermList (premises'.map (·.term))

private def expandTypeBindingsNode (node : Syntax) : MacroM (TSyntax `term) :=
  expandTypeBindings ((sepSyntaxToList node).map (fun stx => ⟨stx⟩))

private def expandPremisesNode (node : Syntax) : MacroM (TSyntax `term) :=
  expandPremises ((sepSyntaxToList node).map (fun stx => ⟨stx⟩))

private def expandPremisesNodeInfo (node : Syntax) : MacroM (List ExpandedPremise) :=
  expandPremisesInfo ((sepSyntaxToList node).map (fun stx => ⟨stx⟩))

private def tryExpandTypeBindingsNode? (node : Syntax) : MacroM (Option (TSyntax `term)) := do
  try
    return some (← expandTypeBindingsNode node)
  catch _ =>
    return none

private partial def unwrapChoiceSyntax (stx : Syntax) : Syntax :=
  match stx with
  | .node _ `choice args =>
      match args[0]? with
      | some inner => unwrapChoiceSyntax inner
      | none => stx
  | _ => stx

private def expandTermDecl : TSyntax `langDefTermDecl → MacroM (TSyntax `term)
  | `(langDefTermDecl| $label:ident . $params:langDefTermParam,* |- $syns:langDefSyntaxAtom* : $category:ident ; ) => do
      let params' ← params.getElems.toList.mapM expandTermParam
      let synArrays ← syns.toList.mapM expandSyntaxAtom
      let syns' := synArrays.foldl (init := #[]) (fun acc arr => acc ++ arr)
      let paramsTerm ← mkTermList params'
      let synsTerm ← mkTermList syns'.toList
      `(GrammarRule.mk $(mkStrTerm label.getId.toString) $(mkStrTerm category.getId.toString) $paramsTerm $synsTerm)
  | stx => Macro.throwErrorAt stx "unsupported term declaration"

private def mkEquationTerm
    (nm : Syntax)
    (ctxTerm premisesTerm premiseSurfaceTerm lhsTerm rhsTerm lhsSurface rhsSurface : TSyntax `term) :
    MacroM (TSyntax `term) :=
  `(Equation.mk $(mkStrTerm nm.getId.toString)
      $ctxTerm
      $premisesTerm
      $lhsTerm
      $rhsTerm
      $premiseSurfaceTerm
      (some $lhsSurface)
      (some $rhsSurface))

private def mkRewriteTerm
    (nm : Syntax)
    (ctxTerm premisesTerm premiseSurfaceTerm lhsTerm rhsTerm lhsSurface rhsSurface : TSyntax `term) :
    MacroM (TSyntax `term) :=
  `(RewriteRule.mk $(mkStrTerm nm.getId.toString)
      $ctxTerm
      $premisesTerm
      $lhsTerm
      $rhsTerm
      $premiseSurfaceTerm
      (some $lhsSurface)
      (some $rhsSurface))

private def expandEquationDecl (stx : TSyntax `langDefEquationDecl) : MacroM (TSyntax `term) := do
  let raw := unwrapChoiceSyntax stx.raw
  let args := raw.getArgs
  match args.size with
  | 8 =>
      let ctxOrPremisesNode := args[2]!
      let ctxTerm? ← tryExpandTypeBindingsNode? ctxOrPremisesNode
      let premisesInfo ←
        match ctxTerm? with
        | some _ => pure []
        | none => expandPremisesNodeInfo ctxOrPremisesNode
      let premisesTerm ← mkTermList (premisesInfo.map (·.term))
      let premiseSurfaceTerm ← mkTermList (premisesInfo.map (fun p => mkStrTerm p.surface))
      let ctxTerm ←
        match ctxTerm? with
        | some term => pure term
        | none => `([])
      let lhs' ← expandPatternInfo ⟨args[4]!⟩
      let rhs' ← expandPatternInfo ⟨args[6]!⟩
      mkEquationTerm args[0]! ctxTerm premisesTerm premiseSurfaceTerm lhs'.term rhs'.term
        (mkStrTerm lhs'.surface) (mkStrTerm rhs'.surface)
  | 10 =>
      let ctxTerm ← expandTypeBindingsNode args[2]!
      let premisesInfo ← expandPremisesNodeInfo args[4]!
      let premisesTerm ← mkTermList (premisesInfo.map (·.term))
      let premiseSurfaceTerm ← mkTermList (premisesInfo.map (fun p => mkStrTerm p.surface))
      let lhs' ← expandPatternInfo ⟨args[6]!⟩
      let rhs' ← expandPatternInfo ⟨args[8]!⟩
      mkEquationTerm args[0]! ctxTerm premisesTerm premiseSurfaceTerm lhs'.term rhs'.term
        (mkStrTerm lhs'.surface) (mkStrTerm rhs'.surface)
  | _ =>
      Macro.throwErrorAt raw "unsupported equation declaration"

private def expandRewriteDecl (stx : TSyntax `langDefRewriteDecl) : MacroM (TSyntax `term) := do
  let raw := unwrapChoiceSyntax stx.raw
  let args := raw.getArgs
  match args.size with
  | 8 =>
      let ctxOrPremisesNode := args[2]!
      let ctxTerm? ← tryExpandTypeBindingsNode? ctxOrPremisesNode
      let premisesInfo ←
        match ctxTerm? with
        | some _ => pure []
        | none => expandPremisesNodeInfo ctxOrPremisesNode
      let premisesTerm ← mkTermList (premisesInfo.map (·.term))
      let premiseSurfaceTerm ← mkTermList (premisesInfo.map (fun p => mkStrTerm p.surface))
      let ctxTerm ←
        match ctxTerm? with
        | some term => pure term
        | none => `([])
      let lhs' ← expandPatternInfo ⟨args[4]!⟩
      let rhs' ← expandPatternInfo ⟨args[6]!⟩
      mkRewriteTerm args[0]! ctxTerm premisesTerm premiseSurfaceTerm lhs'.term rhs'.term
        (mkStrTerm lhs'.surface) (mkStrTerm rhs'.surface)
  | 10 =>
      let ctxTerm ← expandTypeBindingsNode args[2]!
      let premisesInfo ← expandPremisesNodeInfo args[4]!
      let premisesTerm ← mkTermList (premisesInfo.map (·.term))
      let premiseSurfaceTerm ← mkTermList (premisesInfo.map (fun p => mkStrTerm p.surface))
      let lhs' ← expandPatternInfo ⟨args[6]!⟩
      let rhs' ← expandPatternInfo ⟨args[8]!⟩
      mkRewriteTerm args[0]! ctxTerm premisesTerm premiseSurfaceTerm lhs'.term rhs'.term
        (mkStrTerm lhs'.surface) (mkStrTerm rhs'.surface)
  | _ =>
      Macro.throwErrorAt raw "unsupported rewrite declaration"

private def expandLogicDecl (stx : TSyntax `langDefLogicDecl) : MacroM (TSyntax `term) := do
  let args := stx.raw.getArgs
  match args.size with
  | 6 =>
      let argTypes' ← ((@Syntax.SepArray.mk "," args[3]!.getArgs) : Array Syntax).toList.mapM (fun ty => expandTypeExpr ⟨ty⟩)
      let argTypesTerm ← mkTermList argTypes'
      `(LogicDecl.relation (LogicRelationDecl.mk $(mkStrTerm args[1]!.getId.toString) $argTypesTerm))
  | 3 =>
      let txt : TSyntax `str := ⟨args[1]!⟩
      `(LogicDecl.ruleText $txt)
  | _ =>
      Macro.throwErrorAt stx "unsupported logic declaration"

private def expandOracleDecl (stx : TSyntax `langDefOracleDecl) : MacroM (TSyntax `term) := do
  let args := stx.raw.getArgs
  match args.size with
  | 8 =>
      let argTypes' ← ((@Syntax.SepArray.mk "," args[3]!.getArgs) : Array Syntax).toList.mapM (fun ty => expandTypeExpr ⟨ty⟩)
      let argTypesTerm ← mkTermList argTypes'
      let resultType' ← expandTypeExpr ⟨args[6]!⟩
      `(OracleDecl.mk $(mkStrTerm args[1]!.getId.toString) $argTypesTerm $resultType')
  | _ =>
      Macro.throwErrorAt stx "unsupported oracle declaration"

macro
  "languageDef!" "{"
  "name" ":" langName:term
  "types" "{" typeDecls:langDefTypeDecl* "}"
  "terms" "{" termDecls:langDefTermDecl* "}"
  "equations" "{" eqs:langDefEquationDecl* "}"
  "rewrites" "{" rws:langDefRewriteDecl* "}"
  "logic" "{" lgs:langDefLogicDecl* "}"
  "oracles" "{" ors:langDefOracleDecl* "}"
  "congruenceCollections" "{" colls:ident,* "}"
  "}" : term => do
    let typeDecls' ← typeDecls.toList.mapM expandTypeDecl
    let termDecls' ← termDecls.toList.mapM expandTermDecl
    let eqDecls' ← eqs.toList.mapM expandEquationDecl
    let rwDecls' ← rws.toList.mapM expandRewriteDecl
    let logicDecls' ← lgs.toList.mapM expandLogicDecl
    let oracleDecls' ← ors.toList.mapM expandOracleDecl
    let collDecls' ← colls.getElems.toList.mapM (fun stx => do
      let ct ← resolveCollName stx
      pure (collTerm ct))
    let typeDeclsTerm ← mkTermList typeDecls'
    let termDeclsTerm ← mkTermList termDecls'
    let eqDeclsTerm ← mkTermList eqDecls'
    let rwDeclsTerm ← mkTermList rwDecls'
    let logicDeclsTerm ← mkTermList logicDecls'
    let oracleDeclsTerm ← mkTermList oracleDecls'
    let collDeclsTerm ← mkTermList collDecls'
    `(LanguageDef.mk
        $langName
        $typeDeclsTerm
        $termDeclsTerm
        $eqDeclsTerm
        $rwDeclsTerm
        $collDeclsTerm
        $logicDeclsTerm
        $oracleDeclsTerm)

macro_rules
  | `(T! $s:str) => `(SyntaxItem.terminal $s)
  | `(N! $s:str) => `(SyntaxItem.nonTerminal $s)
  | `(Sep! $s:str) => `(SyntaxItem.separator $s)
  | `(Delim! $l:str $r:str) => `(SyntaxItem.delimiter $l $r)
  | `(P! $nm:str : $ty:str) => `(TermParam.simple $nm (TypeExpr.base $ty))
  | `(AParam! $nm:str : $ty:str) => `(TermParam.abstraction $nm (TypeExpr.base $ty))
  | `(MParam! $nm:str : $ty:str) => `(TermParam.multiAbstraction $nm (TypeExpr.base $ty))
  | `(Var! $nm:str) => `(Pattern.fvar $nm)
  | `(App! $ctor:str [ $args,* ]) => `(Pattern.apply $ctor [ $args,* ])
  | `(Rel! $rel:str [ $args,* ]) => `(Premise.relationQuery $rel [ $args,* ])
  | `(relation $relName:str [ $args,* ]) =>
      `(LogicDecl.relation (LogicRelationDecl.mk $relName [ $args,* ]))
  | `(rule $txt:str) => `(LogicDecl.ruleText $txt)
  | `(external $oracleName:str [ $args,* ] -> $result:term) =>
      `(OracleDecl.mk $oracleName [ $args,* ] $result)
  | `(languageDef! {
      name : $langName,
      types : $tys,
      terms : $tmRules,
      equations : $eqns,
      rewrites : $rws,
      logic : $lgs,
      oracles : $ors,
      congruenceCollections : $ccs
    }) =>
      `(LanguageDef.mk $langName $tys $tmRules $eqns $rws $ccs $lgs $ors)

/-! ## Generic Builders -/

def gRule (label category : String) (params : List TermParam) (syntaxPattern : List SyntaxItem) :
    GrammarRule :=
  { label := label
    category := category
    params := params
    syntaxPattern := syntaxPattern }

def rwRule
    (ruleName : String)
    (typeContext : List (String × TypeExpr))
    (premises : List Premise)
    (left right : Pattern) : RewriteRule :=
  RewriteRule.mk ruleName typeContext premises left right [] none none

def mkLang
    (langName : String)
    (typeDecls : List TypeDecl)
    (termRules : List GrammarRule)
    (rewriteRules : List RewriteRule)
    (eqRules : List Equation := [])
    (congCollections : List CollType := []) : LanguageDef :=
  LanguageDef.mk
    langName
    typeDecls
    termRules
    eqRules
    rewriteRules
    congCollections
    []
    []

end Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
