import Init.Data.String.Lemmas.Pattern.Find.String
import Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
import Mettapedia.OSLF.MeTTaIL.Export
import Mettapedia.OSLF.MeTTaIL.Canonical
import Mettapedia.OSLF.MeTTaIL.CoreSyntaxBridge
import Mettapedia.GSLT.LanguageDef.LogicExtension
import Mettapedia.GSLT.LanguageDef.OracleExtension

namespace Mettapedia.OSLF.MeTTaIL.LanguageDefDSLTests

attribute [local cbv_eval] Std.Iter.toList_eq_match_step Std.Iter.fold_eq_match_step
attribute [local cbv_opaque] Std.Shrink.deflate Std.Shrink.inflate
attribute [local cbv_eval] Std.Shrink.inflate_deflate

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

local macro "certify_literal_replace" : tactic => `(tactic| (
  repeat (cbv; simp (config := { failIfUnchanged := true }) only [Std.Shrink.inflate_deflate])
  cbv))

@[local cbv_eval]
private theorem literal_new_backslash (replacement : String) :
    "new".replace "\\" replacement = "new" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_new_quote (replacement : String) :
    "new".replace "\"" replacement = "new" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_leftParen_backslash (replacement : String) :
    "(".replace "\\" replacement = "(" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_leftParen_quote (replacement : String) :
    "(".replace "\"" replacement = "(" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_rightParen_backslash (replacement : String) :
    ")".replace "\\" replacement = ")" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_rightParen_quote (replacement : String) :
    ")".replace "\"" replacement = ")" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_comma_backslash (replacement : String) :
    ",".replace "\\" replacement = "," := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_comma_quote (replacement : String) :
    ",".replace "\"" replacement = "," := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_keep_backslash (replacement : String) :
    "keep".replace "\\" replacement = "keep" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_keep_quote (replacement : String) :
    "keep".replace "\"" replacement = "keep" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_scope_backslash (replacement : String) :
    "scope".replace "\\" replacement = "scope" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_scope_quote (replacement : String) :
    "scope".replace "\"" replacement = "scope" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_leftBrace_backslash (replacement : String) :
    "{".replace "\\" replacement = "{" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_leftBrace_quote (replacement : String) :
    "{".replace "\"" replacement = "{" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_rightBrace_backslash (replacement : String) :
    "}".replace "\\" replacement = "}" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_rightBrace_quote (replacement : String) :
    "}".replace "\"" replacement = "}" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_bar_backslash (replacement : String) :
    "|".replace "\\" replacement = "|" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_bar_quote (replacement : String) :
    "|".replace "\"" replacement = "|" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_for_backslash (replacement : String) :
    "for".replace "\\" replacement = "for" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_for_quote (replacement : String) :
    "for".replace "\"" replacement = "for" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_leftArrow_backslash (replacement : String) :
    "<-".replace "\\" replacement = "<-" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_leftArrow_quote (replacement : String) :
    "<-".replace "\"" replacement = "<-" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_maybe_backslash (replacement : String) :
    "maybe".replace "\\" replacement = "maybe" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_maybe_quote (replacement : String) :
    "maybe".replace "\"" replacement = "maybe" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_bang_backslash (replacement : String) :
    "!".replace "\\" replacement = "!" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_bang_quote (replacement : String) :
    "!".replace "\"" replacement = "!" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_in_backslash (replacement : String) :
    "in".replace "\\" replacement = "in" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_in_quote (replacement : String) :
    "in".replace "\"" replacement = "in" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_dot_backslash (replacement : String) :
    ".".replace "\\" replacement = "." := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_dot_quote (replacement : String) :
    ".".replace "\"" replacement = "." := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_at_backslash (replacement : String) :
    "@".replace "\\" replacement = "@" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_at_quote (replacement : String) :
    "@".replace "\"" replacement = "@" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_pair_backslash (replacement : String) :
    "pair".replace "\\" replacement = "pair" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_pair_quote (replacement : String) :
    "pair".replace "\"" replacement = "pair" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_int_backslash (replacement : String) :
    "int".replace "\\" replacement = "int" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_int_quote (replacement : String) :
    "int".replace "\"" replacement = "int" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_plus_backslash (replacement : String) :
    "+".replace "\\" replacement = "+" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_plus_quote (replacement : String) :
    "+".replace "\"" replacement = "+" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_rand_backslash (replacement : String) :
    "rand".replace "\\" replacement = "rand" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_rand_quote (replacement : String) :
    "rand".replace "\"" replacement = "rand" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_plain_backslash (replacement : String) :
    "plain".replace "\\" replacement = "plain" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_plain_quote (replacement : String) :
    "plain".replace "\"" replacement = "plain" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_keepCtor_backslash (replacement : String) :
    "Keep".replace "\\" replacement = "Keep" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_keepCtor_quote (replacement : String) :
    "Keep".replace "\"" replacement = "Keep" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_scopeCtor_backslash (replacement : String) :
    "Scope".replace "\\" replacement = "Scope" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_scopeCtor_quote (replacement : String) :
    "Scope".replace "\"" replacement = "Scope" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_PNew_operator (replacement : String) :
    "PNew".replace "⊛" replacement = "PNew" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_Keep_operator (replacement : String) :
    "Keep".replace "⊛" replacement = "Keep" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_Scope_operator (replacement : String) :
    "Scope".replace "⊛" replacement = "Scope" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_PPar_operator (replacement : String) :
    "PPar".replace "⊛" replacement = "PPar" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_PInputs_operator (replacement : String) :
    "PInputs".replace "⊛" replacement = "PInputs" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_PMaybe_operator (replacement : String) :
    "PMaybe".replace "⊛" replacement = "PMaybe" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_POutput_operator (replacement : String) :
    "POutput".replace "⊛" replacement = "POutput" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_NQuote_operator (replacement : String) :
    "NQuote".replace "⊛" replacement = "NQuote" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_Pair_operator (replacement : String) :
    "Pair".replace "⊛" replacement = "Pair" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_eval_operator (replacement : String) :
    "eval".replace "⊛" replacement = "eval" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_CastInt_operator (replacement : String) :
    "CastInt".replace "⊛" replacement = "CastInt" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_Add_operator (replacement : String) :
    "Add".replace "⊛" replacement = "Add" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_Rand_operator (replacement : String) :
    "Rand".replace "⊛" replacement = "Rand" := by
  certify_literal_replace

@[local cbv_eval]
private theorem literal_Plain_operator (replacement : String) :
    "Plain".replace "⊛" replacement = "Plain" := by
  certify_literal_replace

attribute [local cbv_opaque] String.replace HAppend.hAppend String.toList


open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Canonical
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open Mettapedia.GSLT.LanguageDef.LogicExtension
open Mettapedia.GSLT.LanguageDef.OracleExtension
open scoped Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

/-- Positive smoke example: the five core blocks parse into one `LanguageDef`,
and binder names survive on the relevant `TermParam`s. -/
def smokeLang : LanguageDef :=
  languageDef! {
    name : "SmokeLang"
    types {
      Expr
      Env
      Result
      ![raw] as Sym
    }
    terms {
      SymLeaf . tok:Sym |- tok : Expr;
      Lam . ^ x . body : [Expr -> Expr] |- "lam" body : Expr;
      MultiLam . ^[x, y]. body : [Expr * -> Expr] |- "mlam" body : Expr;
    }
    equations {
      EqSym . tok:Sym |- SymLeaf(tok) = SymLeaf(tok);
    }
    rewrites {
      Beta . env:Env | knownSymbol(SymLeaf(tok)) |- Lam(SymLeaf(tok)) ~> SymLeaf(tok);
    }
  }

private def smokeRelation : LogicRelationDecl :=
  LogicRelationDecl.mk "knownSymbol" [.base "Expr"]

def smokeLogic : AdmittedProgram smokeLang :=
  ⟨[LogicDeclaration.relation smokeRelation], by decide⟩

def smokeOracles : AdmittedLibrary smokeLang :=
  ⟨[OracleDecl.mk "evalExpr"
      [.base "Expr", .base "Env"] (.base "Result")], by decide⟩

private def nth? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => nth? xs n

private def binderNamesAt (lang : LanguageDef) (termIdx paramIdx : Nat) : List String :=
  match nth? lang.terms termIdx with
  | some g =>
      match nth? g.params paramIdx with
      | some param => TermParam.binderNames param
      | none => []
  | none => []

private def rewriteShape (lang : LanguageDef) : Nat × Nat :=
  match nth? lang.rewrites 0 with
  | some rw => (rw.typeContext.length, rw.premises.length)
  | none => (0, 0)

example : smokeLang.equations.length = 1 := rfl
example : smokeLang.rewrites.length = 1 := rfl
example : smokeLogic.1.length = 1 := rfl
example : smokeOracles.1.length = 1 := rfl
example : binderNamesAt smokeLang 1 0 = ["x"] := rfl
example : binderNamesAt smokeLang 2 0 = ["x", "y"] := rfl
example : rewriteShape smokeLang = (1, 1) := rfl

/-- Positive smoke example: compact Rust-style single-binder authoring forms
    like `^x.p:[...]` and `^x.P` parse directly rather than requiring spaced
    fallback spellings. -/
def compactBinderLang : LanguageDef :=
  languageDef! {
    name : "CompactBinderLang"
    types {
      Proc
      Name
    }
    terms {
      PNew . ^x.p:[Name -> Proc] |- "new" "(" x "," p ")" : Proc;
    }
    equations {
      Scope . |- PNew(^x.P) = PNew(^x.P);
    }
    rewrites { }
  }

example : binderNamesAt compactBinderLang 0 0 = ["x"] := rfl

private def compactBinderHasLambdaBody : Bool :=
  match compactBinderLang.equations.get ⟨0, by decide +kernel⟩ with
  | { left := .apply "PNew" [.lambda (some "x") (.fvar "P")], .. } => true
  | _ => false

private def hasSubstring (needle haystack : String) : Bool :=
  haystack.contains needle

private theorem contains_concatenated (left needle right : String) :
    (left ++ needle ++ right).contains needle = true := by
  apply String.contains_string_iff.mpr
  simp only [String.toList_append]
  exact List.infix_append _ _ _

local elab "certify_literal_infix" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isAppOfArity ``Eq 3 do
    throwError "Expected a literal string containment equality"
  let args := target.getAppArgs
  unless args[2]!.isConstOf ``Bool.true do
    throwError "Constructive containment requires a positive conclusion"
  let strings := args[1]!.getAppArgs.filterMap fun
    | .lit (.strVal value) => some value
    | _ => none
  unless strings.size == 2 do
    throwError "Expected two literal string arguments"
  let haystack := strings[0]!
  let needle := strings[1]!
  let parts := haystack.splitOn needle
  unless parts.length ≥ 2 do
    throwError "No literal containment witness found"
  let hay : Lean.TSyntax `term := ⟨Lean.Syntax.mkStrLit haystack⟩
  let pat : Lean.TSyntax `term := ⟨Lean.Syntax.mkStrLit needle⟩
  let left : Lean.TSyntax `term := ⟨Lean.Syntax.mkStrLit parts.head!⟩
  let right : Lean.TSyntax `term := ⟨Lean.Syntax.mkStrLit (String.intercalate needle parts.tail!)⟩
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    (have split : $hay = $left ++ $pat ++ $right := rfl
     exact Eq.mpr (congrArg (fun text : String => text.contains $pat = true) split)
       (contains_concatenated $left $pat $right))))

local macro "certify_rendered_infix" renderer:ident : tactic => `(tactic| (
  simp only [hasSubstring, ($renderer)]
  first
  | certify_literal_infix
  | (simp only [String.contains_string_eq_internal]; decide +kernel)))

example :
    compactBinderHasLambdaBody = true := by
  decide +kernel

private theorem rendered_compactBinder :
    Export.renderLanguageWithUserSyntax compactBinderLang =
      "language! {\n    name: CompactBinderLang,\n\n    types {\n        Proc\n        Name\n    },\n\n    terms {\n        PNew . ^x.p:[Name -> Proc] |- \"new\" \"(\" x \",\" p \")\" : Proc;\n    },\n\n    equations {\n        Scope . |- (PNew ^x.P) = (PNew ^x.P);\n    },\n\n    rewrites {    },\n}" := by
  cbv

example :
    hasSubstring "PNew . ^x.p:[Name -> Proc] |- \"new\" \"(\" x \",\" p \")\" : Proc;"
      (Export.renderLanguageWithUserSyntax compactBinderLang) = true := by
  certify_rendered_infix rendered_compactBinder

example :
    hasSubstring "Scope . |- (PNew ^x.P) = (PNew ^x.P);"
      (Export.renderLanguageWithUserSyntax compactBinderLang) = true := by
  certify_rendered_infix rendered_compactBinder

/-- Positive smoke example: uppercase metavariables remain metavariables, while
    authored binder/rest spellings are preserved for export. -/
def authoredPatternLang : LanguageDef :=
  languageDef! {
    name : "AuthoredPatternLang"
    types {
      Proc
    }
    terms {
      Keep . p:Proc |- "keep" p : Proc;
      Scope . p:Proc |- "scope" p : Proc;
    }
    equations { }
    rewrites {
      PreserveSyntax . | X # ... rest |- Scope(^ x . Keep(X), {X, ... rest}) ~> Scope(^ y . Keep(X), {X});
    }
  }

private def firstRewrite : RewriteRule :=
  authoredPatternLang.rewrites.get ⟨0, by decide +kernel⟩

private def isError {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

private def hasValidationMessage (needle : String) (errs : List ValidationError) : Bool :=
  errs.any (fun err => err.message.contains needle)

private def firstRewriteFreshnessOk : Bool :=
  match firstRewrite.premises with
  | [.freshness fc] =>
      decide (fc.varName = "X") &&
      decide (fc.term = .collection .hashBag [] (some "rest"))
  | _ => false

example :
    firstRewrite.left =
      .apply "Scope"
        [ .lambda (some "x") (.apply "Keep" [.fvar "X"])
        , .collection .hashBag [.fvar "X"] (some "rest") ] := by
  decide +kernel
example : firstRewriteFreshnessOk = true := by
  decide +kernel
-- Linearized string fields removed: Pattern.lambda now carries binder names
-- structurally, so export uses renderPattern directly.
private def firstRewriteHasBinderX : Bool :=
  match firstRewrite.left with
  | .apply "Scope" [.lambda (some binder) _, _] => binder == "x"
  | _ => false

example : firstRewriteHasBinderX = true := by
  decide +kernel
private theorem rendered_authoredPattern :
    Export.renderLanguage authoredPatternLang =
      "language! {\n    name: AuthoredPatternLang,\n\n    types {\n        Proc\n    },\n\n    terms {\n        Keep . p:Proc |- \"Keep\" \"(\" p \")\" : Proc;\n        Scope . p:Proc |- \"Scope\" \"(\" p \")\" : Proc;\n    },\n\n    equations {    },\n\n    rewrites {\n        PreserveSyntax . | X # ...rest |- (Scope ^x.(Keep X) {X, ...rest}) ~> (Scope ^y.(Keep X) {X});\n    },\n}" := by
  cbv

example : hasSubstring "^x.(Keep X)" (Export.renderLanguage authoredPatternLang) = true := by
  certify_rendered_infix rendered_authoredPattern
example : hasSubstring "X # ...rest" (Export.renderLanguage authoredPatternLang) = true := by
  certify_rendered_infix rendered_authoredPattern
example : isError (CoreSyntaxBridge.specToCoreLanguage authoredPatternLang) = true := by
  decide +kernel

/-- Positive smoke example: quantified premises now parse, but core lowering
    rejects them explicitly rather than erasing them. -/
def forAllLang : LanguageDef :=
  languageDef! {
    name : "ForAllLang"
    types {
      Proc
    }
    terms {
      Keep . p:Proc |- "keep" p : Proc;
    }
    equations { }
    rewrites {
      Quantified . | forAll(xs, x, seen(x)) |- Keep(x) ~> Keep(x);
    }
  }

example : isError (CoreSyntaxBridge.specToCoreLanguage forAllLang) = true := by
  decide +kernel
private theorem rendered_forAll :
    Export.renderLanguage forAllLang =
      "language! {\n    name: ForAllLang,\n\n    types {\n        Proc\n    },\n\n    terms {\n        Keep . p:Proc |- \"Keep\" \"(\" p \")\" : Proc;\n    },\n\n    equations {    },\n\n    rewrites {\n        Quantified . | forAll(xs, x, seen(x)) |- (Keep x) ~> (Keep x);\n    },\n}" := by
  cbv

example : hasSubstring "forAll(xs, x, seen(x))" (Export.renderLanguage forAllLang) = true := by
  certify_rendered_infix rendered_forAll

/-- Positive smoke example: Rust-style metasyntax operators parse into the
    single Lean `LanguageDef`, export faithfully, and are rejected by the flat
    core bridge rather than silently flattened. -/
def syntaxOpsLang : LanguageDef :=
  languageDef! {
    name : "SyntaxOpsLang"
    types {
      Proc
      Name
    }
    terms {
      PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
      PInputs . ns:Vec(Name), xs:Vec(Name), p:Proc |- "for" "(" *zip(ns, xs).*map(|n, x| x "<-" n).*sep(",") ")" "{" p "}" : Proc;
      PMaybe . x:Name, p:Proc |- "maybe" "(" *opt(x) ")" "{" p "}" : Proc;
    }
    equations { }
    rewrites { }
  }

private def firstSyntaxRule : GrammarRule :=
  syntaxOpsLang.terms.get ⟨0, by decide +kernel⟩

private def secondSyntaxRule : GrammarRule :=
  syntaxOpsLang.terms.get ⟨1, by decide +kernel⟩

private def thirdSyntaxRule : GrammarRule :=
  syntaxOpsLang.terms.get ⟨2, by decide +kernel⟩

private def firstSyntaxShapeOk : Bool :=
  match firstSyntaxRule.syntaxPattern with
  | [.terminal "{", .op (.sep "ps" "|" none), .terminal "}"] => true
  | _ => false

private def secondSyntaxShapeOk : Bool :=
  match secondSyntaxRule.syntaxPattern with
  | [.terminal "for", .terminal "(", .op (.sep "__chain__" "," (some (.map (.zip "ns" "xs") ["n", "x"] _))), .terminal ")", .terminal "{", .nonTerminal "p", .terminal "}"] => true
  | _ => false

private def thirdSyntaxShapeOk : Bool :=
  match thirdSyntaxRule.syntaxPattern with
  | [.terminal "maybe", .terminal "(", .op (.opt [.nonTerminal "x"]), .terminal ")", .terminal "{", .nonTerminal "p", .terminal "}"] => true
  | _ => false

example : firstSyntaxShapeOk = true := by
  decide +kernel

example : secondSyntaxShapeOk = true := by
  decide +kernel

example : thirdSyntaxShapeOk = true := by
  decide +kernel

private theorem rendered_syntaxOps :
    Export.renderLanguageWithUserSyntax syntaxOpsLang =
      "language! {\n    name: SyntaxOpsLang,\n\n    types {\n        Proc\n        Name\n    },\n\n    terms {\n        PPar . ps:HashBag(Proc) |- \"{\" ps.*sep(\"|\") \"}\" : Proc;\n        PInputs . ns:Vec(Name), xs:Vec(Name), p:Proc |- \"for\" \"(\" *zip(ns, xs).*map(|n, x| x \"<-\" n).*sep(\",\") \")\" \"{\" p \"}\" : Proc;\n        PMaybe . x:Name, p:Proc |- \"maybe\" \"(\" *opt(x) \")\" \"{\" p \"}\" : Proc;\n    },\n\n    equations {    },\n\n    rewrites {    },\n}" := by
  cbv

example : hasSubstring "ps.*sep(\"|\")" (Export.renderLanguageWithUserSyntax syntaxOpsLang) = true := by
  certify_rendered_infix rendered_syntaxOps
example : hasSubstring "*zip(ns, xs).*map(|n, x| x \"<-\" n).*sep(\",\")" (Export.renderLanguageWithUserSyntax syntaxOpsLang) = true := by
  certify_rendered_infix rendered_syntaxOps
example : hasSubstring "*opt(x)" (Export.renderLanguageWithUserSyntax syntaxOpsLang) = true := by
  certify_rendered_infix rendered_syntaxOps
example : isError (CoreSyntaxBridge.specToCoreLanguage syntaxOpsLang) = true := by
  decide +kernel

/-- Positive smoke example: rule-side Rust-style pattern operators and mapped
    freshness sugar parse into structured `Pattern` / `Premise` forms, export
    faithfully through stored source text, and are rejected explicitly by the
    flat core bridge. -/
def rulePatternOpsLang : LanguageDef :=
  languageDef! {
    name : "RulePatternOpsLang"
    types {
      Proc
      Name
    }
    terms {
      PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
      POutput . n:Name, q:Proc |- n "!" "(" q ")" : Proc;
      PInputs . ns:Vec(Name), cont:Proc |- "in" "(" ns ")" "." "{" cont "}" : Proc;
      NQuote . p:Proc |- "@" "(" p ")" : Name;
      PNew . ^[xs].p:[Name* -> Proc] |- "new" "(" xs.*sep(",") ")" "in" "{" p "}" : Proc;
    }
    equations {
      Extrude . | forAll(xs, x, x # ...rest) |- PPar({PNew(^[xs].p), ...rest}) = PNew(^[xs].PPar({p, ...rest}));
    }
    rewrites {
      Comm . |- PPar({PInputs(ns, cont), *zip(ns, qs).*map(|n, q| POutput(n, q)), ...rest})
        ~> PPar({eval(cont, qs.*map(|q| NQuote(q))), ...rest});
    }
  }

private def extrudeEq : Equation :=
  rulePatternOpsLang.equations.get ⟨0, by decide +kernel⟩

private def commRw : RewriteRule :=
  rulePatternOpsLang.rewrites.get ⟨0, by decide +kernel⟩

private def extrudePremiseIsForAll : Bool :=
  match extrudeEq.premises with
  | [.forAll "xs" "x" (.freshness fc)] =>
      fc.varName == "x" && fc.term == .collection .hashBag [] (some "rest")
  | _ => false

private def commLeftHasZipMap : Bool :=
  match commRw.left with
  | .apply "PPar" [.collection .hashBag
      [ .apply "PInputs" [_, _]
      , mapped ] (some "rest")] =>
        match Pattern.mapArgs? mapped with
        | some (source, ["n", "q"], body) =>
            match Pattern.zipArgs? source, body with
            | some (.fvar "ns", .fvar "qs"), .apply "POutput" [.fvar "n", .fvar "q"] => true
            | _, _ => false
        | _ => false
  | _ => false

private def commRightHasEvalMap : Bool :=
  match commRw.right with
  | .apply "PPar" [.collection .hashBag [evalPat] (some "rest")] =>
      match Pattern.evalArgs? evalPat with
      | some (.fvar "cont", mapped) =>
          match Pattern.mapArgs? mapped with
          | some (.fvar "qs", ["q"], .apply "NQuote" [.fvar "q"]) => true
          | _ => false
      | _ => false
  | _ => false

example : extrudePremiseIsForAll = true := by
  decide +kernel

example : commLeftHasZipMap = true := by
  decide +kernel

example : commRightHasEvalMap = true := by
  decide +kernel

private theorem rendered_rulePatternOps :
    Export.renderLanguageWithUserSyntax rulePatternOpsLang =
      "language! {\n    name: RulePatternOpsLang,\n\n    types {\n        Proc\n        Name\n    },\n\n    terms {\n        PPar . ps:HashBag(Proc) |- \"{\" ps.*sep(\"|\") \"}\" : Proc;\n        POutput . n:Name, q:Proc |- n \"!\" \"(\" q \")\" : Proc;\n        PInputs . ns:Vec(Name), cont:Proc |- \"in\" \"(\" ns \")\" \".\" \"{\" cont \"}\" : Proc;\n        NQuote . p:Proc |- \"@\" \"(\" p \")\" : Name;\n        PNew . ^[xs].p:[Name* -> Proc] |- \"new\" \"(\" xs.*sep(\",\") \")\" \"in\" \"{\" p \"}\" : Proc;\n    },\n\n    equations {\n        Extrude . | forAll(xs, x, x # ...rest) |- (PPar {(PNew ^[xs].p), ...rest}) = (PNew ^[xs].(PPar {p, ...rest}));\n    },\n\n    rewrites {\n        Comm . |- (PPar {(PInputs ns cont), *zip(ns, qs).*map(|n, q| (POutput n q)), ...rest}) ~> (PPar {(eval cont qs.*map(|q| (NQuote q))), ...rest});\n    },\n}" := by
  cbv

example :
    hasSubstring
        "Extrude . | forAll(xs, x, x # ...rest) |- (PPar {(PNew ^[xs].p), ...rest}) = (PNew ^[xs].(PPar {p, ...rest}));"
        (Export.renderLanguageWithUserSyntax rulePatternOpsLang) = true := by
  certify_rendered_infix rendered_rulePatternOps

example :
    hasSubstring
        "Comm . |- (PPar {(PInputs ns cont), *zip(ns, qs).*map(|n, q| (POutput n q)), ...rest}) ~> (PPar {(eval cont qs.*map(|q| (NQuote q))), ...rest});"
        (Export.renderLanguageWithUserSyntax rulePatternOpsLang) = true := by
  certify_rendered_infix rendered_rulePatternOps

example : isError (CoreSyntaxBridge.specToCoreLanguage rulePatternOpsLang) = true := by
  decide +kernel

/-- Syntax-sugar smoke example: keep mapped-freshness sugar and prefix-style
    pattern forms alive as authored syntax, even when canonical RhoCalc uses the
    more stable structural spelling today. -/
def ruleSyntaxSugarLang : LanguageDef :=
  languageDef! {
    name : "RuleSyntaxSugarLang"
    types {
      Proc
    }
    terms {
      Pair . a:Proc, b:Proc |- "pair" "(" a "," b ")" : Proc;
    }
    equations {
      FreshMap . xs.*map(|x| x # ...rest) |- (Pair A B) = (Pair A B);
    }
    rewrites {
      EvalSugar . |- eval(A, B) ~> eval(A, B);
    }
  }

private def sugarEq : Equation :=
  ruleSyntaxSugarLang.equations.get ⟨0, by decide +kernel⟩

private def sugarRw : RewriteRule :=
  ruleSyntaxSugarLang.rewrites.get ⟨0, by decide +kernel⟩

private def sugarPremiseIsForAll : Bool :=
  match sugarEq.premises with
  | [.forAll "xs" "x" (.freshness fc)] =>
      fc.varName == "x" && fc.term == .collection .hashBag [] (some "rest")
  | _ => false

private def sugarEqUsesPrefixApply : Bool :=
  match sugarEq.left, sugarEq.right with
  | .apply "Pair" [.fvar "A", .fvar "B"], .apply "Pair" [.fvar "A", .fvar "B"] => true
  | _, _ => false

private def sugarRwUsesPrefixEval : Bool :=
  match sugarRw.left, sugarRw.right with
  | lhs, rhs =>
      match Pattern.evalArgs? lhs, Pattern.evalArgs? rhs with
      | some (.fvar "A", .fvar "B"), some (.fvar "A", .fvar "B") => true
      | _, _ => false

example : sugarPremiseIsForAll = true := by
  decide +kernel

example : sugarEqUsesPrefixApply = true := by
  decide +kernel

example : sugarRwUsesPrefixEval = true := by
  decide +kernel

private theorem rendered_ruleSyntaxSugar :
    Export.renderLanguageWithUserSyntax ruleSyntaxSugarLang =
      "language! {\n    name: RuleSyntaxSugarLang,\n\n    types {\n        Proc\n    },\n\n    terms {\n        Pair . a:Proc, b:Proc |- \"pair\" \"(\" a \",\" b \")\" : Proc;\n    },\n\n    equations {\n        FreshMap . | forAll(xs, x, x # ...rest) |- (Pair A B) = (Pair A B);\n    },\n\n    rewrites {\n        EvalSugar . |- (eval A B) ~> (eval A B);\n    },\n}" := by
  cbv

example :
    hasSubstring "FreshMap . | forAll(xs, x, x # ...rest) |- (Pair A B) = (Pair A B);"
      (Export.renderLanguageWithUserSyntax ruleSyntaxSugarLang) = true := by
  certify_rendered_infix rendered_ruleSyntaxSugar

example :
    hasSubstring "EvalSugar . |- (eval A B) ~> (eval A B);"
      (Export.renderLanguageWithUserSyntax ruleSyntaxSugarLang) = true := by
  certify_rendered_infix rendered_ruleSyntaxSugar

example : isError (CoreSyntaxBridge.specToCoreLanguage ruleSyntaxSugarLang) = true := by
  decide +kernel

/-- Semantic validation examples on authored `languageDef!` values. -/
def badValidationLang : LanguageDef :=
  languageDef! {
    name : "BadValidation"
    types {
      Expr
      Expr
    }
    terms {
      Wrap . x:Expr |- y : Expr;
    }
    equations { }
    rewrites {
      Bad . | unknownRel(X) |- Unknown(X) ~> Wrap(X);
    }
  }

example : hasValidationMessage "duplicate type `Expr`" (LanguageDef.validate badValidationLang) = true := by
  simp only [hasValidationMessage, String.contains_string_eq_internal]
  decide +kernel
example : hasValidationMessage "unknown syntax parameter `y`" (LanguageDef.validate badValidationLang) = true := by
  simp only [hasValidationMessage, String.contains_string_eq_internal]
  decide +kernel
example : LogicProgram.AdmissibleFor [] badValidationLang = false := by
  decide
example : hasValidationMessage "unknown constructor `Unknown/1`" (LanguageDef.validate badValidationLang) = true := by
  simp only [hasValidationMessage, String.contains_string_eq_internal]
  decide +kernel

/-- Validation should recurse through authored syntax operators rather than
    silently skipping nested references. -/
def badNestedSyntaxValidationLang : LanguageDef :=
  languageDef! {
    name : "BadNestedSyntaxValidation"
    types {
      Proc
      Name
    }
    terms {
      PInputs . ns:Vec(Name), xs:Vec(Name), p:Proc |- "for" "(" *zip(ns, ys).*map(|n, x| x "<-" y).*sep(",") ")" "{" q "}" : Proc;
      PMaybe . x:Name, p:Proc |- "maybe" "(" *opt(y) ")" "{" p "}" : Proc;
    }
    equations { }
    rewrites { }
  }

example :
    hasValidationMessage "unknown syntax parameter `ys`"
      (LanguageDef.validate badNestedSyntaxValidationLang) = true := by
  simp only [hasValidationMessage, String.contains_string_eq_internal]
  decide +kernel

example :
    hasValidationMessage "unknown syntax parameter `y`"
      (LanguageDef.validate badNestedSyntaxValidationLang) = true := by
  simp only [hasValidationMessage, String.contains_string_eq_internal]
  decide +kernel

example :
    hasValidationMessage "unknown syntax parameter `q`"
      (LanguageDef.validate badNestedSyntaxValidationLang) = true := by
  simp only [hasValidationMessage, String.contains_string_eq_internal]
  decide +kernel

/-- Eval-policy parsing/exporting examples: fold/oracle/rewrite annotations on
    term declarations are preserved in `GrammarRule.evalPolicy?`. -/
def termEvalPolicyLang : LanguageDef :=
  languageDef! {
    name : "TermEvalPolicyLang"
    types {
      Proc
      ![i64] as Int
    }
    terms {
      CastInt . n:Int |- "int" "(" n ")" : Proc ![fold];
      Add . a:Proc, b:Proc |- a "+" b : Proc ![fold];
      Rand . |- "rand" "(" ")" : Proc ![oracle];
      Keep . p:Proc |- "keep" p : Proc ![rewrite];
      Plain . p:Proc |- "plain" p : Proc;
    }
    equations { }
    rewrites { }
  }

private def castIntRule : GrammarRule :=
  termEvalPolicyLang.terms.get ⟨0, by decide +kernel⟩

private def randRule : GrammarRule :=
  termEvalPolicyLang.terms.get ⟨2, by decide +kernel⟩

private def keepRule : GrammarRule :=
  termEvalPolicyLang.terms.get ⟨3, by decide +kernel⟩

private def plainRule : GrammarRule :=
  termEvalPolicyLang.terms.get ⟨4, by decide +kernel⟩

example : castIntRule.evalPolicy? = some .fold := rfl
example : randRule.evalPolicy? = some .oracle := rfl
example : keepRule.evalPolicy? = some .rewrite := rfl
example : plainRule.evalPolicy? = none := rfl

private theorem rendered_termEvalPolicy :
    Export.renderLanguageWithUserSyntax termEvalPolicyLang =
      "language! {\n    name: TermEvalPolicyLang,\n\n    types {\n        Proc\n        ![i64] as Int\n    },\n\n    terms {\n        CastInt . n:Int |- \"int\" \"(\" n \")\" : Proc ![fold];\n        Add . a:Proc, b:Proc |- a \"+\" b : Proc ![fold];\n        Rand . |- \"rand\" \"(\" \")\" : Proc ![oracle];\n        Keep . p:Proc |- \"keep\" p : Proc ![rewrite];\n        Plain . p:Proc |- \"plain\" p : Proc;\n    },\n\n    equations {    },\n\n    rewrites {    },\n}" := by
  cbv

example :
    hasSubstring "CastInt . n:Int |- \"int\" \"(\" n \")\" : Proc ![fold];"
      (Export.renderLanguageWithUserSyntax termEvalPolicyLang) = true := by
  certify_rendered_infix rendered_termEvalPolicy

example :
    hasSubstring "Rand . |- \"rand\" \"(\" \")\" : Proc ![oracle];"
      (Export.renderLanguageWithUserSyntax termEvalPolicyLang) = true := by
  certify_rendered_infix rendered_termEvalPolicy

example :
    hasSubstring "Keep . p:Proc |- \"keep\" p : Proc ![rewrite];"
      (Export.renderLanguageWithUserSyntax termEvalPolicyLang) = true := by
  certify_rendered_infix rendered_termEvalPolicy

example : isError (CoreSyntaxBridge.specToCoreLanguage termEvalPolicyLang) = true := by
  decide +kernel

private theorem rendered_termPolicies :
    zone2WithEvalPolicy termEvalPolicyLang =
      "name:TermEvalPolicyLang\ntypes:\n  ![i64] as Int\n  Proc\nterms:\n  Add . <2:arg,arg>|-<syntax>:Proc\n  CastInt . <1:arg>|-<syntax>:Proc\n  Keep . <1:arg>|-<syntax>:Proc\n  Plain . <1:arg>|-<syntax>:Proc\n  Rand . <0:>|-<syntax>:Proc\nequations:\nrewrites:\nterm-policies:\n  CastInt=Mettapedia.OSLF.MeTTaIL.Canonical.CanonicalEvalPolicy.fold\n  Add=Mettapedia.OSLF.MeTTaIL.Canonical.CanonicalEvalPolicy.fold\n  Rand=Mettapedia.OSLF.MeTTaIL.Canonical.CanonicalEvalPolicy.hostCodeOnly\n  Keep=Mettapedia.OSLF.MeTTaIL.Canonical.CanonicalEvalPolicy.rewrite\n  Plain=Mettapedia.OSLF.MeTTaIL.Canonical.CanonicalEvalPolicy.rewrite\n" := by
  cbv

example :
    hasSubstring "term-policies:"
      (zone2WithEvalPolicy termEvalPolicyLang) = true := by
  certify_rendered_infix rendered_termPolicies

example :
    hasSubstring "CastInt="
      (zone2WithEvalPolicy termEvalPolicyLang) = true := by
  certify_rendered_infix rendered_termPolicies

example :
    hasSubstring "Rand="
      (zone2WithEvalPolicy termEvalPolicyLang) = true := by
  certify_rendered_infix rendered_termPolicies

example :
    hasSubstring "Keep="
      (zone2WithEvalPolicy termEvalPolicyLang) = true := by
  certify_rendered_infix rendered_termPolicies

example :
    hasSubstring "fold"
      (zone2WithEvalPolicy termEvalPolicyLang) = true := by
  certify_rendered_infix rendered_termPolicies

example :
    hasSubstring "hostCodeOnly"
      (zone2WithEvalPolicy termEvalPolicyLang) = true := by
  certify_rendered_infix rendered_termPolicies

example :
    hasSubstring "rewrite"
      (zone2WithEvalPolicy termEvalPolicyLang) = true := by
  certify_rendered_infix rendered_termPolicies


/-- Zone-2 distinguishes all three eval policies in a single language. -/
private def zone2Fingerprint : String := zone2WithEvalPolicy termEvalPolicyLang

example : zone2Fingerprint.contains "CastInt=Mettapedia.OSLF.MeTTaIL.Canonical.CanonicalEvalPolicy.fold" = true := by
  unfold zone2Fingerprint
  certify_rendered_infix rendered_termPolicies
example : zone2Fingerprint.contains "Rand=Mettapedia.OSLF.MeTTaIL.Canonical.CanonicalEvalPolicy.hostCodeOnly" = true := by
  unfold zone2Fingerprint
  certify_rendered_infix rendered_termPolicies
example : zone2Fingerprint.contains "Keep=Mettapedia.OSLF.MeTTaIL.Canonical.CanonicalEvalPolicy.rewrite" = true := by
  unfold zone2Fingerprint
  certify_rendered_infix rendered_termPolicies
example : zone2Fingerprint.contains "Plain=Mettapedia.OSLF.MeTTaIL.Canonical.CanonicalEvalPolicy.rewrite" = true := by
  unfold zone2Fingerprint
  certify_rendered_infix rendered_termPolicies

/-- Zone-2 is strictly richer than Zone-1: Zone-1 does not contain policy info. -/
private theorem rendered_sharedCore :
    zone1SharedCore termEvalPolicyLang =
      "name:TermEvalPolicyLang\ntypes:\n  ![i64] as Int\n  Proc\nterms:\n  Add . <2:arg,arg>|-<syntax>:Proc\n  CastInt . <1:arg>|-<syntax>:Proc\n  Keep . <1:arg>|-<syntax>:Proc\n  Plain . <1:arg>|-<syntax>:Proc\n  Rand . <0:>|-<syntax>:Proc\nequations:\nrewrites:\n" := by
  cbv

/-- The policy-preserving code differs from the shared-core code. -/
example :
    zone2WithEvalPolicy termEvalPolicyLang ≠
    zone1SharedCore termEvalPolicyLang := by
  intro sameCode
  have sameSize := congrArg String.utf8ByteSize sameCode
  rw [rendered_termPolicies, rendered_sharedCore] at sameSize
  exact (by decide +kernel : (608 : Nat) ≠ 246) sameSize

example :
    (zone1SharedCore termEvalPolicyLang).contains "term-policies:" = false := by
  certify_rendered_infix rendered_sharedCore
example :
    (zone2WithEvalPolicy termEvalPolicyLang).contains "term-policies:" = true := by
  certify_rendered_infix rendered_termPolicies

local elab "isolated_rejection" cmd:command : command => do
  Lean.withoutModifyingEnv <| Lean.Elab.Command.elabCommand cmd

/-- error: unsupported carrier `mystery` -/
#guard_msgs in
isolated_rejection
def badCarrierLang : LanguageDef :=
  languageDef! {
    name : "BadCarrier"
    types {
      ![mystery] as Tok
    }
    terms { }
    equations { }
    rewrites { }
  }

/-- error: unsupported congruence collection `Maybe` -/
#guard_msgs in
isolated_rejection
def badTypeCollectionLang : LanguageDef :=
  languageDef! {
    name : "BadTypeCollection"
    types {
      Expr
    }
    terms {
      Wrap . xs:Maybe(Expr) |- "wrap" xs : Expr;
    }
    equations { }
    rewrites { }
  }

end Mettapedia.OSLF.MeTTaIL.LanguageDefDSLTests
