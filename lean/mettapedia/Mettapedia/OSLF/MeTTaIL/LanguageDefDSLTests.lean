import Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
import Mettapedia.OSLF.MeTTaIL.Export
import Mettapedia.OSLF.MeTTaIL.CoreSyntaxBridge

namespace Mettapedia.OSLF.MeTTaIL.LanguageDefDSLTests

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open scoped Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

/-- Positive smoke example: all authored blocks parse directly into one
    `LanguageDef`, and binder names survive on the relevant `TermParam`s. -/
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
    logic {
      relation knownSymbol(Expr);
      rule "knownSymbol(x) <-- true";
    }
    oracles {
      external evalExpr(Expr, Env) -> Result;
    }
    congruenceCollections { HashBag }
  }

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
example : smokeLang.logic.length = 2 := rfl
example : smokeLang.oracles.length = 1 := rfl
example : smokeLang.congruenceCollections = [.hashBag] := rfl
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
    logic { }
    oracles { }
    congruenceCollections { }
  }

example : binderNamesAt compactBinderLang 0 0 = ["x"] := rfl

private def compactBinderHasLambdaBody : Bool :=
  match compactBinderLang.equations.get ⟨0, by native_decide⟩ with
  | { left := .apply "PNew" [.lambda (some "x") (.fvar "P")], .. } => true
  | _ => false

private def hasSubstring (needle haystack : String) : Bool :=
  haystack.contains needle

example :
    compactBinderHasLambdaBody = true := by
  native_decide

example :
    hasSubstring "PNew . ^x.p:[Name -> Proc] |- \"new\" \"(\" x \",\" p \")\" : Proc;"
      (Export.renderLanguageWithUserSyntax compactBinderLang) = true := by
  native_decide

example :
    hasSubstring "Scope . |- PNew (^x.P) = PNew (^x.P);"
      (Export.renderLanguageWithUserSyntax compactBinderLang) = true := by
  native_decide

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
      PreserveSurface . | X # ... rest |- Scope(^ x . Keep(X), {X, ... rest}) ~> Scope(^ y . Keep(X), {X});
    }
    logic { }
    oracles { }
    congruenceCollections { HashBag }
  }

private def firstRewrite : RewriteRule :=
  authoredPatternLang.rewrites.get ⟨0, by native_decide⟩

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
  native_decide
example : firstRewriteFreshnessOk = true := by
  native_decide
example : firstRewrite.leftSurface? = some "Scope(^x.Keep (X), {X, ...rest})" := by
  native_decide
example : firstRewrite.rightSurface? = some "Scope(^y.Keep (X), {X})" := by
  native_decide
example : firstRewrite.premiseSurface = ["X # ...rest"] := by
  native_decide
private def firstRewriteHasBinderX : Bool :=
  match firstRewrite.left with
  | .apply "Scope" [.lambda (some binder) _, _] => binder == "x"
  | _ => false

example : firstRewriteHasBinderX = true := by
  native_decide
example : hasSubstring "^x.Keep (X)" (Export.renderLanguage authoredPatternLang) = true := by native_decide
example : hasSubstring "X # ...rest" (Export.renderLanguage authoredPatternLang) = true := by native_decide
example : isError (CoreSyntaxBridge.specToCoreLanguage authoredPatternLang) = true := by
  native_decide

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
    logic { }
    oracles { }
    congruenceCollections { }
  }

example : isError (CoreSyntaxBridge.specToCoreLanguage forAllLang) = true := by
  native_decide
example : hasSubstring "forAll(xs, x, seen(x))" (Export.renderLanguage forAllLang) = true := by
  native_decide

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
    logic { }
    oracles { }
    congruenceCollections { }
  }

private def firstSyntaxRule : GrammarRule :=
  syntaxOpsLang.terms.get ⟨0, by native_decide⟩

private def secondSyntaxRule : GrammarRule :=
  syntaxOpsLang.terms.get ⟨1, by native_decide⟩

private def thirdSyntaxRule : GrammarRule :=
  syntaxOpsLang.terms.get ⟨2, by native_decide⟩

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
  native_decide

example : secondSyntaxShapeOk = true := by
  native_decide

example : thirdSyntaxShapeOk = true := by
  native_decide

example : hasSubstring "ps.*sep(\"|\")" (Export.renderLanguageWithUserSyntax syntaxOpsLang) = true := by
  native_decide
example : hasSubstring "*zip(ns, xs).*map(|n, x| x \"<-\" n).*sep(\",\")" (Export.renderLanguageWithUserSyntax syntaxOpsLang) = true := by
  native_decide
example : hasSubstring "*opt(x)" (Export.renderLanguageWithUserSyntax syntaxOpsLang) = true := by
  native_decide
example : isError (CoreSyntaxBridge.specToCoreLanguage syntaxOpsLang) = true := by
  native_decide

/-- Positive smoke example: rule-side Rust-style pattern operators and mapped
    freshness sugar parse into structured `Pattern` / `Premise` forms, export
    faithfully through stored surface text, and are rejected explicitly by the
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
    logic { }
    oracles { }
    congruenceCollections { HashBag }
  }

private def extrudeEq : Equation :=
  rulePatternOpsLang.equations.get ⟨0, by native_decide⟩

private def commRw : RewriteRule :=
  rulePatternOpsLang.rewrites.get ⟨0, by native_decide⟩

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
  native_decide

example : commLeftHasZipMap = true := by
  native_decide

example : commRightHasEvalMap = true := by
  native_decide

example :
    hasSubstring
        "Extrude . | forAll(xs, x, x # ...rest) |- PPar ({PNew (^[xs].p), ...rest}) = PNew (^[xs].PPar ({p, ...rest}));"
        (Export.renderLanguageWithUserSyntax rulePatternOpsLang) = true := by
  native_decide

example :
    hasSubstring
        "Comm . |- PPar ({PInputs(ns, cont), *zip(ns, qs).*map(|n, q| POutput(n, q)), ...rest}) ~> PPar ({eval(cont, qs.*map(|q| NQuote (q))), ...rest});"
        (Export.renderLanguageWithUserSyntax rulePatternOpsLang) = true := by
  native_decide

example : isError (CoreSyntaxBridge.specToCoreLanguage rulePatternOpsLang) = true := by
  native_decide

/-- Surface-sugar smoke example: keep mapped-freshness sugar and prefix-style
    pattern forms alive as authored syntax, even when canonical RhoCalc uses the
    more stable structural spelling today. -/
def ruleSurfaceSugarLang : LanguageDef :=
  languageDef! {
    name : "RuleSurfaceSugarLang"
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
    logic { }
    oracles { }
    congruenceCollections { HashBag }
  }

private def sugarEq : Equation :=
  ruleSurfaceSugarLang.equations.get ⟨0, by native_decide⟩

private def sugarRw : RewriteRule :=
  ruleSurfaceSugarLang.rewrites.get ⟨0, by native_decide⟩

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
  native_decide

example : sugarEqUsesPrefixApply = true := by
  native_decide

example : sugarRwUsesPrefixEval = true := by
  native_decide

example :
    hasSubstring "FreshMap . | xs.*map(|x| x # ...rest) |- (Pair A B) = (Pair A B);"
      (Export.renderLanguageWithUserSyntax ruleSurfaceSugarLang) = true := by
  native_decide

example :
    hasSubstring "EvalSugar . |- eval(A, B) ~> eval(A, B);"
      (Export.renderLanguageWithUserSyntax ruleSurfaceSugarLang) = true := by
  native_decide

example : isError (CoreSyntaxBridge.specToCoreLanguage ruleSurfaceSugarLang) = true := by
  native_decide

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
    logic { }
    oracles { }
    congruenceCollections { }
  }

example : hasValidationMessage "duplicate type `Expr`" (LanguageDef.validate badValidationLang) = true := by
  native_decide
example : hasValidationMessage "unknown syntax parameter `y`" (LanguageDef.validate badValidationLang) = true := by
  native_decide
example : hasValidationMessage "unknown relation `unknownRel`" (LanguageDef.validate badValidationLang) = true := by
  native_decide
example : hasValidationMessage "unknown constructor `Unknown`" (LanguageDef.validate badValidationLang) = true := by
  native_decide

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
    logic { }
    oracles { }
    congruenceCollections { }
  }

example :
    hasValidationMessage "unknown syntax parameter `ys`"
      (LanguageDef.validate badNestedSyntaxValidationLang) = true := by
  native_decide

example :
    hasValidationMessage "unknown syntax parameter `y`"
      (LanguageDef.validate badNestedSyntaxValidationLang) = true := by
  native_decide

example :
    hasValidationMessage "unknown syntax parameter `q`"
      (LanguageDef.validate badNestedSyntaxValidationLang) = true := by
  native_decide

/-- error: unsupported carrier `mystery` -/
#guard_msgs in
def badCarrierLang : LanguageDef :=
  languageDef! {
    name : "BadCarrier"
    types {
      ![mystery] as Tok
    }
    terms { }
    equations { }
    rewrites { }
    logic { }
    oracles { }
    congruenceCollections { }
  }

/-- error: unsupported congruence collection `Maybe` -/
#guard_msgs in
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
    logic { }
    oracles { }
    congruenceCollections { }
  }

/-- error: unsupported congruence collection `Bag` -/
#guard_msgs in
def badCongruenceCollectionLang : LanguageDef :=
  languageDef! {
    name : "BadCongruenceCollection"
    types {
      Expr
    }
    terms { }
    equations { }
    rewrites { }
    logic { }
    oracles { }
    congruenceCollections { Bag }
  }

end Mettapedia.OSLF.MeTTaIL.LanguageDefDSLTests
