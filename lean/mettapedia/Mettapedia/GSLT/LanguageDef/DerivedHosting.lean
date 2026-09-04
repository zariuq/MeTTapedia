import Mettapedia.GSLT.LanguageDef.LFTyping
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

/-!
# Derived hosting inputs for LF and HOL

This module advances the O2/O5 input leg: LF and HOL are authored as
`languageDef!` values, the existing ungraded OSLF machinery is run on them, and
a generic extraction function maps any `LanguageDef` into the small LF signature
shape used by the pure kernel reference.

It does not discharge O2's graded/bridge obligation, and it does not discharge
O3's native HOL checker obligation.  The HOL extracted LF signature below is a
pure-mode shadow only.
-/

namespace Mettapedia.GSLT.LanguageDef.DerivedHosting

open Mettapedia.GSLT.LanguageDef.LF (Srt Term)
open Mettapedia.GSLT.LanguageDef.LFTyping (Decl Sig)
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open Mettapedia.OSLF.MeTTaIL.Syntax
open scoped Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

/-! ## LF as a `languageDef!` input -/

/-- LF (lambda-Pi) term syntax as a `LanguageDef`.

The constructor set mirrors `LF.Term`: `srt`, `con`, `var`, `pi`, `lam`, and
`app`.  The equations/rewrites record the alpha/beta syntax at the languageDef
level; the checked LF type/proof kernel remains the separate `LFTyping` layer.
-/
def lfLanguageDef : LanguageDef :=
  languageDef! {
    name : "LF"
    types {
      LFSort
      LFTerm
      LFName
      LFIndex
    }
    terms {
      SortType . |- "Type" : LFSort;
      SortKind . |- "Kind" : LFSort;
      Srt . s:LFSort |- "Srt" "(" s ")" : LFTerm;
      Con . n:LFName |- "Con" "(" n ")" : LFTerm;
      Var . i:LFIndex |- "Var" "(" i ")" : LFTerm;
      Pi . a:LFTerm, ^x.body:[LFTerm] |- "Pi" "(" a "," x "." body ")" : LFTerm;
      Lam . a:LFTerm, ^x.body:[LFTerm] |- "Lam" "(" a "," x "." body ")" : LFTerm;
      App . f:LFTerm, a:LFTerm |- "App" "(" f "," a ")" : LFTerm;
    }
    equations {
      AlphaPi . |- Pi(A, ^x.B) = Pi(A, ^y.B);
      AlphaLam . |- Lam(A, ^x.B) = Lam(A, ^y.B);
      BetaEq . |- App(Lam(A, ^x.B), X) = eval(B, X);
    }
    rewrites {
      Beta . |- App(Lam(A, ^x.B), X) ~> eval(B, X);
    }
  }

def lfOSLF : OSLFTypeSystem (langRewriteSystem lfLanguageDef "LFTerm") :=
  langOSLF lfLanguageDef "LFTerm"

abbrev lfPredicate := EquationPredicate (langGSLT lfLanguageDef)

abbrev lfDiamond : lfPredicate → lfPredicate :=
  langDiamond lfLanguageDef

abbrev lfBox : lfPredicate → lfPredicate :=
  langBox lfLanguageDef

theorem lfGalois :
    GaloisConnection lfDiamond lfBox :=
  langGalois lfLanguageDef

theorem lf_srt_crossing :
    ("Srt", "LFSort", "LFTerm") ∈ unaryCrossings lfLanguageDef := by
  decide

theorem lf_con_crossing :
    ("Con", "LFName", "LFTerm") ∈ unaryCrossings lfLanguageDef := by
  decide

theorem lf_var_crossing :
    ("Var", "LFIndex", "LFTerm") ∈ unaryCrossings lfLanguageDef := by
  decide

/-! ## HOL as its own `languageDef!` input -/

/-- Classical STT-style syntax as an unpinned HOL-adjacent language definition.

The grammar borrows the `hol-core-g` precedence ladder from `HOL.lean`, but the
equations below are classical propositional identities, not HOL Light's
equality-based definitions. This value is an OSLF pressure test and pure-mode
shadow input, not the faithful HOL-Light hosting target.
-/
def holLanguageDef : LanguageDef :=
  languageDef! {
    name : "HOL"
    types {
      HolTerm
      Name
    }
    terms {
      HConst . n:Name |- n : HolTerm;
      Truth . |- "T" : HolTerm;
      Falsehood . |- "F" : HolTerm;
      HApp . f:HolTerm, a:HolTerm |- f a : HolTerm;
      HAll . ^x.body:[HolTerm] |- "HALL" x "." body : HolTerm;
      HEx . ^x.body:[HolTerm] |- "HEX" x "." body : HolTerm;
      HLam . ^x.body:[HolTerm] |- "HLAM" x "." body : HolTerm;
      HIff . p:HolTerm, q:HolTerm |- p "HIFF" q : HolTerm;
      HImp . p:HolTerm, q:HolTerm |- p "HIMP" q : HolTerm;
      HOr . p:HolTerm, q:HolTerm |- p "HOR" q : HolTerm;
      HAnd . p:HolTerm, q:HolTerm |- p "HAND" q : HolTerm;
      HEq . p:HolTerm, q:HolTerm |- p "HEQ" q : HolTerm;
      HNot . p:HolTerm |- "HNOT" p : HolTerm;
    }
    equations {
      ImpAsOr . |- HImp(P, Q) = HOr(HNot(P), Q);
      AndAsNotImp . |- HAnd(P, Q) = HNot(HImp(P, HNot(Q)));
      IffAsAndImp . |- HIff(P, Q) = HAnd(HImp(P, Q), HImp(Q, P));
    }
    rewrites {
      HBeta . |- HApp(HLam(^x.B), X) ~> eval(B, X);
    }
  }

def holOSLF : OSLFTypeSystem (langRewriteSystem holLanguageDef "HolTerm") :=
  langOSLF holLanguageDef "HolTerm"

abbrev holPredicate := EquationPredicate (langGSLT holLanguageDef)

abbrev holDiamond : holPredicate → holPredicate :=
  langDiamond holLanguageDef

abbrev holBox : holPredicate → holPredicate :=
  langBox holLanguageDef

theorem holGalois :
    GaloisConnection holDiamond holBox :=
  langGalois holLanguageDef

theorem hol_const_crossing :
    ("HConst", "Name", "HolTerm") ∈ unaryCrossings holLanguageDef := by
  decide

/-! ## Generic pure-mode LF extraction -/

def lfType : Term := .srt Srt.type

def lfCon (s : String) : Term := .con s

def lfAppN (head : Term) : List Term → Term
  | [] => head
  | arg :: rest => lfAppN (.app head arg) rest

def lfPiChain (args : List Term) (result : Term) : Term :=
  args.foldr (fun arg rest => .pi arg rest) result

def collTypeName : CollType → String
  | .vec => "__ldVec"
  | .hashBag => "__ldHashBag"
  | .hashSet => "__ldHashSet"

def collTagName : CollType → String
  | .vec => "__ldCollVec"
  | .hashBag => "__ldCollHashBag"
  | .hashSet => "__ldCollHashSet"

def typeExprToLF : TypeExpr → Term
  | .base s => lfCon s
  | .arrow dom cod => .pi (typeExprToLF dom) (typeExprToLF cod)
  | .multiBinder body => lfAppN (lfCon "__ldMultiBinder") [typeExprToLF body]
  | .collection coll elem => lfAppN (lfCon (collTypeName coll)) [typeExprToLF elem]

def termParamToLF (resultSort : String) : TermParam → Term
  | .simple _ ty => typeExprToLF ty
  | .abstractionNamed _ _ ty => .pi (typeExprToLF ty) (lfCon resultSort)
  | .multiAbstractionNamed _ _ ty => typeExprToLF ty

def grammarRuleToLFDecl (r : GrammarRule) : Decl :=
  .const r.label
    (lfPiChain (r.params.map (termParamToLF r.category)) (lfCon r.category))

def typeDeclToLFDecl (decl : TypeDecl) : Decl :=
  .const decl.name lfType

def nameLit (s : String) : Term :=
  lfCon ("name:" ++ s)

def natLit (n : Nat) : Term :=
  lfCon ("nat:" ++ toString n)

mutual
  def nameListToLF : List String → Term
    | [] => lfCon "__ldNameNil"
    | s :: rest => lfAppN (lfCon "__ldNameCons") [nameLit s, nameListToLF rest]

  def patternToLF : Pattern → Term
    | .bvar n => lfAppN (lfCon "__ldPBVar") [natLit n]
    | .fvar s => lfAppN (lfCon "__ldPFVar") [nameLit s]
    | .apply ctor args => lfAppN (lfCon "__ldPApply") [nameLit ctor, patternListToLF args]
    | .lambda none body => lfAppN (lfCon "__ldPLambda") [lfCon "__ldNoName", patternToLF body]
    | .lambda (some binder) body =>
        lfAppN (lfCon "__ldPLambda") [nameLit binder, patternToLF body]
    | .multiLambda arity binders body =>
        lfAppN (lfCon "__ldPMultiLambda")
          [natLit arity, nameListToLF binders, patternToLF body]
    | .subst body repl => lfAppN (lfCon "__ldPSubst") [patternToLF body, patternToLF repl]
    | .collection coll elems none =>
        lfAppN (lfCon "__ldPCollection")
          [lfCon (collTagName coll), patternListToLF elems, lfCon "__ldNoName"]
    | .collection coll elems (some rest) =>
        lfAppN (lfCon "__ldPCollection")
          [lfCon (collTagName coll), patternListToLF elems, nameLit rest]

  def patternListToLF : List Pattern → Term
    | [] => lfCon "__ldPNil"
    | pat :: rest => lfAppN (lfCon "__ldPCons") [patternToLF pat, patternListToLF rest]
end

def addFreshName (names : List String) (nm : String) : List String :=
  if nm ∈ names then names else names ++ [nm]

mutual
  def patternFVarNamesAcc : Pattern → List String → List String
    | .bvar _, names => names
    | .fvar s, names => addFreshName names s
    | .apply _ args, names => patternListFVarNamesAcc args names
    | .lambda _ body, names => patternFVarNamesAcc body names
    | .multiLambda _ _ body, names => patternFVarNamesAcc body names
    | .subst body repl, names => patternFVarNamesAcc repl (patternFVarNamesAcc body names)
    | .collection _ elems rest, names =>
        let names' := patternListFVarNamesAcc elems names
        match rest with
        | none => names'
        | some s => addFreshName names' s

  def patternListFVarNamesAcc : List Pattern → List String → List String
    | [], names => names
    | pat :: rest, names => patternListFVarNamesAcc rest (patternFVarNamesAcc pat names)
end

def patternFVarNames (pat : Pattern) : List String :=
  patternFVarNamesAcc pat []

def rewriteFVarNames (rw : RewriteRule) : List String :=
  patternFVarNamesAcc rw.right (patternFVarNamesAcc rw.left [])

def nameIndex? (nm : String) : List String → Nat → Option Nat
  | [], _ => none
  | head :: rest, n =>
      if head = nm then some n else nameIndex? nm rest (n + 1)

def fvarDeBruijn? (vars : List String) (nm : String) : Option Nat :=
  match nameIndex? nm vars 0 with
  | none => none
  | some pos => some (vars.length - (pos + 1))

mutual
  def patternToLFSchema (vars : List String) : Pattern → Term
    | .bvar n => lfAppN (lfCon "__ldPBVar") [natLit n]
    | .fvar s =>
        match fvarDeBruijn? vars s with
        | some idx => .var idx
        | none => lfAppN (lfCon "__ldPFVar") [nameLit s]
    | .apply ctor args =>
        lfAppN (lfCon "__ldPApply") [nameLit ctor, patternListToLFSchema vars args]
    | .lambda none body =>
        lfAppN (lfCon "__ldPLambda") [lfCon "__ldNoName", patternToLFSchema vars body]
    | .lambda (some binder) body =>
        lfAppN (lfCon "__ldPLambda") [nameLit binder, patternToLFSchema vars body]
    | .multiLambda arity binders body =>
        lfAppN (lfCon "__ldPMultiLambda")
          [natLit arity, nameListToLF binders, patternToLFSchema vars body]
    | .subst body repl =>
        lfAppN (lfCon "__ldPSubst")
          [patternToLFSchema vars body, patternToLFSchema vars repl]
    | .collection coll elems none =>
        lfAppN (lfCon "__ldPCollection")
          [lfCon (collTagName coll), patternListToLFSchema vars elems,
            lfCon "__ldNoName"]
    | .collection coll elems (some rest) =>
        let restTerm :=
          match fvarDeBruijn? vars rest with
          | some idx => .var idx
          | none => nameLit rest
        lfAppN (lfCon "__ldPCollection")
          [lfCon (collTagName coll), patternListToLFSchema vars elems, restTerm]

  def patternListToLFSchema (vars : List String) : List Pattern → Term
    | [] => lfCon "__ldPNil"
    | pat :: rest =>
        lfAppN (lfCon "__ldPCons")
          [patternToLFSchema vars pat, patternListToLFSchema vars rest]
end

def equationToLFDecl (eqn : Equation) : Decl :=
  .const ("equation:" ++ eqn.name)
    (lfAppN (lfCon "__ldEquationRule") [patternToLF eqn.left, patternToLF eqn.right])

def rewriteToLFDecl (rw : RewriteRule) : Decl :=
  .const ("rewrite:" ++ rw.name)
    (lfAppN (lfCon "__ldRewriteRule") [patternToLF rw.left, patternToLF rw.right])

mutual
  def patternNameLits : Pattern → List String
    | .bvar _ => []
    | .fvar s => [s]
    | .apply ctor args => ctor :: patternListNameLits args
    | .lambda none body => patternNameLits body
    | .lambda (some binder) body => binder :: patternNameLits body
    | .multiLambda _ binders body => binders ++ patternNameLits body
    | .subst body repl => patternNameLits body ++ patternNameLits repl
    | .collection _ elems none => patternListNameLits elems
    | .collection _ elems (some rest) => rest :: patternListNameLits elems

  def patternListNameLits : List Pattern → List String
    | [] => []
    | pat :: rest => patternNameLits pat ++ patternListNameLits rest
end

mutual
  def patternIndexLits : Pattern → List Nat
    | .bvar n => [n]
    | .fvar _ => []
    | .apply _ args => patternListIndexLits args
    | .lambda _ body => patternIndexLits body
    | .multiLambda arity _ body => arity :: patternIndexLits body
    | .subst body repl => patternIndexLits body ++ patternIndexLits repl
    | .collection _ elems _ => patternListIndexLits elems

  def patternListIndexLits : List Pattern → List Nat
    | [] => []
    | pat :: rest => patternIndexLits pat ++ patternListIndexLits rest
end

def equationNameLits (eqn : Equation) : List String :=
  patternNameLits eqn.left ++ patternNameLits eqn.right

def rewriteNameLits (rw : RewriteRule) : List String :=
  patternNameLits rw.left ++ patternNameLits rw.right

def equationIndexLits (eqn : Equation) : List Nat :=
  patternIndexLits eqn.left ++ patternIndexLits eqn.right

def rewriteIndexLits (rw : RewriteRule) : List Nat :=
  patternIndexLits rw.left ++ patternIndexLits rw.right

def equationListNameLits : List Equation → List String
  | [] => []
  | eqn :: rest => equationNameLits eqn ++ equationListNameLits rest

def rewriteListNameLits : List RewriteRule → List String
  | [] => []
  | rw :: rest => rewriteNameLits rw ++ rewriteListNameLits rest

def grammarRuleNameLits (r : GrammarRule) : List String :=
  [r.label]

def grammarRuleListNameLits : List GrammarRule → List String
  | [] => []
  | r :: rest => grammarRuleNameLits r ++ grammarRuleListNameLits rest

def equationListIndexLits : List Equation → List Nat
  | [] => []
  | eqn :: rest => equationIndexLits eqn ++ equationListIndexLits rest

def rewriteListIndexLits : List RewriteRule → List Nat
  | [] => []
  | rw :: rest => rewriteIndexLits rw ++ rewriteListIndexLits rest

def languageNameLits (lang : LanguageDef) : List String :=
  (grammarRuleListNameLits lang.terms ++
    equationListNameLits lang.equations ++
    rewriteListNameLits lang.rewrites).eraseDups

def languageIndexLits (lang : LanguageDef) : List Nat :=
  (equationListIndexLits lang.equations ++
    rewriteListIndexLits lang.rewrites).eraseDups

def nameLiteralDecl (s : String) : Decl :=
  .const ("name:" ++ s) (lfCon "__ldName")

def indexLiteralDecl (n : Nat) : Decl :=
  .const ("nat:" ++ toString n) (lfCon "__ldIndex")

def languageLiteralDecls (lang : LanguageDef) : Sig :=
  (languageNameLits lang).map nameLiteralDecl ++
    (languageIndexLits lang).map indexLiteralDecl

/-- Generic scaffold used by the extractor to type its metadata constructors.
The concrete hosted language's own declarations are appended after this prefix. -/
def extractionScaffold : Sig :=
  [ .const "__ldName" lfType
  , .const "__ldIndex" lfType
  , .const "__ldPattern" lfType
  , .const "__ldPatternList" lfType
  , .const "__ldNameList" lfType
  , .const "__ldColl" lfType
  , .const "__ldNoName" (lfCon "__ldName")
  , .const "__ldNameNil" (lfCon "__ldNameList")
  , .const "__ldNameCons"
      (.pi (lfCon "__ldName") (.pi (lfCon "__ldNameList") (lfCon "__ldNameList")))
  , .const "__ldPNil" (lfCon "__ldPatternList")
  , .const "__ldPCons"
      (.pi (lfCon "__ldPattern")
        (.pi (lfCon "__ldPatternList") (lfCon "__ldPatternList")))
  , .const "__ldPBVar"
      (.pi (lfCon "__ldIndex") (lfCon "__ldPattern"))
  , .const "__ldPFVar"
      (.pi (lfCon "__ldName") (lfCon "__ldPattern"))
  , .const "__ldPApply"
      (.pi (lfCon "__ldName")
        (.pi (lfCon "__ldPatternList") (lfCon "__ldPattern")))
  , .const "__ldPLambda"
      (.pi (lfCon "__ldName")
        (.pi (lfCon "__ldPattern") (lfCon "__ldPattern")))
  , .const "__ldPMultiLambda"
      (.pi (lfCon "__ldIndex")
        (.pi (lfCon "__ldNameList")
          (.pi (lfCon "__ldPattern") (lfCon "__ldPattern"))))
  , .const "__ldPSubst"
      (.pi (lfCon "__ldPattern")
        (.pi (lfCon "__ldPattern") (lfCon "__ldPattern")))
  , .const "__ldPCollection"
      (.pi (lfCon "__ldColl")
        (.pi (lfCon "__ldPatternList")
          (.pi (lfCon "__ldName") (lfCon "__ldPattern"))))
  , .const (collTagName .vec) (lfCon "__ldColl")
  , .const (collTagName .hashBag) (lfCon "__ldColl")
  , .const (collTagName .hashSet) (lfCon "__ldColl")
  , .const "__ldEquationRule" (.pi (lfCon "__ldPattern") (.pi (lfCon "__ldPattern") lfType))
  , .const "__ldRewriteRule" (.pi (lfCon "__ldPattern") (.pi (lfCon "__ldPattern") lfType))
  , .const "__ldMultiBinder" (.pi lfType lfType)
  , .const "__ldVec" (.pi lfType lfType)
  , .const "__ldHashBag" (.pi lfType lfType)
  , .const "__ldHashSet" (.pi lfType lfType)
  ]

/-- Total generic extraction from one `LanguageDef` value to a pure LF signature. -/
def languageDefToLFSig (lang : LanguageDef) : Sig :=
  extractionScaffold ++
    lang.types.map typeDeclToLFDecl ++
    lang.terms.map grammarRuleToLFDecl ++
    languageLiteralDecls lang ++
    lang.equations.map equationToLFDecl ++
    lang.rewrites.map rewriteToLFDecl

def isHigherKindScaffoldName : String → Bool
  | "__ldMultiBinder" => true
  | "__ldVec" => true
  | "__ldHashBag" => true
  | "__ldHashSet" => true
  | _ => false

def kernelExtractionScaffold : Sig :=
  extractionScaffold.filter fun
    | .const n _ => !isHigherKindScaffoldName n
    | .defn n _ _ => !isHigherKindScaffoldName n

/-! ## Generic reachability hosting

This is the generic table-to-signature layer for authored `LanguageDef`
rewrites.  It generates LF constants for a reachability judgment over the
language-def pattern objects plus one proof constructor per rewrite rule.  The
kernel still checks ordinary LF proof terms; this layer only lowers rule data to
signature data.
-/

def reachReducesName (langName : String) : String :=
  langName ++ ":Reduces"

def reachEvalEqName (langName : String) : String :=
  langName ++ ":EvalEq"

def reachReflName (langName : String) : String :=
  langName ++ ":reduces-refl"

def reachTransName (langName : String) : String :=
  langName ++ ":reduces-trans"

def reachEvalEqIntroName (langName : String) : String :=
  langName ++ ":eval-eq-intro"

def reachApplyHeadCongName (langName : String) : String :=
  langName ++ ":reduces-apply-head"

def reachApplySecondCongName (langName : String) : String :=
  langName ++ ":reduces-apply-second"

def reachRewriteName (langName ruleName : String) : String :=
  langName ++ ":rewrite:" ++ ruleName

def ldPatternType : Term :=
  lfCon "__ldPattern"

def reachReduces (langName : String) (left right : Term) : Term :=
  lfAppN (lfCon (reachReducesName langName)) [left, right]

def reachEvalEq (langName : String) (left right : Term) : Term :=
  lfAppN (lfCon (reachEvalEqName langName)) [left, right]

def reachabilityScaffold (langName : String) : Sig :=
  [ .const (reachReducesName langName)
      (.pi ldPatternType (.pi ldPatternType lfType))
  , .const (reachEvalEqName langName)
      (.pi ldPatternType (.pi ldPatternType lfType))
  , .const (reachReflName langName)
      (.pi ldPatternType (reachReduces langName (.var 0) (.var 0)))
  , .const (reachTransName langName)
      (.pi ldPatternType
        (.pi ldPatternType
          (.pi ldPatternType
            (.pi (reachReduces langName (.var 2) (.var 1))
              (.pi (reachReduces langName (.var 2) (.var 1))
                (reachReduces langName (.var 4) (.var 2)))))))
  , .const (reachEvalEqIntroName langName)
      (.pi ldPatternType
        (.pi ldPatternType
          (.pi (reachReduces langName (.var 1) (.var 0))
            (reachEvalEq langName (.var 2) (.var 1)))))
  , .const (reachApplyHeadCongName langName)
      (.pi (lfCon "__ldName")
        (.pi ldPatternType
          (.pi ldPatternType
            (.pi (lfCon "__ldPatternList")
              (.pi (reachReduces langName (.var 2) (.var 1))
                (reachReduces langName
                  (lfAppN (lfCon "__ldPApply")
                    [ .var 4
                    , lfAppN (lfCon "__ldPCons") [.var 3, .var 1]
                    ])
                  (lfAppN (lfCon "__ldPApply")
                    [ .var 4
                    , lfAppN (lfCon "__ldPCons") [.var 2, .var 1]
                    ])))))))
  , .const (reachApplySecondCongName langName)
      (.pi (lfCon "__ldName")
        (.pi ldPatternType
          (.pi ldPatternType
            (.pi ldPatternType
              (.pi (reachReduces langName (.var 1) (.var 0))
                (reachReduces langName
                  (lfAppN (lfCon "__ldPApply")
                    [ .var 4
                    , lfAppN (lfCon "__ldPCons")
                        [ .var 3
                        , lfAppN (lfCon "__ldPCons") [.var 2, lfCon "__ldPNil"]
                        ]
                    ])
                  (lfAppN (lfCon "__ldPApply")
                    [ .var 4
                    , lfAppN (lfCon "__ldPCons")
                        [ .var 3
                        , lfAppN (lfCon "__ldPCons") [.var 1, lfCon "__ldPNil"]
                        ]
                    ])))))))
  ]

def rewriteToReachabilityDecl (langName : String) (rw : RewriteRule) : Decl :=
  let vars := rewriteFVarNames rw
  .const (reachRewriteName langName rw.name)
    (lfPiChain (vars.map fun _ => ldPatternType)
      (reachReduces langName
        (patternToLFSchema vars rw.left)
        (patternToLFSchema vars rw.right)))

/-- Generic reachability signature generated from the same authored rewrite
table that drives `langOSLF`/`langDiamond`. -/
def languageDefToReachabilityLFSig (lang : LanguageDef) : Sig :=
  languageDefToLFSig lang ++
    reachabilityScaffold lang.name ++
    lang.rewrites.map (rewriteToReachabilityDecl lang.name)

/-- Kernel-admissible extraction for hosted reachability proof terms.

The full `LanguageDef` extraction includes higher-kinded metadata such as
collection type constructors.  The current small LF kernel admits the
pattern-level reachability slice instead: pattern/name/index constructors,
language and rule literals, rewrite metadata, and generated reachability proof
constructors.  This is the generic table-to-kernel-signature path used by
derived proof-term fixtures; it is not a checker and it carries no execution
trace data.
-/
def languageDefToKernelReachabilityLFSig (lang : LanguageDef) : Sig :=
  kernelExtractionScaffold ++
    lang.types.map typeDeclToLFDecl ++
    languageLiteralDecls lang ++
    lang.rewrites.map rewriteToLFDecl ++
    reachabilityScaffold lang.name ++
    lang.rewrites.map (rewriteToReachabilityDecl lang.name)

/-! ## Kernel fixture rendering -/

def renderLFTermAsKernelExpr : Term → String
  | .srt .type => "(Srt type)"
  | .srt .kind => "(Srt kind)"
  | .con n => "(Con " ++ n ++ ")"
  | .var i => "(Var " ++ toString i ++ ")"
  | .pi dom cod =>
      "(Pi " ++ renderLFTermAsKernelExpr dom ++ " " ++
        renderLFTermAsKernelExpr cod ++ ")"
  | .lam dom body =>
      "(Lam " ++ renderLFTermAsKernelExpr dom ++ " " ++
        renderLFTermAsKernelExpr body ++ ")"
  | .app f a =>
      "(App " ++ renderLFTermAsKernelExpr f ++ " " ++
        renderLFTermAsKernelExpr a ++ ")"

def renderLFDeclAsKernelExpr : Decl → String
  | .const n ty => "(DConst " ++ n ++ " " ++ renderLFTermAsKernelExpr ty ++ ")"
  | .defn n ty body =>
      "(DDef " ++ n ++ " " ++ renderLFTermAsKernelExpr ty ++ " " ++
        renderLFTermAsKernelExpr body ++ ")"

def renderLFSigAsKernelExpr : Sig → String
  | [] => "SNil"
  | decl :: rest =>
      "(SCons " ++ renderLFDeclAsKernelExpr decl ++ "\n" ++
        renderLFSigAsKernelExpr rest ++ ")"

def lfExtractedSig : Sig :=
  languageDefToLFSig lfLanguageDef

def lfReachabilitySig : Sig :=
  languageDefToReachabilityLFSig lfLanguageDef

/-- HOL's extracted LF signature is a pure-mode shadow, not a HOL checker. -/
def holExtractedSigShadow : Sig :=
  languageDefToLFSig holLanguageDef

def holReachabilitySigShadow : Sig :=
  languageDefToReachabilityLFSig holLanguageDef

theorem lfReachabilitySig_extends_extracted :
    lfReachabilitySig.take lfExtractedSig.length = lfExtractedSig := by
  simp [lfReachabilitySig, languageDefToReachabilityLFSig, lfExtractedSig]

theorem lfReachabilitySig_rewrite_decl_count :
    lfReachabilitySig.length =
      lfExtractedSig.length +
        (reachabilityScaffold lfLanguageDef.name).length +
        lfLanguageDef.rewrites.length := by
  simp [lfReachabilitySig, languageDefToReachabilityLFSig, lfExtractedSig,
    Nat.add_assoc]

theorem lfExtractedSig_firstDecl :
    lfExtractedSig.head? = some (.const "__ldName" lfType) := rfl

theorem corpusSig_firstDecl :
    Mettapedia.GSLT.LanguageDef.LFTyping.corpusSig.head? =
      some (.const "prop" lfType) := rfl

/-- The first grounding check currently diverges: the derived LF signature
starts from the generic languageDef metadata scaffold, while the existing corpus
signature starts from a hand-written object-logic constant. -/
theorem lfExtractedSig_diverges_from_corpusSig :
    lfExtractedSig ≠ Mettapedia.GSLT.LanguageDef.LFTyping.corpusSig := by
  intro h
  have hhead := congrArg List.head? h
  rw [lfExtractedSig_firstDecl, corpusSig_firstDecl] at hhead
  have hneq :
      (some (.const "__ldName" lfType) : Option Decl) ≠ some (.const "prop" lfType) := by
    decide
  exact hneq hhead

#eval unaryCrossings lfLanguageDef
#eval unaryCrossings holLanguageDef
#eval lfExtractedSig.length
#eval holExtractedSigShadow.length
#print axioms lfExtractedSig_diverges_from_corpusSig

end Mettapedia.GSLT.LanguageDef.DerivedHosting
