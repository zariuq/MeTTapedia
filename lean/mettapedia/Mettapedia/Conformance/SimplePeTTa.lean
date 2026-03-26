import Algorithms.MeTTa.PeTTa.LegacySessionBridge
import Algorithms.MeTTa.ProfileChecksum
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
import Mettapedia.OSLF.MeTTaIL.Engine

namespace Mettapedia.Conformance.SimplePeTTa

open Algorithms.MeTTa.PeTTa
open Algorithms.MeTTa.Simple

/-! ## Core/Spec translation layer -/

abbrev CCollType := MeTTailCore.MeTTaIL.Syntax.CollType
abbrev SCollType := Mettapedia.OSLF.MeTTaIL.Syntax.CollType

abbrev CTypeExpr := MeTTailCore.MeTTaIL.Syntax.TypeExpr
abbrev STypeExpr := Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr

abbrev CTermParam := MeTTailCore.MeTTaIL.Syntax.TermParam
abbrev STermParam := Mettapedia.OSLF.MeTTaIL.Syntax.TermParam

abbrev CSyntaxItem := MeTTailCore.MeTTaIL.Syntax.SyntaxItem
abbrev SSyntaxItem := Mettapedia.OSLF.MeTTaIL.Syntax.SyntaxItem

abbrev CGrammarRule := MeTTailCore.MeTTaIL.Syntax.GrammarRule
abbrev SGrammarRule := Mettapedia.OSLF.MeTTaIL.Syntax.GrammarRule

abbrev CPattern := MeTTailCore.MeTTaIL.Syntax.Pattern
abbrev SPattern := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

abbrev CFreshness := MeTTailCore.MeTTaIL.Syntax.FreshnessCondition
abbrev SFreshness := Mettapedia.OSLF.MeTTaIL.Syntax.FreshnessCondition

abbrev CPremise := MeTTailCore.MeTTaIL.Syntax.Premise
abbrev SPremise := Mettapedia.OSLF.MeTTaIL.Syntax.Premise

abbrev CEquation := MeTTailCore.MeTTaIL.Syntax.Equation
abbrev SEquation := Mettapedia.OSLF.MeTTaIL.Syntax.Equation

abbrev CRewriteRule := MeTTailCore.MeTTaIL.Syntax.RewriteRule
abbrev SRewriteRule := Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule

abbrev CCongruenceCollection := MeTTailCore.MeTTaIL.Syntax.CongruenceCollection
abbrev CLanguageDef := MeTTailCore.MeTTaIL.Syntax.LanguageDef
abbrev SLanguageDef := Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef

private def coreToSpecTypeDecl (typeName : String) : Mettapedia.OSLF.MeTTaIL.Syntax.TypeDecl :=
  Mettapedia.OSLF.MeTTaIL.Syntax.TypeDecl.plain typeName

private def specToCoreTypeName (typeDecl : Mettapedia.OSLF.MeTTaIL.Syntax.TypeDecl) : String :=
  typeDecl.name

private def coreToSpecCollType : CCollType → SCollType
  | .vec => .vec
  | .hashBag => .hashBag
  | .hashSet => .hashSet

private def specToCoreCollType : SCollType → CCollType
  | .vec => .vec
  | .hashBag => .hashBag
  | .hashSet => .hashSet

private def coreToSpecTypeExpr : CTypeExpr → STypeExpr
  | .base s => .base s
  | .arrow a b => .arrow (coreToSpecTypeExpr a) (coreToSpecTypeExpr b)
  | .multiBinder t => .multiBinder (coreToSpecTypeExpr t)
  | .collection ct t => .collection (coreToSpecCollType ct) (coreToSpecTypeExpr t)

private def specToCoreTypeExpr : STypeExpr → CTypeExpr
  | .base s => .base s
  | .arrow a b => .arrow (specToCoreTypeExpr a) (specToCoreTypeExpr b)
  | .multiBinder t => .multiBinder (specToCoreTypeExpr t)
  | .collection ct t => .collection (specToCoreCollType ct) (specToCoreTypeExpr t)

private def coreToSpecTermParam : CTermParam → STermParam
  | .simple x t => .simple x (coreToSpecTypeExpr t)
  | .abstraction x t => .abstraction x (coreToSpecTypeExpr t)
  | .multiAbstraction x t => .multiAbstraction x (coreToSpecTypeExpr t)

private def specToCoreTermParam : STermParam → CTermParam
  | .simple x t => .simple x (specToCoreTypeExpr t)
  | .abstraction x t => .abstraction x (specToCoreTypeExpr t)
  | .multiAbstraction x t => .multiAbstraction x (specToCoreTypeExpr t)

private def coreToSpecSyntaxItem : CSyntaxItem → SSyntaxItem
  | .terminal s => .terminal s
  | .nonTerminal s => .nonTerminal s
  | .separator s => .separator s
  | .delimiter a b => .delimiter a b

private def specToCoreSyntaxItem : SSyntaxItem → CSyntaxItem
  | .terminal s => .terminal s
  | .nonTerminal s => .nonTerminal s
  | .separator s => .separator s
  | .delimiter a b => .delimiter a b

private def coreToSpecGrammarRule (g : CGrammarRule) : SGrammarRule :=
  { label := g.label
    category := g.category
    params := g.params.map coreToSpecTermParam
    syntaxPattern := g.syntaxPattern.map coreToSpecSyntaxItem }

private def specToCoreGrammarRule (g : SGrammarRule) : CGrammarRule :=
  { label := g.label
    category := g.category
    params := g.params.map specToCoreTermParam
    syntaxPattern := g.syntaxPattern.map specToCoreSyntaxItem }

private def coreToSpecPattern : CPattern → SPattern
  | .bvar n => .bvar n
  | .fvar x => .fvar x
  | .apply c args => .apply c (args.map coreToSpecPattern)
  | .lambda body => .lambda (coreToSpecPattern body)
  | .multiLambda n body => .multiLambda n (coreToSpecPattern body)
  | .subst body repl => .subst (coreToSpecPattern body) (coreToSpecPattern repl)
  | .collection ct elems rest =>
      .collection (coreToSpecCollType ct) (elems.map coreToSpecPattern) rest

private def specToCorePattern : SPattern → CPattern
  | .bvar n => .bvar n
  | .fvar x => .fvar x
  | .apply c args => .apply c (args.map specToCorePattern)
  | .lambda body => .lambda (specToCorePattern body)
  | .multiLambda n body => .multiLambda n (specToCorePattern body)
  | .subst body repl => .subst (specToCorePattern body) (specToCorePattern repl)
  | .collection ct elems rest =>
      .collection (specToCoreCollType ct) (elems.map specToCorePattern) rest

private def coreToSpecFreshness (fc : CFreshness) : SFreshness :=
  { varName := fc.varName
    term := coreToSpecPattern fc.term }

private def specToCoreFreshness (fc : SFreshness) : CFreshness :=
  { varName := fc.varName
    term := specToCorePattern fc.term }

private def coreToSpecPremise : CPremise → SPremise
  | .freshness fc => .freshness (coreToSpecFreshness fc)
  | .congruence a b => .congruence (coreToSpecPattern a) (coreToSpecPattern b)
  | .relationQuery rel args => .relationQuery rel (args.map coreToSpecPattern)

private def specToCorePremise : SPremise → CPremise
  | .freshness fc => .freshness (specToCoreFreshness fc)
  | .congruence a b => .congruence (specToCorePattern a) (specToCorePattern b)
  | .relationQuery rel args => .relationQuery rel (args.map specToCorePattern)
  | .forAll _ _ body => specToCorePremise body

private def coreToSpecEquation (eqn : CEquation) : SEquation :=
  { name := eqn.name
    typeContext := eqn.typeContext.map (fun (x, t) => (x, coreToSpecTypeExpr t))
    premises := eqn.premises.map coreToSpecPremise
    left := coreToSpecPattern eqn.left
    right := coreToSpecPattern eqn.right }

private def specToCoreEquation (eqn : SEquation) : CEquation :=
  { name := eqn.name
    typeContext := eqn.typeContext.map (fun (x, t) => (x, specToCoreTypeExpr t))
    premises := eqn.premises.map specToCorePremise
    left := specToCorePattern eqn.left
    right := specToCorePattern eqn.right }

private def coreToSpecRewriteRule (r : CRewriteRule) : SRewriteRule :=
  { name := r.name
    typeContext := r.typeContext.map (fun (x, t) => (x, coreToSpecTypeExpr t))
    premises := r.premises.map coreToSpecPremise
    left := coreToSpecPattern r.left
    right := coreToSpecPattern r.right }

private def specToCoreRewriteRule (r : SRewriteRule) : CRewriteRule :=
  { name := r.name
    typeContext := r.typeContext.map (fun (x, t) => (x, specToCoreTypeExpr t))
    premises := r.premises.map specToCorePremise
    left := specToCorePattern r.left
    right := specToCorePattern r.right }

private def coreToSpecLanguage (lang : CLanguageDef) : SLanguageDef :=
  { name := lang.name
    types := lang.types.map coreToSpecTypeDecl
    terms := lang.terms.map coreToSpecGrammarRule
    equations := lang.equations.map coreToSpecEquation
    rewrites := lang.rewrites.map coreToSpecRewriteRule
    congruenceCollections := lang.congruenceCollections.map (fun c => coreToSpecCollType c.collectionType) }

private def specToCoreLanguage (lang : SLanguageDef) : CLanguageDef :=
  { name := lang.name
    types := lang.types.map specToCoreTypeName
    terms := lang.terms.map specToCoreGrammarRule
    equations := lang.equations.map specToCoreEquation
    rewrites := lang.rewrites.map specToCoreRewriteRule
    congruenceCollections := lang.congruenceCollections.map
      (fun ct => ({ collectionType := specToCoreCollType ct } : CCongruenceCollection)) }

private def coreLanguageEq (a b : CLanguageDef) : Bool :=
  decide (a.name = b.name) &&
  decide (a.types = b.types) &&
  decide (a.terms = b.terms) &&
  decide (a.equations = b.equations) &&
  decide (a.rewrites = b.rewrites) &&
  decide (a.congruenceCollections = b.congruenceCollections)

/-! ## Translation round-trip theorems (direct, non-native_decide) -/

private theorem collType_roundTrip (ct : CCollType) :
    specToCoreCollType (coreToSpecCollType ct) = ct := by
  cases ct <;> rfl

private theorem typeExpr_roundTrip (t : CTypeExpr) :
    specToCoreTypeExpr (coreToSpecTypeExpr t) = t := by
  induction t with
  | base s =>
      rfl
  | arrow a b ihA ihB =>
      simp [coreToSpecTypeExpr, specToCoreTypeExpr, ihA, ihB]
  | multiBinder t ih =>
      simp [coreToSpecTypeExpr, specToCoreTypeExpr, ih]
  | collection ct t ih =>
      cases ct <;> simp [coreToSpecTypeExpr, specToCoreTypeExpr, ih, collType_roundTrip]

private theorem termParam_roundTrip (tp : CTermParam) :
    specToCoreTermParam (coreToSpecTermParam tp) = tp := by
  cases tp with
  | simple x t =>
      simp [coreToSpecTermParam, specToCoreTermParam, typeExpr_roundTrip]
  | abstraction x t =>
      simp [coreToSpecTermParam, specToCoreTermParam, typeExpr_roundTrip]
  | multiAbstraction x t =>
      simp [coreToSpecTermParam, specToCoreTermParam, typeExpr_roundTrip]

private theorem syntaxItem_roundTrip (si : CSyntaxItem) :
    specToCoreSyntaxItem (coreToSpecSyntaxItem si) = si := by
  cases si <;> rfl

private theorem map_termParam_roundTrip (xs : List CTermParam) :
    xs.map (specToCoreTermParam ∘ coreToSpecTermParam) = xs := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [ih, termParam_roundTrip, Function.comp]

private theorem map_syntaxItem_roundTrip (xs : List CSyntaxItem) :
    xs.map (specToCoreSyntaxItem ∘ coreToSpecSyntaxItem) = xs := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [ih, syntaxItem_roundTrip, Function.comp]

private theorem grammarRule_roundTrip (g : CGrammarRule) :
    specToCoreGrammarRule (coreToSpecGrammarRule g) = g := by
  cases g with
  | mk label category params syntaxPattern =>
      simp [coreToSpecGrammarRule, specToCoreGrammarRule, map_termParam_roundTrip, map_syntaxItem_roundTrip]

private def coreTupleToSpecRow (row : RelationTuple) : String × List SPattern :=
  (row.relation, row.tuple.map coreToSpecPattern)

private def tuplesForSpecRows (rows : List (String × List SPattern))
    (rel : String) (arity : Nat) : List (List SPattern) :=
  rows.filterMap fun row =>
    if row.1 == rel && row.2.length == arity then
      some row.2
    else
      none

private def specRelationEnvOfRows (rows : List (String × List SPattern)) :
    Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv where
  tuples := fun rel args => tuplesForSpecRows rows rel args.length

/-! ## Spec-side evaluator (Session-shaped) -/

private def specRewriteWithContext (cfg : FrozenPeTTaConfig) (term : SPattern) : List SPattern :=
  let lang := coreToSpecLanguage (toLanguageDef cfg)
  let relationRows := cfg.relationFacts.map coreTupleToSpecRow
  let builtinRows := cfg.builtinFacts.map coreTupleToSpecRow
  let relEnv := specRelationEnvOfRows (relationRows ++ builtinRows)
  Mettapedia.OSLF.MeTTaIL.Engine.rewriteWithContextWithPremisesUsing relEnv lang term

private def insertUniqueSpec (xs : List SPattern) (x : SPattern) : List SPattern :=
  if xs.contains x then xs else x :: xs

private def enqueueNextSpec (pending : List (SPattern × Nat)) (depth : Nat)
    (terms : List SPattern) : List (SPattern × Nat) :=
  (terms.map (fun t => (t, depth))) ++ pending

private def evalSpecAux (cfg : FrozenPeTTaConfig) (fuel : Nat)
    (pending : List (SPattern × Nat)) (normals : List SPattern) : List SPattern :=
  match fuel with
  | 0 => normals.reverse ++ pending.map Prod.fst
  | fuel + 1 =>
      match pending with
      | [] => normals.reverse
      | (term, depth) :: rest =>
          if depth >= cfg.maxSteps then
            evalSpecAux cfg fuel rest (insertUniqueSpec normals term)
          else
            let reducts := specRewriteWithContext cfg term
            if reducts.isEmpty then
              evalSpecAux cfg fuel rest (insertUniqueSpec normals term)
            else
              let pending' := enqueueNextSpec rest (depth + 1) reducts
              evalSpecAux cfg fuel pending' normals

private def runSpec (cfg : FrozenPeTTaConfig) (query : CPattern) : List CPattern :=
  let querySpec := coreToSpecPattern query
  let outSpec := evalSpecAux cfg cfg.maxNodes [(querySpec, 0)] []
  outSpec.map specToCorePattern

private def runSimple (cfg : FrozenPeTTaConfig) (query : CPattern) : List CPattern :=
  let sess := toSession cfg
  Algorithms.MeTTa.Simple.Session.eval sess query

/-! ## Fixed fixtures -/

private def sym (s : String) : CPattern := .apply s []
private def app (f : String) (args : List CPattern) : CPattern := .apply f args

private def cfgSimple : FrozenPeTTaConfig :=
  { rules := [{ lhs := app "f" [sym "a"], rhs := sym "b" }]
    maxSteps := 16
    maxNodes := 512 }

private def cfgNested : FrozenPeTTaConfig :=
  { rules :=
      [ { lhs := app "g" [sym "a"], rhs := app "f" [sym "a"] }
      , { lhs := app "f" [sym "a"], rhs := sym "b" }
      ]
    maxSteps := 16
    maxNodes := 512 }

private def cfgNondet : FrozenPeTTaConfig :=
  { rules :=
      [ { lhs := app "choose" [], rhs := sym "red" }
      , { lhs := app "choose" [], rhs := sym "blue" }
      ]
    maxSteps := 16
    maxNodes := 512 }

private def cfgRelationPremise : FrozenPeTTaConfig :=
  { rules :=
      [ { lhs := app "fromRel" []
          rhs := .fvar "x"
          premises := [.relationQuery "allowed" [.fvar "x"]] }
      ]
    relationFacts :=
      [ { relation := "allowed", tuple := [sym "alpha"] }
      , { relation := "allowed", tuple := [sym "beta"] }
      ]
    maxSteps := 16
    maxNodes := 512 }

private def cfgBuiltinPremise : FrozenPeTTaConfig :=
  { rules :=
      [ { lhs := app "fromBuiltin" []
          rhs := .fvar "x"
          premises := [.relationQuery "palette" [.fvar "x"]] }
      ]
    builtinFacts :=
      [ { relation := "palette", tuple := [sym "warm"] }
      , { relation := "palette", tuple := [sym "cool"] }
      ]
    maxSteps := 16
    maxNodes := 512 }

private def matchSelfRule : FrozenPeTTaRule :=
  { lhs := app "match" [app "&self" [], .fvar "pat", .fvar "tmpl"]
    rhs := .fvar "out"
    premises := [.relationQuery "spaceMatch" [.fvar "pat", .fvar "tmpl", .fvar "out"]] }

private def matchSelfRule2 : FrozenPeTTaRule :=
  { lhs := app "match2" [app "&self" [], .fvar "pat", .fvar "tmpl"]
    rhs := .fvar "tmpl"
    premises := [.relationQuery "spaceMatch" [.fvar "pat", .fvar "tmpl"]] }

private def cfgMatchSelf : FrozenPeTTaConfig :=
  { rules :=
      [matchSelfRule]
    facts := [app "color" [sym "red"], app "color" [sym "blue"]]
    maxSteps := 16
    maxNodes := 512 }

private def cfgMatchSelfFriends : FrozenPeTTaConfig :=
  { rules := [matchSelfRule, matchSelfRule2]
    facts :=
      [ app "friend" [sym "tim", sym "tom"]
      , app "friend" [sym "tom", sym "bob"]
      ]
    maxSteps := 16
    maxNodes := 512 }

private def cfgMatchSelfShared : FrozenPeTTaConfig :=
  { rules := [matchSelfRule, matchSelfRule2]
    facts :=
      [ app "friend" [sym "tim", sym "tom"]
      , app "friend" [sym "tom", sym "bob"]
      , app "friend" [sym "bob", sym "bob"]
      ]
    maxSteps := 16
    maxNodes := 512 }

private def cfgMatchSelfTemplateShare : FrozenPeTTaConfig :=
  { rules := [matchSelfRule]
    facts :=
      [ app "friend" [sym "tim", sym "tom"]
      , app "friend" [sym "tim", sym "bob"]
      ]
    maxSteps := 16
    maxNodes := 512 }

private def cfgIntrinsicArith : FrozenPeTTaConfig :=
  { rules := []
    facts := []
    relationFacts := []
    builtinFacts := []
    maxSteps := 16
    maxNodes := 512 }

private def cfgMatchConj : FrozenPeTTaConfig :=
  { rules := [matchSelfRule]
    facts :=
      [ app "friend" [sym "tim", sym "tom"]
      , app "friend" [sym "tom", sym "tam"]
      , app "friend" [sym "sim", sym "som"]
      , app "friend" [sym "som", sym "sam"]
      ]
    maxSteps := 16
    maxNodes := 512 }

private def cfgMatchSingle : FrozenPeTTaConfig :=
  { rules := [matchSelfRule]
    facts := [app "a" [sym "b"], app "a" [sym "c"]]
    maxSteps := 16
    maxNodes := 512 }

private def matchWuspaceRule : FrozenPeTTaRule :=
  { lhs := app "match" [app "&wuspace" [], .fvar "pat", .fvar "tmpl"]
    rhs := .fvar "out"
    premises := [.relationQuery "spaceMatch" [.fvar "pat", .fvar "tmpl", .fvar "out"]] }

private def cfgMatchNamedSpace : FrozenPeTTaConfig :=
  { rules := [matchWuspaceRule]
    facts := [app "wu" [], app "wu" [sym "42"]]
    maxSteps := 16
    maxNodes := 512 }

private def qSimple : CPattern := app "f" [sym "a"]
private def qNested : CPattern := app "g" [sym "a"]
private def qNondet : CPattern := app "choose" []
private def qNoReduction : CPattern := app "unknown" [sym "arg"]
private def qRelationPremise : CPattern := app "fromRel" []
private def qBuiltinPremise : CPattern := app "fromBuiltin" []
private def qMatchSelf : CPattern :=
  app "match"
    [ app "&self" []
    , app "color" [.fvar "x"]
    , app "picked" [.fvar "x"]
    ]
private def qMatchSelfFriendsAll : CPattern :=
  app "match"
    [ app "&self" []
    , app "friend" [.fvar "a", .fvar "b"]
    , app "edge" [.fvar "a", .fvar "b"]
    ]
private def qMatchSelfFriendsTim : CPattern :=
  app "match"
    [ app "&self" []
    , app "friend" [sym "tim", .fvar "b"]
    , .fvar "b"
    ]
private def qMatchSelf2Arg : CPattern :=
  app "match2"
    [ app "&self" []
    , app "friend" [sym "tim", sym "tom"]
    , app "friendOnly" [sym "tom"]
    ]
private def qMatchSelfMiss : CPattern :=
  app "match"
    [ app "&self" []
    , app "friend" [sym "bob", .fvar "b"]
    , app "edge" [sym "bob", .fvar "b"]
    ]
private def qMatchSelfSharedMiss : CPattern :=
  app "match"
    [ app "&self" []
    , app "friend" [.fvar "b", .fvar "b"]
    , app "diag" [.fvar "b"]
    ]
private def qMatchSelfSharedHit : CPattern :=
  app "match"
    [ app "&self" []
    , app "friend" [.fvar "b", .fvar "b"]
    , app "diag" [.fvar "b"]
    ]
private def qMatchSelfShared2ArgHit : CPattern :=
  app "match2"
    [ app "&self" []
    , app "friend" [.fvar "b", .fvar "b"]
    , app "diag2" [.fvar "b"]
    ]
private def qMatchSelfTemplateShare : CPattern :=
  app "match"
    [ app "&self" []
    , app "friend" [sym "tim", .fvar "b"]
    , app "pair" [.fvar "b", .fvar "b"]
    ]
private def qIntrinsicEqModulo : CPattern :=
  app "==" [sym "0", app "%" [sym "10", sym "5"]]
private def qIntrinsicEqNestedAdd : CPattern :=
  app "==" [app "+" [sym "1", sym "2"], sym "3"]
private def qIntrinsicNeqNestedSub : CPattern :=
  app "!=" [app "-" [sym "7", sym "3"], sym "5"]
private def qIntrinsicCmpNested : CPattern :=
  app "<" [app "+" [sym "1", sym "2"], app "*" [sym "2", sym "2"]]
private def qMatchConj : CPattern :=
  app "match"
    [ app "&self" []
    , app ","
        [ app "friend" [.fvar "a", .fvar "b"]
        , app "friend" [.fvar "b", .fvar "c"]
        ]
    , app "transitive" [.fvar "a", .fvar "b", .fvar "c"]
    ]
private def qMatchSingle : CPattern :=
  app "match"
    [ app "&self" []
    , app "a" [.fvar "x"]
    , app "a" [.fvar "x"]
    ]
private def qMatchNamedSpace : CPattern :=
  app "match"
    [ app "&wuspace" []
    , .fvar "x"
    , .fvar "x"
    ]

private def qSessionMatchSelfAfterAdd : CPattern :=
  app "match"
    [ app "&self" []
    , app "friend" [sym "tim", .fvar "x"]
    , .fvar "x"
    ]

private def qSessionMatchNamedAfterAdd : CPattern :=
  app "match"
    [ app "&wuspace" []
    , app "wu" []
    , app "seen" []
    ]

private def qSessionNestedHideAdd : CPattern :=
  app "hide"
    [ app "Expr"
        [ app "add-atom" [app "&self" [], app "friend" [sym "tim", sym "tom"]]
        , app "add-atom" [app "&self" [], app "friend" [sym "tom", sym "bob"]]
        ]
    ]

private def qSessionNestedHideRemove : CPattern :=
  app "hide"
    [ app "Expr"
        [ app "remove-atom" [app "&self" [], app "friend" [sym "tim", sym "tom"]]
        ]
    ]

private def expectedSimple : List CPattern := [sym "b"]
private def expectedNested : List CPattern := [sym "b"]
private def expectedNondet : List CPattern := [sym "red", sym "blue"]
private def expectedNoReduction : List CPattern := [app "unknown" [sym "arg"]]
private def expectedRelationPremise : List CPattern := [sym "alpha", sym "beta"]
private def expectedBuiltinPremise : List CPattern := [sym "warm", sym "cool"]
private def expectedMatchSelf : List CPattern := [app "picked" [sym "red"], app "picked" [sym "blue"]]
private def expectedMatchSelfFriendsAll : List CPattern :=
  [app "edge" [sym "tim", sym "tom"], app "edge" [sym "tom", sym "bob"]]
private def expectedMatchSelfFriendsTim : List CPattern := [sym "tom"]
private def expectedMatchSelf2Arg : List CPattern := [app "friendOnly" [sym "tom"]]
private def expectedMatchSelfMiss : List CPattern := []
private def expectedMatchSelfSharedMiss : List CPattern := []
private def expectedMatchSelfSharedHit : List CPattern := [app "diag" [sym "bob"]]
private def expectedMatchSelfShared2ArgHit : List CPattern := [app "diag2" [.fvar "b"]]
private def expectedMatchSelfTemplateShare : List CPattern :=
  [app "pair" [sym "tom", sym "tom"], app "pair" [sym "bob", sym "bob"]]
private def expectedIntrinsicTrue : List CPattern := [sym "True"]
private def expectedIntrinsicFalse : List CPattern := [sym "False"]
private def expectedMatchConj : List CPattern :=
  [ app "transitive" [sym "tim", sym "tom", sym "tam"]
  , app "transitive" [sym "sim", sym "som", sym "sam"]
  ]
private def expectedMatchSingle : List CPattern :=
  [app "a" [sym "b"], app "a" [sym "c"]]
private def expectedMatchNamedSpace : List CPattern :=
  [app "wu" [], app "wu" [sym "42"]]
private def expectedSessionMatchSelfAfterAdd : List CPattern := [sym "tom"]
private def expectedSessionMatchNamedAfterAdd : List CPattern := [app "seen" []]
private def expectedSessionNestedMatchAfterAdd : List CPattern := [sym "tom"]
private def expectedSessionNestedMatchAfterRemove : List CPattern := []

private def oracleSpaceMatch (facts : List CPattern) (pat tmpl : CPattern) : List CPattern :=
  let space : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace :=
    { facts := facts.map coreToSpecPattern
      rules := [] }
  (space.spaceMatch
      (coreToSpecPattern pat)
      (coreToSpecPattern tmpl)).map specToCorePattern

private def oracleMatchSelf : List CPattern :=
  oracleSpaceMatch cfgMatchSelf.facts
    (app "color" [.fvar "x"])
    (app "picked" [.fvar "x"])

private def oracleMatchSelfFriendsAll : List CPattern :=
  oracleSpaceMatch cfgMatchSelfFriends.facts
    (app "friend" [.fvar "a", .fvar "b"])
    (app "edge" [.fvar "a", .fvar "b"])

private def oracleMatchSelfFriendsTim : List CPattern :=
  oracleSpaceMatch cfgMatchSelfFriends.facts
    (app "friend" [sym "tim", .fvar "b"])
    (.fvar "b")

private def oracleMatchSelf2Arg : List CPattern :=
  oracleSpaceMatch cfgMatchSelfFriends.facts
    (app "friend" [sym "tim", sym "tom"])
    (app "friendOnly" [sym "tom"])

private def oracleMatchSelfMiss : List CPattern :=
  oracleSpaceMatch cfgMatchSelfFriends.facts
    (app "friend" [sym "bob", .fvar "b"])
    (app "edge" [sym "bob", .fvar "b"])

private def oracleMatchSelfSharedMiss : List CPattern :=
  oracleSpaceMatch cfgMatchSelfFriends.facts
    (app "friend" [.fvar "b", .fvar "b"])
    (app "diag" [.fvar "b"])

private def oracleMatchSelfSharedHit : List CPattern :=
  oracleSpaceMatch cfgMatchSelfShared.facts
    (app "friend" [.fvar "b", .fvar "b"])
    (app "diag" [.fvar "b"])

private def oracleMatchSelfShared2ArgHit : List CPattern :=
  runSpec cfgMatchSelfShared qMatchSelfShared2ArgHit

private def oracleMatchSelfTemplateShare : List CPattern :=
  oracleSpaceMatch cfgMatchSelfTemplateShare.facts
    (app "friend" [sym "tim", .fvar "b"])
    (app "pair" [.fvar "b", .fvar "b"])

private def oracleMatchConj : List CPattern :=
  runSpec cfgMatchConj qMatchConj

private def oracleMatchSingle : List CPattern :=
  runSpec cfgMatchSingle qMatchSingle

private def oracleMatchNamedSpace : List CPattern :=
  runSpec cfgMatchNamedSpace qMatchNamedSpace

def checkSimple : Bool :=
  decide (runSimple cfgSimple qSimple = runSpec cfgSimple qSimple)

def checkNested : Bool :=
  decide (runSimple cfgNested qNested = runSpec cfgNested qNested)

def checkNondet : Bool :=
  decide (runSimple cfgNondet qNondet = runSpec cfgNondet qNondet)

def checkNoReduction : Bool :=
  decide (runSimple cfgSimple qNoReduction = runSpec cfgSimple qNoReduction)

def checkRelationPremise : Bool :=
  decide (runSimple cfgRelationPremise qRelationPremise =
            runSpec cfgRelationPremise qRelationPremise)

def checkBuiltinPremise : Bool :=
  decide (runSimple cfgBuiltinPremise qBuiltinPremise =
            runSpec cfgBuiltinPremise qBuiltinPremise)

def checkMatchSelf : Bool :=
  decide (runSimple cfgMatchSelf qMatchSelf = oracleMatchSelf)

def checkMatchSelfFriendsAll : Bool :=
  decide (runSimple cfgMatchSelfFriends qMatchSelfFriendsAll = oracleMatchSelfFriendsAll)

def checkMatchSelfFriendsTim : Bool :=
  decide (runSimple cfgMatchSelfFriends qMatchSelfFriendsTim = oracleMatchSelfFriendsTim)

def checkMatchSelf2Arg : Bool :=
  decide (runSimple cfgMatchSelfFriends qMatchSelf2Arg = oracleMatchSelf2Arg)

def checkMatchSelfMiss : Bool :=
  decide (runSimple cfgMatchSelfFriends qMatchSelfMiss = oracleMatchSelfMiss)

def checkMatchSelfSharedMiss : Bool :=
  decide (runSimple cfgMatchSelfFriends qMatchSelfSharedMiss = oracleMatchSelfSharedMiss)

def checkMatchSelfSharedHit : Bool :=
  decide (runSimple cfgMatchSelfShared qMatchSelfSharedHit = oracleMatchSelfSharedHit)

def checkMatchSelfShared2ArgHit : Bool :=
  decide (runSimple cfgMatchSelfShared qMatchSelfShared2ArgHit = expectedMatchSelfShared2ArgHit)

def checkMatchSelfTemplateShare : Bool :=
  decide (runSimple cfgMatchSelfTemplateShare qMatchSelfTemplateShare = oracleMatchSelfTemplateShare)

def checkIntrinsicEqModulo : Bool :=
  decide (runSimple cfgIntrinsicArith qIntrinsicEqModulo = expectedIntrinsicTrue)

def checkIntrinsicEqNestedAdd : Bool :=
  decide (runSimple cfgIntrinsicArith qIntrinsicEqNestedAdd = expectedIntrinsicTrue)

def checkIntrinsicNeqNestedSub : Bool :=
  decide (runSimple cfgIntrinsicArith qIntrinsicNeqNestedSub = expectedIntrinsicTrue)

def checkIntrinsicCmpNested : Bool :=
  decide (runSimple cfgIntrinsicArith qIntrinsicCmpNested = expectedIntrinsicTrue)

def checkMatchConj : Bool :=
  decide (runSimple cfgMatchConj qMatchConj = expectedMatchConj)

def checkMatchSingle : Bool :=
  decide (runSimple cfgMatchSingle qMatchSingle = expectedMatchSingle)

def checkMatchNamedSpace : Bool :=
  decide (runSimple cfgMatchNamedSpace qMatchNamedSpace = expectedMatchNamedSpace)

private def runStmt (sess : Algorithms.MeTTa.Simple.Session)
    (stmt : Algorithms.MeTTa.Simple.Session.SyntaxStmt) :
    Algorithms.MeTTa.Simple.Session × List CPattern :=
  Algorithms.MeTTa.Simple.Session.applyStmt sess stmt

private def checkSessionAddAndMatch (space : CPattern) (fact query : CPattern)
    (expected : List CPattern) : Bool :=
  let sess0 := Algorithms.MeTTa.Simple.Session.new (toSpecBundle cfgSimple)
  let (sess1, _) := runStmt sess0 (.eval (app "add-atom" [space, fact]))
  let (_sess2, out) := runStmt sess1 (.eval query)
  decide (out = expected)

def checkSessionAddAtomMatchSelf : Bool :=
  checkSessionAddAndMatch
    (app "&self" [])
    (app "friend" [sym "tim", sym "tom"])
    qSessionMatchSelfAfterAdd
    expectedSessionMatchSelfAfterAdd

def checkSessionAddAtomMatchNamed : Bool :=
  checkSessionAddAndMatch
    (app "&wuspace" [])
    (app "wu" [])
    qSessionMatchNamedAfterAdd
    expectedSessionMatchNamedAfterAdd

def checkSessionNestedSideEffects : Bool :=
  let sess0 := Algorithms.MeTTa.Simple.Session.new (toSpecBundle cfgSimple)
  let (sess1, _) := runStmt sess0 (.defineEq (app "hide" [.fvar "x"]) (sym "empty"))
  let (sess2, _) := runStmt sess1 (.eval qSessionNestedHideAdd)
  let (_sess3, out1) := runStmt sess2 (.eval qSessionMatchSelfAfterAdd)
  decide (out1 = expectedSessionNestedMatchAfterAdd)

def checkSessionNestedRemoveSideEffects : Bool :=
  let sess0 := Algorithms.MeTTa.Simple.Session.new (toSpecBundle cfgSimple)
  let (sess1, _) := runStmt sess0 (.defineEq (app "hide" [.fvar "x"]) (sym "empty"))
  let (sess2, _) := runStmt sess1 (.eval qSessionNestedHideAdd)
  let (sess3, _) := runStmt sess2 (.eval qSessionNestedHideRemove)
  let (_sess4, out2) := runStmt sess3 (.eval qSessionMatchSelfAfterAdd)
  decide (out2 = expectedSessionNestedMatchAfterRemove)

def checkExpectedSimple : Bool :=
  decide (runSimple cfgSimple qSimple = expectedSimple)

def checkExpectedNested : Bool :=
  decide (runSimple cfgNested qNested = expectedNested)

def checkExpectedNondet : Bool :=
  decide (runSimple cfgNondet qNondet = expectedNondet)

def checkExpectedNoReduction : Bool :=
  decide (runSimple cfgSimple qNoReduction = expectedNoReduction)

def checkExpectedRelationPremise : Bool :=
  decide (runSimple cfgRelationPremise qRelationPremise = expectedRelationPremise)

def checkExpectedBuiltinPremise : Bool :=
  decide (runSimple cfgBuiltinPremise qBuiltinPremise = expectedBuiltinPremise)

def checkExpectedMatchSelf : Bool :=
  decide (runSimple cfgMatchSelf qMatchSelf = expectedMatchSelf)

def checkExpectedMatchSelfFriendsAll : Bool :=
  decide (runSimple cfgMatchSelfFriends qMatchSelfFriendsAll = expectedMatchSelfFriendsAll)

def checkExpectedMatchSelfFriendsTim : Bool :=
  decide (runSimple cfgMatchSelfFriends qMatchSelfFriendsTim = expectedMatchSelfFriendsTim)

def checkExpectedMatchSelf2Arg : Bool :=
  decide (runSimple cfgMatchSelfFriends qMatchSelf2Arg = expectedMatchSelf2Arg)

def checkExpectedMatchSelfMiss : Bool :=
  decide (runSimple cfgMatchSelfFriends qMatchSelfMiss = expectedMatchSelfMiss)

def checkExpectedMatchSelfSharedMiss : Bool :=
  decide (runSimple cfgMatchSelfFriends qMatchSelfSharedMiss = expectedMatchSelfSharedMiss)

def checkExpectedMatchSelfSharedHit : Bool :=
  decide (runSimple cfgMatchSelfShared qMatchSelfSharedHit = expectedMatchSelfSharedHit)

def checkExpectedMatchSelfShared2ArgHit : Bool :=
  decide (runSimple cfgMatchSelfShared qMatchSelfShared2ArgHit = expectedMatchSelfShared2ArgHit)

def checkExpectedMatchSelfTemplateShare : Bool :=
  decide (runSimple cfgMatchSelfTemplateShare qMatchSelfTemplateShare = expectedMatchSelfTemplateShare)

def checkExpectedMatchConj : Bool :=
  decide (runSimple cfgMatchConj qMatchConj = expectedMatchConj)

def checkExpectedMatchSingle : Bool :=
  decide (runSimple cfgMatchSingle qMatchSingle = expectedMatchSingle)

def checkExpectedMatchNamedSpace : Bool :=
  decide (runSimple cfgMatchNamedSpace qMatchNamedSpace = expectedMatchNamedSpace)

/-! ## Cross-package translation invariants -/

private def samplePatterns : List CPattern :=
  [ .bvar 0
  , .fvar "x"
  , app "f" [sym "a", .fvar "y"]
  , .lambda (.apply "id" [.bvar 0])
  , .multiLambda 2 (.apply "pair" [.bvar 1, .bvar 0])
  , .subst (.apply "body" [.bvar 0]) (sym "r")
  , .collection .hashBag [sym "a", .fvar "rest"] (some "tail")
  ]

def checkPatternRoundTrip : Bool :=
  samplePatterns.all fun p =>
    decide (specToCorePattern (coreToSpecPattern p) = p)

def checkRuleRoundTrip : Bool :=
  let rules := (toLanguageDef cfgRelationPremise).rewrites ++ (toLanguageDef cfgBuiltinPremise).rewrites
  rules.all fun r =>
    decide (specToCoreRewriteRule (coreToSpecRewriteRule r) = r)

def checkLanguageRoundTrip : Bool :=
  let lang := toLanguageDef cfgRelationPremise
  coreLanguageEq (specToCoreLanguage (coreToSpecLanguage lang)) lang

def checkTupleRoundTrip : Bool :=
  let rows := cfgRelationPremise.relationFacts ++ cfgBuiltinPremise.builtinFacts
  rows.all fun row =>
    decide ((coreTupleToSpecRow row).2.map specToCorePattern = row.tuple)

def translationInvariantsPass : Bool :=
  checkPatternRoundTrip &&
  checkRuleRoundTrip &&
  checkLanguageRoundTrip &&
  checkTupleRoundTrip

/-! ## Theorem-level conformance scaffolding (non-native_decide) -/

theorem simple_conformance_of_check (h : checkSimple = true) :
    runSimple cfgSimple qSimple = runSpec cfgSimple qSimple := by
  exact decide_eq_true_eq.mp (by simpa [checkSimple] using h)

theorem nondet_conformance_of_check (h : checkNondet = true) :
    runSimple cfgNondet qNondet = runSpec cfgNondet qNondet := by
  exact decide_eq_true_eq.mp (by simpa [checkNondet] using h)

theorem premise_conformance_of_check (h : checkRelationPremise = true) :
    runSimple cfgRelationPremise qRelationPremise =
      runSpec cfgRelationPremise qRelationPremise := by
  exact decide_eq_true_eq.mp (by simpa [checkRelationPremise] using h)

theorem expected_simple_of_check (h : checkExpectedSimple = true) :
    runSimple cfgSimple qSimple = expectedSimple := by
  exact decide_eq_true_eq.mp (by simpa [checkExpectedSimple] using h)

theorem expected_nondet_of_check (h : checkExpectedNondet = true) :
    runSimple cfgNondet qNondet = expectedNondet := by
  exact decide_eq_true_eq.mp (by simpa [checkExpectedNondet] using h)

theorem expected_premise_of_check (h : checkExpectedRelationPremise = true) :
    runSimple cfgRelationPremise qRelationPremise = expectedRelationPremise := by
  exact decide_eq_true_eq.mp (by simpa [checkExpectedRelationPremise] using h)

theorem match_oracle_conformance_of_check (h : checkMatchSelf = true) :
    runSimple cfgMatchSelf qMatchSelf = oracleMatchSelf := by
  exact decide_eq_true_eq.mp (by simpa [checkMatchSelf] using h)

theorem match2_oracle_conformance_of_check (h : checkMatchSelf2Arg = true) :
    runSimple cfgMatchSelfFriends qMatchSelf2Arg = oracleMatchSelf2Arg := by
  exact decide_eq_true_eq.mp (by simpa [checkMatchSelf2Arg] using h)

theorem intrinsic_eq_modulo_conformance_of_check (h : checkIntrinsicEqModulo = true) :
    runSimple cfgIntrinsicArith qIntrinsicEqModulo = expectedIntrinsicTrue := by
  exact decide_eq_true_eq.mp (by simpa [checkIntrinsicEqModulo] using h)

theorem intrinsic_eq_nested_add_conformance_of_check (h : checkIntrinsicEqNestedAdd = true) :
    runSimple cfgIntrinsicArith qIntrinsicEqNestedAdd = expectedIntrinsicTrue := by
  exact decide_eq_true_eq.mp (by simpa [checkIntrinsicEqNestedAdd] using h)

theorem intrinsic_cmp_nested_conformance_of_check (h : checkIntrinsicCmpNested = true) :
    runSimple cfgIntrinsicArith qIntrinsicCmpNested = expectedIntrinsicTrue := by
  exact decide_eq_true_eq.mp (by simpa [checkIntrinsicCmpNested] using h)

theorem translation_invariants_hold_of_check (h : translationInvariantsPass = true) :
    checkPatternRoundTrip = true ∧
    checkRuleRoundTrip = true ∧
    checkLanguageRoundTrip = true ∧
    checkTupleRoundTrip = true := by
  simp [translationInvariantsPass, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨hPattern, hRule⟩, hLang⟩, hTuple⟩
  exact ⟨hPattern, hRule, hLang, hTuple⟩

/-! ## Profile export/import checksum drift tests -/

private def roundTripRuleViaSpec (r : FrozenPeTTaRule) : FrozenPeTTaRule :=
  let lhs' := specToCorePattern (coreToSpecPattern r.lhs)
  let rhs' := specToCorePattern (coreToSpecPattern r.rhs)
  let premises' := r.premises.map fun prem =>
    match prem with
    | .relationQuery rel args =>
        .relationQuery rel (args.map (fun a => specToCorePattern (coreToSpecPattern a)))
  { lhs := lhs', rhs := rhs', premises := premises' }

private def roundTripTupleViaSpec (row : RelationTuple) : RelationTuple :=
  let rowSpec := coreTupleToSpecRow row
  { relation := rowSpec.1
    tuple := rowSpec.2.map specToCorePattern }

private def roundTripConfigViaSpec (cfg : FrozenPeTTaConfig) : FrozenPeTTaConfig :=
  { rules := cfg.rules.map roundTripRuleViaSpec
    facts := cfg.facts.map (fun p => specToCorePattern (coreToSpecPattern p))
    relationFacts := cfg.relationFacts.map roundTripTupleViaSpec
    builtinFacts := cfg.builtinFacts.map roundTripTupleViaSpec
    maxSteps := cfg.maxSteps
    maxNodes := cfg.maxNodes }

private def checksumPair (cfg : FrozenPeTTaConfig) : Nat × Nat :=
  let chkExport := Algorithms.MeTTa.ProfileChecksum.checksumFrozenPeTTaConfig cfg
  let chkImport := Algorithms.MeTTa.ProfileChecksum.checksumFrozenPeTTaConfig (roundTripConfigViaSpec cfg)
  (chkExport, chkImport)

def checkChecksumSimple : Bool :=
  let p := checksumPair cfgSimple
  decide (p.1 = p.2)

def checkChecksumNondet : Bool :=
  let p := checksumPair cfgNondet
  decide (p.1 = p.2)

def checkChecksumMatch : Bool :=
  let p := checksumPair cfgMatchSelf
  decide (p.1 = p.2)

def checkChecksumMatchFriends : Bool :=
  let p := checksumPair cfgMatchSelfFriends
  decide (p.1 = p.2)

def checkChecksumMatchShared : Bool :=
  let p := checksumPair cfgMatchSelfShared
  decide (p.1 = p.2)

def checksumChecksPass : Bool :=
  checkChecksumSimple &&
  checkChecksumNondet &&
  checkChecksumMatch &&
  checkChecksumMatchFriends &&
  checkChecksumMatchShared

def allChecks : List (String × Bool) :=
  [ ("simple", checkSimple)
  , ("nested", checkNested)
  , ("nondet", checkNondet)
  , ("noReduction", checkNoReduction)
  , ("relationPremise", checkRelationPremise)
  , ("builtinPremise", checkBuiltinPremise)
  , ("matchSelf", checkMatchSelf)
  , ("matchSelfFriendsAll", checkMatchSelfFriendsAll)
  , ("matchSelfFriendsTim", checkMatchSelfFriendsTim)
  , ("matchSelf2Arg", checkMatchSelf2Arg)
  , ("matchSelfMiss", checkMatchSelfMiss)
  , ("matchSelfSharedMiss", checkMatchSelfSharedMiss)
  , ("matchSelfSharedHit", checkMatchSelfSharedHit)
  , ("matchSelfShared2ArgHit", checkMatchSelfShared2ArgHit)
  , ("matchSelfTemplateShare", checkMatchSelfTemplateShare)
  , ("intrinsicEqModulo", checkIntrinsicEqModulo)
  , ("intrinsicEqNestedAdd", checkIntrinsicEqNestedAdd)
  , ("intrinsicNeqNestedSub", checkIntrinsicNeqNestedSub)
  , ("intrinsicCmpNested", checkIntrinsicCmpNested)
  , ("matchConj", checkMatchConj)
  , ("matchSingle", checkMatchSingle)
  , ("matchNamedSpace", checkMatchNamedSpace)
  , ("sessionAddAtomMatchSelf", checkSessionAddAtomMatchSelf)
  , ("sessionAddAtomMatchNamed", checkSessionAddAtomMatchNamed)
  , ("sessionNestedSideEffects", checkSessionNestedSideEffects)
  , ("sessionNestedRemoveSideEffects", checkSessionNestedRemoveSideEffects)
  , ("expectedSimple", checkExpectedSimple)
  , ("expectedNested", checkExpectedNested)
  , ("expectedNondet", checkExpectedNondet)
  , ("expectedNoReduction", checkExpectedNoReduction)
  , ("expectedRelationPremise", checkExpectedRelationPremise)
  , ("expectedBuiltinPremise", checkExpectedBuiltinPremise)
  , ("expectedMatchSelf", checkExpectedMatchSelf)
  , ("expectedMatchSelfFriendsAll", checkExpectedMatchSelfFriendsAll)
  , ("expectedMatchSelfFriendsTim", checkExpectedMatchSelfFriendsTim)
  , ("expectedMatchSelf2Arg", checkExpectedMatchSelf2Arg)
  , ("expectedMatchSelfMiss", checkExpectedMatchSelfMiss)
  , ("expectedMatchSelfSharedMiss", checkExpectedMatchSelfSharedMiss)
  , ("expectedMatchSelfSharedHit", checkExpectedMatchSelfSharedHit)
  , ("expectedMatchSelfShared2ArgHit", checkExpectedMatchSelfShared2ArgHit)
  , ("expectedMatchSelfTemplateShare", checkExpectedMatchSelfTemplateShare)
  , ("expectedMatchConj", checkExpectedMatchConj)
  , ("expectedMatchSingle", checkExpectedMatchSingle)
  , ("expectedMatchNamedSpace", checkExpectedMatchNamedSpace)
  , ("patternRoundTrip", checkPatternRoundTrip)
  , ("ruleRoundTrip", checkRuleRoundTrip)
  , ("languageRoundTrip", checkLanguageRoundTrip)
  , ("tupleRoundTrip", checkTupleRoundTrip)
  , ("checksumSimple", checkChecksumSimple)
  , ("checksumNondet", checkChecksumNondet)
  , ("checksumMatch", checkChecksumMatch)
  , ("checksumMatchFriends", checkChecksumMatchFriends)
  , ("checksumMatchShared", checkChecksumMatchShared)
  ]

def allChecksPass : Bool :=
  allChecks.all (fun c => c.2)

#eval ("runtimeSimple", runSimple cfgSimple qSimple)
#eval ("specSimple", runSpec cfgSimple qSimple)
#eval ("runtimeNested", runSimple cfgNested qNested)
#eval ("specNested", runSpec cfgNested qNested)
#eval ("runtimeNondet", runSimple cfgNondet qNondet)
#eval ("specNondet", runSpec cfgNondet qNondet)
#eval ("runtimeNoReduction", runSimple cfgSimple qNoReduction)
#eval ("specNoReduction", runSpec cfgSimple qNoReduction)
#eval ("runtimeRelationPremise", runSimple cfgRelationPremise qRelationPremise)
#eval ("specRelationPremise", runSpec cfgRelationPremise qRelationPremise)
#eval ("runtimeBuiltinPremise", runSimple cfgBuiltinPremise qBuiltinPremise)
#eval ("specBuiltinPremise", runSpec cfgBuiltinPremise qBuiltinPremise)
#eval ("runtimeMatchSelf", runSimple cfgMatchSelf qMatchSelf)
#eval ("oracleMatchSelf", oracleMatchSelf)
#eval ("runtimeMatchSelfFriendsAll", runSimple cfgMatchSelfFriends qMatchSelfFriendsAll)
#eval ("oracleMatchSelfFriendsAll", oracleMatchSelfFriendsAll)
#eval ("runtimeMatchSelfFriendsTim", runSimple cfgMatchSelfFriends qMatchSelfFriendsTim)
#eval ("oracleMatchSelfFriendsTim", oracleMatchSelfFriendsTim)
#eval ("runtimeMatchSelf2Arg", runSimple cfgMatchSelfFriends qMatchSelf2Arg)
#eval ("oracleMatchSelf2Arg", oracleMatchSelf2Arg)
#eval ("runtimeMatchSelfMiss", runSimple cfgMatchSelfFriends qMatchSelfMiss)
#eval ("oracleMatchSelfMiss", oracleMatchSelfMiss)
#eval ("runtimeMatchSelfSharedMiss", runSimple cfgMatchSelfFriends qMatchSelfSharedMiss)
#eval ("oracleMatchSelfSharedMiss", oracleMatchSelfSharedMiss)
#eval ("runtimeMatchSelfSharedHit", runSimple cfgMatchSelfShared qMatchSelfSharedHit)
#eval ("oracleMatchSelfSharedHit", oracleMatchSelfSharedHit)
#eval ("runtimeMatchSelfShared2ArgHit", runSimple cfgMatchSelfShared qMatchSelfShared2ArgHit)
#eval ("oracleMatchSelfShared2ArgHit", oracleMatchSelfShared2ArgHit)
#eval ("runtimeMatchSelfTemplateShare", runSimple cfgMatchSelfTemplateShare qMatchSelfTemplateShare)
#eval ("oracleMatchSelfTemplateShare", oracleMatchSelfTemplateShare)
#eval ("runtimeIntrinsicEqModulo", runSimple cfgIntrinsicArith qIntrinsicEqModulo)
#eval ("runtimeIntrinsicEqNestedAdd", runSimple cfgIntrinsicArith qIntrinsicEqNestedAdd)
#eval ("runtimeIntrinsicNeqNestedSub", runSimple cfgIntrinsicArith qIntrinsicNeqNestedSub)
#eval ("runtimeIntrinsicCmpNested", runSimple cfgIntrinsicArith qIntrinsicCmpNested)
#eval ("runtimeMatchConj", runSimple cfgMatchConj qMatchConj)
#eval ("oracleMatchConj", oracleMatchConj)
#eval ("runtimeMatchSingle", runSimple cfgMatchSingle qMatchSingle)
#eval ("oracleMatchSingle", oracleMatchSingle)
#eval ("runtimeMatchNamedSpace", runSimple cfgMatchNamedSpace qMatchNamedSpace)
#eval ("oracleMatchNamedSpace", oracleMatchNamedSpace)
#eval ("translationInvariantsPass", translationInvariantsPass)
#eval ("checksumPairSimple", checksumPair cfgSimple)
#eval ("checksumPairNondet", checksumPair cfgNondet)
#eval ("checksumPairMatch", checksumPair cfgMatchSelf)
#eval ("checksumPairMatchFriends", checksumPair cfgMatchSelfFriends)
#eval ("checksumPairMatchShared", checksumPair cfgMatchSelfShared)
#eval ("checksumChecksPass", checksumChecksPass)
#eval allChecks
#eval ("allChecksPass", allChecksPass)

end Mettapedia.Conformance.SimplePeTTa
