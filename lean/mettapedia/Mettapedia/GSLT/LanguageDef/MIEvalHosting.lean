import Mettapedia.GSLT.LanguageDef.DerivedHosting
import Mettapedia.GSLT.LanguageDef.MIEvalEncoding

/-!
# MeTTa evaluator tables as hosted LanguageDef reachability inputs

This module is a mechanical adapter from the LeaTTa/MOPS `RewriteDecl` table
shape used by `MIEvalEncoding` into the `LanguageDef` rewrite table consumed by
generic derived hosting.  It does not define a checker and it does not validate
execution traces; it only exposes the same rewrite data to the generic
table-to-signature lowering.
-/

namespace Mettapedia.GSLT.LanguageDef.MIEvalHosting

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.DerivedHosting

abbrev LDPattern := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
abbrev LDRewriteRule := Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule
abbrev LDLanguageDef := Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef
abbrev LDGrammarRule := Mettapedia.OSLF.MeTTaIL.Syntax.GrammarRule

mutual
  def mettaASTToPattern? : MeTTaIL.AST → Option LDPattern
    | .var (.base v) => some (.fvar v)
    | .var (.qualified _ _) => none
    | .sexp (.id head) args => do
        let ps ← mettaASTListToPatterns? args
        some (.apply head ps)
    | .sexp _ _ => none
    | .subst _ _ _ => none

  def mettaASTListToPatterns? : List MeTTaIL.AST →
      Option (List LDPattern)
    | [] => some []
    | term :: rest => do
        let p ← mettaASTToPattern? term
        let ps ← mettaASTListToPatterns? rest
        some (p :: ps)
end

def rewriteDeclToLanguageRewrite?
    (rd : MeTTaIL.RewriteDecl) : Option LDRewriteRule :=
  match rd.rw with
  | .base lhs rhs => do
      let left ← mettaASTToPattern? lhs
      let right ← mettaASTToPattern? rhs
      return Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule.mk
        rd.name [] [] left right
  | .ctx _ _ => none

def rewriteDeclsToLanguageDefWithTerms
    (langName : String) (termRules : List LDGrammarRule)
    (rws : List MeTTaIL.RewriteDecl) : LDLanguageDef :=
  { name := langName
    types := ["MTerm"]
    terms := termRules
    equations := []
    rewrites := rws.filterMap rewriteDeclToLanguageRewrite? }

def rewriteDeclsToLanguageDef
    (langName : String) (rws : List MeTTaIL.RewriteDecl) : LDLanguageDef :=
  rewriteDeclsToLanguageDefWithTerms langName [] rws

def mettaNullaryTermRule (label : String) : LDGrammarRule :=
  Mettapedia.OSLF.MeTTaIL.Syntax.GrammarRule.mk label "MTerm" [] [] none

def mettaUnaryTermRule (label argName : String) : LDGrammarRule :=
  Mettapedia.OSLF.MeTTaIL.Syntax.GrammarRule.mk label "MTerm"
    [Mettapedia.OSLF.MeTTaIL.Syntax.TermParam.simple argName
      (.base "MTerm")]
    [] none

def peanoCorpusTermRules : List LDGrammarRule :=
  [mettaNullaryTermRule "Z", mettaUnaryTermRule "S" "n"]

def addDeclsLanguageDef : LDLanguageDef :=
  rewriteDeclsToLanguageDef "MeTTaAdd"
    Mettapedia.GSLT.LanguageDef.MIEvalEncoding.addDecls

def revDeclsLanguageDef : LDLanguageDef :=
  rewriteDeclsToLanguageDefWithTerms "MeTTaRev" peanoCorpusTermRules
    Mettapedia.GSLT.LanguageDef.MIEvalEncoding.revDecls

def addDeclsReachabilitySig :
    Mettapedia.GSLT.LanguageDef.LFTyping.Sig :=
  languageDefToReachabilityLFSig addDeclsLanguageDef

def revDeclsReachabilitySig :
    Mettapedia.GSLT.LanguageDef.LFTyping.Sig :=
  languageDefToReachabilityLFSig revDeclsLanguageDef

def addDeclsKernelReachabilitySig :
    Mettapedia.GSLT.LanguageDef.LFTyping.Sig :=
  languageDefToKernelReachabilityLFSig addDeclsLanguageDef

def revDeclsKernelReachabilitySig :
    Mettapedia.GSLT.LanguageDef.LFTyping.Sig :=
  languageDefToKernelReachabilityLFSig revDeclsLanguageDef

def addDeclsKernelReachabilitySigMettaExpr : String :=
  renderLFSigAsKernelExpr addDeclsKernelReachabilitySig

def revDeclsKernelReachabilitySigMettaExpr : String :=
  renderLFSigAsKernelExpr revDeclsKernelReachabilitySig

def lfDeclName : Mettapedia.GSLT.LanguageDef.LFTyping.Decl → String
  | .const n _ => n
  | .defn n _ _ => n

def addZeroPattern : LDPattern := .apply "Z" []

def addOnePattern : LDPattern := .apply "S" [addZeroPattern]

def addTwoPattern : LDPattern := .apply "S" [addOnePattern]

def addThreePattern : LDPattern := .apply "S" [addTwoPattern]

def addZOnePattern : LDPattern :=
  .apply "add" [addZeroPattern, addOnePattern]

def addOneOnePattern : LDPattern :=
  .apply "add" [addOnePattern, addOnePattern]

def addOneOneAfterRootPattern : LDPattern :=
  .apply "S" [addZOnePattern]

def addTwoOnePattern : LDPattern :=
  .apply "add" [addTwoPattern, addOnePattern]

def addTwoOneAfterRootPattern : LDPattern :=
  .apply "S" [addOneOnePattern]

def addTwoOneAfterInnerPattern : LDPattern :=
  .apply "S" [addOneOneAfterRootPattern]

def addZRule : LDRewriteRule :=
  RewriteRule.mk "add-z" [] [] (.apply "add" [addZeroPattern, .fvar "n"])
    (.fvar "n")

def addSRule : LDRewriteRule :=
  RewriteRule.mk "add-s" [] []
    (.apply "add" [.apply "S" [.fvar "m"], .fvar "n"])
    (.apply "S" [.apply "add" [.fvar "m", .fvar "n"]])

def nilValuePattern : LDPattern := .apply "Nil" []

def consValuePattern (x xs : LDPattern) : LDPattern :=
  .apply "Cons" [x, xs]

def list0Pattern : LDPattern := consValuePattern addZeroPattern nilValuePattern

def revCallPattern (xs : LDPattern) : LDPattern := .apply "rev" [xs]

def appendCallPattern (xs ys : LDPattern) : LDPattern :=
  .apply "listAppend" [xs, ys]

def revRevList0Pattern : LDPattern :=
  revCallPattern (revCallPattern list0Pattern)

def revList0AfterRootPattern : LDPattern :=
  appendCallPattern (revCallPattern nilValuePattern) list0Pattern

def revList0AfterInnerPattern : LDPattern :=
  appendCallPattern nilValuePattern list0Pattern

def revRevList0AfterInnerRootPattern : LDPattern :=
  revCallPattern revList0AfterRootPattern

def revRevList0AfterInnerNilPattern : LDPattern :=
  revCallPattern revList0AfterInnerPattern

def revAppendNilRule : LDRewriteRule :=
  RewriteRule.mk "append-nil" [] []
    (.apply "listAppend" [nilValuePattern, .fvar "ys"]) (.fvar "ys")

def revAppendConsRule : LDRewriteRule :=
  RewriteRule.mk "append-cons" [] []
    (.apply "listAppend"
      [consValuePattern (.fvar "x") (.fvar "xs"), .fvar "ys"])
    (consValuePattern (.fvar "x")
      (appendCallPattern (.fvar "xs") (.fvar "ys")))

def revNilRule : LDRewriteRule :=
  RewriteRule.mk "rev-nil" [] [] (revCallPattern nilValuePattern)
    nilValuePattern

def revConsRule : LDRewriteRule :=
  RewriteRule.mk "rev-cons" [] []
    (revCallPattern (consValuePattern (.fvar "x") (.fvar "xs")))
    (appendCallPattern (revCallPattern (.fvar "xs"))
      (consValuePattern (.fvar "x") nilValuePattern))

theorem addDeclsLanguageDef_rewrites_eq :
    addDeclsLanguageDef.rewrites = [addZRule, addSRule] := by
  rfl

@[simp] theorem addDeclsLanguageDef_reflectivePresentations :
    addDeclsLanguageDef.reflectivePresentations = [] := by
  rfl

@[simp] theorem revDeclsLanguageDef_reflectivePresentations :
    revDeclsLanguageDef.reflectivePresentations = [] := by
  rfl

theorem revDeclsLanguageDef_rewrites_eq :
    revDeclsLanguageDef.rewrites =
      [revAppendNilRule, revAppendConsRule, revNilRule, revConsRule] := by
  rfl

theorem addDeclsLanguageDef_rewrite_names :
    addDeclsLanguageDef.rewrites.map (·.name) = ["add-z", "add-s"] := by
  rfl

theorem addDeclsLanguageDef_rewrite_count :
    addDeclsLanguageDef.rewrites.length =
      Mettapedia.GSLT.LanguageDef.MIEvalEncoding.addDecls.length := by
  rfl

theorem revDeclsLanguageDef_rewrite_names :
    revDeclsLanguageDef.rewrites.map (·.name) =
      ["append-nil", "append-cons", "rev-nil", "rev-cons"] := by
  rfl

theorem revDeclsLanguageDef_rewrite_count :
    revDeclsLanguageDef.rewrites.length =
      Mettapedia.GSLT.LanguageDef.MIEvalEncoding.revDecls.length := by
  rfl

theorem addDeclsLanguageDef_name_literals :
    languageNameLits addDeclsLanguageDef = ["add", "Z", "n", "S", "m"] := by
  rfl

theorem revDeclsLanguageDef_name_literals :
    languageNameLits revDeclsLanguageDef =
      ["Z", "S", "listAppend", "Nil", "ys", "Cons", "x", "xs", "rev"] := by
  rfl

theorem addDeclsLanguageDef_index_literals :
    languageIndexLits addDeclsLanguageDef = [] := by
  rfl

theorem revDeclsLanguageDef_index_literals :
    languageIndexLits revDeclsLanguageDef = [] := by
  rfl

theorem mettaASTToPattern_add_z_one :
    mettaASTToPattern?
        (Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gAdd
          Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gZ
          Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gOne) =
      some addZOnePattern := by
  rfl

theorem sourceStep_add_z_one :
    Mettapedia.GSLT.LanguageDef.MIEvalEncoding.stepBaseStep?
        Mettapedia.GSLT.LanguageDef.MIEvalEncoding.addDecls
        (Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gAdd
          Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gZ
          Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gOne) =
      some Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gOne := by
  rfl

theorem addDeclsLanguageDef_reduces_add_z_one :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReduces addDeclsLanguageDef
      addZOnePattern addOnePattern := by
  change Step (engineBasePremises RelationEnv.empty) addDeclsLanguageDef
    addZOnePattern addOnePattern
  refine step_of_rule (rule := addZRule)
    (initialBindings := [("n", addOnePattern)])
    (finalBindings := [("n", addOnePattern)])
    ?hr ?hbs0 .nil ?hprem ?hq
  · rw [addDeclsLanguageDef_rewrites_eq]
    simp
  · unfold addZRule addZOnePattern addOnePattern addZeroPattern
    simp [Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
      Mettapedia.OSLF.MeTTaIL.Match.matchArgs,
      Mettapedia.OSLF.MeTTaIL.Match.mergeBindings]
  · unfold addZRule addOnePattern addZeroPattern
    simp [Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv]
  · unfold addZRule addOnePattern addZeroPattern
    simp [applyBindingsForRule, declarationForRule?, addDeclsLanguageDef,
      rewriteDeclsToLanguageDef, rewriteDeclsToLanguageDefWithTerms,
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings]

theorem addDeclsLanguageDef_not_reduces_add_z_one_to_zero :
    ¬ Mettapedia.OSLF.Framework.TypeSynthesis.langReduces addDeclsLanguageDef
      addZOnePattern addZeroPattern := by
  intro h
  change Step (engineBasePremises RelationEnv.empty) addDeclsLanguageDef
    addZOnePattern addZeroPattern at h
  obtain ⟨_, h⟩ := h
  cases h with
  | @rule _ _ _ r bs0 bs hr hbs0 hprem hq =>
      rw [addDeclsLanguageDef_rewrites_eq] at hr
      simp at hr
      rcases hr with rfl | rfl
      · simp [addZRule, addZOnePattern, addOnePattern, addZeroPattern,
          Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
          Mettapedia.OSLF.MeTTaIL.Match.matchArgs,
          Mettapedia.OSLF.MeTTaIL.Match.mergeBindings] at hbs0
        subst bs0
        cases hprem
        simp [addZRule, addZeroPattern,
          applyBindingsForRule, declarationForRule?, addDeclsLanguageDef,
          rewriteDeclsToLanguageDef, rewriteDeclsToLanguageDefWithTerms,
          Mettapedia.OSLF.MeTTaIL.Match.applyBindings] at hq
      · simp [addSRule, addZOnePattern, addOnePattern, addZeroPattern,
          Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
          Mettapedia.OSLF.MeTTaIL.Match.matchArgs,
          Mettapedia.OSLF.MeTTaIL.Match.mergeBindings] at hbs0

theorem source_and_languageDef_step_agree_add_z_one :
    Mettapedia.GSLT.LanguageDef.MIEvalEncoding.stepBaseStep?
        Mettapedia.GSLT.LanguageDef.MIEvalEncoding.addDecls
        (Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gAdd
          Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gZ
          Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gOne) =
      some Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gOne ∧
    Mettapedia.OSLF.Framework.TypeSynthesis.langReduces addDeclsLanguageDef
      addZOnePattern addOnePattern := by
  exact ⟨sourceStep_add_z_one, addDeclsLanguageDef_reduces_add_z_one⟩

theorem addDeclsLanguageDef_reduces_add_one_one_root :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReduces addDeclsLanguageDef
      addOneOnePattern addOneOneAfterRootPattern := by
  change Step (engineBasePremises RelationEnv.empty) addDeclsLanguageDef
    addOneOnePattern addOneOneAfterRootPattern
  refine step_of_rule (rule := addSRule)
    (initialBindings := [("n", addOnePattern), ("m", addZeroPattern)])
    (finalBindings := [("n", addOnePattern), ("m", addZeroPattern)])
    ?hr ?hbs0 .nil ?hprem ?hq
  · rw [addDeclsLanguageDef_rewrites_eq]
    simp
  · unfold addSRule addOneOnePattern addOnePattern addZeroPattern
    simp [Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
      Mettapedia.OSLF.MeTTaIL.Match.matchArgs,
      Mettapedia.OSLF.MeTTaIL.Match.mergeBindings]
  · unfold addSRule addOnePattern addZeroPattern
    simp [Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv]
  · unfold addSRule addOneOneAfterRootPattern addZOnePattern addOnePattern addZeroPattern
    simp [applyBindingsForRule, declarationForRule?, addDeclsLanguageDef,
      rewriteDeclsToLanguageDef, rewriteDeclsToLanguageDefWithTerms,
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings]

theorem addDeclsLanguageDef_reduces_add_two_one_root :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReduces addDeclsLanguageDef
      addTwoOnePattern addTwoOneAfterRootPattern := by
  change Step (engineBasePremises RelationEnv.empty) addDeclsLanguageDef
    addTwoOnePattern addTwoOneAfterRootPattern
  refine step_of_rule (rule := addSRule)
    (initialBindings := [("n", addOnePattern), ("m", addOnePattern)])
    (finalBindings := [("n", addOnePattern), ("m", addOnePattern)])
    ?hr ?hbs0 .nil ?hprem ?hq
  · rw [addDeclsLanguageDef_rewrites_eq]
    simp
  · unfold addSRule addTwoOnePattern addTwoPattern addOnePattern addZeroPattern
    simp [Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
      Mettapedia.OSLF.MeTTaIL.Match.matchArgs,
      Mettapedia.OSLF.MeTTaIL.Match.mergeBindings]
  · unfold addSRule addOnePattern addZeroPattern
    simp [Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv]
  · unfold addSRule addTwoOneAfterRootPattern addOneOnePattern addOnePattern
      addZeroPattern
    simp [applyBindingsForRule, declarationForRule?, addDeclsLanguageDef,
      rewriteDeclsToLanguageDef, rewriteDeclsToLanguageDefWithTerms,
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings]

theorem revDeclsLanguageDef_reduces_rev_nil :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReduces revDeclsLanguageDef
      (revCallPattern nilValuePattern) nilValuePattern := by
  change Step (engineBasePremises RelationEnv.empty) revDeclsLanguageDef
    (revCallPattern nilValuePattern) nilValuePattern
  refine step_of_rule (rule := revNilRule)
    (initialBindings := []) (finalBindings := [])
    ?hr ?hbs0 .nil ?hprem ?hq
  · rw [revDeclsLanguageDef_rewrites_eq]
    simp
  · unfold revNilRule revCallPattern nilValuePattern
    simp [Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
      Mettapedia.OSLF.MeTTaIL.Match.matchArgs,
      Mettapedia.OSLF.MeTTaIL.Match.mergeBindings]
  · unfold revNilRule
    simp [Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv]
  · unfold revNilRule nilValuePattern
    simp [applyBindingsForRule, declarationForRule?, revDeclsLanguageDef,
      rewriteDeclsToLanguageDefWithTerms,
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings]

theorem revDeclsLanguageDef_reduces_append_nil_list0 :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReduces revDeclsLanguageDef
      revList0AfterInnerPattern list0Pattern := by
  change Step (engineBasePremises RelationEnv.empty) revDeclsLanguageDef
    revList0AfterInnerPattern list0Pattern
  refine step_of_rule (rule := revAppendNilRule)
    (initialBindings := [("ys", list0Pattern)])
    (finalBindings := [("ys", list0Pattern)])
    ?hr ?hbs0 .nil ?hprem ?hq
  · rw [revDeclsLanguageDef_rewrites_eq]
    simp
  · unfold revAppendNilRule revList0AfterInnerPattern appendCallPattern
      nilValuePattern list0Pattern consValuePattern addZeroPattern
    simp [Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
      Mettapedia.OSLF.MeTTaIL.Match.matchArgs,
      Mettapedia.OSLF.MeTTaIL.Match.mergeBindings]
  · unfold revAppendNilRule list0Pattern consValuePattern nilValuePattern
      addZeroPattern
    simp [Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv]
  · unfold revAppendNilRule list0Pattern consValuePattern nilValuePattern
      addZeroPattern
    simp [applyBindingsForRule, declarationForRule?, revDeclsLanguageDef,
      rewriteDeclsToLanguageDefWithTerms,
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings]

theorem revDeclsLanguageDef_reduces_rev_list0_root :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReduces revDeclsLanguageDef
      (revCallPattern list0Pattern) revList0AfterRootPattern := by
  change Step (engineBasePremises RelationEnv.empty) revDeclsLanguageDef
    (revCallPattern list0Pattern) revList0AfterRootPattern
  refine step_of_rule (rule := revConsRule)
    (initialBindings := [("xs", nilValuePattern), ("x", addZeroPattern)])
    (finalBindings := [("xs", nilValuePattern), ("x", addZeroPattern)])
    ?hr ?hbs0 .nil ?hprem ?hq
  · rw [revDeclsLanguageDef_rewrites_eq]
    simp
  · unfold revConsRule revCallPattern list0Pattern consValuePattern
      nilValuePattern addZeroPattern
    simp [Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
      Mettapedia.OSLF.MeTTaIL.Match.matchArgs,
      Mettapedia.OSLF.MeTTaIL.Match.mergeBindings]
  · unfold revConsRule nilValuePattern addZeroPattern
    simp [Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv]
  · unfold revConsRule revList0AfterRootPattern appendCallPattern
      revCallPattern list0Pattern consValuePattern nilValuePattern
      addZeroPattern
    simp [applyBindingsForRule, declarationForRule?, revDeclsLanguageDef,
      rewriteDeclsToLanguageDefWithTerms,
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings]

theorem addDeclsReachabilitySig_extends_extracted :
    addDeclsReachabilitySig.take (languageDefToLFSig addDeclsLanguageDef).length =
      languageDefToLFSig addDeclsLanguageDef := by
  simp [addDeclsReachabilitySig, languageDefToReachabilityLFSig]

theorem addDeclsReachabilitySig_rule_suffix :
    addDeclsReachabilitySig.drop
        ((languageDefToLFSig addDeclsLanguageDef).length +
          (reachabilityScaffold addDeclsLanguageDef.name).length) =
      addDeclsLanguageDef.rewrites.map
        (rewriteToReachabilityDecl addDeclsLanguageDef.name) := by
  simp [addDeclsReachabilitySig, languageDefToReachabilityLFSig]

def addDeclsReachabilityRuleDeclNames : List String :=
  addDeclsLanguageDef.rewrites.map fun rw =>
    lfDeclName (rewriteToReachabilityDecl addDeclsLanguageDef.name rw)

theorem addDeclsReachabilityRuleDeclNames_eq :
    addDeclsReachabilityRuleDeclNames =
      ["MeTTaAdd:rewrite:add-z", "MeTTaAdd:rewrite:add-s"] := by
  rfl

theorem addDeclsReachabilityRuleDeclNames_has_add_z :
    "MeTTaAdd:rewrite:add-z" ∈ addDeclsReachabilityRuleDeclNames := by
  rw [addDeclsReachabilityRuleDeclNames_eq]
  simp

theorem addDeclsReachabilityRuleDeclNames_has_add_s :
    "MeTTaAdd:rewrite:add-s" ∈ addDeclsReachabilityRuleDeclNames := by
  rw [addDeclsReachabilityRuleDeclNames_eq]
  simp

theorem addDeclsReachabilityRuleDeclNames_rejects_bogus :
    ¬ "MeTTaAdd:rewrite:add-bogus" ∈ addDeclsReachabilityRuleDeclNames := by
  rw [addDeclsReachabilityRuleDeclNames_eq]
  simp

theorem addDeclsReachabilitySig_rewrite_decl_count :
    addDeclsReachabilitySig.length =
      (languageDefToLFSig addDeclsLanguageDef).length +
        (reachabilityScaffold addDeclsLanguageDef.name).length +
        addDeclsLanguageDef.rewrites.length := by
  simp [addDeclsReachabilitySig, languageDefToReachabilityLFSig,
    Nat.add_assoc]

def addDeclsKernelReachabilityDeclNames : List String :=
  addDeclsKernelReachabilitySig.map lfDeclName

def revDeclsKernelReachabilityDeclNames : List String :=
  revDeclsKernelReachabilitySig.map lfDeclName

theorem addDeclsKernelReachabilityDeclNames_eq :
    addDeclsKernelReachabilityDeclNames =
      [ "__ldName"
      , "__ldIndex"
      , "__ldPattern"
      , "__ldPatternList"
      , "__ldNameList"
      , "__ldColl"
      , "__ldNoName"
      , "__ldNameNil"
      , "__ldNameCons"
      , "__ldPNil"
      , "__ldPCons"
      , "__ldPBVar"
      , "__ldPFVar"
      , "__ldPApply"
      , "__ldPLambda"
      , "__ldPMultiLambda"
      , "__ldPSubst"
      , "__ldPCollection"
      , "__ldCollVec"
      , "__ldCollHashBag"
      , "__ldCollHashSet"
      , "__ldEquationRule"
      , "__ldRewriteRule"
      , "MTerm"
      , "name:add"
      , "name:Z"
      , "name:n"
      , "name:S"
      , "name:m"
      , "rewrite:add-z"
      , "rewrite:add-s"
      , "MeTTaAdd:Reduces"
      , "MeTTaAdd:EvalEq"
      , "MeTTaAdd:reduces-refl"
      , "MeTTaAdd:reduces-trans"
      , "MeTTaAdd:eval-eq-intro"
      , "MeTTaAdd:reduces-apply-head"
      , "MeTTaAdd:reduces-apply-second"
      , "MeTTaAdd:rewrite:add-z"
      , "MeTTaAdd:rewrite:add-s"
      ] := by
  rfl

theorem addDeclsKernelReachabilityDeclNames_has_apply_head :
    addDeclsKernelReachabilityDeclNames.contains
      "MeTTaAdd:reduces-apply-head" = true := by
  rfl

theorem addDeclsKernelReachabilityDeclNames_has_apply_second :
    addDeclsKernelReachabilityDeclNames.contains
      "MeTTaAdd:reduces-apply-second" = true := by
  rfl

theorem revDeclsKernelReachabilityDeclNames_has_append_nil :
    revDeclsKernelReachabilityDeclNames.contains
      "MeTTaRev:rewrite:append-nil" = true := by
  rfl

theorem revDeclsKernelReachabilityDeclNames_has_append_cons :
    revDeclsKernelReachabilityDeclNames.contains
      "MeTTaRev:rewrite:append-cons" = true := by
  rfl

theorem revDeclsKernelReachabilityDeclNames_has_rev_nil :
    revDeclsKernelReachabilityDeclNames.contains
      "MeTTaRev:rewrite:rev-nil" = true := by
  rfl

theorem revDeclsKernelReachabilityDeclNames_has_rev_cons :
    revDeclsKernelReachabilityDeclNames.contains
      "MeTTaRev:rewrite:rev-cons" = true := by
  rfl

theorem revDeclsKernelReachabilityDeclNames_has_apply_head :
    revDeclsKernelReachabilityDeclNames.contains
      "MeTTaRev:reduces-apply-head" = true := by
  rfl

theorem revDeclsKernelReachabilityDeclNames_has_apply_second :
    revDeclsKernelReachabilityDeclNames.contains
      "MeTTaRev:reduces-apply-second" = true := by
  rfl

theorem addDeclsKernelReachabilityDeclNames_omits_higher_kind_metadata :
    ( addDeclsKernelReachabilityDeclNames.contains "__ldMultiBinder"
    , addDeclsKernelReachabilityDeclNames.contains "__ldVec"
    , addDeclsKernelReachabilityDeclNames.contains "__ldHashBag"
    , addDeclsKernelReachabilityDeclNames.contains "__ldHashSet"
    ) = (false, false, false, false) := by
  rfl

theorem addDeclsKernelReachabilitySig_rule_suffix :
    addDeclsKernelReachabilitySig.drop
        (kernelExtractionScaffold.length +
          addDeclsLanguageDef.types.length +
          (languageLiteralDecls addDeclsLanguageDef).length +
          addDeclsLanguageDef.rewrites.length +
          (reachabilityScaffold addDeclsLanguageDef.name).length) =
      addDeclsLanguageDef.rewrites.map
        (rewriteToReachabilityDecl addDeclsLanguageDef.name) := by
  rfl

theorem addDeclsKernelReachabilitySig_rewrite_decl_count :
    addDeclsKernelReachabilitySig.length =
      kernelExtractionScaffold.length +
        addDeclsLanguageDef.types.length +
        (languageLiteralDecls addDeclsLanguageDef).length +
        addDeclsLanguageDef.rewrites.length +
        (reachabilityScaffold addDeclsLanguageDef.name).length +
        addDeclsLanguageDef.rewrites.length := by
  simp [addDeclsKernelReachabilitySig, languageDefToKernelReachabilityLFSig,
    Nat.add_assoc]

theorem revDeclsKernelReachabilitySig_rule_suffix :
    revDeclsKernelReachabilitySig.drop
        (kernelExtractionScaffold.length +
          revDeclsLanguageDef.types.length +
          (languageLiteralDecls revDeclsLanguageDef).length +
          revDeclsLanguageDef.rewrites.length +
          (reachabilityScaffold revDeclsLanguageDef.name).length) =
      revDeclsLanguageDef.rewrites.map
        (rewriteToReachabilityDecl revDeclsLanguageDef.name) := by
  rfl

theorem revDeclsKernelReachabilitySig_rewrite_decl_count :
    revDeclsKernelReachabilitySig.length =
      kernelExtractionScaffold.length +
        revDeclsLanguageDef.types.length +
        (languageLiteralDecls revDeclsLanguageDef).length +
        revDeclsLanguageDef.rewrites.length +
        (reachabilityScaffold revDeclsLanguageDef.name).length +
        revDeclsLanguageDef.rewrites.length := by
  simp [revDeclsKernelReachabilitySig, languageDefToKernelReachabilityLFSig,
    Nat.add_assoc]

inductive HostedKernelStep (lang : LDLanguageDef) : LDPattern → LDPattern → Prop where
  | root {p q : LDPattern} :
      Mettapedia.OSLF.Framework.TypeSynthesis.langReduces lang p q →
      HostedKernelStep lang p q
  | applyHead {head : String} {p q : LDPattern} {rest : List LDPattern} :
      HostedKernelStep lang p q →
      HostedKernelStep lang (.apply head (p :: rest)) (.apply head (q :: rest))
  | applySecond {head : String} {first p q : LDPattern} :
      HostedKernelStep lang p q →
      HostedKernelStep lang (.apply head [first, p]) (.apply head [first, q])

abbrev HostedKernelReach (lang : LDLanguageDef) : LDPattern → LDPattern → Prop :=
  Relation.ReflTransGen (HostedKernelStep lang)

theorem addDeclsHostedKernelStep_add_one_one_root :
    HostedKernelStep addDeclsLanguageDef
      addOneOnePattern addOneOneAfterRootPattern :=
  HostedKernelStep.root addDeclsLanguageDef_reduces_add_one_one_root

theorem addDeclsHostedKernelStep_add_z_one_under_s :
    HostedKernelStep addDeclsLanguageDef
      addOneOneAfterRootPattern addTwoPattern := by
  exact HostedKernelStep.applyHead
    (head := "S") (rest := [])
    (HostedKernelStep.root addDeclsLanguageDef_reduces_add_z_one)

theorem addDeclsHostedKernelReach_add_one_one :
    HostedKernelReach addDeclsLanguageDef
      addOneOnePattern addTwoPattern := by
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.tail
      (Relation.ReflTransGen.refl)
      addDeclsHostedKernelStep_add_one_one_root)
    addDeclsHostedKernelStep_add_z_one_under_s

theorem addDeclsHostedKernelStep_add_two_one_root :
    HostedKernelStep addDeclsLanguageDef
      addTwoOnePattern addTwoOneAfterRootPattern :=
  HostedKernelStep.root addDeclsLanguageDef_reduces_add_two_one_root

theorem addDeclsHostedKernelStep_add_one_one_under_s :
    HostedKernelStep addDeclsLanguageDef
      addTwoOneAfterRootPattern addTwoOneAfterInnerPattern := by
  exact HostedKernelStep.applyHead
    (head := "S") (rest := [])
    addDeclsHostedKernelStep_add_one_one_root

theorem addDeclsHostedKernelStep_add_z_one_under_ss :
    HostedKernelStep addDeclsLanguageDef
      addTwoOneAfterInnerPattern addThreePattern := by
  exact HostedKernelStep.applyHead
    (head := "S") (rest := [])
    addDeclsHostedKernelStep_add_z_one_under_s

theorem addDeclsHostedKernelReach_add_two_one :
    HostedKernelReach addDeclsLanguageDef
      addTwoOnePattern addThreePattern := by
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.tail
      (Relation.ReflTransGen.tail
        (Relation.ReflTransGen.refl)
        addDeclsHostedKernelStep_add_two_one_root)
      addDeclsHostedKernelStep_add_one_one_under_s)
    addDeclsHostedKernelStep_add_z_one_under_ss

theorem revDeclsHostedKernelStep_rev_nil_root :
    HostedKernelStep revDeclsLanguageDef
      (revCallPattern nilValuePattern) nilValuePattern :=
  HostedKernelStep.root revDeclsLanguageDef_reduces_rev_nil

theorem revDeclsHostedKernelStep_append_nil_list0_root :
    HostedKernelStep revDeclsLanguageDef
      revList0AfterInnerPattern list0Pattern :=
  HostedKernelStep.root revDeclsLanguageDef_reduces_append_nil_list0

theorem revDeclsHostedKernelStep_rev_list0_root :
    HostedKernelStep revDeclsLanguageDef
      (revCallPattern list0Pattern) revList0AfterRootPattern :=
  HostedKernelStep.root revDeclsLanguageDef_reduces_rev_list0_root

theorem revDeclsHostedKernelStep_rev_rev_list0_inner_root :
    HostedKernelStep revDeclsLanguageDef
      revRevList0Pattern revRevList0AfterInnerRootPattern := by
  exact HostedKernelStep.applyHead
    (head := "rev") (rest := [])
    revDeclsHostedKernelStep_rev_list0_root

theorem revDeclsHostedKernelStep_rev_rev_list0_inner_nil :
    HostedKernelStep revDeclsLanguageDef
      revRevList0AfterInnerRootPattern revRevList0AfterInnerNilPattern := by
  exact HostedKernelStep.applyHead
    (head := "rev") (rest := [])
    (HostedKernelStep.applyHead
      (head := "listAppend") (rest := [list0Pattern])
      revDeclsHostedKernelStep_rev_nil_root)

theorem revDeclsHostedKernelStep_rev_rev_list0_inner_append :
    HostedKernelStep revDeclsLanguageDef
      revRevList0AfterInnerNilPattern (revCallPattern list0Pattern) := by
  exact HostedKernelStep.applyHead
    (head := "rev") (rest := [])
    revDeclsHostedKernelStep_append_nil_list0_root

theorem revDeclsHostedKernelStep_rev_list0_inner_nil :
    HostedKernelStep revDeclsLanguageDef
      revList0AfterRootPattern revList0AfterInnerPattern := by
  exact HostedKernelStep.applyHead
    (head := "listAppend") (rest := [list0Pattern])
    revDeclsHostedKernelStep_rev_nil_root

theorem revDeclsHostedKernelStep_append_second_rev_nil :
    HostedKernelStep revDeclsLanguageDef
      (appendCallPattern list0Pattern (revCallPattern nilValuePattern))
      (appendCallPattern list0Pattern nilValuePattern) := by
  exact HostedKernelStep.applySecond
    (head := "listAppend") (first := list0Pattern)
    revDeclsHostedKernelStep_rev_nil_root

theorem revDeclsHostedKernelReach_rev_involution_list0 :
    HostedKernelReach revDeclsLanguageDef
      revRevList0Pattern list0Pattern := by
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.tail
      (Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail
          (Relation.ReflTransGen.tail
            (Relation.ReflTransGen.tail
              (Relation.ReflTransGen.refl)
              revDeclsHostedKernelStep_rev_rev_list0_inner_root)
            revDeclsHostedKernelStep_rev_rev_list0_inner_nil)
          revDeclsHostedKernelStep_rev_rev_list0_inner_append)
        revDeclsHostedKernelStep_rev_list0_root)
      revDeclsHostedKernelStep_rev_list0_inner_nil)
    revDeclsHostedKernelStep_append_nil_list0_root

structure AddOneOneCoherenceSquare where
  sourceVerdict :
    Mettapedia.GSLT.LanguageDef.MIEvalEncoding.sourceInterpVerdict
        Mettapedia.GSLT.LanguageDef.MIEvalEncoding.addDecls 10
        (Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gAdd
          Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gOne
          Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gOne) =
      Mettapedia.GSLT.LanguageDef.MIEvalEncoding.SourceInterpVerdict.done
        (Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gS
          Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gOne)
  evaluatorMatches :
    ∃ N host,
      MeTTaIL.eval Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.pMI N
          (Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miEval
            Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.rulesAdd
            (Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miAdd
              Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miOne
              Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miOne)
            (Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.fuel 10)) =
        host ∧
      Mettapedia.GSLT.LanguageDef.MIEvalEncoding.MatchesInterp host
        (Mettapedia.GSLT.LanguageDef.MIEvalEncoding.sourceInterpVerdict
          Mettapedia.GSLT.LanguageDef.MIEvalEncoding.addDecls 10
          (Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gAdd
            Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gOne
            Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gOne))
  hostedReach :
    HostedKernelReach addDeclsLanguageDef addOneOnePattern addTwoPattern
  generatedKernelSigHasRules :
    addDeclsKernelReachabilityDeclNames.contains
        "MeTTaAdd:rewrite:add-s" = true ∧
      addDeclsKernelReachabilityDeclNames.contains
        "MeTTaAdd:rewrite:add-z" = true ∧
      addDeclsKernelReachabilityDeclNames.contains
        "MeTTaAdd:reduces-apply-head" = true ∧
      addDeclsKernelReachabilityDeclNames.contains
        "MeTTaAdd:reduces-apply-second" = true

def add_one_one_coherence_square :
    AddOneOneCoherenceSquare := by
  refine
    { sourceVerdict := ?_
      evaluatorMatches := ?_
      hostedReach := ?_
      generatedKernelSigHasRules := ?_ }
  · exact Mettapedia.GSLT.LanguageDef.MIEvalEncoding.sourceInterpVerdict_add_1_1
  · exact Mettapedia.GSLT.LanguageDef.MIEvalEncoding.miEval_add_1_1_matches_sourceInterp_by_interp_sim
  · exact addDeclsHostedKernelReach_add_one_one
  · exact ⟨rfl, rfl, rfl, rfl⟩

structure AddTwoOneCoherenceSquare where
  sourceVerdict :
    Mettapedia.GSLT.LanguageDef.MIEvalEncoding.sourceInterpVerdict
        Mettapedia.GSLT.LanguageDef.MIEvalEncoding.addDecls 10
        (Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gAdd
          Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gTwo
          Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gOne) =
      Mettapedia.GSLT.LanguageDef.MIEvalEncoding.SourceInterpVerdict.done
        Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gThree
  evaluatorMatches :
    ∃ N host,
      MeTTaIL.eval Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.pMI N
          (Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miEval
            Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.rulesAdd
            (Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miAdd
              Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miTwo
              Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miOne)
            (Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.fuel 10)) =
        host ∧
      Mettapedia.GSLT.LanguageDef.MIEvalEncoding.MatchesInterp host
        (Mettapedia.GSLT.LanguageDef.MIEvalEncoding.sourceInterpVerdict
          Mettapedia.GSLT.LanguageDef.MIEvalEncoding.addDecls 10
          (Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gAdd
            Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gTwo
            Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gOne))
  hostedReach :
    HostedKernelReach addDeclsLanguageDef addTwoOnePattern addThreePattern
  generatedKernelSigHasRules :
    addDeclsKernelReachabilityDeclNames.contains
        "MeTTaAdd:rewrite:add-s" = true ∧
      addDeclsKernelReachabilityDeclNames.contains
        "MeTTaAdd:rewrite:add-z" = true ∧
      addDeclsKernelReachabilityDeclNames.contains
        "MeTTaAdd:reduces-apply-head" = true ∧
      addDeclsKernelReachabilityDeclNames.contains
        "MeTTaAdd:reduces-apply-second" = true

def add_two_one_coherence_square :
    AddTwoOneCoherenceSquare := by
  refine
    { sourceVerdict := ?_
      evaluatorMatches := ?_
      hostedReach := ?_
      generatedKernelSigHasRules := ?_ }
  · exact Mettapedia.GSLT.LanguageDef.MIEvalEncoding.sourceInterpVerdict_add_2_1
  · exact Mettapedia.GSLT.LanguageDef.MIEvalEncoding.miEval_add_2_1_matches_sourceInterp_by_interp_sim
  · exact addDeclsHostedKernelReach_add_two_one
  · exact ⟨rfl, rfl, rfl, rfl⟩

structure RevInvolutionHostingBridge where
  encodedRules :
    Mettapedia.GSLT.LanguageDef.MIEvalEncoding.encRules?
        Mettapedia.GSLT.LanguageDef.MIEvalEncoding.revDecls =
      some Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.rulesRev
  evaluatorRuns :
    MeTTaIL.eval Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.pMI 12000
        (Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miEval
          Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.rulesRev
          (Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miRev
            (Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miRev
              Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miList012))
          (Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.fuel 40)) =
    Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.MIDone
        Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miList012
  evaluatorMatches :
    ∃ N host,
      MeTTaIL.eval Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.pMI N
          (Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miEval
            Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.rulesRev
            (Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miRev
              (Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miRev
                Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miList012))
            (Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.fuel 40)) =
        host ∧
      Mettapedia.GSLT.LanguageDef.MIEvalEncoding.MatchesInterp host
        (Mettapedia.GSLT.LanguageDef.MIEvalEncoding.sourceInterpVerdict
          Mettapedia.GSLT.LanguageDef.MIEvalEncoding.revDecls 40
          (Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gRev
            (Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gRev
              Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gList012)))
  generatedKernelSigHasRules :
    revDeclsKernelReachabilityDeclNames.contains
        "MeTTaRev:rewrite:append-nil" = true ∧
      revDeclsKernelReachabilityDeclNames.contains
        "MeTTaRev:rewrite:append-cons" = true ∧
      revDeclsKernelReachabilityDeclNames.contains
        "MeTTaRev:rewrite:rev-nil" = true ∧
      revDeclsKernelReachabilityDeclNames.contains
        "MeTTaRev:rewrite:rev-cons" = true ∧
      revDeclsKernelReachabilityDeclNames.contains
        "MeTTaRev:reduces-apply-head" = true ∧
      revDeclsKernelReachabilityDeclNames.contains
        "MeTTaRev:reduces-apply-second" = true
  rootStableShortcutDoesNotApply :
    ¬ Mettapedia.GSLT.LanguageDef.MIEvalEncoding.StepProducesRootStable
        Mettapedia.GSLT.LanguageDef.MIEvalEncoding.revDecls
  traceRootStableShortcutDoesNotApply :
    ¬ Mettapedia.GSLT.LanguageDef.MIEvalEncoding.SourceTraceRootStable
        Mettapedia.GSLT.LanguageDef.MIEvalEncoding.revDecls 40
        (Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gRev
          (Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gRev
            Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gList012))

def rev_involution_hosting_bridge :
    RevInvolutionHostingBridge := by
  refine
    { encodedRules := ?_
      evaluatorRuns := ?_
      evaluatorMatches := ?_
      generatedKernelSigHasRules := ?_
      rootStableShortcutDoesNotApply := ?_
      traceRootStableShortcutDoesNotApply := ?_ }
  · exact Mettapedia.GSLT.LanguageDef.MIEvalEncoding.encRules_revDecls
  · exact
      Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.self_rev_involution_eval_012
  · exact
      Mettapedia.GSLT.LanguageDef.MIEvalEncoding.miEval_rev_involution_012_matches_sourceInterp
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact Mettapedia.GSLT.LanguageDef.MIEvalEncoding.revDecls_not_stepProducesRootStable
  · simpa [Mettapedia.GSLT.LanguageDef.MIEvalEncoding.sourceRevInv_0] using
      Mettapedia.GSLT.LanguageDef.MIEvalEncoding.sourceTraceRootStable_rev_involution_012_40_fails

def revList0Source : MeTTaIL.AST :=
  Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gCons
    Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gZ
    Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gNil

def revRevList0Source : MeTTaIL.AST :=
  Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gRev
    (Mettapedia.GSLT.LanguageDef.MIEvalEncoding.gRev revList0Source)

def miList0Term : MeTTaIL.AST :=
  Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miCons
    Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miZ
    Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miNil

def miRawRevList0Term : MeTTaIL.AST :=
  Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miListAppend
    (Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miRev
      Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miNil)
    miList0Term

def miRawAppendList0Term : MeTTaIL.AST :=
  Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miListAppend
    Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miNil
    miList0Term

theorem mettaASTToPattern_rev_involution_list0 :
    mettaASTToPattern? revRevList0Source = some revRevList0Pattern := by
  rfl

theorem encAST_rev_list0 :
    Mettapedia.GSLT.LanguageDef.MIEvalEncoding.encAST? revList0Source =
      some miList0Term := by
  rfl

theorem sourceInterpVerdict_rev_involution_list0 :
    Mettapedia.GSLT.LanguageDef.MIEvalEncoding.sourceInterpVerdict
        Mettapedia.GSLT.LanguageDef.MIEvalEncoding.revDecls 20
        revRevList0Source =
      Mettapedia.GSLT.LanguageDef.MIEvalEncoding.SourceInterpVerdict.done
        revList0Source := by
  rfl

theorem miRawAppendList0Term_ne_miList0Term :
    miRawAppendList0Term ≠ miList0Term := by
  intro h
  unfold miRawAppendList0Term miList0Term at h
  unfold Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miListAppend
    Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miCons
    Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miNil
    Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miZ
    Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.MIApp
    Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.MISym
    Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.MICons
    Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.MINil
    Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.app
    Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.con0 at h
  simp at h

theorem rev_rev_list0_root_exposed_candidate_not_source_match :
    ¬ Mettapedia.GSLT.LanguageDef.MIEvalEncoding.MatchesInterp
        (Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.MIDone
          miRawAppendList0Term)
        (Mettapedia.GSLT.LanguageDef.MIEvalEncoding.sourceInterpVerdict
          Mettapedia.GSLT.LanguageDef.MIEvalEncoding.revDecls 20
          revRevList0Source) := by
  rw [sourceInterpVerdict_rev_involution_list0]
  unfold Mettapedia.GSLT.LanguageDef.MIEvalEncoding.MatchesInterp
  intro h
  rcases h with ⟨encodedTerm, henc, hhost⟩
  rw [encAST_rev_list0] at henc
  injection henc with heq
  subst encodedTerm
  have hterm : miRawAppendList0Term = miList0Term := by
    unfold Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.MIDone
      Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.app at hhost
    injection hhost with _ hargs
    injection hargs
  exact miRawAppendList0Term_ne_miList0Term hterm

structure RevList0HostedKernelBridge where
  sourceTermMaps :
    mettaASTToPattern? revRevList0Source = some revRevList0Pattern
  sourceVerdict :
    Mettapedia.GSLT.LanguageDef.MIEvalEncoding.sourceInterpVerdict
        Mettapedia.GSLT.LanguageDef.MIEvalEncoding.revDecls 20
        revRevList0Source =
      Mettapedia.GSLT.LanguageDef.MIEvalEncoding.SourceInterpVerdict.done
        revList0Source
  hostedReach :
    HostedKernelReach revDeclsLanguageDef revRevList0Pattern list0Pattern
  generatedKernelSigHasRules :
    revDeclsKernelReachabilityDeclNames.contains
        "MeTTaRev:rewrite:append-nil" = true ∧
      revDeclsKernelReachabilityDeclNames.contains
        "MeTTaRev:rewrite:rev-nil" = true ∧
      revDeclsKernelReachabilityDeclNames.contains
        "MeTTaRev:rewrite:rev-cons" = true ∧
      revDeclsKernelReachabilityDeclNames.contains
        "MeTTaRev:reduces-apply-head" = true ∧
      revDeclsKernelReachabilityDeclNames.contains
        "MeTTaRev:reduces-apply-second" = true
  fullReverseEvaluatorBridge :
    RevInvolutionHostingBridge
  tinyReverseRootExposureBoundary :
    ¬ Mettapedia.GSLT.LanguageDef.MIEvalEncoding.MatchesInterp
        (Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.MIDone
          miRawAppendList0Term)
        (Mettapedia.GSLT.LanguageDef.MIEvalEncoding.sourceInterpVerdict
          Mettapedia.GSLT.LanguageDef.MIEvalEncoding.revDecls 20
          revRevList0Source)

def rev_list0_hosted_kernel_bridge : RevList0HostedKernelBridge := by
  refine
    { sourceTermMaps := ?_
      sourceVerdict := ?_
      hostedReach := ?_
      generatedKernelSigHasRules := ?_
      fullReverseEvaluatorBridge := ?_
      tinyReverseRootExposureBoundary := ?_ }
  · exact mettaASTToPattern_rev_involution_list0
  · exact sourceInterpVerdict_rev_involution_list0
  · exact revDeclsHostedKernelReach_rev_involution_list0
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact rev_involution_hosting_bridge
  · exact rev_rev_list0_root_exposed_candidate_not_source_match

end Mettapedia.GSLT.LanguageDef.MIEvalHosting
