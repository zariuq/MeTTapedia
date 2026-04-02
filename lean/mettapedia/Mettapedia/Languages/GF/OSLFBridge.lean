import GFCore.Syntax
import Mettapedia.Languages.GF.SemanticKernelDSL
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.Formula
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.CategoryBridge

/-!
# GF → OSLF Bridge (Real GFCore)

Bridges real GF parses (GFCore.CheckedExpr) to the OSLF type system,
enabling modal semantics (◇/□ Galois connection) for GF-parsed English.

Replaces the hand-crafted bridge (OSLFBridge_handcrafted.lean) which
used manually transcribed function signatures. This version works with
GFCore.GrammarSig loaded at runtime from ParseEng (115K functions).

## Authority boundary

`gfSyntaxLanguageDef` / `gfSyntaxLanguageDefFromList` are the authoritative
"real GF in LanguageDef" entry points. They contain exactly the categories
and constructors present in the checked/generated GF signature, with no
invented equations or rewrites.

`gfRGLLanguageDef` is retained only as a legacy authored semantic overlay for
downstream compatibility. It should not be used for trust-critical claims
about the actual GF→IR→Lean pipeline.

## Hypercube connection (Stay, Meredith, Wells 2026)

A GF grammar is an operational theory in the hypercube sense:
term formers = FunDecl, base rewrites = identity eliminations,
reduction = langReduces. The OSLF framework automatically generates
a modal type system (◇ ⊣ □) from this operational data.

## Pipeline

```
GFCore.GrammarSig ──→ LanguageDef ──→ langOSLF ──→ OSLFTypeSystem
  (FunDecl,            (types,         (Pred, ◇, □,
   CheckedExpr)         GrammarRule,    Galois connection)
                        Pattern)
```
-/

namespace Mettapedia.Languages.GF.GFCoreOSLFBridge

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.CategoryBridge
open GFCore
open Mettapedia.Languages.GF.SemanticKernelDSL

-- ═══════════════════════════════════════════════════════════════════
-- Phase 1: Core bridge functions
-- ═══════════════════════════════════════════════════════════════════

/-- Convert a GFCore.CheckedExpr (verified parse tree) to an OSLF Pattern.
    GF declarations lower to constructor applications, including nullary
    declarations such as `TPres` or lexical constants like `man_N`.

    This is the central bridge — all downstream semantic evaluation
    passes through this function. -/
def gfCheckedExprToPattern (e : CheckedExpr) : Pattern :=
  match e with
  | .node decl args =>
    .apply decl.name (args.toList.map fun a => gfCheckedExprToPattern a)
termination_by sizeOf e
decreasing_by
  simp_wf
  have h1 := List.sizeOf_lt_of_mem ‹a ∈ args.toList›
  cases args with | mk data =>
  simp only [Array.mk.sizeOf_spec] at h1 ⊢
  omega

-- Note: gfCheckedExprToPattern uses WF recursion so can't unfold via simp.
-- Use gfCheckedExprToPattern.eq_def for unfolding in proofs.

/-- Convert a GFCore.FunDecl to an OSLF GrammarRule.
    Uses fresh arg0/arg1/... names to avoid duplicates when
    a function has repeated argument categories. -/
def gfFunDeclToGrammarRule (d : FunDecl) : GrammarRule :=
  let indexed := d.argCats.toList.zip (List.range d.argCats.size)
  let params := indexed.map fun (cat, i) =>
    TermParam.simple s!"arg{i}" (TypeExpr.base cat)
  let synPat := indexed.map fun (_, i) =>
    SyntaxItem.nonTerminal s!"arg{i}"
  { label := d.name
  , category := d.resultCat
  , params := params
  , syntaxPattern := synPat }

private def internalGrammarRule
    (label category : String)
    (params : List (String × TypeExpr)) : GrammarRule :=
  { label := label
  , category := category
  , params := params.map (fun pair => TermParam.simple pair.1 pair.2)
  , syntaxPattern := [] }

-- Semantic support types: only types needed by support constructors.
-- Added conservatively — each type must be referenced by at least one
-- support constructor, and all support constructors must be self-consistent.
-- NEVER add constructors for functions that might exist in generated grammars
-- (duplicate constructors break LanguageDef.validate).
private def gfSemanticSupportTypes : List TypeDecl :=
  [ TypeDecl.plain "TimeOffset", TypeDecl.plain "SC"
  , TypeDecl.plain "QS", TypeDecl.plain "AP"
  , TypeDecl.plain "VPSlash", TypeDecl.plain "PN", TypeDecl.plain "Pron"
  , TypeDecl.plain "CN", TypeDecl.plain "Adv"
  , TypeDecl.plain "VV", TypeDecl.plain "VS", TypeDecl.plain "VQ"
  , TypeDecl.plain "VA", TypeDecl.plain "Subj"
  , TypeDecl.plain "Conj"
  , TypeDecl.plain "ListS", TypeDecl.plain "ListNP"
  , TypeDecl.plain "ListAP", TypeDecl.plain "ListAdv"
  , TypeDecl.plain "ListCN"
  , TypeDecl.plain "RS", TypeDecl.plain "RCl", TypeDecl.plain "RP"
  , TypeDecl.plain "Det" ]

private def gfPassV2GrammarRule : GrammarRule :=
  internalGrammarRule "PassV2" "VP" [("v", .base "V2")]

private def gfTemporalGrammarRule : GrammarRule :=
  internalGrammarRule "⊛temporal" "S"
    [("cl", .base "Cl"), ("offset", .base "TimeOffset")]

private def gfTimeOffsetGrammarRules : List GrammarRule :=
  [ internalGrammarRule "0" "TimeOffset" []
  , internalGrammarRule "-1" "TimeOffset" []
  , internalGrammarRule "1" "TimeOffset" []
  ]

private def gfNegationGrammarRule : GrammarRule :=
  internalGrammarRule "⊛negation" "S" [("inner", .base "S")]

/-- EmbedS : S → SC — the GF RGL's sentential complement constructor.
    This is the **quotation operator**: it takes a live sentence (which can
    reduce via tense/voice/negation rewrites) and freezes it as a sentential
    complement (SC). In NTT, this is a **quoting** arrow (domain = S = procSort),
    giving typing action ◇.

    Linguistically: "that John sees Anna" embeds the sentence as an SC,
    available to be the subject of "is true" or complement of "believe". -/
private def gfEmbedSGrammarRule : GrammarRule :=
  internalGrammarRule "EmbedS" "SC" [("s", .base "S")]

/-- ⊛embedded : Cl → SC — the bare propositional content of an embedded sentence.
    When a sentence UseCl(tense, pol, cl) is embedded, the tense and polarity
    are stripped, leaving the bare clause as the semantic content of the quotation. -/
private def gfEmbeddedGrammarRule : GrammarRule :=
  internalGrammarRule "⊛embedded" "SC" [("cl", .base "Cl")]

private def gfEmbedVPGrammarRule : GrammarRule :=
  internalGrammarRule "EmbedVP" "SC" [("vp", .base "VP")]

private def gfEmbedQSGrammarRule : GrammarRule :=
  internalGrammarRule "EmbedQS" "SC" [("qs", .base "QS")]

private def gfQuestionGrammarRule : GrammarRule :=
  internalGrammarRule "⊛question" "SC" [("qs", .base "QS")]

private def gfSubordinateGrammarRule : GrammarRule :=
  internalGrammarRule "⊛subordinate" "Adv"
    [("s", .base "S"), ("subj", .base "Subj")]

private def gfSubjSGrammarRule : GrammarRule :=
  internalGrammarRule "SubjS" "Adv"
    [("subj", .base "Subj"), ("s", .base "S")]

private def gfMassNPGrammarRule : GrammarRule :=
  internalGrammarRule "MassNP" "NP" [("cn", .base "CN")]

private def gfUsePNGrammarRule : GrammarRule :=
  internalGrammarRule "UsePN" "NP" [("pn", .base "PN")]

private def gfUsePronGrammarRule : GrammarRule :=
  internalGrammarRule "UsePron" "NP" [("pron", .base "Pron")]

private def gfProDropGrammarRule : GrammarRule :=
  internalGrammarRule "ProDrop" "Pron" [("pron", .base "Pron")]

private def gfReflVPGrammarRule : GrammarRule :=
  internalGrammarRule "ReflVP" "VP" [("vps", .base "VPSlash")]

private def gfComplVVGrammarRule : GrammarRule :=
  internalGrammarRule "ComplVV" "VP" [("vv", .base "VV"), ("vp", .base "VP")]

private def gfComplVSGrammarRule : GrammarRule :=
  internalGrammarRule "ComplVS" "VP" [("vs", .base "VS"), ("s", .base "S")]

private def gfComplVQGrammarRule : GrammarRule :=
  internalGrammarRule "ComplVQ" "VP" [("vq", .base "VQ"), ("qs", .base "QS")]

private def gfComplVAGrammarRule : GrammarRule :=
  internalGrammarRule "ComplVA" "VP" [("va", .base "VA"), ("ap", .base "AP")]

-- Semantic output constructors for Tier 3 (coordination, relative, aspect).
private def gfConjunctionGrammarRule : GrammarRule :=
  internalGrammarRule "⊛conjunction" "S"
    [("conj", .base "Conj"), ("a", .base "S"), ("b", .base "S")]

private def gfRelativeGrammarRule : GrammarRule :=
  internalGrammarRule "⊛relative" "RS" [("vp", .base "VP")]

private def gfModifiedGrammarRule : GrammarRule :=
  internalGrammarRule "⊛modified" "CN"
    [("cn", .base "CN"), ("rs", .base "RS")]

private def gfRelclauseGrammarRule : GrammarRule :=
  internalGrammarRule "⊛relclause" "RCl" [("cl", .base "Cl")]

private def gfAnteriorGrammarRule : GrammarRule :=
  internalGrammarRule "⊛anterior" "S" [("s", .base "S")]

private def gfConditionalGrammarRule : GrammarRule :=
  internalGrammarRule "⊛conditional" "S" [("s", .base "S")]

private def gfCondTimeOffsetGrammarRule : GrammarRule :=
  internalGrammarRule "?" "TimeOffset" []

-- Only include support constructors that are genuinely NEW (not in any GF grammar).
-- Constructors like UsePN, UsePron, ConjS, BaseS, etc. are provided by the grammar
-- itself and must NOT be duplicated here (duplicate constructors break validate).
private def gfSemanticSupportTerms : List GrammarRule :=
  [ gfPassV2GrammarRule, gfTemporalGrammarRule, gfNegationGrammarRule
  , gfEmbedSGrammarRule, gfEmbeddedGrammarRule
  , gfEmbedVPGrammarRule, gfEmbedQSGrammarRule, gfQuestionGrammarRule
  , gfSubordinateGrammarRule
  , gfConjunctionGrammarRule
  , gfRelativeGrammarRule, gfModifiedGrammarRule, gfRelclauseGrammarRule
  , gfAnteriorGrammarRule, gfConditionalGrammarRule, gfCondTimeOffsetGrammarRule
  , internalGrammarRule "⊛universal" "NP" [("cn", .base "CN")]
  , internalGrammarRule "⊛existential" "NP" [("cn", .base "CN")]
  , internalGrammarRule "⊛definite" "NP" [("cn", .base "CN")]
  , internalGrammarRule "⊛negUniversal" "NP" [("cn", .base "CN")]
  ] ++ gfTimeOffsetGrammarRules

-- ═══════════════════════════════════════════════════════════════════
-- Phase 2: Shared GF semantic kernel (authored via languageDef!)
-- ═══════════════════════════════════════════════════════════════════

/-- Shared GF semantic-kernel fragment authored in direct `languageDef!` form. -/
@[reducible] def gfSemanticKernelLanguageDef : LanguageDef :=
  SemanticKernelDSL.gfSemanticKernelLanguageDef

/-- UseN identity equation: UseN(x) = x (bidirectional). -/
@[reducible] def useNIdentityEquation : Equation :=
  SemanticKernelDSL.useNIdentityEquation

/-- UseN elimination: UseN(x) ~> x. -/
@[reducible] def useNElimRewrite : RewriteRule :=
  SemanticKernelDSL.useNElimRewrite

/-- PositA elimination: PositA(x) ~> x. -/
@[reducible] def positAElimRewrite : RewriteRule :=
  SemanticKernelDSL.positAElimRewrite

/-- UseComp elimination: UseComp(x) ~> x. -/
@[reducible] def useCompElimRewrite : RewriteRule :=
  SemanticKernelDSL.useCompElimRewrite

/-- UseV elimination: UseV(x) ~> x. -/
@[reducible] def useVElimRewrite : RewriteRule :=
  SemanticKernelDSL.useVElimRewrite

/-- UseN2 elimination: UseN2(x) ~> x. -/
@[reducible] def useN2ElimRewrite : RewriteRule :=
  SemanticKernelDSL.useN2ElimRewrite

/-- UseA2 elimination: UseA2(x) ~> x. -/
@[reducible] def useA2ElimRewrite : RewriteRule :=
  SemanticKernelDSL.useA2ElimRewrite

/-- All identity-wrapper elimination rewrites. -/
@[reducible] def allIdentityRewrites : List RewriteRule :=
  SemanticKernelDSL.allIdentityRewrites

/-- Active-passive rewrite:
    PredVP(np1, ComplSlash(SlashV2a(v), np2)) ⇝ PredVP(np2, PassV2(v)).
    Direction: active → passive (converse does not hold). -/
@[reducible] def activePassiveRewrite : RewriteRule :=
  SemanticKernelDSL.activePassiveRewrite

/-- Present tense: UseCl(TTAnt(TPres, ASimul), PPos, cl) ⇝ ⊛temporal(cl, 0). -/
@[reducible] def presentTenseRewrite : RewriteRule :=
  SemanticKernelDSL.presentTenseRewrite

/-- Past tense: UseCl(TTAnt(TPast, ASimul), PPos, cl) ⇝ ⊛temporal(cl, -1). -/
@[reducible] def pastTenseRewrite : RewriteRule :=
  SemanticKernelDSL.pastTenseRewrite

/-- Future tense: UseCl(TTAnt(TFut, ASimul), PPos, cl) ⇝ ⊛temporal(cl, 1). -/
@[reducible] def futureTenseRewrite : RewriteRule :=
  SemanticKernelDSL.futureTenseRewrite

/-- All tense rewrites. -/
@[reducible] def allTenseRewrites : List RewriteRule :=
  SemanticKernelDSL.allTenseRewrites

/-- Negation + present tense: UseCl(TTAnt(TPres, ASimul), PNeg, cl) ⇝ ⊛negation(⊛temporal(cl, 0)). -/
@[reducible] def negationPresentRewrite : RewriteRule :=
  SemanticKernelDSL.negationPresentRewrite

/-- Negation + past tense. -/
@[reducible] def negationPastRewrite : RewriteRule :=
  SemanticKernelDSL.negationPastRewrite

/-- Negation + future tense. -/
@[reducible] def negationFutureRewrite : RewriteRule :=
  SemanticKernelDSL.negationFutureRewrite

/-- All negation rewrites. -/
@[reducible] def allNegationRewrites : List RewriteRule :=
  SemanticKernelDSL.allNegationRewrites

/-- Embedding + present tense: EmbedS(UseCl(TPres, PPos, cl)) ⇝ ⊛embedded(cl).
    Sentential complement embedding strips tense/polarity to bare clause. -/
@[reducible] def embedPresentRewrite : RewriteRule :=
  SemanticKernelDSL.embedPresentRewrite

/-- Embedding + past tense. -/
@[reducible] def embedPastRewrite : RewriteRule :=
  SemanticKernelDSL.embedPastRewrite

/-- Embedding + future tense. -/
@[reducible] def embedFutureRewrite : RewriteRule :=
  SemanticKernelDSL.embedFutureRewrite

/-- All embedding rewrites. -/
@[reducible] def allEmbeddingRewrites : List RewriteRule :=
  SemanticKernelDSL.allEmbeddingRewrites

/-- All completion rewrites (ComplVV, ComplVS, ComplVQ, ComplVA). -/
@[reducible] def allCompletionRewrites : List RewriteRule :=
  SemanticKernelDSL.allCompletionRewrites

/-- All subordination rewrites. -/
@[reducible] def allSubordinationRewrites : List RewriteRule :=
  SemanticKernelDSL.allSubordinationRewrites

/-- All semantic entailment rewrites (7 families, 29 rules). -/
@[reducible] def allSemanticRewrites : List RewriteRule :=
  SemanticKernelDSL.allSemanticRewrites

-- ═══════════════════════════════════════════════════════════════════
-- Phase 3: LanguageDef construction from GrammarSig
-- ═══════════════════════════════════════════════════════════════════

/-- Build an OSLF LanguageDef from a list of function declarations.
    This is the kernel-reducible version (no HashMap.fold). -/
def gfFunsListToLanguageDef
    (grammarName : String)
    (funs : List (String × FunDecl))
    (extraTypes : List TypeDecl := [])
    (extraTerms : List GrammarRule := [])
    (rwRules : List RewriteRule := [])
    (eqRules : List Equation := []) : LanguageDef :=
  let allCats := funs.foldl (init := ([] : List String)) fun acc (_, d) =>
    acc ++ d.argCats.toList ++ [d.resultCat]
  let termRules := funs.foldl (init := []) fun acc (_, d) =>
      gfFunDeclToGrammarRule d :: acc
  LanguageDef.mk
    grammarName [] -- options
    ((allCats.eraseDups.map TypeDecl.plain) ++ extraTypes).eraseDups
    (termRules ++ extraTerms) eqRules rwRules
    [.vec, .hashBag, .hashSet] [] []

/-- Build an OSLF LanguageDef from a real GFCore GrammarSig.
    Categories are extracted from function declarations.
    Rewrites and equations are passed in (default: RGL semantics).
    NOTE: Uses HashMap.fold — not kernel-reducible. For kernel-checked
    proofs, use gfFunsListToLanguageDef with a literal funsList. -/
def gfSigToLanguageDef
    (sig : GrammarSig)
    (extraTypes : List TypeDecl := [])
    (extraTerms : List GrammarRule := [])
    (rwRules : List RewriteRule := [])
    (eqRules : List Equation := []) : LanguageDef :=
  let allCats := sig.funs.fold (init := ([] : List String)) fun acc _ d =>
    acc ++ d.argCats.toList ++ [d.resultCat]
  let termRules := sig.funs.fold (init := []) fun acc _ d =>
      gfFunDeclToGrammarRule d :: acc
  LanguageDef.mk
    sig.grammar [] -- options
    ((allCats.eraseDups.map TypeDecl.plain) ++ extraTypes).eraseDups
    (termRules ++ extraTerms) eqRules rwRules
    [.vec, .hashBag, .hashSet] [] []

/-- Authoritative syntax-only `LanguageDef` from a literal GF function list.
    This is the real GF surface in the MeTTaIL DSL: categories + constructors,
    with no authored semantic overlay. -/
def gfSyntaxLanguageDefFromList
    (grammarName : String)
    (funs : List (String × FunDecl)) : LanguageDef :=
  gfFunsListToLanguageDef grammarName funs [] [] [] []

/-- Authoritative syntax-only `LanguageDef` from a real GFCore `GrammarSig`.
    This is the entry point for "actual GF through the DSL". -/
def gfSyntaxLanguageDef (sig : GrammarSig) : LanguageDef :=
  gfSigToLanguageDef sig [] [] [] []

private def gfSemanticValidationSeed (sig : GrammarSig) : LanguageDef :=
  gfSigToLanguageDef sig gfSemanticSupportTypes gfSemanticSupportTerms [] []

/-- Kernel-reducible validation seed from a literal function list. -/
private def gfSemanticValidationSeedFromList
    (grammarName : String) (funs : List (String × FunDecl)) : LanguageDef :=
  gfFunsListToLanguageDef grammarName funs gfSemanticSupportTypes gfSemanticSupportTerms [] []

private def equationSupportedBySig (sig : GrammarSig) (eqn : Equation) : Bool :=
  let baseLang := gfSemanticValidationSeed sig
  let testLang := LanguageDef.mk
    baseLang.name baseLang.options baseLang.types baseLang.terms
    [eqn] baseLang.rewrites baseLang.congruenceCollections
    baseLang.logic baseLang.oracles
  LanguageDef.validate testLang = []

private def rewriteSupportedBySig (sig : GrammarSig) (rw : RewriteRule) : Bool :=
  let baseLang := gfSemanticValidationSeed sig
  let testLang := LanguageDef.mk
    baseLang.name baseLang.options baseLang.types baseLang.terms
    baseLang.equations [rw] baseLang.congruenceCollections
    baseLang.logic baseLang.oracles
  LanguageDef.validate testLang = []

/-- Semantic equations supported by a concrete generated GF signature, after
    adding the small internal semantic extension used by the OSLF bridge. -/
def gfSemanticEquationsForSig (sig : GrammarSig) : List Equation :=
  [useNIdentityEquation].filter (equationSupportedBySig sig)

/-- Semantic rewrites supported by a concrete generated GF signature, after
    adding the small internal semantic extension used by the OSLF bridge. -/
def gfSemanticRewritesForSig (sig : GrammarSig) : List RewriteRule :=
  allSemanticRewrites.filter (rewriteSupportedBySig sig)

/-- Legacy authored semantic overlay on top of a real GF signature.
    This combines the actual GF constructors with hand-written support terms,
    equations, and rewrites. It is preserved only for downstream legacy modules
    that still study the authored OSLF semantics.

    Prefer `gfSyntaxLanguageDef` for any trust-critical real-GF claim. -/
def gfLegacySemanticLanguageDef (sig : GrammarSig) : LanguageDef :=
  gfSigToLanguageDef sig
    gfSemanticSupportTypes
    gfSemanticSupportTerms
    (gfSemanticRewritesForSig sig)
    (gfSemanticEquationsForSig sig)

/-- Compatibility alias for downstream legacy GF semantic modules.
    Non-authoritative: prefer `gfLegacySemanticLanguageDef` or
    `gfSyntaxLanguageDef` depending on intent. -/
abbrev gfRGLLanguageDef := gfLegacySemanticLanguageDef

/-! ### Kernel-reducible parallel (for proofs on literal function lists)

These functions mirror the HashMap-based bridge but work on `List (String × FunDecl)`,
enabling `decide`-based proofs without `native_decide`. Use when the generated sig
provides a `funsList` alongside its `HashMap`. -/

private def equationSupportedByList
    (grammarName : String) (funs : List (String × FunDecl)) (eqn : Equation) : Bool :=
  let baseLang := gfSemanticValidationSeedFromList grammarName funs
  let testLang := LanguageDef.mk
    baseLang.name baseLang.options baseLang.types baseLang.terms
    [eqn] baseLang.rewrites baseLang.congruenceCollections
    baseLang.logic baseLang.oracles
  LanguageDef.validate testLang = []

private def rewriteSupportedByList
    (grammarName : String) (funs : List (String × FunDecl)) (rw : RewriteRule) : Bool :=
  let baseLang := gfSemanticValidationSeedFromList grammarName funs
  let testLang := LanguageDef.mk
    baseLang.name baseLang.options baseLang.types baseLang.terms
    baseLang.equations [rw] baseLang.congruenceCollections
    baseLang.logic baseLang.oracles
  LanguageDef.validate testLang = []

/-- Kernel-reducible legacy authored semantic overlay from a literal function
    list. -/
def gfLegacySemanticLanguageDefFromList
    (grammarName : String) (funs : List (String × FunDecl)) : LanguageDef :=
  gfFunsListToLanguageDef grammarName funs
    gfSemanticSupportTypes
    gfSemanticSupportTerms
    (allSemanticRewrites.filter (rewriteSupportedByList grammarName funs))
    ([useNIdentityEquation].filter (equationSupportedByList grammarName funs))

/-- Compatibility alias for downstream legacy GF semantic modules. -/
abbrev gfRGLLanguageDefFromList := gfLegacySemanticLanguageDefFromList

/-- Rewrite system induced by the authoritative syntax-only GF grammar.
    Since the real syntax lane contains no authored rewrites, this exposes the
    OSLF structure attached to actual GF constructors alone. -/
noncomputable def gfSyntaxRewriteSystem (sig : GrammarSig) :=
  langRewriteSystem (gfSyntaxLanguageDef sig) "S"

/-- OSLF type system induced by the authoritative syntax-only GF grammar. -/
noncomputable def gfSyntaxOSLF (sig : GrammarSig) :=
  langOSLF (gfSyntaxLanguageDef sig) "S"

/-- Galois connection ◇ ⊣ □ for the authoritative syntax-only GF grammar. -/
theorem gfSyntaxGrammar_galois (sig : GrammarSig) :
    GaloisConnection
      (langDiamond (gfSyntaxLanguageDef sig))
      (langBox (gfSyntaxLanguageDef sig)) :=
  langGalois (gfSyntaxLanguageDef sig)

-- ═══════════════════════════════════════════════════════════════════
-- Phase 4: Derived OSLF constructions
-- ═══════════════════════════════════════════════════════════════════

/-- Rewrite system induced by the legacy authored semantic overlay. -/
noncomputable def gfLegacyRewriteSystem (sig : GrammarSig) :=
  langRewriteSystem (gfLegacySemanticLanguageDef sig) "S"

/-- Full OSLF type system for the legacy authored semantic overlay. -/
noncomputable def gfLegacyOSLF (sig : GrammarSig) :=
  langOSLF (gfLegacySemanticLanguageDef sig) "S"

/-- Galois connection ◇ ⊣ □ for the legacy authored semantic overlay. -/
theorem gfLegacyGrammar_galois (sig : GrammarSig) :
    GaloisConnection
      (langDiamond (gfLegacySemanticLanguageDef sig))
      (langBox (gfLegacySemanticLanguageDef sig)) :=
  langGalois (gfLegacySemanticLanguageDef sig)

/-- Compatibility alias for downstream legacy GF semantic modules. -/
noncomputable abbrev gfRewriteSystem := gfLegacyRewriteSystem

/-- Compatibility alias for downstream legacy GF semantic modules. -/
noncomputable abbrev gfOSLF := gfLegacyOSLF

/-- Compatibility alias for downstream legacy GF semantic modules. -/
abbrev gfGrammar_galois := gfLegacyGrammar_galois

-- ═══════════════════════════════════════════════════════════════════
-- Phase 5: Soundness theorems
-- ═══════════════════════════════════════════════════════════════════

open Mettapedia.OSLF.MeTTaIL.Engine

/-- If `checkLangUsing` returns `.sat` on a real GF parse tree converted
    to a Pattern, then the formula's denotational semantics hold.

    Master bridge: GF parse → OSLF semantics. -/
theorem gfCheckedExpr_checkSat_sound
    {lang : LanguageDef}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    {fuel : Nat} {node : CheckedExpr} {φ : OSLFFormula}
    (h : checkLangUsing .empty lang I_check fuel
           (gfCheckedExprToPattern node) φ = .sat) :
    sem (langReduces lang) I_sem φ (gfCheckedExprToPattern node) :=
  checkLangUsing_sat_sound h_atoms h

/-- If a GF parse tree reduces under a language, the ◇ modality witnesses it. -/
theorem gfCheckedExpr_diamond_of_reduces
    {lang : LanguageDef}
    {φ : Pattern → Prop} {node : CheckedExpr} {q : Pattern}
    (hReduce : langReduces lang (gfCheckedExprToPattern node) q)
    (hφ : φ q) :
    langDiamond lang φ (gfCheckedExprToPattern node) := by
  rw [langDiamond_spec]
  exact ⟨q, hReduce, hφ⟩

/-- Executable reduction on a GF tree implies the declarative relation. -/
theorem gfCheckedExpr_exec_implies_reduces
    {lang : LanguageDef} {node : CheckedExpr} {q : Pattern}
    (h : q ∈ rewriteWithContextWithPremises lang (gfCheckedExprToPattern node)) :
    langReduces lang (gfCheckedExprToPattern node) q :=
  exec_to_langReducesUsing .empty lang
    (show langReducesExecUsing .empty lang (gfCheckedExprToPattern node) q from h)

/-- Practical bridge: run the rewriter on a GF tree, check a predicate
    on the result, conclude ◇-satisfaction in the OSLF type system. -/
theorem gfCheckedExpr_diamond_of_exec
    {lang : LanguageDef}
    {φ : Pattern → Prop} {node : CheckedExpr} {q : Pattern}
    (hExec : q ∈ rewriteWithContextWithPremises lang (gfCheckedExprToPattern node))
    (hφ : φ q) :
    langDiamond lang φ (gfCheckedExprToPattern node) :=
  gfCheckedExpr_diamond_of_reduces (gfCheckedExpr_exec_implies_reduces hExec) hφ

end Mettapedia.Languages.GF.GFCoreOSLFBridge
