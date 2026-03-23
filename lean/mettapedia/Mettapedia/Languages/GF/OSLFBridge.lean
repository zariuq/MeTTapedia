import GFCore.Syntax
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
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

namespace Mettapedia.Languages.GF.OSLFBridge

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.CategoryBridge
open GFCore

-- ═══════════════════════════════════════════════════════════════════
-- Phase 1: Core bridge functions
-- ═══════════════════════════════════════════════════════════════════

/-- Convert a GFCore.CheckedExpr (verified parse tree) to an OSLF Pattern.
    Leaves (lexical items) become free variables; applications become
    Pattern.apply with the function name.

    This is the central bridge — all downstream semantic evaluation
    passes through this function. -/
def gfCheckedExprToPattern (e : CheckedExpr) : Pattern :=
  match e with
  | .node decl args =>
    if args.isEmpty then .fvar decl.name
    else .apply decl.name (args.toList.map fun a => gfCheckedExprToPattern a)
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

-- ═══════════════════════════════════════════════════════════════════
-- Phase 2: Rewrite rules (RGL-universal, no HandCrafted dependency)
-- ═══════════════════════════════════════════════════════════════════

/-- UseN elimination: UseN(x) ~> x.
    In Czech, N = CN (no articles), so UseN is identity. -/
def useNElimRewrite : RewriteRule :=
  { name := "UseNElim"
  , typeContext := [("x", TypeExpr.base "N")]
  , premises := []
  , left := .apply "UseN" [.fvar "x"]
  , right := .fvar "x" }

/-- PositA elimination: PositA(x) ~> x.
    Positive adjective degree is identity. -/
def positAElimRewrite : RewriteRule :=
  { name := "PositAElim"
  , typeContext := [("x", TypeExpr.base "A")]
  , premises := []
  , left := .apply "PositA" [.fvar "x"]
  , right := .fvar "x" }

/-- UseN identity equation: UseN(x) = x (bidirectional). -/
def useNIdentityEquation : Equation :=
  { name := "UseNIdentity"
  , typeContext := [("x", TypeExpr.base "N")]
  , premises := []
  , left := .apply "UseN" [.fvar "x"]
  , right := .fvar "x" }

/-- UseComp elimination: UseComp(x) ~> x. -/
def useCompElimRewrite : RewriteRule :=
  { name := "UseCompElim"
  , typeContext := [("x", TypeExpr.base "Comp")]
  , premises := []
  , left := .apply "UseComp" [.fvar "x"]
  , right := .fvar "x" }

/-- UseV elimination: UseV(x) ~> x. -/
def useVElimRewrite : RewriteRule :=
  { name := "UseVElim"
  , typeContext := [("x", TypeExpr.base "V")]
  , premises := []
  , left := .apply "UseV" [.fvar "x"]
  , right := .fvar "x" }

/-- UseN2 elimination: UseN2(x) ~> x. -/
def useN2ElimRewrite : RewriteRule :=
  { name := "UseN2Elim"
  , typeContext := [("x", TypeExpr.base "N2")]
  , premises := []
  , left := .apply "UseN2" [.fvar "x"]
  , right := .fvar "x" }

/-- UseA2 elimination: UseA2(x) ~> x. -/
def useA2ElimRewrite : RewriteRule :=
  { name := "UseA2Elim"
  , typeContext := [("x", TypeExpr.base "A2")]
  , premises := []
  , left := .apply "UseA2" [.fvar "x"]
  , right := .fvar "x" }

/-- All identity-wrapper elimination rewrites.
    These give ◇/□ non-vacuous behavioral content. -/
def allIdentityRewrites : List RewriteRule :=
  [ useNElimRewrite, positAElimRewrite, useCompElimRewrite
  , useVElimRewrite, useN2ElimRewrite, useA2ElimRewrite ]

/-- Active-passive rewrite:
    PredVP(np1, ComplSlash(SlashV2a(v), np2)) ⇝ PredVP(np2, PassV2(v)).
    Direction: active → passive (converse does not hold). -/
def activePassiveRewrite : RewriteRule :=
  { name := "ActivePassive"
  , typeContext := [("v", TypeExpr.base "V2"), ("np1", TypeExpr.base "NP"),
                    ("np2", TypeExpr.base "NP")]
  , premises := []
  , left := .apply "PredVP" [.fvar "np1",
              .apply "ComplSlash" [.apply "SlashV2a" [.fvar "v"], .fvar "np2"]]
  , right := .apply "PredVP" [.fvar "np2", .apply "PassV2" [.fvar "v"]] }

/-- Present tense: UseCl(TTAnt(TPres, ASimul), PPos, cl) ⇝ ⊛temporal(cl, 0). -/
def presentTenseRewrite : RewriteRule :=
  { name := "PresentTense"
  , typeContext := [("cl", TypeExpr.base "Cl")]
  , premises := []
  , left := .apply "UseCl" [.apply "TTAnt" [.apply "TPres" [], .apply "ASimul" []], .apply "PPos" [], .fvar "cl"]
  , right := .apply "⊛temporal" [.fvar "cl", .apply "0" []] }

/-- Past tense: UseCl(TTAnt(TPast, ASimul), PPos, cl) ⇝ ⊛temporal(cl, -1). -/
def pastTenseRewrite : RewriteRule :=
  { name := "PastTense"
  , typeContext := [("cl", TypeExpr.base "Cl")]
  , premises := []
  , left := .apply "UseCl" [.apply "TTAnt" [.apply "TPast" [], .apply "ASimul" []], .apply "PPos" [], .fvar "cl"]
  , right := .apply "⊛temporal" [.fvar "cl", .apply "-1" []] }

/-- Future tense: UseCl(TTAnt(TFut, ASimul), PPos, cl) ⇝ ⊛temporal(cl, 1). -/
def futureTenseRewrite : RewriteRule :=
  { name := "FutureTense"
  , typeContext := [("cl", TypeExpr.base "Cl")]
  , premises := []
  , left := .apply "UseCl" [.apply "TTAnt" [.apply "TFut" [], .apply "ASimul" []], .apply "PPos" [], .fvar "cl"]
  , right := .apply "⊛temporal" [.fvar "cl", .apply "1" []] }

/-- All tense rewrites. -/
def allTenseRewrites : List RewriteRule :=
  [ presentTenseRewrite, pastTenseRewrite, futureTenseRewrite ]

/-- All semantic entailment rewrites (identity + active-passive + tense). -/
def allSemanticRewrites : List RewriteRule :=
  allIdentityRewrites ++ [ activePassiveRewrite ] ++ allTenseRewrites

-- ═══════════════════════════════════════════════════════════════════
-- Phase 3: LanguageDef construction from GrammarSig
-- ═══════════════════════════════════════════════════════════════════

/-- Build an OSLF LanguageDef from a real GFCore GrammarSig.
    Categories are extracted from function declarations.
    Rewrites and equations are passed in (default: RGL semantics). -/
def gfSigToLanguageDef
    (sig : GrammarSig)
    (rwRules : List RewriteRule := [])
    (eqRules : List Equation := []) : LanguageDef :=
  let allCats := sig.funs.fold (init := ([] : List String)) fun acc _ d =>
    acc ++ d.argCats.toList ++ [d.resultCat]
  let termRules := sig.funs.fold (init := []) fun acc _ d =>
      gfFunDeclToGrammarRule d :: acc
  open scoped Mettapedia.OSLF.MeTTaIL.LanguageDefDSL in
  languageDef! {
    name : sig.grammar,
    types : allCats.eraseDups,
    terms : termRules,
    equations : eqRules,
    rewrites : rwRules,
    logic : [],
    oracles : [],
    congruenceCollections : [.vec, .hashBag, .hashSet]
  }

/-- Build the RGL LanguageDef with standard semantic rewrites. -/
def gfRGLLanguageDef (sig : GrammarSig) : LanguageDef :=
  gfSigToLanguageDef sig allSemanticRewrites [useNIdentityEquation]

-- ═══════════════════════════════════════════════════════════════════
-- Phase 4: Derived OSLF constructions
-- ═══════════════════════════════════════════════════════════════════

/-- Rewrite system induced by a GF grammar with process sort "S". -/
noncomputable def gfRewriteSystem (sig : GrammarSig) :=
  langRewriteSystem (gfRGLLanguageDef sig) "S"

/-- Full OSLF type system for a GF grammar. -/
noncomputable def gfOSLF (sig : GrammarSig) :=
  langOSLF (gfRGLLanguageDef sig) "S"

/-- Galois connection ◇ ⊣ □ for any GF grammar.
    Comes for free from the OSLF framework (langGalois). -/
theorem gfGrammar_galois (sig : GrammarSig) :
    GaloisConnection
      (langDiamond (gfRGLLanguageDef sig))
      (langBox (gfRGLLanguageDef sig)) :=
  langGalois (gfRGLLanguageDef sig)

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

end Mettapedia.Languages.GF.OSLFBridge
