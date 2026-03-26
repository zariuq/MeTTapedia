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
open Mettapedia.Languages.GF.SemanticKernelDSL

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

/-- All semantic entailment rewrites (identity + active-passive + tense). -/
@[reducible] def allSemanticRewrites : List RewriteRule :=
  SemanticKernelDSL.allSemanticRewrites

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
  LanguageDef.mk
    sig.grammar
    (allCats.eraseDups.map TypeDecl.plain)
    termRules
    eqRules
    rwRules
    [.vec, .hashBag, .hashSet]
    []
    []

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
