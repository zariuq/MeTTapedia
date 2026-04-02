import GFCore.Syntax
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.Formula
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.MeTTaIL.Engine

/-!
# GF Real Syntax → OSLF Bridge

Minimal authoritative bridge for the real GFCore → `LanguageDef` lane.

This file contains only the syntax-side material needed to map generated or
checked GF artifacts into the MeTTaIL DSL:

- `GFCore.CheckedExpr -> Pattern`
- `GFCore.FunDecl / GrammarSig -> LanguageDef`
- the induced syntax-only OSLF layer (`gfSyntaxLanguageDef`, `gfSyntaxOSLF`)
- generic soundness lemmas for checked GF trees

It intentionally excludes the legacy authored semantic overlay. That older
overlay remains in `/home/zar/claude/lean-projects/mettapedia/Mettapedia/Languages/GF/OSLFBridge.lean`
for explicitly legacy modules, but trust-critical GF imports should prefer this
file.
-/

namespace Mettapedia.Languages.GF.GFCoreOSLFBridge

open GFCore
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.Framework.TypeSynthesis

/-- Convert a checked GF tree into the canonical MeTTaIL pattern surface. -/
def gfCheckedExprToPattern (e : CheckedExpr) : Pattern :=
  match e with
  | .node decl args =>
    .apply decl.name (args.toList.map fun a => gfCheckedExprToPattern a)
termination_by sizeOf e
decreasing_by
  simp_wf
  have h1 := List.sizeOf_lt_of_mem ‹a ∈ args.toList›
  cases args with
  | mk data =>
      simp only [Array.mk.sizeOf_spec] at h1 ⊢
      omega

/-- Lower a GF declaration to a `LanguageDef` grammar rule. -/
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

/-- Kernel-reducible `LanguageDef` construction from a literal function list. -/
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

/-- `LanguageDef` construction from a real GFCore `GrammarSig`. -/
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

/-- Authoritative syntax-only `LanguageDef` from a literal GF function list. -/
def gfSyntaxLanguageDefFromList
    (grammarName : String)
    (funs : List (String × FunDecl)) : LanguageDef :=
  gfFunsListToLanguageDef grammarName funs [] [] [] []

/-- Authoritative syntax-only `LanguageDef` from a real `GrammarSig`. -/
def gfSyntaxLanguageDef (sig : GrammarSig) : LanguageDef :=
  gfSigToLanguageDef sig [] [] [] []

/-- Syntax-only rewrite system induced by the real GF grammar. -/
noncomputable def gfSyntaxRewriteSystem (sig : GrammarSig) :=
  langRewriteSystem (gfSyntaxLanguageDef sig) "S"

/-- Syntax-only OSLF layer induced by the real GF grammar. -/
noncomputable def gfSyntaxOSLF (sig : GrammarSig) :=
  langOSLF (gfSyntaxLanguageDef sig) "S"

/-- Galois connection for the syntax-only GF lane. -/
theorem gfSyntaxGrammar_galois (sig : GrammarSig) :
    GaloisConnection
      (langDiamond (gfSyntaxLanguageDef sig))
      (langBox (gfSyntaxLanguageDef sig)) :=
  langGalois (gfSyntaxLanguageDef sig)

open Mettapedia.OSLF.MeTTaIL.Engine

/-- If `checkLangUsing` reports `sat` on a checked GF tree, semantics hold. -/
theorem gfCheckedExpr_checkSat_sound
    {lang : LanguageDef}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    {fuel : Nat} {node : CheckedExpr} {φ : OSLFFormula}
    (h : checkLangUsing .empty lang I_check fuel
           (gfCheckedExprToPattern node) φ = .sat) :
    sem (langReduces lang) I_sem φ (gfCheckedExprToPattern node) :=
  checkLangUsing_sat_sound h_atoms h

/-- A checked GF tree that reduces witnesses `◇`. -/
theorem gfCheckedExpr_diamond_of_reduces
    {lang : LanguageDef}
    {φ : Pattern → Prop} {node : CheckedExpr} {q : Pattern}
    (hReduce : langReduces lang (gfCheckedExprToPattern node) q)
    (hφ : φ q) :
    langDiamond lang φ (gfCheckedExprToPattern node) := by
  rw [langDiamond_spec]
  exact ⟨q, hReduce, hφ⟩

/-- Executable reduction on a checked GF tree implies the declarative relation. -/
theorem gfCheckedExpr_exec_implies_reduces
    {lang : LanguageDef} {node : CheckedExpr} {q : Pattern}
    (h : q ∈ rewriteWithContextWithPremises lang (gfCheckedExprToPattern node)) :
    langReduces lang (gfCheckedExprToPattern node) q :=
  exec_to_langReducesUsing .empty lang
    (show langReducesExecUsing .empty lang (gfCheckedExprToPattern node) q from h)

/-- Practical checked-tree bridge from executable reduction to `◇`. -/
theorem gfCheckedExpr_diamond_of_exec
    {lang : LanguageDef}
    {φ : Pattern → Prop} {node : CheckedExpr} {q : Pattern}
    (hExec : q ∈ rewriteWithContextWithPremises lang (gfCheckedExprToPattern node))
    (hφ : φ q) :
    langDiamond lang φ (gfCheckedExprToPattern node) :=
  gfCheckedExpr_diamond_of_reduces (gfCheckedExpr_exec_implies_reduces hExec) hφ

end Mettapedia.Languages.GF.GFCoreOSLFBridge
