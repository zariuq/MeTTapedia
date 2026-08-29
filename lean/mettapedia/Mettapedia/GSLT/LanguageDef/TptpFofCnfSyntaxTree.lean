import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
import Mettapedia.GSLT.LanguageDef.CanonicalWire

/-!
# TPTP FOF/CNF syntax trees

This is the closed tree carrier produced from the FOF/CNF ParserPack syntax
algebra.  It preserves every parser node, codepoint, product, list, and option;
the finite node-label type prevents unrecognized parser vocabulary from being
smuggled into later transformations.

The carrier has no reductions.  Parsing and transformations out of it are
separate theories.
-/

namespace Mettapedia.GSLT.LanguageDef.TptpFofCnfSyntaxTree

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
open Mettapedia.GSLT.LanguageDef.TotalGSLT

private def ctor (label category : String)
    (parameters : List (String × String) := []) : GrammarRule := {
  label := label
  category := category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := [.terminal label]
  evalPolicy? := none
}

def labels : List String := [
  "and", "arguments", "application", "atomic", "back-quoted", "iff",
  "implies", "reverse-implies", "xor", "nor", "nand", "cnf",
  "cnf-disjunction", "negative-literal", "negative-paren-literal",
  "positive-literal", "defined-application", "defined-word",
  "disequality", "distinct-object", "equality", "fof", "formula-role",
  "constant", "defined-constant", "system-constant", "number", "distinct",
  "general-empty-list", "general-list", "general-function",
  "general-atomic", "general-variable", "general-number", "general-distinct",
  "general-term", "general-terms", "include", "integer", "lower-word",
  "name-list", "or", "forall", "exists", "rational", "real",
  "single-quoted", "system-application", "system-word", "variable",
  "block-comment", "tptp-file", "line-comment", "negation", "paren",
  "upper-word", "variable-list"]

private def labelCtor (label : String) : GrammarRule :=
  ctor ("tptp-cst:label-" ++ label) "NodeLabel"

/-- Lossless closed carrier for the current FOF/CNF parser-tree vocabulary. -/
def language : LanguageDef := {
  name := "TptpFofCnfSyntaxTree"
  types := [
    { name := "Integer", carrier := .builtinInt },
    "NodeLabel", "SyntaxTree"]
  terms := labels.map labelCtor ++ [
    ctor "tptp-cst:node" "SyntaxTree"
      [("label", "NodeLabel"), ("payload", "SyntaxTree")],
    ctor "tptp-cst:codepoint" "SyntaxTree" [("value", "Integer")],
    ctor "tptp-cst:pair" "SyntaxTree"
      [("left", "SyntaxTree"), ("right", "SyntaxTree")],
    ctor "tptp-cst:cons" "SyntaxTree"
      [("first", "SyntaxTree"), ("rest", "SyntaxTree")],
    ctor "tptp-cst:some" "SyntaxTree" [("value", "SyntaxTree")],
    ctor "tptp-cst:none" "SyntaxTree",
    ctor "tptp-cst:nil" "SyntaxTree"]
  equations := []
  rewrites := []
}

theorem labels_length : labels.length = 57 := by decide

theorem labels_nodup : labels.Nodup := by decide

theorem language_validate : language.validate = [] := by
  decide +kernel

theorem language_inventory :
    language.types.length = 3 ∧ language.terms.length = 64 ∧
      language.rewrites.length = 0 := by
  decide

theorem codepoint_tree_crossing :
    ("tptp-cst:codepoint", "Integer", "SyntaxTree") ∈
      unaryCrossings language := by
  decide

/-- A node label cannot bypass the binary node constructor and become a tree
on its own. -/
theorem no_label_tree_crossing :
    ("tptp-cst:invented-label-tree", "NodeLabel", "SyntaxTree") ∉
      unaryCrossings language := by
  decide

def theory : Mettapedia.GSLT.GSLT :=
  languageGSLT language
    (ReductionRespectsEquations.of_no_equations rfl)

theorem theory_no_step (source target : Pattern) :
    ¬ theory.Step source target := by
  intro reduction
  change langReducesUsing RelationEnv.empty language source target at reduction
  unfold langReducesUsing at reduction
  rcases reduction with ⟨_, step⟩
  cases step with
  | rule ruleMember =>
      change _ ∈ ([] : List RewriteRule) at ruleMember
      simp at ruleMember

def stepDecision : EffectiveStructure.StepDecision theory where
  decideStep _ _ := false
  correct := by
    intro source target
    simp only [Bool.false_eq_true, false_iff]
    exact theory_no_step source target

def oslf := langOSLF language "SyntaxTree"

theorem galois :
    GaloisConnection (langDiamond language) (langBox language) :=
  langGalois language

theorem wire_isSome :
    (CanonicalWire.renderLanguage? language).isSome := by
  decide +kernel

def wire : String :=
  (CanonicalWire.renderLanguage? language).getD ""

theorem wire_nonempty : wire ≠ "" := by
  decide +kernel

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

#print axioms labels_nodup
#print axioms language_validate
#print axioms codepoint_tree_crossing
#print axioms no_label_tree_crossing
#print axioms theory_no_step
#print axioms galois
#print axioms wire_isSome

end Mettapedia.GSLT.LanguageDef.TptpFofCnfSyntaxTree
