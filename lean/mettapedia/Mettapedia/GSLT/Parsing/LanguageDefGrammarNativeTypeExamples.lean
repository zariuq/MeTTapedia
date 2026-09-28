import Mettapedia.GSLT.Parsing.LanguageDefGrammarNativeType
import Mathlib.Tactic

/-!
# Positive and negative controls for grammar-derived interpretation

These exercise the generic construction on a small recursive source grammar.
They are not a substitute for constructing the complete TPTP interpretation.
In particular, the final negative control distinguishes operational native
typing from the separate obligation to choose a faithful interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.LanguageDefGrammarNativeTypeExamples

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing.LanguageDefGrammarAlgebra
open Mettapedia.GSLT.Parsing.LanguageDefGrammarNativeType
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySortedEvaluation
open Mettapedia.OSLF.Framework.PathTypeSynthesis

def language : LanguageDef where
  name := "BinaryFormulaExample"
  types := [.plain "Formula"]
  terms := [
    { label := "P", category := "Formula", params := [], syntaxPattern := [.terminal "p"] },
    { label := "Q", category := "Formula", params := [], syntaxPattern := [.terminal "q"] },
    { label := "And", category := "Formula",
      params := [.simple "left" (.base "Formula"), .simple "right" (.base "Formula")],
      syntaxPattern := [.terminal "(", .nonTerminal "left", .terminal "&",
        .nonTerminal "right", .terminal ")"] }]
  equations := []
  rewrites := []

def binding : Binding where
  literalRef := some
  lexicalSortRef := fun _ => none
  categoryRef := id
  ruleRef := id

/-- The constructor list is computed from the source, not copied into the test. -/
def rules : List CompiledRule :=
  (compileRules? binding language).get (by decide)

theorem compiled : compileRules? binding language = some rules := rfl

def compactOperation (connective : String) :
    {inputs : List String} → {output : String} → Operation rules inputs output →
    FamilyList (fun _ : String => Pattern) inputs → Pattern
  | _, _, .at ⟨0, _⟩, .nil => .apply "p" []
  | _, _, .at ⟨1, _⟩, .nil => .apply "q" []
  | _, _, .at ⟨2, _⟩, .cons left (.cons right .nil) =>
      .apply connective [left, right]
  | _, _, .at ⟨index + 3, bound⟩, _ => False.elim (by
      have impossible : index + 3 < 3 := bound
      omega)

def compact (connective : String) : Interpretation rules where
  Carrier := fun _ => Pattern
  operation := compactOperation connective

def p : ConstructionTree (syntaxAlgebra rules) "Formula" :=
  .apply (.at ⟨0, by decide⟩) .nil

def q : ConstructionTree (syntaxAlgebra rules) "Formula" :=
  .apply (.at ⟨1, by decide⟩) .nil

def conjunction (left right : ConstructionTree (syntaxAlgebra rules) "Formula") :
    ConstructionTree (syntaxAlgebra rules) "Formula" :=
  .apply (.at ⟨2, by decide⟩) (.cons left (.cons right .nil))

def sample := conjunction p (conjunction q p)

def expected : Pattern :=
  .apply "∧" [.apply "p" [], .apply "∧" [.apply "q" [], .apply "p" []]]

theorem direct_compact_result : (directInterpreter (compact "∧")).run sample = expected := rfl

/-- info: true -/
#guard_msgs in
#eval
  let output : Pattern := (directInterpreter (compact "∧")).run sample
  decide (output = expected)

theorem nested_result_is_native :
    (pathOSLF (evaluationGSLT (compact "∧").algebra "Formula")).satisfies
      (initialState (compact "∧") sample)
      (resultNativeType (compact "∧").algebra expected).pred :=
  (result_native_iff (compact "∧") sample expected).mpr rfl

/-- All source terminals and recursive child occurrences are accounted for. -/
theorem exact_source_observation :
    Derives language "Formula" ["(", "p", "&", "(", "q", "&", "p", ")", ")"]
      (.apply "And" [.apply "P" [], .apply "And" [.apply "Q" [], .apply "P" []]]) :=
  (source_derives_iff_route compiled _ _ _).mpr ⟨sample, rfl⟩

/-- A wrong result cannot inhabit the native type of the intended computation. -/
theorem wrong_connective_not_native :
    ¬ (pathOSLF (evaluationGSLT (compact "∧").algebra "Formula")).satisfies
      (initialState (compact "∧") (conjunction p q))
      (resultNativeType (compact "∧").algebra
        (.apply "∨" [.apply "p" [], .apply "q" []])).pred := by
  intro native
  have impossible := (result_native_iff (compact "∧") (conjunction p q) _).mp native
  exact (by decide : (.apply "∧" [.apply "p" [], .apply "q" []] : Pattern) ≠
    .apply "∨" [.apply "p" [], .apply "q" []]) impossible

/-- Ordered child occurrences cannot be exchanged by a specialized evaluator. -/
theorem swapped_children_not_native :
    ¬ (pathOSLF (evaluationGSLT (compact "∧").algebra "Formula")).satisfies
      (initialState (compact "∧") (conjunction p q))
      (resultNativeType (compact "∧").algebra
        (.apply "∧" [.apply "q" [], .apply "p" []])).pred := by
  intro native
  have impossible := (result_native_iff (compact "∧") (conjunction p q) _).mp native
  exact (by decide : (.apply "∧" [.apply "p" [], .apply "q" []] : Pattern) ≠
    .apply "∧" [.apply "q" [], .apply "p" []]) impossible

/-- Operational correctness does not select the right interpretation: changing
the declared operation changes the theory whose native type is generated. -/
theorem different_interpretation_has_different_native_result :
    (pathOSLF (evaluationGSLT (compact "∨").algebra "Formula")).satisfies
      (initialState (compact "∨") (conjunction p q))
      (resultNativeType (compact "∨").algebra
        (.apply "∨" [.apply "p" [], .apply "q" []])).pred :=
  (result_native_iff (compact "∨") (conjunction p q) _).mpr rfl

/-- Native evidence for the changed interpretation cannot license that output
under the intended interpretation. -/
theorem changed_interpretation_cannot_be_admitted :
    ¬ ∃ interpreter : AdmittedInterpreter (compact "∧"),
      interpreter.run (conjunction p q) = interpret (compact "∨") (conjunction p q) := by
  rintro ⟨interpreter, wrong⟩
  have correct := admitted_interpreter_agrees interpreter (conjunction p q)
  have impossible := wrong.symm.trans correct
  exact (by decide : (.apply "∨" [.apply "p" [], .apply "q" []] : Pattern) ≠
    .apply "∧" [.apply "p" [], .apply "q" []]) impossible

#print axioms nested_result_is_native
#print axioms exact_source_observation
#print axioms wrong_connective_not_native
#print axioms swapped_children_not_native
#print axioms changed_interpretation_cannot_be_admitted

end Mettapedia.GSLT.Parsing.LanguageDefGrammarNativeTypeExamples
