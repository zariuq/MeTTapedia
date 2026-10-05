import Mettapedia.Languages.MeTTa.PeTTa.MinimalInstructions
import Mettapedia.OSLF.MeTTaIL.RuleInstances

/-!
# Plain authored rules in MeTTa's equation instruction

Loading a language's premise-free, binder-aligned rules into an atomspace
gives exactly its authored root steps through the existing `eval` instruction.
The statement concerns the equation instruction, not type-directed evaluation,
an arbitrary dialect's dispatch policy, or textual source compilation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleEvaluation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine

/-- Load the authored equations without adding facts or extra reductions. -/
def space (language : LanguageDef) : PeTTaSpace :=
  { facts := [], rules := language.rewrites }

/-- Forward and backward correspondence for the actual minimal instruction. -/
theorem evalInstruction_iff {language : LanguageDef} (plain : PlainRules language)
    (source target : Pattern) :
    MeTTaStep (space language) (.apply "eval" [source]) target ↔
      Step (engineBasePremises RelationEnv.empty) language source target := by
  constructor
  · intro instruction
    generalize requestEq : (.apply "eval" [source] : Pattern) = request at instruction
    cases instruction <;> simp_all
    apply (step_iff_exists_match plain).mpr
    exact ⟨_, by assumption, _, by assumption, by assumption⟩
  · intro authored
    obtain ⟨rule, member, bindings, matched, result⟩ :=
      (step_iff_exists_match plain).mp authored
    exact .evalStep rule bindings source target member (plain rule member).1 matched result

/-- An authored root reduction produces the same singleton equation answer. -/
theorem equationAnswer_of_step {language : LanguageDef} (plain : PlainRules language)
    {source target : Pattern}
    (authored : Step (engineBasePremises RelationEnv.empty) language source target) :
    PeTTaEval (space language) source [target] := by
  obtain ⟨rule, member, bindings, matched, result⟩ :=
    (step_iff_exists_match plain).mp authored
  exact .ruleApp rule bindings source target member (plain rule member).1 matched result

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleEvaluation
