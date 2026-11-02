import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlInstructionShapes
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFunctionBindingProperties

/-! Every generated instruction row reads an evaluation configuration and
retains its caller continuation. Environment lookup adds a finite prefix;
all other instructions read the complete captured environment.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem instruction_left_environment (pool : List OCaml.MatchPattern) (reference : OCaml.Code) (instruction : OCaml.Instruction)
    (compiled : RewriteRule) (formed : compileInstruction? pool reference instruction = some compiled) :
    ∃ captured, compiled.left = node "MlEvaluate" [code reference, captured, hole "continuation"] := by
  cases instruction with
  | letValue parameter argument body =>
      cases resolved : patternReference? pool parameter <;>
        simp only [compileInstruction?, resolved, Option.bind_eq_bind, Option.bind_none, Option.bind_some,
          Option.pure_def, Option.some.injEq, reduceCtorEq] at formed
      cases formed
      exact ⟨_, rfl⟩
  | matchValue scrutinee clauses =>
      cases resolved : clauseList? pool clauses <;>
        simp only [compileInstruction?, resolved, Option.bind_eq_bind, Option.bind_none, Option.bind_some,
          Option.pure_def, Option.some.injEq, reduceCtorEq] at formed
      cases formed
      exact ⟨_, rfl⟩
  | _ =>
      simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
      cases formed
      exact ⟨_, rfl⟩

theorem instruction_input_properties (pool : List OCaml.MatchPattern) (reference : OCaml.Code) (instruction : OCaml.Instruction)
    (compiled : RewriteRule) (formed : compileInstruction? pool reference instruction = some compiled) :
    compiled.left.freeFvarNames ≠ [] ∧
      GeneralRuleBindingGrammar.headType? baseLanguage [] [] compiled.left = some (.base "MlConfig") := by
  obtain ⟨captured, same⟩ := instruction_left_environment pool reference instruction compiled formed
  constructor
  · intro empty
    have present : "ml:continuation" ∈ compiled.left.freeFvarNames := by
      rw [same]
      simp only [node_freeNames, code_freeNames, hole_freeNames, List.flatMap_cons, List.flatMap_nil,
        List.nil_append, List.append_nil, List.mem_append, List.mem_singleton]
      exact Or.inr rfl
    rw [empty] at present
    cases present
  · rw [same]
    simp only [node, GeneralRuleBindingGrammar.headType?]
    decide +kernel

#print axioms instruction_left_environment
#print axioms instruction_input_properties

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
