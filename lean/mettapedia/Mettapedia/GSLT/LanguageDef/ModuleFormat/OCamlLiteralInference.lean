import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlInferenceConstants

/-! Literal dispatch infers its capture sorts from the authored O0 grammar.
Source code and literal payloads remain opaque closed constants.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralRuleBindingGrammar
open Mettapedia.GSLT.LanguageDef.WellSorted

def evaluateOccurrences : List Occurrence :=
  [⟨⟨"ml:environment", .left, [1]⟩, [], .base "MlEnvironment"⟩,
   ⟨⟨"ml:continuation", .left, [2]⟩, [], .base "MlContinuation"⟩]

def literalReturnOccurrences : List Occurrence :=
  [⟨⟨"ml:continuation", .right, [1]⟩, [], .base "MlContinuation"⟩]

theorem evaluate_head (reference : Nat) :
    headType? baseLanguage [] [] (node "MlEvaluate" [code reference, hole "environment", hole "continuation"]) =
      some (.base "MlConfig") := by
  simp only [headType?, node]
  decide +kernel

theorem evaluate_inspect (reference : Nat) :
    inspect baseLanguage [] .left [] (.base "MlConfig")
      (node "MlEvaluate" [code reference, hole "environment", hole "continuation"]) = some evaluateOccurrences := by
  simp only [inspect, node, addresses, argumentAddresses, code_addresses, hole,
    List.nil_append, List.append_nil]
  simp [GeneralRuleBindingGrammar.constructor?, baseLanguage, contextAt?, usesBareCollection?, parameterType?,
    matchesParameterRepresentation?, guard, evaluateOccurrences]

theorem literal_return_inspect (datum : OCaml.Literal) :
    inspect baseLanguage [] .right [] (.base "MlConfig")
      (node "MlReturn" [literal datum, hole "continuation"]) = some literalReturnOccurrences := by
  simp only [inspect, node, addresses, argumentAddresses, literal_addresses, hole,
    List.nil_append, List.append_nil, List.mapM_cons, List.mapM_nil]
  simp [GeneralRuleBindingGrammar.constructor?, baseLanguage, contextAt?, usesBareCollection?, parameterType?,
    matchesParameterRepresentation?, guard, literalReturnOccurrences]

#print axioms evaluate_head
#print axioms evaluate_inspect
#print axioms literal_return_inspect

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
