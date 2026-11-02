import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlLiteralAdmission

/-! Argument builders infer captures from their authored empty/nonempty
continuations. The code list remains an opaque closed payload.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralRuleBindingGrammar GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

def emptyBuildOccurrences : List Occurrence := [⟨⟨"ml:continuation", .right, [2]⟩, [], .base "MlContinuation"⟩]
def nonemptyBuildOccurrences : List Occurrence :=
  [⟨⟨"ml:environment", .right, [1]⟩, [], .base "MlEnvironment"⟩,
   ⟨⟨"ml:environment", .right, [2, 2]⟩, [], .base "MlEnvironment"⟩,
   ⟨⟨"ml:continuation", .right, [2, 4]⟩, [], .base "MlContinuation"⟩]

def buildInference (empty : Bool) : Inference :=
  let rows := evaluateOccurrences ++ (if empty then emptyBuildOccurrences else nonemptyBuildOccurrences)
  let context := [("ml:environment", TypeExpr.base "MlEnvironment"), ("ml:continuation", .base "MlContinuation")]
  ⟨context, specification context rows, rows⟩

theorem codes_closed (references : List OCaml.Code) : (codes (references.map code)).freeFvarNames = [] :=
  vector_typed_closed (codes_vector references) (codes_typed baseLanguage rfl FreeTypeContext.empty [] references)

theorem empty_build_inspect (kind : Pattern) (shape : VectorFirstOrder kind) (closed : kind.freeFvarNames = []) :
    inspect baseLanguage [] .right [] (.base "MlConfig")
      (node "MlBuildConfig" [kind, node "MlValueNil", hole "continuation"]) = some emptyBuildOccurrences := by
  have payloadAddresses := vector_addresses_closed shape closed
  simp only [inspect, node, addresses, argumentAddresses, payloadAddresses, hole, List.nil_append, List.append_nil]
  simp [GeneralRuleBindingGrammar.constructor?, baseLanguage, contextAt?, usesBareCollection?, parameterType?,
    matchesParameterRepresentation?, guard, emptyBuildOccurrences]

theorem nonempty_build_inspect (kind : Pattern) (shape : VectorFirstOrder kind) (closed : kind.freeFvarNames = [])
    (last : OCaml.Code) (later : List OCaml.Code) :
    inspect baseLanguage [] .right [] (.base "MlConfig")
      (node "MlEvaluate" [code last, hole "environment", node "MlKBuild"
        [kind, codes (later.map code), hole "environment", node "MlValueNil", hole "continuation"]]) =
      some nonemptyBuildOccurrences := by
  have payloadAddresses := vector_addresses_closed shape closed
  have laterAddresses := vector_addresses_closed (codes_vector later) (codes_closed later)
  simp only [inspect, node, addresses, argumentAddresses, payloadAddresses, laterAddresses, code_addresses, hole,
    List.nil_append, List.append_nil]
  simp [GeneralRuleBindingGrammar.constructor?, baseLanguage, contextAt?, usesBareCollection?, parameterType?,
    matchesParameterRepresentation?, guard, nonemptyBuildOccurrences]

theorem build_infer (name : String) (reference : Nat) (kind : Pattern) (references : List OCaml.Code)
    (shape : VectorFirstOrder kind) (closed : kind.freeFvarNames = []) :
    infer? baseLanguage (rule name (node "MlEvaluate" [code reference, hole "environment", hole "continuation"])
      (startArguments kind references (hole "environment") (hole "continuation"))) = some (buildInference references.isEmpty) := by
  cases reversed : references.reverse with
  | nil =>
    have empty : references.isEmpty = true := by simp_all
    simp only [startArguments, reversed, values, linked, List.foldr_nil]
    simp only [infer?, rule, evaluate_head, evaluate_inspect,
      empty_build_inspect kind shape closed, Option.bind_eq_bind, Option.bind_some]
    simp [empty, buildInference, evaluateOccurrences, emptyBuildOccurrences, implicitTypes, consistent,
      lookupType, unique?, specification, dependencyRows, admittedFor, dependencies?, elaborate,
      dependencySortsDeclared, occurrenceDeclared, occurrenceDepthAtSite?, sitePattern?, siteBinderDepth?,
      occurrenceAt?, occurrenceDepthAt?, node, hole]
    decide +kernel
  | cons last later =>
    have empty : references.isEmpty = false := by cases references <;> simp_all
    simp only [startArguments, reversed, values, linked, List.foldr_nil]
    simp only [infer?, rule, evaluate_head, evaluate_inspect,
      nonempty_build_inspect kind shape closed last later, Option.bind_eq_bind, Option.bind_some]
    simp [empty, buildInference, evaluateOccurrences, nonemptyBuildOccurrences, implicitTypes, consistent,
      lookupType, unique?, specification, dependencyRows, admittedFor, dependencies?, elaborate,
      dependencySortsDeclared, occurrenceDeclared, occurrenceDepthAtSite?, sitePattern?, siteBinderDepth?,
      occurrenceAt?, occurrenceDepthAt?, node, hole]
    decide +kernel

#print axioms empty_build_inspect
#print axioms nonempty_build_inspect
#print axioms build_infer

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
