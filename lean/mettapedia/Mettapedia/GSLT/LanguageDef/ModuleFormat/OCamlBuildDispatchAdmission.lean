import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlBuildInference
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlInferredRuleAdmission

/-! Tuple, variant and primitive argument-gathering dispatch is admitted
for arbitrary source code lists, including the empty argument case.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralFirstOrderProjection GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem build_rule_ready (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) (index : Nat) (name : String) (reference : Nat)
    (kind : Pattern) (references : List OCaml.Code) (shape : VectorFirstOrder kind) (closed : kind.freeFvarNames = []) :
    let authored := rule name (node "MlEvaluate" [code reference, hole "environment", hole "continuation"])
      (startArguments kind references (hole "environment") (hole "continuation"))
    let inference := buildInference references.isEmpty
    let binding : GeneralRuleBindingInference.BindingPlan := ⟨inference.spec, .inferredGrammar inference.extraTypes⟩
    rulePlan? snapshot index authored = some ⟨index, authored, binding⟩ ∧ ruleObligations snapshot index authored = [] := by
  apply inferred_rule_ready snapshot terms types index _ (buildInference references.isEmpty) rfl rfl
  · simp [rule, node_freeNames, code_freeNames, hole_freeNames]
  · exact node_vector_all _ _ (vector_list_cons (code_vector reference)
      (vector_list_cons (.metavariable _) (vector_list_cons (.metavariable _) vector_list_nil)))
  · exact startArguments_vector kind references _ _ shape (.metavariable _) (.metavariable _)
  · rfl
  · intro captured member
    cases reversed : references.reverse with
    | nil =>
      simp only [rule, startArguments, reversed, node_freeNames, code_freeNames, hole_freeNames, closed, values, linked,
        List.foldr_nil, List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      exact Or.inr member
    | cons last later =>
      simp only [rule, startArguments, reversed, node_freeNames, code_freeNames, hole_freeNames, closed, codes_closed,
        values, linked, List.foldr_nil, List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      tauto
  · exact build_infer name reference kind references shape closed

theorem tuple_dispatch_admitted (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) (pool : List OCaml.MatchPattern)
    (index reference : Nat) (fields : List OCaml.Code) (row : RewriteRule)
    (formed : compileInstruction? pool reference (.tuple fields) = some row) : ruleObligations snapshot index row = [] := by
  simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
  subst row
  exact (build_rule_ready snapshot terms types index _ reference (node "MlBuildTuple") fields
    (.constructor _ [] (by simp)) (by simp [node_freeNames])).2

theorem variant_dispatch_admitted (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) (pool : List OCaml.MatchPattern)
    (index reference typeId constructor : Nat) (fields : List OCaml.Code) (row : RewriteRule)
    (formed : compileInstruction? pool reference (.variant typeId constructor fields) = some row) : ruleObligations snapshot index row = [] := by
  simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
  subst row
  exact (build_rule_ready snapshot terms types index _ reference (node "MlBuildVariant" [tag typeId constructor]) fields
    (node_vector_all _ _ (vector_list_cons (tag_vector typeId constructor) vector_list_nil))
    (by simp [node_freeNames, tag_freeNames])).2

theorem primitive_closed (operator : OCaml.Primitive) : (primitive operator).freeFvarNames = [] :=
  vector_typed_closed (primitive_vector operator) (primitive_typed baseLanguage rfl FreeTypeContext.empty [] operator)

theorem primitive_dispatch_admitted (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) (pool : List OCaml.MatchPattern)
    (index reference : Nat) (operator : OCaml.Primitive) (arguments : List OCaml.Code) (row : RewriteRule)
    (formed : compileInstruction? pool reference (.primitive operator arguments) = some row) : ruleObligations snapshot index row = [] := by
  simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
  subst row
  exact (build_rule_ready snapshot terms types index _ reference (node "MlBuildPrimitive" [primitive operator]) arguments
    (node_vector_all _ _ (vector_list_cons (primitive_vector operator) vector_list_nil))
    (by simp [node_freeNames, primitive_closed])).2

#print axioms build_rule_ready
#print axioms tuple_dispatch_admitted
#print axioms variant_dispatch_admitted
#print axioms primitive_dispatch_admitted

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
