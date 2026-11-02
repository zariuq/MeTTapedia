import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCaptureSchemaTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlBaseSchemaTyping

/-! Generated evaluation and recursive-environment schemas inhabit their
authored O0 sorts. Runtime capture names keep their source-schema types.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem evaluate_schema_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (reference captured rest : Pattern)
    (codeTyped : HasType language free bound reference (.base "MlCode"))
    (environmentTyped : HasType language free bound captured (.base "MlEnvironment"))
    (restTyped : HasType language free bound rest (.base "MlContinuation")) :
    HasType language free bound (node "MlEvaluate" [reference, captured, rest]) (.base "MlConfig") :=
  nonbare_constructor_typed terms [("code", .base "MlCode"), ("environment", .base "MlEnvironment"),
    ("continuation", .base "MlContinuation")] _ (by decide +kernel)
    (.cons codeTyped (.cons environmentTyped (.cons restTyped .nil)))

theorem return_schema_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (datum rest : Pattern)
    (valueTyped : HasType language free bound datum (.base "MlValue"))
    (restTyped : HasType language free bound rest (.base "MlContinuation")) :
    HasType language free bound (node "MlReturn" [datum, rest]) (.base "MlConfig") :=
  nonbare_constructor_typed terms [("value", .base "MlValue"), ("continuation", .base "MlContinuation")] _
    (by decide +kernel) (.cons valueTyped (.cons restTyped .nil))

theorem recursive_function_schema_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (group slot : Nat) :
    HasType language free bound (node "MlRecursiveFunction" [code group, code slot]) (.base "MlFunction") :=
  nonbare_constructor_typed terms [("group", .base "MlCode"), ("slot", .base "MlCode")] _
    (by decide +kernel) (.cons (code_typed language terms free bound group) (.cons (code_typed language terms free bound slot) .nil))

theorem closure_schema_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (function captured : Pattern)
    (functionTyped : HasType language free bound function (.base "MlFunction"))
    (environmentTyped : HasType language free bound captured (.base "MlEnvironment")) :
    HasType language free bound (node "MlClosure" [function, captured]) (.base "MlValue") :=
  nonbare_constructor_typed terms [("function", .base "MlFunction"), ("captured", .base "MlEnvironment")] _
    (by decide +kernel) (.cons functionTyped (.cons environmentTyped .nil))

theorem recursive_environment_schema_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (group : Nat) (definitions : List OCaml.Code) (captured : Pattern)
    (environmentTyped : HasType language free bound captured (.base "MlEnvironment")) :
    HasType language free bound (recursiveEnvironment group definitions captured) (.base "MlEnvironment") := by
  apply extend_schema_typed language terms free bound _ captured _ environmentTyped
  intro item member
  obtain ⟨slot, _, same⟩ := List.mem_map.mp member
  subst item
  exact closure_schema_typed language terms free bound _ captured
    (recursive_function_schema_typed language terms free bound group slot) environmentTyped

theorem generated_typed_row_admitted (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (index : Nat) (row : RewriteRule) (shapes : VectorFirstOrder row.left ∧ VectorFirstOrder row.right)
    (omitted : row.bindings = none) (empty : row.typeContext = []) (premiseFree : row.premises = [])
    (leftTyped : HasType snapshot.language captureContext [] row.left (.base "MlConfig"))
    (rightTyped : HasType snapshot.language captureContext [] row.right (.base "MlConfig"))
    (head : GeneralRuleBindingGrammar.headType? baseLanguage [] [] row.left = some (.base "MlConfig"))
    (captures : row.left.freeFvarNames ≠ [])
    (bound : ∀ name ∈ row.right.freeFvarNames, name ∈ row.left.freeFvarNames) :
    ruleObligations snapshot index row = [] := by
  obtain ⟨binding, _, checked⟩ := typed_vector_rule_ready snapshot index row captureContext (.base "MlConfig")
    (grammar_labels_unique snapshot.language terms) (base_collection_deterministic snapshot.language terms)
    omitted empty premiseFree shapes.1 shapes.2 leftTyped rightTyped
    (by rw [GeneralRuleBindingGrammar.headType?_transport terms]; exact head) captures bound
  exact checked

#print axioms recursive_environment_schema_typed
#print axioms generated_typed_row_admitted

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
