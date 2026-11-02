import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlGeneratedSchemaTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlLambdaAdmission

/-! Recursive closure application uses sorted captured environments and
source pattern references. Every generated function batch is admitted by
the existing grammar-inference and premise-flow checks.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem recursive_row_schema_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (group slot body : Nat) (definitions : List OCaml.Code) (patternCode : Pattern)
    (patternTyped : HasType language captureContext [] patternCode (.base "MlPattern")) :
    HasType language captureContext [] (recursiveRow group slot body patternCode definitions).left (.base "MlConfig") ∧
      HasType language captureContext [] (recursiveRow group slot body patternCode definitions).right (.base "MlConfig") := by
  constructor
  · exact nonbare_constructor_typed terms [("function", .base "MlValue"), ("argument", .base "MlValue"),
      ("continuation", .base "MlContinuation")] _ (by decide +kernel)
      (.cons (closure_schema_typed language terms captureContext [] _ _
        (recursive_function_schema_typed language terms captureContext [] group slot) (environment_capture_typed language []))
        (.cons (argument_capture_typed language []) (.cons (continuation_capture_typed language []) .nil)))
  · exact nonbare_constructor_typed terms [("pattern", .base "MlPattern"), ("value", .base "MlValue"),
      ("body", .base "MlCode"), ("environment", .base "MlEnvironment"), ("continuation", .base "MlContinuation")] _
      (by decide +kernel) (.cons patternTyped (.cons (argument_capture_typed language [])
        (.cons (code_typed language terms captureContext [] body)
          (.cons (recursive_environment_schema_typed language terms captureContext [] group definitions _
            (environment_capture_typed language [])) (.cons (continuation_capture_typed language []) .nil)))))

theorem function_row_admitted (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) (program : OCaml.Program) (pool : List OCaml.MatchPattern)
    (reference index : Nat) (instruction : OCaml.Instruction) (rows : List RewriteRule) (row : RewriteRule)
    (formed : functionRules? program pool reference instruction = some rows) (member : row ∈ rows) :
    ruleObligations snapshot index row = [] := by
  have shapes := function_row_shapes program pool reference instruction rows row formed member
  have fields := function_binding_fields program pool reference instruction rows row formed member
  cases instruction with
  | lambda parameter body => exact lambda_function_admitted snapshot terms types program pool index reference parameter body rows row formed member
  | letRecursive definitions body =>
      obtain ⟨slot, target, parameter, functionBody, patternCode, _, _, resolved, same⟩ :=
        recursive_rule_origin program pool reference body definitions rows row formed member
      have typed : HasType snapshot.language captureContext [] row.left (.base "MlConfig") ∧
          HasType snapshot.language captureContext [] row.right (.base "MlConfig") := by
        rw [same]
        exact recursive_row_schema_typed snapshot.language terms reference slot functionBody definitions patternCode
          (patternReference?_typed snapshot.language terms captureContext [] resolved)
      exact generated_typed_row_admitted snapshot terms index row ⟨shapes.1, shapes.2.1⟩ fields.1 fields.2.1
        shapes.2.2 typed.1 typed.2 fields.2.2.2.2 (by rw [fields.2.2.1]; simp) fields.2.2.2.1
  | _ =>
      simp only [functionRules?] at formed
      cases Option.some.inj formed
      cases member

#print axioms recursive_row_schema_typed
#print axioms function_row_admitted

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
