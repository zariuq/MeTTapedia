import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternSchemaTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternPlanCoverage
import Mettapedia.OSLF.MeTTaIL.ValidatedRuleBounds

/-! Both generated nested-pattern rule forms derive actual admission.
Source validation supplies the no-new-output-capture condition; the schema
typing proof supplies the grammar-inference certificate.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem pattern_row_schema_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (parameter : OCaml.MatchPattern) (index : Nat) (row : RewriteRule) (member : row ∈ patternRules index parameter) :
    HasType language captureContext [] row.left (.base "MlConfig") ∧
      HasType language captureContext [] row.right (.base "MlConfig") := by
  have compiled := pattern_schema_typed language terms [] parameter 0
  have environment := extend_schema_typed language terms captureContext [] (patternAt parameter 0).bindings
    (hole "environment") compiled.2 (environment_capture_typed language [])
  have result := evaluate_schema_typed language terms captureContext [] (hole "body")
    (extend (patternAt parameter 0).bindings (hole "environment")) (hole "continuation")
    (body_capture_typed language []) environment (continuation_capture_typed language [])
  simp only [patternRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · refine ⟨?_, result⟩
    exact nonbare_constructor_typed terms [("pattern", .base "MlPattern"), ("value", .base "MlValue"),
      ("body", .base "MlCode"), ("environment", .base "MlEnvironment"), ("continuation", .base "MlContinuation")] _
      (by decide +kernel) (.cons (patternId_typed language terms captureContext [] index)
        (.cons compiled.1 (.cons (body_capture_typed language [])
          (.cons (environment_capture_typed language []) (.cons (continuation_capture_typed language []) .nil)))))
  · refine ⟨?_, result⟩
    exact nonbare_constructor_typed terms [("pattern", .base "MlPattern"), ("value", .base "MlValue"),
      ("body", .base "MlCode"), ("later", .base "MlClauses"), ("environment", .base "MlEnvironment"),
      ("continuation", .base "MlContinuation")] _ (by decide +kernel)
      (.cons (patternId_typed language terms captureContext [] index) (.cons compiled.1
        (.cons (body_capture_typed language []) (.cons (later_capture_typed language [])
          (.cons (environment_capture_typed language []) (.cons (continuation_capture_typed language []) .nil))))))

theorem pattern_row_admitted (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (valid : snapshot.language.validate = []) (parameter : OCaml.MatchPattern) (patternIndex index : Nat) (row : RewriteRule)
    (authored : row ∈ snapshot.language.rewrites) (member : row ∈ patternRules patternIndex parameter) :
    ruleObligations snapshot index row = [] := by
  have shapes := pattern_rule_shapes parameter patternIndex row member
  have fields := pattern_rule_binding_fields parameter patternIndex row member
  have typed := pattern_row_schema_typed snapshot.language terms parameter patternIndex row member
  exact generated_typed_row_admitted snapshot terms index row ⟨shapes.1, shapes.2.1⟩ fields.1 fields.2.1
    shapes.2.2 typed.1 typed.2 fields.2.2.2 fields.2.2.1
    (LanguageDef.validated_premise_free_bound snapshot.language row valid authored shapes.2.2)

#print axioms pattern_row_schema_typed
#print axioms pattern_row_admitted

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
