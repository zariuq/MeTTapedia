import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlGeneratedSchemaTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlInstructionInput

/-! Arbitrarily long environment-lookup prefixes and recursive groups
derive actual selected-rule admission from their source-schema typing.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem recursive_dispatch_admitted (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (pool : List OCaml.MatchPattern) (index reference : Nat) (definitions : List OCaml.Code) (body : OCaml.Code)
    (row : RewriteRule) (formed : compileInstruction? pool reference (.letRecursive definitions body) = some row) :
    ruleObligations snapshot index row = [] := by
  have shapes := instruction_shapes pool reference (.letRecursive definitions body) row formed
  have input := instruction_input_properties pool reference (.letRecursive definitions body) row formed
  simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
  subst row
  apply generated_typed_row_admitted snapshot terms index _ ⟨shapes.1, shapes.2.1⟩ rfl rfl rfl
  · exact evaluate_schema_typed snapshot.language terms captureContext [] _ _ _
      (code_typed snapshot.language terms captureContext [] reference)
      (environment_capture_typed snapshot.language []) (continuation_capture_typed snapshot.language [])
  · exact evaluate_schema_typed snapshot.language terms captureContext [] _ _ _
      (code_typed snapshot.language terms captureContext [] body)
      (recursive_environment_schema_typed snapshot.language terms captureContext [] reference definitions _
        (environment_capture_typed snapshot.language []))
      (continuation_capture_typed snapshot.language [])
  · exact input.2
  · exact input.1
  · intro name member
    simpa only [rule, node_freeNames, code_freeNames, hole_freeNames, List.flatMap_cons,
      List.flatMap_nil, List.nil_append, List.append_nil, List.mem_append, recursiveEnvironment_freeNames] using member

theorem variable_dispatch_admitted (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (pool : List OCaml.MatchPattern) (index reference slot : Nat) (row : RewriteRule)
    (formed : compileInstruction? pool reference (.variable slot) = some row) : ruleObligations snapshot index row = [] := by
  have shapes := instruction_shapes pool reference (.variable slot) row formed
  have input := instruction_input_properties pool reference (.variable slot) row formed
  simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
  subst row
  apply generated_typed_row_admitted snapshot terms index _ ⟨shapes.1, shapes.2.1⟩ rfl rfl rfl
  · apply evaluate_schema_typed snapshot.language terms captureContext []
    · exact code_typed snapshot.language terms captureContext [] reference
    · apply extend_schema_typed snapshot.language terms captureContext []
      · intro item member
        obtain ⟨skip, _, same⟩ := List.mem_map.mp (List.mem_reverse.mp member)
        subst item
        exact skip_capture_typed snapshot.language [] skip
      · exact nonbare_constructor_typed terms [("head", .base "MlValue"), ("tail", .base "MlEnvironment")] _
          (by decide +kernel) (.cons (variable_capture_typed snapshot.language []) (.cons (tail_capture_typed snapshot.language []) .nil))
    · exact continuation_capture_typed snapshot.language []
  · exact return_schema_typed snapshot.language terms captureContext [] _ _
      (variable_capture_typed snapshot.language []) (continuation_capture_typed snapshot.language [])
  · exact input.2
  · exact input.1
  · intro name member
    simp only [rule, node_freeNames, code_freeNames, hole_freeNames, List.flatMap_cons,
      List.flatMap_nil, List.nil_append, List.append_nil, List.mem_append, extend_freeNames,
      List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    tauto

#print axioms recursive_dispatch_admitted
#print axioms variable_dispatch_admitted

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
