import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlLambdaInference
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlInferredRuleAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFunctionBindingProperties

/-! Every generated nonrecursive function row passes existing selected-rule
admission. No source-program size, code reference or pattern index is fixed.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission

theorem lambda_function_admitted (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) (program : OCaml.Program)
    (pool : List OCaml.MatchPattern) (index reference : Nat) (parameter : OCaml.MatchPattern)
    (body : OCaml.Code) (rows : List RewriteRule) (row : RewriteRule)
    (formed : functionRules? program pool reference (.lambda parameter body) = some rows) (member : row ∈ rows) :
    ruleObligations snapshot index row = [] := by
  have fields := function_binding_fields program pool reference (.lambda parameter body) rows row formed member
  have shapes := function_row_shapes program pool reference (.lambda parameter body) rows row formed member
  have inferred : GeneralRuleBindingGrammar.infer? baseLanguage row = some lambdaInference := by
    cases resolved : patternReference? pool parameter with
    | none => simp [functionRules?, resolved] at formed
    | some patternCode =>
        rw [function_lambda_rows program reference body resolved] at formed
        cases Option.some.inj formed
        have same := List.mem_singleton.mp member
        subst row
        unfold patternReference? at resolved
        obtain ⟨patternIndex, _, encoded⟩ := Option.map_eq_some_iff.mp resolved
        cases encoded
        exact lambda_infer _ reference patternIndex body
  exact (inferred_rule_ready snapshot terms types index row lambdaInference fields.1 fields.2.1
    (by rw [fields.2.2.1]; simp) shapes.1 shapes.2.1 shapes.2.2 fields.2.2.2.1 inferred).2

#print axioms lambda_function_admitted

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
