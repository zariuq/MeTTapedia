import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlGeneratedAdmission

/-! Actual admission controls distinguish generated captures from invented
results, inconsistent sorts and undeclared grammar constructors. Kernel
checks supplement the parametric source-family proofs.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.AdmissionControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission

private def input : Pattern := node "MlEvaluate" [code 0, hole "environment", hole "continuation"]
private def checkedSnapshot : Snapshot := ⟨baseLanguage, [], provider⟩

set_option cbv.maxSteps 2000000 in
theorem kernel_admitted : baseLanguage.rewrites.all
    (fun row => (ruleObligations checkedSnapshot 27 row).isEmpty) = true := by cbv

theorem large_code_and_signed_literal : ∃ row,
    compileInstruction? [] 1048577 (.literal (.integer (-9007199254740991))) = some row ∧
      ruleObligations checkedSnapshot 28 row = [] := by
  refine ⟨_, rfl, ?_⟩
  exact literal_dispatch_admitted checkedSnapshot rfl rfl [] 28 1048577 _ _ rfl

theorem empty_tuple_admitted : ∃ row, compileInstruction? [] 4 (.tuple []) = some row ∧
    ruleObligations checkedSnapshot 29 row = [] := by
  refine ⟨_, rfl, ?_⟩
  exact tuple_dispatch_admitted checkedSnapshot rfl rfl [] 29 4 [] _ rfl

theorem nonempty_primitive_request_admitted : ∃ row,
    compileInstruction? [] 7 (.primitive .subtract [19, 2]) = some row ∧
      ruleObligations checkedSnapshot 30 row = [] := by
  refine ⟨_, rfl, ?_⟩
  exact primitive_dispatch_admitted checkedSnapshot rfl rfl [] 30 7 _ _ _ rfl

private def invented : RewriteRule := rule "invented" input
  (node "MlReturn" [hole "unbound", hole "continuation"])

set_option cbv.maxSteps 2000000 in
theorem invented_output_refused : ruleObligations checkedSnapshot 31 invented = [.rulePremises 31] := by cbv

private def wrongSort : RewriteRule := rule "wrong-sort" input
  (node "MlReturn" [hole "environment", hole "continuation"])

set_option cbv.maxSteps 2000000 in
theorem inconsistent_capture_sort_refused : ruleObligations checkedSnapshot 32 wrongSort = [.ruleBinding 32] := by cbv

private def undeclared : RewriteRule := rule "undeclared" input
  (node "UnknownRuntimeFrame" [hole "environment", hole "continuation"])

set_option cbv.maxSteps 2000000 in
theorem undeclared_capture_position_refused : ruleObligations checkedSnapshot 33 undeclared = [.ruleBinding 33] := by cbv

#print axioms kernel_admitted
#print axioms large_code_and_signed_literal
#print axioms empty_tuple_admitted
#print axioms nonempty_primitive_request_admitted
#print axioms invented_output_refused
#print axioms inconsistent_capture_sort_refused
#print axioms undeclared_capture_position_refused

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.AdmissionControls
