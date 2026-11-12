import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedFixtures
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeEquationScalarReduction

/-! # Kernel controls for nested handoff, refusal and delimiter preservation -/

set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 16000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedControls

open PettaInheritedFixtures
open PettaCheckpointFixtures (num text)

theorem source_entry_reaches_a_root_body :
    readyView false false = some (1, 1, true, true) := by cbv

theorem source_collapse_reaches_its_own_body_depth :
    readyView true false = some (2, 2, true, true) := by cbv

theorem refused_result_keeps_the_older_typed_call :
    observed false true = some ([text "outside"], [text "before", text "body"]) := by
  unfold observed
  simp only [PettaInheritedContext.execute_in_host]
  cbv

theorem collection_parent_and_older_typed_call_both_resume :
    observed true false = some ([.expression [num 4], text "outside"], [text "before", text "body"]) := by
  unfold observed
  simp only [PettaInheritedContext.execute_in_host]
  cbv

theorem refused_nested_result_collects_an_empty_answer_list :
    observed true true = some ([.expression [], text "outside"], [text "before", text "body"]) := by
  unfold observed
  simp only [PettaInheritedContext.execute_in_host]
  cbv

theorem omitting_nested_handoff_collects_the_wrong_type :
    withoutHandoff true true = some ([.expression [text "wrong"], text "outside"], [text "before", text "body"]) := by cbv

theorem corrupting_the_cut_delimiter_deletes_the_older_call :
    wrongDelimiter = some ([num 4], [text "before", text "body"]) := by
  unfold wrongDelimiter
  simp only [PettaInheritedContext.execute_in_host]
  cbv

theorem resetting_the_inherited_depth_loses_the_nested_guard :
    unrebasedNested = some ([.expression [text "wrong"], text "outside"], [text "before", text "body"]) := by
  unfold unrebasedNested
  simp only [PettaInheritedContext.execute_in_host]
  cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedControls
