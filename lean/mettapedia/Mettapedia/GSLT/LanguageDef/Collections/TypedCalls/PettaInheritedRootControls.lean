import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedFixtures
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeEquationScalarReduction

/-! # Root-frontier controls retaining complete source answer records -/

set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 16000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedControls

open PettaInheritedFixtures
open PettaCheckpointFixtures (num text)

theorem body_commit_keeps_the_older_typed_call :
    observed false false = some ([num 4, text "outside"], [text "before", text "body"]) := by
  unfold observed
  simp only [PettaInheritedContext.execute_in_host]
  cbv

theorem omitting_handoff_publishes_the_unguarded_wrong_type :
    withoutHandoff false true = some ([text "wrong", text "outside"], [text "before", text "body"]) := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaInheritedControls
