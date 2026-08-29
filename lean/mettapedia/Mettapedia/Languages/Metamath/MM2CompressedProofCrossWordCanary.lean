import Mettapedia.Languages.Metamath.MM2CompressedProofCrossWordAdvanceCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofCrossWordPrefixProbeCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofCrossWordTerminalCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofCrossWordResultCanary

/-!
# Cross-word compressed proof control
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofCrossWordCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofExecutionCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofCrossWordAdvanceCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofCrossWordPrefixProbeCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofCrossWordTerminalCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofCrossWordResultCanary
open Mettapedia.Languages.ProcessCalculi.MORK

/-- Prefix state survives the lexical word boundary.  The target emits one
compact pending index-20 action rather than a twenty-element expansion. -/
theorem compressedUA_cross_word_run_emits_compact_twenty :
    CReflectiveReachable .leaveInert 3 compressedCrossWordTwentyProgram
        compressedCrossWordAfterTerminal ∧
      canaryCodeTwentyPending ∈ compressedCrossWordAfterTerminal :=
  ⟨.step cross_word_advance_selected
      (.step cross_word_prefix_probe_selected
        (.step cross_word_terminal_selected .refl)),
    cross_word_result_is_compact_twenty⟩

#print axioms compressedUA_cross_word_run_emits_compact_twenty

end Mettapedia.Languages.Metamath.MM2CompressedProofCrossWordCanary
