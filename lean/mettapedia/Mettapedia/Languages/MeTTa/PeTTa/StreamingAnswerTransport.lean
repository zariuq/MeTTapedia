import Mettapedia.Languages.MeTTa.PeTTa.AnswerReadout
import Mettapedia.Languages.MeTTa.PeTTa.StreamingPrefixes

/-!
# Lossless answer transport into actual streaming callers

The existing branch packet retains each substitution and an inverse display
basis. Re-entry restores executable values before running the caller. Neither
printed labels nor resolved values alone replace the original branch packet.
This is an optional transport interface, not a mandatory evaluator pass.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.StreamingAnswerTransport

def resume (base : Streaming.State) (packet : AnswerReadout.BranchPacket)
    (caller : List Streaming.Frame) (older : List Streaming.Job) : Streaming.State :=
  {base with agenda := .execute ⟨.returned (AnswerReadout.restoreAnswers packet),caller⟩ :: older}

theorem resume_pack (base : Streaming.State) (answers : List Unifying.Answer)
    (caller : List Streaming.Frame) (older : List Streaming.Job) :
    resume base (AnswerReadout.packAnswers answers) caller older =
      {base with agenda := .execute ⟨.returned answers,caller⟩ :: older} := by
  simp only [resume,AnswerReadout.restore_packAnswers]

/-- Every paid prefix retains the exact world, counters, pending alternatives
and scope markers because the entire re-entered state is recovered. -/
theorem every_prefix_after_transport (program : SpaceSemantics.Program) (fuel : Nat)
    (base : Streaming.State) (answers : List Unifying.Answer)
    (caller : List Streaming.Frame) (older : List Streaming.Job) :
    Streaming.advance program fuel (resume base (AnswerReadout.packAnswers answers) caller older) =
      Streaming.advance program fuel {base with agenda := .execute ⟨.returned answers,caller⟩ :: older} := by
  rw [resume_pack]

theorem outcomes_after_transport (program : SpaceSemantics.Program) (fuel : Nat)
    (base : Streaming.State) (answers : List Unifying.Answer)
    (caller : List Streaming.Frame) (older : List Streaming.Job) :
    Streaming.run program fuel (resume base (AnswerReadout.packAnswers answers) caller older) =
      Streaming.run program fuel {base with agenda := .execute ⟨.returned answers,caller⟩ :: older} := by
  rw [resume_pack]

end Mettapedia.Languages.MeTTa.PeTTa.StreamingAnswerTransport
