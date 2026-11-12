import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.InterchangeTrace
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventTraceControls

/-! # Actual interchanges and an extra identification in the existing trace quotient -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.InterchangeTraceControls

open Presentation.Controls (Store)
open PublicationTransportControls

abbrev P := program permissive
abbrev T := transport permissive

theorem admitted (state : Store) (label : Bool) : P.Admits (s := state) label :=
  ⟨Presentation.Controls.prepares state (), trivial⟩

def pairRun (first second : Bool) : P.Run ([] : Store) :=
  .cons first (admitted [] first) (.cons second (admitted _ second) (.nil _))

theorem pair_interchange : T.Interchange (pairRun false true) (pairRun true false) :=
  Transport.Interchange.here (T := T) (admitted [] false) (admitted [] true)
    (admitted _ true) (admitted _ false) ⟨rfl⟩ (.nil _)

theorem pair_endpoints_equal : (pairRun false true).last = (pairRun true false).last := rfl

theorem pair_free_paths_different : (pairRun false true).eventPath P ≠ (pairRun true false).eventPath P := by
  intro same
  have words := congrArg P.eventWord same
  rw [Step.Run.eventPath_word, Step.Run.eventPath_word] at words
  have labels := congrArg (List.map (fun entry : (_ : Store) × Bool => entry.2)) words
  simp [pairRun, Step.Run.word] at labels

theorem pair_quotient_related : T.TraceEquiv [] (pairRun false true) (pairRun true false) :=
  .rel _ _ (.inl pair_interchange.toSwap)

theorem old_trace_has_extra_identifications :
    T.TraceEquiv EventTraceControls.start (EventTraceControls.run true) (EventTraceControls.run false) ∧
      ¬ T.InterchangeClosure EventTraceControls.start
        (EventTraceControls.run true) (EventTraceControls.run false) := by
  constructor
  · exact .rel _ _ (.inr (Transport.Similar.cons_alike True.intro
      (permissive_admits true) (permissive_admits false)
        (Transport.Similar.refl (Step.Run.nil _))))
  · intro related
    have same := related.rigid_of_length_le_one (by simp [EventTraceControls.run, Step.Run.word])
    have words := congrArg (fun run : P.Run EventTraceControls.start =>
      run.word.map (fun entry : (_ : Store) × Bool => entry.2)) same
    simp [EventTraceControls.run, Step.Run.word] at words

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.InterchangeTraceControls
