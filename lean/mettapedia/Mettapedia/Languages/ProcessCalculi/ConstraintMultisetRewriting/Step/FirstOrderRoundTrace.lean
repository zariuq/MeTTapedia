import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderWordTrace

/-! # The established round equations map into native trace equations -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.FirstOrderNativeRuns

open AnnotatedRuns (Firing firstOrder firstOrderTransport)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

theorem round_swap_word {state : Configuration T O} {first second : List (Firing T S O)}
    (swapped : AnnotatedRuns.RoundSwap A label state first second) : WordSwap A label state first second := by
  cases swapped with
  | swap before after f g round => exact .swap before after f g (AnnotatedRuns.round_independent A label round)

theorem round_trace_word {state : Configuration T O} {first second : List (Firing T S O)}
    (related : AnnotatedRuns.RoundEquiv A label state first second) : WordTrace A label state first second :=
  Relation.EqvGen.mono (fun _ _ swapped => round_swap_word A label swapped) first second related

theorem native_trace_of_rounds {state : Configuration T O}
    (first second : (firstOrder A label).toStep.Run state)
    (related : AnnotatedRuns.RoundEquiv A label state (sites A label first) (sites A label second)) :
    (firstOrderTransport A label).TraceEquiv state first second :=
  (native_trace_iff_word_trace A label first second).mpr (round_trace_word A label related)

theorem WordTrace.perm {state : Configuration T O} {first second : List (Firing T S O)}
    (related : WordTrace A label state first second) : first.Perm second := by
  induction related with
  | rel _ _ swapped =>
      cases swapped with
      | swap before after f g _ => exact List.Perm.append_left before (List.Perm.swap g f after)
  | refl => exact List.Perm.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ left right => exact left.trans right

theorem native_trace_preserves_firing_bag {state : Configuration T O}
    {first second : (firstOrder A label).toStep.Run state}
    (related : (firstOrderTransport A label).TraceEquiv state first second) :
    (sites A label first).Perm (sites A label second) :=
  ((native_trace_iff_word_trace A label first second).mp related).perm A label

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.FirstOrderNativeRuns
