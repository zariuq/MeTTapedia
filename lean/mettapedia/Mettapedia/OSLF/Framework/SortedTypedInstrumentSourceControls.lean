import Mettapedia.OSLF.Framework.SortedTypedInstrumentSourceCategory
import Mettapedia.OSLF.Framework.SortedTypedInstrumentControls
import Mathlib.Algebra.BigOperators.Fin

/-!+# Complete mixed-coordinate source contexts and partial-reading boundaries

A channel-to-process context retains its full process sibling, including
the different channel nested inside that sibling. The independently formed
source and native filling squares agree. Partial source readings reject a
genuine observer-bearing native value at an empty original source sort;
its hereditary count is positive, while every embedded source has zero
support. No global erasure or source-sort inhabitation is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstrumentSourceControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open SortedTypedInstruments SortedTypedInstrumentControls
open scoped BigOperators

def sendContext (payload : SourceValue .process) :
    RawContext sourceSignature sourceParallel .channel .process :=
  RawContext.frame (signature := sourceSignature) (Parallel := sourceParallel) Symbol.send 0
    (Fin.cases (motive := fun other => other ≠ 0 → SourceValue (sourceSignature.input Symbol.send other))
      (fun absent => (absent rfl).elim) (fun _ _ => payload)) .hole

theorem complete_source_filling (index : Nat) (payload : SourceValue .process) :
    (sendContext payload).fill (sourceName index) =
      Term.node (signature := sourceSignature) (Parallel := sourceParallel) Symbol.send
        (Fin.cases (motive := fun position => SourceValue (sourceSignature.input Symbol.send position))
          (sourceName index) (fun _ => payload)) := by
  apply congrArg (Term.node (signature := sourceSignature) (Parallel := sourceParallel) Symbol.send)
  funext position
  fin_cases position <;> rfl

theorem complete_native_filling (index : Nat) (payload : SourceValue .process) :
    (embedContext (sendContext payload)).fill (embed (sourceName index)) =
      embed (Term.node (signature := sourceSignature) (Parallel := sourceParallel) Symbol.send
        (Fin.cases (motive := fun position => SourceValue (sourceSignature.input Symbol.send position))
          (sourceName index) (fun _ => payload))) := by
  rw [embedContext_fill, complete_source_filling]

theorem original_and_nested_coordinates_survive :
    (embedContext (sendContext (sourcePayload 9))).fill (embed (sourceName 7)) =
      embed (Term.node (signature := sourceSignature) (Parallel := sourceParallel) Symbol.send
        (Fin.cases (motive := fun position => SourceValue (sourceSignature.input Symbol.send position))
          (sourceName 7) (fun _ => sourcePayload 9))) :=
  complete_native_filling 7 (sourcePayload 9)

theorem heterogeneous_context_class_is_read_back (payload : SourceValue .process) :
    classContextReading (contextEmbedding (contextClassOf (sendContext payload))) =
      some ((sendContext payload).normalize) :=
  classContextReading_embedding (contextClassOf (sendContext payload))

theorem complete_categorical_action_is_retained (index : Nat) (payload : SourceValue .process) :
    (inclusion sourceSignature sourceParallel).map
        ((RawArrow.value (classOf (sourceName index)) :
          (.origin : SourceCategory sourceSignature sourceParallel) ⟶ .interface .channel) ≫
          (RawArrow.context (contextClassOf (sendContext payload)) :
            (.interface .channel : SourceCategory sourceSignature sourceParallel) ⟶ .interface .process)) =
      (RawArrow.value (classOf ((embedContext (sendContext payload)).fill (embed (sourceName index)))) :
        (.origin : ContextCategory sourceSignature sourceParallel) ⟶ .interface (.original .process)) := by
  rw [Functor.map_comp]
  rfl

theorem partial_reading_rejects_the_observer_bearing_empty_sort :
    readSource observerBearingAbsent =
      (none : Option (Class sourceSignature sourceParallel .absent)) := rfl

theorem no_original_equation_class_at_absent_sort :
    ¬Nonempty (Class sourceSignature sourceParallel .absent) := by
  rintro ⟨supplied⟩
  exact no_source_value_at_absent_sort supplied.out

private theorem probe_count (instrument : Probe sourceSignature sourceParallel) :
    observerCount (probe instrument) = 1 := by
  change 1 + (∑ position : Fin 0, observerCount (Fin.elim0 position)) = 1
  simp only [Fin.sum_univ_zero, Nat.add_zero]

private theorem cut_count (instrument : Probe sourceSignature sourceParallel)
    (suppliedProbe : NativeValue (.probe instrument)) (body : NativeValue (receiver instrument)) :
    observerCount (cut instrument suppliedProbe body) =
      1 + (observerCount suppliedProbe + observerCount body) := by
  change 1 + (∑ position : Fin 2, _) = _
  rw [Fin.sum_univ_two]
  rfl

theorem empty_sort_counterexample_has_actual_positive_support : observerCount observerBearingAbsent = 4 := by
  rw [observerBearingAbsent, cut_count, probe_count, blockedArguments, cut_count, probe_count, observerCount_embed]

theorem all_heterogeneous_source_values_have_zero_support (index : Nat) (payload : SourceValue .process) :
    observerCount (embed (sourceName index)) = 0 ∧ observerCount (embed payload) = 0 :=
  ⟨observerCount_embed _, observerCount_embed _⟩

theorem complete_source_context_has_zero_support (payload : SourceValue .process) :
    contextObserverCount (embedContext (sendContext payload)) = 0 :=
  contextObserverCount_embed _

end Mettapedia.OSLF.Framework.SortedTypedInstrumentSourceControls
