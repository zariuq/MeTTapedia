import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderRoundTrace

/-!
# Count-preserving replacement separates native swaps from rounds

A writer replaces occurrence zero by occurrence one with the same label.
A count-only guard sees one match before and after. Both orders are admitted
and their native square closes, while the round's write-ignorance condition
fails. Thus the legacy round quotient is strictly finer on this example.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.FirstOrderNativeRuns.TraceBoundaryControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns (Firing firstOrder firstOrderTransport)

def label (_ : Nat) : Term signature := .const 7
def source : Configuration (Term signature) Nat := ⟨[], {0}⟩
def writer : Firing (Term signature) (Subst signature) Nat :=
  ⟨⟨[.const 7], [], [], [], [.const 7]⟩, [], ⟨[0], [], [1]⟩⟩
def counter : Firing (Term signature) (Subst signature) Nat :=
  ⟨⟨[], [], [], [.count (.const 7) 1], []⟩, [], ⟨[], [], []⟩⟩

theorem writer_models {state : Configuration (Term signature) Nat} {σ : Subst signature}
    (base : A.Models σ state.equations) : A.Models σ (writer.result label state).equations := by
  intro equation member
  have origin : equation ∈ state.equations ∨ equation = (.const 7, .const 7) := by
    simpa [Firing.result, Selection.result, Selection.problem, Selection.equations, writer, label] using member
  rcases origin with original | rfl
  · exact base equation original
  · rfl

theorem writer_allowed : writer.Valid A label source :=
  ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
    ⟨Subst.id signature, writer_models (by simp [source])⟩,
    by simp [writer]⟩, by simp [writer]⟩

theorem counter_result (state : Configuration (Term signature) Nat) : counter.result label state = state := by
  cases state
  simp [Firing.result, Selection.result, Selection.problem, Selection.equations, counter,
    MeTTaCalculus.OccurrenceCommits.fire, Selection.commit]

theorem counter_allowed {state : Configuration (Term signature) Nat}
    (consistent : A.Consistent state.equations) (size : state.present.card = 1) : counter.Valid A label state := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, ?_, ?_, ?_⟩, by simp [counter]⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Selection.commit, counter]
  · simpa [Selection.problem, Selection.equations, counter] using consistent
  · intro check member σ _
    have only : check = .count (.const 7) 1 := List.mem_singleton.mp member
    subst check
    have all : Check.matches A σ label state.present (.const 7) = state.present := by
      ext occurrence
      simp only [Check.matches, Finset.mem_filter]
      change (occurrence ∈ state.present ∧ (.const 7 : Term signature) = .const 7) ↔ occurrence ∈ state.present
      exact ⟨And.left, fun inside => ⟨inside, rfl⟩⟩
    change (Check.matches A σ label state.present (.const 7)).card = 1
    rw [all]
    exact size

theorem counter_at_source : counter.Valid A label source :=
  counter_allowed ⟨Subst.id signature, by simp [source]⟩ (by decide)

theorem counter_after_writer : counter.Valid A label (writer.result label source) :=
  counter_allowed ⟨Subst.id signature, writer_models (by simp [source])⟩ (by decide)

theorem writer_after_counter : writer.Valid A label (counter.result label source) := by
  rw [counter_result]
  exact writer_allowed

theorem independent : (firstOrderTransport A label).Independent source writer counter :=
  (AnnotatedRuns.firstOrder_independent_iff A label).mpr
    ⟨writer_allowed, counter_at_source, counter_after_writer, writer_after_counter⟩

def forward : (firstOrder A label).toStep.Run source :=
  .cons writer writer_allowed (.cons counter counter_after_writer (.nil _))
def backward : (firstOrder A label).toStep.Run source :=
  .cons counter counter_at_source (.cons writer writer_after_counter (.nil _))

theorem native_orders_agree : (firstOrderTransport A label).TraceEquiv source forward backward := by
  apply (native_trace_iff_word_trace A label forward backward).mpr
  exact .rel _ _ (.swap [] [] writer counter independent)

theorem not_a_round : ¬AnnotatedRuns.Round A label source [writer, counter] := by
  intro round
  have compatible := List.pairwise_pair.mp round.compatible
  have ignored := compatible.2.2.1 (.count (.const 7) 1) (by simp [counter])
  have apart := ignored 0 (by simp [writer])
  apply apart
  refine ⟨Subst.id signature, ?_⟩
  intro equation member
  have same : equation = (.const 7, .const 7) := by
    simpa [AnnotatedRuns.pairCut, Firing.added, GuardFreeProcessOrders.added,
      Selection.equations, source, writer, counter, label] using member
  subst equation
  rfl

theorem roundSwap_symm {first second : List (Firing (Term signature) (Subst signature) Nat)}
    (swapped : AnnotatedRuns.RoundSwap A label source first second) :
    AnnotatedRuns.RoundSwap A label source second first := by
  cases swapped with
  | swap before after f g round => exact .swap before after g f (round.perm A label (List.Perm.swap g f []))

theorem no_round_swap {first second : List (Firing (Term signature) (Subst signature) Nat)}
    (swapped : AnnotatedRuns.RoundSwap A label source first second) (same : first = [writer, counter]) : False := by
  cases swapped with
  | swap before after f g round =>
      have lengths := congrArg List.length same
      simp only [List.length_append, List.length_cons, List.length_nil] at lengths
      have beforeEmpty : before = [] := List.length_eq_zero_iff.mp (by omega)
      have afterEmpty : after = [] := List.length_eq_zero_iff.mp (by omega)
      subst before
      subst after
      obtain ⟨head, tail⟩ := List.cons.inj same
      have next := (List.cons.inj tail).1
      subst f
      subst g
      exact not_a_round round

theorem legacy_orders_distinguished : ¬AnnotatedRuns.RoundEquiv A label source [writer, counter] [counter, writer] := by
  have invariant : ∀ {first second : List (Firing (Term signature) (Subst signature) Nat)},
      AnnotatedRuns.RoundEquiv A label source first second →
        (first = [writer, counter] ↔ second = [writer, counter]) := by
    intro first second related
    induction related with
    | rel _ _ swapped =>
        exact ⟨fun same => False.elim (no_round_swap swapped same),
          fun same => False.elim (no_round_swap (roundSwap_symm swapped) same)⟩
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ first second => exact first.trans second
  intro related
  have same := (invariant related).mp rfl
  have head := congrArg (fun firing => firing.selection.taken) (List.cons.inj same).1
  simp [counter, writer] at head

theorem strict_trace_boundary :
    (firstOrderTransport A label).TraceEquiv source forward backward ∧
      ¬AnnotatedRuns.RoundEquiv A label source (sites A label forward) (sites A label backward) :=
  ⟨native_orders_agree, legacy_orders_distinguished⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.FirstOrderNativeRuns.TraceBoundaryControls
