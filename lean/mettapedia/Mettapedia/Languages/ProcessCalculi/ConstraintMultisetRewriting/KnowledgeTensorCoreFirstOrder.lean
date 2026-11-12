import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCore
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorFirstOrderZoned
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderFourBlock

/-!
# The first-order step: native runs are zoned proofs

The first-order step is the one-frame instance of the step's interface. Its native runs, the
dependent words of admitted firings of `Step.Run`, are here the objects of the logical reading.

* `native_run_iff_zoned_proof`: native runs of firings without predicate queries, with every kind
  of check, are exactly the graded proofs of the zoned calculus whose grade admits the empty
  extra context and whose final knowledge is consistent, with the same uses in the same order.
* `stableAt_of_guardsOnly`: a firing whose checks are equality checks is stable under every
  placement, so its grade is structural: fresh outputs and a consistent joint problem.
  `guardTransportAt_of_guardsOnly` reads its guard along the identity of the one frame.
* `contextChecks_iff_holdsOn`: beside a context, the permission part of the grade is the check
  on the labels of the joint store at the solutions of the joint problem.
* `native_tensor_is_zoned_proof`: the native parallel composition of two runs is a zoned proof
  from the tensor of the two configurations whose uses are those of the first run, then those of
  the second.
* `tensor_readouts_one_trace`, `native_tensor_readouts`: the two readouts of a tensor of
  separated runs are one native trace.
* `native_transposition`: two native runs whose words differ by one adjacent transposition are
  one native trace. `framed_swap_one_trace`: so the frame rule respects a swap wherever both
  orders are in the grade.
* `knowledge_tensor`: the knowledge of a tensor of configurations is the meet of the knowledges.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.FirstOrder

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Logic.LinearLogic
open _root_.CategoryTheory
open AnnotatedRuns (Firing firstOrder firstOrderTransport)
open FirstOrderNativeRuns
open KnowledgeTensorFirstOrder

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

omit [DecidableEq O] in
/-- A firing without predicate queries is the schedule entry it was made from. -/
theorem plain_ofPlain (schedule : List (ConditionalSchedule.Firing T O)) :
    (schedule.map (Firing.ofPlain (S := S))).map Firing.plain = schedule := by
  induction schedule with
  | nil => rfl
  | cons head rest ih => exact congrArg (List.cons head) ih

/-- A native run of firings without predicate queries ends where its schedule leaves the
configuration. -/
theorem last_eq_follow_plain (A : SubstitutionAction T S) (label : O → T) {C : Configuration T O}
    (run : (firstOrder A label).toStep.Run C) (schedule : List (ConditionalSchedule.Firing T O))
    (word : sites A label run = schedule.map (Firing.ofPlain (S := S))) :
    run.last = ConditionalSchedule.follow label C schedule := by
  rw [← AnnotatedRuns.follow_eq_last A label run]
  show AnnotatedRuns.follow label C (sites A label run) = _
  rw [word, AnnotatedRuns.follow_eq_plain, plain_ofPlain]

/-- **Native runs of the first-order step are zoned proofs.** A native run of declared firings
without predicate queries that ends in consistent knowledge exists exactly when a graded proof of
the zoned calculus exists whose grade admits the empty extra context and whose final knowledge is
consistent, with the same uses in the same order. -/
theorem native_run_iff_zoned_proof [DecidableEq T] (A : SubstitutionAction T S)
    (program : Set (RuleInstance T)) (label : O → T)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value)
    (C : Configuration T O) (uses : List (Use T)) (finalKnown : Set S) (Γ' : Multiset T) :
    (∃ (schedule : List (ConditionalSchedule.Firing T O)) (run : (firstOrder A label).toStep.Run C),
      sites A label run = schedule.map (Firing.ofPlain (S := S)) ∧
      A.Consistent run.last.equations ∧
      (∀ firing ∈ schedule, firing.1 ∈ program) ∧
      schedule.map (useOf label) = uses ∧
      knowledge A run.last = finalKnown ∧ resources label run.last = Γ') ↔
      (∃ (along : (() : Unit) ⟶ ()) (grade : Multiset T → Prop), grade 0 ∧
        (checkedSystem A program).zoned.Proves () 0 (knowledge A C) (resources label C) grade
          (uses.map (Sigma.mk ())) () along finalKnown Γ') ∧ finalKnown.Nonempty := by
  refine Iff.trans ?_ (schedule_iff_zoned_proof A program label supply C uses finalKnown Γ')
  constructor
  · rintro ⟨schedule, run, word, consistent, declared, used, known, left⟩
    have executable : ConditionalSchedule.Executable A label C schedule :=
      (AnnotatedRuns.executable_ofPlain_iff A label C schedule).mp
        ((AnnotatedRuns.executable_iff_run A label C _).mpr ⟨run, word, consistent⟩)
    have ends := last_eq_follow_plain A label run schedule word
    rw [ends] at known left
    exact ⟨schedule, executable, declared, used, known, left⟩
  · rintro ⟨schedule, executable, declared, used, known, left⟩
    obtain ⟨run, word, consistent⟩ := (AnnotatedRuns.executable_iff_run A label C _).mp
      ((AnnotatedRuns.executable_ofPlain_iff A label C schedule).mpr executable)
    have ends := last_eq_follow_plain A label run schedule word
    rw [← ends] at known left
    exact ⟨schedule, run, word, consistent, declared, used, known, left⟩

/-- **Equality checks are stable under placement.** A firing without predicate queries whose
checks are equality checks is admitted beside every context that leaves its placed candidate
prepared. -/
theorem stableAt_of_guardsOnly (A : SubstitutionAction T S) (label : O → T)
    {left right : Configuration T O} (f : Firing T S O) (guards : GuardsOnly f.rule)
    (plain : f.queries = []) :
    StableAt (contextualRunInterpretation A label) (left := left) (right := right) PUnit.unit f := by
  intro allowed _ prepared
  refine (valid_tensor_iff A label f allowed).mpr ⟨?_, ?_, ?_, ?_⟩
  · exact Finset.disjoint_of_subset_right Finset.subset_union_right prepared.2.1.fresh
  · exact (Frames.ofSubstitution_solvable_iff A _).mp prepared.2.2
  · intro check member σ solved
    obtain ⟨one, two, rfl⟩ := guards check member
    have localSolved : A.Models σ (f.selection.problem label f.rule left) := by
      simp only [Selection.problem, AnnotatedRuns.tensor, A.models_append] at solved ⊢
      exact ⟨⟨⟨solved.1.1.1.1, solved.1.1.2⟩, solved.1.2⟩, solved.2⟩
    exact allowed.firing.checks _ member σ localSolved
  · intro query member
    rw [plain] at member
    cases member

/-- **Equality checks are read along the identity of the one frame**: the information of the
placed candidate contains the information of the local firing, and an equality check does not
read the store. -/
def guardTransportAt_of_guardsOnly (A : SubstitutionAction T S) (label : O → T)
    {left right : Configuration T O} (f : Firing T S O) (guards : GuardsOnly f.rule)
    (plain : f.queries = []) :
    GuardTransportAt (contextualRunInterpretation A label) (left := left) (right := right)
      PUnit.unit f where
  through := A.identity
  refines := by
    intro _ σ solved
    have joint : A.Models σ (f.selection.problem label f.rule (AnnotatedRuns.tensor left right)) :=
      solved
    have localSolved : A.Models σ (f.selection.problem label f.rule left) := by
      simp only [Selection.problem, AnnotatedRuns.tensor, A.models_append] at joint ⊢
      exact ⟨⟨⟨joint.1.1.1.1, joint.1.1.2⟩, joint.1.2⟩, joint.2⟩
    intro equation member
    have here := localSolved equation member
    show A.E (A.apply (A.compose σ A.identity) equation.1)
      (A.apply (A.compose σ A.identity) equation.2)
    rw [A.apply_compose, A.apply_compose, A.apply_identity, A.apply_identity]
    exact here
  holds := by
    intro _ σ _ asked
    have asked' : (∀ check ∈ f.rule.checks,
          check.Holds A (A.compose σ A.identity) label left.present) ∧
        ∀ query ∈ f.queries,
          (query.atSolution (A.compose σ A.identity)).Holds label left.present := asked
    show (∀ check ∈ f.rule.checks,
        check.Holds A σ label (AnnotatedRuns.tensor left right).present) ∧
      ∀ query ∈ f.queries, (query.atSolution σ).Holds label (AnnotatedRuns.tensor left right).present
    refine ⟨fun check member => ?_, fun query member => ?_⟩
    · obtain ⟨one, two, rfl⟩ := guards check member
      have here : A.E (A.apply (A.compose σ A.identity) one) (A.apply (A.compose σ A.identity) two) :=
        asked'.1 _ member
      rw [A.apply_compose, A.apply_compose, A.apply_identity, A.apply_identity] at here
      exact here
    · rw [plain] at member
      cases member

/-- **The permission part of the grade is the check on labels.** Beside a context, a firing
without predicate queries is checked on the labels of the joint store, at every solution of the
joint problem; the rest of its grade is structural. -/
theorem contextChecks_iff_holdsOn (A : SubstitutionAction T S) (label : O → T)
    (left right : Configuration T O) (f : Firing T S O) (plain : f.queries = []) :
    ContextChecks A label left right f ↔
      Disjoint f.selection.made.toFinset right.present ∧
        A.Consistent (f.selection.problem label f.rule (AnnotatedRuns.tensor left right)) ∧
        ∀ check ∈ f.rule.checks, ∀ σ : S,
          A.Models σ (f.selection.problem label f.rule (AnnotatedRuns.tensor left right)) →
            HoldsOn A σ check (labels label (left.present ∪ right.present)) := by
  constructor
  · rintro ⟨fresh, consistent, guards, _⟩
    exact ⟨fresh, consistent, fun check member σ solved =>
      (holds_iff_holdsOn A σ label _ check).mp (guards check member σ solved)⟩
  · rintro ⟨fresh, consistent, guards⟩
    refine ⟨fresh, consistent, fun check member σ solved =>
      (holds_iff_holdsOn A σ label _ check).mpr (guards check member σ solved), ?_⟩
    intro query member
    rw [plain] at member
    cases member

/-- The knowledge of a tensor of configurations is the meet of their knowledges. -/
theorem knowledge_tensor (A : SubstitutionAction T S) (left right : Configuration T O) :
    knowledge A (AnnotatedRuns.tensor left right) = knowledge A left ⊓ knowledge A right := by
  ext σ
  show A.Models σ (left.equations ++ right.equations) ↔
    A.Models σ left.equations ∧ A.Models σ right.equations
  exact A.models_append σ _ _

/-- **The native tensor of two runs is a zoned proof of the tensor sequent.** Its uses are the
uses of the first run, then those of the second. -/
theorem native_tensor_is_zoned_proof [DecidableEq T] (A : SubstitutionAction T S)
    (program : Set (RuleInstance T)) (label : O → T)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value)
    {left right : Configuration T O} {first : (firstOrder A label).toStep.Run left}
    {second : (firstOrder A label).toStep.Run right}
    (plan : (contextualRunInterpretation A label).TensorPlan (contextualFlip A label) PUnit.unit
      first second)
    (one two : List (ConditionalSchedule.Firing T O))
    (firstWord : sites A label first = one.map (Firing.ofPlain (S := S)))
    (secondWord : sites A label second = two.map (Firing.ofPlain (S := S)))
    (declared : ∀ firing ∈ one ++ two, firing.1 ∈ program)
    (consistent : A.Consistent
      (plan.realize (contextualRunInterpretation A label) (contextualFlip A label)).execution.last.equations) :
    ∃ (along : (() : Unit) ⟶ ()) (grade : Multiset T → Prop), grade 0 ∧
      (checkedSystem A program).zoned.Proves () 0
        (knowledge A left ⊓ knowledge A right) (resources label (AnnotatedRuns.tensor left right)) grade
        ((one.map (useOf label) ++ two.map (useOf label)).map (Sigma.mk ())) () along
        (knowledge A
          (plan.realize (contextualRunInterpretation A label) (contextualFlip A label)).execution.last)
        (resources label
          (plan.realize (contextualRunInterpretation A label) (contextualFlip A label)).execution.last) := by
  rw [← knowledge_tensor, ← List.map_append]
  refine ((native_run_iff_zoned_proof A program label supply (AnnotatedRuns.tensor left right) _ _ _).mp
    ⟨one ++ two, (plan.realize (contextualRunInterpretation A label) (contextualFlip A label)).execution,
      ?_, consistent, declared, rfl, rfl, rfl⟩).1
  rw [tensor_sites, firstWord, secondWord, List.map_append]

/-- **The two readouts of a tensor are one native trace**, on complete firing words. -/
theorem tensor_readouts_one_trace (A : SubstitutionAction T S) (label : O → T)
    {left right : Configuration T O} (first second : List (Firing T S O))
    (separated : AnnotatedRuns.Separated A label left first right second) :
    WordTrace A label (AnnotatedRuns.tensor left right) (first ++ second) (second ++ first) :=
  round_trace_word A label (AnnotatedRuns.tensor_interchange A label left first right second separated)

/-- Two native runs from a tensor of configurations whose words are the two readouts of a tensor
of separated runs are trace equivalent. -/
theorem native_tensor_readouts (A : SubstitutionAction T S) (label : O → T)
    {left right : Configuration T O} (first second : List (Firing T S O))
    (separated : AnnotatedRuns.Separated A label left first right second)
    (one two : (firstOrder A label).toStep.Run (AnnotatedRuns.tensor left right))
    (straight : sites A label one = first ++ second) (swapped : sites A label two = second ++ first) :
    (firstOrderTransport A label).TraceEquiv (AnnotatedRuns.tensor left right) one two := by
  apply (native_trace_iff_word_trace A label one two).mpr
  rw [straight, swapped]
  exact tensor_readouts_one_trace A label first second separated

/-- **Two native runs whose words differ by one adjacent transposition are one trace.** The
swap of two uses is an equation of proofs exactly when both orders run. -/
theorem native_transposition (A : SubstitutionAction T S) (label : O → T)
    {state : Configuration T O} (one two : (firstOrder A label).toStep.Run state)
    (before suffix : List (Firing T S O)) (f g : Firing T S O)
    (straight : sites A label one = before ++ f :: g :: suffix)
    (swapped : sites A label two = before ++ g :: f :: suffix) :
    (firstOrderTransport A label).TraceEquiv state one two := by
  have first : AnnotatedRuns.Executable A label state (before ++ f :: g :: suffix) := by
    rw [← straight]
    refine executable_of_nonempty A label one ?_
    rw [straight]
    exact List.append_ne_nil_of_right_ne_nil before (List.cons_ne_nil f _)
  have second : AnnotatedRuns.Executable A label state (before ++ g :: f :: suffix) := by
    rw [← swapped]
    refine executable_of_nonempty A label two ?_
    rw [swapped]
    exact List.append_ne_nil_of_right_ne_nil before (List.cons_ne_nil g _)
  have here := AnnotatedRuns.executable_append_right A label state before _ first
  have there := AnnotatedRuns.executable_append_right A label state before _ second
  apply (native_trace_iff_word_trace A label one two).mpr
  rw [straight, swapped]
  exact .rel _ _ (.swap before suffix f g
    ((AnnotatedRuns.firstOrder_independent_iff A label).mpr ⟨here.1, there.1, here.2.1, there.2.1⟩))

/-- **The frame rule respects a swap on the common grade.** Two local runs whose words differ by
one adjacent transposition, both with a plan at one placement, have trace-equivalent placed
runs. -/
theorem framed_swap_one_trace (A : SubstitutionAction T S) (label : O → T)
    {left right : Configuration T O} (one two : (firstOrder A label).toStep.Run left)
    (before suffix : List (Firing T S O)) (f g : Firing T S O)
    (straight : sites A label one = before ++ f :: g :: suffix)
    (swapped : sites A label two = before ++ g :: f :: suffix)
    (plan : (contextualRunInterpretation A label).Plan (right := right) PUnit.unit one)
    (plan' : (contextualRunInterpretation A label).Plan (right := right) PUnit.unit two) :
    (firstOrderTransport A label).TraceEquiv (AnnotatedRuns.tensor left right)
      (plan.realize (contextualRunInterpretation A label) PUnit.unit one).execution
      (plan'.realize (contextualRunInterpretation A label) PUnit.unit two).execution :=
  native_transposition A label _ _ before suffix f g
    ((plan_sites A label PUnit.unit one plan).trans straight)
    ((plan_sites A label PUnit.unit two plan').trans swapped)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.FirstOrder
