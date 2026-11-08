import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsSeparationConcurrency
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsSeparationSoundness

/-!
# Separating examples for separation logic over runs

On the control signature of `AnnotatedRuns.Controls` (natural-number identities; `0 : f(X)`,
`1 : X`, `9 : 9`, other identities `2`, `3 : 0`).

## The algebra

* `classes_not_cancellative`: knowledge `X = 1` joins with itself and with the empty configuration
  to the same class.
* `conflicting_knowledge_not_separable`: disjoint occurrences whose equations conflict are not
  separable.
* `ends_separable_not_tensor`: a run that makes and then takes `9` starts and ends separable from a
  configuration holding `9`, and their tensor does not run.
* `tell_splits_two_ways`: a tell splits two ways into separated halves.

## The frame rule

* `knowledge_frame_refused`: the taker binds `X = 0`; a frame with disjoint occurrences that knows
  `X = 1` is separable from the taker's start, and the framed taker is refused.
* `name_frame_refused`: the run that makes and takes `9`, framed by `9`, is refused.
* `absence_frame_refused`, `count_frame_refused`: a frame that inserts into an absence query's or a
  count query's region refuses it.
* `evidence_is_not_permission`: knowledge is duplicable and grants no take; one occurrence cannot be
  owned twice. `read_is_not_take`: a shared read is compatible with another read, not with a take.
* `round_verified_by_frames`, `round_from_start`: the taker and the reader, each specified on its
  own occurrence, verified together by two uses of the frame rule and sequencing.
  `round_by_parallel_rule`: the same two specifications, composed by the parallel rule, for the
  order with the reader first. `round_derivable`: the round as a derivation.

## Persistence, concurrency, soundness, authority

* `occupancy_not_persistent`: "occurrence `0` is present" is no persistent predicate from the start.
* `program_frame_fails`: a program run consumes the frame; the frame rule is a law of single runs.
* `shared_read_compatible`: two readers of one occurrence have compatible footprints and form a
  round; no split makes them separated runs.
* `completeness_fails_with_absence`, `soundness_fails_with_count_guard`, `multi_step_frame_unsound`.
* `authority_admits_outside`, `authority_refuses_inside`: owning the persistent region, the absence
  query is local beside a frame outside it, and a frame inside it is not separable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace SeparationRuns

namespace SeparationControls

open Mettapedia.Logic.LP
open GuardFreeProcessOrders (SameUpTo)
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label Run zeros taker reader start taker_valid observer maker noPersistent
  persistent observer_valid)

/-- The empty configuration. -/
abbrev none₀ : Configuration (Term signature) Nat := AnnotatedRuns.Controls.empty

/-- Occurrence `9` alone. -/
def nineSpace : Configuration (Term signature) Nat := ⟨[], {9}⟩

theorem nineSpace_consistent : A.Consistent nineSpace.equations :=
  ⟨Subst.id signature, A.models_nil _⟩

/-! ## The algebra -/

/-- Knowledge `X = 1`. -/
def knowOne : Configuration (Term signature) Nat := ⟨[(.var 0, .const 1)], ∅⟩

theorem knowOne_consistent : A.Consistent knowOne.equations := by
  refine ⟨fun _ => .const 1, ?_⟩
  intro e member
  have same : e = (.var 0, .const 1) := by simpa [knowOne] using member
  subst same
  rfl

/-- **Classes are not cancellative**: knowledge composed with itself and with the empty
configuration gives one class. -/
theorem classes_not_cancellative :
    JoinClass A (ConfigurationClass.mk A knowOne) (ConfigurationClass.mk A knowOne)
        (ConfigurationClass.mk A knowOne) ∧
      JoinClass A (ConfigurationClass.mk A knowOne)
        (ConfigurationClass.mk A (unitConfiguration : Configuration (Term signature) Nat))
        (ConfigurationClass.mk A knowOne) ∧
      ConfigurationClass.mk A knowOne ≠
        ConfigurationClass.mk A (unitConfiguration : Configuration (Term signature) Nat) := by
  refine ⟨joinClass_knowledge_self A knowOne_consistent,
    (joinClass_unit_iff A _).mpr knowOne_consistent, fun same => ?_⟩
  have models := ((Quotient.exact same).1 (fun _ => .const 0)).mpr (A.models_nil _)
  have one := models _ (List.mem_singleton_self _)
  change Term.const (σ := signature) 0 = .const 1 at one
  cases one

/-- `X = 1` on occurrence `0`. -/
def oneAtZero : Configuration (Term signature) Nat := ⟨[(.var 0, .const 1)], {0}⟩

/-- `X = 2` on occurrence `1`. -/
def twoAtOne : Configuration (Term signature) Nat := ⟨[(.var 0, .const 2)], {1}⟩

/-- **Disjoint occurrences whose shared equations conflict are not separable.** -/
theorem conflicting_knowledge_not_separable :
    Disjoint oneAtZero.present twoAtOne.present ∧ A.Consistent oneAtZero.equations ∧
      A.Consistent twoAtOne.equations ∧ ¬ Separable A oneAtZero twoAtOne := by
  refine ⟨by decide, ⟨fun _ => .const 1, ?_⟩, ⟨fun _ => .const 2, ?_⟩, ?_⟩
  · intro e member
    have same : e = (.var 0, .const 1) := by simpa [oneAtZero] using member
    subst same
    rfl
  · intro e member
    have same : e = (.var 0, .const 2) := by simpa [twoAtOne] using member
    subst same
    rfl
  · rintro ⟨-, σ, solved⟩
    have one := solved (.var 0, .const 1) (by simp [oneAtZero, twoAtOne])
    have two := solved (.var 0, .const 2) (by simp [oneAtZero, twoAtOne])
    change σ 0 = .const 1 at one
    change σ 0 = .const 2 at two
    rw [one] at two
    cases two

/-- Takes the persistent `9`. -/
def takerNine : Run := ⟨⟨[.const 9], [], [], [], []⟩, [], ⟨[9], [], []⟩⟩

theorem takerNine_valid : takerNine.Valid A label (maker.result label none₀) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨Subst.id signature, ?_⟩,
    by simp [takerNine]⟩, by simp [takerNine]⟩
  intro e member
  have same : e = (.const 9, label 9) := by
    simpa [Selection.problem, Selection.equations, Selection.result, Firing.result,
      AnnotatedRuns.Controls.empty, maker, takerNine] using member
  subst same
  rfl

/-- Make `9`, then take it. -/
theorem make_then_take_nine : Executable A label none₀ [maker, takerNine] :=
  ⟨StoredControls.maker_valid_empty, takerNine_valid, takerNine_valid.firing.consistent⟩

/-- **Separable ends are not enough for the tensor.** The run that makes and takes `9` starts and
ends separable from `9`; beside `9` it cannot make `9`. -/
theorem ends_separable_not_tensor :
    Separable A none₀ nineSpace ∧
      Separable A (follow label none₀ [maker, takerNine]) nineSpace ∧
      Executable A label none₀ [maker, takerNine] ∧
      ¬ Executable A label (tensor none₀ nineSpace) ([maker, takerNine] ++ []) := by
  refine ⟨⟨by decide, Subst.id signature, A.models_nil _⟩, ⟨by decide, ?_⟩, make_then_take_nine,
    fun runs => ?_⟩
  · obtain ⟨σ, solved⟩ := Executable.joint A label make_then_take_nine
    refine ⟨σ, (A.models_append σ _ _).mpr ⟨?_, A.models_nil σ⟩⟩
    rw [follow_equations]
    exact solved
  · have fresh := runs.1.firing.occurrences.fresh
    revert fresh
    decide

/-- **A tell splits two ways.** -/
theorem tell_splits_two_ways :
    Separated A label TensorControls.empty [] TensorControls.empty [TensorControls.tellOne] ∧
      Separated A label TensorControls.empty [TensorControls.tellOne] TensorControls.empty [] ∧
      ([] : List Run) ++ [TensorControls.tellOne] = [TensorControls.tellOne] ++ [] ∧
      ([] : List Run) ≠ [TensorControls.tellOne] := by
  have plain : ∀ f ∈ [TensorControls.tellOne], ∀ frame : Finset Nat, BlindTo A label frame f := by
    intro f member frame
    obtain rfl := List.mem_singleton.mp member
    exact blindTo_of_plain A label rfl rfl
  have live : Executable A label TensorControls.empty [] := ⟨Subst.id signature, A.models_nil _⟩
  have joint : A.Consistent (TensorControls.tellOne.added label) := by
    refine ⟨fun _ => .const 1, ?_⟩
    intro e member
    have same : e = (.var 0, .const 1) := by
      simpa [Firing.added, GuardFreeProcessOrders.added, Selection.equations,
        TensorControls.tellOne] using member
    subst same
    rfl
  obtain ⟨σ, solved⟩ := joint
  refine ⟨⟨live, TensorControls.tellOne_runs, by decide, fun f member => (by cases member),
    fun g member => plain g member _, ⟨σ, ?_⟩⟩,
    ⟨TensorControls.tellOne_runs, live, by decide, fun f member => plain f member _,
      fun g member => (by cases member), ⟨σ, ?_⟩⟩, rfl, by simp⟩
  · simpa [jointStore, TensorControls.empty] using solved
  · simpa [jointStore, TensorControls.empty] using solved

/-! ## The frame rule -/

/-- Occurrence `1` beside the knowledge `X = 1`. -/
def knowsOneFrame : Configuration (Term signature) Nat := ⟨[(.var 0, .const 1)], {1}⟩

/-- **The frame's knowledge must agree with what the run tells.** The taker binds `X = 0`. A frame
with disjoint occurrences that knows `X = 1` is separable from the taker's start, and the framed
taker is refused. -/
theorem knowledge_frame_refused :
    taker.Valid A label TensorControls.takerSide ∧
      Separable A TensorControls.takerSide knowsOneFrame ∧
      ¬ taker.Valid A label (tensor TensorControls.takerSide knowsOneFrame) := by
  refine ⟨TensorControls.taker_runs.1, ⟨by decide, fun _ => .const 1, ?_⟩, fun valid => ?_⟩
  · intro e member
    have same : e = (.var 0, .const 1) := by
      simpa [TensorControls.takerSide, knowsOneFrame] using member
    subst same
    rfl
  · obtain ⟨σ, solved⟩ := valid.firing.consistent
    have one := solved (.var 0, .const 1) (by
      simp [Selection.problem, Selection.equations, tensor, TensorControls.takerSide, knowsOneFrame,
        taker])
    have zero := solved (ConstraintMultisetRewriting.Controls.f (.const 0), label 0) (by
      simp [Selection.problem, Selection.equations, tensor, TensorControls.takerSide, knowsOneFrame,
        taker])
    change σ 0 = .const 1 at one
    change ConstraintMultisetRewriting.Controls.f (.const 0) =
      ConstraintMultisetRewriting.Controls.f (σ 0) at zero
    have children : (fun _ : Fin 1 => Term.const (σ := signature) 0) = (fun _ => σ 0) :=
      eq_of_heq (Term.app.inj zero).2
    have bound := congr_fun children 0
    rw [one] at bound
    cases bound

/-- **Made identities are names**: the run that makes and takes `9`, framed by `9`, is refused,
although the frame is separable from where it starts and where it ends. -/
theorem name_frame_refused :
    Separable A none₀ nineSpace ∧ Separable A (follow label none₀ [maker, takerNine]) nineSpace ∧
      ¬ Executable A label (tensor none₀ nineSpace) [maker, takerNine] :=
  ⟨ends_separable_not_tensor.1, ends_separable_not_tensor.2.1, ends_separable_not_tensor.2.2.2⟩

/-- **A frame inserting into an absence query's region refuses it.** -/
theorem absence_frame_refused :
    observer.Valid A label none₀ ∧ Separable A (observer.result label none₀) nineSpace ∧
      ¬ observer.Valid A label (tensor none₀ nineSpace) := by
  refine ⟨observer_valid, ⟨by decide, Subst.id signature, ?_⟩, fun valid => ?_⟩
  · simp [Firing.result, Selection.result, Selection.problem, Selection.equations,
      AnnotatedRuns.Controls.empty, nineSpace, observer]
  · have holds := valid.observations _ (List.mem_singleton_self _) (Subst.id signature) (by
      simp [Selection.problem, Selection.equations, tensor, AnnotatedRuns.Controls.empty, nineSpace,
        observer])
    revert holds
    decide

/-- The region of the default atom `2`. -/
def isTwo : Term signature → Bool
  | .const name => name == 2
  | _ => false

/-- A census of the region of `2` that saw exactly occurrence `5`. -/
def countFive : MeTTaCalculus.OccurrenceCommits.PredicateQuery Nat (Term signature) := ⟨isTwo, {5}⟩

/-- Observes that exactly occurrence `5` carries `2`. -/
def counter : Run := ⟨⟨[], [], [], [], []⟩, [PredicateQueryAdmission.Query.fixed countFive], ⟨[], [], []⟩⟩

def fiveSpace : Configuration (Term signature) Nat := ⟨[], {5}⟩

def sixSpace : Configuration (Term signature) Nat := ⟨[], {6}⟩

theorem counter_valid : counter.Valid A label fiveSpace := by
  refine (PredicateQueryAdmission.valid_fixed_iff A label counter.rule [countFive] fiveSpace
    counter.selection).mpr ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
      ⟨Subst.id signature, by simp [Selection.problem, Selection.equations, fiveSpace, counter]⟩,
      by simp [counter]⟩, ?_⟩
  intro query member
  obtain rfl := List.mem_singleton.mp member
  decide

/-- **A frame inserting into a count query's region refuses it.** -/
theorem count_frame_refused :
    counter.Valid A label fiveSpace ∧ Separable A (counter.result label fiveSpace) sixSpace ∧
      ¬ counter.Valid A label (tensor fiveSpace sixSpace) := by
  refine ⟨counter_valid, ⟨by decide, Subst.id signature, ?_⟩, fun valid => ?_⟩
  · simp [Firing.result, Selection.result, Selection.problem, Selection.equations, fiveSpace,
      sixSpace, counter]
  · have holds := valid.observations _ (List.mem_singleton_self _) (Subst.id signature) (by
      simp [Selection.problem, Selection.equations, tensor, fiveSpace, sixSpace, counter])
    revert holds
    decide

/-- Knowledge `X = 0`, and no occurrence. -/
def knowZero : Configuration (Term signature) Nat := ⟨[(.var 0, .const 0)], ∅⟩

/-- The knowledge that `X` is `0`. -/
def xIsZero (σ : Subst signature) : Prop := σ 0 = .const 0

/-- **Reusable evidence is not a permission to consume.** Knowledge that `X = 0` is duplicable,
and no configuration of knowledge alone runs the taker, which needs the occurrence `0`; that
occurrence cannot be owned twice. -/
theorem evidence_is_not_permission :
    knows A xIsZero knowZero ∧ star A (knows A xIsZero) (knows A xIsZero) knowZero ∧
      (∀ C, knows A xIsZero C → ¬ Executable A label C [taker]) ∧
      ¬ star A (pointsTo A label 0 (label 0)) (pointsTo A label 0 (label 0)) TensorControls.takerSide := by
  have known : knows A xIsZero knowZero := by
    refine ⟨rfl, ⟨zeros, ?_⟩, fun σ solved => solved _ (List.mem_singleton_self _)⟩
    intro e member
    have same : e = (.var 0, .const 0) := by simpa [knowZero] using member
    subst same
    rfl
  refine ⟨known, knows_duplicable A known, ?_, pointsTo_star_self A label 0 _ _ _⟩
  rintro C ⟨present, -, -⟩ runs
  have taken := runs.1.firing.occurrences.taken_subset
    (show (0 : Nat) ∈ (taker.selection.commit (T := Term signature)).taken by decide)
  rw [present] at taken
  exact Finset.notMem_empty 0 taken

/-! ## A program verified by the frame rule -/

/-- Where the taker leaves its side. -/
abbrev takerEnd : Configuration (Term signature) Nat := follow label TensorControls.takerSide [taker]

/-- Where the reader leaves its side. -/
abbrev readerEnd : Configuration (Term signature) Nat := follow label TensorControls.readerSide [reader]

theorem taker_queryFree : ∀ f ∈ [taker], QueryFree f := by
  intro f member
  obtain rfl := List.mem_singleton.mp member
  exact ⟨rfl, fun check inChecks => by simp [taker] at inChecks⟩

theorem reader_queryFree : ∀ f ∈ [reader], QueryFree f := by
  intro f member
  obtain rfl := List.mem_singleton.mp member
  exact ⟨rfl, fun check inChecks => by simp [reader] at inChecks⟩

/-- **The taker, framed by the reader's occurrence**: the classical frame rule. -/
theorem taker_framed :
    Triple A label (star A (exactly A TensorControls.takerSide) (exactly A TensorControls.readerSide))
      [taker] (star A (exactly A takerEnd) (exactly A TensorControls.readerSide)) := by
  refine frame_rule_spatial A label (triple_exactly A label TensorControls.taker_runs)
    taker_queryFree fun E same => ⟨fun σ => (same.1 σ).symm, ?_⟩
  rw [← same.2]
  decide

/-- **The reader, framed by what the taker left**: the frame shares the variable `X`, and its
knowledge `X = 0` agrees with what the reader tells. -/
theorem reader_framed :
    Triple A label (star A (exactly A TensorControls.readerSide) (exactly A takerEnd)) [reader]
      (star A (exactly A readerEnd) (exactly A takerEnd)) := by
  refine frame_rule_queryFree A label (triple_exactly A label TensorControls.reader_runs)
    reader_queryFree fun C E hC hE _ => ⟨?_, zeros, ?_⟩
  · unfold space
    rw [← hC.2, ← hE.2]
    decide
  · rw [A.models_append, follow_equations, A.models_append]
    refine ⟨⟨(hC.1 zeros).mp (A.models_nil zeros), ?_⟩, (hE.1 zeros).mp ?_⟩
    · intro e member
      have same : e = (.var 1, label 1) := by
        simpa [Firing.added, GuardFreeProcessOrders.added, Selection.equations, reader] using member
      subst same
      rfl
    · intro e member
      have same : e = (ConstraintMultisetRewriting.Controls.f (.const 0), label 0) := by
        simpa [takerEnd, follow, Firing.result, Selection.result, Selection.problem,
          Selection.equations, TensorControls.takerSide, taker] using member
      subst same
      rfl

/-- **The round of the taker and the reader, verified from local specifications**: each firing is
specified on its own occurrence, and two uses of the frame rule with sequencing verify the run of
both. -/
theorem round_verified_by_frames :
    Triple A label (star A (exactly A TensorControls.takerSide) (exactly A TensorControls.readerSide))
      [taker, reader] (star A (exactly A readerEnd) (exactly A takerEnd)) :=
  triple_append A label taker_framed
    (triple_mono A label reader_framed (fun _ holds => star_comm A holds) (fun _ holds => holds))

/-- **The verified run from the start.** -/
theorem round_from_start :
    Executable A label start [taker, reader] ∧
      star A (exactly A readerEnd) (exactly A takerEnd) (follow label start [taker, reader]) := by
  refine round_verified_by_frames start ⟨TensorControls.takerSide, TensorControls.readerSide,
    ⟨by decide, Subst.id signature, A.models_nil _⟩, ⟨fun σ => Iff.rfl, by decide⟩,
    SameUpTo.refl A _, SameUpTo.refl A _⟩

/-- **The parallel rule, used**: the taker and the reader from their own sides, run in the order
with the reader first. -/
theorem round_by_parallel_rule :
    Triple A label (star A (exactly A TensorControls.takerSide) (exactly A TensorControls.readerSide))
      [reader, taker] (star A (exactly A takerEnd) (exactly A readerEnd)) := by
  refine parallel_rule A label (triple_exactly A label TensorControls.taker_runs)
    (triple_exactly A label TensorControls.reader_runs) ?_ ?_ ?_ (.right reader (.left taker .nil))
  · intro C₁ C₂ h₁ h₂ _
    unfold space
    rw [← h₁.2, ← h₂.2]
    decide
  · intro C₁ C₂ _ _ _
    refine ⟨fun f member => ?_, fun g member => ?_⟩
    · obtain rfl := List.mem_singleton.mp member
      exact blindTo_of_plain A label rfl rfl
    · obtain rfl := List.mem_singleton.mp member
      exact blindTo_of_plain A label rfl rfl
  · intro C₁ C₂ h₁ h₂ _
    refine ⟨zeros, ?_⟩
    rw [models_jointStore]
    refine ⟨(h₁.1 zeros).mp (A.models_nil zeros), (h₂.1 zeros).mp (A.models_nil zeros), ?_, ?_⟩
    · intro e member
      have same : e = (ConstraintMultisetRewriting.Controls.f (.const 0), label 0) := by
        simpa [Firing.added, GuardFreeProcessOrders.added, Selection.equations, taker] using member
      subst same
      rfl
    · intro e member
      have same : e = (.var 1, label 1) := by
        simpa [Firing.added, GuardFreeProcessOrders.added, Selection.equations, reader] using member
      subst same
      rfl

/-- **A derivation of the round, through completeness**: positive control for
`derives_iff_reaches`. -/
theorem round_derivable :
    Derives A label {taker, reader} start (follow label start [taker, reader]) := by
  refine (derives_iff_reaches A label ?_).mpr
    ⟨[taker, reader], by simp, AnnotatedRuns.Controls.taker_then_reader, SameUpTo.refl A _⟩
  intro f member
  rcases Set.mem_insert_iff.mp member with rfl | single
  · exact ⟨rfl, fun check inChecks => by simp [taker] at inChecks⟩
  · obtain rfl := Set.mem_singleton_iff.mp single
    exact ⟨rfl, fun check inChecks => by simp [reader] at inChecks⟩

/-! ## Persistence -/

/-- **Occupancy is not persistent**: the taker takes occurrence `0`. -/
theorem occupancy_not_persistent :
    ¬ ∃ P : Persistent A label start, ∀ y, restrict P y = atEnd A label start (PresentAt A 0) y :=
  presentAt_not_persistent A label (w := [taker]) ⟨taker_valid, taker_valid.firing.consistent⟩
    (by decide) (by decide)

/-- **The frame rule is a law of runs, not of programs.** The start is a part without `0` beside the
frame `0 ↦ f(X)`; the taker program has a run from it after which no part carries the frame. A
single run is framed only by frames apart from what it uses (`frame_rule`); a program's runs are
not fixed in advance, so R28's program triples do not frame. -/
theorem program_frame_fails :
    star A (fun C => (0 : Nat) ∉ C.present ∧ A.Consistent C.equations)
        (pointsTo A label 0 (label 0)) start ∧
      Executable A label start [taker] ∧
      ¬ star A (fun _ => True) (pointsTo A label 0 (label 0)) (follow label start [taker]) := by
  refine ⟨⟨⟨[], {1}⟩, ⟨[], {0}⟩, ⟨by decide, Subst.id signature, A.models_nil _⟩,
    ⟨fun σ => Iff.rfl, by decide⟩, ⟨by decide, Subst.id signature, A.models_nil _⟩,
    ⟨rfl, rfl, fun σ => Iff.rfl⟩⟩, ⟨taker_valid, taker_valid.firing.consistent⟩, fun framed => ?_⟩
  have present := ((star_true_pointsTo_iff A label 0 (label 0) _).mp (star_comm A framed)).1
  revert present
  decide

/-! ## Concurrency -/

/-- Reads occurrence `1` and makes `4`. -/
def readerB : Run := ⟨⟨[], [.var 2], [], [], [.const 2]⟩, [], ⟨[], [1], [4]⟩⟩

/-- Takes occurrence `1`. -/
def takerOne : Run := ⟨⟨[.var 2], [], [], [], []⟩, [], ⟨[1], [], []⟩⟩

theorem readerB_valid_at_start : readerB.Valid A label start := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, by simp [readerB]⟩,
    by simp [readerB]⟩
  intro e member
  have same : e = (.var 2, label 1) := by
    simpa [Selection.problem, Selection.equations, start, readerB] using member
  subst same
  rfl

/-- **Two readers of one occurrence**: compatible footprints, a round at the start, and no split
into separated runs. -/
theorem shared_read_compatible :
    Bernstein label reader readerB ∧ (1 : Nat) ∈ reader.selection.read ∧
      (1 : Nat) ∈ readerB.selection.read ∧ Round A label start [reader, readerB] ∧
      ∀ C₁ C₂ : Configuration (Term signature) Nat, ¬ Separated A label C₁ [reader] C₂ [readerB] := by
  have bernstein : Bernstein label reader readerB := by
    rw [bernstein_iff_pointwise]
    intro σ o
    refine ⟨fun written => ⟨fun other => ?_, fun other => ?_⟩, fun written other => ?_⟩ <;>
      simp [Writes, ReadsAt, reader, readerB] at written other <;> omega
  refine ⟨bernstein, by decide, by decide, ?_, fun C₁ C₂ separated => ?_⟩
  · refine round_pair_of_bernstein A label ⟨rfl, by simp [Firing.StaticQueries, reader]⟩
      ⟨rfl, by simp [Firing.StaticQueries, readerB]⟩ RoundControls.reader_valid_at_start
      readerB_valid_at_start ⟨zeros, ?_⟩ bernstein
    intro e member
    have cases : e = (.var 1, label 1) ∨ e = (.var 2, label 1) := by
      simpa [jointProblem, Firing.added, GuardFreeProcessOrders.added, Selection.equations, start,
        reader, readerB] using member
    rcases cases with rfl | rfl <;> rfl
  · have one₁ : (1 : Nat) ∈ C₁.present :=
      used_present A label separated.left.1 (Or.inr (by decide))
    have one₂ : (1 : Nat) ∈ C₂.present :=
      used_present A label separated.right.1 (Or.inr (by decide))
    exact Finset.disjoint_left.mp separated.apart (Finset.mem_union_left _ one₁)
      (Finset.mem_union_left _ one₂)

/-- **A shared read is not a take.** -/
theorem read_is_not_take : Bernstein label reader readerB ∧ ¬ Bernstein label reader takerOne := by
  refine ⟨shared_read_compatible.1, fun bernstein => ?_⟩
  have pointwise := (bernstein_iff_pointwise label).mp bernstein zeros 1
  exact (pointwise.2 (Or.inl (by decide))) (Or.inl (by decide))

/-! ## Soundness and completeness -/

/-- Makes `8` when no persistent atom is present. -/
def unlessNine : Run :=
  ⟨⟨[], [], [], [], [.const 2]⟩, [PredicateQueryAdmission.Query.fixed noPersistent], ⟨[], [], [8]⟩⟩

theorem unlessNine_valid : unlessNine.Valid A label none₀ := by
  refine (PredicateQueryAdmission.valid_fixed_iff A label unlessNine.rule [noPersistent] none₀
    unlessNine.selection).mpr ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
      ⟨Subst.id signature, by
        simp [Selection.problem, Selection.equations, AnnotatedRuns.Controls.empty, unlessNine]⟩,
      by simp [unlessNine]⟩, ?_⟩
  intro query member
  obtain rfl := List.mem_singleton.mp member
  decide

/-- **Completeness fails with an absence query.** The framed small step of the absence query beside
`9` is a derivation; no run of the program reaches its end. -/
theorem completeness_fails_with_absence :
    Derives A label {unlessNine} nineSpace (tensor (unlessNine.result label none₀) nineSpace) ∧
      ¬ ProgramReaches A label {unlessNine} nineSpace
        (tensor (unlessNine.result label none₀) nineSpace) := by
  refine ⟨.step ⟨unlessNine, Set.mem_singleton _, none₀, nineSpace, by decide, unlessNine_valid,
      ⟨by decide, Subst.id signature, A.models_nil _⟩, ⟨by decide, Subst.id signature, ?_⟩,
      ⟨fun σ => Iff.rfl, by decide⟩, SameUpTo.refl A _⟩ (.refl ⟨Subst.id signature, ?_⟩
        (SameUpTo.refl A _)), ?_⟩
  · simp [Firing.result, Selection.result, Selection.problem, Selection.equations,
      AnnotatedRuns.Controls.empty, nineSpace, unlessNine]
  · simp [tensor, Firing.result, Selection.result, Selection.problem, Selection.equations,
      AnnotatedRuns.Controls.empty, nineSpace, unlessNine]
  · rintro ⟨w, inF, runs, same⟩
    cases w with
    | nil =>
        have present := same.2
        revert present
        decide
    | cons f w =>
        obtain rfl := Set.mem_singleton_iff.mp (inF f List.mem_cons_self)
        have holds := runs.1.observations _ (List.mem_singleton_self _) (Subst.id signature) (by
          simp [Selection.problem, Selection.equations, nineSpace, unlessNine])
        revert holds
        decide

/-- Makes `8` when exactly one occurrence carries `9`. -/
def countNine : Run := ⟨⟨[], [], [], [.count (.const 9) 1], [.const 2]⟩, [], ⟨[], [], [8]⟩⟩

theorem countNine_valid : countNine.Valid A label nineSpace := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
    ⟨Subst.id signature, by simp [Selection.problem, Selection.equations, nineSpace, countNine]⟩,
    ?_⟩, by simp [countNine]⟩
  intro check member σ _
  obtain rfl := List.mem_singleton.mp member
  show (Check.matches A σ label nineSpace.present (.const 9)).card = 1
  have region : Check.matches A σ label nineSpace.present (.const 9) = {9} := by
    ext o
    simp only [Check.matches, Finset.mem_filter, nineSpace, Finset.mem_singleton]
    constructor
    · exact fun inside => inside.1
    · rintro rfl
      exact ⟨rfl, rfl⟩
  rw [region]
  exact Finset.card_singleton 9

/-- **Soundness fails with a count guard**: the guard counted `9`, which is not in its footprint, so
no small axiom admits it. -/
theorem soundness_fails_with_count_guard :
    ProgramReaches A label {countNine} nineSpace (countNine.result label nineSpace) ∧
      ¬ Derives A label {countNine} nineSpace (countNine.result label nineSpace) := by
  refine ⟨⟨[countNine], by simp, ⟨countNine_valid, countNine_valid.firing.consistent⟩,
    SameUpTo.refl A _⟩, fun derives => ?_⟩
  cases derives with
  | refl _ same =>
      have present := same.2
      revert present
      decide
  | step framed _ =>
      obtain ⟨f, member, M, E, foot, valid, -⟩ := framed
      obtain rfl := Set.mem_singleton_iff.mp member
      obtain ⟨σ, solved⟩ := valid.firing.consistent
      have counted := valid.firing.checks _ (List.mem_singleton_self _) σ solved
      have empty : footprintSet countNine = ∅ := by decide
      change (Check.matches A σ label M.present (.const 9)).card = 1 at counted
      rw [foot, empty] at counted
      simp [Check.matches] at counted

/-- Makes `9` and `7`. -/
def makerPair : Run := ⟨⟨[], [], [], [], [.const 9, .const 2]⟩, [], ⟨[], [], [9, 7]⟩⟩

/-- Takes `9` and `7`, and makes `5`. -/
def takerPair : Run := ⟨⟨[.const 9, .const 2], [], [], [], [.const 2]⟩, [], ⟨[9, 7], [], [5]⟩⟩

theorem makerPair_valid : makerPair.Valid A label none₀ := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨Subst.id signature, ?_⟩,
    by simp [makerPair]⟩, by simp [makerPair]⟩
  simp [Selection.problem, Selection.equations, AnnotatedRuns.Controls.empty, makerPair]

theorem takerPair_valid : takerPair.Valid A label (makerPair.result label none₀) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨Subst.id signature, ?_⟩,
    by simp [takerPair]⟩, by simp [takerPair]⟩
  intro e member
  have cases : e = (.const 9, label 9) ∨ e = (.const 2, label 7) := by
    simpa [Selection.problem, Selection.equations, Selection.result, Firing.result,
      AnnotatedRuns.Controls.empty, makerPair, takerPair] using member
  rcases cases with rfl | rfl <;> rfl

theorem pair_runs : Executable A label none₀ [makerPair, takerPair] :=
  ⟨makerPair_valid, takerPair_valid, takerPair_valid.firing.consistent⟩

/-- **Framing a whole derivation is unsound, even without queries.** The program makes `9` and `7`
and then takes them; from nothing it reaches `5`. Beside `9`, which is separable from where it
starts and from where it ends, it reaches nothing new: made identities are names. -/
theorem multi_step_frame_unsound :
    ProgramReaches A label {makerPair, takerPair} none₀
        (follow label none₀ [makerPair, takerPair]) ∧
      Separable A none₀ nineSpace ∧
      Separable A (follow label none₀ [makerPair, takerPair]) nineSpace ∧
      ¬ ProgramReaches A label {makerPair, takerPair} (tensor none₀ nineSpace)
        (tensor (follow label none₀ [makerPair, takerPair]) nineSpace) := by
  refine ⟨⟨[makerPair, takerPair], by simp, pair_runs, SameUpTo.refl A _⟩,
    ⟨by decide, Subst.id signature, A.models_nil _⟩, ⟨by decide, ?_⟩, ?_⟩
  · obtain ⟨σ, solved⟩ := Executable.joint A label pair_runs
    refine ⟨σ, (A.models_append σ _ _).mpr ⟨?_, A.models_nil σ⟩⟩
    rw [follow_equations]
    exact solved
  · rintro ⟨w, inF, runs, same⟩
    cases w with
    | nil =>
        have present := same.2
        revert present
        decide
    | cons f w =>
        rcases Set.mem_insert_iff.mp (inF f List.mem_cons_self) with rfl | single
        · have fresh := runs.1.firing.occurrences.fresh
          revert fresh
          decide
        · obtain rfl := Set.mem_singleton_iff.mp single
          have taken := runs.1.firing.occurrences.taken_subset
          revert taken
          decide

/-! ## Authority over regions -/

/-- The empty configuration, owning the persistent region. -/
def owner : Owned (Term signature) Nat := ⟨none₀, [persistent]⟩

/-- **Owning the region makes the absence query local**: beside the occurrence `0`, outside the
persistent region, the owner's absence query is still admitted. -/
theorem authority_admits_outside :
    OwnedSeparable A label owner ⟨TensorControls.takerSide, []⟩ ∧
      observer.Valid A label (tensor none₀ TensorControls.takerSide) := by
  have sep : OwnedSeparable A label owner ⟨TensorControls.takerSide, []⟩ := by
    refine ⟨⟨by decide, Subst.id signature, A.models_nil _⟩, ?_,
      fun region member => (by cases member)⟩
    intro region member o present
    obtain rfl := List.mem_singleton.mp member
    have zero : o = 0 := by simpa [TensorControls.takerSide] using present
    subst zero
    rfl
  refine ⟨sep, owned_valid_frame A label (x := owner) (y := ⟨TensorControls.takerSide, []⟩)
    (fun check member => by simp [observer] at member) ?_ observer_valid sep
    ⟨by decide, Subst.id signature, ?_⟩⟩
  · intro query member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨persistent, List.mem_singleton_self _, fun _ => rfl⟩
  · simp [owner, none₀, Firing.result, Selection.result, Selection.problem, Selection.equations,
      AnnotatedRuns.Controls.empty, TensorControls.takerSide, observer]

/-- **A frame inside an owned region is not separable**: the occurrence `9` lies in the persistent
region the owner owns. -/
theorem authority_refuses_inside : ¬ OwnedSeparable A label owner ⟨nineSpace, []⟩ := by
  rintro ⟨-, inside, -⟩
  have := inside persistent (List.mem_singleton_self _) 9 (by decide)
  revert this
  decide

end SeparationControls

end SeparationRuns

open SeparationRuns.SeparationControls

#print axioms classes_not_cancellative
#print axioms conflicting_knowledge_not_separable
#print axioms takerNine_valid
#print axioms make_then_take_nine
#print axioms ends_separable_not_tensor
#print axioms tell_splits_two_ways
#print axioms knowledge_frame_refused
#print axioms name_frame_refused
#print axioms absence_frame_refused
#print axioms counter_valid
#print axioms count_frame_refused
#print axioms evidence_is_not_permission
#print axioms taker_framed
#print axioms reader_framed
#print axioms round_verified_by_frames
#print axioms round_from_start
#print axioms round_by_parallel_rule
#print axioms round_derivable
#print axioms occupancy_not_persistent
#print axioms program_frame_fails
#print axioms readerB_valid_at_start
#print axioms shared_read_compatible
#print axioms read_is_not_take
#print axioms unlessNine_valid
#print axioms completeness_fails_with_absence
#print axioms countNine_valid
#print axioms soundness_fails_with_count_guard
#print axioms makerPair_valid
#print axioms takerPair_valid
#print axioms pair_runs
#print axioms multi_step_frame_unsound
#print axioms authority_admits_outside
#print axioms authority_refuses_inside

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
