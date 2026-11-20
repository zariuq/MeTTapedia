import Mettapedia.PLN.WorldModel.WeightedSourcePrograms
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.AnswerCollection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit

/-!
# Weighted finite computations on the source answer collector

Compile finite shared-draw bodies to actual read-only source computations by
specializing a complete finite draw tape. Each returned source datum is the
world index, so two equal output values keep distinct execution occurrences.
Scores are retained by the weighted observer of captured traces, not added as
an unsupported source primitive. This proves a concrete exhaustive source run,
collector completion and equality of its weighted fold with the BDD circuit.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.WeightedSourceExecution

open scoped ENNReal
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open Mettapedia.PLN.WorldModel.WeightedSourcePrograms
open Mettapedia.Logic.BDDCore Mettapedia.Logic.BDDCore.WMPLNBDDWMCExact
open Mettapedia.Machines.GuardEvaluationRegimes (scalar)

abbrev D : Discipline MSig [] () := numbers.discipline
abbrev SourceComp := Comp mkeys [] () D.Ty
abbrev SourceBranch := Branch mkeys [] () D.Ty
abbrev SourceWorld := World mkeys [] ()

/-- No source calls or effects are needed after finite tape specialization. -/
def program : SourceLanguage.Program mkeys [] () D.Ty := ⟨[], fun _ => .fail⟩
def supply : Nat → MClosed := fun _ => csym "space"

def terminal {n : Nat} (world : Fin (2 ^ n)) : SourceBranch :=
  ⟨[], .value (num world.val), [], []⟩

def start (computation : SourceComp) : SourceBranch := ⟨[], .eval computation, [], []⟩

private def number? : MData → Option Int
  | .op (.inl (.num value)) .nil => some value
  | _ => none

theorem terminal_injective {n : Nat} : Function.Injective (terminal (n := n)) := by
  intro left right same
  have focused := congrArg Branch.focus same
  have datum := Focus.value.inj focused
  have numbered := congrArg number? datum
  have equal : (left.val : Int) = (right.val : Int) := Option.some.inj numbered
  exact Fin.ext (Int.ofNat_inj.mp equal)

/-- Structural finite specialization: score annotations remain in the weight
valuation, observations and conditionals select actual source computations. -/
def leaf {n : Nat} : Body n → Fin (2 ^ n) → SourceComp
  | .ret _, world => .ret (num world.val)
  | .fail, _ => .fail
  | .score _ body, world => leaf body world
  | .observe test body, world =>
      if scalar (worldAssignmentEquiv n world) test then leaf body world else .fail
  | .branch test yes no, world =>
      if scalar (worldAssignmentEquiv n world) test then leaf yes world else leaf no world

theorem leaf_result {n : Nat} (body : Body n) (world : Fin (2 ^ n)) :
    leaf body world = if (body.result (worldAssignmentEquiv n world)).isSome then
      .ret (num world.val) else .fail := by
  induction body with
  | ret value => rfl
  | fail => rfl
  | score factor body ih => exact ih
  | observe test body ih =>
    cases h : scalar (worldAssignmentEquiv n world) test <;> simp [leaf, Body.result, h, ih]
  | branch test yes no iy ino =>
    cases h : scalar (worldAssignmentEquiv n world) test <;> simp [leaf, Body.result, h, iy, ino]

def sourceFrom {n : Nat} (body : Body n) : List (Fin (2 ^ n)) → SourceComp
  | [] => .fail
  | world :: worlds => .choice (leaf body world) (sourceFrom body worlds)

def completed {n : Nat} (body : Body n) : List (Fin (2 ^ n)) → List SourceBranch
  | [] => []
  | world :: worlds => if (body.result (worldAssignmentEquiv n world)).isSome then
      terminal world :: completed body worlds else completed body worlds

theorem completed_ready {n : Nat} (body : Body n) (worlds : List (Fin (2 ^ n)))
    (branch : SourceBranch) (member : branch ∈ completed body worlds) :
    branch.Finished (D := D) ∧ Solvable branch.store := by
  induction worlds with
  | nil => simp [completed] at member
  | cons world worlds ih =>
    unfold completed at member
    split at member
    · rcases List.mem_cons.mp member with rfl | member
      · exact ⟨⟨rfl, _, rfl⟩, live_nil⟩
      · exact ih member
    · exact ih member

/-- Every specialized leaf is an actual source return or failure transition. -/
theorem leaf_runs {n : Nat} (body : Body n) (world : Fin (2 ^ n)) (shared : SourceWorld) :
    Runs D program supply ⟨shared, {start (leaf body world)}⟩
      ⟨shared, (completed body [world] : Multiset SourceBranch)⟩ := by
  rw [leaf_result]
  simp only [completed]
  split
  · exact .single (Step.single live_nil (.ret _ _ _ _ _))
  · exact .single (Step.single live_nil (.fail _ _ _ _))

/-- Exact source execution, with occurrence multiplicity retained. -/
theorem source_runs {n : Nat} (body : Body n) (worlds : List (Fin (2 ^ n))) (shared : SourceWorld) :
    Runs D program supply ⟨shared, {start (sourceFrom body worlds)}⟩
      ⟨shared, (completed body worlds : Multiset SourceBranch)⟩ := by
  induction worlds with
  | nil => exact .single (Step.single live_nil (.fail _ _ _ _))
  | cons world worlds ih =>
    have step : Step D program supply ⟨shared, {start (sourceFrom body (world :: worlds))}⟩
        ⟨shared, {start (leaf body world)} + {start (sourceFrom body worlds)}⟩ :=
      Step.single live_nil (.choice _ _ _ _ _ _)
    have first := (leaf_runs body world shared).frame {start (sourceFrom body worlds)}
    have second := ih.frame (completed body [world] : Multiset SourceBranch)
    have bridge : (completed body [world] : Multiset SourceBranch) + {start (sourceFrom body worlds)} =
        {start (sourceFrom body worlds)} + (completed body [world] : Multiset SourceBranch) := add_comm _ _
    rw [bridge] at first
    have last : (completed body worlds : Multiset SourceBranch) + (completed body [world] : Multiset SourceBranch) =
        (completed body (world :: worlds) : Multiset SourceBranch) := by
      by_cases h : (body.result (worldAssignmentEquiv n world)).isSome = true
      · simp only [completed, h, if_true, Multiset.coe_nil, ← Multiset.cons_coe]
        exact (add_comm _ _).trans (Multiset.singleton_add _ _)
      · simp [completed, h]

    rw [last] at second
    exact (Relation.ReflTransGen.single step).trans (first.trans second)

/-- The resulting source configuration has only finished live branches. -/
theorem source_quiescent {n : Nat} (body : Body n) (worlds : List (Fin (2 ^ n))) (shared : SourceWorld) :
    Config.Quiescent (D := D) program supply ⟨shared, (completed body worlds : Multiset SourceBranch)⟩ :=
  Config.quiescent_of_finished fun branch member _ =>
    (completed_ready body worlds branch (Multiset.mem_coe.mp member)).1

/-- Lift a source run through the actual collector's drive transitions. -/
theorem collector_drive {before after : Config mkeys [] () D.Ty}
    (run : Runs D program supply before after) :
    AnswerCollection.CollectorRuns D program supply
      (AnswerCollection.State.initial before) (AnswerCollection.State.initial after) := by
  induction run with
  | refl => exact .refl
  | tail previous step ih => exact ih.tail (.drive [] 0 step)

/-- Drain a finite source answer bag using the collector's capture rule. -/
theorem collector_capture (branches : List SourceBranch) (shared : SourceWorld)
    (answers : List SourceBranch)
    (ready : ∀ branch ∈ branches, branch.Finished (D := D) ∧ Solvable branch.store) :
    AnswerCollection.CollectorRuns D program supply
      ⟨⟨shared, (branches : Multiset SourceBranch)⟩, answers, 0⟩
      ⟨⟨shared, 0⟩, branches.reverse ++ answers, 0⟩ := by
  induction branches generalizing answers with
  | nil => exact .refl
  | cons branch branches ih =>
    have proof := ready branch (by simp)
    have capture := AnswerCollection.CollectorStep.admin (D := D) (P := program) (supply := supply)
      (.capture shared branch (branches : Multiset SourceBranch) answers 0 proof.1 proof.2)
    have rest := ih (branch :: answers) (fun b member => ready b (List.mem_cons_of_mem _ member))
    simpa [List.reverse_cons, List.append_assoc] using (Relation.ReflTransGen.single capture).trans rest

def finishedState {n : Nat} (body : Body n) (worlds : List (Fin (2 ^ n))) (shared : SourceWorld) :
    AnswerCollection.State mkeys [] () D :=
  ⟨⟨shared, 0⟩, (completed body worlds).reverse, 0⟩

theorem collector_runs {n : Nat} (body : Body n) (worlds : List (Fin (2 ^ n))) (shared : SourceWorld) :
    AnswerCollection.CollectorRuns D program supply
      (AnswerCollection.State.initial ⟨shared, {start (sourceFrom body worlds)}⟩)
      (finishedState body worlds shared) := by
  exact (collector_drive (source_runs body worlds shared)).trans
    (by simpa [AnswerCollection.State.initial, finishedState] using
      collector_capture (completed body worlds) shared [] (completed_ready body worlds))

theorem finishedState_valid {n : Nat} (body : Body n) (worlds : List (Fin (2 ^ n))) (shared : SourceWorld) :
    (finishedState body worlds shared).Valid :=
  (collector_runs body worlds shared).preserves_valid (AnswerCollection.State.initial_valid _)

/-- Captured rows retain the actual source branch objects, with their stores. -/
def answers {n : Nat} (body : Body n) (worlds : List (Fin (2 ^ n))) :
    AnswerCollection.AnswerSpace mkeys [] () D :=
  ⟨(completed body worlds : Multiset SourceBranch), fun branch member =>
    completed_ready body worlds branch (Multiset.mem_coe.mp member)⟩

theorem collector_reifies {n : Nat} (body : Body n) (worlds : List (Fin (2 ^ n))) (shared : SourceWorld) :
    AnswerCollection.reify (finishedState body worlds shared) (finishedState_valid body worlds shared) =
      some (answers body worlds) := by
  simp [AnswerCollection.reify, finishedState, answers]

/-- The observer reads a retained trace occurrence. It never treats equal
Boolean outputs as identical stochastic executions. -/
noncomputable def observe {n : Nat} (body : Body n) (probability : Fin n → ℝ≥0∞)
    (query : Bool → Bool) (branch : SourceBranch) : ℝ≥0∞ := by
  classical
  exact ∑ world : Fin (2 ^ n), if terminal world = branch then
    assignmentWeight probability (worldAssignmentEquiv n world) *
      body.density query (worldAssignmentEquiv n world) else 0

theorem observe_terminal {n : Nat} (body : Body n) (probability : Fin n → ℝ≥0∞)
    (query : Bool → Bool) (world : Fin (2 ^ n)) :
    observe body probability query (terminal world) =
      assignmentWeight probability (worldAssignmentEquiv n world) *
        body.density query (worldAssignmentEquiv n world) := by
  classical
  simp only [observe, terminal_injective.eq_iff]
  simp

/-- The additive fold of source answers equals the finite tape sum. -/
theorem completed_fold {n : Nat} (body : Body n) (probability : Fin n → ℝ≥0∞)
    (query : Bool → Bool) (worlds : List (Fin (2 ^ n))) :
    ((completed body worlds).map (observe body probability query)).sum =
      (worlds.map fun world => assignmentWeight probability (worldAssignmentEquiv n world) *
        body.density query (worldAssignmentEquiv n world)).sum := by
  induction worlds with
  | nil => rfl
  | cons world worlds ih =>
    unfold completed
    cases h : body.result (worldAssignmentEquiv n world) with
    | none => simpa [h, Body.density] using ih
    | some value => simp [observe_terminal, ih]

/-- The real constrained answer collector's monoidal fold computes BDD mass.
`Multiplicative` selects the additive mass monoid without changing the collector. -/
theorem answer_fold_eq_compiled {n : Nat} (body : Body n) (probability : Fin n → ℝ≥0∞)
    (bounded : ∀ i, probability i ≤ 1) (query : Bool → Bool) :
    Multiplicative.toAdd ((answers body (List.ofFn (fun world : Fin (2 ^ n) => world))).fold
      (fun branch => Multiplicative.ofAdd (observe body probability query branch))) =
        (WeightedSourcePrograms.compile body query).count probability := by
  rw [compile_countWorld body probability bounded]
  rw [countWorld_joint]
  change ((completed body (List.ofFn (fun world : Fin (2 ^ n) => world))).map
    (observe body probability query)).sum = body.mass probability query
  rw [completed_fold]
  simp only [List.map_ofFn, List.sum_ofFn]
  unfold Body.mass
  exact Equiv.sum_comp (worldAssignmentEquiv n) (fun state : Fin n → Bool =>
    assignmentWeight probability state * body.density query state)

noncomputable def posteriorFromAnswers {n : Nat} (body : Body n) (probability : Fin n → ℝ≥0∞)
    (query : Bool → Bool) : Option ℝ≥0∞ :=
  let rows := answers body (List.ofFn (fun world : Fin (2 ^ n) => world))
  let mass := fun predicate => Multiplicative.toAdd
    (rows.fold (fun branch => Multiplicative.ofAdd (observe body probability predicate branch)))
  if mass (fun _ => true) = 0 ∨ mass (fun _ => true) = ⊤ then none
  else some (mass query / mass (fun _ => true))

/-- Actual collected numerator and denominator yield the same partial
posterior as the independently defined program semantics and BDD circuit. -/
theorem posteriorFromAnswers_eq {n : Nat} (body : Body n) (probability : Fin n → ℝ≥0∞)
    (bounded : ∀ i, probability i ≤ 1) (query : Bool → Bool) :
    posteriorFromAnswers body probability query = body.posterior probability query := by
  simp only [posteriorFromAnswers, answer_fold_eq_compiled body probability bounded,
    compile_mass body probability bounded, Body.posterior]

/-- Before the producer is drained the actual collector refuses a closed answer space. -/
theorem pending_not_empty {n : Nat} (body : Body n) (worlds : List (Fin (2 ^ n))) (shared : SourceWorld) :
    AnswerCollection.reify
      (AnswerCollection.State.initial ⟨shared, {start (sourceFrom body worlds)}⟩)
      (AnswerCollection.State.initial_valid _) = none := by
  apply AnswerCollection.reify_none_of_pending
  exact Multiset.mem_singleton_self _

#print axioms source_runs
#print axioms collector_runs
#print axioms answer_fold_eq_compiled
#print axioms posteriorFromAnswers_eq

end Mettapedia.PLN.WorldModel.WeightedSourceExecution
