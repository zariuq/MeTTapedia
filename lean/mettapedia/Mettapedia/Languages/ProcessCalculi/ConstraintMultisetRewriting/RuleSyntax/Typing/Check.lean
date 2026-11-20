import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Typing.Programs

/-!
# The check at each firing, and why a well-typed program does not need it

**The checked step** (`checked`) is the step of a program restricted to the firings that pass the
answer check (`AnswerCheck`: at every solution of the firing's information, each answer has the type of
the row it answers). It is the per-firing typing premise for answers.

* **Checking only refuses** (`checked_le`): every transition of the checked step is a transition of the
  step, to the same state.
* **The check is exact** (`answerCheck_iff_result_wellTyped`): from a well-typed state, an admitted firing
  passes the check exactly when its result is well typed at the retyping. So it refuses only firings
  whose results would be ill typed.
* **The check keeps every program typed** (`checked_reach_wellTyped`): along every run of the checked
  step of any program, well typed or not, every state is well typed at the typing carried along the
  run.
* **For a well-typed program the check refuses nothing** (`checked_succ_iff`, `checked_reach_iff`): the
  checked step and the step have the same transitions and the same runs, from every state.

So the judgment removes refusals and changes nothing else.

**Controls.** In the rigid package, where the program is not well typed, the step admits the firing of
`appendNil` on the closed call, the check refuses it, and the state the step reaches is ill typed at
the retyping (`rigid_check_refuses`). Where addition computes, the checked step has the whole run
(`declared_checked_run`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Typing

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface (Frames)
open Interface.DependentFull (Helpers)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open Dependent (Terms helperExtensions)

variable {Head : Type} {rules : Rules Head}

/-- **The state's step, read back**: from the answer at its expected type and the taken row at its
expected type, the answer at the taken row's type. -/
theorem typeEq_back {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L)
    {Γ Δ Θ : Context rules} (w : Δ ⟶ Γ) (σ : Θ ⟶ Δ) {X : Tm Head Θ.arity}
    {B D : TypeOver Γ} (answer : TypeEq rules Θ.raw X ((D.reindex w).reindex σ).code)
    (before : TypeEq rules Θ.raw (B.reindex (σ ≫ w)).code (D.reindex (σ ≫ w)).code) :
    TypeEq rules Θ.raw X ((B.reindex w).reindex σ).code := by
  rw [← TypeOver.reindex_comp] at answer
  rw [← TypeOver.reindex_comp]
  exact answer.trans levels before.symm

section Checked

variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L) {O : Type} [DecidableEq O]
  (P : Program (Terms rules)) (answers : Rule (Terms rules) → List (Option ℕ))

/-- **The checked step**: the step of the program, admitting only the firings that pass the answer
check. -/
def checked : Interface.Step (frames levels) O (State (Terms rules) O)
    (fun s => Firing O (helperExtensions (rules := rules)) P s.frame) :=
  Spaces.restrict (step (frames levels) O helperExtensions P).toStep
    (fun {_} f => AnswerCheck levels f (answers f.rule))

variable {levels P answers}

theorem checked_admits_iff {s : State (Terms rules) O}
    (f : Firing O (helperExtensions (rules := rules)) P s.frame) :
    (checked levels P answers).Admits (s := s) f ↔
      (step (frames levels) O helperExtensions P).Admits (s := s) f ∧
        AnswerCheck levels f (answers f.rule) :=
  Iff.rfl

/-- **Checking only refuses**: every transition of the checked step is a transition of the step, to the
same state. -/
theorem checked_le {s t : State (Terms rules) O} (succ : Succ (checked levels P answers) s t) :
    Succ (step (frames levels) O helperExtensions P).toStep s t := by
  obtain ⟨f, admitted, reached⟩ := succ
  exact ⟨f, admitted.1, reached⟩

/-- **The check is exact**: from a well-typed state, an admitted firing passes the answer check exactly
when its result is well typed at the retyping. -/
theorem answerCheck_iff_result_wellTyped {s : State (Terms rules) O} {Δ : O → TypeOver s.frame}
    {f : Firing O (helperExtensions (rules := rules)) P s.frame} {a : List (Option ℕ)}
    (admitted : (step (frames levels) O helperExtensions P).Admits (s := s) f)
    (state : WellTypedState levels s Δ) :
    AnswerCheck levels f a ↔
      WellTypedState levels (f.result (frames levels) s) (retype levels f a Δ) := by
  refine ⟨fun check => result_wellTyped_of_check levels admitted check state, fun typed => ?_⟩
  obtain ⟨⟨-, -, madeNodup, -, -, produceLength, -⟩, enabled, -, -⟩ := admitted
  intro j oi t hAnswer rowJ Θ σ solved
  have lengths : (f.opened (frames levels)).produce.length = f.selection.made.length := by
    simp only [Firing.opened, RuleInstance.map, List.length_map]
    exact produceLength
  obtain ⟨o, madeJ⟩ := exists_getElem?_of_length lengths rowJ
  obtain ⟨i, -, takenI⟩ := answerOf_eq_some.mp hAnswer
  have present : o ∈ (f.result (frames levels) s).present :=
    mem_fire.mpr (Or.inr (List.mem_toFinset.mpr (List.mem_of_getElem? madeJ)))
  have label : (f.result (frames levels) s).label o = t :=
    relabel_getElem? _ _ _ j madeNodup madeJ rowJ
  have expected := retype_answer levels f a Δ madeNodup madeJ rowJ hAnswer
  have atResult := typed o present Θ σ solved
  rw [label, expected] at atResult
  have takenPresent : oi ∈ s.present :=
    enabled.taken_subset (List.mem_toFinset.mpr (List.mem_of_getElem? takenI))
  have before : TypeEq rules Θ.raw ((s.label oi).1.reindex (σ ≫ f.ext.weaken)).code
      ((Δ oi).reindex (σ ≫ f.ext.weaken)).code :=
    state oi takenPresent Θ (σ ≫ f.ext.weaken) (f.knowledge_solved solved)
  exact typeEq_back levels f.ext.weaken σ (B := (s.label oi).1) (D := Δ oi) atResult before

/-! ## The check keeps every program's runs typed -/

variable (levels P answers) in
/-- **Runs of the checked step that carry a typing.** -/
inductive CheckedReach :
    (s : State (Terms rules) O) → (O → TypeOver s.frame) → (t : State (Terms rules) O) →
      (O → TypeOver t.frame) → Prop
  | refl (s : State (Terms rules) O) (Δ : O → TypeOver s.frame) : CheckedReach s Δ s Δ
  | head {s : State (Terms rules) O} {Δ : O → TypeOver s.frame} {t : State (Terms rules) O}
      {Δt : O → TypeOver t.frame} (f : Firing O (helperExtensions (rules := rules)) P s.frame)
      (admitted : (checked levels P answers).Admits (s := s) f) :
      CheckedReach (f.result (frames levels) s) (retype levels f (answers f.rule) Δ) t Δt →
      CheckedReach s Δ t Δt

/-- **Along a checked typed run of any program, every state is well typed.** -/
theorem CheckedReach.wellTyped {s t : State (Terms rules) O} {Δ : O → TypeOver s.frame}
    {Δt : O → TypeOver t.frame} (reach : CheckedReach levels P answers s Δ t Δt)
    (state : WellTypedState levels s Δ) : WellTypedState levels t Δt := by
  induction reach with
  | refl => exact state
  | head f admitted _ rest => exact rest (result_wellTyped_of_check levels admitted.1 admitted.2 state)

/-- **Every run of the checked step carries every initial typing.** -/
theorem checkedReach_of_reach {s t : State (Terms rules) O}
    (reach : Relation.ReflTransGen (Succ (checked levels P answers)) s t) :
    ∀ Δ : O → TypeOver s.frame, ∃ Δt : O → TypeOver t.frame, CheckedReach levels P answers s Δ t Δt := by
  induction reach using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun Δ => ⟨Δ, .refl _ _⟩
  | head first _ rest =>
      obtain ⟨f, admitted, rfl⟩ := first
      intro Δ
      obtain ⟨Δt, carried⟩ := rest (retype levels f (answers f.rule) Δ)
      exact ⟨Δt, .head f admitted carried⟩

/-- **The check keeps every program typed**: from a well-typed state, every state that the checked step
of any program reaches is well typed at the typing carried along the run. -/
theorem checked_reach_wellTyped {s t : State (Terms rules) O} {Δ : O → TypeOver s.frame}
    (state : WellTypedState levels s Δ)
    (reach : Relation.ReflTransGen (Succ (checked levels P answers)) s t) :
    ∃ Δt : O → TypeOver t.frame, CheckedReach levels P answers s Δ t Δt ∧ WellTypedState levels t Δt := by
  obtain ⟨Δt, carried⟩ := checkedReach_of_reach reach Δ
  exact ⟨Δt, carried, carried.wellTyped state⟩

/-! ## For a well-typed program the check refuses nothing -/

/-- **The checked step and the step have the same transitions**, from every state, for a well-typed
program. -/
theorem checked_succ_iff (typed : WellTypedProgram levels P answers) {s t : State (Terms rules) O} :
    Succ (checked levels P answers) s t ↔ Succ (step (frames levels) O helperExtensions P).toStep s t := by
  refine ⟨checked_le, ?_⟩
  rintro ⟨f, admitted, reached⟩
  exact ⟨f, ⟨admitted, answerCheck_of_wellTyped levels (typed f.rule f.member) admitted⟩, reached⟩

/-- **... hence the same runs.** -/
theorem checked_reach_iff (typed : WellTypedProgram levels P answers) {s t : State (Terms rules) O} :
    Relation.ReflTransGen (Succ (checked levels P answers)) s t ↔
      Relation.ReflTransGen (Succ (step (frames levels) O helperExtensions P).toStep) s t :=
  ⟨fun reach => Relation.ReflTransGen.mono (fun _ _ => checked_le) _ _ reach,
    fun reach => Relation.ReflTransGen.mono (fun _ _ succ => (checked_succ_iff typed).mpr succ) _ _ reach⟩

end Checked

/-! ## Controls -/

section Controls

open Programs

/-- **Control: an ill-typed program.** In the rigid package the step admits the firing of `appendNil` on
the closed call, the answer check refuses it, and the state the step reaches is ill typed at the
retyping. -/
theorem rigid_check_refuses :
    (step (frames rigid.levels) ℕ helperExtensions (program rigid)).Admits (s := start rigid)
        (firstFiring rigid) ∧
      ¬ (checked rigid.levels (program rigid) (answers rigid)).Admits (s := start rigid)
        (firstFiring rigid) ∧
      Succ (step (frames rigid.levels) ℕ helperExtensions (program rigid)).toStep (start rigid)
        (firstResult rigid) ∧
      ¬ WellTypedState rigid.levels (firstResult rigid)
        (retype rigid.levels (firstFiring rigid) [some 0] (fun o => ((start rigid).label o).1)) := by
  refine ⟨firstFiring_admitted rigid, fun admitted => ?_,
    ⟨firstFiring rigid, firstFiring_admitted rigid, rfl⟩, rigid_result_not_wellTyped.2⟩
  have check : AnswerCheck rigid.levels (firstFiring rigid) (answers rigid (firstFiring rigid).rule) :=
    admitted.2
  have answersEq : answers rigid (firstFiring rigid).rule = [some 0] := answers_appendNil rigid
  rw [answersEq] at check
  have atSolution :=
    check 0 0 _ rfl rfl (empty rigid.R) (firstSolution rigid) (firstSolution_solves rigid)
  exact rigid_vec_not_typeEq atSolution

/-- **Where addition computes, the checked step has the whole run.** -/
theorem declared_checked_run :
    Relation.ReflTransGen (Succ (checked declared.levels (program declared) (answers declared)))
      (start declared) (secondResult declared) :=
  (checked_reach_iff declared_wellTyped).mpr (run declared)

end Controls

#print axioms checked_le
#print axioms answerCheck_iff_result_wellTyped
#print axioms CheckedReach.wellTyped
#print axioms checkedReach_of_reach
#print axioms checked_reach_wellTyped
#print axioms checked_succ_iff
#print axioms checked_reach_iff
#print axioms rigid_check_refuses
#print axioms declared_checked_run

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Typing
