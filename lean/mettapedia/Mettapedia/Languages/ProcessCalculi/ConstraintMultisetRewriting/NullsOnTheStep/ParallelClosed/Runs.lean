import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.StepSource

/-!
# Reachability under a program is reachability by the step's own runs

The reachable configurations of `ProgramStep` are exactly the ends of the runs of the first-order
step (`Interface.Step.Run` of `AnnotatedRuns.firstOrder`) whose firings all have rules of the
program (`reaches_iff_run`). So "success is reachable", "no run shows success" and the existence of
runs are statements about the step's runs, not about a separate relation (`succeeds_iff_run`,
`blocked_on_runs`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed

section General

variable {T : Type*} {S : Type*} {O : Type*} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T) (rules : RuleInstance T → Prop)

/-- A run of the first-order step whose firings all have rules of the program. -/
def ProgramRun {C : Configuration T O} (r : (AnnotatedRuns.firstOrder A label).toStep.Run C) :
    Prop :=
  ∀ x ∈ r.word, rules x.2.rule

/-- **The reachable configurations under a program are the ends of the program's runs.** -/
theorem reaches_iff_run (C D : Configuration T O) :
    Relation.ReflTransGen (ProgramStep A label rules) C D ↔
      ∃ r : (AnnotatedRuns.firstOrder A label).toStep.Run C, ProgramRun A label rules r ∧
        r.last = D := by
  constructor
  · intro reaches
    induction reaches using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨.nil D, fun _ member => absurd member List.not_mem_nil, rfl⟩
    | head step _ ih =>
        obtain ⟨f, inProgram, admitted, rfl⟩ := step
        obtain ⟨r, onlyProgram, last⟩ := ih
        refine ⟨.cons f admitted r, ?_, last⟩
        intro x member
        rcases List.mem_cons.mp member with rfl | later
        · exact inProgram
        · exact onlyProgram x later
  · rintro ⟨r, onlyProgram, rfl⟩
    induction r with
    | nil => exact .refl
    | cons f admitted rest ih =>
        exact Relation.ReflTransGen.head ⟨f, onlyProgram ⟨_, f⟩ List.mem_cons_self, admitted, rfl⟩
          (ih fun x member => onlyProgram x (List.mem_cons_of_mem _ member))

/-- **Reachable success is success at the end of a run of the program.** -/
theorem succeeds_iff_run (row : T → Prop) (C : Configuration T O) :
    (stepCalculus A label rules row).Succeeds C ↔
      ∃ r : (AnnotatedRuns.firstOrder A label).toStep.Run C, ProgramRun A label rules r ∧
        Shows label row r.last := by
  constructor
  · rintro ⟨D, reaches, shows⟩
    obtain ⟨r, onlyProgram, last⟩ := (reaches_iff_run A label rules C D).mp reaches
    exact ⟨r, onlyProgram, last ▸ shows⟩
  · rintro ⟨r, onlyProgram, shows⟩
    exact ⟨r.last, (reaches_iff_run A label rules C r.last).mpr ⟨r, onlyProgram, rfl⟩, shows⟩

end General

/-- **The blocked situation, read on runs**: beside the store holding `U`, a run of the program that
fires exists (`tick`), and no run of the program ends in a store holding `T`. -/
theorem blocked_on_runs :
    (∃ r : (AnnotatedRuns.firstOrder NamesOnTheStep.IssuingControls.ground
        (Prod.fst : NamesOnTheStep.IssuingControls.Occ → NamesOnTheStep.Expr)).toStep.Run
          (Composition.unionOf alone blocker),
        ProgramRun _ _ program r ∧ r.word ≠ []) ∧
      ∀ r : (AnnotatedRuns.firstOrder NamesOnTheStep.IssuingControls.ground
          (Prod.fst : NamesOnTheStep.IssuingControls.Occ → NamesOnTheStep.Expr)).toStep.Run
            (Composition.unionOf alone blocker),
        ProgramRun _ _ program r →
          ¬ Shows Prod.fst (· = NamesOnTheStep.IssuingControls.factT) r.last := by
  refine ⟨?_, fun r onlyProgram shows =>
    beside_blocked ((succeeds_iff_run _ _ program _ _).mpr ⟨r, onlyProgram, shows⟩)⟩
  obtain ⟨⟨f, inProgram, admitted, _⟩, _⟩ := tick_runs_beside
  refine ⟨.cons f admitted (.nil _), fun x member => ?_, by simp [Interface.Step.Run.word]⟩
  simp only [Interface.Step.Run.word, List.mem_cons, List.not_mem_nil, or_false] at member
  subst member
  exact inProgram

#print axioms reaches_iff_run
#print axioms succeeds_iff_run
#print axioms blocked_on_runs

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed
