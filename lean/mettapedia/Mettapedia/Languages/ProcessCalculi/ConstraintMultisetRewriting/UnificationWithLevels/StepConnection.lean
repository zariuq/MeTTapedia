import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.PatternSolverControls

/-!
# Postponed constraints in the step's knowledge, and what admission's `solvable` means

**Where postponed constraints sit.** A firing's information is a store at its target frame. A
solver run from it ends at a frame `m` with a settlement `σ` and a residual `R`. A step that settles
along `σ` and keeps the transported information as knowledge (the `Standard` profile:
knowledge = `applyStore settle information`) then has, as knowledge,

* a store **equivalent to the residual**, for every literal solver (`Solver.Reaches.literal`): the
  postponed equations are the knowledge, and no further bookkeeping is needed; the solver of
  cumulative codes is literal (`CumulativeCodes.solver_literal`);
* an exact transition from the information (`knowledge_keeps_solutions`): beyond the core's own
  law (a solution after the firing pulls back), **no solution of the information is lost** along
  the settlement. For a settlement with transported knowledge this is the same as every solution
  of the information factoring through it (`exact_applyStore_iff`).

Level constraints are equations of the same store (`CumulativeCodes.levelEquation`), so postponed
level constraints sit in the knowledge in the same way (`models_with_level`).

**On the step.** For every `Step.Standard` whose settlement of a firing is the composite of a
literal solver run from the firing's information, the knowledge of the result is equivalent to the
run's residual (`standard_knowledge_residual`, `standard_result_residual`): this is
`knowledge_preparedResult` and `Solver.Reaches.literal` together. Such steps exist for every
solver: the **settled step** (`Settled.step`) tells equations and settles along a run of the solver
that has stopped, keeping the transported information as knowledge; for a literal solver its
knowledge after a firing is the run's residual (`Settled.knowledge_is_residual`). Controls, with
the solver of cumulative codes: telling `X par ≐ arr (V par) gnd` settles along the solving run and
leaves knowledge equivalent to the empty residual, which the information itself is not
(`SettledControls.solved_knowledge`); telling the cross store settles along the stopped run and
leaves the postponed cross equation as the knowledge (`SettledControls.cross_knowledge`).

**What `solvable` in admission means.** Preparation asks `Solvable information`, a semantic
proposition the core never computes. With an exact run it is `Solvable` of the residual
(`prepares_iff_residual`). A run therefore gives one of three verdicts (`Verdict.ofRun`):

* solved (`Verdict.solved`): the solvability conjunct holds, with a principal answer; admission
  still asks the shapes, the enabling and the guards;
* refuted: not prepared, hence not admitted, with the reason;
* postponed: **undecided**; the residual's solvability is still the question.

The third verdict is not a default for either of the others: a postponed run can start from a
solvable store (`undecided_solvable`) or from an unsolvable one (`undecided_unsolvable`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

open Interface
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uOcc uS uF

section General

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
variable {X : Frames Tm Hom}

theorem agree_assoc {a b c d : Obj} (h : Hom a b) (f : Hom b c) (g : Hom c d) :
    Agree X (X.comp g (X.comp f h)) (X.comp (X.comp g f) h) := by
  intro t
  rw [X.act_comp, X.act_comp, X.act_comp, X.act_comp]
  exact (X.equivalence d).refl _

/-- **With transported knowledge, exactness is "no solution lost".** -/
theorem exact_applyStore_iff {a m : Obj} (S : EquationStore (Tm a)) (σ : Hom a m) :
    Exact X S σ (X.applyStore σ S) ↔
      ∀ (b : Obj) (f : Hom a b), X.Models f S → ∃ g : Hom m b, Agree X f (X.comp g σ) := by
  constructor
  · intro exact b f solved
    obtain ⟨g, fg, _⟩ := (exact b f).mp solved
    exact ⟨g, fg⟩
  · intro factors b f
    constructor
    · intro solved
      obtain ⟨g, fg⟩ := factors b f solved
      refine ⟨g, fg, ?_⟩
      rw [Frames.models_applyStore]
      exact (models_of_agree fg S).mp solved
    · rintro ⟨g, fg, solvedG⟩
      rw [Frames.models_applyStore] at solvedG
      exact (models_of_agree fg S).mpr solvedG

/-- A solver is **literal** when each residual is its store transported along the transition. -/
def Solver.Literal (P : Solver X) : Prop :=
  ∀ {a m : Obj} {S : EquationStore (Tm a)} {σ : Hom a m} {S' : EquationStore (Tm m)},
    P.Step S m σ S' → X.Equivalent (X.applyStore σ S) S'

/-- **For a literal solver, the transported store is the residual**, along every run. -/
theorem Solver.Reaches.literal {P : Solver X} (lit : P.Literal) {a m : Obj}
    {S : EquationStore (Tm a)} {σ : Hom a m} {R : EquationStore (Tm m)} (run : P.Reaches S m σ R) :
    X.Equivalent (X.applyStore σ S) R := by
  induction run with
  | refl S =>
      rw [Frames.applyStore_id]
      exact fun _ _ => Iff.rfl
  | @step a m n S σ S' τ S'' first _ ih =>
      intro b g
      rw [Frames.models_applyStore, models_of_agree (agree_assoc σ τ g) S,
        ← Frames.models_applyStore, lit first b (X.comp g τ), ← Frames.models_applyStore]
      exact ih b g

/-- **Postponed constraints are the knowledge.** For a literal solver run from the information,
the transported information along the run's settlement keeps every solution and is equivalent to
the residual. -/
theorem knowledge_keeps_solutions {P : Solver X} (lit : P.Literal) {a m : Obj}
    {S : EquationStore (Tm a)} {σ : Hom a m} {R : EquationStore (Tm m)} (run : P.Reaches S m σ R) :
    Exact X S σ (X.applyStore σ S) ∧ X.Equivalent (X.applyStore σ S) R := by
  refine ⟨(exact_applyStore_iff S σ).mpr fun b f solved => ?_, run.literal lit⟩
  obtain ⟨g, fg, _⟩ := (run.exact b f).mp solved
  exact ⟨g, fg⟩

/-- **What `solvable` in preparation means with an exact run**: the residual is solvable. -/
theorem prepares_iff_residual {O : Type uOcc} [DecidableEq O] {State : Type uS}
    {Firing : State → Type uF} (E : EffectCore X O State Firing) {s : State} (f : Firing s)
    {m : Obj} {σ : Hom (E.target f) m} {R : EquationStore (Tm m)}
    (exact : Exact X (E.information f) σ R) :
    E.Prepares f ↔ E.Shapes f ∧
      Enabled (fun _ : O => ()) (E.present s) ((E.selection f).commit (T := Unit)) ∧
        X.Solvable R := by
  constructor
  · rintro ⟨shapes, enabled, solvable⟩
    exact ⟨shapes, enabled, exact.solvable_iff.mp solvable⟩
  · rintro ⟨shapes, enabled, solvable⟩
    exact ⟨shapes, enabled, exact.solvable_iff.mpr solvable⟩

/-- **On a standard step that settles along a solver run, the knowledge after a firing is the
run's residual.** A `Step.Standard` keeps the information transported along its settlement as the
knowledge of the result (`knowledge_preparedResult`). When that settlement is the composite of a
run of a literal solver from the firing's information, the knowledge is equivalent to the run's
residual (`Solver.Reaches.literal`), and the solutions of the information are exactly the
composites through the settlement of the solutions of the knowledge. -/
theorem standard_knowledge_residual {O : Type uOcc} [DecidableEq O] {State : Type uS}
    {Firing : State → Type uF} (Q : Interface.Step.Standard X O State Firing) {s : State}
    (f : Firing s) (p : Q.Prepares f) {P : Solver X} (lit : P.Literal)
    {R : EquationStore (Tm (Q.frame (Q.preparedResult f p)))}
    (run : P.Reaches (Q.information f) _ (Q.preparedSettle f p) R) :
    X.Equivalent (Q.knowledge (Q.preparedResult f p)) R ∧
      Exact X (Q.information f) (Q.preparedSettle f p) (Q.knowledge (Q.preparedResult f p)) := by
  rw [Q.knowledge_preparedResult f p]
  exact ⟨run.literal lit, (knowledge_keeps_solutions lit run).1⟩

/-- **The same for an admitted firing**: the knowledge of its result is the residual of a literal
run along its settlement. -/
theorem standard_result_residual {O : Type uOcc} [DecidableEq O] {State : Type uS}
    {Firing : State → Type uF} (Q : Interface.Step.Standard X O State Firing) {s : State}
    (f : Firing s) (admitted : Q.Admits f) {P : Solver X} (lit : P.Literal)
    {R : EquationStore (Tm (Q.frame (Q.result f admitted)))}
    (run : P.Reaches (Q.information f) _ (Q.settle f admitted) R) :
    X.Equivalent (Q.knowledge (Q.result f admitted)) R :=
  (standard_knowledge_residual Q f (Q.prepares admitted) lit run).1

/-! ## The settled step: a step whose settlement is a solver run -/

namespace Settled

/-- A firing of the settled step: equations told at the state's frame, and **a run of the solver**
from the knowledge with them. -/
structure Firing (P : Solver X) (s : (a : Obj) × EquationStore (Tm a)) where
  told : EquationStore (Tm s.1)
  frame : Obj
  settle : Hom s.1 frame
  residual : EquationStore (Tm frame)
  run : P.Reaches (s.2 ++ told) frame settle residual

/-- **The settled step** of a solver. A state is knowledge at a frame. A firing tells equations at
the state's frame and carries a run of the solver from the knowledge with them; it is shaped when
that run has stopped (`Solver.Stopped`: no transition and no refutation applies to its residual).
Its result is at the run's frame and keeps the information transported along the run's settlement
as knowledge (the `Standard` profile). It takes and makes no occurrences, and its guard is the
empty store's, which every solution satisfies. -/
def step (P : Solver X) :
    Interface.Step.Standard X Empty ((a : Obj) × EquationStore (Tm a)) (Firing P) where
  frame s := s.1
  knowledge s := s.2
  present _ := ∅
  selection _ := ⟨[], [], []⟩
  target {s} _ := s.1
  extension {s} _ := X.id s.1
  information {s} f := s.2 ++ f.told
  transported {s} _ e member := by
    show (X.act (X.id s.1) e.1, X.act (X.id s.1) e.2) ∈ s.2 ++ _
    rw [X.act_id, X.act_id]
    exact List.mem_append_left _ member
  Shapes f := P.Stopped f.residual
  Holds _ _ σ := X.Models σ []
  Admits {s} f := P.Stopped f.residual ∧
    Enabled (fun _ : Empty => ()) (∅ : Finset Empty)
      ((⟨[], [], []⟩ : Selection Empty).commit (T := Unit)) ∧
    X.Solvable (s.2 ++ f.told) ∧ X.Entails (s.2 ++ f.told) (fun _ σ => X.Models σ [])
  admits_iff _ := Iff.rfl
  preparedResult {s} f _ := ⟨f.frame, X.applyStore f.settle (s.2 ++ f.told)⟩
  present_preparedResult _ _ := by simp [fire, Selection.commit]
  preparedSettle f _ := f.settle
  knowledge_preparedResult _ _ := rfl

/-- The settled step takes, keeps and makes nothing, so its selection is always enabled. -/
theorem enabled : Enabled (fun _ : Empty => ()) (∅ : Finset Empty)
    ((⟨[], [], []⟩ : Selection Empty).commit (T := Unit)) := by
  constructor <;> simp [Selection.commit]

/-- **A firing of the settled step is admitted exactly when its run has stopped and the
information is solvable.** -/
theorem admits_iff (P : Solver X) {s : (a : Obj) × EquationStore (Tm a)} (f : Firing P s) :
    (step P).Admits f ↔ P.Stopped f.residual ∧ X.Solvable (s.2 ++ f.told) :=
  ⟨fun admitted => ⟨admitted.1, admitted.2.2.1⟩,
    fun ⟨stopped, solvable⟩ => ⟨stopped, enabled, solvable, fun _ σ _ => Frames.models_nil σ⟩⟩

/-- **On the settled step, postponed equations are the knowledge.** For a literal solver, the
knowledge after an admitted firing is equivalent to the residual of the firing's run, and that
residual has stopped. -/
theorem knowledge_is_residual {P : Solver X} (lit : P.Literal)
    {s : (a : Obj) × EquationStore (Tm a)} (f : Firing P s) (admitted : (step P).Admits f) :
    X.Equivalent ((step P).knowledge ((step P).result f admitted)) f.residual ∧
      P.Stopped f.residual :=
  ⟨standard_result_residual (step P) f admitted lit f.run, admitted.1⟩

end Settled

variable (X) in
/-- **What a run tells admission's `solvable`.** -/
inductive Verdict {a : Obj} (S : EquationStore (Tm a)) : Type (max uO uT uH)
  /-- Solved: a principal answer, so the store is solvable. This is the solvability conjunct of
  preparation; admission still asks the shapes, the enabling and the guards. -/
  | solved {m : Obj} (σ : Hom a m) (principal : X.Principal S σ)
  /-- Refuted: no solution, with the reason. -/
  | refused (reason : Reason) (none : ¬ X.Solvable S)
  /-- Postponed: solvable exactly when the residual is; the run decides neither. -/
  | undecided {m : Obj} (σ : Hom a m) (R : EquationStore (Tm m)) (exact : Exact X S σ R)

/-- The verdict at the end of a run. -/
def Verdict.ofRun {P : Solver X} {a m : Obj} {S : EquationStore (Tm a)} {σ : Hom a m}
    {R : EquationStore (Tm m)} (run : P.Reaches S m σ R)
    (refutation : Option {r : Reason // P.Refutes R r}) [Decidable (R = [])] : Verdict X S :=
  match refutation with
  | some ⟨r, h⟩ => .refused r (refuted_none run h)
  | none =>
      if empty : R = [] then .solved σ (solved_principal (empty ▸ run))
      else .undecided σ R run.exact

theorem Verdict.solved_solvable {a m : Obj} {S : EquationStore (Tm a)} {σ : Hom a m}
    (principal : X.Principal S σ) : X.Solvable S :=
  principal.solvable

theorem Verdict.undecided_iff {a m : Obj} {S : EquationStore (Tm a)} {σ : Hom a m}
    {R : EquationStore (Tm m)} (exact : Exact X S σ R) : X.Solvable S ↔ X.Solvable R :=
  exact.solvable_iff

end General

/-! ## The solver of cumulative codes -/

namespace CumulativeCodes

variable {v : Nat → Nat}

theorem solve_fixes {X : Nat} {t : Tm} (fresh : Tm.occurs X t = false) :
    Tm.act (Function.update Tm.idA X t) t = t := by
  rw [Tm.act_congr_occurs (σ := Function.update Tm.idA X t) (τ := Tm.idA)
    (fun V hV => by rw [Function.update_of_ne hV]) t fresh, Tm.act_id]

/-- **The solver of cumulative codes is literal.** -/
theorem solver_literal : (solver v).Literal := by
  intro a m S σ S' r
  change Rule v S m σ S' at r
  cases r with
  | delete same =>
      intro b g
      rw [Frames.models_applyStore, ← models_of_agree (agree_comp_id g)]
      exact equivalent_of_exact_id (delete_exact same) b g
  | decompose h h' h₁ h₁' h₂ h₂' =>
      intro b g
      rw [Frames.models_applyStore, ← models_of_agree (agree_comp_id g)]
      exact equivalent_of_exact_id (decompose_exact h h' h₁ h₁' h₂ h₂') b g
  | solveLeft hl fresh hσ =>
      intro b g
      constructor
      · intro solved e he
        exact solved e (List.mem_cons_of_mem _ he)
      · intro solved e he
        rcases List.mem_cons.mp he with rfl | he
        · show Tm.lower v (Tm.act g.1 (Tm.act _ _)) = Tm.lower v (Tm.act g.1 (Tm.act _ _))
          rw [hl, act_app_par, hσ, Function.update_self, solve_fixes fresh]
        · exact solved e he
  | solveRight hr fresh hσ =>
      intro b g
      constructor
      · intro solved e he
        exact solved e (List.mem_cons_of_mem _ he)
      · intro solved e he
        rcases List.mem_cons.mp he with rfl | he
        · show Tm.lower v (Tm.act g.1 (Tm.act _ _)) = Tm.lower v (Tm.act g.1 (Tm.act _ _))
          rw [hr, act_app_par, hσ, Function.update_self, solve_fixes fresh]
        · exact solved e he

/-- **A level constraint in the knowledge** constrains the levels and nothing else. -/
theorem models_with_level {Δ Γ : Ctx} (f : Assign v Δ Γ) (S : EquationStore (Term Δ))
    (c : LevelLe) :
    (frames v).Models f (S ++ [levelEquation c]) ↔ (frames v).Models f S ∧ c.Holds v := by
  rw [Frames.models_append]
  constructor
  · rintro ⟨solved, level⟩
    exact ⟨solved, (solves_levelEquation f c).mp (level _ List.mem_cons_self)⟩
  · rintro ⟨solved, level⟩
    refine ⟨solved, fun e he => ?_⟩
    rw [List.mem_singleton] at he
    subst he
    exact (solves_levelEquation f c).mpr level

namespace Cross

/-- `sort a`. -/
def sortA : Term ctx := ⟨.sort a, .sort _⟩

/-- **Undecided and solvable**: where `a = 0` and `b = 1` the cross store is postponed and
solvable. -/
theorem undecided_solvable :
    (solver (fun i => i)).Stopped store ∧ (frames (fun i => i)).Solvable store :=
  ⟨cross_stopped (by decide), solvable _⟩

/-- **Undecided and unsolvable**: with `Y par ≐ sort a` added, the store is still postponed at its
cross equation, and it has no solution: `X` would have to be `sort a`, which is not a code of
`Sort a`. -/
theorem undecided_unsolvable :
    (solver (fun i => i)).Stopped [(X, Y), (Y, sortA)] ∧
      ¬ (frames (fun i => i)).Solvable [(X, Y), (Y, sortA)] := by
  refine ⟨cross_stopped_cons (by decide) _, ?_⟩
  rintro ⟨Γ, f, solved⟩
  have first : Tm.lower (fun i => i) (Tm.act f.1 X.1) = Tm.lower (fun i => i) (Tm.act f.1 Y.1) :=
    solved (X, Y) List.mem_cons_self
  have second : Tm.lower (fun i => i) (Tm.act f.1 Y.1) =
      Tm.lower (fun i => i) (Tm.act f.1 sortA.1) :=
    solved (Y, sortA) (List.mem_cons_of_mem _ List.mem_cons_self)
  have typed := (f.2 0 ⟨a, a⟩ rfl).lower
  have same : Tm.lower (fun i => i) (f.1 0) = .sort (.const 0) := by
    have := first.trans second
    simpa [X, Y, sortA, Tm.act, act_app_par, Tm.lower] using this
  rw [same] at typed
  cases typed with
  | sort h => simp at h

end Cross

/-- The solver of cumulative codes has nothing to do at the empty store. -/
theorem stopped_nil (Δ : Ctx) : (solver v).Stopped ([] : EquationStore (Term Δ)) := by
  refine ⟨fun n τ R' r => ?_, fun reason r => ?_⟩
  · change Rule v [] n τ R' at r
    cases r
  · change Refutes v [] reason at r
    cases r

/-! ### Controls of the settled step -/

namespace SettledControls

/-- Told `X par ≐ arr (V par) gnd` at empty knowledge, the firing settles along the solving run. -/
def solvedFiring (v : Nat → Nat) :
    Settled.Firing (solver v) ⟨SolverControls.ctx, []⟩ where
  told := [(SolverControls.X, SolverControls.target)]
  frame := SolverControls.ctx
  settle := (frames v).comp ((frames v).id SolverControls.ctx) (SolverControls.answer v)
  residual := []
  run := SolverControls.solved_run v

theorem solved_admitted (v : Nat → Nat) : (Settled.step (solver v)).Admits (solvedFiring v) :=
  (Settled.admits_iff (solver v) (solvedFiring v)).mpr
    ⟨stopped_nil _, ⟨_, _, (SolverControls.solved_principal_answer v).sound⟩⟩

/-- **Positive control, solved**: after the firing the knowledge is equivalent to the empty
residual, so the identity solves it; the information told is not solved by the identity. -/
theorem solved_knowledge (v : Nat → Nat) :
    (frames v).Equivalent
        ((Settled.step (solver v)).knowledge
          ((Settled.step (solver v)).result (solvedFiring v) (solved_admitted v)))
        ([] : EquationStore (Term SolverControls.ctx)) ∧
      ¬ (frames v).Models ((frames v).id SolverControls.ctx)
        [(SolverControls.X, SolverControls.target)] := by
  refine ⟨(Settled.knowledge_is_residual solver_literal _ _).1, fun solved => ?_⟩
  have same := solved _ List.mem_cons_self
  change Tm.lower v (Tm.act Tm.idA (.app 0 .par)) =
    Tm.lower v (Tm.act Tm.idA (.arr (.app 1 .par) .gnd)) at same
  rw [Tm.act_id, Tm.act_id] at same
  exact absurd same (by simp [Tm.lower])

/-- Told the cross store at empty knowledge, where `a = 0` and `b = 1`, the firing settles along
the stopped run. -/
def crossFiring : Settled.Firing (solver (fun i => i)) ⟨Cross.ctx, []⟩ where
  told := Cross.store
  frame := Cross.ctx
  settle := (frames (fun i => i)).id Cross.ctx
  residual := Cross.store
  run := .refl _

theorem cross_admitted : (Settled.step (solver (fun i => i))).Admits crossFiring :=
  (Settled.admits_iff (solver (fun i => i)) crossFiring).mpr
    ⟨Cross.cross_stopped (v := fun i => i) (by decide), Cross.solvable (fun i => i)⟩

/-- **Positive control, postponed**: after the firing the knowledge is equivalent to the postponed
cross equation, which is not empty. -/
theorem cross_knowledge :
    (frames (fun i => i)).Equivalent
        ((Settled.step (solver (fun i => i))).knowledge
          ((Settled.step (solver (fun i => i))).result crossFiring cross_admitted)) Cross.store ∧
      Cross.store ≠ [] :=
  ⟨(Settled.knowledge_is_residual solver_literal _ _).1, List.cons_ne_nil _ _⟩

end SettledControls

end CumulativeCodes

#print axioms exact_applyStore_iff
#print axioms Solver.Reaches.literal
#print axioms knowledge_keeps_solutions
#print axioms standard_knowledge_residual
#print axioms standard_result_residual
#print axioms Settled.admits_iff
#print axioms Settled.knowledge_is_residual
#print axioms CumulativeCodes.stopped_nil
#print axioms CumulativeCodes.SettledControls.solved_knowledge
#print axioms CumulativeCodes.SettledControls.cross_knowledge
#print axioms Verdict.solved_solvable
#print axioms prepares_iff_residual
#print axioms CumulativeCodes.solver_literal
#print axioms CumulativeCodes.models_with_level
#print axioms CumulativeCodes.Cross.undecided_solvable
#print axioms CumulativeCodes.Cross.undecided_unsolvable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
