import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Calculi
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.AbsenceNotCompositional

/-!
# The step under a program, as a calculus with a parallel composition

## The calculus

* **The first-order step under a program** (`ProgramStep A label program`): a firing of the
  first-order step (`AnnotatedRuns.firstOrder`) whose rule the program holds, admitted at `C`,
  leads to its result.
* **Parallel composition** is the tree's union of configurations (`Composition.unionOf`: both
  knowledges, the union of the stores), with its side condition (`Composable`): the stores are
  disjoint, and the two knowledges are solvable together. That is less than
  `Composition.positive_admission_monotone` needs, which is a solution of the firing's own
  information (the knowledge it fires at, its take and read equations and its tells) together with
  the neighbour's knowledge. Over ground terms the two coincide; over first-order terms a firing with
  no check is refused beside a composable neighbour whose knowledge constrains an unknown the firing
  tells (`PositiveTell.composable_not_monotone`). Without joint solvability of the two knowledges,
  even a firing that only makes is refused beside (`Composition.Controls.makeX_refused_beside`, on a
  pair that is not composable).
* **Success** (`Shows label row`): a row satisfying `row` is present. Reachable success is a weak
  barb.

`stepCalculus` bundles these, with equality as the static equivalence.

## The blocked situation, along every run

`never_succeeds_of_blocker`, over ground terms and for every program: if no rule of the program
takes a row `u`, and every rule of the program that makes a row `t` asks that `u` be absent, then
from a store that holds `u` and no `t`, **no run** reaches a store holding `t`
(`blocked_step`: the invariant is kept by every admitted firing).

## The example

The program `program`: `spawn` (make `T` where `U` is absent) and `tick` (read `U`, make `W`).

* `alone_succeeds`: from the empty store `spawn` fires and `T` is present.
* `beside_blocked`: beside the store holding `U` no run ever makes `T`; and such runs exist
  (`tick_runs_beside`: `tick` fires there, and `U` stays).
* `succeeds_beside_clear`: beside every store with no `U` (whose knowledge has identical sides and
  which does not hold the occurrence `spawn` makes), success stays reachable. The switch-off happens
  exactly off the grade of `Composition.guarded_union_iff`.
* `source_switchable`: the step under this program is switchable: the empty store and the store
  holding `U` are composable, the first succeeds, their union does not.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed

open NamesOnTheStep NamesOnTheStep.IssuingControls
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.Composition
  (unionOf union guarded_union_iff)

/-! ## The calculus -/

section General

variable {T : Type*} {S : Type*} {O : Type*} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T)

/-- **The first-order step under a program**: a firing whose rule the program holds, admitted at
`C`, leads to its result. -/
def ProgramStep (program : RuleInstance T → Prop) (C C' : Configuration T O) : Prop :=
  ∃ f : AnnotatedRuns.Firing T S O, program f.rule ∧
    (AnnotatedRuns.firstOrder A label).toStep.Admits (s := C) f ∧ f.result label C = C'

/-- **Composable configurations**: their stores are disjoint and their joint knowledge is
solvable. -/
def Composable (C D : Configuration T O) : Prop :=
  Disjoint C.present D.present ∧ A.Consistent (C.equations ++ D.equations)

/-- **Success**: a row satisfying `row` is present. -/
def Shows (row : T → Prop) (C : Configuration T O) : Prop :=
  ∃ o ∈ C.present, row (label o)

/-- **The step under a program, as a calculus with a parallel composition**: configurations, the
program's steps, `unionOf` on composable configurations, success "a row satisfying `row` is
present", and equality as the static equivalence. -/
def stepCalculus (program : RuleInstance T → Prop) (row : T → Prop) : ParallelCalculus where
  Term := Configuration T O
  step := ProgramStep A label program
  par := unionOf
  composable := Composable A
  success := Shows label row
  same := Eq

end General

/-! ## The blocked situation, along every run -/

/-- A pair related by `Forall₂` has a partner for every element on the right. -/
theorem exists_left_of_forall₂ {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {b : β}, b ∈ l₂ → ∃ a ∈ l₁, R a b
  | _, _, .nil, _, member => absurd member List.not_mem_nil
  | _, _, .cons head tail, _, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self, head⟩
      · obtain ⟨a, inTail, related⟩ := exists_left_of_forall₂ tail later
        exact ⟨a, List.mem_cons_of_mem _ inTail, related⟩

/-- **One admitted firing keeps the blocker and keeps success away**, over ground terms: when no rule
of the program takes `u`, and every rule that makes `t` asks that `u` be absent. -/
theorem blocked_step {program : RuleInstance Expr → Prop} {u t : Expr}
    (keeps : ∀ r, program r → u ∉ r.take)
    (guards : ∀ r, program r → t ∈ r.produce → Check.predicate .none u ∈ r.checks)
    {C C' : Conf} (step : ProgramStep ground (Prod.fst : Occ → Expr) program C C')
    (holds : ∃ o ∈ C.present, o.1 = u) (clear : ∀ o ∈ C.present, o.1 ≠ t) :
    (∃ o ∈ C'.present, o.1 = u) ∧ ∀ o ∈ C'.present, o.1 ≠ t := by
  obtain ⟨f, inProgram, admitted, rfl⟩ := step
  have valid : f.selection.Valid ground Prod.fst f.rule C :=
    (show f.Valid ground Prod.fst C from admitted).firing
  obtain ⟨o, present, labelled⟩ := holds
  refine ⟨⟨o, ?_, labelled⟩, ?_⟩
  · change o ∈ fire C.present (f.selection.commit (T := Expr))
    rw [mem_fire]
    refine Or.inl ⟨present, fun taken => ?_⟩
    have selected : o ∈ f.selection.taken := List.mem_toFinset.mp taken
    obtain ⟨p, inTake, same⟩ := exists_left_of_forall₂ (takes_match valid) selected
    exact keeps _ inProgram (by rw [same, labelled] at inTake; exact inTake)
  · intro o' member isT
    change o' ∈ fire C.present (f.selection.commit (T := Expr)) at member
    rw [mem_fire] at member
    rcases member with ⟨old, _⟩ | made
    · exact clear o' old isT
    · have produced : o'.1 ∈ f.rule.produce := made_label valid (List.mem_toFinset.mp made)
      rw [isT] at produced
      exact absent_refuted valid (guards _ inProgram produced) present labelled

/-- **A persistent blocker keeps success unreachable along every run**, over ground terms: no rule of
the program takes `u`, every rule that makes `t` asks that `u` be absent, and the store holds `u`
and no `t`. -/
theorem never_succeeds_of_blocker {program : RuleInstance Expr → Prop} {u t : Expr}
    (keeps : ∀ r, program r → u ∉ r.take)
    (guards : ∀ r, program r → t ∈ r.produce → Check.predicate .none u ∈ r.checks)
    {C : Conf} (holds : ∃ o ∈ C.present, o.1 = u) (clear : ∀ o ∈ C.present, o.1 ≠ t) :
    ¬ (stepCalculus ground (Prod.fst : Occ → Expr) program (· = t)).Succeeds C := by
  rintro ⟨C', run, o, member, isT⟩
  have invariant : ∀ D, Relation.ReflTransGen (ProgramStep ground Prod.fst program) C D →
      (∃ o ∈ D.present, o.1 = u) ∧ ∀ o ∈ D.present, o.1 ≠ t := by
    intro D reaches
    induction reaches with
    | refl => exact ⟨holds, clear⟩
    | tail _ step ih => exact blocked_step keeps guards step ih.1 ih.2
  exact (invariant C' run).2 o member isT

/-- Every reachable configuration still holds the blocker. -/
theorem blocker_stays {program : RuleInstance Expr → Prop} {u t : Expr}
    (keeps : ∀ r, program r → u ∉ r.take)
    (guards : ∀ r, program r → t ∈ r.produce → Check.predicate .none u ∈ r.checks)
    {C D : Conf} (holds : ∃ o ∈ C.present, o.1 = u) (clear : ∀ o ∈ C.present, o.1 ≠ t)
    (reaches : Relation.ReflTransGen (ProgramStep ground Prod.fst program) C D) :
    ∃ o ∈ D.present, o.1 = u := by
  have invariant : (∃ o ∈ D.present, o.1 = u) ∧ ∀ o ∈ D.present, o.1 ≠ t := by
    induction reaches with
    | refl => exact ⟨holds, clear⟩
    | tail _ step ih => exact blocked_step keeps guards step ih.1 ih.2
  exact invariant.1

/-! ## The example -/

/-- `tick`: read `U`, make `W`. -/
def tick : RuleInstance Expr := rule [] [factU] [factW]

/-- **The absence-guarded program**: `spawn` (make `T` where `U` is absent) and `tick` (read `U`,
make `W`). -/
def program (r : RuleInstance Expr) : Prop := r = Separations.spawn ∨ r = tick

/-- The step under the program, success "a row `T` is present". -/
abbrev source : ParallelCalculus := stepCalculus ground (Prod.fst : Occ → Expr) program (· = factT)

/-- No rule of the program takes `U`. -/
theorem program_keeps : ∀ r, program r → factU ∉ r.take := by
  rintro r (rfl | rfl) <;> simp [Separations.spawn, tick, rule]

/-- Every rule of the program that makes `T` asks that `U` be absent. -/
theorem program_guards : ∀ r, program r → factT ∈ r.produce → Check.predicate .none factU ∈ r.checks := by
  rintro r (rfl | rfl) made
  · simp [Separations.spawn, rule]
  · simp [tick, rule, factT, factW] at made

/-- The empty store and the store holding `U`. -/
abbrev alone : Conf := Separations.emptyS.1
abbrev blocker : Conf := Separations.onlyU.1

/-- **Alone, success is reachable**: `spawn` fires at the empty store and makes `T`. -/
theorem alone_succeeds : source.Succeeds alone := by
  refine ⟨_, .single ⟨Separations.spawnAt.1, Or.inl rfl, Separations.spawn_admitted.1, rfl⟩,
    (factT, 0), ?_, rfl⟩
  change (factT, 0) ∈ fire alone.present (Separations.spawnAt.1.selection.commit (T := Expr))
  rw [mem_fire]
  exact Or.inr (by simp [Separations.spawnAt, Selection.commit])

/-- The two stores are composable: disjoint, with solvable joint knowledge. -/
theorem alone_blocker_composable : Composable ground alone blocker :=
  ⟨Finset.disjoint_empty_left _, ⟨(), fun _ member => absurd member List.not_mem_nil⟩⟩

/-- **Beside the store holding `U`, success is unreachable along every run.** -/
theorem beside_blocked : ¬ source.Succeeds (unionOf alone blocker) :=
  never_succeeds_of_blocker program_keeps program_guards ⟨(factU, 0), by decide, rfl⟩
    (by decide)

/-- `tick`, reading the blocker and making `W` with copy number `0`. -/
def tickAt : Fir := ⟨tick, [], ⟨[], [(factU, 0)], [(factW, 0)]⟩⟩

/-- **Runs exist beside the blocker**: `tick` is admitted there, and after it `U` is still present
and `T` still absent. -/
theorem tick_runs_beside :
    ProgramStep ground Prod.fst program (unionOf alone blocker)
        (tickAt.result Prod.fst (unionOf alone blocker)) ∧
      (∃ o ∈ (tickAt.result Prod.fst (unionOf alone blocker)).present, o.1 = factU) ∧
      ∀ o ∈ (tickAt.result Prod.fst (unionOf alone blocker)).present, o.1 ≠ factT := by
  have admitted : base.Admits (s := unionOf alone blocker) tickAt :=
    (admits_of (D := fun _ _ _ _ => True) (σ := (unionOf alone blocker, ∅)) (fresh := []) (by decide)
      (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl) trivial).1
  have step : ProgramStep ground Prod.fst program (unionOf alone blocker)
      (tickAt.result Prod.fst (unionOf alone blocker)) := ⟨tickAt, Or.inr rfl, admitted, rfl⟩
  exact ⟨step, blocked_step program_keeps program_guards step ⟨(factU, 0), by decide, rfl⟩
    (by decide)⟩

/-- **On the grade, success stays reachable**: beside every store that holds no `U`, whose knowledge
has identical sides and which does not hold the occurrence `spawn` makes. -/
theorem succeeds_beside_clear {D : Conf} (clearU : ∀ o ∈ D.present, o.1 ≠ factU)
    (fresh : (factT, 0) ∉ D.present) (knowledge : ∀ e ∈ D.equations, e.1 = e.2) :
    source.Succeeds (unionOf alone D) := by
  have admitted : base.Admits (s := union alone D) Separations.spawnAt.1 :=
    (guarded_union_iff rfl rfl Separations.spawn_admitted.1
      (fun o made => by
        simp only [Separations.spawnAt, List.mem_singleton] at made
        rw [made]
        exact fresh) knowledge).mpr (absent_holds clearU)
  refine ⟨_, .single ⟨Separations.spawnAt.1, Or.inl rfl, admitted, rfl⟩, (factT, 0), ?_, rfl⟩
  change (factT, 0) ∈ fire (unionOf alone D).present
    (Separations.spawnAt.1.selection.commit (T := Expr))
  rw [mem_fire]
  exact Or.inr (by simp [Separations.spawnAt, Selection.commit])

/-- **The step under the absence-guarded program is switchable**: the empty store succeeds, and
beside the composable store holding `U` it does not. -/
theorem source_switchable : source.Switchable :=
  ⟨alone, blocker, alone_blocker_composable, alone_succeeds, beside_blocked⟩

#print axioms blocked_step
#print axioms never_succeeds_of_blocker
#print axioms blocker_stays
#print axioms alone_succeeds
#print axioms alone_blocker_composable
#print axioms beside_blocked
#print axioms tick_runs_beside
#print axioms succeeds_beside_clear
#print axioms source_switchable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed
