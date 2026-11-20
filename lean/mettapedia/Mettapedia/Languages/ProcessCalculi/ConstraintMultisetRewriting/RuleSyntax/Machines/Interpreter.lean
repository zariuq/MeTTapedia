import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.PartialRecursive
import Mettapedia.Languages.PartrecMachine.Rice

/-!
# A deterministic transition system with a partial recursive step is a finite positive program

A code `c` of Mathlib's `Turing.ToPartrec` computes a transition system on the naturals: `n` steps to `m` when
`c` evaluates `[n]` to `[m]` (`Next c`). Every transition system `n ↦ m ∈ f n` with `f` partial recursive in one
argument is of this form (`next_of_partrec`, by Mathlib's `Turing.ToPartrec.Code.exists_code`).

The program that hosts it (`loopRules c`) is the nineteen rules of the machine and one more, which takes the
halted row with one output and makes the pending evaluation of `c` on that output (`restartLhs`,
`restartRhs`). It has twenty rules, each taking one row and making one row. All statements are about the
one-match step, `RuleSyntax.step` at the one first-order frame over rows with unknowns.

* **The correspondence** (`loopCorrespondence`): an `OperationalCorrespondence` from the transition system
  `Next c` to the step of the program. A state is related to `n` when it reads as the row of a point that the
  machine reaches from the pending evaluation of `c` on `[n]` (`Computing`). A firing is read back as no step of
  the system, while the machine computes, or as one step, when the restart rule fires. A step `n` to `m` of the
  system is realized by a path of firings: the rest of the computation of `c` on `[n]`, which is determined, and
  the restart.
* **Every partial recursive step** (`hosts_partrec_system`).

## What the correspondence gives, and what it does not

* **Reachable numbers, both ways** (`reaches_iff`): `n` reaches `m` in one or more steps of the system exactly
  when the program, run from the pending evaluation of `n`, reaches a state that reads as the halted row with
  output `[m]`.
* **Divergence is preserved** (`infinite_run_of_source`): an infinite run of the system from `n` gives an
  infinite run of the program from the state of `n`, because every step of the system is realized by at least
  one firing (`acc_next_of_acc`).
* **Divergence is not reflected, and a dead state is not preserved** (`runs_forever_of_none`): where the code
  has no value, the system has no step, and the program runs for ever: every state it reaches admits a firing
  (`never_stuck_of_none`). The silent firings of the computation do not end there. The code `silent` is an
  instance at every number (`silent_runs_forever`). This is the price of a partial step: the program cannot
  know that the computation of the next state will not end.
* **Halting is reflected** (`stuck_reflected`): where the program has no firing, the number it is related to
  has no step; that happens when the code's output is not one number (`nil_halts`, with `Code.nil`).

## Cost

One step of the system from `n` to `m` is realized by exactly `k + 1` firings, where `k` is the number of
reductions of the authored machine from the pending evaluation of `c` on `[n]` to the halted configuration
(`step_cost`), and that number is determined (`runFor_halt_unique`); the extra firing is the restart. Every
firing of the program at a state that reads as the row of a point is that point's one move of the loop
(`loop_deterministic`), so the run is the machine's. Numbers are unary rows (`eNat`): a firing matches a whole
row in one step, so the successor of any number costs two reductions (`succ_cost`), while the size of a row is
linear in the numbers it holds.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.PartialRecursive

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open Mettapedia.Languages.PartrecMachine
open Turing.ToPartrec
open NamesOnTheStep (Expr)
open Presentation.Schematic

/-! ## Runs of a system -/

/-- A path of steps of a system is a finite run of it. -/
theorem multiStep_of_steps {S : GSLT} {a b : S.Term} (path : Relation.ReflTransGen S.Step a b) :
    S.MultiStep a b := by
  induction path with
  | refl => exact .refl _
  | tail _ stepped reached => exact multiStepAppend reached (.step stepped (.refl _))

/-- A finite run of a system is a path of its steps. -/
theorem steps_of_multiStep {S : GSLT} {a b : S.Term} (path : S.MultiStep a b) :
    Relation.ReflTransGen S.Step a b := by
  induction path with
  | refl => exact .refl
  | step stepped _ reached => exact Relation.ReflTransGen.head stepped reached

/-- **A system that is never stuck along the runs from a state runs for ever from it.** -/
theorem exists_infinite_run {S : GSLT} {start : S.Term}
    (neverStuck : ∀ s, S.MultiStep start s → ∃ s', S.Step s s') :
    ∃ run : ℕ → S.Term, run 0 = start ∧ ∀ i, S.Step (run i) (run (i + 1)) := by
  have notAcc : ¬ Acc (fun next state => S.Step state next) start := by
    intro accessible
    have never : ∀ s, Acc (fun next state => S.Step state next) s → S.MultiStep start s → False := by
      intro s acc
      induction acc with
      | intro s _ ih =>
          intro reached
          obtain ⟨s', stepped⟩ := neverStuck s reached
          exact ih s' stepped (multiStepAppend reached (.step stepped (.refl _)))
    exact never start accessible (.refl _)
  exact not_acc_iff_exists_descending_chain.mp notAcc

/-- A finite run is empty or begins with a step. -/
theorem multiStep_cases {S : GSLT} {a b : S.Term} (path : S.MultiStep a b) :
    a = b ∨ ∃ c, S.Step a c ∧ S.MultiStep c b := by
  cases path with
  | refl => exact Or.inl rfl
  | step stepped rest => exact Or.inr ⟨_, stepped, rest⟩

/-- A run of a system on the naturals from a number with no step stays at that number. -/
theorem multiStep_stuck {R : ℕ → ℕ → Prop} {n a : ℕ} (stuck : ∀ m, ¬ R n m)
    (path : (equalityGSLT ℕ R).MultiStep n a) : a = n := by
  rcases multiStep_cases path with same | ⟨c, stepped, -⟩
  · exact same.symm
  · exact (stuck c stepped).elim

/-- A path followed by one step is one longer. -/
theorem length_append_single {S : GSLT} {a b c : S.Term} (path : ExecutionPath S a b) (step : S.Step b c) :
    (path.append (.cons ⟨step⟩ (.refl c))).length = path.length + 1 := by
  simp [Mettapedia.GSLT.Ultrainfinite.Route.length_append, Mettapedia.GSLT.Ultrainfinite.Route.length]

/-! ## Points and their paths -/

/-- **A point advances to its successor.** -/
def Advances (p p' : Point) : Prop := successor p = some p'

theorem advances_rightUnique : Relator.RightUnique Advances := fun _ _ _ first second =>
  Option.some.inj (first.symm.trans second)

/-- A reduction path of the authored machine from a point is a path of points. -/
theorem points_of_reduces {p : Point} {t : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (path : Relation.ReflTransGen Reduces p.pattern t) :
    ∃ q : Point, t = q.pattern ∧ Relation.ReflTransGen Advances p q := by
  induction path with
  | refl => exact ⟨p, rfl, .refl⟩
  | tail _ stepped ih =>
      obtain ⟨q, rfl, reached⟩ := ih
      obtain ⟨q', advanced, rfl⟩ := (reduces_iff_successor q _).mp stepped
      exact ⟨q', rfl, reached.tail advanced⟩

/-- A path of points is a reduction path of the authored machine. -/
theorem reduces_of_points {p q : Point} (path : Relation.ReflTransGen Advances p q) :
    Relation.ReflTransGen Reduces p.pattern q.pattern := by
  induction path with
  | refl => exact .refl
  | tail _ advanced reached => exact reached.tail ((reduces_iff_successor _ _).mpr ⟨_, advanced, rfl⟩)

/-- A halted configuration is the end of its paths. -/
theorem halted_terminal {w : List ℕ} {q : Point}
    (path : Relation.ReflTransGen Advances (.config (.halt w)) q) : q = .config (.halt w) := by
  rcases Relation.ReflTransGen.cases_head path with same | ⟨middle, advanced, -⟩
  · exact same.symm
  · cases advanced

/-! ## The machine's run, counted -/

/-- **The machine run for a number of reductions**: the point reached after `k` reductions, if the machine has
not stopped before. -/
def runFor : ℕ → Point → Option Point
  | 0, p => some p
  | k + 1, p => (successor p).bind (runFor k)

theorem runFor_add (j k : ℕ) (p : Point) : runFor (j + k) p = (runFor j p).bind (runFor k) := by
  induction j generalizing p with
  | zero => simp [runFor]
  | succ j ih =>
      rw [show j + 1 + k = (j + k) + 1 by omega]
      simp only [runFor]
      cases successor p with
      | none => rfl
      | some p' => exact ih p'

/-- **A path of points is a counted run of the machine.** -/
theorem reaches_iff_runFor {p q : Point} :
    Relation.ReflTransGen Advances p q ↔ ∃ k, runFor k p = some q := by
  constructor
  · intro path
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, rfl⟩
    | head advanced _ ih =>
        obtain ⟨k, ran⟩ := ih
        have stepped : successor _ = some _ := advanced
        refine ⟨k + 1, ?_⟩
        simp only [runFor]
        rw [stepped]
        exact ran
  · rintro ⟨k, ran⟩
    induction k generalizing p with
    | zero =>
        have same : p = q := Option.some.inj ran
        subst same
        exact .refl
    | succ k ih =>
        cases stepped : successor p with
        | none => simp [runFor, stepped] at ran
        | some p' =>
            have ran' : runFor k p' = some q := by simpa [runFor, stepped] using ran
            exact Relation.ReflTransGen.head stepped (ih ran')

/-- **The number of reductions to a halted configuration is determined**, and so is the output. -/
theorem runFor_halt_unique {p : Point} {j k : ℕ} {w w' : List ℕ}
    (first : runFor j p = some (.config (.halt w))) (second : runFor k p = some (.config (.halt w'))) :
    j = k ∧ w = w' := by
  have onward : ∀ {j k : ℕ} {w w' : List ℕ}, j ≤ k → runFor j p = some (.config (.halt w)) →
      runFor k p = some (.config (.halt w')) → j = k ∧ w = w' := by
    intro j k w w' le first second
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le le
    rw [runFor_add, first] at second
    have rest : runFor d (.config (.halt w)) = some (.config (.halt w')) := second
    cases d with
    | zero =>
        have same : Point.config (.halt w) = .config (.halt w') := Option.some.inj rest
        cases same
        exact ⟨rfl, rfl⟩
    | succ d => cases rest
  rcases Nat.le_total j k with le | le
  · exact onward le first second
  · obtain ⟨same, sameW⟩ := onward le second first
    exact ⟨same.symm, sameW.symm⟩

/-- **The successor of any number costs two reductions.** -/
theorem succ_cost (n : ℕ) : runFor 2 (.normal .succ .halt [n]) = some (.config (.halt [n + 1])) := rfl

/-! ## The transition system of a code -/

/-- **The transition system a code computes on one number**: `n` steps to `m` when the code evaluates `[n]`
to `[m]`. -/
def Next (c : Code) (n m : ℕ) : Prop := [m] ∈ c.eval [n]

/-- A step of the system is a path of points from the pending evaluation to the halted configuration. -/
theorem next_iff_reaches (c : Code) (n m : ℕ) :
    Next c n m ↔ Relation.ReflTransGen Advances (.normal c .halt [n]) (.config (.halt [m])) := by
  constructor
  · intro next
    obtain ⟨q, isHalt, path⟩ :=
      points_of_reduces (p := .normal c .halt [n]) ((adequacy c [n] [m]).mpr next)
    rw [← pattern_halt isHalt.symm]
    exact path
  · intro path
    exact (adequacy c [n] [m]).mp (reduces_of_points path)

/-- **A step of the system is a counted run of the machine.** -/
theorem next_iff_runFor (c : Code) (n m : ℕ) :
    Next c n m ↔ ∃ k, runFor k (.normal c .halt [n]) = some (.config (.halt [m])) :=
  (next_iff_reaches c n m).trans reaches_iff_runFor

/-- **Every transition system with a partial recursive step in one argument is the system of a code.** -/
theorem next_of_partrec {f : List.Vector ℕ 1 →. ℕ} (partrec : Nat.Partrec' f) :
    ∃ c : Code, ∀ n m : ℕ, Next c n m ↔ m ∈ f ⟨[n], rfl⟩ := by
  obtain ⟨c, evaluates⟩ := Code.exists_code partrec
  refine ⟨c, fun n m => ?_⟩
  have evaluated : c.eval [n] = pure <$> f ⟨[n], rfl⟩ := evaluates ⟨[n], rfl⟩
  show [m] ∈ c.eval [n] ↔ m ∈ f ⟨[n], rfl⟩
  rw [evaluated]
  constructor
  · intro member
    obtain ⟨a, inside, same⟩ := (Part.mem_map_iff _).mp member
    have equal : [a] = [m] := same
    rw [← (List.cons.inj equal).1]
    exact inside
  · intro member
    exact (Part.mem_map_iff _).mpr ⟨m, member, rfl⟩

/-- The system has no step from a number at which the code has no value. -/
theorem next_none {c : Code} {n : ℕ} (none : c.eval [n] = Part.none) (m : ℕ) : ¬ Next c n m := by
  intro next
  have member : [m] ∈ c.eval [n] := next
  rw [none] at member
  exact Part.notMem_none _ member

/-- The successor code steps every number to the next. -/
theorem next_succ (n m : ℕ) : Next .succ n m ↔ m = n + 1 := by
  show [m] ∈ Code.succ.eval [n] ↔ m = n + 1
  simp [Code.eval]

/-! ## The schemas of the loop -/

/-- The schemas of the machine. -/
def schemas : List (Tm × Tm) := names.map fun n => (lhs n, rhs n)

theorem unknowns_toTerm : ∀ e : Expr, unknowns (toTerm e) = []
  | .sym _ => rfl
  | .app f a => congrArg₂ (· ++ ·) (unknowns_toTerm f) (unknowns_toTerm a)
  | .name _ => rfl
  | .code e => unknowns_toTerm e

/-- The pattern of a halted configuration with one output. -/
def restartLhs : Tm := ap (con 16) (consP (unk 0) (con 2))

/-- The pattern of the pending evaluation of a code on that output. -/
def restartRhs (c : Code) : Tm := ap (ap (ap (con 18) (toTerm (eCode c))) (con 11)) (consP (unk 0) (con 2))

/-- **The schemas of the loop of a code**: the machine's, and the restart of the code on a halted output. -/
def loopSchemas (c : Code) : List (Tm × Tm) := schemas ++ [(restartLhs, restartRhs c)]

theorem loopSchemas_closed (c : Code) : ∀ p ∈ loopSchemas c, ∀ x ∈ unknowns p.2, x ∈ unknowns p.1 := by
  intro p member x inside
  rcases List.mem_append.mp member with inMachine | isRestart
  · obtain ⟨n, -, rfl⟩ := List.mem_map.mp inMachine
    exact range n x inside
  · rw [List.mem_singleton.mp isRestart] at inside ⊢
    have unfolded : x ∈ (([] ++ unknowns (toTerm (eCode c))) ++ []) ++ (([] ++ [0]) ++ []) := inside
    rw [unknowns_toTerm] at unfolded
    exact unfolded

/-- **The program of the loop of a code**: twenty rules, each taking one row and making one row. -/
def loopRules (c : Code) : List SRule := rootRules (loopSchemas c)

/-! ## Root rewrites of the loop at the rows of points -/

/-- A root rewrite by the machine's schemas at the row of a point is the point's advance. -/
theorem rootStep_schemas_iff (p : Point) (e' : Expr) :
    RootStep schemas p.row e' ↔ ∃ p', Advances p p' ∧ e' = p'.row := by
  constructor
  · rintro ⟨pair, member, θ, matched, rfl⟩
    obtain ⟨n, -, rfl⟩ := List.mem_map.mp member
    obtain ⟨p', advanced, made⟩ := successor_of_instance (n := n) matched
    exact ⟨p', advanced, made⟩
  · rintro ⟨p', advanced, rfl⟩
    obtain ⟨n, θ, matched, made⟩ := fires_of_successor advanced
    exact ⟨(lhs n, rhs n), List.mem_map_of_mem (mem_names n), θ, matched, made⟩

/-- **The restart schema at the row of a point**: it rewrites exactly a halted configuration with one output,
to the pending evaluation of the code on that output. -/
theorem restart_iff (c : Code) (p : Point) (e' : Expr) :
    (∃ θ : ℕ → Expr, inst θ restartLhs = p.row ∧ inst θ (restartRhs c) = e') ↔
      ∃ m, p = .config (.halt [m]) ∧ e' = (Point.normal c .halt [m]).row := by
  constructor
  · rintro ⟨θ, matched, rfl⟩
    cases p with
    | normal c' k v => cases (Expr.app.inj matched).1
    | config cfg =>
        cases cfg with
        | ret k v => cases (Expr.app.inj matched).1
        | halt v =>
            have lists : Expr.app (Expr.app (Expr.sym 3) (θ 0)) (Expr.sym 2) = eNats v :=
              (Expr.app.inj matched).2
            cases v with
            | nil => cases lists
            | cons m w =>
                have parts := Expr.app.inj lists
                have isNat : θ 0 = eNat m := (Expr.app.inj parts.1).2
                cases w with
                | cons b w' => cases parts.2
                | nil =>
                    exact ⟨m, rfl, congrArg₂ (fun code x => Expr.app (Expr.app (Expr.app (Expr.sym 18) code)
                      (Expr.sym 11)) (Expr.app (Expr.app (Expr.sym 3) x) (Expr.sym 2)))
                      (inst_toTerm θ (eCode c)) isNat⟩
  · rintro ⟨m, rfl, rfl⟩
    exact ⟨fun _ => eNat m, rfl, congrArg (fun code => Expr.app (Expr.app (Expr.app (Expr.sym 18) code)
      (Expr.sym 11)) (Expr.app (Expr.app (Expr.sym 3) (eNat m)) (Expr.sym 2)))
      (inst_toTerm (fun _ => eNat m) (eCode c))⟩

/-- **The loop on points**: a point advances, or a halted configuration with one output restarts the code on
it. -/
def Loops (c : Code) (p p' : Point) : Prop :=
  Advances p p' ∨ ∃ m, p = .config (.halt [m]) ∧ p' = .normal c .halt [m]

/-- **The loop is deterministic**: a point has at most one move. -/
theorem loops_rightUnique (c : Code) : Relator.RightUnique (Loops c) := by
  intro p first second toFirst toSecond
  rcases toFirst with advanced | ⟨m, rfl, rfl⟩ <;> rcases toSecond with advanced' | ⟨m', same, rfl⟩
  · exact advances_rightUnique advanced advanced'
  · subst same
    cases advanced
  · cases advanced'
  · cases same
    rfl

/-- **A root rewrite by the loop's schemas at the row of a point is a step of the loop on points.** -/
theorem rootStep_loop_iff (c : Code) (p : Point) (e' : Expr) :
    RootStep (loopSchemas c) p.row e' ↔ ∃ p', Loops c p p' ∧ e' = p'.row := by
  constructor
  · rintro ⟨pair, member, θ, matched, made⟩
    rcases List.mem_append.mp member with inMachine | isRestart
    · obtain ⟨p', advanced, same⟩ := (rootStep_schemas_iff p e').mp ⟨pair, inMachine, θ, matched, made⟩
      exact ⟨p', Or.inl advanced, same⟩
    · rw [List.mem_singleton.mp isRestart] at matched made
      obtain ⟨m, isHalt, same⟩ := (restart_iff c p e').mp ⟨θ, matched, made⟩
      exact ⟨.normal c .halt [m], Or.inr ⟨m, isHalt, rfl⟩, same⟩
  · rintro ⟨p', looped, rfl⟩
    rcases looped with advanced | ⟨m, isHalt, isNormal⟩
    · obtain ⟨pair, member, rooted⟩ := (rootStep_schemas_iff p p'.row).mpr ⟨p', advanced, rfl⟩
      exact ⟨pair, List.mem_append_left _ member, rooted⟩
    · subst isNormal
      obtain ⟨θ, matched, made⟩ := (restart_iff c p (Point.normal c .halt [m]).row).mpr ⟨m, isHalt, rfl⟩
      exact ⟨(restartLhs, restartRhs c), List.mem_append_right _ (List.mem_singleton_self _), θ, matched,
        made⟩

/-- A path of points is a path of root rewrites of the loop. -/
theorem rootPath_of_points (c : Code) {p q : Point} (path : Relation.ReflTransGen Advances p q) :
    Relation.ReflTransGen (RootStep (loopSchemas c)) p.row q.row := by
  induction path with
  | refl => exact .refl
  | tail _ advanced reached =>
      exact reached.tail ((rootStep_loop_iff c _ _).mpr ⟨_, Or.inl advanced, rfl⟩)

/-- The restart is one root rewrite. -/
theorem restart_rootStep (c : Code) (m : ℕ) :
    RootStep (loopSchemas c) (eCfg (.halt [m])) (eNormal c .halt [m]) :=
  (rootStep_loop_iff c (.config (.halt [m])) (Point.normal c .halt [m]).row).mpr
    ⟨.normal c .halt [m], Or.inr ⟨m, rfl, rfl⟩, rfl⟩

/-- A step of the system is a path of root rewrites from the pending evaluation to the halted row. -/
theorem rootPath_of_next {c : Code} {n m : ℕ} (next : Next c n m) :
    Relation.ReflTransGen (RootStep (loopSchemas c)) (eNormal c .halt [n]) (eCfg (.halt [m])) :=
  rootPath_of_points c ((next_iff_reaches c n m).mp next)

/-- A step of the system is a nonempty path of root rewrites between pending evaluations. -/
theorem rootTransGen_of_next {c : Code} {n m : ℕ} (next : Next c n m) :
    Relation.TransGen (RootStep (loopSchemas c)) (eNormal c .halt [n]) (eNormal c .halt [m]) :=
  Relation.TransGen.tail' (rootPath_of_next next) (restart_rootStep c m)

/-- A path of the system is a path of root rewrites between pending evaluations. -/
theorem rootPath_of_path {c : Code} {n m : ℕ} (path : Relation.ReflTransGen (Next c) n m) :
    Relation.ReflTransGen (RootStep (loopSchemas c)) (eNormal c .halt [n]) (eNormal c .halt [m]) := by
  induction path with
  | refl => exact .refl
  | tail _ next reached => exact reached.trans (rootTransGen_of_next next).to_reflTransGen

/-! ## Root rewrites as firings, along paths -/

section Lift

variable {table : List (Tm × Tm)}

/-- **A path of root rewrites is a run of firings**, from every state that reads as its first row. -/
theorem firings_of_rootPath (closed : ∀ p ∈ table, ∀ x ∈ unknowns p.2, x ∈ unknowns p.1) {e e' : Expr}
    (path : Relation.ReflTransGen (RootStep table) e e') {s : SState ℕ} (reads : ReadsBag s {e}) :
    ∃ s', (stepSystem ℕ (rootRules table)).MultiStep s s' ∧ ReadsBag s' {e'} := by
  induction path with
  | refl => exact ⟨s, .refl _, reads⟩
  | tail _ rooted reached =>
      obtain ⟨s₁, run, reads₁⟩ := reached
      obtain ⟨g, admitted, reads₂⟩ := firing_of_rootStep closed reads₁ rooted
      exact ⟨_, multiStepAppend run (.step ⟨g, admitted, rfl⟩ (.refl _)), reads₂⟩

/-- **A nonempty path of root rewrites is a nonempty run of firings.** -/
theorem firings_of_rootTransGen (closed : ∀ p ∈ table, ∀ x ∈ unknowns p.2, x ∈ unknowns p.1) {e e' : Expr}
    (path : Relation.TransGen (RootStep table) e e') {s : SState ℕ} (reads : ReadsBag s {e}) :
    ∃ s', Relation.TransGen (stepSystem ℕ (rootRules table)).Step s s' ∧ ReadsBag s' {e'} := by
  induction path with
  | single rooted =>
      obtain ⟨g, admitted, reads'⟩ := firing_of_rootStep closed reads rooted
      exact ⟨_, .single ⟨g, admitted, rfl⟩, reads'⟩
  | tail _ rooted reached =>
      obtain ⟨s₁, run, reads₁⟩ := reached
      obtain ⟨g, admitted, reads₂⟩ := firing_of_rootStep closed reads₁ rooted
      exact ⟨_, run.tail ⟨g, admitted, rfl⟩, reads₂⟩

end Lift

/-- **A counted run of the machine is a counted run of firings of the loop.** -/
theorem firings_of_runFor (c : Code) : ∀ (k : ℕ) {p q : Point}, runFor k p = some q → ∀ {s : SState ℕ},
    ReadsBag s {p.row} → ∃ s', ∃ path : ExecutionPath (stepSystem ℕ (loopRules c)) s s',
      path.length = k ∧ ReadsBag s' {q.row}
  | 0, p, q, ran, s, reads => by
      have same : p = q := Option.some.inj ran
      subst same
      exact ⟨s, .refl s, rfl, reads⟩
  | k + 1, p, q, ran, s, reads => by
      cases stepped : successor p with
      | none => simp [runFor, stepped] at ran
      | some p' =>
          have ran' : runFor k p' = some q := by simpa [runFor, stepped] using ran
          obtain ⟨g, admitted, reads'⟩ := firing_of_rootStep (loopSchemas_closed c) reads
            ((rootStep_loop_iff c p p'.row).mpr ⟨p', Or.inl stepped, rfl⟩)
          obtain ⟨s', path, length, readsEnd⟩ := firings_of_runFor c k ran' reads'
          refine ⟨s', .cons ⟨⟨g, admitted, rfl⟩⟩ path, ?_, readsEnd⟩
          show path.length + 1 = k + 1
          rw [length]

/-- **Every firing of the loop at the row of a point is the point's one move of the loop.** -/
theorem loop_deterministic {c : Code} {p : Point} {s : SState ℕ} (reads : ReadsBag s {p.row})
    (g : Firing ℕ E {r | r ∈ loopRules c} s.frame)
    (admitted : (schematicStep ℕ (loopRules c)).Admits (s := s) g) :
    ∃ p', Loops c p p' ∧ ReadsBag ((schematicStep ℕ (loopRules c)).result g admitted) {p'.row} := by
  obtain ⟨e', rooted, reads'⟩ := rootStep_of_firing (loopSchemas_closed c) reads g admitted
  obtain ⟨p', looped, rfl⟩ := (rootStep_loop_iff c p e').mp rooted
  exact ⟨p', looped, reads'⟩

/-! ## The correspondence -/

/-- **A number is being computed at a row**: the row is the row of a point that the machine reaches from the
pending evaluation of the code on the number. -/
def Computing (c : Code) (n : ℕ) (e : Expr) : Prop :=
  ∃ p : Point, e = p.row ∧ Relation.ReflTransGen Advances (.normal c .halt [n]) p

/-- **The system of a code and the loop's root rewriting**: a rewrite is no step of the system or one, and a
step of the system is a path of rewrites. -/
def loopHosted (c : Code) : OperationalCorrespondence (equalityGSLT ℕ (Next c)) (rootSystem (loopSchemas c)) where
  related := Computing c
  readStep := by
    rintro n e e' ⟨p, rfl, path⟩ stepped
    obtain ⟨p', looped, rfl⟩ := (rootStep_loop_iff c p e').mp stepped
    rcases looped with advanced | ⟨m, isHalt, isNormal⟩
    · exact Or.inl ⟨p', rfl, path.tail advanced⟩
    · subst isNormal
      subst isHalt
      exact Or.inr ⟨m, (next_iff_reaches c n m).mpr path, _, rfl, .refl⟩
  forward := by
    rintro n m e ⟨p, rfl, path⟩ next
    have toHalt := (next_iff_reaches c n m).mp next
    have fromPoint : Relation.ReflTransGen Advances p (.config (.halt [m])) := by
      rcases Relation.ReflTransGen.total_of_right_unique advances_rightUnique path toHalt with onward | back
      · exact onward
      · have same := halted_terminal back
        subst same
        exact .refl
    have rooted := rootPath_of_points c fromPoint
    exact ⟨(Point.normal c .halt [m]).row,
      (executionPath_nonempty_iff_multiStep (rootSystem (loopSchemas c)) _ _).mpr
        (multiStep_of_steps (S := rootSystem (loopSchemas c)) (rooted.tail (restart_rootStep c m))),
      .normal c .halt [m], rfl, .refl⟩

/-- **The system of a code and the step of the loop's program**: a firing is no step of the system or one,
and a step of the system is a path of firings. -/
def loopCorrespondence (c : Code) :
    OperationalCorrespondence (equalityGSLT ℕ (Next c)) (stepSystem ℕ (loopRules c)) :=
  (loopHosted c).comp (rootCorrespondence (O := ℕ) (loopSchemas_closed c))

/-- The one-row state of the pending evaluation of the code on a number is related to the number. -/
theorem loop_start (c : Code) (n : ℕ) : (loopCorrespondence c).related n (start c [n]) :=
  ⟨eNormal c .halt [n], ⟨.normal c .halt [n], rfl, .refl⟩, ({eNormal c .halt [n]} : Multiset Expr), rfl,
    rowState_reads _⟩

/-- **Every deterministic transition system on the naturals with a partial recursive step corresponds to the
step of a finite positive program**: the system is the system of a code, and the system of a code corresponds
to the step of the loop's twenty rules. -/
theorem hosts_partrec_system {f : List.Vector ℕ 1 →. ℕ} (partrec : Nat.Partrec' f) :
    ∃ c : Code, (∀ n m : ℕ, Next c n m ↔ m ∈ f ⟨[n], rfl⟩) ∧
      Nonempty (OperationalCorrespondence (equalityGSLT ℕ (Next c)) (stepSystem ℕ (loopRules c))) := by
  obtain ⟨c, same⟩ := next_of_partrec partrec
  exact ⟨c, same, ⟨loopCorrespondence c⟩⟩

/-! ## What the correspondence gives -/

/-- Every state the program reaches from the state of a number is related to a number the system reaches. -/
theorem reached_related {c : Code} {n : ℕ} {s : SState ℕ}
    (reached : (stepSystem ℕ (loopRules c)).MultiStep (start c [n]) s) :
    ∃ a, (equalityGSLT ℕ (Next c)).MultiStep n a ∧ (loopCorrespondence c).related a s :=
  (loopCorrespondence c).toOperationalReadback.reflectMultiStep (loop_start c n) reached

/-- **Reachable numbers, both ways**: `n` reaches `m` in one or more steps of the system exactly when the
program, run from the state of `n`, reaches a state that reads as the halted row with output `[m]`. -/
theorem reaches_iff (c : Code) (n m : ℕ) :
    Relation.TransGen (Next c) n m ↔
      ∃ s, (stepSystem ℕ (loopRules c)).MultiStep (start c [n]) s ∧ HaltedWith [m] s := by
  constructor
  · intro path
    obtain ⟨a, before, next⟩ := Relation.TransGen.tail'_iff.mp path
    exact firings_of_rootPath (loopSchemas_closed c)
      ((rootPath_of_path before).trans (rootPath_of_next next)) (rowState_reads _)
  · rintro ⟨s, reached, halted⟩
    obtain ⟨a, path, e, ⟨p, rfl, points⟩, bag, rowBag, reads⟩ := reached_related reached
    have isRow : bag = ({p.row} : Multiset Expr) := rowBag
    subst isRow
    have sameBag : ({p.row} : Multiset Expr) = {eCfg (.halt [m])} :=
      readsAs_unique (ReadsBag.readsAs reads).1 (ReadsBag.readsAs reads).2 (ReadsBag.readsAs halted).2
    have isHalt : p = .config (.halt [m]) := row_halt (Multiset.singleton_inj.mp sameBag)
    subst isHalt
    exact Relation.TransGen.tail' (steps_of_multiStep path) ((next_iff_reaches c a m).mpr points)

/-- **Accessibility of the program reflects accessibility of the system**: a state that reads as the pending
evaluation of `n`, from which the program has no infinite run, is a number from which the system has none.
Every step of the system is realized by at least one firing. -/
theorem acc_next_of_acc {c : Code} {s : SState ℕ}
    (accessible : Acc (Relation.TransGen fun next state => (stepSystem ℕ (loopRules c)).Step state next) s) :
    ∀ {n : ℕ}, ReadsBag s {eNormal c .halt [n]} → Acc (fun after before => Next c before after) n := by
  induction accessible with
  | intro s _ ih =>
      intro n reads
      refine Acc.intro n fun m next => ?_
      obtain ⟨s', path, reads'⟩ :=
        firings_of_rootTransGen (loopSchemas_closed c) (rootTransGen_of_next next) reads
      exact ih s' ((Relation.transGen_swap (r := (stepSystem ℕ (loopRules c)).Step)).mpr path) reads'

/-- **Divergence is preserved**: an infinite run of the system from `n` gives an infinite run of the program
from the state of `n`. -/
theorem infinite_run_of_source {c : Code} {n : ℕ} (run : ℕ → ℕ) (starts : run 0 = n)
    (steps : ∀ i, Next c (run i) (run (i + 1))) :
    ∃ firings : ℕ → SState ℕ, firings 0 = start c [n] ∧
      ∀ i, (stepSystem ℕ (loopRules c)).Step (firings i) (firings (i + 1)) := by
  have sourceDiverges : ¬ Acc (fun after before => Next c before after) n :=
    not_acc_iff_exists_descending_chain.mpr ⟨run, starts, steps⟩
  have targetDiverges :
      ¬ Acc (fun next state => (stepSystem ℕ (loopRules c)).Step state next) (start c [n]) :=
    fun accessible => sourceDiverges (acc_next_of_acc accessible.transGen (rowState_reads _))
  exact not_acc_iff_exists_descending_chain.mp targetDiverges

/-! ## What the correspondence does not give -/

/-- **Where the code has no value the program is never stuck**: every state it reaches from the state of the
number admits a firing. The system has no step there. -/
theorem never_stuck_of_none {c : Code} {n : ℕ} (none : c.eval [n] = Part.none) {s : SState ℕ}
    (reached : (stepSystem ℕ (loopRules c)).MultiStep (start c [n]) s) :
    ∃ s', (stepSystem ℕ (loopRules c)).Step s s' := by
  obtain ⟨a, path, e, ⟨p, rfl, points⟩, bag, rowBag, reads⟩ := reached_related reached
  have same : a = n := multiStep_stuck (next_none none) path
  rw [same] at points
  have isRow : bag = ({p.row} : Multiset Expr) := rowBag
  subst isRow
  obtain ⟨p', advanced⟩ : ∃ p', Advances p p' := by
    cases p with
    | normal c' k v => exact ⟨_, rfl⟩
    | config cfg =>
        cases cfg with
        | ret k v => exact ⟨_, rfl⟩
        | halt w =>
            have member : w ∈ c.eval [n] := (adequacy c [n] w).mp (reduces_of_points points)
            rw [none] at member
            exact absurd member (Part.notMem_none _)
  obtain ⟨g, admitted, -⟩ := firing_of_rootStep (loopSchemas_closed c) reads
    ((rootStep_loop_iff c p p'.row).mpr ⟨p', Or.inl advanced, rfl⟩)
  exact ⟨_, g, admitted, rfl⟩

/-- **Where the code has no value the program runs for ever**, while the system is stuck at the number:
divergence is not reflected, and a dead state of the system is not a dead state of the program. -/
theorem runs_forever_of_none {c : Code} {n : ℕ} (none : c.eval [n] = Part.none) :
    (∀ m, ¬ Next c n m) ∧ ∃ firings : ℕ → SState ℕ, firings 0 = start c [n] ∧
      ∀ i, (stepSystem ℕ (loopRules c)).Step (firings i) (firings (i + 1)) :=
  ⟨next_none none, exists_infinite_run fun _ reached => never_stuck_of_none none reached⟩

/-- **An instance at every number**: the code `silent` has no value anywhere, so its system has no step, and
the program runs for ever from the state of every number. -/
theorem silent_runs_forever (n : ℕ) :
    (∀ m, ¬ Next silent n m) ∧ ∃ firings : ℕ → SState ℕ, firings 0 = start silent [n] ∧
      ∀ i, (stepSystem ℕ (loopRules silent)).Step (firings i) (firings (i + 1)) :=
  runs_forever_of_none (silent_eval [n])

/-- **Halting is reflected**: a state the program reaches from the state of `n`, at which no firing is admitted,
is related to a number the system reaches from `n` and from which it has no step. -/
theorem stuck_reflected {c : Code} {n : ℕ} {s : SState ℕ}
    (reached : (stepSystem ℕ (loopRules c)).MultiStep (start c [n]) s)
    (stuck : ∀ s', ¬ (stepSystem ℕ (loopRules c)).Step s s') :
    ∃ a, Relation.ReflTransGen (Next c) n a ∧ ∀ m, ¬ Next c a m := by
  obtain ⟨a, path, e, ⟨p, rfl, points⟩, bag, rowBag, reads⟩ := reached_related reached
  have isRow : bag = ({p.row} : Multiset Expr) := rowBag
  subst isRow
  refine ⟨a, steps_of_multiStep path, fun m next => ?_⟩
  have noMove : ∀ p', ¬ Loops c p p' := fun p' looped => by
    obtain ⟨g, admitted, -⟩ := firing_of_rootStep (loopSchemas_closed c) reads
      ((rootStep_loop_iff c p p'.row).mpr ⟨p', looped, rfl⟩)
    exact stuck _ ⟨g, admitted, rfl⟩
  cases p with
  | normal c' k v => exact noMove _ (Or.inl rfl)
  | config cfg =>
      cases cfg with
      | ret k v => exact noMove _ (Or.inl rfl)
      | halt w =>
          have member : w ∈ c.eval [a] := (adequacy c [a] w).mp (reduces_of_points points)
          have same : w = [m] := Part.mem_unique member next
          subst same
          exact noMove _ (Or.inr ⟨m, rfl, rfl⟩)

/-- **An instance where the program halts**: `Code.nil` evaluates every input to the empty list, so its system
has no step, and from the state of `n` the program reaches a state at which no firing is admitted. -/
theorem nil_halts (n : ℕ) :
    (∀ m, ¬ Next Code.nil n m) ∧ ∃ s, (stepSystem ℕ (loopRules Code.nil)).MultiStep (start Code.nil [n]) s ∧
      ∀ s', ¬ (stepSystem ℕ (loopRules Code.nil)).Step s s' := by
  have value : ([] : List ℕ) ∈ Code.nil.eval [n] := by simp
  refine ⟨fun m next => (by cases Part.mem_unique value next), ?_⟩
  obtain ⟨q, isHalt, path⟩ :=
    points_of_reduces (p := .normal Code.nil .halt [n]) ((adequacy Code.nil [n] []).mpr value)
  rw [pattern_halt isHalt.symm] at path
  obtain ⟨s, run, reads⟩ := firings_of_rootPath (loopSchemas_closed Code.nil)
    (rootPath_of_points Code.nil path) (rowState_reads _)
  refine ⟨s, run, ?_⟩
  rintro s' ⟨g, admitted, rfl⟩
  obtain ⟨p', looped, -⟩ := loop_deterministic reads g admitted
  rcases looped with advanced | ⟨m, same, -⟩
  · cases advanced
  · cases same

/-- **A step of the system realized, positive control**: the successor code steps `n` to `n + 1`, and the
program reaches the halted row with output `[n + 1]`. -/
theorem succ_reaches (n : ℕ) :
    ∃ s, (stepSystem ℕ (loopRules .succ)).MultiStep (start .succ [n]) s ∧ HaltedWith [n + 1] s :=
  (reaches_iff .succ n (n + 1)).mp (.single ((next_succ n (n + 1)).mpr rfl))

/-! ## Cost -/

/-- **The cost of one step**: a step from `n` to `m` is realized from the state of `n` by a run of exactly
`k + 1` firings to a state that reads as the pending evaluation of `m`, where `k` is the number of reductions
of the authored machine from the pending evaluation of `n` to the halted configuration with output `[m]`.
That number is determined by `n` (`runFor_halt_unique`). -/
theorem step_cost {c : Code} {n m : ℕ} (next : Next c n m) :
    ∃ k, runFor k (.normal c .halt [n]) = some (.config (.halt [m])) ∧
      ∃ s', ∃ path : ExecutionPath (stepSystem ℕ (loopRules c)) (start c [n]) s',
        path.length = k + 1 ∧ ReadsBag s' {eNormal c .halt [m]} := by
  obtain ⟨k, ran⟩ := (next_iff_runFor c n m).mp next
  obtain ⟨s₁, path, length, reads⟩ := firings_of_runFor c k ran (rowState_reads (eNormal c .halt [n]))
  obtain ⟨g, admitted, reads'⟩ := firing_of_rootStep (loopSchemas_closed c) reads (restart_rootStep c m)
  have step : (stepSystem ℕ (loopRules c)).Step s₁ ((schematicStep ℕ (loopRules c)).result g admitted) :=
    ⟨g, admitted, rfl⟩
  exact ⟨k, ran, _, path.append (.cons ⟨step⟩ (.refl _)),
    (length_append_single path step).trans (congrArg (· + 1) length), reads'⟩

#print axioms multiStep_of_steps
#print axioms exists_infinite_run
#print axioms runFor_halt_unique
#print axioms reaches_iff_runFor
#print axioms succ_cost
#print axioms next_iff_reaches
#print axioms next_of_partrec
#print axioms loopSchemas_closed
#print axioms loops_rightUnique
#print axioms rootStep_loop_iff
#print axioms firings_of_rootPath
#print axioms firings_of_rootTransGen
#print axioms firings_of_runFor
#print axioms loop_deterministic
#print axioms loopHosted
#print axioms loopCorrespondence
#print axioms loop_start
#print axioms hosts_partrec_system
#print axioms reaches_iff
#print axioms acc_next_of_acc
#print axioms infinite_run_of_source
#print axioms never_stuck_of_none
#print axioms runs_forever_of_none
#print axioms silent_runs_forever
#print axioms stuck_reflected
#print axioms nil_halts
#print axioms succ_reaches
#print axioms step_cost

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.PartialRecursive
