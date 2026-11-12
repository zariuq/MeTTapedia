import Mettapedia.Languages.MeTTa.PeTTa.LibTransformComplete

/-!
# Driving a program of rules: one run of the step, to a quiescent configuration

A program is a list of rules, each a kernel of reads and takes guarded by absences with a
template made into the store (`MadeRule`). A pass calls each rule's transform in order; the
driver repeats passes until the program is idle or its fuel is spent.

* `pass`, `drive`: the model's pass and driver.
* `executable_append`: executable words of the step compose.
* `call_executable`, `pass_executable`, `drive_executable`: a call, a pass and a drive are
  executable words from a known configuration, and what they leave knows the store the
  model leaves. Every firing of the word is a rule of the program with fresh variables.
* `drive_is_run`: **a drive is one run of `firstOrder atomAction label`.** At its end the
  knowledge is consistent and, under every solution of it, the labels of the last rows are
  the atoms of the store the driver returns. **If the program is idle at that store, no
  rule of the program is admitted by the step at the run's last configuration**
  (`Quiescent`): the run is complete for the program, which is more than the driver having
  stopped.

Examples: `Controls.drive_pToQ` (the driver turns every `(p x)` into `(q x)` and reaches an
idle store) and `Controls.no_fuel_not_idle` (with no fuel the store is returned as it is,
and it is not idle: stopping is not halting).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
  (Selection RuleInstance Configuration SubstitutionAction EquationStore)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison
  (atomAction)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
  (Firing Executable follow firstOrder executable_iff_run follow_eq_last)
open LibTransform

variable {O : Type} [DecidableEq O]

/-! ## The model's driver -/

/-- One pass: each rule's call, in order, on the store the earlier calls left. -/
def pass (program : List MadeRule) (s : Store) : Store :=
  program.foldl (fun store r => ((transformInto r.sources r.template store).drain).2) s

instance (program : List MadeRule) (s : Store) : Decidable (Idle program s) := by
  unfold Idle
  infer_instance

/-- Passes until the program is idle or the fuel is spent. -/
def drive : Nat → List MadeRule → Store → Store
  | 0, _, s => s
  | fuel + 1, program, s => if Idle program s then s else drive fuel program (pass program s)

/-! ## Executable words compose -/

/-- A word executable to a configuration, followed by a word executable from it. -/
theorem executable_append {label : O → Atom} :
    ∀ (first : List (Firing Atom Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst O))
      {second : List (Firing Atom Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst O)}
      {C D : Configuration Atom O},
      Executable atomAction label C first → follow label C first = D →
      Executable atomAction label D second →
      Executable atomAction label C (first ++ second) ∧
        follow label C (first ++ second) = follow label D second
  | [], _, _, _, _, ends, later => by
      have same : follow label _ ([] : List (Firing Atom _ O)) = _ := ends
      simp only [follow] at same
      subst same
      exact ⟨later, rfl⟩
  | f :: rest, _, _, _, exec, ends, later => by
      obtain ⟨valid, restExec⟩ := exec
      have both := executable_append rest restExec ends later
      exact ⟨⟨valid, both.1⟩, both.2⟩

/-! ## A call, a pass, a drive -/

/-- What a word of the program's rules is: each firing is a rule of the program with fresh
variables and no predicate query. -/
def OfProgram (program : List MadeRule)
    (word : List (Firing Atom Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst O)) : Prop :=
  ∀ f ∈ word, ∃ r ∈ program, ∃ m,
    f.rule = (madeRule r.pats r.absents r.template).map (rename m) ∧ f.queries = []

/-- A call of a rule from a known configuration. -/
theorem call_executable {label : O → Atom}
    (supply : ∀ (X : Finset O) (t : Atom), ∃ o, o ∉ X ∧ label o = t)
    {K : EquationStore Atom} {n : Nat} {rows : List O} {s : Store}
    (knows : Knows label K n rows s) (r : MadeRule) (closed : Closed r.pats r.template) :
    ∃ (word : List (Firing Atom Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst O))
      (rows' : List O) (K' : EquationStore Atom) (n' : Nat),
      Executable atomAction label ⟨K, rows.toFinset⟩ word ∧
      follow label ⟨K, rows.toFinset⟩ word = ⟨K', rows'.toFinset⟩ ∧
      Knows label K' n' rows' ((transformInto r.sources r.template s).drain).2 ∧
      OfProgram [r] word := by
  obtain ⟨word, rows', K', n', exec, ends, knows', rules, _⟩ :=
    made_fold_executable supply r.pats r.absents r.template closed _
      (fun g member => guarded_proposal_fits knows.ground member) ([], s) rows K n knows
  refine ⟨word, rows', K', n', exec, ends, ?_, ?_⟩
  · rw [transformInto, transformWith_drain]
    exact knows'
  · intro f member
    obtain ⟨m, isRule, noQueries⟩ := rules f member
    exact ⟨r, List.mem_singleton_self _, m, isRule, noQueries⟩

/-- A pass of a program from a known configuration. -/
theorem pass_executable {label : O → Atom}
    (supply : ∀ (X : Finset O) (t : Atom), ∃ o, o ∉ X ∧ label o = t) :
    ∀ (rules : List MadeRule) (program : List MadeRule),
      (∀ r ∈ rules, r ∈ program ∧ Closed r.pats r.template) →
      ∀ {K : EquationStore Atom} {n : Nat} {rows : List O} {s : Store},
        Knows label K n rows s →
        ∃ (word : List (Firing Atom Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst O))
          (rows' : List O) (K' : EquationStore Atom) (n' : Nat),
          Executable atomAction label ⟨K, rows.toFinset⟩ word ∧
          follow label ⟨K, rows.toFinset⟩ word = ⟨K', rows'.toFinset⟩ ∧
          Knows label K' n' rows' (pass rules s) ∧ OfProgram program word
  | [], _, _, K, n, rows, s, knows =>
      ⟨[], rows, K, n, knows.consistent, rfl, knows, fun f member => by simp at member⟩
  | r :: rules, program, good, K, n, rows, s, knows => by
      obtain ⟨first, mid, K₁, n₁, exec₁, ends₁, knows₁, ofRule⟩ :=
        call_executable supply knows r (good r (List.mem_cons_self ..)).2
      obtain ⟨second, rows', K', n', exec₂, ends₂, knows₂, ofRest⟩ :=
        pass_executable supply rules program
          (fun r' member => good r' (List.mem_cons_of_mem _ member)) knows₁
      obtain ⟨exec, ends⟩ := executable_append first exec₁ ends₁ exec₂
      refine ⟨first ++ second, rows', K', n', exec, ends.trans ends₂, ?_, ?_⟩
      · show Knows label K' n' rows' (pass rules
          ((transformInto r.sources r.template s).drain).2)
        exact knows₂
      · intro f member
        rcases List.mem_append.mp member with inFirst | inSecond
        · obtain ⟨r', isR, m, isRule, noQueries⟩ := ofRule f inFirst
          rw [List.mem_singleton] at isR
          subst isR
          exact ⟨r', (good r' (List.mem_cons_self ..)).1, m, isRule, noQueries⟩
        · exact ofRest f inSecond

/-- A drive of a program from a known configuration. -/
theorem drive_executable {label : O → Atom}
    (supply : ∀ (X : Finset O) (t : Atom), ∃ o, o ∉ X ∧ label o = t)
    (program : List MadeRule) (closed : ∀ r ∈ program, Closed r.pats r.template) :
    ∀ (fuel : Nat) {K : EquationStore Atom} {n : Nat} {rows : List O} {s : Store},
      Knows label K n rows s →
      ∃ (word : List (Firing Atom Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst O))
        (rows' : List O) (K' : EquationStore Atom) (n' : Nat),
        Executable atomAction label ⟨K, rows.toFinset⟩ word ∧
        follow label ⟨K, rows.toFinset⟩ word = ⟨K', rows'.toFinset⟩ ∧
        Knows label K' n' rows' (drive fuel program s) ∧ OfProgram program word
  | 0, K, n, rows, s, knows =>
      ⟨[], rows, K, n, knows.consistent, rfl, knows, fun f member => by simp at member⟩
  | fuel + 1, K, n, rows, s, knows => by
      by_cases idle : Idle program s
      · refine ⟨[], rows, K, n, knows.consistent, rfl, ?_, fun f member => by simp at member⟩
        simp only [drive, idle, if_true]
        exact knows
      · obtain ⟨first, mid, K₁, n₁, exec₁, ends₁, knows₁, ofFirst⟩ :=
          pass_executable supply program program
            (fun r member => ⟨member, closed r member⟩) knows
        obtain ⟨second, rows', K', n', exec₂, ends₂, knows₂, ofSecond⟩ :=
          drive_executable supply program closed fuel knows₁
        obtain ⟨exec, ends⟩ := executable_append first exec₁ ends₁ exec₂
        refine ⟨first ++ second, rows', K', n', exec, ends.trans ends₂, ?_, ?_⟩
        · simp only [drive, idle, if_false]
          exact knows₂
        · intro f member
          rcases List.mem_append.mp member with inFirst | inSecond
          · exact ofFirst f inFirst
          · exact ofSecond f inSecond

/-- **A drive is one run of the first-order step, and an idle end is a quiescent one.** On a
ground store represented by `rows`, with a supply of fresh occurrences, the driver's work
on a program whose templates are closed in their kernels is a run of
`firstOrder atomAction label` from the configuration with the rows' occurrences and no
knowledge. At its end the knowledge is consistent and, under every solution of it, the
labels of the last rows are the atoms of the store the driver returns. If the program is
idle at that store, the step admits no rule of the program at the run's last
configuration. -/
theorem drive_is_run {label : O → Atom}
    (supply : ∀ (X : Finset O) (t : Atom), ∃ o, o ∉ X ∧ label o = t)
    {rows : List O} {s : Store} (rep : Represents label rows s)
    (ground : ∀ a ∈ s, isGroundAtom a = true)
    (program : List MadeRule) (closed : ∀ r ∈ program, Closed r.pats r.template)
    (fuel : Nat) :
    ∃ (run : (firstOrder atomAction label).Run (⟨[], rows.toFinset⟩ : Configuration Atom O))
      (rows' : List O) (n : Nat),
      run.last.present = rows'.toFinset ∧
      Knows label run.last.equations n rows' (drive fuel program s) ∧
      (Idle program (drive fuel program s) →
        Quiescent label program run.last.equations n rows') := by
  obtain ⟨word, rows', K', n', exec, ends, knows', _⟩ :=
    drive_executable supply program closed fuel (knows_of_represents rep ground)
  obtain ⟨run, isWord, _⟩ := (executable_iff_run atomAction label _ word).mp exec
  have last : run.last = ⟨K', rows'.toFinset⟩ := by
    rw [← follow_eq_last atomAction label run, isWord]
    exact ends
  refine ⟨run, rows', n', by rw [last], by rw [last]; exact knows', ?_⟩
  intro idle
  rw [last]
  exact (quiescent_iff_idle supply knows' program closed).mpr idle

namespace Controls

/-- The driver turns `(p a)` into `(q a)` and stops at an idle store. -/
theorem drive_pToQ :
    drive 3 [pToQ] [.expression [.symbol "p", a], b] = [b, .expression [.symbol "q", a]] ∧
      Idle [pToQ] (drive 3 [pToQ] [.expression [.symbol "p", a], b]) := by
  decide

/-- With no fuel the store is returned as it is, and the program is not idle there: a
driver that stopped has not shown that nothing can fire. -/
theorem no_fuel_not_idle :
    drive 0 [pToQ] [.expression [.symbol "p", a], b] = [.expression [.symbol "p", a], b] ∧
      ¬ Idle [pToQ] (drive 0 [pToQ] [.expression [.symbol "p", a], b]) := by
  decide

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep
