import Mettapedia.Machines.TIsa.Derivation.Defunctionalized
import Mettapedia.Machines.BoundedDeterministicRun

/-!
# The abstract machine of the transform calculus

The fourth stage of the derivation. Each clause of the defunctionalized evaluator is a tail call, so
each is one transition of a machine whose states are the configurations (`step`). The machine has
eighteen transitions; `Derivation.Instructions` reads the instruction set off them.

* `eval_steps`: every evaluation is a run of the machine to its outcome.
* `steps_eval`: every run of the machine to a halted configuration is an evaluation.
* `machine_iff`: from every configuration, the machine halts with an outcome exactly when that
  outcome is the configuration's meaning; from a store, exactly when it is the evaluator's `run`
  (`machine_run_iff`).
* **A complete run exists** from every configuration (`complete_run`), so the machine never gets
  stuck and never runs for ever; with the existing bounded driver it halts within some fuel
  (`complete_run_bounded`). Its outcome is unique (`outcome_unique`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation

universe u v w

variable {T : Type u} {V : Type v} {B : Type w} [DecidableEq V] (M : Matcher T V B)
  (P : List (Rule T))

/-- **The abstract machine**: one transition for each clause of the defunctionalized evaluator. -/
def step : Config T V B → Option (Config T V B)
  | .run a s => some (.rules a s P .quiescent)
  | .rules a s [] fk => some (.fail a s fk)
  | .rules a s (r :: rs) fk => some (.solve a s (goals r) (Match.start M) .fire (.rules rs fk))
  | .solve a s [] m sk fk => some (.succeed a s sk m fk)
  | .solve a s (.premise role pattern :: gs) m sk fk =>
      some (.scan a s role pattern (.goals gs sk) s.occurrences m fk)
  | .solve a s (.determinate d :: gs) m sk fk =>
      match d.apply M s m with
      | some m' => some (.solve a s gs m' sk fk)
      | none => some (.fail a s fk)
  | .scan a s _ _ _ [] _ fk => some (.fail a s fk)
  | .scan a s role pattern next (x :: rest) m fk =>
      match attempt M role pattern m x with
      | some m' => some (.succeed a s next m' (.scan role pattern next rest m fk))
      | none => some (.scan a s role pattern next rest m fk)
  | .succeed a s (.goals gs next) m fk => some (.solve a s gs m next fk)
  | .succeed 0 s .fire _ _ => some (.halt (.exhausted s))
  | .succeed (a + 1) s .fire m _ => some (.taking a s m.taken m.made)
  | .fail a s (.scan role pattern next rest m fk) => some (.scan a s role pattern next rest m fk)
  | .fail a s (.rules rs fk) => some (.rules a s rs fk)
  | .fail _ s .quiescent => some (.halt (.quiescent s))
  | .taking a s (o :: os) ws => some (.taking a (s.remove o) os ws)
  | .taking a s [] ws => some (.making a s ws)
  | .making a s (w :: ws) => some (.making a (s.add w) ws)
  | .making a s [] => some (.run a s)
  | .halt _ => none

/-- The outcome of a halted configuration. -/
def Config.outcome? : Config T V B → Option (Outcome V)
  | .halt o => some o
  | _ => none

/-- Runs of the machine. -/
abbrev Steps : Config T V B → Config T V B → Prop :=
  Relation.ReflTransGen fun c c' => step M P c = some c'

theorem step_halt (o : Outcome V) : step M P (.halt o) = none := rfl

/-- **Every evaluation is a run of the machine.** -/
theorem eval_steps {c : Config T V B} {o : Outcome V} (evaluated : Eval M P c o) :
    Steps M P c (.halt o) := by
  induction evaluated with
  | run _ ih => exact .head rfl ih
  | rulesNil _ ih => exact .head rfl ih
  | rulesCons _ ih => exact .head rfl ih
  | solveNil _ ih => exact .head rfl ih
  | solvePremise _ ih => exact .head rfl ih
  | solvePass applied _ ih => exact .head (by simp [step, applied]) ih
  | solveFail applied _ ih => exact .head (by simp [step, applied]) ih
  | scanNil _ ih => exact .head rfl ih
  | scanHit attempted _ ih => exact .head (by simp [step, attempted]) ih
  | scanMiss attempted _ ih => exact .head (by simp [step, attempted]) ih
  | succeedGoals _ ih => exact .head rfl ih
  | succeedExhausted => exact .single rfl
  | succeedFire _ ih => exact .head rfl ih
  | failScan _ ih => exact .head rfl ih
  | failRules _ ih => exact .head rfl ih
  | failQuiescent => exact .single rfl
  | takingCons _ ih => exact .head rfl ih
  | takingNil _ ih => exact .head rfl ih
  | makingCons _ ih => exact .head rfl ih
  | makingNil _ ih => exact .head rfl ih
  | halt => exact .refl

/-- A transition followed by an evaluation is an evaluation. -/
theorem eval_of_step {c c' : Config T V B} {o : Outcome V} (stepped : step M P c = some c')
    (evaluated : Eval M P c' o) : Eval M P c o := by
  cases c with
  | run a s =>
      cases stepped
      exact .run evaluated
  | rules a s rs fk =>
      cases rs with
      | nil => cases stepped; exact .rulesNil evaluated
      | cons r rs => cases stepped; exact .rulesCons evaluated
  | solve a s gs m sk fk =>
      cases gs with
      | nil => cases stepped; exact .solveNil evaluated
      | cons g gs =>
          cases g with
          | premise role pattern => cases stepped; exact .solvePremise evaluated
          | determinate d =>
              simp only [step] at stepped
              cases applied : d.apply M s m with
              | some m' =>
                  rw [applied] at stepped
                  cases stepped
                  exact .solvePass applied evaluated
              | none =>
                  rw [applied] at stepped
                  cases stepped
                  exact .solveFail applied evaluated
  | scan a s role pattern next cands m fk =>
      cases cands with
      | nil => cases stepped; exact .scanNil evaluated
      | cons x rest =>
          simp only [step] at stepped
          cases attempted : attempt M role pattern m x with
          | some m' =>
              rw [attempted] at stepped
              cases stepped
              exact .scanHit attempted evaluated
          | none =>
              rw [attempted] at stepped
              cases stepped
              exact .scanMiss attempted evaluated
  | succeed a s sk m fk =>
      cases sk with
      | goals gs next => cases stepped; exact .succeedGoals evaluated
      | fire =>
          cases a with
          | zero =>
              cases stepped
              cases evaluated
              exact .succeedExhausted
          | succ a => cases stepped; exact .succeedFire evaluated
  | fail a s fk =>
      cases fk with
      | scan role pattern next rest m fk => cases stepped; exact .failScan evaluated
      | rules rs fk => cases stepped; exact .failRules evaluated
      | quiescent =>
          cases stepped
          cases evaluated
          exact .failQuiescent
  | taking a s os ws =>
      cases os with
      | nil => cases stepped; exact .takingNil evaluated
      | cons o os => cases stepped; exact .takingCons evaluated
  | making a s ws =>
      cases ws with
      | nil => cases stepped; exact .makingNil evaluated
      | cons w ws => cases stepped; exact .makingCons evaluated
  | halt o => cases stepped

/-- **Every run of the machine to a halted configuration is an evaluation.** -/
theorem steps_eval {c : Config T V B} {o : Outcome V} (ran : Steps M P c (.halt o)) :
    Eval M P c o := by
  induction ran using Relation.ReflTransGen.head_induction_on with
  | refl => exact .halt
  | head stepped _ ih => exact eval_of_step M P stepped ih

/-- **The machine halts with exactly the meaning of the configuration it starts from.** -/
theorem machine_iff (c : Config T V B) (o : Outcome V) :
    Steps M P c (.halt o) ↔ o = c.meaning M P :=
  ⟨fun ran => eval_sound M P (steps_eval M P ran), fun same => same ▸ eval_steps M P (eval_meaning M P c)⟩

/-- **Started from a store, the machine halts with exactly the evaluator's run.** -/
theorem machine_run_iff (a : ℕ) (s : Store V) (o : Outcome V) :
    Steps M P (.run a s) (.halt o) ↔ o = run M P a s := by
  rw [machine_iff]
  exact Iff.of_eq (congrArg (o = ·) (runK_eq M P a s))

/-- **A complete run exists from every configuration.** -/
theorem complete_run (c : Config T V B) : Steps M P c (.halt (c.meaning M P)) :=
  eval_steps M P (eval_meaning M P c)

/-- **The bounded driver completes**: some fuel brings every configuration to its halted outcome,
and every larger fuel stays there. -/
theorem complete_run_bounded (c : Config T V B) :
    ∃ fuel, ∀ more, BoundedDeterministicRun.run (step M P) (fuel + more) c = .halt (c.meaning M P) := by
  obtain ⟨fuel, continues⟩ := BoundedDeterministicRun.run_suffix_of_path (step M P) (complete_run M P c)
  refine ⟨fuel, fun more => ?_⟩
  rw [continues more]
  exact BoundedDeterministicRun.run_of_none (step M P) _ (step_halt M P _) more

/-- **The bounded driver computes the run**: with enough fuel, the machine started from a store halts
with the evaluator's outcome. -/
theorem driver_run (a : ℕ) (s : Store V) :
    ∃ fuel, ∀ more, (BoundedDeterministicRun.run (step M P) (fuel + more) (.run a s)).outcome? =
      some (run M P a s) := by
  obtain ⟨fuel, completes⟩ := complete_run_bounded M P (.run a s)
  refine ⟨fuel, fun more => ?_⟩
  rw [completes more]
  exact congrArg some (runK_eq M P a s)

/-- **What the bounded driver reports is the run**: whenever the machine halts within the fuel, its
outcome is the evaluator's. -/
theorem driver_sound (a fuel : ℕ) (s : Store V) (o : Outcome V)
    (halted : (BoundedDeterministicRun.run (step M P) fuel (.run a s)).outcome? = some o) :
    o = run M P a s := by
  have reached := BoundedDeterministicRun.run_reachable (step M P) fuel (.run a s)
  cases ended : BoundedDeterministicRun.run (step M P) fuel (.run a s) with
  | halt o' =>
      rw [ended] at halted reached
      simp only [Config.outcome?, Option.some.injEq] at halted
      subst halted
      exact (machine_run_iff M P a s _).mp reached
  | _ => rw [ended] at halted; cases halted

/-- The outcome of a complete run is unique. -/
theorem outcome_unique {c : Config T V B} {o o' : Outcome V} (first : Steps M P c (.halt o))
    (second : Steps M P c (.halt o')) : o = o' :=
  ((machine_iff M P c o).mp first).trans ((machine_iff M P c o').mp second).symm

/-! ## The search phase of the machine -/

/-- **The machine's search finds the first match**: from the goals of a rule, it fails to the
choice point it was given when there is no match, and otherwise reaches the success continuation
with the first match. -/
theorem solve_first (a : ℕ) (s : Store V) :
    ∀ (gs : List (Goal T)) (m : Match V B) (sk : Success T) (fk : Failure T V B),
      (solve M s gs m = [] → Steps M P (.solve a s gs m sk fk) (.fail a s fk)) ∧
      (∀ first rest, solve M s gs m = first :: rest →
        ∃ fk', Steps M P (.solve a s gs m sk fk) (.succeed a s sk first fk'))
  | [], m, sk, fk => by
      refine ⟨fun empty => by simp [solve] at empty, ?_⟩
      intro first rest found
      simp only [solve, List.cons.injEq] at found
      obtain ⟨rfl, -⟩ := found
      exact ⟨fk, .single rfl⟩
  | .determinate d :: gs, m, sk, fk => by
      cases applied : d.apply M s m with
      | none =>
          refine ⟨fun _ => .single (by simp [step, applied]), ?_⟩
          intro first rest found
          simp [solve, applied] at found
      | some m' =>
          have stepped : step M P (.solve a s (.determinate d :: gs) m sk fk) = some (.solve a s gs m' sk fk) := by
            simp [step, applied]
          have same : solve M s (.determinate d :: gs) m = solve M s gs m' := by simp [solve, applied]
          obtain ⟨noMatch, firstMatch⟩ := solve_first a s gs m' sk fk
          refine ⟨fun empty => .head stepped (noMatch (same ▸ empty)), ?_⟩
          intro first rest found
          obtain ⟨fk', reached⟩ := firstMatch first rest (same ▸ found)
          exact ⟨fk', .head stepped reached⟩
  | .premise role pattern :: gs, m, sk, fk => by
      let F : (ℕ × V) → List (Match V B) := fun x =>
        match attempt M role pattern m x with
        | some m' => solve M s gs m'
        | none => []
      have unfolded : solve M s (.premise role pattern :: gs) m = s.occurrences.flatMap F := rfl
      have scan : ∀ (cands : List (ℕ × V)) (fk : Failure T V B),
          (cands.flatMap F = [] →
            Steps M P (.scan a s role pattern (.goals gs sk) cands m fk) (.fail a s fk)) ∧
          (∀ first rest, cands.flatMap F = first :: rest →
            ∃ fk', Steps M P (.scan a s role pattern (.goals gs sk) cands m fk) (.succeed a s sk first fk')) := by
        intro cands
        induction cands with
        | nil =>
            intro fk
            exact ⟨fun _ => .single rfl, fun first rest found => by simp at found⟩
        | cons x rest ih =>
            intro fk
            cases tried : attempt M role pattern m x with
            | none =>
                have stepped : step M P (.scan a s role pattern (.goals gs sk) (x :: rest) m fk) =
                    some (.scan a s role pattern (.goals gs sk) rest m fk) := by
                  simp [step, tried]
                have here : F x = [] := by simp only [F, tried]
                obtain ⟨noMatch, firstMatch⟩ := ih fk
                refine ⟨fun empty => .head stepped (noMatch ?_), ?_⟩
                · rw [List.flatMap_cons, here, List.nil_append] at empty
                  exact empty
                · intro first rest' found
                  rw [List.flatMap_cons, here, List.nil_append] at found
                  obtain ⟨fk', reached⟩ := firstMatch first rest' found
                  exact ⟨fk', .head stepped reached⟩
            | some m' =>
                have stepped : step M P (.scan a s role pattern (.goals gs sk) (x :: rest) m fk) =
                    some (.succeed a s (.goals gs sk) m' (.scan role pattern (.goals gs sk) rest m fk)) := by
                  simp [step, tried]
                have here : F x = solve M s gs m' := by simp only [F, tried]
                have resumed : Steps M P (.scan a s role pattern (.goals gs sk) (x :: rest) m fk)
                    (.solve a s gs m' sk (.scan role pattern (.goals gs sk) rest m fk)) :=
                  .head stepped (.single rfl)
                obtain ⟨innerNone, innerSome⟩ := solve_first a s gs m' sk (.scan role pattern (.goals gs sk) rest m fk)
                obtain ⟨noMatch, firstMatch⟩ := ih fk
                constructor
                · intro empty
                  rw [List.flatMap_cons, here, List.append_eq_nil_iff] at empty
                  exact resumed.trans ((innerNone empty.1).trans (.head rfl (noMatch empty.2)))
                · intro first rest' found
                  rw [List.flatMap_cons, here] at found
                  cases inner : solve M s gs m' with
                  | nil =>
                      rw [inner, List.nil_append] at found
                      obtain ⟨fk', reached⟩ := firstMatch first rest' found
                      exact ⟨fk', resumed.trans ((innerNone inner).trans (.head rfl reached))⟩
                  | cons head tail =>
                      rw [inner, List.cons_append, List.cons.injEq] at found
                      obtain ⟨rfl, -⟩ := found
                      obtain ⟨fk', reached⟩ := innerSome _ tail inner
                      exact ⟨fk', resumed.trans reached⟩
      obtain ⟨noMatch, firstMatch⟩ := scan s.occurrences fk
      refine ⟨fun empty => .head rfl (noMatch (unfolded ▸ empty)), ?_⟩
      intro first rest found
      obtain ⟨fk', reached⟩ := firstMatch first rest (unfolded ▸ found)
      exact ⟨fk', .head rfl reached⟩

/-- **The machine's rule search finds the first firing.** -/
theorem rules_first (a : ℕ) (s : Store V) :
    ∀ (rs : List (Rule T)) (fk : Failure T V B),
      ((firings M rs s).map Prod.snd = [] → Steps M P (.rules a s rs fk) (.fail a s fk)) ∧
      (∀ first rest, (firings M rs s).map Prod.snd = first :: rest →
        ∃ fk', Steps M P (.rules a s rs fk) (.succeed a s .fire first fk'))
  | [], fk => ⟨fun _ => .single rfl, fun first rest found => by simp [firings] at found⟩
  | r :: rs, fk => by
      have entered : Steps M P (.rules a s (r :: rs) fk)
          (.solve a s (goals r) (Match.start M) .fire (.rules rs fk)) := .single rfl
      have split : (firings M (r :: rs) s).map Prod.snd =
          solve M s (goals r) (Match.start M) ++ (firings M rs s).map Prod.snd := by
        simp [firings, List.map_flatMap, Function.comp_def]
      obtain ⟨innerNone, innerSome⟩ := solve_first M P a s (goals r) (Match.start M) .fire (.rules rs fk)
      obtain ⟨noMatch, firstMatch⟩ := rules_first a s rs fk
      rw [split]
      constructor
      · intro empty
        rw [List.append_eq_nil_iff] at empty
        exact entered.trans ((innerNone empty.1).trans (.head rfl (noMatch empty.2)))
      · intro first rest found
        cases inner : solve M s (goals r) (Match.start M) with
        | nil =>
            rw [inner, List.nil_append] at found
            obtain ⟨fk', reached⟩ := firstMatch first rest found
            exact ⟨fk', entered.trans ((innerNone inner).trans (.head rfl reached))⟩
        | cons head tail =>
            rw [inner, List.cons_append, List.cons.injEq] at found
            obtain ⟨rfl, -⟩ := found
            obtain ⟨fk', reached⟩ := innerSome _ tail inner
            exact ⟨fk', entered.trans reached⟩

theorem publication_steps (a : ℕ) :
    ∀ (s : Store V) (os : List ℕ) (ws : List V),
      Steps M P (.taking a s os ws) (.run a ((s.takeAll os).makeAll ws))
  | s, [], ws => by
      have making : ∀ (s : Store V) (ws : List V), Steps M P (.making a s ws) (.run a (s.makeAll ws)) := by
        intro s ws
        induction ws generalizing s with
        | nil => exact .single rfl
        | cons w ws ih => exact .head rfl (ih (s.add w))
      exact .head rfl (making s ws)
  | s, o :: os, ws => .head rfl (publication_steps a (s.remove o) os ws)

/-- **One firing of the machine**: from a store with a firing and an allowance left, the machine
reaches the next search on the store with the first firing published, one unit less. -/
theorem search_commits (a : ℕ) (s : Store V) (f : Rule T × Match V B)
    (rest : List (Rule T × Match V B)) (first : firings M P s = f :: rest) :
    Steps M P (.run (a + 1) s) (.run a (publish s f.2)) := by
  obtain ⟨_, firstMatch⟩ := rules_first M P (a + 1) s P .quiescent
  obtain ⟨fk', reached⟩ := firstMatch f.2 (rest.map Prod.snd) (by rw [first]; rfl)
  have toCommit : Steps M P (.run (a + 1) s) (.succeed (a + 1) s .fire f.2 fk') := .head rfl reached
  have commit : step M P (.succeed (a + 1) s .fire f.2 fk') =
      some (Config.taking a s f.2.taken f.2.made) := rfl
  exact toCommit.trans (.head commit (publication_steps M P a s f.2.taken f.2.made))

end Mettapedia.Machines.TIsa.Derivation
