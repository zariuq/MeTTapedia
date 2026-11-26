import Mettapedia.Machines.TIsa.Derivation.ContinuationPassing

/-!
# The defunctionalized evaluator

The third stage of the derivation. Every continuation of the CPS evaluator is replaced by first-order
data naming the closure it stood for (Reynolds's defunctionalization):

* **success continuations** (`Success`): the closure `fun m fk => solveK s gs m k fk` built at a
  premise becomes `goals gs k`; the run's success continuation becomes `fire`;
* **failure continuations** (`Failure`), the choice points: the closure resuming a scan becomes
  `scan role pattern next rest m older`; the closure trying the next rules becomes `rules rest
  older`; the run's failure continuation becomes `quiescent`.

The publication loops pass the store to the next search; their continuation becomes the
configurations `taking` and `making`.

The evaluator is now a family of first-order, tail-recursive functions, one per configuration
(`Config`), each clause a tail call. Its recursion is not structural (a resumed choice point
re-enters a scan), so it is given by its clauses as the inductive relation `Eval`, one constructor
per clause. The meaning of every configuration is the CPS computation it stands for
(`Config.meaning`, through `Success.meaning` and `Failure.meaning`).

* `eval_sound`: whatever the defunctionalized evaluator computes is the CPS meaning.
* `eval_meaning`: from **every** configuration it computes the CPS meaning; in particular it never
  gets stuck. The proof is a logical relation on continuation data, by induction on the allowance,
  the continuation data, the goals and the candidates; it needs no termination measure.
* `eval_iff`: both together, and `eval_run_iff`: started from a store, it computes `run`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation

universe u v w

/-- **Success continuations, defunctionalized**: the remaining goals of a rule with the
continuation after them, or the run's success continuation. -/
inductive Success (T : Type u) where
  | goals (gs : List (Goal T)) (next : Success T)
  | fire

/-- **Failure continuations, defunctionalized: the choice points.** A scan of the store resumed at
the remaining candidates, the rules not yet tried, or the end of the search. -/
inductive Failure (T : Type u) (V : Type v) (B : Type w) where
  | scan (role : Role) (pattern : T) (next : Success T) (rest : List (ℕ × V)) (m : Match V B)
      (older : Failure T V B)
  | rules (rest : List (Rule T)) (older : Failure T V B)
  | quiescent

/-- **Configurations**: one for each function of the defunctionalized evaluator, and the halted
outcome. Each carries the allowance and the store of the current search. -/
inductive Config (T : Type u) (V : Type v) (B : Type w) where
  | run (a : ℕ) (s : Store V)
  | rules (a : ℕ) (s : Store V) (rs : List (Rule T)) (fk : Failure T V B)
  | solve (a : ℕ) (s : Store V) (gs : List (Goal T)) (m : Match V B) (sk : Success T)
      (fk : Failure T V B)
  | scan (a : ℕ) (s : Store V) (role : Role) (pattern : T) (next : Success T)
      (cands : List (ℕ × V)) (m : Match V B) (fk : Failure T V B)
  | succeed (a : ℕ) (s : Store V) (sk : Success T) (m : Match V B) (fk : Failure T V B)
  | fail (a : ℕ) (s : Store V) (fk : Failure T V B)
  | taking (a : ℕ) (s : Store V) (os : List ℕ) (ws : List V)
  | making (a : ℕ) (s : Store V) (ws : List V)
  | halt (o : Outcome V)

variable {T : Type u} {V : Type v} {B : Type w} [DecidableEq V] (M : Matcher T V B)
  (P : List (Rule T))

/-- The run's success continuation at an allowance: pay, publish and run on, or end exhausted. -/
def fireK (a : ℕ) (s : Store V) (m : Match V B) : Outcome V :=
  match a with
  | 0 => .exhausted s
  | a' + 1 => runK M P a' (publish s m)

/-- **The meaning of a success continuation**: the CPS closure it stands for. -/
def Success.meaning (a : ℕ) (s : Store V) : Success T → Match V B → (Unit → Outcome V) → Outcome V
  | .goals gs next, m, fk => solveK M s gs m (next.meaning a s) fk
  | .fire, m, _ => fireK M P a s m

/-- **The meaning of a choice point**: the CPS closure it stands for. -/
def Failure.meaning (a : ℕ) (s : Store V) : Failure T V B → Unit → Outcome V
  | .scan role pattern next rest m older, _ =>
      scanK M role pattern (next.meaning M P a s) rest m (older.meaning a s)
  | .rules rest older, _ => rulesK M s (Success.fire.meaning M P a s) rest (older.meaning a s)
  | .quiescent, _ => .quiescent s

/-- **The meaning of a configuration**: the CPS computation it stands for. -/
def Config.meaning : Config T V B → Outcome V
  | .run a s => runK M P a s
  | .rules a s rs fk => rulesK M s (Success.fire.meaning M P a s) rs (fk.meaning M P a s)
  | .solve a s gs m sk fk => solveK M s gs m (sk.meaning M P a s) (fk.meaning M P a s)
  | .scan a s role pattern next cands m fk =>
      scanK M role pattern (next.meaning M P a s) cands m (fk.meaning M P a s)
  | .succeed a s sk m fk => sk.meaning M P a s m (fk.meaning M P a s)
  | .fail a s fk => fk.meaning M P a s ()
  | .taking a s os ws => runK M P a ((s.takeAll os).makeAll ws)
  | .making a s ws => runK M P a (s.makeAll ws)
  | .halt o => o

/-- **The defunctionalized evaluator**, one constructor for each clause, each clause a tail call. -/
inductive Eval : Config T V B → Outcome V → Prop
  | run {a : ℕ} {s : Store V} {o : Outcome V} :
      Eval (.rules a s P .quiescent) o → Eval (.run a s) o
  | rulesNil {a : ℕ} {s : Store V} {fk : Failure T V B} {o : Outcome V} :
      Eval (.fail a s fk) o → Eval (.rules a s [] fk) o
  | rulesCons {a : ℕ} {s : Store V} {r : Rule T} {rs : List (Rule T)} {fk : Failure T V B}
      {o : Outcome V} :
      Eval (.solve a s (goals r) (Match.start M) .fire (.rules rs fk)) o → Eval (.rules a s (r :: rs) fk) o
  | solveNil {a : ℕ} {s : Store V} {m : Match V B} {sk : Success T} {fk : Failure T V B}
      {o : Outcome V} :
      Eval (.succeed a s sk m fk) o → Eval (.solve a s [] m sk fk) o
  | solvePremise {a : ℕ} {s : Store V} {role : Role} {pattern : T} {gs : List (Goal T)}
      {m : Match V B} {sk : Success T} {fk : Failure T V B} {o : Outcome V} :
      Eval (.scan a s role pattern (.goals gs sk) s.occurrences m fk) o →
      Eval (.solve a s (.premise role pattern :: gs) m sk fk) o
  | solvePass {a : ℕ} {s : Store V} {d : Determinate T} {gs : List (Goal T)} {m m' : Match V B}
      {sk : Success T} {fk : Failure T V B} {o : Outcome V} :
      d.apply M s m = some m' → Eval (.solve a s gs m' sk fk) o →
      Eval (.solve a s (.determinate d :: gs) m sk fk) o
  | solveFail {a : ℕ} {s : Store V} {d : Determinate T} {gs : List (Goal T)} {m : Match V B}
      {sk : Success T} {fk : Failure T V B} {o : Outcome V} :
      d.apply M s m = none → Eval (.fail a s fk) o → Eval (.solve a s (.determinate d :: gs) m sk fk) o
  | scanNil {a : ℕ} {s : Store V} {role : Role} {pattern : T} {next : Success T} {m : Match V B}
      {fk : Failure T V B} {o : Outcome V} :
      Eval (.fail a s fk) o → Eval (.scan a s role pattern next [] m fk) o
  | scanHit {a : ℕ} {s : Store V} {role : Role} {pattern : T} {next : Success T} {x : ℕ × V}
      {rest : List (ℕ × V)} {m m' : Match V B} {fk : Failure T V B} {o : Outcome V} :
      attempt M role pattern m x = some m' →
      Eval (.succeed a s next m' (.scan role pattern next rest m fk)) o →
      Eval (.scan a s role pattern next (x :: rest) m fk) o
  | scanMiss {a : ℕ} {s : Store V} {role : Role} {pattern : T} {next : Success T} {x : ℕ × V}
      {rest : List (ℕ × V)} {m : Match V B} {fk : Failure T V B} {o : Outcome V} :
      attempt M role pattern m x = none → Eval (.scan a s role pattern next rest m fk) o →
      Eval (.scan a s role pattern next (x :: rest) m fk) o
  | succeedGoals {a : ℕ} {s : Store V} {gs : List (Goal T)} {next : Success T} {m : Match V B}
      {fk : Failure T V B} {o : Outcome V} :
      Eval (.solve a s gs m next fk) o → Eval (.succeed a s (.goals gs next) m fk) o
  | succeedExhausted {s : Store V} {m : Match V B} {fk : Failure T V B} :
      Eval (.succeed 0 s .fire m fk) (.exhausted s)
  | succeedFire {a : ℕ} {s : Store V} {m : Match V B} {fk : Failure T V B} {o : Outcome V} :
      Eval (.taking a s m.taken m.made) o → Eval (.succeed (a + 1) s .fire m fk) o
  | failScan {a : ℕ} {s : Store V} {role : Role} {pattern : T} {next : Success T}
      {rest : List (ℕ × V)} {m : Match V B} {fk : Failure T V B} {o : Outcome V} :
      Eval (.scan a s role pattern next rest m fk) o →
      Eval (.fail a s (.scan role pattern next rest m fk)) o
  | failRules {a : ℕ} {s : Store V} {rs : List (Rule T)} {fk : Failure T V B} {o : Outcome V} :
      Eval (.rules a s rs fk) o → Eval (.fail a s (.rules rs fk)) o
  | failQuiescent {a : ℕ} {s : Store V} : Eval (.fail a s .quiescent) (.quiescent s)
  | takingCons {a : ℕ} {s : Store V} {o' : ℕ} {os : List ℕ} {ws : List V} {o : Outcome V} :
      Eval (.taking a (s.remove o') os ws) o → Eval (.taking a s (o' :: os) ws) o
  | takingNil {a : ℕ} {s : Store V} {ws : List V} {o : Outcome V} :
      Eval (.making a s ws) o → Eval (.taking a s [] ws) o
  | makingCons {a : ℕ} {s : Store V} {w : V} {ws : List V} {o : Outcome V} :
      Eval (.making a (s.add w) ws) o → Eval (.making a s (w :: ws)) o
  | makingNil {a : ℕ} {s : Store V} {o : Outcome V} :
      Eval (.run a s) o → Eval (.making a s []) o
  | halt {o : Outcome V} : Eval (.halt o) o

/-- The run's CPS success continuation, read through the publication loops, is `fireK`. -/
theorem runK_rules (a : ℕ) (s : Store V) :
    runK M P a s = rulesK M s (Success.fire.meaning M P a s) P (Failure.quiescent.meaning M P a s) := by
  cases a with
  | zero => rfl
  | succ a =>
      rw [runK]
      congr 1
      funext m _
      rw [takeAllK_eq, makeAllK_eq]
      rfl

/-- **Soundness of the defunctionalized evaluator**: it computes the CPS meaning. -/
theorem eval_sound {c : Config T V B} {o : Outcome V} (evaluated : Eval M P c o) :
    o = c.meaning M P := by
  induction evaluated with
  | run _ ih => rw [ih]; exact (runK_rules M P _ _).symm
  | rulesNil _ ih => exact ih
  | rulesCons _ ih => exact ih
  | solveNil _ ih => exact ih
  | solvePremise _ ih => exact ih
  | solvePass applied _ ih => rw [ih]; simp [Config.meaning, solveK, applied]
  | solveFail applied _ ih => rw [ih]; simp [Config.meaning, solveK, applied]
  | scanNil _ ih => exact ih
  | scanHit attempted _ ih => rw [ih]; simp [Config.meaning, scanK, attempted, Failure.meaning]
  | scanMiss attempted _ ih => rw [ih]; simp [Config.meaning, scanK, attempted]
  | succeedGoals _ ih => exact ih
  | succeedExhausted => rfl
  | succeedFire _ ih => exact ih
  | failScan _ ih => exact ih
  | failRules _ ih => exact ih
  | failQuiescent => rfl
  | takingCons _ ih => exact ih
  | takingNil _ ih => exact ih
  | makingCons _ ih => exact ih
  | makingNil _ ih => exact ih
  | halt => rfl

/-! ## Totality: the logical relation on continuation data -/

/-- A success continuation is good when applying it to any match and any good choice point computes
its meaning. -/
def GoodSuccess (a : ℕ) (s : Store V) (sk : Success T) : Prop :=
  ∀ (m : Match V B) (fk : Failure T V B),
    Eval M P (.fail a s fk) (fk.meaning M P a s ()) →
    Eval M P (.succeed a s sk m fk) (sk.meaning M P a s m (fk.meaning M P a s))

theorem scan_good (a : ℕ) (s : Store V) (role : Role) (pattern : T) (next : Success T)
    (good : GoodSuccess M P a s next) :
    ∀ (cands : List (ℕ × V)) (m : Match V B) (fk : Failure T V B),
      Eval M P (.fail a s fk) (fk.meaning M P a s ()) →
      Eval M P (.scan a s role pattern next cands m fk)
        (scanK M role pattern (next.meaning M P a s) cands m (fk.meaning M P a s))
  | [], _, _, failing => .scanNil failing
  | x :: rest, m, fk, failing => by
      have resumed : Eval M P (.fail a s (.scan role pattern next rest m fk))
          ((Failure.scan role pattern next rest m fk).meaning M P a s ()) :=
        .failScan (scan_good a s role pattern next good rest m fk failing)
      cases attempted : attempt M role pattern m x with
      | some m' =>
          have hit := good m' (.scan role pattern next rest m fk) resumed
          simp only [scanK, attempted]
          exact .scanHit attempted hit
      | none =>
          simp only [scanK, attempted]
          exact .scanMiss attempted (scan_good a s role pattern next good rest m fk failing)

theorem solve_good (a : ℕ) (s : Store V) :
    ∀ (gs : List (Goal T)) (m : Match V B) (sk : Success T) (fk : Failure T V B),
      GoodSuccess M P a s sk → Eval M P (.fail a s fk) (fk.meaning M P a s ()) →
      Eval M P (.solve a s gs m sk fk) (solveK M s gs m (sk.meaning M P a s) (fk.meaning M P a s))
  | [], m, sk, fk, good, failing => .solveNil (good m fk failing)
  | .premise role pattern :: gs, m, sk, fk, good, failing => by
      have next : GoodSuccess M P a s (.goals gs sk) := fun m' fk' failing' =>
        .succeedGoals (solve_good a s gs m' sk fk' good failing')
      exact .solvePremise (scan_good M P a s role pattern _ next s.occurrences m fk failing)
  | .determinate d :: gs, m, sk, fk, good, failing => by
      cases applied : d.apply M s m with
      | some m' =>
          simp only [solveK, applied]
          exact .solvePass applied (solve_good a s gs m' sk fk good failing)
      | none =>
          simp only [solveK, applied]
          exact .solveFail applied failing

theorem publication_good (a : ℕ) (runs : ∀ s, Eval M P (.run a s) (runK M P a s)) :
    ∀ (s : Store V) (os : List ℕ) (ws : List V),
      Eval M P (.taking a s os ws) (runK M P a ((s.takeAll os).makeAll ws))
  | s, [], ws => by
      have making : ∀ (s : Store V) (ws : List V), Eval M P (.making a s ws) (runK M P a (s.makeAll ws)) := by
        intro s ws
        induction ws generalizing s with
        | nil => exact .makingNil (runs s)
        | cons w ws ih => exact .makingCons (ih (s.add w))
      exact .takingNil (making s ws)
  | s, o :: os, ws => .takingCons (publication_good a runs (s.remove o) os ws)

theorem fire_good (a : ℕ) (lower : ∀ a', a = a' + 1 → ∀ s, Eval M P (.run a' s) (runK M P a' s))
    (s : Store V) : GoodSuccess M P a s .fire := by
  intro m fk _
  cases a with
  | zero => exact .succeedExhausted
  | succ a' =>
      exact .succeedFire (publication_good M P a' (lower a' rfl) s m.taken m.made)

theorem success_good (a : ℕ) (lower : ∀ a', a = a' + 1 → ∀ s, Eval M P (.run a' s) (runK M P a' s))
    (s : Store V) : ∀ sk : Success T, GoodSuccess M P a s sk
  | .fire => fire_good M P a lower s
  | .goals gs next => fun m fk failing =>
      .succeedGoals (solve_good M P a s gs m next fk (success_good a lower s next) failing)

theorem rules_good (a : ℕ) (lower : ∀ a', a = a' + 1 → ∀ s, Eval M P (.run a' s) (runK M P a' s))
    (s : Store V) :
    ∀ (rs : List (Rule T)) (fk : Failure T V B), Eval M P (.fail a s fk) (fk.meaning M P a s ()) →
      Eval M P (.rules a s rs fk) (rulesK M s (Success.fire.meaning M P a s) rs (fk.meaning M P a s))
  | [], _, failing => .rulesNil failing
  | r :: rs, fk, failing =>
      .rulesCons (solve_good M P a s (goals r) (Match.start M) .fire (.rules rs fk)
        (fire_good M P a lower s) (.failRules (rules_good a lower s rs fk failing)))

theorem failure_good (a : ℕ) (lower : ∀ a', a = a' + 1 → ∀ s, Eval M P (.run a' s) (runK M P a' s))
    (s : Store V) : ∀ fk : Failure T V B, Eval M P (.fail a s fk) (fk.meaning M P a s ())
  | .quiescent => .failQuiescent
  | .scan role pattern next rest m older =>
      .failScan (scan_good M P a s role pattern next (success_good M P a lower s next) rest m older
        (failure_good a lower s older))
  | .rules rest older => .failRules (rules_good M P a lower s rest older (failure_good a lower s older))

/-- From every store and allowance, the defunctionalized evaluator computes the CPS run. -/
theorem run_good : ∀ (a : ℕ) (s : Store V), Eval M P (.run a s) (runK M P a s)
  | a, s => by
      have lower : ∀ a', a = a' + 1 → ∀ s, Eval M P (.run a' s) (runK M P a' s) := by
        intro a' same s'
        subst same
        exact run_good a' s'
      rw [runK_rules]
      exact .run (rules_good M P a lower s P .quiescent .failQuiescent)

/-- **Totality**: from every configuration, the defunctionalized evaluator computes its meaning. -/
theorem eval_meaning (c : Config T V B) : Eval M P c (c.meaning M P) := by
  have lower (a : ℕ) : ∀ a', a = a' + 1 → ∀ s, Eval M P (.run a' s) (runK M P a' s) :=
    fun a' _ s => run_good M P a' s
  cases c with
  | run a s => exact run_good M P a s
  | rules a s rs fk => exact rules_good M P a (lower a) s rs fk (failure_good M P a (lower a) s fk)
  | solve a s gs m sk fk =>
      exact solve_good M P a s gs m sk fk (success_good M P a (lower a) s sk)
        (failure_good M P a (lower a) s fk)
  | scan a s role pattern next cands m fk =>
      exact scan_good M P a s role pattern next (success_good M P a (lower a) s next) cands m fk
        (failure_good M P a (lower a) s fk)
  | succeed a s sk m fk =>
      exact success_good M P a (lower a) s sk m fk (failure_good M P a (lower a) s fk)
  | fail a s fk => exact failure_good M P a (lower a) s fk
  | taking a s os ws => exact publication_good M P a (run_good M P a) s os ws
  | making a s ws =>
      have taking := publication_good M P a (run_good M P a) s [] ws
      cases taking with
      | takingNil making => exact making
  | halt o => exact .halt

/-- **The defunctionalized evaluator is the CPS evaluator**, in both directions. -/
theorem eval_iff (c : Config T V B) (o : Outcome V) : Eval M P c o ↔ o = c.meaning M P :=
  ⟨eval_sound M P, fun same => same ▸ eval_meaning M P c⟩

/-- **Started from a store, the defunctionalized evaluator computes the run.** -/
theorem eval_run_iff (a : ℕ) (s : Store V) (o : Outcome V) :
    Eval M P (.run a s) o ↔ o = run M P a s := by
  rw [eval_iff]
  exact Iff.of_eq (congrArg (o = ·) (runK_eq M P a s))

end Mettapedia.Machines.TIsa.Derivation
