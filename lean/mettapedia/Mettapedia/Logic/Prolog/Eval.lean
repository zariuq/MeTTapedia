import Mettapedia.Logic.Prolog.Core

/-!
# Prolog Operational Semantics

Formalizes the **list-monad** (backtracking) operational semantics of the Prolog
built-in goal language defined in `Core.lean`.

## Central judgment

`PrologEval oracle goal env result` means:
> Starting from environment `env`, running `goal` (with oracle `oracle` for `reduceCall`)
> produces `result : PrologEvalResult`.

`result.answers` is the (ordered) list of answer environments.
`result.isCut` indicates whether a `!` was executed.

## Design: self-referential hypothesis pattern (avoids mutual inductive)

For constructors that need to run a sub-goal on each element of a list (conjunction,
spaceMatch), we use a **pairs witness**:

```lean
(pairs : List (PEnv × List PEnv))
(h_each : ∀ p ∈ pairs, PrologEval oracle g p.1 (.normal p.2))
```

`PrologEval` appears in the *conclusion* of `h_each` — a positive position — so Lean's
strict positivity checker accepts this without a `mutual` block.

## Cut semantics

| Context | Cut behavior |
|---------|-------------|
| `conj g1 g2` | run g2 left-to-right on g1 answers; any cut in g1/g2 propagates after current branch |
| `disj g1 g2` | cut from g1 is CAUGHT (g2 pruned, signal absorbed) |
| `findall v g` | cut barrier: g's cut is absorbed |
| `once g`      | cut barrier |
| `ite c t e`   | cut in c absorbed; cut in t/e propagates |

## References

- Lloyd, *Foundations of Logic Programming* (1987), Ch. 9
- Sterling & Shapiro, *The Art of Prolog* (1994), Ch. 11
- PeTTa `translator.pl`, `translate_expr/3`
-/

namespace Mettapedia.Logic.Prolog

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-! ## Abstract Space Interface -/

/-- The only space operation the Prolog layer needs:
    match a pattern against the space, returning all matching facts. -/
structure PrologSpace where
  matchFacts : Pattern → List Pattern

/-! ## Eval Oracle -/

/-- Oracle for `reduceCall` and `spaceMatch`: plugs the MeTTa evaluator into Prolog.
    Instantiated to `PeTTaEval` in `OSLF.PeTTa.PrologBridge`. -/
structure EvalOracle where
  space : PrologSpace
  call  : List Pattern → List Pattern → Prop
  /-- Match oracle: `matchEval pat tmpl outs` means matching `pat` against
      the space, instantiating `tmpl` with each binding set, produces `outs`.
      This threads the pattern-match bindings into template instantiation,
      matching Prolog's variable-sharing semantics for `match/3`. -/
  matchEval : Pattern → Pattern → List Pattern → Prop

/-! ## Evaluation Result (with cut signal) -/

/-- Prolog evaluation result.
    - `normal envs`    — backtracking produced `envs`.
    - `cutThrown envs` — a `!` was executed; `envs` gathered before the cut. -/
inductive PrologEvalResult where
  | normal    : List PEnv → PrologEvalResult
  | cutThrown : List PEnv → PrologEvalResult
  deriving Repr

namespace PrologEvalResult

/-- Answers regardless of cut. -/
def answers : PrologEvalResult → List PEnv
  | .normal envs    => envs
  | .cutThrown envs => envs

/-- True iff cut was thrown. -/
def isCut : PrologEvalResult → Bool
  | .normal _    => false
  | .cutThrown _ => true

end PrologEvalResult

/-! ## Prolog Evaluation Relation -/

/-- **Prolog evaluation judgment** (with cut signal).

    `PrologEval oracle goal env result` means: evaluating `goal` from `env`
    under oracle `oracle` yields `result`. -/
inductive PrologEval (oracle : EvalOracle) : PrologGoal → PEnv → PrologEvalResult → Prop where

  /-- `true` — succeed once. -/
  | succeed_eval (env : PEnv) :
      PrologEval oracle .succeed env (.normal [env])

  /-- `fail` — no answers. -/
  | fail_eval (env : PEnv) :
      PrologEval oracle .fail env (.normal [])

  /-- `!` — succeed once and throw cut. -/
  | cut_eval (env : PEnv) :
      PrologEval oracle .cut env (.cutThrown [env])

  /-- `G1, G2` — g1 succeeds normally; run g2 on each answer from g1.
      Uses a *pairs witness* `pairs : List (PEnv × List PEnv)` where each pair
      `(e, es)` records: evaluate g2 from `e`, producing answers `es`. -/
  | conj_normal (g1 g2 : PrologGoal) (env : PEnv) (envs1 : List PEnv)
      (pairs : List (PEnv × List PEnv))
      (h1 : PrologEval oracle g1 env (.normal envs1))
      (h_dom : envs1 = pairs.map Prod.fst)
      (h_each : ∀ p ∈ pairs, PrologEval oracle g2 p.1 (.normal p.2)) :
      PrologEval oracle (.conj g1 g2) env (.normal (pairs.flatMap Prod.snd))

  /-- `G1, G2` — g1 normal; g2 throws cut for the first time at one branch.
      Prefix branches are evaluated normally; suffix branches are pruned. -/
  | conj_g2_cut (g1 g2 : PrologGoal) (env : PEnv) (envs1 : List PEnv)
      (pref : List (PEnv × List PEnv)) (cutEnv : PEnv) (cutOut : List PEnv)
      (suff : List PEnv)
      (h1 : PrologEval oracle g1 env (.normal envs1))
      (h_split : envs1 = pref.map Prod.fst ++ cutEnv :: suff)
      (h_prefix_each : ∀ p ∈ pref, PrologEval oracle g2 p.1 (.normal p.2))
      (h_cut : PrologEval oracle g2 cutEnv (.cutThrown cutOut)) :
      PrologEval oracle (.conj g1 g2) env
        (.cutThrown (pref.flatMap Prod.snd ++ cutOut))

  /-- `G1, G2` — g1 throws cut; g2 still runs on each answer from g1, then cut propagates.
      This matches Prolog behavior where `!` commits choice points but does not
      skip subsequent goals in the conjunction. -/
  | conj_g1_cut (g1 g2 : PrologGoal) (env : PEnv) (envs1 : List PEnv)
      (pairs : List (PEnv × List PEnv))
      (h1 : PrologEval oracle g1 env (.cutThrown envs1))
      (h_dom : envs1 = pairs.map Prod.fst)
      (h_each : ∀ p ∈ pairs, PrologEval oracle g2 p.1 (.normal p.2)) :
      PrologEval oracle (.conj g1 g2) env (.cutThrown (pairs.flatMap Prod.snd))

  /-- `G1, G2` — g1 already threw cut; while running g2, an inner cut is thrown
      on one branch. Prefix branches are evaluated normally; suffix branches are pruned. -/
  | conj_g1_cut_g2_cut (g1 g2 : PrologGoal) (env : PEnv) (envs1 : List PEnv)
      (pref : List (PEnv × List PEnv)) (cutEnv : PEnv) (cutOut : List PEnv)
      (suff : List PEnv)
      (h1 : PrologEval oracle g1 env (.cutThrown envs1))
      (h_split : envs1 = pref.map Prod.fst ++ cutEnv :: suff)
      (h_prefix_each : ∀ p ∈ pref, PrologEval oracle g2 p.1 (.normal p.2))
      (h_cut : PrologEval oracle g2 cutEnv (.cutThrown cutOut)) :
      PrologEval oracle (.conj g1 g2) env
        (.cutThrown (pref.flatMap Prod.snd ++ cutOut))

  /-- `G1 ; G2` — g1 throws cut; cut is CAUGHT here (g2 pruned, signal absorbed). -/
  | disj_g1_cut (g1 g2 : PrologGoal) (env : PEnv) (envs1 : List PEnv)
      (h1 : PrologEval oracle g1 env (.cutThrown envs1)) :
      PrologEval oracle (.disj g1 g2) env (.normal envs1)

  /-- `G1 ; G2` — g1 succeeds normally; concatenate answers from both branches. -/
  | disj_normal (g1 g2 : PrologGoal) (env : PEnv)
      (envs1 envs2 : List PEnv)
      (h1 : PrologEval oracle g1 env (.normal envs1))
      (h2 : PrologEval oracle g2 env (.normal envs2)) :
      PrologEval oracle (.disj g1 g2) env (.normal (envs1 ++ envs2))

  /-- `G1 ; G2` — g1 normal, g2 throws cut. -/
  | disj_g2_cut (g1 g2 : PrologGoal) (env : PEnv)
      (envs1 envs2 : List PEnv)
      (h1 : PrologEval oracle g1 env (.normal envs1))
      (h2 : PrologEval oracle g2 env (.cutThrown envs2)) :
      PrologEval oracle (.disj g1 g2) env (.cutThrown (envs1 ++ envs2))

  /-- `(Cond -> Then ; Else)` — cond has answers; commit to first, run Then. -/
  | ite_then (cond then_ else_ : PrologGoal) (env : PEnv)
      (cond_first : PEnv) (cond_rest : List PEnv)
      (r_cond r_then : PrologEvalResult)
      (h_cond  : PrologEval oracle cond env r_cond)
      (h_first : r_cond.answers = cond_first :: cond_rest)
      (h_then  : PrologEval oracle then_ cond_first r_then) :
      PrologEval oracle (.ite cond then_ else_) env r_then

  /-- `(Cond -> Then ; Else)` — cond has no answers; run Else. -/
  | ite_else (cond then_ else_ : PrologGoal) (env : PEnv)
      (r_cond r_else : PrologEvalResult)
      (h_cond  : PrologEval oracle cond env r_cond)
      (h_empty : r_cond.answers = [])
      (h_else  : PrologEval oracle else_ env r_else) :
      PrologEval oracle (.ite cond then_ else_) env r_else

  /-- `once(G)` — take first answer (cut barrier). -/
  | once_some (g : PrologGoal) (env : PEnv)
      (r : PrologEvalResult) (first_ans : PEnv) (rest : List PEnv)
      (h       : PrologEval oracle g env r)
      (h_first : r.answers = first_ans :: rest) :
      PrologEval oracle (.once g) env (.normal [first_ans])

  | once_none (g : PrologGoal) (env : PEnv)
      (r : PrologEvalResult)
      (h       : PrologEval oracle g env r)
      (h_empty : r.answers = []) :
      PrologEval oracle (.once g) env (.normal [])

  /-- `\+ G` — succeed iff G fails. -/
  | neg_succ (g : PrologGoal) (env : PEnv) (r : PrologEvalResult)
      (h       : PrologEval oracle g env r)
      (h_empty : r.answers = []) :
      PrologEval oracle (.neg g) env (.normal [env])

  | neg_fail (g : PrologGoal) (env : PEnv) (r : PrologEvalResult)
      (first : PEnv) (rest : List PEnv)
      (h    : PrologEval oracle g env r)
      (h_ne : r.answers = first :: rest) :
      PrologEval oracle (.neg g) env (.normal [])

  /-- `var(P)` — succeeds iff `P` stays a free variable after applying env bindings. -/
  | isVar_succ (p : Pattern) (env : PEnv) (v : String)
      (h : applyBindings env p = .fvar v) :
      PrologEval oracle (.isVar p) env (.normal [env])

  | isVar_fail (p : Pattern) (env : PEnv)
      (h : ¬ ∃ v : String, applyBindings env p = .fvar v) :
      PrologEval oracle (.isVar p) env (.normal [])

  /-- `P = Q` — pattern unification under the current environment.
      Existing environment bindings are applied before matching. -/
  | unify_succ (p q : Pattern) (env : PEnv) (bs : Bindings)
      (h : bs ∈ matchPattern (applyBindings env p) (applyBindings env q)) :
      PrologEval oracle (.unify p q) env (.normal [env ++ bs])

  | unify_fail (p q : Pattern) (env : PEnv)
      (h : matchPattern (applyBindings env p) (applyBindings env q) = []) :
      PrologEval oracle (.unify p q) env (.normal [])

  /-- `P \= Q` — unification failure under the current environment. -/
  | notUnify_succ (p q : Pattern) (env : PEnv)
      (h : matchPattern (applyBindings env p) (applyBindings env q) = []) :
      PrologEval oracle (.notUnify p q) env (.normal [env])

  | notUnify_fail (p q : Pattern) (env : PEnv)
      (bs : Bindings) (rest : List Bindings)
      (h : matchPattern (applyBindings env p) (applyBindings env q) = bs :: rest) :
      PrologEval oracle (.notUnify p q) env (.normal [])

  /-- `findall(V, G, _)` — all-solutions collection (cut barrier).
      Runs G to exhaustion, collects values of V from each answer environment,
      returns singleton answer with V bound to the collected list. -/
  | findall_eval (v : String) (g : PrologGoal) (env : PEnv)
      (r : PrologEvalResult) (vals : List Pattern)
      (h      : PrologEval oracle g env r)
      (h_vals : vals = r.answers.filterMap (fun e => e.lookup v)) :
      PrologEval oracle (.findall v g) env
        (.normal [env.insert v (Pattern.mkList vals)])

  /-- `match(&self, Pat, Tmpl)` — match Pat against space, instantiate Tmpl,
      return all instantiated templates.  The `matchEval` oracle computes the
      match results (threading bindings from `matchPattern` into `applyBindings`). -/
  | spaceMatch_eval (pat tmpl : Pattern) (env : PEnv)
      (outs : List Pattern)
      (h_match : oracle.matchEval pat tmpl outs) :
      PrologEval oracle (.spaceMatch pat tmpl) env
        (.normal (outs.map (fun out => env.insert "Out" out)))

  /-- `reduce([F|Args], Out)` — MeTTa evaluator oracle. -/
  | reduceCall_eval (args : List Pattern) (env : PEnv) (outs : List Pattern)
      (h : oracle.call args outs) :
      PrologEval oracle (.reduceCall args) env
        (.normal (outs.map (fun out => env.insert "Out" out)))

/-! ## Derived: PrologConjAll -/

/-- **Sequential conjunction**: running `g` on each environment in `envs_in`
    and collecting all answers into `result`.

    Defined as a Prop (not an inductive) using the pairs-witness encoding. -/
def PrologConjAll (oracle : EvalOracle) (g : PrologGoal)
    (envs_in result : List PEnv) : Prop :=
  ∃ (pairs : List (PEnv × List PEnv)),
    envs_in = pairs.map Prod.fst ∧
    result = pairs.flatMap Prod.snd ∧
    ∀ p ∈ pairs, PrologEval oracle g p.1 (.normal p.2)

namespace PrologConjAll

/-- Empty list → empty result. -/
theorem nil {oracle : EvalOracle} {g : PrologGoal} :
    PrologConjAll oracle g [] [] :=
  ⟨[], rfl, rfl, fun _ h => by simp at h⟩

/-- Singleton: g evaluates on env with answers `envs`. -/
theorem singleton {oracle : EvalOracle} {g : PrologGoal} {env : PEnv}
    {envs : List PEnv}
    (h : PrologEval oracle g env (.normal envs)) :
    PrologConjAll oracle g [env] envs := by
  refine ⟨[(env, envs)], ?_, ?_, ?_⟩
  · simp
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact h

end PrologConjAll

/-! ## Basic Properties -/

/-- succeed gives exactly one answer. -/
theorem prologEval_succeed {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle .succeed env (.normal [env]) :=
  PrologEval.succeed_eval env

/-- fail gives no answers. -/
theorem prologEval_fail {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle .fail env (.normal []) :=
  PrologEval.fail_eval env

/-- once produces at most one answer. -/
theorem prologEval_once_length {oracle : EvalOracle} {g : PrologGoal}
    {env : PEnv} {r : PrologEvalResult}
    (h : PrologEval oracle (.once g) env r) :
    r.answers.length ≤ 1 := by
  cases h with
  | once_some => simp [PrologEvalResult.answers]
  | once_none => simp [PrologEvalResult.answers]

/-- neg succeeds iff inner goal fails. -/
theorem prologEval_neg_iff {oracle : EvalOracle} {g : PrologGoal} {env : PEnv} :
    (∃ r, PrologEval oracle (.neg g) env r ∧ r.answers = [env]) ↔
    (∃ r, PrologEval oracle g env r ∧ r.answers = []) := by
  constructor
  · rintro ⟨r, h, hr⟩
    cases h with
    | neg_succ _ _ r' h_g h_e => exact ⟨_, h_g, h_e⟩
    | neg_fail _ _ _ _ _ _ h_ne =>
        simp only [PrologEvalResult.answers] at hr
        exact absurd hr (by simp)
  · rintro ⟨r, h_g, h_e⟩
    exact ⟨.normal [env], PrologEval.neg_succ g env r h_g h_e, rfl⟩

/-- findall is a cut barrier: the outer result is always `normal`. -/
theorem findall_cut_barrier {oracle : EvalOracle} {v : String} {g : PrologGoal}
    {env : PEnv} {r : PrologEvalResult}
    (h : PrologEval oracle (.findall v g) env r) : ¬ r.isCut := by
  cases h; simp [PrologEvalResult.isCut]

/-- disj with g1 cutting absorbs the cut. -/
theorem disj_g1_cut_normal {oracle : EvalOracle} {g1 g2 : PrologGoal}
    {env : PEnv} {envs1 : List PEnv}
    (h : PrologEval oracle g1 env (.cutThrown envs1)) :
    ∃ r, PrologEval oracle (.disj g1 g2) env r ∧ ¬ r.isCut :=
  ⟨.normal envs1, PrologEval.disj_g1_cut g1 g2 env envs1 h,
   by simp [PrologEvalResult.isCut]⟩

/-- Example: succeed → disj → answers are the expected env. -/
theorem example_disj_succeed {oracle : EvalOracle} {env : PEnv} :
    ∃ r, PrologEval oracle (.disj .succeed .fail) env r ∧ r.answers = [env] :=
  ⟨.normal ([env] ++ []),
   PrologEval.disj_normal .succeed .fail env [env] []
     (PrologEval.succeed_eval env) (PrologEval.fail_eval env),
   by simp [PrologEvalResult.answers]⟩

/-- **disjList evaluation**: running `disjList` over a list of goals, where each goal
    evaluates normally, concatenates all answers.

    Uses a pairs witness `(goal, answers)` to express the "each goal evaluates to its
    answers" premise without mutual induction. -/
theorem prologEval_disjList_normal {oracle : EvalOracle} {env : PEnv}
    (pairs : List (PrologGoal × List PEnv))
    (h_each : ∀ p ∈ pairs, PrologEval oracle p.1 env (.normal p.2)) :
    PrologEval oracle (disjList (pairs.map Prod.fst)) env
      (.normal (pairs.flatMap Prod.snd)) := by
  induction pairs with
  | nil => simp only [List.map_nil, List.flatMap_nil, disjList]; exact PrologEval.fail_eval env
  | cons p ps ih =>
    simp only [List.map_cons, List.flatMap_cons]
    have h1 : PrologEval oracle p.1 env (.normal p.2) :=
      h_each p List.mem_cons_self
    have h2 : PrologEval oracle (disjList (ps.map Prod.fst)) env (.normal (ps.flatMap Prod.snd)) :=
      ih (fun q hq => h_each q (List.mem_cons_of_mem p hq))
    -- Case: ps is empty or non-empty determines whether disjList uses singleton or disj case
    match ps with
    | [] =>
        simp only [List.map_nil, disjList, List.flatMap_nil, List.append_nil]
        exact h1
    | q :: qs =>
        simp only [List.map_cons, disjList]
        exact PrologEval.disj_normal p.1 (disjList (q.1 :: (qs.map Prod.fst)))
          env p.2 ((q :: qs).flatMap Prod.snd) h1 h2

/-- **disjList soundness**: if evaluating `disjList goals` produces answer `ans`,
    then some `g ∈ goals` produces `ans` when evaluated directly.

    This is the "left-to-right" soundness companion to `prologEval_disjList_normal`. -/
theorem prologEval_disjList_sound {oracle : EvalOracle} {env : PEnv} {ans : PEnv}
    (goals : List PrologGoal)
    (r : PrologEvalResult)
    (h : PrologEval oracle (disjList goals) env r)
    (h_ans : ans ∈ r.answers) :
    ∃ g ∈ goals, ∃ r', PrologEval oracle g env r' ∧ ans ∈ r'.answers := by
  induction goals generalizing r with
  | nil =>
      simp only [disjList] at h
      cases h; simp [PrologEvalResult.answers] at h_ans
  | cons g gs ih =>
      match gs with
      | [] =>
          -- disjList [g] = g; witness is g itself
          simp only [disjList] at h
          exact ⟨g, List.mem_cons_self, r, h, h_ans⟩
      | g2 :: rest =>
          -- disjList (g :: g2 :: rest) = .disj g (disjList (g2 :: rest))
          simp only [disjList] at h
          cases h with
          | disj_normal _ _ _ envs1 envs2 h1 h2 =>
              -- r = .normal (envs1 ++ envs2)
              simp only [PrologEvalResult.answers] at h_ans
              rw [List.mem_append] at h_ans
              rcases h_ans with h | h
              · -- ans came from g
                exact ⟨g, List.mem_cons_self, .normal envs1, h1, h⟩
              · -- ans came from disjList gs
                obtain ⟨g', hg', r', hr', hans⟩ := ih (.normal envs2) h2 h
                exact ⟨g', List.mem_cons_of_mem g hg', r', hr', hans⟩
          | disj_g1_cut _ _ _ envs1 h1 =>
              -- g cuts; cut is absorbed; r = .normal envs1
              simp only [PrologEvalResult.answers] at h_ans
              exact ⟨g, List.mem_cons_self, .cutThrown envs1, h1, h_ans⟩
          | disj_g2_cut _ _ _ envs1 envs2 h1 h2 =>
              -- g normal, disjList gs cuts; r = .cutThrown (envs1 ++ envs2)
              simp only [PrologEvalResult.answers] at h_ans
              rw [List.mem_append] at h_ans
              rcases h_ans with h | h
              · exact ⟨g, List.mem_cons_self, .normal envs1, h1, h⟩
              · obtain ⟨g', hg', r', hr', hans⟩ := ih (.cutThrown envs2) h2 h
                exact ⟨g', List.mem_cons_of_mem g hg', r', hr', hans⟩

end Mettapedia.Logic.Prolog
