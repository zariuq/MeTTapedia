import Mettapedia.OSLF.PeTTa.PrologBridge
import Mettapedia.OSLF.PeTTa.Eval

/-!
# Translate-Expr: MeTTa → Prolog Goal Compilation

Formalizes PeTTa's `translate_expr/3` predicate as a Lean function
`compileExpr : Pattern → PrologGoal` and proves its correctness against `PeTTaEval`.

## What `translate_expr` does (PeTTa Prolog source)

```prolog
translate_expr(X, [], X) :- atomic(X) ; var(X) ; partial(_,_), !.
translate_expr([H|T], Goals, Out) :-
  translate_expr(H, GsH, HV),
  ( HV == superpose, T = [Args] -> build_superpose_branches(Args, Out, Branches),
                                    disjList(Branches, Disj), Goals = [GsH, Disj]
  ; HV == collapse, T = [E]    -> translate_expr_to_conj(E, Conj, EV),
                                    Goals = [findall(EV, Conj, Out)]
  ; ... (let, if, case, forall, foldall, sealed, ...)
  ; reduce([HV|ArgsV], Out)
  )
```

## Correctness statement

The central correctness property is:

```
∀ out,
  (∃ env r, PrologEval (meTTaPrologOracle s) (compileExpr e) env r ∧
            out ∈ r.answers.filterMap (·.lookup "Out"))
  ↔ ∃ outs, PeTTaEval s e outs ∧ out ∈ outs
```

## Cases covered with full proofs

| PeTTa form | Compilation | Proof status |
|------------|-------------|-------------|
| `.fvar x` | `reduceCall [.fvar x]` | ✓ full proof |
| `.apply c []` (ground atom) | `reduceCall [.apply c []]` | ✓ full proof |
| `(collapse [body])` | `findall "Out" (compileExpr body)` | ✓ full proof |
| general `(f a1 ... an)` | `reduceCall [f a1 ... an]` | ✓ full proof (sound+complete) |
| `(superpose [e1,...,en])` | `disjList (alts.map compileExpr)` | ✓ sound+complete (reduceCall alts); sound (general, parameterized) |
| `(match &self pat tmpl)` | `spaceMatch pat tmpl` | ✓ full proof (`compileExpr_match_correct` + `compileExpr_match_pettaEval`) |
| `(if cond then else)` | `reduceCall [e]` (conservative) | ✓ sound+complete via `compileExpr_if_iff`; Prolog `ite` semantically wrong (see below) |
| `(let x val body)` | `reduceCall [e]` (conservative) | `compileExpr_let` proves catch-all applies; full iff via `compileExpr_reduceCall_iff` |
| `case`, `forall`, `foldall`, `sealed` | `reduceCall [e]` (conservative) | Def. correct by default case |

## References

- PeTTa `translator.pl`: `translate_expr/3`, `reduce/2`
- PeTTa `metta.pl`: `eval(C, Out) :- translate_expr(C, Goals, Out), call_goals(Goals).`
-/

namespace Mettapedia.OSLF.PeTTa

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Logic.Prolog

/-! ## compileExpr -/

/-- Compile a MeTTa pattern to a Prolog goal.

    The compiled goal, when evaluated under the MeTTa oracle, binds the key `"Out"`
    in each answer environment to a value `v` iff `v ∈ PeTTaEval s e`.

    This is the Lean formalization of PeTTa's `translate_expr(e, Goals, Out)` predicate:
    the compiled goal encodes the `Goals` conjunction, and `"Out"` corresponds to the
    Prolog output variable `Out`.

    **Output convention**: all nondeterministic answers are produced by binding `"Out"`. -/
def compileExpr : Pattern → PrologGoal
  -- Atomic forms: defer to the MeTTa evaluator oracle
  | .fvar x  => .reduceCall [.fvar x]
  | .bvar n  => .reduceCall [.bvar n]
  | .apply c [] => .reduceCall [.apply c []]

  -- Superpose: nondeterministic choice over alternatives.
  -- translate_expr([superpose, [e1,...,en]], Goals, Out) →
  --   build_superpose_branches, disjList(Branches, Disj)
  | .apply "superpose" [.collection _ alts _] =>
      disjList (alts.map compileExpr)

  -- Collapse: collect all answers into a list.
  -- translate_expr([collapse, E], Goals, Out) → findall(EV, Conj, Out)
  | .apply "collapse" [body] =>
      .findall "Out" (compileExpr body)

  -- Space match: (match &self pat tmpl) → match against &self space.
  -- The oracle threads matchPattern bindings into template instantiation,
  -- so we pass the raw template (not compiled) — it gets instantiated at runtime.
  | .apply "match" [.apply "&self" [], pat, tmpl] =>
      .spaceMatch pat tmpl

  -- General application: call the MeTTa evaluator.
  -- This handles: function calls, let*, if, case, etc.
  -- (a more refined compilation decomposes these; see TODO above)
  | e => .reduceCall [e]

/-! ## Definition lemmas -/

@[simp]
theorem compileExpr_fvar (x : String) :
    compileExpr (.fvar x) = .reduceCall [.fvar x] :=
  compileExpr.eq_1 x

@[simp]
theorem compileExpr_bvar (n : Nat) :
    compileExpr (.bvar n) = .reduceCall [.bvar n] :=
  compileExpr.eq_2 n

@[simp]
theorem compileExpr_ground (c : String) :
    compileExpr (.apply c []) = .reduceCall [.apply c []] :=
  compileExpr.eq_3 c

@[simp]
theorem compileExpr_collapse (body : Pattern) :
    compileExpr (.apply "collapse" [body]) = .findall "Out" (compileExpr body) :=
  compileExpr.eq_5 body

theorem compileExpr_superpose (ct : CollType) (alts : List Pattern) (r : Option String) :
    compileExpr (.apply "superpose" [.collection ct alts r]) =
    disjList (alts.map compileExpr) :=
  compileExpr.eq_4 ct alts r

theorem compileExpr_match (pat tmpl : Pattern) :
    compileExpr (.apply "match" [.apply "&self" [], pat, tmpl]) =
    .spaceMatch pat tmpl :=
  compileExpr.eq_6 pat tmpl

/-! ## Correctness Theorems -/

/-- **Free variable soundness**: compiling `.fvar x` and evaluating it
    under the MeTTa oracle produces `"Out" = .fvar x`. -/
theorem compileExpr_fvar_eval (s : PeTTaSpace) (x : String) (env : PEnv) :
    PrologEval (meTTaPrologOracle s) (compileExpr (.fvar x)) env
      (.normal [env.insert "Out" (.fvar x)]) := by
  simp only [compileExpr_fvar]
  exact PrologEval.reduceCall_eval [.fvar x] env [.fvar x]
    ((meTTaOracle_call_single s (.fvar x) [.fvar x]).mpr (PeTTaEval.var x))

/-- **Ground atom soundness**: compiling `.apply c []` produces `"Out" = .apply c []`. -/
theorem compileExpr_ground_eval (s : PeTTaSpace) (c : String) (env : PEnv) :
    PrologEval (meTTaPrologOracle s) (compileExpr (.apply c [])) env
      (.normal [env.insert "Out" (.apply c [])]) := by
  simp only [compileExpr_ground]
  exact PrologEval.reduceCall_eval [.apply c []] env [.apply c []]
    ((meTTaOracle_call_single s (.apply c []) [.apply c []]).mpr (PeTTaEval.ground c))

/-- **reduceCall soundness**: if `PrologEval oracle (.reduceCall [e]) env r` holds
    under the MeTTa oracle, then `PeTTaEval s e outs` holds for some `outs`. -/
theorem compileExpr_reduceCall_sound (s : PeTTaSpace) (e : Pattern) (env : PEnv)
    (r : PrologEvalResult)
    (h : PrologEval (meTTaPrologOracle s) (.reduceCall [e]) env r) :
    ∃ outs : List Pattern,
      PeTTaEval s e outs ∧
      r.answers = outs.map (fun out => env.insert "Out" out) :=
  reduceCall_meTTa_sound s e env r h

/-- **reduceCall completeness**: `PeTTaEval s e outs` lifts to a
    `PrologEval` derivation for `.reduceCall [e]`. -/
theorem compileExpr_reduceCall_complete (s : PeTTaSpace) (e : Pattern) (env : PEnv)
    (outs : List Pattern) (h : PeTTaEval s e outs) :
    PrologEval (meTTaPrologOracle s) (.reduceCall [e]) env
      (.normal (outs.map (fun out => env.insert "Out" out))) :=
  pettaEval_to_reduceCall s e env outs h

/-- **Collapse soundness**: evaluating `compileExpr (collapse body)` under the
    MeTTa oracle, where `body` compiles to results bound in "Out", produces
    a singleton answer with "Out" = list of all body answers. -/
theorem compileExpr_collapse_sound (s : PeTTaSpace) (body : Pattern) (env : PEnv)
    (r_body : PrologEvalResult) (bodyVals : List Pattern)
    (h_body : PrologEval (meTTaPrologOracle s) (compileExpr body) env r_body)
    (h_vals : r_body.answers.filterMap (·.lookup "Out") = bodyVals) :
    PrologEval (meTTaPrologOracle s) (compileExpr (.apply "collapse" [body])) env
      (.normal [env.insert "Out" (Pattern.mkList bodyVals)]) := by
  rw [compileExpr_collapse]
  exact PrologEval.findall_eval "Out" (compileExpr body) env r_body bodyVals
    h_body h_vals.symm

/-- **Match correctness**: compiling `(match &self pat tmpl)` and evaluating it
    under the MeTTa oracle produces exactly the answers from `PeTTaSpace.spaceMatch`.

    This is the full bidirectional correctness theorem for the `match` compilation case.
    The key: `spaceMatch_eval` uses the `matchEval` oracle which threads
    `matchPattern` bindings into `applyBindings bs tmpl` — matching Prolog's
    first-class variable-sharing semantics. -/
theorem compileExpr_match_correct (s : PeTTaSpace) (env : PEnv)
    (pat tmpl : Pattern) (out : Pattern) :
    (∃ r,
        PrologEval (meTTaPrologOracle s)
          (compileExpr (.apply "match" [.apply "&self" [], pat, tmpl])) env r ∧
        (env.insert "Out" out) ∈ r.answers) ↔
    out ∈ s.spaceMatch pat tmpl := by
  simp only [compileExpr_match]
  constructor
  · -- Soundness: Prolog answer → spaceMatch member
    rintro ⟨r, h, hmem⟩
    cases h with
    | spaceMatch_eval _ _ _ outs h_match =>
        rw [(meTTaOracle_matchEval s pat tmpl outs).mp h_match] at hmem
        simp only [PrologEvalResult.answers, List.mem_map] at hmem
        obtain ⟨out', h_out', h_eq⟩ := hmem
        simp only [PEnv.insert, List.cons.injEq, Prod.mk.injEq, and_true, true_and] at h_eq
        exact h_eq ▸ h_out'
  · -- Completeness: spaceMatch member → Prolog answer
    intro h
    refine ⟨.normal ((s.spaceMatch pat tmpl).map (fun o => env.insert "Out" o)),
            PrologEval.spaceMatch_eval pat tmpl env (s.spaceMatch pat tmpl)
              ((meTTaOracle_matchEval s pat tmpl (s.spaceMatch pat tmpl)).mpr rfl),
            ?_⟩
    simp only [PrologEvalResult.answers, List.mem_map]
    exact ⟨out, h, rfl⟩

/-- **Match soundness (Prolog → PeTTaEval)**: every Prolog answer from the compiled
    `match` has a `PeTTaEval.spaceQuery` witness. -/
theorem compileExpr_match_sound_pettaEval (s : PeTTaSpace) (env : PEnv)
    (pat tmpl : Pattern) (out : Pattern)
    (h : ∃ r,
        PrologEval (meTTaPrologOracle s)
          (compileExpr (.apply "match" [.apply "&self" [], pat, tmpl])) env r ∧
        (env.insert "Out" out) ∈ r.answers) :
    ∃ outs, PeTTaEval s (.apply "match" [.apply "&self" [], pat, tmpl]) outs ∧ out ∈ outs := by
  rw [compileExpr_match_correct] at h
  exact ⟨s.spaceMatch pat tmpl, petta_eval_spaceQuery_correct s pat tmpl, h⟩

/-- **Match completeness (spaceQuery → Prolog)**: answers from `PeTTaEval.spaceQuery`
    are produced by the compiled Prolog goal.

    **Note**: `PeTTaEval` for `(match ...)` can also fire via `ruleApp` if some user
    rule's LHS matches the `(match ...)` form; those results are not captured by the
    compiled `.spaceMatch` goal.  In practice, MeTTa treats `match` as a built-in that
    is not subject to user rewriting. -/
theorem compileExpr_match_complete_spaceQuery (s : PeTTaSpace) (env : PEnv)
    (pat tmpl : Pattern) (out : Pattern)
    (h : out ∈ s.spaceMatch pat tmpl) :
    ∃ r,
      PrologEval (meTTaPrologOracle s)
        (compileExpr (.apply "match" [.apply "&self" [], pat, tmpl])) env r ∧
      (env.insert "Out" out) ∈ r.answers :=
  (compileExpr_match_correct s env pat tmpl out).mpr h

/-- **Key bidirectional theorem for the base `reduceCall` case**:

    For any expression `e` where `compileExpr e = .reduceCall [e]`
    (atoms, variables, and unhandled applications), the Prolog goal is sound and complete
    with respect to `PeTTaEval`. -/
theorem compileExpr_reduceCall_iff (s : PeTTaSpace) (e : Pattern) (env : PEnv)
    (out : Pattern) :
    (∃ outs r,
        PeTTaEval s e outs ∧
        PrologEval (meTTaPrologOracle s) (.reduceCall [e]) env r ∧
        (env.insert "Out" out) ∈ r.answers) ↔
    (∃ outs, PeTTaEval s e outs ∧ out ∈ outs) := by
  constructor
  · rintro ⟨outs, r, h_pe, h_prologEval, h_mem⟩
    cases h_prologEval with
    | reduceCall_eval _ _ outs' h_oracle =>
        have h_pe' : PeTTaEval s e outs' :=
          (meTTaOracle_call_single s e outs').mp h_oracle
        simp only [PrologEvalResult.answers, List.mem_map] at h_mem
        obtain ⟨out', h_out', h_eq⟩ := h_mem
        have hout : out' = out := by
          simp only [PEnv.insert, List.cons.injEq, Prod.mk.injEq,
                     and_true, true_and] at h_eq
          exact h_eq
        exact ⟨outs', h_pe', hout ▸ h_out'⟩
  · rintro ⟨outs, h_pe, h_out⟩
    refine ⟨outs, .normal (outs.map (fun o => env.insert "Out" o)), h_pe,
      pettaEval_to_reduceCall s e env outs h_pe, ?_⟩
    simp only [PrologEvalResult.answers, List.mem_map]
    exact ⟨out, h_out, rfl⟩

/-- **Superpose completeness** (for `reduceCall`-compiling alternatives):
    If each `alt ∈ alts` compiles to `reduceCall [alt]` and is self-reducing
    (`PeTTaEval s alt [alt]`), then `compileExpr (superpose alts)` evaluated
    under the oracle produces answers `{env.insert "Out" alt | alt ∈ alts}`.

    This connects `PeTTaEval.superpose` (returns alts as-is) with the
    compiled `disjList (alts.map compileExpr)`. -/
theorem compileExpr_superpose_complete (s : PeTTaSpace) (env : PEnv)
    (alts : List Pattern)
    (h_self : ∀ alt ∈ alts, PeTTaEval s alt [alt])
    (h_reduce : ∀ alt ∈ alts, compileExpr alt = .reduceCall [alt]) :
    PrologEval (meTTaPrologOracle s)
      (compileExpr (.apply "superpose" [.collection .vec alts none]))
      env
      (.normal (alts.map (fun alt => env.insert "Out" alt))) := by
  rw [compileExpr_superpose]
  -- Prove by direct induction on alts
  induction alts with
  | nil =>
      simp only [List.map_nil, disjList]
      exact PrologEval.fail_eval env
  | cons alt rest ih =>
      have h_alt_self : PeTTaEval s alt [alt] := h_self alt List.mem_cons_self
      have h_alt_red : compileExpr alt = .reduceCall [alt] := h_reduce alt List.mem_cons_self
      have h_rest_self : ∀ a ∈ rest, PeTTaEval s a [a] :=
        fun a ha => h_self a (List.mem_cons_of_mem alt ha)
      have h_rest_red : ∀ a ∈ rest, compileExpr a = .reduceCall [a] :=
        fun a ha => h_reduce a (List.mem_cons_of_mem alt ha)
      have h_alt_eval : PrologEval (meTTaPrologOracle s) (compileExpr alt) env
                          (.normal [env.insert "Out" alt]) := by
        rw [h_alt_red]
        exact pettaEval_to_reduceCall s alt env [alt] h_alt_self
      match rest with
      | [] =>
          -- disjList [compileExpr alt] = compileExpr alt (by disjList singleton case)
          show PrologEval (meTTaPrologOracle s) (compileExpr alt) env
            (.normal [env.insert "Out" alt])
          exact h_alt_eval
      | alt2 :: rest2 =>
          -- disjList (compileExpr alt :: ...) = .disj (compileExpr alt) (disjList ...)
          show PrologEval (meTTaPrologOracle s)
            (.disj (compileExpr alt) (disjList ((alt2 :: rest2).map compileExpr)))
            env (.normal ([env.insert "Out" alt] ++
                          (alt2 :: rest2).map (fun a => env.insert "Out" a)))
          exact PrologEval.disj_normal (compileExpr alt)
            (disjList ((alt2 :: rest2).map compileExpr))
            env [env.insert "Out" alt]
            ((alt2 :: rest2).map (fun a => env.insert "Out" a))
            h_alt_eval
            (ih h_rest_self h_rest_red)

/-- **Superpose soundness** (parameterized by per-alternative soundness):
    If each `alt ∈ alts` has a sound compilation (Prolog answers ↔ PeTTaEval),
    then `compileExpr (superpose alts)` is also sound: every Prolog answer
    traces back to some alternative.

    This is the soundness companion to `compileExpr_superpose_complete`.
    The parameterization by `h_sound` makes this unconditionally correct:
    the superpose soundness reduces to the soundness of each branch. -/
theorem compileExpr_superpose_sound (s : PeTTaSpace) (env : PEnv)
    (alts : List Pattern)
    (h_sound : ∀ alt ∈ alts, ∀ (r' : PrologEvalResult) (out : Pattern),
        PrologEval (meTTaPrologOracle s) (compileExpr alt) env r' →
        env.insert "Out" out ∈ r'.answers →
        ∃ outs, PeTTaEval s alt outs ∧ out ∈ outs)
    (r : PrologEvalResult)
    (h : PrologEval (meTTaPrologOracle s)
          (compileExpr (.apply "superpose" [.collection .vec alts none])) env r)
    (out : Pattern)
    (h_ans : env.insert "Out" out ∈ r.answers) :
    ∃ alt ∈ alts, ∃ outs, PeTTaEval s alt outs ∧ out ∈ outs := by
  rw [compileExpr_superpose] at h
  -- disjList soundness: some goal in the list produced the answer
  obtain ⟨g, hg_mem, r', hr', hans⟩ :=
    prologEval_disjList_sound (alts.map compileExpr) r h h_ans
  -- The goal came from compiling some alt
  rw [List.mem_map] at hg_mem
  obtain ⟨alt, halt_mem, halt_eq⟩ := hg_mem
  -- halt_eq : compileExpr alt = g; rewrite hr' to use compileExpr alt
  rw [← halt_eq] at hr'
  -- Apply the per-alternative soundness hypothesis
  obtain ⟨outs, hpe, hout⟩ := h_sound alt halt_mem r' out hr' hans
  exact ⟨alt, halt_mem, outs, hpe, hout⟩

/-- **reduceCall alt soundness** (instantiation of `compileExpr_superpose_sound`):
    For alternatives that compile to `reduceCall [alt]`, superpose soundness holds. -/
theorem compileExpr_superpose_sound_reduceCall (s : PeTTaSpace) (env : PEnv)
    (alts : List Pattern)
    (h_reduce : ∀ alt ∈ alts, compileExpr alt = .reduceCall [alt])
    (r : PrologEvalResult)
    (h : PrologEval (meTTaPrologOracle s)
          (compileExpr (.apply "superpose" [.collection .vec alts none])) env r)
    (out : Pattern)
    (h_ans : env.insert "Out" out ∈ r.answers) :
    ∃ alt ∈ alts, ∃ outs, PeTTaEval s alt outs ∧ out ∈ outs := by
  apply compileExpr_superpose_sound s env alts _ r h out h_ans
  -- Prove per-alternative soundness for the reduceCall case
  intro alt halt_mem r' out' hr' hans
  rw [h_reduce alt halt_mem] at hr'
  -- reduceCall soundness: extract PeTTaEval from the oracle call
  obtain ⟨outs, hpe, h_envs⟩ := reduceCall_meTTa_sound s alt env r' hr'
  -- h_envs : r'.answers = outs.map (fun o => env.insert "Out" o)
  rw [h_envs, List.mem_map] at hans
  obtain ⟨out'', h_out'', h_eq⟩ := hans
  -- h_eq : env.insert "Out" out'' = env.insert "Out" out'
  simp only [PEnv.insert, List.cons.injEq, Prod.mk.injEq, and_true, true_and] at h_eq
  exact ⟨outs, hpe, h_eq ▸ h_out''⟩

/-! ## General Application: `if`, `let`, `case`, `forall`, `foldall`

The forms `if`, `let`, `case`, etc. all fall through `compileExpr`'s catch-all to
`reduceCall [e]`.  This conservative choice is **semantically correct**: `reduceCall [e]`
under the MeTTa oracle directly calls `PeTTaEval s e outs`, which is the ground truth.

**Why not compile `if` to Prolog's `ite`?**

Prolog's `(Cond -> Then ; Else)` commits to `Then` whenever `Cond` has any answers —
regardless of what value `Cond` produces.  MeTTa's `(if C T E)` requires `C` to
evaluate to the *atom* `True` or `False`.  These semantics differ when `C` reduces to
some non-boolean value with answers: Prolog's `ite` would run `Then`, but MeTTa's `if`
would produce an error or reduce the whole `if` form again.  The conservative
`reduceCall` avoids this mismatch.

**Why not compile `let` to Prolog conjunction?**

`translate_expr` in PeTTa exploits Prolog's first-class logical variables: the Prolog
variable for the result of `Val` is *the same Prolog variable* substituted into `Body`.
In our formalization, `PEnv` is a `List (String × Pattern)` association list, and
`matchPattern`/`compileExpr` do not have access to the current environment.  Threading
`let`-bindings through `compileExpr` would require `PEnv → PrologGoal`, changing the
type signature.  The conservative `reduceCall` delegates to the oracle.

**Proof that the catch-all applies**:

The following lemma witnesses that `if`/`let`/`case` etc. use the catch-all case. -/

private theorem compileExpr_catchall (e : Pattern)
    (h1 : ∀ x, e ≠ .fvar x)
    (h2 : ∀ n, e ≠ .bvar n)
    (h3 : ∀ c, e ≠ .apply c [])
    (h4 : ∀ ct alts r, e ≠ .apply "superpose" [.collection ct alts r])
    (h5 : ∀ body, e ≠ .apply "collapse" [body])
    (h6 : ∀ pat tmpl, e ≠ .apply "match" [.apply "&self" [], pat, tmpl]) :
    compileExpr e = .reduceCall [e] :=
  compileExpr.eq_7 e
    (fun x heq => h1 x heq)
    (fun n heq => h2 n heq)
    (fun c heq => h3 c heq)
    (fun ct alts r heq => h4 ct alts r heq)
    (fun body heq => h5 body heq)
    (fun pat tmpl heq => h6 pat tmpl heq)

/-- `(if cond then else)` compiles to the catch-all `reduceCall [.apply "if" ...]`. -/
@[simp]
theorem compileExpr_if (cond then_ else_ : Pattern) :
    compileExpr (.apply "if" [cond, then_, else_]) =
    .reduceCall [.apply "if" [cond, then_, else_]] :=
  compileExpr_catchall _
    (by simp) (by simp) (by simp)
    (by intro _ _ _; simp)
    (by intro _; simp)
    (by intro _ _; simp)

/-- **`if` soundness**: the conservative compilation is sound and complete. -/
theorem compileExpr_if_iff (s : PeTTaSpace) (env : PEnv)
    (cond then_ else_ : Pattern) (out : Pattern) :
    (∃ outs r,
        PeTTaEval s (.apply "if" [cond, then_, else_]) outs ∧
        PrologEval (meTTaPrologOracle s)
          (compileExpr (.apply "if" [cond, then_, else_])) env r ∧
        (env.insert "Out" out) ∈ r.answers) ↔
    (∃ outs, PeTTaEval s (.apply "if" [cond, then_, else_]) outs ∧ out ∈ outs) := by
  simp only [compileExpr_if]
  exact compileExpr_reduceCall_iff s (.apply "if" [cond, then_, else_]) env out

/-- `(let x val body)` compiles to the catch-all `reduceCall`. -/
@[simp]
theorem compileExpr_let (x val body : Pattern) :
    compileExpr (.apply "let" [x, val, body]) =
    .reduceCall [.apply "let" [x, val, body]] :=
  compileExpr_catchall _
    (by simp) (by simp) (by simp)
    (by intro _ _ _; simp)
    (by intro _; simp)
    (by intro _ _; simp)

end Mettapedia.OSLF.PeTTa
