import Mettapedia.Logic.BDD.Operations
import Mettapedia.Logic.ProbLogCompilation

/-!
# ProbLog-to-BDD Compilation Correctness

Formalizes the compilation from ground ProbLog programs to BDDs and proves
soundness: a compiled BDD evaluates to `true` under assignment `a` implies
the query holds in the corresponding ProbLog world.

## ProbLog Background (De Raedt, Kimmig, Toivonen 2007)

A ProbLog program consists of:
- **Probabilistic facts**: `p_i :: f_i` — ground atoms independently true with probability `p_i`
- **Definite clauses**: `head :- body₁, ..., bodyₖ` — logic programming rules

## BDD Compilation (Fierens et al. 2015)

ProbLog compiles queries to BDDs via proof enumeration:
1. Probabilistic fact `f_i` → BDD variable `i`
2. Conjunction `(b₁, ..., bₖ)` → AND of sub-BDDs
3. Multiple derivations → OR

## Connection to ProbMeTTa

Each constructor mirrors `lib_prob.metta`:
- `.fact` ↔ `prob-assume`
- `.rule` ↔ `prob-goal` + `exec-conj`
- `.disj` ↔ `?prob-bdd` + `bdd-disjunction`

0 sorry.
-/

namespace Mettapedia.Logic.BDDCore

open Mettapedia.Logic.LP
open Mettapedia.Logic.ProbLogCompilation

/-! ## §1 Assignment-Based Residual Program -/

/-- Residual EDB for assignment `a`: `f_i` is included iff `a i = true`. -/
def residualDBa {σ : LPSignature} {n : ℕ} (prog : ProbLogProgram σ n)
    (a : Fin n → Bool) : Set (GroundAtom σ) :=
  { ga | ∃ i : Fin n, a i = true ∧ prog.probFacts i = ga }

/-- Residual KB for assignment `a`. -/
def residualKBa {σ : LPSignature} {n : ℕ} (prog : ProbLogProgram σ n)
    (a : Fin n → Bool) : KnowledgeBase σ where
  prog := prog.rules
  db := residualDBa prog a

/-- Query holds under assignment `a` (ProbLog distribution semantics). -/
def queryHoldsA {σ : LPSignature} {n : ℕ} (prog : ProbLogProgram σ n)
    (q : GroundAtom σ) (a : Fin n → Bool) : Prop :=
  q ∈ leastHerbrandModel (residualKBa prog a)

/-! ## §2 Ground BDD Compilation -/

/-- Ground BDD compilation: how ProbMeTTa builds a BDD for a query.
    This IS ProbLog's knowledge compilation (Fierens et al. 2015, §3.2). -/
inductive GroundBDDCompile {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) : GroundAtom σ → BDD n → Prop where
  /-- Probabilistic fact `f_i` compiles to BDD variable `i`.
      ProbMeTTa: `prob-assume` -/
  | fact (i : Fin n) :
      GroundBDDCompile prog (prog.probFacts i) (bddVar i)
  /-- Rule with empty body: head holds unconditionally.
      ProbMeTTa: `exec-conj () $trace` returns trace -/
  | ruleNil (head : GroundAtom σ)
      (hrule : (⟨head.toAtom, []⟩ : Clause σ) ∈ prog.rules) :
      GroundBDDCompile prog head .one
  /-- Rule with one body atom: compile body, result is the body's BDD.
      Simpler than the general conjunction case. -/
  | ruleOne (head body : GroundAtom σ)
      (hrule : (⟨head.toAtom, [body.toAtom]⟩ : Clause σ) ∈ prog.rules)
      (fb : BDD n) (hb : GroundBDDCompile prog body fb) :
      GroundBDDCompile prog head fb
  /-- Rule with conjunction body: compile each, AND together.
      ProbMeTTa: `prob-goal` + `exec-conj` -/
  | rulePair (head b₁ b₂ : GroundAtom σ) (rest : List (GroundAtom σ))
      (hrule : (⟨head.toAtom, (b₁ :: b₂ :: rest).map GroundAtom.toAtom⟩ : Clause σ) ∈ prog.rules)
      (f₁ f₂ : BDD n)
      (h₁ : GroundBDDCompile prog b₁ f₁)
      (h₂ : GroundBDDCompile prog b₂ f₂)
      (frest : List (BDD n))
      (hrest_len : frest.length = rest.length)
      (hrest : ∀ j : Fin rest.length,
        GroundBDDCompile prog (rest.get j) (frest.get (j.cast hrest_len.symm)))
      (conjBDD : BDD n)
      (hconj : conjBDD = (f₂ :: frest).foldl (apply (· && ·)) f₁) :
      GroundBDDCompile prog head conjBDD
  /-- **General rule with grounding**: given clause `c ∈ prog.rules` and grounding `g`,
      if `g.groundAtom c.head = head` and each body atom `g.groundAtom b` has a
      witness BDD, AND them together to get the head's BDD.
      This matches `T_P_LP`'s rule application with variable instantiation. -/
  | ruleG (head : GroundAtom σ) (c : Clause σ) (g : Grounding σ)
      (hc : c ∈ prog.rules) (hhead : g.groundAtom c.head = head)
      (bodyBDDs : List (BDD n))
      (hlen : bodyBDDs.length = c.body.length)
      (hbody : ∀ j : Fin c.body.length,
        GroundBDDCompile prog (g.groundAtom (c.body.get j))
          (bodyBDDs.get (j.cast hlen.symm)))
      (conjBDD : BDD n)
      (hconj : conjBDD = bodyBDDs.foldl (apply (· && ·)) .one) :
      GroundBDDCompile prog head conjBDD
  /-- Multiple derivations: OR the BDDs.
      ProbMeTTa: `?prob-bdd` + `bdd-disjunction` -/
  | disj (q : GroundAtom σ) (f₁ f₂ : BDD n)
      (h₁ : GroundBDDCompile prog q f₁)
      (h₂ : GroundBDDCompile prog q f₂) :
      GroundBDDCompile prog q (apply (· || ·) f₁ f₂)
  /-- Bottom: trivially false BDD. Sound vacuously (`.zero` never evaluates to true).
      Used as the base case when OR-ing all derivation witnesses for NAF completeness.
      Mirrors ProbLog's behavior when `prob-not` finds no proofs: the negation
      succeeds unconditionally (`NODE_TRUE` in `eval_nodes.py:752`). -/
  | bottom (q : GroundAtom σ) :
      GroundBDDCompile prog q .zero

/-! ## §3 Compilation Soundness -/

/-- Helper: if `foldl AND` evaluates to true, each component evaluates to true. -/
private theorem foldl_and_all_true {n : ℕ} (init : BDD n) (bdds : List (BDD n))
    (env : Fin n → Bool)
    (h : (bdds.foldl (apply (· && ·)) init).eval env = true) :
    init.eval env = true ∧ ∀ b ∈ bdds, b.eval env = true := by
  induction bdds generalizing init with
  | nil => exact ⟨h, fun _ hm => absurd hm (by simp)⟩
  | cons hd tl ih =>
    simp only [List.foldl_cons] at h
    have ⟨hinit_and, htl⟩ := ih _ h
    rw [apply_eval] at hinit_and
    have h1 : init.eval env = true := by
      cases hinit_eval : init.eval env <;> simp_all
    have h2 : hd.eval env = true := by
      cases hd_eval : hd.eval env <;> simp_all
    exact ⟨h1, fun b hb => by
      rcases List.mem_cons.mp hb with rfl | htl_mem
      · exact h2
      · exact htl b htl_mem⟩

/-- **Soundness of BDD compilation**: if the compiled BDD evaluates to true,
    the query holds in the corresponding ProbLog world.

    Combined with `bdd_wmc_correct`, this proves ProbMeTTa computes
    ProbLog probabilities correctly. -/
theorem GroundBDDCompile_sound {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbLogProgram σ n) (q : GroundAtom σ) (f : BDD n)
    (hcomp : GroundBDDCompile prog q f)
    (a : Fin n → Bool) (heval : f.eval a = true) :
    queryHoldsA prog q a := by
  induction hcomp with
  | fact i =>
    -- bddVar i evaluates to true ↔ a i = true
    simp [bddVar] at heval
    -- Fact i is in residual DB → in least Herbrand model
    exact leastHerbrandModel_db _ _ ⟨i, heval, rfl⟩
  | ruleNil head hrule =>
    -- Empty body: head follows from the rule immediately
    let g : Grounding σ := fun _ => Classical.arbitrary (GroundTerm σ)
    show head ∈ leastHerbrandModel (residualKBa prog a)
    rw [← Grounding.groundAtom_toAtom_self g head]
    exact leastHerbrandModel_clause _ ⟨head.toAtom, []⟩ hrule g (fun _ h => absurd h (by simp))
  | ruleOne head body hrule fb _ ih =>
    -- Single body: IH gives body in LHM, apply clause
    have hbody := ih heval
    let g : Grounding σ := fun _ => Classical.arbitrary (GroundTerm σ)
    show head ∈ leastHerbrandModel (residualKBa prog a)
    rw [← Grounding.groundAtom_toAtom_self g head]
    exact leastHerbrandModel_clause _ ⟨head.toAtom, [body.toAtom]⟩ hrule g
      (fun b hb => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rw [hb, Grounding.groundAtom_toAtom_self]; exact hbody)
  | rulePair head b₁ b₂ rest hrule f₁ f₂ _ _ frest hrest_len hrest conjBDD hconj ih₁ ih₂ ih_rest =>
    -- Conjunction: foldl AND evaluates to true → each component true
    subst hconj
    have ⟨hf₁_eval, hall⟩ := foldl_and_all_true f₁ (f₂ :: frest) a heval
    have hf₂_eval := hall f₂ (List.mem_cons_self ..)
    -- Apply IH to get each body atom in LHM
    have hb₁ := ih₁ hf₁_eval
    have hb₂ := ih₂ hf₂_eval
    -- Apply the clause rule
    let g : Grounding σ := fun _ => Classical.arbitrary (GroundTerm σ)
    show head ∈ leastHerbrandModel (residualKBa prog a)
    rw [← Grounding.groundAtom_toAtom_self g head]
    apply leastHerbrandModel_clause _ ⟨head.toAtom, (b₁ :: b₂ :: rest).map GroundAtom.toAtom⟩ hrule g
    intro b hb
    rw [List.mem_map] at hb
    obtain ⟨ga, hga_mem, rfl⟩ := hb
    rw [Grounding.groundAtom_toAtom_self]
    rcases List.mem_cons.mp hga_mem with rfl | hga_rest
    · exact hb₁
    · rcases List.mem_cons.mp hga_rest with rfl | hga_tail
      · exact hb₂
      · -- ga ∈ rest: use ih_rest
        obtain ⟨j, hj⟩ := List.get_of_mem hga_tail
        have hfj_eval := hall (frest.get (j.cast hrest_len.symm))
          (List.mem_cons_of_mem _ (List.get_mem ..))
        rw [← hj]
        exact ih_rest j hfj_eval
  | ruleG head c g hc hhead bodyBDDs hlen hbody conjBDD hconj ih_body =>
    -- General rule with grounding
    subst hconj; subst hhead
    have ⟨hinit_eval, hall⟩ := foldl_and_all_true .one bodyBDDs a heval
    show g.groundAtom c.head ∈ leastHerbrandModel (residualKBa prog a)
    apply leastHerbrandModel_clause _ c hc g
    intro b hb
    obtain ⟨j, hj⟩ := List.get_of_mem hb
    rw [← hj]
    have hfj_eval := hall (bodyBDDs.get (j.cast hlen.symm)) (List.get_mem ..)
    exact ih_body j hfj_eval
  | disj q f₁ f₂ _ _ ih₁ ih₂ =>
    -- OR: at least one evaluates to true
    rw [apply_eval] at heval
    cases hf₁ : f₁.eval a <;> cases hf₂ : f₂.eval a <;> simp_all
  | bottom q =>
    -- .zero never evaluates to true — vacuously sound
    simp at heval

/-! ## §4 General Completeness

For arbitrary ground definite clause programs, we prove completeness:
if the query holds under assignment `a`, there exists a compiled BDD
that evaluates to true under `a`.

The proof uses the iterate characterization of `leastHerbrandModel`:
  `leastHerbrandModel kb = ⋃ k, T_P_LP_iter kb k`
and inducts on the iterate level `k`. At each level:
- Base (EDB): probabilistic facts compile to variable nodes
- Rule: body atoms have witness BDDs by IH; AND them; the rule gives the head

This follows the same pattern as `sldWitness_iter_lift_of_db_and_rule`
in `LP/SLDCompute.lean`. -/

/-- Helper: if all BDDs in a list evaluate to true, their foldl-AND evaluates to true. -/
private theorem foldl_and_true_of_all_true {n : ℕ} (init : BDD n) (bdds : List (BDD n))
    (env : Fin n → Bool)
    (hinit : init.eval env = true)
    (hall : ∀ b ∈ bdds, b.eval env = true) :
    (bdds.foldl (apply (· && ·)) init).eval env = true := by
  induction bdds generalizing init with
  | nil => exact hinit
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    · rw [apply_eval]; simp [hinit, hall hd (List.mem_cons_self ..)]
    · intro b hb; exact hall b (List.mem_cons_of_mem _ hb)

/-- **General completeness**: if a query holds under assignment `a`, there exists
    a compiled BDD that evaluates to true.

    The proof constructs a witness BDD by following the derivation through
    `T_P_LP` iterates: each EDB fact gives a variable node, each rule application
    gives an AND of body BDDs.

    This is the general version — no restriction to OR-pattern programs.
    It covers conjunctions, chains, overlapping derivations, and all programs
    that ProbMeTTa handles. -/
theorem GroundBDDCompile_complete {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbLogProgram σ n) (ga : GroundAtom σ)
    (a : Fin n → Bool) (hq : queryHoldsA prog ga a) :
    ∃ (f : BDD n), GroundBDDCompile prog ga f ∧ f.eval a = true := by
  -- Unfold leastHerbrandModel into iterates
  unfold queryHoldsA at hq
  rw [leastHerbrandModel_eq_iter_sup] at hq
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hq
  -- Induct on iterate level k
  induction k generalizing ga with
  | zero =>
    -- T_P_LP_iter^0 = EDB = residualDBa
    simp [T_P_LP_iter, residualKBa] at hk
    obtain ⟨i, hai, hfi⟩ := hk
    exact ⟨bddVar i,
      hfi ▸ GroundBDDCompile.fact i,
      by simp [bddVar, hai]⟩
  | succ k ih =>
    -- T_P_LP_iter^(k+1) = T_P_LP(T_P_LP_iter^k)
    simp [T_P_LP_iter, T_P_LP, residualKBa] at hk
    rcases hk with hdb | ⟨c, g, hmem_c, hhead, hbody⟩
    · -- In EDB: same as base case
      obtain ⟨i, hai, hfi⟩ := hdb
      exact ⟨bddVar i,
        hfi ▸ GroundBDDCompile.fact i,
        by simp [bddVar, hai]⟩
    · -- Derived by a rule: c ∈ prog.rules, g.groundAtom c.head = ga,
      -- and ∀ b ∈ c.body, g.groundAtom b ∈ T_P_LP_iter^k
      -- By IH, each body atom has a witness BDD
      -- We construct the conjunction BDD for the body, then use the rule
      -- Function-free: g.groundAtom c.head = ga, g.groundAtom b = the ground atom
      subst hhead
      -- For each body position, get a witness BDD via IH
      -- (note: g is the rule membership, hmem_c is the grounding — names from rcases)
      have hchoice : ∀ j : Fin c.body.length,
          ∃ fb : BDD n,
            GroundBDDCompile prog (hmem_c.groundAtom (c.body.get j)) fb ∧
            fb.eval a = true := by
        intro j
        apply ih
        · exact Set.mem_iUnion.mpr ⟨k, hbody (c.body.get j) (List.get_mem ..)⟩
        · exact hbody (c.body.get j) (List.get_mem ..)
      -- Extract witness BDDs via classical choice
      classical
      let chooseBDD : Fin c.body.length → BDD n := fun j => (hchoice j).choose
      let bodyBDDs := List.ofFn chooseBDD
      have hlen : bodyBDDs.length = c.body.length := List.length_ofFn
      -- Each chosen BDD compiles and evaluates correctly
      have hcompile : ∀ j : Fin c.body.length,
          GroundBDDCompile prog (hmem_c.groundAtom (c.body.get j))
            (bodyBDDs.get (j.cast hlen.symm)) := by
        intro j
        simp only [bodyBDDs, List.get_ofFn]
        exact (hchoice j).choose_spec.1
      have heval_all : ∀ j : Fin c.body.length,
          (bodyBDDs.get (j.cast hlen.symm)).eval a = true := by
        intro j
        simp only [bodyBDDs, List.get_ofFn]
        exact (hchoice j).choose_spec.2
      -- Construct the conjunction BDD and show it evaluates to true
      refine ⟨bodyBDDs.foldl (apply (· && ·)) .one,
        GroundBDDCompile.ruleG _ c hmem_c g rfl bodyBDDs hlen hcompile _ rfl, ?_⟩
      -- Show foldl AND evaluates to true
      apply foldl_and_true_of_all_true
      · simp
      · intro b hb
        obtain ⟨j, hj⟩ := List.get_of_mem hb
        rw [← hj]
        exact heval_all (j.cast hlen)

/-! ## §5 Goal-Level Compilation: NAF, Inequality Constraints

ProbMeTTa's `prob-goal` handles not just ground atoms but also:
- `(naf $goal)` — negation-as-failure (goal fails → succeeds)
- `(neq $a $b)` — inequality constraint (guard)

These are goal-level constructs, not ground atoms. We formalize them
as a `GoalLit` type and a `GoalBDDCompile` relation that composes
with the existing `GroundBDDCompile` for positive atoms. -/

/-- A goal literal in a ProbLog rule body. Extends ground atoms with
    negation-as-failure and inequality constraints.

    Mirrors ProbMeTTa's `prob-goal` dispatch:
    - `pos a` ↔ positive atom (standard resolution)
    - `neg a` ↔ `(naf $goal)` (negation-as-failure)
    - `neq a b` ↔ `(neq $a $b)` (inequality guard) -/
inductive GoalLit (σ : LPSignature) where
  | pos : GroundAtom σ → GoalLit σ
  | neg : GroundAtom σ → GoalLit σ
  | neq : GroundAtom σ → GroundAtom σ → GoalLit σ

/-- Goal-level BDD compilation: compiles a conjunction of goal literals
    to a BDD by threading AND/NOT operations.

    Mirrors ProbMeTTa's `exec-conj` with `prob-goal` dispatch for each literal:
    - Positive atom: compile via `GroundBDDCompile`, AND into trace
    - Negated atom: compile, negate via `bddNot`, AND into trace
    - Inequality: guard (pass trace if unequal, fail if equal) -/
inductive GoalBDDCompile {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) : List (GoalLit σ) → BDD n → Prop where
  /-- Empty goal list: trace is constant true.
      ProbMeTTa: `(exec-conj () $trace)` returns trace. -/
  | nil : GoalBDDCompile prog [] .one
  /-- Positive atom: compile atom, AND with rest.
      ProbMeTTa: `(prob-goal $goal $trace)` for non-NAF goals. -/
  | posAtom (a : GroundAtom σ) (rest : List (GoalLit σ)) (fa fr : BDD n)
      (ha : GroundBDDCompile prog a fa)
      (hr : GoalBDDCompile prog rest fr) :
      GoalBDDCompile prog (.pos a :: rest) (apply (· && ·) fa fr)
  /-- Negated atom (NAF): use a COMPLETE BDD for the atom, negate, AND with rest.
      ProbMeTTa: `(prob-goal (naf $goal) $trace) = (prob-not $goal $trace)`.
      `prob-not` uses `collapse` to collect ALL proofs, then negates.

      The `ha_complete` hypothesis ensures `fa` captures all derivations:
      if the atom holds, `fa` evaluates to true. This matches ProbMeTTa's
      `collapse` semantics. Combined with `GroundBDDCompile_sound` (which
      gives soundness), the BDD is exact. -/
  | negAtom (a : GroundAtom σ) (rest : List (GoalLit σ)) (fa fr : BDD n)
      (ha : GroundBDDCompile prog a fa)
      (ha_complete : ∀ b, queryHoldsA prog a b → fa.eval b = true)
      (hr : GoalBDDCompile prog rest fr) :
      GoalBDDCompile prog (.neg a :: rest) (apply (· && ·) (bddNot fa) fr)
  /-- Inequality constraint: pass if atoms are unequal, fail otherwise.
      ProbMeTTa: `(prob-goal (neq $a $b) $trace) = if (== $a $b) (empty) $trace`. -/
  | neqGuard (a b : GroundAtom σ) (rest : List (GoalLit σ)) (fr : BDD n)
      (hne : a ≠ b)
      (hr : GoalBDDCompile prog rest fr) :
      GoalBDDCompile prog (.neq a b :: rest) fr

/-! ## §6 Goal-Level Soundness

If the compiled goal BDD evaluates to true, then:
- Each positive atom holds in the residual LHM
- Each negated atom does NOT hold in the residual LHM
- Each inequality constraint is satisfied -/

/-- Interpretation of a goal literal in the least Herbrand model. -/
def GoalLit.holds {σ : LPSignature} {n : ℕ} (prog : ProbLogProgram σ n)
    (a : Fin n → Bool) : GoalLit σ → Prop
  | .pos ga => queryHoldsA prog ga a
  | .neg ga => ¬ queryHoldsA prog ga a
  | .neq ga gb => ga ≠ gb

/-- **Goal-level soundness**: if the compiled goal BDD evaluates to true,
    then every goal literal holds.

    Uses `GroundBDDCompile_sound` for positive atoms and `bddNot_eval`
    for negated atoms. -/
theorem GoalBDDCompile_sound {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbLogProgram σ n) (goals : List (GoalLit σ)) (f : BDD n)
    (hcomp : GoalBDDCompile prog goals f)
    (a : Fin n → Bool) (heval : f.eval a = true) :
    ∀ g ∈ goals, g.holds prog a := by
  induction hcomp with
  | nil => intro _ hm; exact absurd hm (by simp)
  | posAtom atom rest fa fr ha hr ih =>
    intro g hg
    rw [apply_eval] at heval
    have hfa : fa.eval a = true := by
      cases hfa' : fa.eval a <;> cases hfr' : fr.eval a <;> simp_all
    have hfr : fr.eval a = true := by
      cases hfa' : fa.eval a <;> cases hfr' : fr.eval a <;> simp_all
    rcases List.mem_cons.mp hg with rfl | hrest
    · -- positive atom: use GroundBDDCompile_sound
      exact GroundBDDCompile_sound prog atom fa ha a hfa
    · exact ih hfr g hrest
  | negAtom atom rest fa fr ha ha_complete hr ih =>
    intro g hg
    rw [apply_eval] at heval
    have hneg : (bddNot fa).eval a = true := by
      cases hn' : (bddNot fa).eval a <;> cases hfr' : fr.eval a <;> simp_all
    have hfr : fr.eval a = true := by
      cases hn' : (bddNot fa).eval a <;> cases hfr' : fr.eval a <;> simp_all
    rcases List.mem_cons.mp hg with rfl | hrest
    · -- NAF: bddNot fa true → fa false → by ha_complete contrapositive, atom NOT in LHM
      show ¬queryHoldsA prog atom a
      intro habs
      have := ha_complete a habs
      rw [bddNot_eval] at hneg
      simp [this] at hneg
    · exact ih hfr g hrest
  | neqGuard a b rest fr hne hr ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hrest
    · exact hne
    · exact ih heval g hrest

/-! ## §6b Ordered-Preservation for Compilation Witnesses -/

/-- Helper: `foldl (apply (· && ·))` preserves `Ordered`. -/
private theorem foldl_and_ordered {n : ℕ} (init : BDD n) (bdds : List (BDD n))
    (bound : Option (Fin n))
    (hinit : init.Ordered bound) (hall : ∀ b ∈ bdds, b.Ordered bound) :
    (bdds.foldl (apply (· && ·)) init).Ordered bound := by
  induction bdds generalizing init with
  | nil => exact hinit
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact ih _ (apply_ordered _ init hd bound hinit (hall hd (List.mem_cons_self ..)))
      (fun b hb => hall b (List.mem_cons_of_mem _ hb))

/-- Compiled atom BDDs are ordered. Each `GroundBDDCompile` constructor produces
    an ordered BDD: `bddVar` for facts, `.one`/`.zero` for terminals, `apply`
    for combinations. -/
theorem GroundBDDCompile_ordered {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) (q : GroundAtom σ) (f : BDD n)
    (hcomp : GroundBDDCompile prog q f) : f.Ordered none := by
  induction hcomp with
  | fact i => exact bddVar_ordered i
  | ruleNil _ _ => exact .one
  | ruleOne _ _ _ _ _ ih => exact ih
  | rulePair _ _ _ _ _ _ _ _ _ frest hrest_len _ _ hconj ih₁ ih₂ ih_rest =>
    subst hconj
    apply foldl_and_ordered
    · exact ih₁
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hrest
      · exact ih₂
      · have ⟨j, hj⟩ := List.mem_iff_get.mp hrest
        rw [← hj]
        exact ih_rest ⟨j, by omega⟩
  | ruleG _ _ _ _ _ bodyBDDs hlen _ hconj =>
    subst hconj
    rename_i ih_bdy
    apply foldl_and_ordered
    · exact .one
    · intro b hb
      have ⟨j, hj⟩ := List.mem_iff_get.mp hb
      rw [← hj]
      exact ih_bdy ⟨j, by omega⟩
  | disj _ _ _ _ _ ih₁ ih₂ =>
    exact apply_ordered _ _ _ _ ih₁ ih₂
  | bottom _ => exact .zero

/-- Compiled goal BDDs are ordered. Uses `GroundBDDCompile_ordered` for
    positive atoms and `bddNot_ordered` for NAF. -/
theorem GoalBDDCompile_ordered {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) (goals : List (GoalLit σ)) (f : BDD n)
    (hcomp : GoalBDDCompile prog goals f) : f.Ordered none := by
  induction hcomp with
  | nil => exact .one
  | posAtom _ _ _ _ ha _ ih =>
    exact apply_ordered _ _ _ _ (GroundBDDCompile_ordered prog _ _ ha) ih
  | negAtom _ _ _ _ ha _ _ ih =>
    exact apply_ordered _ _ _ _ (bddNot_ordered _ _ (GroundBDDCompile_ordered prog _ _ ha)) ih
  | neqGuard _ _ _ _ _ _ ih => exact ih

/-! ## §7 Complete BDD Construction

For NAF completeness, we need a BDD that is BOTH a `GroundBDDCompile` witness
AND evaluates to true whenever the atom holds under ANY assignment.

**Construction:** Start with `bottom` (`.zero`). For each assignment `a ∈ Fin n → Bool`
where the atom holds, get a witness BDD from `GroundBDDCompile_complete` and OR it in
via `disj`. The result is a `GroundBDDCompile` witness (by iterated `disj` + `bottom`)
that is complete (each assignment's witness contributes).

This mirrors ProbLog's `collapse + bdd-disjunction` algorithm
(see `eval_nodes.py:727-734` in ML-KULeuven/problog). -/

/-- Fold `disj` over a finset of assignments, OR-ing witness BDDs.
    Returns a `GroundBDDCompile` witness that is complete for all
    assignments in the finset. -/
private theorem fold_disj_complete {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbLogProgram σ n) (ga : GroundAtom σ)
    (assignments : List (Fin n → Bool))
    (hhold : ∀ a ∈ assignments, queryHoldsA prog ga a) :
    ∃ f : BDD n, GroundBDDCompile prog ga f ∧
      (∀ a ∈ assignments, f.eval a = true) := by
  induction assignments with
  | nil =>
    exact ⟨.zero, .bottom ga, fun _ h => absurd h (by simp)⟩
  | cons a rest ih =>
    have ⟨f_rest, hcomp_rest, heval_rest⟩ := ih (fun a' h => hhold a' (List.mem_cons_of_mem _ h))
    have hqa := hhold a (List.mem_cons_self ..)
    obtain ⟨f_a, hcomp_a, heval_a⟩ := GroundBDDCompile_complete prog ga a hqa
    refine ⟨apply (· || ·) f_rest f_a,
      .disj ga f_rest f_a hcomp_rest hcomp_a, ?_⟩
    intro a' ha'
    rw [apply_eval]
    rcases List.mem_cons.mp ha' with rfl | hrest
    · simp [heval_a]
    · simp [heval_rest a' hrest]

/-- **Complete BDD existence**: for any ground atom, there exists a BDD that
    is a `GroundBDDCompile` witness AND evaluates to true for every assignment
    where the atom holds.

    Uses `Fintype (Fin n → Bool)` to enumerate all assignments. -/
theorem exists_complete_bdd {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbLogProgram σ n) (ga : GroundAtom σ) :
    ∃ f : BDD n, GroundBDDCompile prog ga f ∧
      (∀ a, queryHoldsA prog ga a → f.eval a = true) := by
  classical
  -- Get the list of ALL assignments where the atom holds
  let allAssignments := (Finset.univ : Finset (Fin n → Bool)).val.toList
  -- Filter to those where the atom holds
  let holdingList := allAssignments.filter (fun a => decide (queryHoldsA prog ga a))
  -- Build the complete BDD by folding disj
  obtain ⟨f, hcomp, heval⟩ := fold_disj_complete prog ga holdingList
    (fun a ha => by
      have := List.mem_filter.mp ha
      exact of_decide_eq_true this.2)
  exact ⟨f, hcomp, fun a hqa => heval a (by
    apply List.mem_filter.mpr
    exact ⟨Multiset.mem_toList.mpr (Finset.mem_univ a), decide_eq_true hqa⟩)⟩

/-! ## §8 Full Goal-Level Completeness -/

/-- **Full goal completeness** including NAF: if all goal literals hold
    (positive atoms in LHM, negated atoms NOT in LHM, inequalities satisfied),
    there exists a compiled BDD that evaluates to true.

    Uses `exists_complete_bdd` for NAF goals: the complete BDD captures all
    derivations, so its negation correctly reflects non-derivability. -/
theorem GoalBDDCompile_complete {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbLogProgram σ n) (goals : List (GoalLit σ))
    (a : Fin n → Bool) (hall : ∀ g ∈ goals, g.holds prog a) :
    ∃ f : BDD n, GoalBDDCompile prog goals f ∧ f.eval a = true := by
  induction goals with
  | nil => exact ⟨.one, .nil, rfl⟩
  | cons g rest ih =>
    have hg := hall g (List.mem_cons_self ..)
    have hrest := ih (fun g' hg' => hall g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨fr, hfr_comp, hfr_eval⟩ := hrest
    match g, hg with
    | .pos atom, hpos =>
      obtain ⟨fa, hfa_comp, hfa_eval⟩ := GroundBDDCompile_complete prog atom a hpos
      exact ⟨apply (· && ·) fa fr,
        .posAtom atom rest fa fr hfa_comp hfr_comp,
        by rw [apply_eval]; simp [hfa_eval, hfr_eval]⟩
    | .neg atom, hneg =>
      -- NAF: atom does NOT hold. Use exists_complete_bdd to get a complete BDD.
      obtain ⟨fa, hfa_comp, ha_complete⟩ := exists_complete_bdd prog atom
      -- hneg : ¬queryHoldsA. By contrapositive of GroundBDDCompile_sound: fa.eval a = false
      have hfa_false : fa.eval a = false := by
        by_contra h
        push_neg at h
        have heval : fa.eval a = true := by cases hfa : fa.eval a <;> simp_all
        exact hneg (GroundBDDCompile_sound prog atom fa hfa_comp a heval)
      exact ⟨apply (· && ·) (bddNot fa) fr,
        .negAtom atom rest fa fr hfa_comp ha_complete hfr_comp,
        by rw [apply_eval, bddNot_eval]; simp [hfa_false, hfr_eval]⟩
    | .neq ga gb, hne =>
      exact ⟨fr, .neqGuard ga gb rest fr hne hfr_comp, hfr_eval⟩

/-! ## §9 Ordered Semantic Goal BDD

A single BDD that is `Ordered none` and semantically equivalent to the goal formula.
This is an extensional existence theorem — the BDD is constructed by OR-ing
per-assignment witnesses from `GoalBDDCompile_complete`. It is NOT a compiler
theorem (`GoalBDDCompile` is not claimed for the result BDD). -/

/-- **Ordered semantic goal BDD**: there exists a single ordered BDD whose
    evaluation matches goal satisfaction for ALL assignments simultaneously.

    This is the semantic equivalence theorem for goal queries. Combined with
    `bdd_wmc_correct`, it gives the goal-level WMC bridge. -/
theorem exists_ordered_goal_semantic_bdd {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbLogProgram σ n) (goals : List (GoalLit σ)) :
    ∃ f : BDD n, f.Ordered none ∧
      (∀ a, f.eval a = true ↔ ∀ g ∈ goals, g.holds prog a) := by
  classical
  let holdingList := ((Finset.univ : Finset (Fin n → Bool)).val.toList).filter
    (fun a => decide (∀ g ∈ goals, g.holds prog a))
  -- Build by induction on holdingList, folding OR
  -- Invariant: result is Ordered none, sound, and complete for all seen assignments
  suffices ∀ (l : List (Fin n → Bool)),
      (∀ a ∈ l, ∀ g ∈ goals, g.holds prog a) →
      ∃ f : BDD n, f.Ordered none ∧
        (∀ a ∈ l, f.eval a = true) ∧
        (∀ a, f.eval a = true → ∀ g ∈ goals, g.holds prog a) by
    obtain ⟨f, hord, heval, hsound⟩ := this holdingList
      (fun a ha => of_decide_eq_true (List.mem_filter.mp ha).2)
    exact ⟨f, hord, fun a => ⟨hsound a, fun hall => heval a (by
      apply List.mem_filter.mpr
      exact ⟨Multiset.mem_toList.mpr (Finset.mem_univ a), decide_eq_true hall⟩)⟩⟩
  intro l hl
  induction l with
  | nil => exact ⟨.zero, .zero, fun _ h => absurd h (by simp), fun _ h => by simp at h⟩
  | cons b rest ih =>
    obtain ⟨f_rest, hord_rest, heval_rest, hsound_rest⟩ := ih
      (fun a ha => hl a (List.mem_cons_of_mem _ ha))
    obtain ⟨f_b, hcomp_b, heval_b⟩ := GoalBDDCompile_complete prog goals b
      (hl b (List.mem_cons_self ..))
    have hord_b := GoalBDDCompile_ordered prog goals f_b hcomp_b
    refine ⟨apply (· || ·) f_rest f_b,
      apply_ordered _ _ _ _ hord_rest hord_b, ?_, ?_⟩
    · intro a ha
      rw [apply_eval]
      rcases List.mem_cons.mp ha with rfl | hrest
      · simp [heval_b]
      · simp [heval_rest a hrest]
    · intro a heval
      rw [apply_eval] at heval
      cases hf_rest : f_rest.eval a <;> cases hf_b : f_b.eval a <;>
        simp_all [GoalBDDCompile_sound prog goals f_b hcomp_b]

/-! ## §10 Normal Programs

Syntax for ProbLog programs with NAF in rule bodies. Stratified
fixed-point semantics: `LP/Stratification.lean` (`queryHoldsNormalA`).
Semantic BDD existence: `BDD/NormalCompilation.lean`.
WMC + conditioning bridge: `BDD/ProbMeTTaBridge.lean` (§7). -/

/-- A normal clause: ground head with goal literal body (may include NAF/neq).
    Semantics: see `Mettapedia.Logic.LP.Stratification` for the stratified
    fixed-point semantics (`queryHoldsNormalA`). -/
structure NormalClause (σ : LPSignature) where
  head : GroundAtom σ
  body : List (GoalLit σ)

/-- A normal program: probabilistic facts + definite clauses + normal clauses
    (with NAF in bodies). Semantics via stratified fixed-point in
    `Mettapedia.Logic.LP.Stratification`. -/
structure NormalProbLogProgram (σ : LPSignature) (n : ℕ) extends ProbLogProgram σ n where
  normalRules : List (NormalClause σ)

-- Normal goal BDD theorem: see `BDD/NormalCompilation.lean`

end Mettapedia.Logic.BDDCore
