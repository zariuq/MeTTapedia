import Mettapedia.Logic.BDD.Compilation

/-!
# ProbMeTTa Runtime Core

This file formalizes the query/runtime core of
`/home/zar/claude/ProbMeTTa/lib_prob.metta` as an explicit Lean relation over
the source-level function names:

- `prob-assume`
- `prob-not`
- `prob-goal`
- `exec-conj`
- `?prob-bdd`
- `?prob-bdd-ev`

The semantics here are intentionally normalized to the BDD result computed from
unit trace `bdd-1`. That keeps the actual source operations explicit while
landing on the already-proved BDD compilation boundary.

Positive example:
- `prob-goal (.neg q)` is a genuine runtime operation in the source language,
  and here it evaluates by first evaluating `prob-not q`.

Negative example:
- this file does not formalize program-construction macros like `::` or `::=>`;
  it isolates only the query/runtime fragment of `lib_prob.metta`.
-/

namespace Mettapedia.Logic.BDDCore

open Mettapedia.Logic.LP
open Mettapedia.PLN.Bridges.Languages.ProbLog.Compilation

/-- Source-level ProbMeTTa runtime expressions for the BDD-producing query core
of `lib_prob.metta`. -/
inductive ProbMeTTaCoreExpr (σ : LPSignature) where
  | probAssume : GroundAtom σ → ProbMeTTaCoreExpr σ
  | probNot : GroundAtom σ → ProbMeTTaCoreExpr σ
  | probGoal : GoalLit σ → ProbMeTTaCoreExpr σ
  | execConj : List (GoalLit σ) → ProbMeTTaCoreExpr σ
  | queryBDD : GroundAtom σ → ProbMeTTaCoreExpr σ
  | queryBDDEv : List (GroundAtom σ) → ProbMeTTaCoreExpr σ

/-- Big-step runtime-core evaluation for the BDD-producing query fragment of
ProbMeTTa. -/
inductive ProbMeTTaCoreEval {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) : ProbMeTTaCoreExpr σ → BDD n → Prop where
  /-- `prob-assume` uses the BDD variable corresponding to a probabilistic fact. -/
  | probAssume (i : Fin n) :
      ProbMeTTaCoreEval prog (.probAssume (prog.probFacts i)) (bddVar i)
  /-- `prob-not` is `collapse + bdd-disjunction + bdd-not`, represented here by
  an exact complete BDD witness for the positive atom, then negated. -/
  | probNot (atom : GroundAtom σ) (fa : BDD n)
      (ha : GroundBDDCompile prog atom fa)
      (ha_complete : ∀ a, queryHoldsA prog atom a → fa.eval a = true) :
      ProbMeTTaCoreEval prog (.probNot atom) (bddNot fa)
  /-- Positive `prob-goal` delegates to the ground-query compiler. -/
  | probGoal_pos (atom : GroundAtom σ) (f : BDD n)
      (h : GroundBDDCompile prog atom f) :
      ProbMeTTaCoreEval prog (.probGoal (.pos atom)) f
  /-- Negated `prob-goal` dispatches to `prob-not`. -/
  | probGoal_neg (atom : GroundAtom σ) (f : BDD n)
      (h : ProbMeTTaCoreEval prog (.probNot atom) f) :
      ProbMeTTaCoreEval prog (.probGoal (.neg atom)) f
  /-- Inequality guard succeeds exactly when the atoms differ, yielding `bdd-1`. -/
  | probGoal_neq (a b : GroundAtom σ)
      (hne : a ≠ b) :
      ProbMeTTaCoreEval prog (.probGoal (.neq a b)) .one
  /-- `exec-conj () bdd-1 = bdd-1`. -/
  | execConj_nil :
      ProbMeTTaCoreEval prog (.execConj []) .one
  /-- Positive goals in `exec-conj` are AND-ed into the rest. -/
  | execConj_cons_pos (atom : GroundAtom σ) (rest : List (GoalLit σ)) (fg fr : BDD n)
      (hg : ProbMeTTaCoreEval prog (.probGoal (.pos atom)) fg)
      (hr : ProbMeTTaCoreEval prog (.execConj rest) fr) :
      ProbMeTTaCoreEval prog (.execConj (.pos atom :: rest)) (apply (· && ·) fg fr)
  /-- NAF goals in `exec-conj` are AND-ed into the rest after `prob-not`. -/
  | execConj_cons_neg (atom : GroundAtom σ) (fnot fr : BDD n)
      (rest : List (GoalLit σ))
      (hg : ProbMeTTaCoreEval prog (.probGoal (.neg atom)) fnot)
      (hr : ProbMeTTaCoreEval prog (.execConj rest) fr) :
      ProbMeTTaCoreEval prog (.execConj (.neg atom :: rest)) (apply (· && ·) fnot fr)
  /-- Inequality goals are pure guards and leave the rest unchanged. -/
  | execConj_cons_neq (a b : GroundAtom σ) (rest : List (GoalLit σ)) (fr : BDD n)
      (hg : ProbMeTTaCoreEval prog (.probGoal (.neq a b)) .one)
      (hr : ProbMeTTaCoreEval prog (.execConj rest) fr) :
      ProbMeTTaCoreEval prog (.execConj (.neq a b :: rest)) fr
  /-- `?prob-bdd` can return any single successful proof BDD. -/
  | queryBDD_single (q : GroundAtom σ) (f : BDD n)
      (h : ProbMeTTaCoreEval prog (.probGoal (.pos q)) f) :
      ProbMeTTaCoreEval prog (.queryBDD q) f
  /-- `?prob-bdd` can OR together multiple successful proof BDDs. -/
  | queryBDD_disj (q : GroundAtom σ) (f₁ f₂ : BDD n)
      (h₁ : ProbMeTTaCoreEval prog (.queryBDD q) f₁)
      (h₂ : ProbMeTTaCoreEval prog (.queryBDD q) f₂) :
      ProbMeTTaCoreEval prog (.queryBDD q) (apply (· || ·) f₁ f₂)
  /-- `?prob-bdd` also admits the empty-proof base `.zero` before disjunctions
  are folded in. -/
  | queryBDD_bottom (q : GroundAtom σ) :
      ProbMeTTaCoreEval prog (.queryBDD q) .zero
  /-- `?prob-bdd-ev () = bdd-1`. -/
  | queryBDDEv_nil :
      ProbMeTTaCoreEval prog (.queryBDDEv []) .one
  /-- `?prob-bdd-ev` conjoins the per-evidence query BDDs. -/
  | queryBDDEv_cons (q : GroundAtom σ) (rest : List (GroundAtom σ)) (fq fr : BDD n)
      (hq : ProbMeTTaCoreEval prog (.queryBDD q) fq)
      (hr : ProbMeTTaCoreEval prog (.queryBDDEv rest) fr) :
      ProbMeTTaCoreEval prog (.queryBDDEv (q :: rest)) (apply (· && ·) fq fr)

theorem probMeTTaCoreEval_probGoal_pos_iff_ground {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) (q : GroundAtom σ) (f : BDD n) :
    ProbMeTTaCoreEval prog (.probGoal (.pos q)) f ↔ GroundBDDCompile prog q f := by
  constructor
  · intro h
    cases h with
    | probGoal_pos _ _ hq => exact hq
  · intro h
    exact .probGoal_pos q f h

theorem probMeTTaCoreEval_probNot_iff {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) (q : GroundAtom σ) (f : BDD n) :
    ProbMeTTaCoreEval prog (.probNot q) f ↔
      ∃ fa : BDD n, GroundBDDCompile prog q fa ∧
        (∀ a, queryHoldsA prog q a → fa.eval a = true) ∧
        f = bddNot fa := by
  constructor
  · intro h
    cases h with
    | probNot atom fa ha ha_complete =>
        exact ⟨fa, ha, ha_complete, rfl⟩
  · rintro ⟨fa, ha, ha_complete, rfl⟩
    exact .probNot q fa ha ha_complete

theorem probMeTTaCoreEval_execConj_iff {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) (goals : List (GoalLit σ)) (f : BDD n) :
    ProbMeTTaCoreEval prog (.execConj goals) f ↔ GoalBDDCompile prog goals f := by
  constructor
  · intro h
    cases h with
    | execConj_nil =>
        exact .nil
    | execConj_cons_pos atom rest fg fr hg hr =>
        have hfg : GroundBDDCompile prog atom fg :=
          (probMeTTaCoreEval_probGoal_pos_iff_ground prog atom fg).1 hg
        have hfr : GoalBDDCompile prog rest fr :=
          (probMeTTaCoreEval_execConj_iff prog rest fr).1 hr
        exact .posAtom atom rest fg fr hfg hfr
    | execConj_cons_neg atom fnot fr rest hg hr =>
        rcases (probMeTTaCoreEval_probNot_iff prog atom fnot).1 (by
          cases hg with
          | probGoal_neg _ _ hnot => exact hnot) with
          ⟨fa, hfa, hcomplete, hfnot⟩
        subst hfnot
        have hfr : GoalBDDCompile prog rest fr :=
          (probMeTTaCoreEval_execConj_iff prog rest fr).1 hr
        exact .negAtom atom rest fa fr hfa hcomplete hfr
    | execConj_cons_neq a b rest =>
        rename_i hg hrest
        have hfr : GoalBDDCompile prog rest f :=
          (probMeTTaCoreEval_execConj_iff prog rest f).1 hrest
        cases hg with
        | probGoal_neq _ _ hne =>
            exact .neqGuard a b rest f hne hfr
  · intro h
    induction h with
    | nil =>
        exact .execConj_nil
    | posAtom atom rest fa fr ha hr ih =>
        exact .execConj_cons_pos atom rest fa fr
          (.probGoal_pos atom fa ha) ih
    | negAtom atom rest fa fr ha hcomplete hr ih =>
        exact .execConj_cons_neg atom (bddNot fa) fr rest
          (.probGoal_neg atom (bddNot fa) (.probNot atom fa ha hcomplete)) ih
    | neqGuard a b rest fr hne hr ih =>
        exact .execConj_cons_neq a b rest fr
          (.probGoal_neq a b hne) ih

private theorem probMeTTaCoreEval_queryBDD_to_ground {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) {e : ProbMeTTaCoreExpr σ} {f : BDD n}
    (h : ProbMeTTaCoreEval prog e f) :
    ∀ q, e = .queryBDD q → GroundBDDCompile prog q f := by
  induction h with
  | queryBDD_single q' f hgoal =>
      intro q he
      cases he
      exact (probMeTTaCoreEval_probGoal_pos_iff_ground prog q' f).1 hgoal
  | queryBDD_disj q' f₁ f₂ h₁ h₂ ih₁ ih₂ =>
      intro q he
      cases he
      exact .disj q' f₁ f₂ (ih₁ q' rfl) (ih₂ q' rfl)
  | queryBDD_bottom q' =>
      intro q he
      cases he
      exact .bottom q'
  | queryBDDEv_nil =>
      intro q he
      cases he
  | queryBDDEv_cons q' rest fq fr hq hr ihq ihr =>
      intro q he
      cases he
  | probAssume i =>
      intro q he
      cases he
  | probNot atom fa ha ha_complete =>
      intro q he
      cases he
  | probGoal_pos atom f hq =>
      intro q he
      cases he
  | probGoal_neg atom f h =>
      intro q he
      cases he
  | probGoal_neq a b hne =>
      intro q he
      cases he
  | execConj_nil =>
      intro q he
      cases he
  | execConj_cons_pos atom rest fg fr hg hr ihg ihr =>
      intro q he
      cases he
  | execConj_cons_neg atom fnot fr rest hg hr ihg ihr =>
      intro q he
      cases he
  | execConj_cons_neq a b rest fr hg hr ihg ihr =>
      intro q he
      cases he

theorem probMeTTaCoreEval_queryBDD_iff_ground {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) (q : GroundAtom σ) (f : BDD n) :
    ProbMeTTaCoreEval prog (.queryBDD q) f ↔ GroundBDDCompile prog q f := by
  constructor
  · intro h
    exact probMeTTaCoreEval_queryBDD_to_ground prog h q rfl
  · intro h
    induction h with
    | fact i =>
        exact .queryBDD_single (prog.probFacts i) (bddVar i) (.probGoal_pos _ _ (.fact i))
    | ruleNil head hrule =>
        exact .queryBDD_single head .one (.probGoal_pos _ _ (.ruleNil _ hrule))
    | ruleOne head body hrule fb hb ih =>
        exact .queryBDD_single head fb (.probGoal_pos _ _ (.ruleOne _ _ hrule _ hb))
    | rulePair head b₁ b₂ rest hrule f₁ f₂ h₁ h₂ frest hlen hrest conjBDD hconj =>
        exact .queryBDD_single head conjBDD
          (.probGoal_pos _ _ (.rulePair _ _ _ _ hrule _ _ h₁ h₂ _ hlen hrest _ hconj))
    | ruleG head c g hc hhead bodyBDDs hlen hbody conjBDD hconj =>
        exact .queryBDD_single head conjBDD
          (.probGoal_pos _ _ (.ruleG _ _ _ hc hhead _ hlen hbody _ hconj))
    | disj q f₁ f₂ h₁ h₂ ih₁ ih₂ =>
        exact .queryBDD_disj q f₁ f₂ ih₁ ih₂
    | bottom q =>
        exact .queryBDD_bottom q

theorem probMeTTaCoreEval_queryBDDEv_iff_goals {σ : LPSignature} {n : ℕ}
    (prog : ProbLogProgram σ n) (qs : List (GroundAtom σ)) (f : BDD n) :
    ProbMeTTaCoreEval prog (.queryBDDEv qs) f ↔
      GoalBDDCompile prog (qs.map GoalLit.pos) f := by
  constructor
  · intro h
    cases h with
    | queryBDDEv_nil =>
        simpa using (GoalBDDCompile.nil (prog := prog))
    | queryBDDEv_cons q rest fq fr hq hr =>
        have hfq : GroundBDDCompile prog q fq :=
          (probMeTTaCoreEval_queryBDD_iff_ground prog q fq).1 hq
        have hfr : GoalBDDCompile prog (rest.map GoalLit.pos) fr :=
          (probMeTTaCoreEval_queryBDDEv_iff_goals prog rest fr).1 hr
        simpa using (GoalBDDCompile.posAtom (prog := prog) q (rest.map GoalLit.pos) fq fr hfq hfr)
  · intro h
    induction qs generalizing f with
    | nil =>
        cases h
        exact .queryBDDEv_nil
    | cons q rest ih =>
        have hcons : GoalBDDCompile prog (.pos q :: rest.map GoalLit.pos) f := by
          simpa using h
        cases hcons with
        | posAtom _ _ fq fr hq hrest =>
            simpa using
              (ProbMeTTaCoreEval.queryBDDEv_cons (prog := prog) q rest fq fr
                ((probMeTTaCoreEval_queryBDD_iff_ground prog q fq).2 hq)
                (ih fr hrest))

theorem probMeTTaCoreEval_probGoal_sound {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbLogProgram σ n) (g : GoalLit σ) (f : BDD n)
    (h : ProbMeTTaCoreEval prog (.probGoal g) f)
    (a : Fin n → Bool) (hf : f.eval a = true) :
    g.holds prog a := by
  cases g with
  | pos atom =>
      exact GroundBDDCompile_sound prog atom f
        ((probMeTTaCoreEval_probGoal_pos_iff_ground prog atom f).1 h) a hf
  | neg atom =>
      rcases (probMeTTaCoreEval_probNot_iff prog atom f).1 (by
        cases h with
        | probGoal_neg _ _ hnot => exact hnot) with ⟨fa, hfa, hcomplete, hEq⟩
      subst hEq
      intro hholds
      have hfa_true := hcomplete a hholds
      rw [bddNot_eval] at hf
      simp [hfa_true] at hf
  | neq ga gb =>
      cases h with
      | probGoal_neq _ _ hne => exact hne

theorem probMeTTaCoreEval_execConj_sound {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbLogProgram σ n) (goals : List (GoalLit σ)) (f : BDD n)
    (h : ProbMeTTaCoreEval prog (.execConj goals) f)
    (a : Fin n → Bool) (hf : f.eval a = true) :
    ∀ g ∈ goals, g.holds prog a := by
  have hcompile := (probMeTTaCoreEval_execConj_iff prog goals f).1 h
  exact GoalBDDCompile_sound prog goals f hcompile a hf

theorem probMeTTaCoreEval_queryBDD_sound {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbLogProgram σ n) (q : GroundAtom σ) (f : BDD n)
    (h : ProbMeTTaCoreEval prog (.queryBDD q) f)
    (a : Fin n → Bool) (hf : f.eval a = true) :
    queryHoldsA prog q a := by
  exact GroundBDDCompile_sound prog q f
    ((probMeTTaCoreEval_queryBDD_iff_ground prog q f).1 h) a hf

theorem probMeTTaCoreEval_queryBDDEv_sound {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbLogProgram σ n) (qs : List (GroundAtom σ)) (f : BDD n)
    (h : ProbMeTTaCoreEval prog (.queryBDDEv qs) f)
    (a : Fin n → Bool) (hf : f.eval a = true) :
    ∀ q ∈ qs, queryHoldsA prog q a := by
  have hcompile := (probMeTTaCoreEval_queryBDDEv_iff_goals prog qs f).1 h
  intro q hq
  have hmem : GoalLit.pos q ∈ qs.map GoalLit.pos := by
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  exact GoalBDDCompile_sound prog (qs.map GoalLit.pos) f hcompile a hf
    (.pos q) hmem

theorem probMeTTaCoreEval_queryBDDEv_complete {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbLogProgram σ n) (qs : List (GroundAtom σ))
    (a : Fin n → Bool) (hq : ∀ q ∈ qs, queryHoldsA prog q a) :
    ∃ f : BDD n, ProbMeTTaCoreEval prog (.queryBDDEv qs) f ∧ f.eval a = true := by
  have hgoals : ∀ g ∈ qs.map GoalLit.pos, g.holds prog a := by
    intro g hg
    obtain ⟨q, hq_mem, rfl⟩ := List.mem_map.mp hg
    exact hq q hq_mem
  obtain ⟨f, hgoal, hf⟩ := GoalBDDCompile_complete prog (qs.map GoalLit.pos) a hgoals
  exact ⟨f, (probMeTTaCoreEval_queryBDDEv_iff_goals prog qs f).2 hgoal, hf⟩

theorem probMeTTaCoreEval_queryBDD_complete {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbLogProgram σ n) (q : GroundAtom σ)
    (a : Fin n → Bool) (hq : queryHoldsA prog q a) :
    ∃ f : BDD n, ProbMeTTaCoreEval prog (.queryBDD q) f ∧ f.eval a = true := by
  obtain ⟨f, hground, hf⟩ := GroundBDDCompile_complete prog q a hq
  exact ⟨f, (probMeTTaCoreEval_queryBDD_iff_ground prog q f).2 hground, hf⟩

theorem exists_ordered_probMeTTa_queryBDD_exact {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbLogProgram σ n) (q : GroundAtom σ) :
    ∃ f : BDD n, ProbMeTTaCoreEval prog (.queryBDD q) f ∧ f.Ordered none ∧
      (∀ a, f.eval a = true ↔ queryHoldsA prog q a) := by
  obtain ⟨f, hground, hcomplete⟩ := exists_complete_bdd prog q
  refine ⟨f, (probMeTTaCoreEval_queryBDD_iff_ground prog q f).2 hground,
    GroundBDDCompile_ordered prog q f hground, ?_⟩
  intro a
  constructor
  · intro hf
    exact GroundBDDCompile_sound prog q f hground a hf
  · intro hq
    exact hcomplete a hq

theorem exists_ordered_probMeTTa_queryBDDEv_exact {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbLogProgram σ n) (qs : List (GroundAtom σ)) :
    ∃ f : BDD n, ProbMeTTaCoreEval prog (.queryBDDEv qs) f ∧ f.Ordered none ∧
      (∀ a, f.eval a = true ↔ ∀ q ∈ qs, queryHoldsA prog q a) := by
  induction qs with
  | nil =>
      refine ⟨.one, .queryBDDEv_nil, .one, ?_⟩
      intro a
      simp
  | cons q rest ih =>
      obtain ⟨fq, hqeval, hordq, hqiff⟩ := exists_ordered_probMeTTa_queryBDD_exact prog q
      obtain ⟨fr, hrev, hordr, hriff⟩ := ih
      refine ⟨apply (· && ·) fq fr, .queryBDDEv_cons q rest fq fr hqeval hrev,
        apply_ordered _ _ _ _ hordq hordr, ?_⟩
      intro a
      rw [apply_eval]
      simp [hqiff a, hriff a]

end Mettapedia.Logic.BDDCore
