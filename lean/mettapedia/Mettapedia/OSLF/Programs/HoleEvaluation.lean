import Mettapedia.Logic.TheoryModel.Basic

/-!
# Evaluation around holes, and fill-and-resume

A small call-by-value calculus with named holes: numbers, booleans, addition,
conditionals, λ-abstraction and application, with de Bruijn variables.

**Evaluation proceeds around holes** (`Eval`).  A hole evaluates to a *hole
closure* `Res.hole u env`, which records the environment in which the hole was
reached.  Operations that need the value of a hole produce *indeterminate
results* instead of failing: a sum with an indeterminate summand
(`Res.add`), a conditional on an indeterminate condition, whose branches are
kept unevaluated together with their environment (`Res.ite`), and an
application of an indeterminate function (`Res.app`).  Indeterminate results
are values for the purposes of evaluation, so evaluation continues past them:
one hole may be reached several times, under different environments
(`HoleInstances`).

**Filling** (`Tm.fill σ`) replaces every hole `u` by `σ u`, read in the hole's
own scope.  **Resumption** (`Resume σ`) takes a result of the unfilled program
and continues it: each hole closure evaluates its filler in its recorded
environment (after resuming that environment), and each indeterminate
operation is retried on the resumed operands.

**Fill-and-resume.**
* Whenever the filled program evaluates, its result is the resumption of the
  unfilled program's result (`Eval.resume_of_eval_fill`).  No determinism and
  no termination assumption is needed.
* Evaluation and resumption are deterministic (`Eval.deterministic`,
  `Resume.deterministic`), so when the filled program terminates, evaluating
  it and resuming agree exactly (`Eval.eval_fill_iff_resume`).
* The termination hypothesis cannot be dropped in a calculus with divergence:
  `(λx. 5) ⦇u⦈` evaluates to `5`, which resumes to `5` for every filling,
  while filling `u` with a divergent term gives a program with no result
  (`Divergence.resume_without_evaluation`).
* The recorded environments are necessary: resuming a hole closure in the
  environment of the whole program instead of its own gives a different
  answer (`Scoping.topLevel_resumption_differs`).
* The calculus must be pure: with a counter effect, resumption runs the
  filler after effects that followed the hole, and disagrees with evaluating
  the filled program (`Effects.commutation_fails`), while an effect-free filler
  agrees (`Effects.pure_filler_agrees`).

**Typed holes.**  With a hole context giving every hole a context and a type
(`HasTy`), filling every hole with a term of its type in its context preserves
typing (`HasTy.fill`, the static theorem behind fill-and-resume).  The typed
completion space (`typedCompletions`) consists of typed programs
(`hasTy_of_mem_typedCompletions`) and can be strictly smaller than the untyped
one (`TypedControl.typed_strict`).

**Completion spaces.**  The completions of a partial program are the complete
terms obtained by filling its holes (`completions`), a model class of the
theory–model Galois connection (`completions_eq_models`).  Filling is monotone
refinement of completion spaces (`completions_fill_subset`), strict in general
(`Refinement.fill_strict`).  A determinate result of the partial program is
the result of every terminating completion (`determinate_of_eval`), while an
indeterminate one is not (`Refinement.indeterminate_outputs_differ`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Programs.HoleEvaluation

open Mettapedia.Logic.TheoryModel

universe u

/-! ## Terms with holes -/

/-- Call-by-value terms with de Bruijn variables and holes named in `H`. -/
inductive Tm (H : Type u) : Type u
  | var (index : Nat)
  | num (value : Nat)
  | bool (value : Bool)
  | add (left right : Tm H)
  | ite (condition thenBranch elseBranch : Tm H)
  | lam (body : Tm H)
  | app (function argument : Tm H)
  | hole (name : H)

variable {H : Type u}

namespace Tm

/-- **Filling**: every hole `u` is replaced by `σ u`.  As in contextual
substitution, the filler is placed without shifting: it is read in the scope
of the hole, and may use the variables bound around it. -/
def fill (σ : H → Tm H) : Tm H → Tm H
  | var i => var i
  | num n => num n
  | bool b => bool b
  | add a b => add (fill σ a) (fill σ b)
  | ite c t e => ite (fill σ c) (fill σ t) (fill σ e)
  | lam b => lam (fill σ b)
  | app f a => app (fill σ f) (fill σ a)
  | hole u => σ u

/-- A term is complete when it contains no hole. -/
def Complete : Tm H → Prop
  | var _ => True
  | num _ => True
  | bool _ => True
  | add a b => Complete a ∧ Complete b
  | ite c t e => Complete c ∧ Complete t ∧ Complete e
  | lam b => Complete b
  | app f a => Complete f ∧ Complete a
  | hole _ => False

/-- Filling every hole with itself changes nothing. -/
theorem fill_hole (t : Tm H) : t.fill (fun u => hole u) = t := by
  induction t with
  | var => rfl
  | num => rfl
  | bool => rfl
  | add a b iha ihb => simp only [fill, iha, ihb]
  | ite c t e ihc iht ihe => simp only [fill, ihc, iht, ihe]
  | lam b ih => simp only [fill, ih]
  | app f a ihf iha => simp only [fill, ihf, iha]
  | hole => rfl

/-- Fillings compose. -/
theorem fill_fill (σ τ : H → Tm H) (t : Tm H) :
    (t.fill τ).fill σ = t.fill (fun u => (τ u).fill σ) := by
  induction t with
  | var => rfl
  | num => rfl
  | bool => rfl
  | add a b iha ihb => simp only [fill, iha, ihb]
  | ite c t e ihc iht ihe => simp only [fill, ihc, iht, ihe]
  | lam b ih => simp only [fill, ih]
  | app f a ihf iha => simp only [fill, ihf, iha]
  | hole => rfl

/-- Filling does not change a complete term. -/
theorem fill_of_complete (σ : H → Tm H) : ∀ {t : Tm H}, t.Complete → t.fill σ = t
  | var _, _ => rfl
  | num _, _ => rfl
  | bool _, _ => rfl
  | add _ _, ⟨ha, hb⟩ => by simp only [fill, fill_of_complete σ ha, fill_of_complete σ hb]
  | ite _ _ _, ⟨hc, ht, he⟩ => by
      simp only [fill, fill_of_complete σ hc, fill_of_complete σ ht, fill_of_complete σ he]
  | lam b, hb => congrArg lam (fill_of_complete σ (t := b) hb)
  | app _ _, ⟨hf, ha⟩ => by simp only [fill, fill_of_complete σ hf, fill_of_complete σ ha]

end Tm

/-! ## Results: values and indeterminate forms -/

/-- Results of evaluation.  `num`, `bool` and `clo` are values; `hole`, `add`,
`ite` and `app` are indeterminate results. -/
inductive Res (H : Type u) : Type u
  /-- A number. -/
  | num (value : Nat)
  /-- A boolean. -/
  | bool (value : Bool)
  /-- A closure: an environment and a body with one more variable. -/
  | clo (env : List (Res H)) (body : Tm H)
  /-- A hole closure: the hole reached, with the environment it was reached in. -/
  | hole (name : H) (env : List (Res H))
  /-- A sum with an indeterminate summand. -/
  | add (left right : Res H)
  /-- A conditional on an indeterminate condition, with its branches kept
  unevaluated in their environment. -/
  | ite (condition : Res H) (env : List (Res H)) (thenBranch elseBranch : Tm H)
  /-- An application of an indeterminate function. -/
  | app (function argument : Res H)

namespace Res

/-- The indeterminate results. -/
inductive Indet : Res H → Prop
  | hole (name : H) (env : List (Res H)) : Indet (hole name env)
  | add (left right : Res H) : Indet (add left right)
  | ite (condition : Res H) (env : List (Res H)) (thenBranch elseBranch : Tm H) :
      Indet (ite condition env thenBranch elseBranch)
  | app (function argument : Res H) : Indet (app function argument)

theorem not_indet_num (n : Nat) : ¬ (num n : Res H).Indet := nofun
theorem not_indet_bool (b : Bool) : ¬ (bool b : Res H).Indet := nofun
theorem not_indet_clo (env : List (Res H)) (body : Tm H) : ¬ (clo env body).Indet := nofun

end Res

/-- Addition on results: numbers add, and a sum with an indeterminate summand
is indeterminate.  A summand that is a boolean or a closure is a type error,
and has no rule. -/
inductive Plus : Res H → Res H → Res H → Prop
  | num (m n : Nat) : Plus (.num m) (.num n) (.num (m + n))
  | indetLeft {left right : Res H} :
      left.Indet → right.Indet ∨ (∃ n, right = .num n) → Plus left right (.add left right)
  | indetRight {m : Nat} {right : Res H} :
      right.Indet → Plus (.num m) right (.add (.num m) right)

theorem Plus.deterministic {a b r r' : Res H} (first : Plus a b r) (second : Plus a b r') :
    r = r' := by
  cases first with
  | num m n =>
    cases second with
    | num => rfl
    | indetLeft hl _ => exact absurd hl (Res.not_indet_num _)
    | indetRight hr => exact absurd hr (Res.not_indet_num _)
  | indetLeft hl hr =>
    cases second with
    | num => exact absurd hl (Res.not_indet_num _)
    | indetLeft => rfl
    | indetRight => exact absurd hl (Res.not_indet_num _)
  | indetRight hr =>
    cases second with
    | num => exact absurd hr (Res.not_indet_num _)
    | indetLeft hl => exact absurd hl (Res.not_indet_num _)
    | indetRight => rfl

/-! ## Evaluation around holes -/

/-- **Big-step call-by-value evaluation around holes.**  Indeterminate
results count as values: they are passed as arguments and bound in
environments.  Type errors (adding a boolean, branching on a number, applying
a number) have no rule. -/
inductive Eval : List (Res H) → Tm H → Res H → Prop
  | var {env : List (Res H)} {i : Nat} {r : Res H} :
      env[i]? = some r → Eval env (.var i) r
  | num (env : List (Res H)) (n : Nat) : Eval env (.num n) (.num n)
  | bool (env : List (Res H)) (b : Bool) : Eval env (.bool b) (.bool b)
  | add {env : List (Res H)} {a b : Tm H} {ra rb r : Res H} :
      Eval env a ra → Eval env b rb → Plus ra rb r → Eval env (.add a b) r
  | iteTrue {env : List (Res H)} {c t e : Tm H} {r : Res H} :
      Eval env c (.bool true) → Eval env t r → Eval env (.ite c t e) r
  | iteFalse {env : List (Res H)} {c t e : Tm H} {r : Res H} :
      Eval env c (.bool false) → Eval env e r → Eval env (.ite c t e) r
  | iteIndet {env : List (Res H)} {c t e : Tm H} {rc : Res H} :
      Eval env c rc → rc.Indet → Eval env (.ite c t e) (.ite rc env t e)
  | lam (env : List (Res H)) (b : Tm H) : Eval env (.lam b) (.clo env b)
  | appClo {env cenv : List (Res H)} {f a b : Tm H} {v r : Res H} :
      Eval env f (.clo cenv b) → Eval env a v → Eval (v :: cenv) b r → Eval env (.app f a) r
  | appIndet {env : List (Res H)} {f a : Tm H} {rf v : Res H} :
      Eval env f rf → rf.Indet → Eval env a v → Eval env (.app f a) (.app rf v)
  | hole (env : List (Res H)) (u : H) : Eval env (.hole u) (.hole u env)

/-- **Evaluation is deterministic.** -/
theorem Eval.deterministic {env : List (Res H)} {t : Tm H} {r r' : Res H}
    (first : Eval env t r) (second : Eval env t r') : r = r' := by
  induction first generalizing r' with
  | var hr => cases second with | var hr' => rw [hr] at hr'; exact Option.some.inj hr'
  | num => cases second; rfl
  | bool => cases second; rfl
  | add _ _ hplus iha ihb =>
    cases second with
    | add ha' hb' hplus' =>
      rw [iha ha', ihb hb'] at hplus
      exact hplus.deterministic hplus'
  | iteTrue _ _ ihc iht =>
    cases second with
    | iteTrue _ ht' => exact iht ht'
    | iteFalse hc' _ => exact Res.bool.inj (ihc hc') |> Bool.noConfusion
    | iteIndet hc' hi => exact absurd (ihc hc' ▸ hi) (Res.not_indet_bool _)
  | iteFalse _ _ ihc ihe =>
    cases second with
    | iteTrue hc' _ => exact Res.bool.inj (ihc hc') |> Bool.noConfusion
    | iteFalse _ he' => exact ihe he'
    | iteIndet hc' hi => exact absurd (ihc hc' ▸ hi) (Res.not_indet_bool _)
  | iteIndet _ hi ihc =>
    cases second with
    | iteTrue hc' _ => exact absurd (ihc hc' ▸ hi) (Res.not_indet_bool _)
    | iteFalse hc' _ => exact absurd (ihc hc' ▸ hi) (Res.not_indet_bool _)
    | iteIndet hc' _ => rw [ihc hc']
  | lam => cases second; rfl
  | appClo _ _ _ ihf iha ihb =>
    cases second with
    | appClo hf' ha' hb' =>
      cases ihf hf'
      cases iha ha'
      exact ihb hb'
    | appIndet hf' hi _ => exact absurd (ihf hf' ▸ hi) (Res.not_indet_clo _ _)
  | appIndet _ hi _ ihf iha =>
    cases second with
    | appClo hf' _ _ => exact absurd ((ihf hf').symm ▸ hi) (Res.not_indet_clo _ _)
    | appIndet hf' _ ha' => rw [ihf hf', iha ha']
  | hole => cases second; rfl

/-! ## Resumption after filling -/

mutual
/-- **Resumption** of a result after filling with `σ`: hole closures evaluate
their filler in their resumed environment, closures and delayed branches are
filled, and indeterminate operations are retried on the resumed operands. -/
inductive Resume (σ : H → Tm H) : Res H → Res H → Prop
  | num (n : Nat) : Resume σ (.num n) (.num n)
  | bool (b : Bool) : Resume σ (.bool b) (.bool b)
  | clo {env env' : List (Res H)} (body : Tm H) :
      ResumeEnv σ env env' → Resume σ (.clo env body) (.clo env' (body.fill σ))
  | hole {u : H} {env env' : List (Res H)} {r : Res H} :
      ResumeEnv σ env env' → Eval env' (σ u) r → Resume σ (.hole u env) r
  | add {left right left' right' sum : Res H} :
      Resume σ left left' → Resume σ right right' → Plus left' right' sum →
        Resume σ (.add left right) sum
  | iteTrue {c : Res H} {env env' : List (Res H)} {t e : Tm H} {r : Res H} :
      Resume σ c (.bool true) → ResumeEnv σ env env' → Eval env' (t.fill σ) r →
        Resume σ (.ite c env t e) r
  | iteFalse {c : Res H} {env env' : List (Res H)} {t e : Tm H} {r : Res H} :
      Resume σ c (.bool false) → ResumeEnv σ env env' → Eval env' (e.fill σ) r →
        Resume σ (.ite c env t e) r
  | iteIndet {c c' : Res H} {env env' : List (Res H)} {t e : Tm H} :
      Resume σ c c' → c'.Indet → ResumeEnv σ env env' →
        Resume σ (.ite c env t e) (.ite c' env' (t.fill σ) (e.fill σ))
  | appClo {f a v r : Res H} {cenv : List (Res H)} {body : Tm H} :
      Resume σ f (.clo cenv body) → Resume σ a v → Eval (v :: cenv) body r →
        Resume σ (.app f a) r
  | appIndet {f f' a a' : Res H} :
      Resume σ f f' → f'.Indet → Resume σ a a' → Resume σ (.app f a) (.app f' a')

/-- Resumption of an environment, entry by entry. -/
inductive ResumeEnv (σ : H → Tm H) : List (Res H) → List (Res H) → Prop
  | nil : ResumeEnv σ [] []
  | cons {r r' : Res H} {env env' : List (Res H)} :
      Resume σ r r' → ResumeEnv σ env env' → ResumeEnv σ (r :: env) (r' :: env')
end

variable {σ : H → Tm H}

/-- A resumed environment resumes each entry. -/
theorem ResumeEnv.getElem? : ∀ {env env' : List (Res H)}, ResumeEnv σ env env' →
    ∀ {i : Nat} {r : Res H}, env[i]? = some r → ∃ r', env'[i]? = some r' ∧ Resume σ r r'
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hr _, 0, _, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨_, rfl, hr⟩
  | _, _, .cons _ henv, i + 1, _, h => by
      simp only [List.getElem?_cons_succ] at h ⊢
      exact henv.getElem? h

theorem Resume.num_inv {n : Nat} {r : Res H} (h : Resume σ (.num n) r) : r = .num n := by
  cases h; rfl

theorem Resume.bool_inv {b : Bool} {r : Res H} (h : Resume σ (.bool b) r) : r = .bool b := by
  cases h; rfl

theorem Resume.clo_inv {env : List (Res H)} {body : Tm H} {r : Res H}
    (h : Resume σ (.clo env body) r) :
    ∃ env', ResumeEnv σ env env' ∧ r = .clo env' (body.fill σ) := by
  cases h with
  | clo _ henv => exact ⟨_, henv, rfl⟩

mutual
/-- **Resumption is deterministic.** -/
theorem Resume.deterministic : ∀ {r r₁ r₂ : Res H},
    Resume σ r r₁ → Resume σ r r₂ → r₁ = r₂
  | _, _, _, .num _, .num _ => rfl
  | _, _, _, .bool _, .bool _ => rfl
  | _, _, _, .clo _ h₁, .clo _ h₂ => by rw [ResumeEnv.deterministic h₁ h₂]
  | _, _, _, .hole h₁ e₁, .hole h₂ e₂ => by
      cases ResumeEnv.deterministic h₁ h₂
      exact e₁.deterministic e₂
  | _, _, _, .add l₁ r₁ p₁, .add l₂ r₂ p₂ => by
      cases Resume.deterministic l₁ l₂
      cases Resume.deterministic r₁ r₂
      exact p₁.deterministic p₂
  | _, _, _, .iteTrue _ h₁ e₁, .iteTrue _ h₂ e₂ => by
      cases ResumeEnv.deterministic h₁ h₂
      exact e₁.deterministic e₂
  | _, _, _, .iteTrue c₁ _ _, .iteFalse c₂ _ _ =>
      Bool.noConfusion (Res.bool.inj (Resume.deterministic c₁ c₂))
  | _, _, _, .iteTrue c₁ _ _, .iteIndet c₂ hi _ =>
      absurd (Resume.deterministic c₁ c₂ ▸ hi) (Res.not_indet_bool _)
  | _, _, _, .iteFalse c₁ _ _, .iteTrue c₂ _ _ =>
      Bool.noConfusion (Res.bool.inj (Resume.deterministic c₁ c₂))
  | _, _, _, .iteFalse _ h₁ e₁, .iteFalse _ h₂ e₂ => by
      cases ResumeEnv.deterministic h₁ h₂
      exact e₁.deterministic e₂
  | _, _, _, .iteFalse c₁ _ _, .iteIndet c₂ hi _ =>
      absurd (Resume.deterministic c₁ c₂ ▸ hi) (Res.not_indet_bool _)
  | _, _, _, .iteIndet c₁ hi _, .iteTrue c₂ _ _ =>
      absurd ((Resume.deterministic c₁ c₂).symm ▸ hi) (Res.not_indet_bool _)
  | _, _, _, .iteIndet c₁ hi _, .iteFalse c₂ _ _ =>
      absurd ((Resume.deterministic c₁ c₂).symm ▸ hi) (Res.not_indet_bool _)
  | _, _, _, .iteIndet c₁ _ h₁, .iteIndet c₂ _ h₂ => by
      rw [Resume.deterministic c₁ c₂, ResumeEnv.deterministic h₁ h₂]
  | _, _, _, .appClo f₁ a₁ e₁, .appClo f₂ a₂ e₂ => by
      cases Resume.deterministic f₁ f₂
      cases Resume.deterministic a₁ a₂
      exact e₁.deterministic e₂
  | _, _, _, .appClo f₁ _ _, .appIndet f₂ hi _ =>
      absurd ((Resume.deterministic f₁ f₂).symm ▸ hi) (Res.not_indet_clo _ _)
  | _, _, _, .appIndet f₁ hi _, .appClo f₂ _ _ =>
      absurd (Resume.deterministic f₁ f₂ ▸ hi) (Res.not_indet_clo _ _)
  | _, _, _, .appIndet f₁ _ a₁, .appIndet f₂ _ a₂ => by
      rw [Resume.deterministic f₁ f₂, Resume.deterministic a₁ a₂]

/-- Resumption of environments is deterministic. -/
theorem ResumeEnv.deterministic : ∀ {env env₁ env₂ : List (Res H)},
    ResumeEnv σ env env₁ → ResumeEnv σ env env₂ → env₁ = env₂
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons r₁ e₁, .cons r₂ e₂ => by
      rw [Resume.deterministic r₁ r₂, ResumeEnv.deterministic e₁ e₂]
end

/-! ## Fill-and-resume -/

/-- **Fill-and-resume, soundness.**  If the filled program evaluates, its
result is the resumption of the unfilled program's result.  Environments are
related by resumption; at top level both are empty. -/
theorem Eval.resume_of_eval_fill {env : List (Res H)} {t : Tm H} {r : Res H}
    (h : Eval env t r) :
    ∀ {env' : List (Res H)}, ResumeEnv σ env env' →
      ∀ {r' : Res H}, Eval env' (t.fill σ) r' → Resume σ r r' := by
  induction h with
  | var hr =>
    intro env' henv r' h'
    cases h' with
    | var hr' =>
      obtain ⟨r'', hr'', hres⟩ := henv.getElem? hr
      rw [hr''] at hr'
      cases hr'
      exact hres
  | num => intro env' _ r' h'; cases h'; exact .num _
  | bool => intro env' _ r' h'; cases h'; exact .bool _
  | add _ _ hplus iha ihb =>
    intro env' henv r' h'
    cases h' with
    | add ha' hb' hplus' =>
      have ra := iha henv ha'
      have rb := ihb henv hb'
      cases hplus with
      | num m n =>
        cases ra.num_inv
        cases rb.num_inv
        cases hplus'
        · exact .num _
        · rename_i hl _; exact absurd hl (Res.not_indet_num _)
        · rename_i hr; exact absurd hr (Res.not_indet_num _)
      | indetLeft => exact .add ra rb hplus'
      | indetRight => exact .add ra rb hplus'
  | iteTrue _ _ ihc iht =>
    intro env' henv r' h'
    cases h' with
    | iteTrue _ ht' => exact iht henv ht'
    | iteFalse hc' _ => exact Bool.noConfusion (Res.bool.inj (ihc henv hc').bool_inv)
    | iteIndet hc' hi => exact absurd ((ihc henv hc').bool_inv ▸ hi) (Res.not_indet_bool _)
  | iteFalse _ _ ihc ihe =>
    intro env' henv r' h'
    cases h' with
    | iteTrue hc' _ => exact Bool.noConfusion (Res.bool.inj (ihc henv hc').bool_inv)
    | iteFalse _ he' => exact ihe henv he'
    | iteIndet hc' hi => exact absurd ((ihc henv hc').bool_inv ▸ hi) (Res.not_indet_bool _)
  | iteIndet _ _ ihc =>
    intro env' henv r' h'
    cases h' with
    | iteTrue hc' ht' => exact .iteTrue (ihc henv hc') henv ht'
    | iteFalse hc' he' => exact .iteFalse (ihc henv hc') henv he'
    | iteIndet hc' hi => exact .iteIndet (ihc henv hc') hi henv
  | lam => intro env' henv r' h'; cases h'; exact .clo _ henv
  | appClo _ _ _ ihf iha ihb =>
    intro env' henv r' h'
    cases h' with
    | appClo hf' ha' hb' =>
      obtain ⟨cenv', hcenv, hclo⟩ := (ihf henv hf').clo_inv
      cases hclo
      exact ihb (.cons (iha henv ha') hcenv) hb'
    | appIndet hf' hi _ =>
      obtain ⟨_, _, hclo⟩ := (ihf henv hf').clo_inv
      subst hclo
      exact absurd hi (Res.not_indet_clo _ _)
  | appIndet _ _ _ ihf iha =>
    intro env' henv r' h'
    cases h' with
    | appClo hf' ha' hb' => exact .appClo (ihf henv hf') (iha henv ha') hb'
    | appIndet hf' hi ha' => exact .appIndet (ihf henv hf') hi (iha henv ha')
  | hole => intro env' henv r' h'; exact .hole henv h'

/-- **Fill-and-resume.**  When the filled program terminates, evaluating it
and resuming the unfilled program's result give the same answer. -/
theorem Eval.eval_fill_iff_resume {env env' : List (Res H)} {t : Tm H} {r : Res H}
    (h : Eval env t r) (henv : ResumeEnv σ env env')
    (terminates : ∃ r'', Eval env' (t.fill σ) r'') (r' : Res H) :
    Eval env' (t.fill σ) r' ↔ Resume σ r r' := by
  obtain ⟨r'', h''⟩ := terminates
  constructor
  · exact h.resume_of_eval_fill henv
  · intro hres
    rw [Resume.deterministic hres (h.resume_of_eval_fill henv h'')]
    exact h''

/-- At top level. -/
theorem Eval.resume_of_eval_fill_nil {t : Tm H} {r r' : Res H} (h : Eval [] t r)
    (h' : Eval [] (t.fill σ) r') : Resume σ r r' :=
  h.resume_of_eval_fill .nil h'

/-- Filling every hole with itself resumes a top-level result to itself. -/
theorem Eval.resume_holes_self {t : Tm H} {r : Res H} (h : Eval [] t r) :
    Resume (fun u => .hole u) r r := by
  apply h.resume_of_eval_fill_nil
  rw [Tm.fill_hole]
  exact h

/-! ## Completion spaces -/

/-- `t` completes `P`: `t` is complete and some filling of `P` gives `t`. -/
def Completes (t P : Tm H) : Prop :=
  t.Complete ∧ ∃ σ : H → Tm H, P.fill σ = t

/-- **The completion space** of a partial program. -/
def completions (P : Tm H) : Set (Tm H) :=
  {t | Completes t P}

/-- The completion space is the model class of the one-sentence theory
`{P}`, for completion as satisfaction. -/
theorem completions_eq_models (P : Tm H) : completions P = models Completes {P} := by
  ext t
  exact ⟨fun h _ hmem => hmem ▸ h, fun h => h rfl⟩

/-- **Hole filling is monotone refinement**: filling shrinks the completion
space. -/
theorem completions_fill_subset (τ : H → Tm H) (P : Tm H) :
    completions (P.fill τ) ⊆ completions P := by
  rintro t ⟨complete, σ, rfl⟩
  exact ⟨complete, fun u => (τ u).fill σ, (Tm.fill_fill σ τ P).symm⟩

/-- In the theory–model reading, a filling entails the partial program it
fills. -/
theorem entails_fill (τ : H → Tm H) (P : Tm H) : Entails Completes {P.fill τ} P := by
  intro t member
  exact completions_fill_subset τ P (member rfl)

/-- A complete program is its own only completion. -/
theorem completions_of_complete {P : Tm H} (hP : P.Complete) : completions P = {P} := by
  ext t
  constructor
  · rintro ⟨_, σ, rfl⟩
    exact Tm.fill_of_complete σ hP
  · intro member
    rw [Set.mem_singleton_iff] at member
    subst member
    exact ⟨hP, fun u => .hole u, Tm.fill_hole _⟩

/-- **A determinate result is the result of every terminating completion.**
Evaluation around holes can therefore report behaviour that no filling can
change. -/
theorem determinate_of_eval {P t : Tm H} {n : Nat} (hP : Eval [] P (.num n))
    (ht : t ∈ completions P) {r' : Res H} (h' : Eval [] t r') : r' = .num n := by
  obtain ⟨_, σ, rfl⟩ := ht
  exact (hP.resume_of_eval_fill_nil h').num_inv

/-- The same for boolean results. -/
theorem determinate_of_eval_bool {P t : Tm H} {b : Bool} (hP : Eval [] P (.bool b))
    (ht : t ∈ completions P) {r' : Res H} (h' : Eval [] t r') : r' = .bool b := by
  obtain ⟨_, σ, rfl⟩ := ht
  exact (hP.resume_of_eval_fill_nil h').bool_inv

/-! ## Typed holes -/

/-- Simple types. -/
inductive Ty where
  | num
  | bool
  | arr (dom cod : Ty)

/-- **Typing with typed holes**: the hole context `Δ` gives every hole the
context it is used in and its type. -/
inductive HasTy (Δ : H → List Ty × Ty) : List Ty → Tm H → Ty → Prop
  | var {Γ : List Ty} {i : Nat} {A : Ty} : Γ[i]? = some A → HasTy Δ Γ (.var i) A
  | num (Γ : List Ty) (n : Nat) : HasTy Δ Γ (.num n) .num
  | bool (Γ : List Ty) (b : Bool) : HasTy Δ Γ (.bool b) .bool
  | add {Γ : List Ty} {a b : Tm H} :
      HasTy Δ Γ a .num → HasTy Δ Γ b .num → HasTy Δ Γ (.add a b) .num
  | ite {Γ : List Ty} {c t e : Tm H} {A : Ty} :
      HasTy Δ Γ c .bool → HasTy Δ Γ t A → HasTy Δ Γ e A → HasTy Δ Γ (.ite c t e) A
  | lam {Γ : List Ty} {body : Tm H} {A B : Ty} :
      HasTy Δ (A :: Γ) body B → HasTy Δ Γ (.lam body) (.arr A B)
  | app {Γ : List Ty} {f a : Tm H} {A B : Ty} :
      HasTy Δ Γ f (.arr A B) → HasTy Δ Γ a A → HasTy Δ Γ (.app f a) B
  | hole {Γ : List Ty} {A : Ty} {u : H} : Δ u = (Γ, A) → HasTy Δ Γ (.hole u) A

/-- **Filling preserves typing**: filling every hole with a term of its type,
in its context, gives a program of the same type (under any hole context for
the holes of the fillers). -/
theorem HasTy.fill {Δ Δ' : H → List Ty × Ty} {Γ : List Ty} {t : Tm H} {A : Ty}
    (typed : HasTy Δ Γ t A) {σ : H → Tm H} (fillers : ∀ u, HasTy Δ' (Δ u).1 (σ u) (Δ u).2) :
    HasTy Δ' Γ (t.fill σ) A := by
  induction typed with
  | var h => exact .var h
  | num => exact .num _ _
  | bool => exact .bool _ _
  | add _ _ iha ihb => exact .add iha ihb
  | ite _ _ _ ihc iht ihe => exact .ite ihc iht ihe
  | lam _ ih => exact .lam ih
  | app _ _ ihf iha => exact .app ihf iha
  | @hole Γ₀ A₀ u h =>
    have filler := fillers u
    rw [h] at filler
    exact filler

/-- A complete program is typed independently of the hole context. -/
theorem HasTy.change_holes {Δ Δ' : H → List Ty × Ty} {Γ : List Ty} {t : Tm H} {A : Ty}
    (typed : HasTy Δ Γ t A) (complete : t.Complete) : HasTy Δ' Γ t A := by
  induction typed with
  | var h => exact .var h
  | num => exact .num _ _
  | bool => exact .bool _ _
  | add _ _ iha ihb => exact .add (iha complete.1) (ihb complete.2)
  | ite _ _ _ ihc iht ihe => exact .ite (ihc complete.1) (iht complete.2.1) (ihe complete.2.2)
  | lam _ ih => exact .lam (ih complete)
  | app _ _ ihf iha => exact .app (ihf complete.1) (iha complete.2)
  | hole => exact complete.elim

/-- **The typed completion space**: fill every hole with a complete term of
its type in its context. -/
def typedCompletions (Δ : H → List Ty × Ty) (P : Tm H) : Set (Tm H) :=
  {t | t.Complete ∧ ∃ σ : H → Tm H,
    (∀ u, (σ u).Complete ∧ HasTy Δ (Δ u).1 (σ u) (Δ u).2) ∧ P.fill σ = t}

theorem typedCompletions_subset (Δ : H → List Ty × Ty) (P : Tm H) :
    typedCompletions Δ P ⊆ completions P :=
  fun _ ⟨complete, σ, _, equal⟩ => ⟨complete, σ, equal⟩

/-- **Typed completions of a typed partial program are typed programs.** -/
theorem hasTy_of_mem_typedCompletions {Δ : H → List Ty × Ty} {Γ : List Ty} {P t : Tm H}
    {A : Ty} (typed : HasTy Δ Γ P A) (member : t ∈ typedCompletions Δ P) : HasTy Δ Γ t A := by
  obtain ⟨_, σ, fillers, rfl⟩ := member
  exact typed.fill fun u => (fillers u).2

/-! ## Examples and controls -/

namespace Refinement

/-- A two-hole alphabet. -/
inductive Hole where
  | u
  | v
  deriving DecidableEq

open Tm in
/-- **Filling is strict refinement in general**: filling `u` with `0` loses
the completion `1`. -/
theorem fill_strict :
    completions ((hole Hole.u : Tm Hole).fill fun _ => num 0) ⊆ completions (hole Hole.u) ∧
      ¬ completions (hole Hole.u) ⊆ completions ((hole Hole.u : Tm Hole).fill fun _ => num 0) := by
  refine ⟨completions_fill_subset _ _, fun included => ?_⟩
  have one : (num 1 : Tm Hole) ∈ completions (hole Hole.u) :=
    ⟨trivial, fun _ => num 1, rfl⟩
  obtain ⟨_, σ, equal⟩ := included one
  have zero : ((hole Hole.u : Tm Hole).fill fun _ => num 0).fill σ = num 0 := rfl
  rw [zero] at equal
  exact absurd (Tm.num.inj equal) (by decide)

open Tm in
/-- `if true then 3 else ⦇u⦈` has a determinate result. -/
theorem guarded_determinate :
    Eval [] (ite (bool true) (num 3) (hole Hole.u) : Tm Hole) (.num 3) :=
  .iteTrue (.bool _ _) (.num _ _)

/-- **Positive control**: every terminating completion of the guarded
program yields `3`. -/
theorem guarded_completions {t : Tm Hole} (ht : t ∈ completions (Tm.ite (.bool true) (.num 3)
    (.hole Hole.u))) {r' : Res Hole} (h' : Eval [] t r') : r' = .num 3 :=
  determinate_of_eval guarded_determinate ht h'

open Tm in
/-- `⦇u⦈ + 1` evaluates to an indeterminate sum. -/
theorem sum_indeterminate :
    Eval [] (add (hole Hole.u) (num 1) : Tm Hole) (.add (.hole Hole.u []) (.num 1)) :=
  .add (.hole _ _) (.num _ _) (.indetLeft (.hole _ _) (Or.inr ⟨1, rfl⟩))

open Tm in
/-- **Negative control**: an indeterminate result does not fix the outputs;
two completions of `⦇u⦈ + 1` evaluate differently. -/
theorem indeterminate_outputs_differ :
    (add (num 0) (num 1) : Tm Hole) ∈ completions (add (hole Hole.u) (num 1)) ∧
      (add (num 1) (num 1) : Tm Hole) ∈ completions (add (hole Hole.u) (num 1)) ∧
      Eval [] (add (num 0) (num 1) : Tm Hole) (.num 1) ∧
      Eval [] (add (num 1) (num 1) : Tm Hole) (.num 2) :=
  ⟨⟨⟨trivial, trivial⟩, fun _ => num 0, rfl⟩, ⟨⟨trivial, trivial⟩, fun _ => num 1, rfl⟩,
    .add (.num _ _) (.num _ _) (.num 0 1), .add (.num _ _) (.num _ _) (.num 1 1)⟩

end Refinement

namespace HoleInstances

open Refinement (Hole)
open Tm

/-- `(λf. f 1 + f 2) (λx. ⦇u⦈ + x)`: the hole sits in a function that is
called twice. -/
def program : Tm Hole :=
  app (lam (add (app (var 0) (num 1)) (app (var 0) (num 2))))
    (lam (add (hole Hole.u) (var 0)))

/-- The body of the function containing the hole. -/
def inner : Tm Hole := add (hole Hole.u) (var 0)

/-- The function containing the hole, as a closure. -/
def innerClosure : Res Hole := .clo [] inner

/-- **Two instances of one hole**: the result holds two closures of `u`, one
recorded with `x = 1` and one with `x = 2`. -/
theorem eval_program :
    Eval [] program
      (.add (.add (.hole Hole.u [.num 1]) (.num 1)) (.add (.hole Hole.u [.num 2]) (.num 2))) := by
  have call : ∀ n : Nat, Eval [innerClosure] (app (var 0) (num n))
      (.add (.hole Hole.u [.num n]) (.num n)) := fun n =>
    .appClo (.var rfl) (.num _ _)
      (.add (.hole _ _) (.var rfl) (.indetLeft (.hole _ _) (Or.inr ⟨n, rfl⟩)))
  exact .appClo (.lam _ _) (.lam _ _)
    (.add (call 1) (call 2) (.indetLeft (.add _ _) (Or.inl (.add _ _))))

/-- Fill `u` with the bound variable `x`. -/
def fillX : Hole → Tm Hole := fun _ => var 0

/-- Resuming the two instances: each evaluates `x` in its own environment. -/
theorem resume_program :
    Resume fillX
      (.add (.add (.hole Hole.u [.num 1]) (.num 1)) (.add (.hole Hole.u [.num 2]) (.num 2)))
      (.num 6) :=
  .add
    (.add (.hole (.cons (.num 1) .nil) (.var rfl)) (.num 1) (.num 1 1))
    (.add (.hole (.cons (.num 2) .nil) (.var rfl)) (.num 2) (.num 2 2))
    (.num 2 4)

/-- The filled program evaluates to the same answer, as fill-and-resume
predicts. -/
theorem eval_filled : Eval [] (program.fill fillX) (.num 6) := by
  have call : ∀ n : Nat, Eval (H := Hole) [.clo [] (add (var 0) (var 0))]
      (app (var 0) (num n)) (.num (n + n)) := fun n =>
    .appClo (.var rfl) (.num _ _) (.add (.var rfl) (.var rfl) (.num n n))
  exact .appClo (.lam _ _) (.lam _ _) (.add (call 1) (call 2) (.num 2 4))

/-- The resumption agrees with the filled evaluation, by the general theorem. -/
theorem resume_agrees : Resume fillX
    (.add (.add (.hole Hole.u [.num 1]) (.num 1)) (.add (.hole Hole.u [.num 2]) (.num 2)))
    (.num 6) :=
  eval_program.resume_of_eval_fill_nil eval_filled

end HoleInstances

/-! ### Control: resumption is not sound without termination -/

namespace Divergence

open Refinement (Hole)
open Tm

/-- `λx. x x`. -/
def selfApply : Tm Hole := lam (app (var 0) (var 0))

/-- `Ω = (λx. x x) (λx. x x)`. -/
def omega : Tm Hole := app selfApply selfApply

/-- The body `x x` in the environment `[λx. x x]` has no result. -/
theorem no_eval_selfApp {env : List (Res Hole)} {t : Tm Hole} {r : Res Hole}
    (h : Eval env t r) :
    ∀ {cenv : List (Res Hole)}, t = app (var 0) (var 0) →
      env = .clo cenv (app (var 0) (var 0)) :: cenv → False := by
  induction h with
  | appClo hf ha hb _ _ ihb =>
    intro cenv ht henv
    cases ht
    subst henv
    cases hf with
    | var hget =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Res.clo.injEq] at hget
      obtain ⟨rfl, rfl⟩ := hget
      cases ha with
      | var hget' =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hget'
        subst hget'
        exact ihb rfl rfl
  | appIndet hf hi _ _ _ =>
    intro cenv ht henv
    cases ht
    subst henv
    cases hf with
    | var hget =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      exact Res.not_indet_clo _ _ hi
  | _ => intro cenv ht; cases ht

/-- **`Ω` has no result.** -/
theorem omega_diverges (env : List (Res Hole)) (r : Res Hole) : ¬ Eval env omega r := by
  intro h
  cases h with
  | appClo hf ha hb =>
    cases hf
    cases ha
    exact no_eval_selfApp hb rfl rfl
  | appIndet hf hi _ =>
    cases hf
    exact Res.not_indet_clo _ _ hi

/-- `(λx. 5) ⦇u⦈`: the argument is never used. -/
def program : Tm Hole := app (lam (num 5)) (hole Hole.u)

/-- Filling `u` with `Ω`. -/
def fillOmega : Hole → Tm Hole := fun _ => omega

/-- **Negative control.**  The unfilled program evaluates to `5` and `5`
resumes to `5`, yet the filled program has no result: call-by-value must
evaluate the discarded argument once it is filled.  Resumption predicts the
result of a completion only when that completion terminates. -/
theorem resume_without_evaluation :
    Eval [] program (.num 5) ∧ Resume fillOmega (.num 5) (.num 5) ∧
      ∀ r, ¬ Eval [] (program.fill fillOmega) r := by
  refine ⟨.appClo (.lam _ _) (.hole _ _) (.num _ _), .num _, fun r h => ?_⟩
  cases h with
  | appClo _ ha _ => exact omega_diverges _ _ ha
  | appIndet hf hi _ =>
    cases hf
    exact Res.not_indet_clo _ _ hi

end Divergence

/-! ### Control: hole closures must record their environment -/

namespace Scoping

open Refinement (Hole)
open Tm

/-- Resumption that ignores the recorded environment and evaluates the filler
in the environment of the whole program. -/
def TopLevelResume (topEnv : List (Res Hole)) (σ : Hole → Tm Hole) (r r' : Res Hole) : Prop :=
  ∃ name env, r = .hole name env ∧ Eval topEnv (σ name) r'

/-- `let x = 1 in ⦇u⦈`, run in a top-level environment where the outer
variable is `7`. -/
def program : Tm Hole := app (lam (hole Hole.u)) (num 1)

/-- Fill `u` with the innermost variable, the `x` of the `let`. -/
def fillX : Hole → Tm Hole := fun _ => var 0

theorem eval_program : Eval [.num 7] program (.hole Hole.u [.num 1, .num 7]) :=
  .appClo (.lam _ _) (.num _ _) (.hole _ _)

theorem eval_filled : Eval [.num 7] (program.fill fillX) (.num 1) :=
  .appClo (.lam _ _) (.num _ _) (.var rfl)

/-- Correct resumption uses the recorded environment. -/
theorem resume_recorded :
    Resume fillX (.hole Hole.u [.num 1, .num 7]) (.num 1) :=
  .hole (.cons (.num 1) (.cons (.num 7) .nil)) (.var rfl)

/-- **Negative control**: resuming in the top-level environment reads the
outer variable and answers `7`, while the filled program answers `1`. -/
theorem topLevel_resumption_differs :
    TopLevelResume [.num 7] fillX (.hole Hole.u [.num 1, .num 7]) (.num 7) ∧
      Eval [.num 7] (program.fill fillX) (.num 1) ∧ (Res.num 7 : Res Hole) ≠ .num 1 :=
  ⟨⟨Hole.u, _, rfl, .var rfl⟩, eval_filled, fun equal => absurd (Res.num.inj equal) (by decide)⟩

end Scoping

/-! ### Control: fill-and-resume needs purity -/

namespace Effects

/-- Terms with one effect: `tick` returns a counter and increments it. -/
inductive ETm where
  | tick
  | num (value : Nat)
  | pair (left right : ETm)
  | hole

/-- Results: numbers, pairs, and the hole closure. -/
inductive ERes where
  | num (value : Nat)
  | pair (left right : ERes)
  | hole
  deriving DecidableEq

/-- Evaluation threads the counter from left to right. -/
def eval : ETm → Nat → ERes × Nat
  | .tick, c => (.num c, c + 1)
  | .num n, c => (.num n, c)
  | .pair a b, c =>
    let left := eval a c
    let right := eval b left.2
    (.pair left.1 right.1, right.2)
  | .hole, c => (.hole, c)

/-- Fill the hole. -/
def fill (e : ETm) : ETm → ETm
  | .pair a b => .pair (fill e a) (fill e b)
  | .hole => e
  | t => t

/-- Resumption evaluates the filler at the hole closure, with the counter
where evaluation stopped. -/
def resume (e : ETm) : ERes → Nat → ERes × Nat
  | .hole, c => eval e c
  | .pair a b, c =>
    let left := resume e a c
    let right := resume e b left.2
    (.pair left.1 right.1, right.2)
  | .num n, c => (.num n, c)

/-- `(⦇⦈, tick)`. -/
def program : ETm := .pair .hole .tick

/-- Filling with `tick`, then evaluating: the filler runs first. -/
theorem fill_then_eval : eval (fill .tick program) 0 = (.pair (.num 0) (.num 1), 2) :=
  rfl

/-- Evaluating, then resuming: the filler runs after the later `tick`. -/
theorem eval_then_resume :
    resume .tick (eval program 0).1 (eval program 0).2 = (.pair (.num 1) (.num 0), 2) :=
  rfl

/-- **Negative control: with effects, fill-and-resume does not commute.** -/
theorem commutation_fails :
    (eval (fill .tick program) 0).1 ≠ (resume .tick (eval program 0).1 (eval program 0).2).1 := by
  rw [fill_then_eval, eval_then_resume]
  decide

/-- **Positive**: an effect-free filler resumes to what the filled program
computes. -/
theorem pure_filler_agrees (n : Nat) :
    resume (.num n) (eval program 0).1 (eval program 0).2 = eval (fill (.num n) program) 0 :=
  rfl

end Effects

/-! ### Control: typing shrinks the completion space -/

namespace TypedControl

open Refinement (Hole)
open Tm

/-- Every hole is a number in the empty context. -/
def numbers : Hole → List Ty × Ty := fun _ => ([], .num)

/-- `⦇u⦈ + 1`. -/
def program : Tm Hole := add (hole Hole.u) (num 1)

theorem program_typed : HasTy numbers [] program .num :=
  .add (.hole rfl) (.num _ _)

/-- `true + 1` is not typable. -/
theorem not_typed_bool_sum (A : Ty) : ¬ HasTy numbers [] (add (bool true) (num 1) : Tm Hole) A := by
  intro typed
  cases typed with
  | add hb _ => cases hb

/-- **Typing shrinks the completion space**: `true + 1` completes `⦇u⦈ + 1`,
but not as a typed completion. -/
theorem typed_strict :
    (add (bool true) (num 1) : Tm Hole) ∈ completions program ∧
      (add (bool true) (num 1) : Tm Hole) ∉ typedCompletions numbers program := by
  refine ⟨⟨⟨trivial, trivial⟩, fun _ => bool true, rfl⟩, fun member => ?_⟩
  exact not_typed_bool_sum .num (hasTy_of_mem_typedCompletions program_typed member)

/-- Positive: `0 + 1` is a typed completion. -/
theorem typed_zero : (add (num 0) (num 1) : Tm Hole) ∈ typedCompletions numbers program :=
  ⟨⟨trivial, trivial⟩, fun _ => num 0, fun _ => ⟨trivial, .num _ _⟩, rfl⟩

end TypedControl

end Mettapedia.OSLF.Programs.HoleEvaluation
