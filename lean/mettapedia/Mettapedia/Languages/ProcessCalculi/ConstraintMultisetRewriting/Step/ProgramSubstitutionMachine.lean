import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramSubstitution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramAdequacy

/-!
# The core's environment machine computes the closure semantics

The λ fragment of the source core (`Program.Step`: variable lookup, abstraction, application,
operand evaluation, β) runs intrinsically scoped λ terms encoded as rows (`enc`): a variable by its
position, an environment as the list of its encoded closures (`encEnv`), a closure as the encoded
body and environment (`encV`).

* `lookup`: a variable is found by one step per position.
* **Completeness** (`machine_complete`): every closure evaluation is a run of the machine, with any
  continuation and any further rows: the machine reaches the encoded value under the same
  continuation.
* **Soundness** (`machine_sound`, `machine_iff`): a run from evaluating a term to a final row passes
  through the closure value of the term, so the machine halts at a closure value exactly when the
  closure semantics evaluates the program to it. A deterministic step is peeled off a run
  (`run_peel`), and a final row has no step (`final_halted`).
* **The correspondence on the core** (`machine_of_eval`, `eval_of_machine`): every substitution
  evaluation of a closed program is reached by the machine, with a closure that reads back as the
  value, and is a contextual execution on the step (`ProgramSubstitution.eval_executes`); every
  halting run of the machine ends in a closure whose read-back is the substitution value.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramSubstitution

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.LambdaContextualRung (sig Srt Op appT lamT)
open ProgramRows

/-! ## Encoding -/

/-- A position as a unary index. -/
def vnum : {Γ : Ctx sig} → {s : sig.Srt} → Var Γ s → Sx
  | _, _, .zero => Program.zero
  | _, _, .succ v => Program.succ (vnum v)

def opEnc : {s : sig.Srt} → Op s → List Sx → Sx
  | _, .app, [f, a] => Program.app f a
  | _, .lam, [b] => Program.lam b
  | _, _, _ => Program.nil

mutual
/-- **A λ term as a row expression.** -/
def enc : {Γ : Ctx sig} → {s : sig.Srt} → Term sig Γ s → Sx
  | _, _, .var v => Program.var (vnum v)
  | _, _, .op o args => opEnc o (encArgs args)

def encArgs : {as : List (List sig.Srt × sig.Srt)} → {Γ : Ctx sig} → Args sig as Γ → List Sx
  | _, _, .nil => []
  | _, _, .cons head tail => enc head :: encArgs tail
end

/-- An environment from the encodings of its values. -/
def encEnvWith : (Γ : Ctx sig) → ((s : sig.Srt) → Var Γ s → Sx) → Sx
  | [], _ => Program.nil
  | s :: Γ, f => Program.cons (f s .zero) (encEnvWith Γ fun t v => f t v.succ)

/-- **A closure as a row value.** -/
def encV : Val → Sx
  | .clo Γ b ρ => Program.clo (enc b) (encEnvWith Γ fun s v => encV (ρ s v))

/-- An environment as a row. -/
def encEnv {Γ : Ctx sig} (ρ : Env Γ) : Sx := encEnvWith Γ fun s v => encV (ρ s v)

theorem enc_app {Γ : Ctx sig} (f a : Term sig Γ .term) :
    enc (appT f a) = Program.app (enc f) (enc a) := rfl

theorem enc_lam {Γ : Ctx sig} (b : Term sig (.term :: Γ) .term) :
    enc (lamT b) = Program.lam (enc b) := rfl

/-! ## Runs of the machine -/

abbrev Rm := Relation.ReflTransGen Program.Step

/-- **Lookup**: one step per position. -/
theorem lookup : ∀ {Γ : Ctx sig} {s : sig.Srt} (x : Var Γ s) (ρ : Env Γ) (κ : Sx) (F : Multiset Sx),
    Rm (Program.ev (Program.var (vnum x)) (encEnv ρ) κ ::ₘ F) (Program.ret (encV (ρ s x)) κ ::ₘ F)
  | _, _, .zero, _, κ, F => .single (Program.Step.varZero _ _ κ F)
  | _, _, .succ y, ρ, κ, F =>
      Relation.ReflTransGen.head (Program.Step.varSucc _ _ _ κ F) (lookup y (fun t v => ρ t v.succ) κ F)

/-- **Completeness of the machine**: every closure evaluation is a run, under any continuation and
beside any further rows. -/
theorem machine_complete {Γ : Ctx sig} {ρ : Env Γ} {e : Term sig Γ .term} {v : Val}
    (h : EvalEnv ρ e v) : ∀ (κ : Sx) (F : Multiset Sx),
      Rm (Program.ev (enc e) (encEnv ρ) κ ::ₘ F) (Program.ret (encV v) κ ::ₘ F) := by
  induction h with
  | var ρ x => exact fun κ F => lookup x ρ κ F
  | lam ρ b => exact fun κ F => .single (Program.Step.lam _ _ κ F)
  | @app Γ Γ' ρ f a b ρ' w v hf ha hb ihf iha ihb =>
      intro κ F
      have s1 : Program.Step (Program.ev (enc (appT f a)) (encEnv ρ) κ ::ₘ F)
          (Program.ev (enc f) (encEnv ρ) (Program.cons (Program.appL (enc a) (encEnv ρ)) κ) ::ₘ F) :=
        Program.Step.app _ _ _ κ F
      have s2 : Program.Step
          (Program.ret (encV (.clo Γ' b ρ')) (Program.cons (Program.appL (enc a) (encEnv ρ)) κ) ::ₘ F)
          (Program.ev (enc a) (encEnv ρ) (Program.cons (Program.appR (encV (.clo Γ' b ρ'))) κ) ::ₘ F) :=
        Program.Step.appL _ _ _ κ F
      have s3 : Program.Step
          (Program.ret (encV w) (Program.cons (Program.appR (encV (.clo Γ' b ρ'))) κ) ::ₘ F)
          (Program.ev (enc b) (encEnv (consEnv w ρ')) κ ::ₘ F) :=
        Program.Step.beta _ _ _ κ F
      exact (Relation.ReflTransGen.head s1 (ihf _ F)).trans
        (Relation.ReflTransGen.head s2 ((iha _ F).trans (Relation.ReflTransGen.head s3 (ihb κ F))))

/-- **Plotkin's correspondence on the core**: a substitution evaluation of a closed program to `u`
is reached by the machine, with a closure that reads back as `u`; and it is a contextual execution
on the step. -/
theorem machine_of_eval {e u : Term sig [] .term} (h : Eval e u) :
    ∃ v : Val, rb v = u ∧
      Rm {Program.ev (enc e) Program.nil Program.nil} {Program.ret (encV v) Program.nil} ∧
      ∃ after, Relation.ReflTransGen LambdaExecution.Transition (LambdaExecution.initial e) after ∧
        LambdaExecution.Represents after u := by
  obtain ⟨v, ev, rfl⟩ := (plotkin_closed e u).mpr h
  exact ⟨v, rfl, machine_complete ev Program.nil 0, eval_executes ev⟩

/-! ## Soundness of the machine -/

/-- Runs of a given length. -/
inductive RunN : ℕ → Multiset Sx → Multiset Sx → Prop
  | zero (W : Multiset Sx) : RunN 0 W W
  | succ {n : ℕ} {W W₁ W₂ : Multiset Sx} : Program.Step W W₁ → RunN n W₁ W₂ → RunN (n + 1) W W₂

theorem rm_iff_runN {W W' : Multiset Sx} : Rm W W' ↔ ∃ n, RunN n W W' := by
  constructor
  · intro run
    induction run using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, .zero _⟩
    | head step _ ih =>
        obtain ⟨n, run⟩ := ih
        exact ⟨n + 1, .succ step run⟩
  · rintro ⟨n, run⟩
    induction run with
    | zero => exact .refl
    | succ step _ ih => exact Relation.ReflTransGen.head step ih

/-- **A rule that is not a choice fixes the successor of a single row it matches.** -/
theorem step_rule {i : Program.RuleName} {p : Pat} (hi : (Program.schema i).take = [p])
    (notChoice : ∀ j, Program.choicePair j i = false) {θ : ℕ → Sx} {W : Multiset Sx}
    (step : Program.Step {p.inst θ} W) :
    W = ProgramTranslation.push ((Program.schema i).make.map (Pat.inst θ)) 0 := by
  obtain ⟨j, q, θ', hj, hrj, hq, rfl⟩ := Program.step_singleton.mp step
  rcases Program.overlap_free hj hi (Program.compatible_of_inst q p hq) with same | choice
  · subst same
    rw [hj, List.cons.injEq] at hi
    obtain ⟨rfl, -⟩ := hi
    have agree := Pat.inst_agree q hq
    congr 1
    refine List.map_congr_left fun m hm => Pat.inst_congr m fun x hx => ?_
    obtain ⟨p', hp', hx'⟩ := (Program.schema_wellFormed j).covered m hm x hx
    rw [hj, hrj, List.append_nil, List.mem_singleton] at hp'
    exact agree x (hp' ▸ hx')
  · rw [notChoice j] at choice
    exact absurd choice Bool.false_ne_true

theorem ret_ne_ev {V e E κ : Sx} : Program.ret V Program.nil ≠ Program.ev e E κ := by
  simp [Program.ret, Program.ev, Program.t2, Program.t3]

theorem ret_nil_ne_cons {V v c κ : Sx} : Program.ret V Program.nil ≠ Program.ret v (Program.cons c κ) := by
  simp [Program.ret, Program.cons, Program.nil, Program.t2, Program.t0]

/-- **Peeling a determined step off a run to a final row.** -/
theorem run_peel {n : ℕ} {X Y V : Sx} (run : RunN n {X} {Program.ret V Program.nil})
    (notFinal : Program.ret V Program.nil ≠ X) (next : ∀ W, Program.Step {X} W → W = {Y}) :
    ∃ n', n = n' + 1 ∧ RunN n' {Y} {Program.ret V Program.nil} := by
  generalize hA : ({X} : Multiset Sx) = A at run
  generalize hB : ({Program.ret V Program.nil} : Multiset Sx) = B at run
  cases run with
  | zero => exact absurd (Multiset.singleton_inj.mp (hB.trans hA.symm)) notFinal
  | @succ n' _ W₁ _ step rest =>
      subst hA hB
      rw [next W₁ step] at rest
      exact ⟨n', rfl, rest⟩

theorem next_varZero (v E κ : Sx) : ∀ W, Program.Step {Program.ev (Program.var Program.zero) (Program.cons v E) κ} W →
    W = {Program.ret v κ} := fun W step =>
  step_rule (i := .varZero) rfl (fun j => by cases j <;> rfl) (θ := Program.args [v, E, κ]) step

theorem next_varSucc (i v E κ : Sx) :
    ∀ W, Program.Step {Program.ev (Program.var (Program.succ i)) (Program.cons v E) κ} W →
      W = {Program.ev (Program.var i) E κ} := fun W step =>
  step_rule (i := .varSucc) rfl (fun j => by cases j <;> rfl) (θ := Program.args [i, v, E, κ]) step

theorem next_lam (b E κ : Sx) : ∀ W, Program.Step {Program.ev (Program.lam b) E κ} W →
    W = {Program.ret (Program.clo b E) κ} := fun W step =>
  step_rule (i := .lam) rfl (fun j => by cases j <;> rfl) (θ := Program.args [b, E, κ]) step

theorem next_app (f a E κ : Sx) : ∀ W, Program.Step {Program.ev (Program.app f a) E κ} W →
    W = {Program.ev f E (Program.cons (Program.appL a E) κ)} := fun W step =>
  step_rule (i := .app) rfl (fun j => by cases j <;> rfl) (θ := Program.args [f, a, E, κ]) step

theorem next_appL (v a E κ : Sx) :
    ∀ W, Program.Step {Program.ret v (Program.cons (Program.appL a E) κ)} W →
      W = {Program.ev a E (Program.cons (Program.appR v) κ)} := fun W step =>
  step_rule (i := .appL) rfl (fun j => by cases j <;> rfl) (θ := Program.args [v, a, E, κ]) step

theorem next_beta (v b E κ : Sx) :
    ∀ W, Program.Step {Program.ret v (Program.cons (Program.appR (Program.clo b E)) κ)} W →
      W = {Program.ev b (Program.cons v E) κ} := fun W step =>
  step_rule (i := .beta) rfl (fun j => by cases j <;> rfl) (θ := Program.args [v, b, E, κ]) step

theorem lookup_sound : ∀ {Γ : Ctx sig} {s : sig.Srt} (x : Var Γ s) (ρ : Env Γ) (κ V : Sx) (n : ℕ),
    RunN n {Program.ev (Program.var (vnum x)) (encEnv ρ) κ} {Program.ret V Program.nil} →
      ∃ m, m < n ∧ RunN m {Program.ret (encV (ρ s x)) κ} {Program.ret V Program.nil}
  | _, _, .zero, ρ, κ, V, n, run => by
      obtain ⟨n', rfl, rest⟩ := run_peel run ret_ne_ev (next_varZero _ _ κ)
      exact ⟨n', Nat.lt_succ_self n', rest⟩
  | _, _, .succ y, ρ, κ, V, n, run => by
      obtain ⟨n', rfl, rest⟩ := run_peel run ret_ne_ev (next_varSucc _ _ _ κ)
      obtain ⟨m, lt, final⟩ := lookup_sound y (fun t v => ρ t v.succ) κ V n' rest
      exact ⟨m, Nat.lt_succ_of_lt lt, final⟩

/-- **Soundness of the machine**: a run from evaluating `e` to a final row passes through the
closure value of `e`. -/
theorem machine_sound : ∀ (n : ℕ) {Γ : Ctx sig} (ρ : Env Γ) (e : Term sig Γ .term) (κ V : Sx),
    RunN n {Program.ev (enc e) (encEnv ρ) κ} {Program.ret V Program.nil} →
      ∃ v m, m < n ∧ EvalEnv ρ e v ∧ RunN m {Program.ret (encV v) κ} {Program.ret V Program.nil} := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro Γ ρ e κ V run
      match e, run with
      | .var x, run =>
          obtain ⟨m, lt, final⟩ := lookup_sound x ρ κ V n run
          exact ⟨ρ .term x, m, lt, .var ρ x, final⟩
      | .op .lam (.cons b .nil), run =>
          obtain ⟨n', rfl, rest⟩ := run_peel run ret_ne_ev (next_lam _ _ κ)
          exact ⟨.clo Γ b ρ, n', Nat.lt_succ_self n', .lam ρ b, rest⟩
      | .op .app (.cons f (.cons a .nil)), run =>
          obtain ⟨n₁, rfl, run₁⟩ := run_peel run ret_ne_ev (next_app _ _ _ κ)
          obtain ⟨vf, m₁, lt₁, evf, run₂⟩ := ih n₁ (Nat.lt_succ_self n₁) ρ f _ V run₁
          cases vf with
          | clo Γ' b ρ' =>
              obtain ⟨m₁', rfl, run₃⟩ := run_peel run₂ ret_nil_ne_cons (next_appL _ _ _ κ)
              obtain ⟨w, m₂, lt₂, evw, run₄⟩ := ih m₁' (by omega) ρ a _ V run₃
              obtain ⟨m₂', rfl, run₅⟩ := run_peel run₄ ret_nil_ne_cons (next_beta _ _ _ κ)
              obtain ⟨v, m₃, lt₃, evb, run₆⟩ := ih m₂' (by omega) (consEnv w ρ') b κ V run₅
              exact ⟨v, m₃, by omega, .app evf evw evb, run₆⟩

/-- The shape of a final row. -/
def finalPat : Pat := Program.p2 30 (.var 0) (Program.p0 20)

theorem final_check : Program.allRules.all (fun i => match (Program.schema i).take with
    | [p] => !(Program.compatible p finalPat)
    | _ => true) = true := by decide

/-- **A final row has no step.** -/
theorem final_halted (V : Sx) : ∀ W, ¬ Program.Step {Program.ret V Program.nil} W := by
  intro W step
  obtain ⟨i, p, θ, hi, -, hp, -⟩ := Program.step_singleton.mp step
  have compat := Program.compatible_of_inst p finalPat (θ' := Program.args [V]) (hp.trans rfl)
  have all := final_check
  simp only [List.all_eq_true] at all
  have check := all i (Program.mem_allRules i)
  rw [hi] at check
  simp [compat] at check

theorem ret_nil_inj {U V : Sx} (h : Program.ret U Program.nil = Program.ret V Program.nil) : U = V := by
  simp [Program.ret, Program.t2] at h
  exact h

theorem run_from_final {m : ℕ} {U V : Sx}
    (run : RunN m {Program.ret U Program.nil} {Program.ret V Program.nil}) : U = V := by
  generalize hA : ({Program.ret U Program.nil} : Multiset Sx) = A at run
  generalize hB : ({Program.ret V Program.nil} : Multiset Sx) = B at run
  cases run with
  | zero => exact ret_nil_inj (Multiset.singleton_inj.mp (hA.trans hB.symm))
  | @succ n' _ W₁ _ step _ =>
      subst hA
      exact absurd step (final_halted U W₁)

/-- **Plotkin's correspondence on the core's machine**: from a closed program, the machine halts
at a closure value exactly when the closure semantics evaluates the program to it; with
`plotkin_closed`, exactly when the substitution semantics evaluates the program to its
read-back. -/
theorem machine_iff {e : Term sig [] .term} (V : Sx) :
    Rm {Program.ev (enc e) Program.nil Program.nil} {Program.ret V Program.nil} ↔
      ∃ v, V = encV v ∧ EvalEnv emptyEnv e v := by
  constructor
  · intro run
    obtain ⟨n, runN⟩ := rm_iff_runN.mp run
    obtain ⟨v, m, -, ev, final⟩ := machine_sound n emptyEnv e Program.nil V runN
    exact ⟨v, (run_from_final final).symm, ev⟩
  · rintro ⟨v, rfl, ev⟩
    exact machine_complete ev Program.nil 0

/-- **A halting machine run is a substitution evaluation**: if the machine halts at a value from a
closed program, the value encodes a closure whose read-back is the program's substitution value. -/
theorem eval_of_machine {e : Term sig [] .term} {V : Sx}
    (run : Rm {Program.ev (enc e) Program.nil Program.nil} {Program.ret V Program.nil}) :
    ∃ v, V = encV v ∧ Eval e (rb v) := by
  obtain ⟨v, same, ev⟩ := (machine_iff V).mp run
  exact ⟨v, same, (plotkin_closed e (rb v)).mp ⟨v, ev, rfl⟩⟩

#print axioms lookup
#print axioms machine_complete
#print axioms machine_of_eval
#print axioms rm_iff_runN
#print axioms step_rule
#print axioms run_peel
#print axioms lookup_sound
#print axioms machine_sound
#print axioms final_halted
#print axioms machine_iff
#print axioms eval_of_machine

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramSubstitution
