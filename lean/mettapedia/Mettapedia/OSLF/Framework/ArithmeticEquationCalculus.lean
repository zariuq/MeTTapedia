import Mettapedia.OSLF.Framework.PureInternalization

/-!
# Arithmetic equations with induction as an authority node

Arithmetic as explicit rules, generic derivability, an
independent standard-model meaning, and consistency by model qualification.

* `ATerm`, `aeval`, `asubst`, `aeval_asubst`: terms over `0, S, +, ×` with a
  substitution/evaluation exchange law.
* `ArithmeticRule`: equational logic (refl/symm/trans/congruences), the defining
  equations of `+` and `×` as schemata, internal `⟹`, and the induction rule
  with an explicit eigenvariable freshness side condition.
* `arithmeticRules_sound`: every rule is sound for the standard model ℕ; hence
  (`Derives.least`) every derivable sequent is valid.
* `arithmeticNode`: the authority-category object
  `derivesTheory ArithmeticRule SeqValid …`.
* `arithmeticNode_consistent`: `0 = S 0` is not derivable — consistency of the
  hosted arithmetic by model qualification, the N4 pattern instantiated.
* `add_zero_one_derivable`: a positive control actually replaying the
  defining equations through the rule system.

This is an arithmetic equation calculus with implication and induction
restricted to equations.  No claim that it is PRA or full first-order PA is
made here; either identification requires a separate interpretation theorem.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.ArithmeticEquationCalculus

open Mettapedia.OSLF.Framework.InitialModalSchema
open Mettapedia.Logic
open Mettapedia.OSLF.Framework.PureInternalization

/-! ## Terms, evaluation, substitution -/

inductive ATerm : Type where
  | var : Nat → ATerm
  | zero : ATerm
  | succ : ATerm → ATerm
  | add : ATerm → ATerm → ATerm
  | mul : ATerm → ATerm → ATerm
deriving DecidableEq, Repr

def aeval (v : Nat → Nat) : ATerm → Nat
  | .var n => v n
  | .zero => 0
  | .succ t => aeval v t + 1
  | .add t s => aeval v t + aeval v s
  | .mul t s => aeval v t * aeval v s

def asubst (σ : Nat → ATerm) : ATerm → ATerm
  | .var n => σ n
  | .zero => .zero
  | .succ t => .succ (asubst σ t)
  | .add t s => .add (asubst σ t) (asubst σ s)
  | .mul t s => .mul (asubst σ t) (asubst σ s)

theorem aeval_asubst (v : Nat → Nat) (σ : Nat → ATerm) :
    ∀ t, aeval v (asubst σ t) = aeval (fun n => aeval v (σ n)) t
  | .var _ => rfl
  | .zero => rfl
  | .succ t => by simp [aeval, asubst, aeval_asubst v σ t]
  | .add t s => by simp [aeval, asubst, aeval_asubst v σ t, aeval_asubst v σ s]
  | .mul t s => by simp [aeval, asubst, aeval_asubst v σ t, aeval_asubst v σ s]

def afv : ATerm → List Nat
  | .var n => [n]
  | .zero => []
  | .succ t => afv t
  | .add t s => afv t ++ afv s
  | .mul t s => afv t ++ afv s

theorem aeval_congr {v w : Nat → Nat} :
    ∀ {t}, (∀ n ∈ afv t, v n = w n) → aeval v t = aeval w t
  | .var n, h => h n (by simp [afv])
  | .zero, _ => rfl
  | .succ t, h => by simp [aeval, aeval_congr (t := t) h]
  | .add t s, h => by
      simp only [aeval]
      rw [aeval_congr (t := t) (fun n hn => h n (by simp [afv, hn])),
        aeval_congr (t := s) (fun n hn => h n (by simp [afv, hn]))]
  | .mul t s, h => by
      simp only [aeval]
      rw [aeval_congr (t := t) (fun n hn => h n (by simp [afv, hn])),
        aeval_congr (t := s) (fun n hn => h n (by simp [afv, hn]))]

/-! ## Formulas: equations with internal implication -/

abbrev Eqn : Type := ATerm × ATerm

abbrev Form : Type := PureForm Eqn

def eqn (t s : ATerm) : Form := .atom (t, s)

def formSubst (σ : Nat → ATerm) : Form → Form
  | .atom e => .atom (asubst σ e.1, asubst σ e.2)
  | .imp p q => .imp (formSubst σ p) (formSubst σ q)

def ffv : Form → List Nat
  | .atom e => afv e.1 ++ afv e.2
  | .imp p q => ffv p ++ ffv q

def feval (v : Nat → Nat) : Form → Prop
  | .atom e => aeval v e.1 = aeval v e.2
  | .imp p q => feval v p → feval v q

theorem feval_formSubst (v : Nat → Nat) (σ : Nat → ATerm) :
    ∀ φ, feval v (formSubst σ φ) ↔ feval (fun n => aeval v (σ n)) φ
  | .atom e => by simp [formSubst, feval, aeval_asubst]
  | .imp p q => by
      simp [formSubst, feval, feval_formSubst v σ p, feval_formSubst v σ q]

theorem feval_congr {v w : Nat → Nat} :
    ∀ {φ}, (∀ n ∈ ffv φ, v n = w n) → (feval v φ ↔ feval w φ)
  | .atom e, h => by
      simp only [feval]
      rw [aeval_congr (t := e.1) (fun n hn => h n (by simp [ffv, hn])),
        aeval_congr (t := e.2) (fun n hn => h n (by simp [ffv, hn]))]
  | .imp p q, h => by
      simp only [feval]
      rw [feval_congr (φ := p) (fun n hn => h n (by simp [ffv, hn])) |>.imp
        (feval_congr (φ := q) (fun n hn => h n (by simp [ffv, hn])))]

/-! ## The rule system -/

def x0 : ATerm := .var 0
def x1 : ATerm := .var 1
def x2 : ATerm := .var 2

/-- Equational logic plus the defining equations of `+` and `×`, as schemata
over metavariables `x0 x1 x2`. -/
def schemas : List (List Form × Form) :=
  [ ([], eqn x0 x0)
  , ([eqn x0 x1], eqn x1 x0)
  , ([eqn x0 x1, eqn x1 x2], eqn x0 x2)
  , ([eqn x0 x1], eqn (.succ x0) (.succ x1))
  , ([eqn x0 x1], eqn (.add x0 x2) (.add x1 x2))
  , ([eqn x0 x1], eqn (.add x2 x0) (.add x2 x1))
  , ([eqn x0 x1], eqn (.mul x0 x2) (.mul x1 x2))
  , ([eqn x0 x1], eqn (.mul x2 x0) (.mul x2 x1))
  , ([], eqn (.add x0 .zero) x0)
  , ([], eqn (.add x0 (.succ x1)) (.succ (.add x0 x1)))
  , ([], eqn (.mul x0 .zero) .zero)
  , ([], eqn (.mul x0 (.succ x1)) (.add (.mul x0 x1) x0)) ]

abbrev Seq : Type := Hyp Eqn

def ctxFv (Γ : List Form) : List Nat := Γ.flatMap ffv

/-- Single-point substitution. -/
def point (x : Nat) (u : ATerm) : Nat → ATerm :=
  fun n => if n = x then u else .var n

/-- The rules: assumption, schema instances, internal `⟹`, and
induction with an eigenvariable freshness side condition. -/
inductive ArithmeticRule : List Seq → Seq → Prop where
  | assumption {concl : Seq} (mem : concl.2 ∈ concl.1) : ArithmeticRule [] concl
  | schema {Γ : List Form} (s : List Form × Form) (hs : s ∈ schemas)
      (σ : Nat → ATerm) :
      ArithmeticRule (s.1.map (fun A => (Γ, formSubst σ A))) (Γ, formSubst σ s.2)
  | impIntro {Γ : List Form} (A B : Form) :
      ArithmeticRule [(A :: Γ, B)] (Γ, .imp A B)
  | impElim {Γ : List Form} (A : Form) {B : Form} :
      ArithmeticRule [(Γ, .imp A B), (Γ, A)] (Γ, B)
  | induction {Γ : List Form} (t s : ATerm) (x : Nat) (fresh : x ∉ ctxFv Γ) :
      ArithmeticRule
        [ (Γ, .atom (asubst (point x .zero) t, asubst (point x .zero) s))
        , (Γ, .imp (.atom (t, s))
            (.atom (asubst (point x (.succ (.var x))) t,
                    asubst (point x (.succ (.var x))) s))) ]
        (Γ, .atom (t, s))

/-- Validity in the standard model: for every valuation, the hypotheses
force the conclusion. -/
def SeqValid (j : Seq) : Prop :=
  ∀ v : Nat → Nat, (∀ B ∈ j.1, feval v B) → feval v j.2

def upd (v : Nat → Nat) (x k : Nat) : Nat → Nat :=
  fun n => if n = x then k else v n

theorem aeval_point (v : Nat → Nat) (x : Nat) (u : ATerm) :
    (fun n => aeval v (point x u n)) = upd v x (aeval v u) := by
  funext n
  by_cases h : n = x <;> simp [point, upd, h, aeval]

/-! ## Soundness for the standard model -/

/-- Each schema is valid under every valuation of its metavariables. -/
theorem schemaValid : ∀ s ∈ schemas, ∀ w : Nat → Nat,
    (∀ A ∈ s.1, feval w A) → feval w s.2 := by
  intro s hs w hp
  simp only [schemas, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [eqn, feval]
  · have h := hp (eqn x0 x1) (by simp)
    simp only [eqn, feval, aeval, x0, x1] at h ⊢
    exact h.symm
  · have h1 := hp (eqn x0 x1) (by simp)
    have h2 := hp (eqn x1 x2) (by simp)
    simp only [eqn, feval, aeval, x0, x1, x2] at h1 h2 ⊢
    exact h1.trans h2
  · have h := hp (eqn x0 x1) (by simp)
    simp only [eqn, feval, aeval, x0, x1] at h ⊢
    rw [h]
  · have h := hp (eqn x0 x1) (by simp)
    simp only [eqn, feval, aeval, x0, x1, x2] at h ⊢
    rw [h]
  · have h := hp (eqn x0 x1) (by simp)
    simp only [eqn, feval, aeval, x0, x1, x2] at h ⊢
    rw [h]
  · have h := hp (eqn x0 x1) (by simp)
    simp only [eqn, feval, aeval, x0, x1, x2] at h ⊢
    rw [h]
  · have h := hp (eqn x0 x1) (by simp)
    simp only [eqn, feval, aeval, x0, x1, x2] at h ⊢
    rw [h]
  · simp [eqn, feval, aeval, x0]
  · simp only [eqn, feval, aeval, x0, x1]
    omega
  · simp [eqn, feval, aeval, x0]
  · simp only [eqn, feval, aeval, x0, x1]
    exact Nat.mul_succ _ _

theorem arithmeticRules_sound :
    ∀ hyps concl, ArithmeticRule hyps concl →
      (∀ h ∈ hyps, SeqValid h) → SeqValid concl := by
  intro hyps concl rule ih
  cases rule with
  | assumption mem =>
    intro v hΓ
    exact hΓ _ mem
  | schema s hs σ =>
    intro v hΓ
    have prem : ∀ A ∈ s.1, feval (fun n => aeval v (σ n)) A := by
      intro A hA
      have := ih (_, formSubst σ A) (List.mem_map_of_mem hA) v hΓ
      exact (feval_formSubst v σ A).mp this
    rw [feval_formSubst]
    exact schemaValid s hs _ prem
  | @impIntro Γ A B =>
    intro v hΓ hA
    refine ih (A :: Γ, B) (by simp) v ?_
    intro B' hB'
    rcases List.mem_cons.mp hB' with rfl | h
    · exact hA
    · exact hΓ _ h
  | @impElim Γ A B =>
    intro v hΓ
    exact (ih (Γ, .imp A B) (by simp) v hΓ) (ih (Γ, A) (by simp) v hΓ)
  | @induction Γ t s x fresh =>
    intro v hΓ
    have base : SeqValid
        (Γ, PureForm.atom (asubst (point x .zero) t, asubst (point x .zero) s)) :=
      ih _ (by simp)
    have step : SeqValid
        (Γ, PureForm.imp (.atom (t, s))
          (.atom (asubst (point x (.succ (.var x))) t,
                  asubst (point x (.succ (.var x))) s))) :=
      ih _ (by simp)
    have ctxStable : ∀ (k : Nat), ∀ B ∈ Γ, feval (upd v x k) B := by
      intro k B hB
      have hx : x ∉ ffv B := fun hmem =>
        fresh (List.mem_flatMap.mpr ⟨B, hB, hmem⟩)
      refine (feval_congr ?_).mpr (hΓ B hB)
      intro n hn
      simp only [upd]
      rw [if_neg]
      intro he
      exact hx (he ▸ hn)
    have P : ∀ k, aeval (upd v x k) t = aeval (upd v x k) s := by
      intro k
      induction k with
      | zero =>
        have h0 := base v hΓ
        simp only [feval] at h0
        rw [aeval_asubst, aeval_asubst, aeval_point] at h0
        simpa [aeval] using h0
      | succ k ihk =>
        have hstep := step (upd v x k) (ctxStable k)
        simp only [feval] at hstep
        have hnext := hstep ihk
        rw [aeval_asubst, aeval_asubst, aeval_point] at hnext
        have upd2 : upd (upd v x k) x (aeval (upd v x k) (.succ (.var x))) =
            upd v x (k + 1) := by
          funext n
          by_cases h : n = x <;> simp [upd, h, aeval]
        rw [upd2] at hnext
        exact hnext
    have final := P (v x)
    have upd_self : upd v x (v x) = v := by
      funext n
      by_cases h : n = x <;> simp [upd, h]
    rw [upd_self] at final
    simpa [feval] using final

/-! ## Theory object, certificate contract, and consistency -/

/-- Certificate witnesses: exactly the rule constructors' data. -/
inductive ArithmeticStep : Type where
  | assumption : ArithmeticStep
  | schema : (List Form × Form) → (Nat → ATerm) → ArithmeticStep
  | impIntro : Form → Form → ArithmeticStep
  | impElim : Form → Form → ArithmeticStep
  | induction : ATerm → ATerm → Nat → ArithmeticStep

def arithmeticWitness : RuleWitness.{0, 0} ArithmeticRule where
  W := ArithmeticStep
  isInstance w hyps concl :=
    match w with
    | .assumption => decide (hyps = [] ∧ concl.2 ∈ concl.1)
    | .schema s σ =>
        decide (s ∈ schemas ∧
          hyps = s.1.map (fun A => (concl.1, formSubst σ A)) ∧
          concl.2 = formSubst σ s.2)
    | .impIntro A B =>
        decide (hyps = [(A :: concl.1, B)] ∧ concl.2 = .imp A B)
    | .impElim A B =>
        decide (hyps = [(concl.1, .imp A B), (concl.1, A)] ∧ concl.2 = B)
    | .induction t s x =>
        decide (x ∉ ctxFv concl.1 ∧
          hyps = [ (concl.1, .atom (asubst (point x .zero) t,
                     asubst (point x .zero) s))
                 , (concl.1, .imp (.atom (t, s))
                     (.atom (asubst (point x (.succ (.var x))) t,
                             asubst (point x (.succ (.var x))) s))) ] ∧
          concl.2 = .atom (t, s))
  sound := by
    intro w hyps concl h
    obtain ⟨Γ, C⟩ := concl
    cases w with
    | assumption =>
      simp only [decide_eq_true_eq] at h
      obtain ⟨rfl, mem⟩ := h
      exact ArithmeticRule.assumption mem
    | schema s σ =>
      simp only [decide_eq_true_eq] at h
      obtain ⟨hs, rfl, rfl⟩ := h
      exact ArithmeticRule.schema s hs σ
    | impIntro A B =>
      simp only [decide_eq_true_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ArithmeticRule.impIntro A B
    | impElim A B =>
      simp only [decide_eq_true_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ArithmeticRule.impElim A
    | induction t s x =>
      simp only [decide_eq_true_eq] at h
      obtain ⟨fresh, rfl, rfl⟩ := h
      exact ArithmeticRule.induction t s x fresh
  complete := by
    intro hyps concl rule
    cases rule with
    | assumption mem =>
      exact ⟨.assumption, decide_eq_true ⟨rfl, mem⟩⟩
    | schema s hs σ =>
      exact ⟨.schema s σ, decide_eq_true ⟨hs, rfl, rfl⟩⟩
    | impIntro A B =>
      exact ⟨.impIntro A B, decide_eq_true ⟨rfl, rfl⟩⟩
    | impElim A =>
      exact ⟨.impElim A _, decide_eq_true ⟨rfl, rfl⟩⟩
    | induction t s x fresh =>
      exact ⟨.induction t s x, decide_eq_true ⟨fresh, rfl, rfl⟩⟩

/-- The arithmetic authority node: theory with standard-model meaning. -/
noncomputable def arithmeticNode :=
  Mettapedia.OSLF.Framework.PureInternalization.derivesTheory
    ArithmeticRule SeqValid arithmeticRules_sound

/-- Its exact replay contract. -/
noncomputable def arithmeticContract :=
  Mettapedia.OSLF.Framework.PureInternalization.derivesContract
    (Meaning := SeqValid) (sound := arithmeticRules_sound) arithmeticWitness

/-- **Consistency of hosted arithmetic, by model qualification.** -/
theorem arithmetic_consistent :
    ¬ Derives ArithmeticRule ([], eqn .zero (.succ .zero)) := by
  intro d
  have h := Derives.least SeqValid arithmeticRules_sound d (fun _ => 0)
    (by intro B hB; cases hB)
  simp [feval, aeval, eqn] at h

theorem arithmeticNode_consistent :
    ¬ arithmeticNode.Scope () ([], eqn .zero (.succ .zero)) :=
  arithmetic_consistent

/-! ## Positive control: `0 + 1 = 1` replays through the rules -/

def σ00 : Nat → ATerm := fun _ => .zero

def σsucc : Nat → ATerm := fun n =>
  match n with
  | 0 => .add .zero .zero
  | _ => .zero

def σtr : Nat → ATerm := fun n =>
  match n with
  | 0 => .add .zero (.succ .zero)
  | 1 => .succ (.add .zero .zero)
  | _ => .succ .zero

theorem add_zero_one_derivable :
    Derives ArithmeticRule ([], eqn (.add .zero (.succ .zero)) (.succ .zero)) := by
  have d2 : Derives ArithmeticRule ([], eqn (.add .zero .zero) .zero) :=
    Derives.node [] _
      (ArithmeticRule.schema (([], eqn (.add x0 .zero) x0)) (by decide) σ00)
      (by intro h hm; cases hm)
  have d3 : Derives ArithmeticRule
      ([], eqn (.succ (.add .zero .zero)) (.succ .zero)) :=
    Derives.node [([], eqn (.add .zero .zero) .zero)] _
      (ArithmeticRule.schema (([eqn x0 x1], eqn (.succ x0) (.succ x1)))
        (by decide) σsucc)
      (by
        intro h hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        subst hm
        exact d2)
  have d1 : Derives ArithmeticRule
      ([], eqn (.add .zero (.succ .zero)) (.succ (.add .zero .zero))) :=
    Derives.node [] _
      (ArithmeticRule.schema
        (([], eqn (.add x0 (.succ x1)) (.succ (.add x0 x1))))
        (by decide) σ00)
      (by intro h hm; cases hm)
  exact Derives.node
    [ ([], eqn (.add .zero (.succ .zero)) (.succ (.add .zero .zero)))
    , ([], eqn (.succ (.add .zero .zero)) (.succ .zero)) ] _
    (ArithmeticRule.schema
      (([eqn x0 x1, eqn x1 x2], eqn x0 x2)) (by decide) σtr)
    (by
      intro h hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact d1
      · exact d3)

#print axioms arithmeticRules_sound
#print axioms arithmeticWitness
#print axioms arithmetic_consistent
#print axioms arithmeticNode_consistent
#print axioms add_zero_one_derivable

end Mettapedia.OSLF.Framework.ArithmeticEquationCalculus
