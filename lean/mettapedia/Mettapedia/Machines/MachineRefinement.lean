import Mettapedia.Machines.MachineSubstrate

/-!
# Observable deterministic machines and evaluator adequacy

`MachineCore` deliberately shares only a term loader and a deterministic step
function. This module derives the common run and observation contract needed by
a meta-machine without identifying the control semantics of its inhabitants.

An `AnswerMachineCore` adds a partial observation of completed answers and
requires every observed answer to be final. The generic uniqueness theorem is
then a consequence of the deterministic step function, not a property assumed
separately for each evaluator.

The CEK and Krivine cores both inhabit this contract. Their existing
evaluator-to-machine correspondence theorems imply top-level answer adequacy.
These are forward adequacy results; no converse simulation or equality of the
two evaluation strategies is claimed.

No project-specific axioms or proof placeholders are introduced.
-/

namespace Mettapedia.Machines

namespace MachineCore

variable {Term : Type}

/-- One transition of a deterministic machine core. -/
def StepRel (M : MachineCore Term) (s s' : M.State) : Prop :=
  M.step s = some s'

/-- Zero or more transitions of a deterministic machine core. -/
abbrev Steps (M : MachineCore Term) : M.State → M.State → Prop :=
  Relation.ReflTransGen M.StepRel

/-- A state with no outgoing transition. This includes both completed and
stuck states; `AnswerMachineCore.answer` distinguishes completed answers. -/
def Final (M : MachineCore Term) (s : M.State) : Prop :=
  M.step s = none

/-- Determinism of the step function makes a reachable final state unique. -/
theorem steps_final_unique (M : MachineCore Term) {s f₁ f₂ : M.State}
    (h₁ : M.Steps s f₁) (h₂ : M.Steps s f₂)
    (hf₁ : M.Final f₁) (hf₂ : M.Final f₂) : f₁ = f₂ := by
  revert h₂
  induction h₁ using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro h₂
    rcases Relation.ReflTransGen.cases_head h₂ with h | ⟨c, hc, _⟩
    · exact h
    · rw [Final] at hf₁
      rw [StepRel, hf₁] at hc
      exact absurd hc.symm (Option.some_ne_none c)
  | head hab _ ih =>
    intro h₂
    rcases Relation.ReflTransGen.cases_head h₂ with h | ⟨c, hc, h₂'⟩
    · subst h
      rw [Final] at hf₂
      rw [StepRel, hf₂] at hab
      exact absurd hab.symm (Option.some_ne_none _)
    · rw [StepRel] at hab hc
      rw [hab] at hc
      cases hc
      exact ih h₂'

end MachineCore

/-- A deterministic machine core with a sound partial observation of completed
answers. Stuck states remain unobserved. -/
structure AnswerMachineCore (Term Answer : Type) extends MachineCore Term where
  answer : State → Option Answer
  answer_final : ∀ s a, answer s = some a → step s = none

namespace AnswerMachineCore

variable {Term Answer : Type}

/-- A loaded term produces an answer when it reaches a state that exposes it. -/
def Produces (M : AnswerMachineCore Term Answer) (t : Term) (a : Answer) : Prop :=
  ∃ s : M.State,
    M.toMachineCore.Steps (M.load t) s ∧ M.answer s = some a

/-- A deterministic answer machine cannot produce two different answers from
one loaded term. -/
theorem produces_unique (M : AnswerMachineCore Term Answer) {t : Term}
    {a b : Answer} (ha : M.Produces t a) (hb : M.Produces t b) : a = b := by
  obtain ⟨sa, hra, haa⟩ := ha
  obtain ⟨sb, hrb, hab⟩ := hb
  have hs : sa = sb := M.toMachineCore.steps_final_unique hra hrb
    (M.answer_final sa a haa) (M.answer_final sb b hab)
  subst sb
  rw [haa] at hab
  exact Option.some.inj hab

end AnswerMachineCore

/-! ## The eager CEK inhabitant -/

/-- Observe only a returned CEK value with an empty continuation. -/
def cekAnswer : CEK.St → Option CEK.Val
  | ⟨.ret v, []⟩ => some v
  | _ => none

theorem cekAnswer_final (s : CEK.St) (v : CEK.Val)
    (h : cekAnswer s = some v) : CEK.step s = none := by
  rcases s with ⟨ctl, k⟩
  cases ctl with
  | ev t ρ => simp [cekAnswer] at h
  | ret w =>
    cases k with
    | nil => rfl
    | cons f k => simp [cekAnswer] at h

/-- The eager CEK core with its completed-answer observer. -/
def cekAnswerCore : AnswerMachineCore Tm CEK.Val where
  State := CEK.St
  load := fun t => ⟨.ev t [], []⟩
  step := CEK.step
  answer := cekAnswer
  answer_final := cekAnswer_final

/-- Forward adequacy of the CBV evaluator for the observable CEK core. -/
theorem cek_eval_to_produces {n : Nat} {t : Tm} {v : CEK.Val}
    (h : CEK.evalV n [] t = some v) : cekAnswerCore.Produces t v := by
  refine ⟨⟨.ret v, []⟩, ?_, rfl⟩
  exact CEK.eval_to_machine n [] t v h []

/-! ## The demand-driven Krivine inhabitant -/

/-- Observe a weak-head value only at an empty argument stack. -/
def krivineAnswer : Krivine.KSt → Option Krivine.NVal
  | ⟨.lit k, _, []⟩ => some (.lit k)
  | ⟨.lam b, ρ, []⟩ => some (.clo b ρ)
  | _ => none

theorem krivineAnswer_final (s : Krivine.KSt) (w : Krivine.NVal)
    (h : krivineAnswer s = some w) : Krivine.kstep s = none := by
  rcases s with ⟨t, ρ, k⟩
  cases t <;> cases k <;> simp [krivineAnswer, Krivine.kstep] at h ⊢

/-- The call-by-name Krivine core with its weak-head answer observer. -/
def krivineAnswerCore : AnswerMachineCore Tm Krivine.NVal where
  State := Krivine.KSt
  load := fun t => ⟨t, [], []⟩
  step := Krivine.kstep
  answer := krivineAnswer
  answer_final := krivineAnswer_final

/-- A top-level Krivine presentation is exactly an observable answer. -/
theorem krivine_presents_nil_answer {w : Krivine.NVal} {s : Krivine.KSt}
    (h : Krivine.Presents w [] s) : krivineAnswer s = some w := by
  cases w with
  | lit k =>
    obtain ⟨ρ, rfl⟩ := h
    rfl
  | clo b ρ =>
    subst s
    rfl

/-- Forward adequacy of the CBN evaluator for the observable Krivine core. -/
theorem krivine_eval_to_produces {n : Nat} {t : Tm} {w : Krivine.NVal}
    (h : Krivine.evalN n [] t = some w) : krivineAnswerCore.Produces t w := by
  obtain ⟨s, hrun, hpresent⟩ :=
    Krivine.eval_to_machine n [] t w h []
  exact ⟨s, hrun, krivine_presents_nil_answer hpresent⟩

end Mettapedia.Machines
