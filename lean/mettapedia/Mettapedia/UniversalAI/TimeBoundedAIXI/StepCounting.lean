import Mathlib.Computability.TuringMachine.Config

/-!
# Chapter 7: Step-counting semantics (extracted)

This module contains the fuel-based evaluator used in the Chapter 7 development:

- `StepCounting.runFor` for deterministic small-step functions
- `StepCounting.ToPartrec.evalWithin` for `Turing.ToPartrec.Code`

It is factored out so other modules (e.g. the core-generic `CoreToPartrec`) can depend on
step-counting without importing the full Chapter 7 development file.
-/

namespace Mettapedia.UniversalAI.TimeBoundedAIXI

universe u

namespace StepCounting

open Relation

/-- Run a deterministic step function for at most `n` steps, stopping early if it halts. -/
def runFor {σ : Type u} (step : σ → Option σ) : ℕ → σ → σ
  | 0, s => s
  | n + 1, s =>
      match step s with
      | none => s
      | some s' => runFor step n s'

@[simp] theorem runFor_zero {σ : Type u} (step : σ → Option σ) (s : σ) :
    runFor step 0 s = s := rfl

theorem runFor_of_step_eq_none {σ : Type u} (step : σ → Option σ) {s : σ} (hs : step s = none) :
    ∀ n, runFor step n s = s := by
  intro n
  induction n with
  | zero =>
      simp [runFor]
  | succ n ih =>
      simp [runFor, hs]

theorem runFor_add {σ : Type u} (step : σ → Option σ) :
    ∀ m n s, runFor step (m + n) s = runFor step n (runFor step m s) := by
  intro m
  induction m with
  | zero =>
      intro n s
      simp [runFor]
  | succ m ih =>
      intro n s
      cases hs : step s with
      | none =>
          have : runFor step n s = s := runFor_of_step_eq_none (step := step) (s := s) hs n
          simp [runFor, hs, Nat.succ_add, this]
      | some s' =>
          simp [runFor, hs, Nat.succ_add, ih]

theorem runFor_one_eq_of_step_eq_some {σ : Type u} (step : σ → Option σ) {s t : σ}
    (hst : step s = some t) : runFor step 1 s = t := by
  simp [runFor, hst]

theorem exists_runFor_eq_of_reaches {σ : Type u} {step : σ → Option σ} {a b : σ}
    (h : StateTransition.Reaches step a b) : ∃ n, runFor step n a = b := by
  induction h with
  | refl =>
      exact ⟨0, by simp [runFor]⟩
  | @tail b c hab hbc ih =>
      rcases ih with ⟨n, hn⟩
      have hEqSome : step b = some c := (Option.mem_def).1 hbc
      refine ⟨n + 1, ?_⟩
      calc
        runFor step (n + 1) a = runFor step 1 (runFor step n a) := by
          simpa using (runFor_add (step := step) (m := n) (n := 1) (s := a))
        _ = runFor step 1 b := by simp [hn]
        _ = c := by simpa using (runFor_one_eq_of_step_eq_some (step := step) (s := b) (t := c) hEqSome)

theorem reaches_runFor {σ : Type u} (step : σ → Option σ) :
    ∀ n a, StateTransition.Reaches step a (runFor step n a) := by
  intro n
  induction n with
  | zero =>
      intro a
      simpa [StateTransition.Reaches, runFor] using
        (ReflTransGen.refl : ReflTransGen (fun x y ↦ y ∈ step x) a a)
  | succ n ih =>
      intro a
      cases hs : step a with
      | none =>
          simpa [StateTransition.Reaches, runFor, hs] using
            (ReflTransGen.refl : ReflTransGen (fun x y ↦ y ∈ step x) a a)
      | some a' =>
          have hab : a' ∈ step a := (Option.mem_def).2 hs
          have hbc : StateTransition.Reaches step a' (runFor step n a') := ih a'
          have hbc' : ReflTransGen (fun x y ↦ y ∈ step x) a' (runFor step n a') := by
            simpa [StateTransition.Reaches] using hbc
          have habc' : ReflTransGen (fun x y ↦ y ∈ step x) a (runFor step n a') :=
            ReflTransGen.head hab hbc'
          have habc : StateTransition.Reaches step a (runFor step n a') := habc'
          have hrw : runFor step (Nat.succ n) a = runFor step n a' := by
            simp [runFor, hs]
          rw [hrw]
          exact habc

namespace ToPartrec

open Turing.ToPartrec

/-- Fuel-bounded evaluator for `ToPartrec.Code`, using `ToPartrec.step`. -/
def evalWithin (n : ℕ) (c : Code) (v : List ℕ) : Option (List ℕ) :=
  match runFor step n (stepNormal c Cont.halt v) with
  | Cfg.halt out => some out
  | _ => none

theorem evalWithin_sound {n : ℕ} {c : Code} {v out : List ℕ} (h : evalWithin n c v = some out) :
    out ∈ c.eval v := by
  classical
  let cfg0 := stepNormal c Cont.halt v
  have hrun : runFor step n cfg0 = Cfg.halt out := by
    cases hcfg : runFor step n cfg0 with
    | halt out' =>
        have : out' = out := by simpa [evalWithin, cfg0, hcfg] using h
        cases this
        rfl
    | ret k v' =>
        have h' := h
        simp [evalWithin, cfg0, hcfg] at h'
  have hreach : StateTransition.Reaches step cfg0 (Cfg.halt out) := by
    have : StateTransition.Reaches step cfg0 (runFor step n cfg0) := reaches_runFor (step := step) n cfg0
    simpa [hrun] using this
  have hmem_eval : Cfg.halt out ∈ StateTransition.eval step cfg0 :=
    (StateTransition.mem_eval).2 ⟨hreach, by simp [step]⟩
  have hmem_map : Cfg.halt out ∈ (Cfg.halt <$> c.eval v) := by
    simpa [cfg0, stepNormal_eval] using hmem_eval
  rcases (Part.mem_map_iff (fun x : List ℕ => Cfg.halt x)).1 hmem_map with ⟨out', hout', houtEq⟩
  cases houtEq
  simpa using hout'

theorem evalWithin_complete {c : Code} {v out : List ℕ} (h : out ∈ c.eval v) :
    ∃ n, evalWithin n c v = some out := by
  classical
  let cfg0 := stepNormal c Cont.halt v
  have hmem_map : Cfg.halt out ∈ (Cfg.halt <$> c.eval v) :=
    Part.mem_map (fun x : List ℕ => Cfg.halt x) h
  have hmem_eval : Cfg.halt out ∈ StateTransition.eval step cfg0 := by
    simpa [cfg0, stepNormal_eval] using hmem_map
  rcases (StateTransition.mem_eval).1 hmem_eval with ⟨hreach, _⟩
  rcases exists_runFor_eq_of_reaches (step := step) (a := cfg0) (b := Cfg.halt out) hreach with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simp [evalWithin, cfg0, hn]

theorem evalWithin_mono {n m : ℕ} {c : Code} {v out : List ℕ} (h : evalWithin n c v = some out)
    (hnm : n ≤ m) : evalWithin m c v = some out := by
  classical
  let cfg0 := stepNormal c Cont.halt v
  have hrun : runFor step n cfg0 = Cfg.halt out := by
    cases hcfg : runFor step n cfg0 with
    | halt out' =>
        have : out' = out := by simpa [evalWithin, cfg0, hcfg] using h
        subst this
        rfl
    | ret k v' =>
        have h' := h
        simp [evalWithin, cfg0, hcfg] at h'
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  have hrun' : runFor step (n + k) cfg0 = Cfg.halt out := by
    calc
      runFor step (n + k) cfg0 = runFor step k (runFor step n cfg0) := by
        simpa using (runFor_add (step := step) (m := n) (n := k) (s := cfg0))
      _ = runFor step k (Cfg.halt out) := by simp [hrun]
      _ = Cfg.halt out := by
        simpa using
          (runFor_of_step_eq_none (step := step) (s := Cfg.halt out) (by simp [step]) k)
  simp [evalWithin, cfg0, hrun']

theorem exists_evalWithin_eq_some_iff {c : Code} {v out : List ℕ} :
    (∃ n, evalWithin n c v = some out) ↔ out ∈ c.eval v := by
  constructor
  · rintro ⟨n, hn⟩
    exact evalWithin_sound hn
  · intro hout
    exact evalWithin_complete hout

end ToPartrec

end StepCounting

end Mettapedia.UniversalAI.TimeBoundedAIXI
