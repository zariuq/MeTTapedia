import Mettapedia.Cybernetics.ApproximateAdequacy.AdaptiveSemantics
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Trace semantics of finite adaptive policies

Each trace retains every next state and observation. Its probability law is
constructed from independent kernel application and tuple-prefix pushforward.
Expected terminal reward agrees with the value recurrence.
-/

namespace Mettapedia.Cybernetics.ApproximateAdequacy

open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.Prob

variable {S O A : Type*} [Fintype S] [Fintype O] [DecidableEq S] [DecidableEq O]

def traceTerminal (initial : S) : {n : ℕ} → (Fin n → S × O) → S
  | 0, _ => initial
  | n + 1, trace => traceTerminal (trace 0).1 (n := n) (Fin.tail trace)

noncomputable def traceLaw (kernel : A → S → Prob (S × O)) :
    {n : ℕ} → ObservationPolicy O A n → S → Prob (Fin n → S × O)
  | 0, _, _ => Prob.dirac (fun i => Fin.elim0 i)
  | n + 1, policy, s =>
      Prob.bind (kernel policy.1 s) (fun next =>
        coarsen (traceLaw kernel (n := n) (policy.2 next.2) next.1)
          (fun trace : Fin n → S × O => Fin.cons next trace))

/-- The recurrence is derived from the entire finite execution law. -/
theorem traceLaw_value (kernel : A → S → Prob (S × O)) (reward : S → ℝ)
    {n : ℕ} (policy : ObservationPolicy O A n) (s : S) :
    (∑ trace, (traceLaw kernel policy s).1 trace * reward (traceTerminal s trace)) =
      adaptiveValue kernel reward policy s := by
  induction n generalizing s with
  | zero =>
      change (∑ trace, (Prob.dirac (fun i : Fin 0 => (Fin.elim0 i : S × O))).1 trace *
        reward s) = reward s
      exact expectation_dirac _ (fun _ => reward s)
  | succ n ih =>
      rw [traceLaw, expectation_bind]
      change (∑ next, (kernel policy.1 s).1 next *
        (∑ trace, (coarsen (traceLaw kernel (policy.2 next.2) next.1)
          (fun trace : Fin n → S × O => Fin.cons next trace)).1 trace *
            reward (traceTerminal s trace))) = _
      simp only [coarsen_expectation, traceTerminal, Fin.cons_zero, Fin.tail_cons, ih,
        adaptiveValue, expect]

end Mettapedia.Cybernetics.ApproximateAdequacy
