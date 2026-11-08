import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CausalHistories

/-!
# The race identity for any number of components

The composition of positive systems is positive (`positive_par`), and a shuffle of two maximal runs
realizes a maximal run of the composition (`endState_realize`, `maximal_realize`). So the race
identity applies again with a composition as one side: **three components that do not interfere
contribute the product of their three factors** (`history_factorizes_three`), the shuffles of the
three runs being enumerated as the shuffles of the first run with each shuffle of the other two. The
likelihood of causal histories is compositional for any finite number of non-interfering
components: normalization is local to each component.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CausalHistories

open Mettapedia.GSLT.GradedSupport (IsNormal)

universe u v w

section Monoidal

variable {A : Type u} {B : Type v} {C : Type w}
  (stepA : A → List (A × ℝ)) (stepB : B → List (B × ℝ)) (stepC : C → List (C × ℝ))

/-- **The composition of positive systems is positive.** -/
theorem positive_par (positiveA : Positive stepA) (positiveB : Positive stepB) :
    Positive (par stepA stepB) := by
  intro x p member
  simp only [par, List.mem_append, List.mem_map] at member
  rcases member with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
  · exact positiveA _ q hq
  · exact positiveB _ q hq

/-- The end of a realized schedule: the ends of its two projections. -/
theorem endState_realize : ∀ (a : A) (b : B) (σ : List ((A × ℝ) ⊕ (B × ℝ))),
    endState (a, b) (realize a b σ) = (endState a (σ.filterMap Sum.getLeft?),
      endState b (σ.filterMap Sum.getRight?))
  | _, _, [] => rfl
  | a, b, .inl p :: rest => by
      rw [List.filterMap_cons_some Sum.getLeft?_inl, List.filterMap_cons_none Sum.getRight?_inl]
      exact endState_realize p.1 b rest
  | a, b, .inr q :: rest => by
      rw [List.filterMap_cons_none Sum.getLeft?_inr, List.filterMap_cons_some Sum.getRight?_inr]
      exact endState_realize a q.1 rest

/-- **A shuffle of two maximal runs realizes a maximal run of the composition.** -/
theorem maximal_realize {a : A} {b : B} {α : List (A × ℝ)} {β : List (B × ℝ)}
    (maximalA : Maximal stepA a α) (maximalB : Maximal stepB b β)
    {σ : List ((A × ℝ) ⊕ (B × ℝ))} (member : σ ∈ shuffles α β) :
    Maximal (par stepA stepB) (a, b) (realize a b σ) := by
  obtain ⟨left, right⟩ := (mem_shuffles_iff α β σ).mp member
  refine ⟨isRun_realize stepA stepB α β a b maximalA.1 maximalB.1 σ member, ?_⟩
  rw [endState_realize, left, right]
  exact (isNormal_par_iff stepA stepB _).mpr ⟨maximalA.2, maximalB.2⟩

/-- **Three components that do not interfere**: summed over the shuffles of the first run with each
shuffle of the other two, the likelihood is the product of the three factors. -/
theorem history_factorizes_three (positiveA : Positive stepA) (positiveB : Positive stepB)
    (positiveC : Positive stepC) {a : A} {b : B} {c : C}
    {α : List (A × ℝ)} {β : List (B × ℝ)} {γ : List (C × ℝ)}
    (maximalA : Maximal stepA a α) (maximalB : Maximal stepB b β) (maximalC : Maximal stepC c γ) :
    ((shuffles β γ).map fun τ =>
        ((shuffles α (realize b c τ)).map (schedProb stepA (par stepB stepC) a (b, c))).sum).sum =
      pathProb stepA a α * pathProb stepB b β * pathProb stepC c γ := by
  have inner : ∀ τ ∈ shuffles β γ,
      ((shuffles α (realize b c τ)).map (schedProb stepA (par stepB stepC) a (b, c))).sum =
        pathProb stepA a α * schedProb stepB stepC b c τ := by
    intro τ member
    have composite := maximal_realize stepB stepC maximalB maximalC member
    rw [sum_shuffles stepA (par stepB stepC) positiveA (positive_par stepB stepC positiveB positiveC)
      α _ a (b, c) maximalA.1 composite.1 maximalA.2 composite.2, pathProb_realize]
  rw [List.map_congr_left inner, List.sum_map_mul_left,
    sum_shuffles stepB stepC positiveB positiveC β γ b c maximalB.1 maximalC.1 maximalB.2 maximalC.2,
    mul_assoc]

end Monoidal

#print axioms positive_par
#print axioms endState_realize
#print axioms maximal_realize
#print axioms history_factorizes_three

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CausalHistories

end
