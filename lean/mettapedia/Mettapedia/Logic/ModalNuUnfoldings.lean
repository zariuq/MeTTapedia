import Mettapedia.Logic.HMLInspection
import Mettapedia.Logic.ModalQuantaleSemantics

/-!
# Authored finite unfoldings of positive greatest fixed points

An unfolding is an actual capture-avoiding substitution into the supplied
body formula. Its satisfaction is compared with the genuine decreasing
Knaster--Tarski approximants. Fixed-point-free bodies earn fixed-point-free
unfoldings, so the independently defined modal inspection can test them.

Every refuted upper approximation refutes the greatest fixed point. A
confirmation is a certificate for that approximation; it becomes a certificate
for the limit under a separately earned stabilization bound. Finite state
carriers supply the existing cardinality bound.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalMuCalculus.Unfolding

open Mettapedia.Logic.ModalQuantaleSemantics.Boolean
open Mettapedia.Order.FiniteSetFixedPoints

universe u v

variable {State : Type u} {Action : Type v}

theorem bind_hml {n m : Nat} (body : Formula Action n) (admitted : body.isHML = true)
    (replacement : Fin n → Formula Action m)
    (finite : ∀ index, (replacement index).isHML = true) :
    (body.bind replacement).isHML = true := by
  induction body generalizing m with
  | tt => rfl
  | ff => rfl
  | var index => exact finite index
  | neg body inductionHypothesis => exact inductionHypothesis admitted replacement finite
  | conj first second firstHypothesis secondHypothesis =>
      have parts := Bool.and_eq_true_iff.mp admitted
      exact Bool.and_eq_true_iff.mpr ⟨firstHypothesis parts.1 replacement finite,
        secondHypothesis parts.2 replacement finite⟩
  | disj first second firstHypothesis secondHypothesis =>
      have parts := Bool.and_eq_true_iff.mp admitted
      exact Bool.and_eq_true_iff.mpr ⟨firstHypothesis parts.1 replacement finite,
        secondHypothesis parts.2 replacement finite⟩
  | diamond action body inductionHypothesis => exact inductionHypothesis admitted replacement finite
  | box action body inductionHypothesis => exact inductionHypothesis admitted replacement finite
  | mu body => exact False.elim (Bool.false_ne_true admitted)
  | nu body => exact False.elim (Bool.false_ne_true admitted)

theorem satisfies_bind_hml {n m : Nat} (lts : LTS State Action)
    (body : Formula Action n) (admitted : body.isHML = true)
    (replacement : Fin n → Formula Action m) (environment : Env State m) (state : State) :
    satisfies lts environment (body.bind replacement) state ↔
      satisfies lts (fun index => sat lts environment (replacement index)) body state := by
  induction body generalizing m state with
  | tt => rfl
  | ff => rfl
  | var index => rfl
  | neg body inductionHypothesis =>
      exact not_congr (inductionHypothesis admitted replacement environment state)
  | conj first second firstHypothesis secondHypothesis =>
      have parts := Bool.and_eq_true_iff.mp admitted
      exact and_congr (firstHypothesis parts.1 replacement environment state)
        (secondHypothesis parts.2 replacement environment state)
  | disj first second firstHypothesis secondHypothesis =>
      have parts := Bool.and_eq_true_iff.mp admitted
      exact or_congr (firstHypothesis parts.1 replacement environment state)
        (secondHypothesis parts.2 replacement environment state)
  | diamond action body inductionHypothesis =>
      change (∃ target ∈ lts.successors state action,
        satisfies lts environment (body.bind replacement) target) ↔ _
      simp only [inductionHypothesis admitted replacement environment, satisfies]
  | box action body inductionHypothesis =>
      change (∀ target ∈ lts.successors state action,
        satisfies lts environment (body.bind replacement) target) ↔ _
      simp only [inductionHypothesis admitted replacement environment, satisfies]
  | mu body => exact False.elim (Bool.false_ne_true admitted)
  | nu body => exact False.elim (Bool.false_ne_true admitted)

theorem subst_closed_hml (body : Formula Action 1) (admitted : body.isHML = true)
    (replacement : Formula Action 0) (finite : replacement.isHML = true) :
    (body.subst replacement).isHML = true := by
  apply bind_hml body admitted
  intro index
  refine Fin.cases finite (fun impossible => Fin.elim0 impossible) index

theorem satisfies_subst_closed (lts : LTS State Action)
    (body : Formula Action 1) (admitted : body.isHML = true)
    (replacement : Formula Action 0) (state : State) :
    satisfies lts Env.empty (body.subst replacement) state ↔
      satisfies lts (Env.empty.extend (sat lts Env.empty replacement)) body state := by
  rw [Formula.subst, satisfies_bind_hml lts body admitted]
  apply satisfies_congr (fun _ _ _ => Iff.rfl)
  intro index target
  refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) index
  simp only [Fin.cases_zero, Env.extend, Fin.val_zero, ↓reduceDIte]

def nuUnfolding (body : Formula Action 1) : Nat → Formula Action 0
  | 0 => .tt
  | index + 1 => body.subst (nuUnfolding body index)

theorem nuUnfolding_hml (body : Formula Action 1) (admitted : body.isHML = true)
    (index : Nat) : (nuUnfolding body index).isHML = true := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis => exact subst_closed_hml body admitted _ inductionHypothesis

theorem nuUnfolding_semantics (lts : LTS State Action) (body : Formula Action 1)
    (admitted : body.isHML = true) (positive : body.isPositive = true)
    (index : Nat) (state : State) :
    satisfies lts Env.empty (nuUnfolding body index) state ↔
      state ∈ upperApproximation (bodyOrderHom lts Env.empty body positive) index := by
  induction index generalizing state with
  | zero => rfl
  | succ index inductionHypothesis =>
      rw [nuUnfolding, satisfies_subst_closed lts body admitted, upperApproximation_succ]
      change satisfies lts (Env.empty.extend (sat lts Env.empty (nuUnfolding body index))) body state ↔
        satisfies lts (Env.empty.extend
          (upperApproximation (bodyOrderHom lts Env.empty body positive) index)) body state
      apply satisfies_congr (fun _ _ _ => Iff.rfl)
      intro position target
      refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) position
      simp only [Env.extend, Fin.val_zero, ↓reduceDIte]
      exact inductionHypothesis target

structure PositiveHMLBody (Action : Type v) where
  body : Formula Action 1
  finite : body.isHML = true
  positive : body.isPositive = true

def PositiveHMLBody.atStage (hypothesis : PositiveHMLBody Action) (index : Nat) : Formula Action 0 :=
  nuUnfolding hypothesis.body index

theorem PositiveHMLBody.stage_admitted (hypothesis : PositiveHMLBody Action) (index : Nat) :
    (hypothesis.atStage index).isHML = true :=
  nuUnfolding_hml hypothesis.body hypothesis.finite index

theorem original_implies_stage (lts : LTS State Action) (hypothesis : PositiveHMLBody Action)
    (index : Nat) (state : State)
    (original : satisfies lts Env.empty (.nu hypothesis.body) state) :
    satisfies lts Env.empty (hypothesis.atStage index) state := by
  apply (nuUnfolding_semantics lts hypothesis.body hypothesis.finite hypothesis.positive index state).2
  exact gfp_le_upperApproximation (bodyOrderHom lts Env.empty hypothesis.body hypothesis.positive) index
    ((satisfies_nu_iff_mem_gfp lts Env.empty hypothesis.body hypothesis.positive state).1 original)

theorem refuted_stage_refutes_original (lts : LTS State Action)
    (hypothesis : PositiveHMLBody Action) (index : Nat) (state : State)
    (refuted : ¬ satisfies lts Env.empty (hypothesis.atStage index) state) :
    ¬ satisfies lts Env.empty (.nu hypothesis.body) state :=
  fun original => refuted (original_implies_stage lts hypothesis index state original)

theorem finite_stage_equals_original [Finite State] (lts : LTS State Action)
    (hypothesis : PositiveHMLBody Action) (index : Nat) (enough : Nat.card State ≤ index)
    (state : State) :
    satisfies lts Env.empty (hypothesis.atStage index) state ↔
      satisfies lts Env.empty (.nu hypothesis.body) state := by
  change satisfies lts Env.empty (nuUnfolding hypothesis.body index) state ↔ _
  rw [nuUnfolding_semantics lts hypothesis.body hypothesis.finite hypothesis.positive,
    satisfies_nu_iff_mem_gfp]
  let transformer := bodyOrderHom lts Env.empty hypothesis.body hypothesis.positive
  have stable : upperApproximation transformer (Nat.card State) = transformer.gfp :=
    (gfp_eq_iterate_univ transformer).symm
  constructor
  · intro atIndex
    exact stable ▸ upperApproximation_antitone transformer enough atIndex
  · intro atLimit
    exact gfp_le_upperApproximation transformer index atLimit

end Mettapedia.Logic.ModalMuCalculus.Unfolding
