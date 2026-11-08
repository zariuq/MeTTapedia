import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.GuardFragments
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionGuarded

/-!
# Polarity on open data: Sigma guards decide at a principal answer, Pi guards wait

The step asks a guard at every solution of a firing's information
(`Superposition.guarded_admits_iff`), so a datum the firing reads may still contain unknowns.
Meredith's constraint is evaluated on a candidate's closed substitution; here the candidate may
leave the datum open, and the polarity of a behaviour specification decides how its ask is
evaluated.

Suppose steps commute with instantiation (`StepsStable`): an instance of a step is a step of the
instance. Instantiation can then add behaviour (a redex appears once an unknown is bound) and
never remove it.

* **A Sigma guard is stable** (`eventually_stable`): if the datum reaches a state satisfying a
  stable predicate at a solution, it does at every instance. So its ask at every solution is **one
  evaluation at a principal answer** (`eventually_entails_iff`, through
  `Superposition.entails_iff_of_stable`).
* **A Pi guard is not** (`Controls.always_not_stable`): an unknown datum has no step, so "it never
  reaches `1`" holds at the principal answer, and fails at the instance `x ↦ 0`, which steps to
  `1`. The ask at every solution refuses, while an evaluation at the principal answer accepts. On
  open data a Pi guard waits until its datum is determined; it is refuted, never certified, by
  what is known so far.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardFragmentsOpen

open Superposition (Stable Respects entails_iff_of_stable)
open GuardFragments

universe uT uS

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S) (succ : T → Finset T)

/-- **Steps commute with instantiation**: an instance of a step is a step of the instance. -/
def StepsStable : Prop := ∀ σ t t', t' ∈ succ t → A.apply σ t' ∈ succ (A.apply σ t)

variable {A succ}

/-- An instance of a path is a path of the instance. -/
theorem reach_apply (stable : StepsStable A succ) (σ : S) {t e : T} (reach : Reach succ t e) :
    Reach succ (A.apply σ t) (A.apply σ e) := by
  induction reach with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.tail ih (stable σ _ _ step)

/-- **A Sigma guard on an open datum is stable.** -/
theorem eventually_stable (stable : StepsStable A succ) {q : T → Prop}
    (qStable : ∀ σ t, q t → q (A.apply σ t)) (d : T) :
    Stable A (fun σ => Eventually succ q (A.apply σ d)) := by
  rintro ν σ ⟨e, reach, holds⟩
  refine ⟨A.apply ν e, ?_, qStable ν e holds⟩
  rw [A.apply_compose]
  exact reach_apply stable ν reach

/-- A guard reading the datum's instance respects a syntactic equality. -/
theorem respects_of_eq (syntactic : ∀ s t, A.E s t → s = t) (d : T) (G : T → Prop) :
    Respects A (fun σ => G (A.apply σ d)) := by
  intro σ τ same
  show G (A.apply σ d) ↔ G (A.apply τ d)
  rw [syntactic _ _ (same d)]

/-- **A Sigma guard is decided at a principal answer by one evaluation.** -/
theorem eventually_entails_iff (stable : StepsStable A succ) {q : T → Prop}
    (qStable : ∀ σ t, q t → q (A.apply σ t)) (syntactic : ∀ s t, A.E s t → s = t) (d : T)
    {store : EquationStore T} {μ : S} (principal : A.Principal store μ) :
    A.Entails store (fun σ => Eventually succ q (A.apply σ d)) ↔ Eventually succ q (A.apply μ d) :=
  entails_iff_of_stable principal (respects_of_eq syntactic d _) (eventually_stable stable qStable d)

namespace Controls

/-- **One unknown**: a datum is the unknown `x` (`none`) or a constant; a substitution binds `x` or
leaves it. -/
def toy : SubstitutionAction (Option ℕ) (Option ℕ) where
  E := Eq
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  apply σ t := match t with
    | none => σ
    | some n => some n
  identity := none
  compose ν σ := match σ with
    | none => ν
    | some n => some n
  apply_identity t := by cases t <;> rfl
  apply_compose ν σ t := by cases t <;> cases σ <;> rfl
  preserves := by
    intro σ s t same
    subst same
    rfl

/-- The constant `0` steps to `1`; the unknown has no step. -/
def toySucc : Option ℕ → Finset (Option ℕ) := fun t => if t = some 0 then {some 1} else ∅

theorem toySucc_stable : StepsStable toy toySucc := by
  intro σ t t' step
  cases t with
  | none => simp [toySucc] at step
  | some n =>
      unfold toySucc at step ⊢
      split_ifs at step with h
      · rw [Finset.mem_singleton.mp step]
        show some 1 ∈ (if some n = some 0 then {some 1} else ∅)
        rw [if_pos h]
        exact Finset.mem_singleton_self _
      · simp at step

/-- The identity is a principal answer of the empty store. -/
theorem identity_principal : toy.Principal [] none :=
  ⟨by simp, fun δ _ => ⟨δ, fun t => by cases t <;> rfl⟩⟩

theorem unknown_reach {e : Option ℕ} (reach : Reach toySucc none e) : e = none := by
  induction reach with
  | refl => rfl
  | tail _ step ih =>
      subst ih
      simp [toySucc] at step

/-- **A Pi guard on an open datum is not stable**: "never reaches `1`" holds of the unknown at the
principal answer and fails at the instance `x ↦ 0`; so its ask at every solution refuses. -/
theorem always_not_stable :
    Always toySucc (fun e => e ≠ some 1) (toy.apply toy.identity none) ∧
      ¬ Always toySucc (fun e => e ≠ some 1) (toy.apply (some 0) none) ∧
      ¬ toy.Entails [] (fun σ => Always toySucc (fun e => e ≠ some 1) (toy.apply σ none)) := by
  have instance_fails : ¬ Always toySucc (fun e => e ≠ some 1) (toy.apply (some 0) none) :=
    fun always => always (some 1)
      (Relation.ReflTransGen.single (by decide : some 1 ∈ toySucc (some 0))) rfl
  refine ⟨fun e reach => ?_, instance_fails, fun asked => instance_fails (asked (some 0) (by simp))⟩
  rw [unknown_reach reach]
  simp

/-- **The Sigma guard "reaches `1`" is decided at the principal answer**: there it fails, so the ask
refuses; at the instance `x ↦ 0` it holds, and the refined store's ask admits. -/
theorem eventually_at_principal :
    (toy.Entails [] (fun σ => Eventually toySucc (fun e => e = some 1) (toy.apply σ none)) ↔
        Eventually toySucc (fun e => e = some 1) (toy.apply toy.identity none)) ∧
      ¬ Eventually toySucc (fun e => e = some 1) (toy.apply toy.identity none) ∧
      Eventually toySucc (fun e => e = some 1) (toy.apply (some 0) none) := by
  refine ⟨eventually_entails_iff toySucc_stable ?_ (fun _ _ same => same) none identity_principal, ?_,
    ⟨some 1, Relation.ReflTransGen.single (by decide : some 1 ∈ toySucc (some 0)), rfl⟩⟩
  · intro σ t holds
    subst holds
    rfl
  · rintro ⟨e, reach, holds⟩
    rw [unknown_reach reach] at holds
    cases holds

end Controls

#print axioms reach_apply
#print axioms eventually_stable
#print axioms eventually_entails_iff
#print axioms Controls.toySucc_stable
#print axioms Controls.identity_principal
#print axioms Controls.always_not_stable
#print axioms Controls.eventually_at_principal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardFragmentsOpen
