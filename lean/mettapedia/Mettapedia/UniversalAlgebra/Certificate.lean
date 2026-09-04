import Mettapedia.UniversalAlgebra.EquationalLogic

/-!
# Replay witnesses for equational consequence

For signatures with decidable operation symbols, each equational-rule
application has finite, directly checkable data.  This gives every equation
system the same generic derivation-certificate format without attaching a
semantic model to the checker.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

open Mettapedia.Logic

universe u

variable {S : Signature.{u}} [DecidableEq S.Operation]

/-- Fully explicit data for one equational-rule application. -/
inductive EquationalRuleWitness (system : EquationSystem S) : Type u where
  | systemInstance (occurrence : Fin system.equations.length)
      (substitution : Nat → Term S)
  | refl (term : Term S)
  | symm (left right : Term S)
  | trans (left middle right : Term S)
  | congruence (operation : S.Operation)
      (left right : Fin (S.arity operation) → Term S)

namespace EquationalRuleWitness

variable {system : EquationSystem S}

/-- Boolean replay for one explicit rule witness. -/
def isInstance (witness : EquationalRuleWitness system)
    (premises : List (Equation S)) (conclusion : Equation S) : Bool :=
  match witness with
  | .systemInstance occurrence substitution =>
      decide (premises = [] ∧ conclusion =
        ((system.equations.get occurrence).1.subst substitution,
         (system.equations.get occurrence).2.subst substitution))
  | .refl term =>
      decide (premises = [] ∧ conclusion = (term, term))
  | .symm left right =>
      decide (premises = [(left, right)] ∧ conclusion = (right, left))
  | .trans left middle right =>
      decide (premises = [(left, middle), (middle, right)] ∧
        conclusion = (left, right))
  | .congruence operation left right =>
      decide (premises = List.ofFn (fun position =>
        (left position, right position)) ∧
        conclusion = (.op operation left, .op operation right))

theorem isInstance_sound (witness : EquationalRuleWitness system)
    (premises : List (Equation S)) (conclusion : Equation S)
    (accepted : witness.isInstance premises conclusion = true) :
    EquationalRule system premises conclusion := by
  cases witness with
  | systemInstance occurrence substitution =>
      simp only [isInstance, decide_eq_true_eq] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      exact EquationalRule.systemInstance
        (List.mem_iff_get.mpr ⟨occurrence, rfl⟩) substitution
  | refl term =>
      simp only [isInstance, decide_eq_true_eq] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      exact EquationalRule.refl term
  | symm left right =>
      simp only [isInstance, decide_eq_true_eq] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      exact EquationalRule.symm left right
  | trans left middle right =>
      simp only [isInstance, decide_eq_true_eq] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      exact EquationalRule.trans left middle right
  | congruence operation left right =>
      simp only [isInstance, decide_eq_true_eq] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      exact EquationalRule.congruence operation left right

theorem isInstance_complete (premises : List (Equation S))
    (conclusion : Equation S) (rule : EquationalRule system premises conclusion) :
    ∃ witness : EquationalRuleWitness system,
      EquationalRuleWitness.isInstance witness premises conclusion = true := by
  cases rule with
  | @systemInstance equation member substitution =>
      change _ ∈ system.equations at member
      obtain ⟨occurrence, equationEq⟩ := List.mem_iff_get.mp member
      refine ⟨EquationalRuleWitness.systemInstance occurrence substitution, ?_⟩
      change decide ([] = [] ∧
        (equation.1.subst substitution, equation.2.subst substitution) =
          ((system.equations.get occurrence).1.subst substitution,
           (system.equations.get occurrence).2.subst substitution)) = true
      rw [equationEq]
      simp
  | refl term =>
      exact ⟨EquationalRuleWitness.refl term, by simp [isInstance]⟩
  | symm left right =>
      exact ⟨EquationalRuleWitness.symm left right, by simp [isInstance]⟩
  | trans left middle right =>
      exact ⟨EquationalRuleWitness.trans left middle right, by simp [isInstance]⟩
  | congruence operation left right =>
      exact ⟨EquationalRuleWitness.congruence operation left right,
        by simp [isInstance]⟩

end EquationalRuleWitness

/-- The exact generic replay interface for an equation system. -/
def equationalRuleInterface (system : EquationSystem S) :
    RuleWitness (EquationalRule system) where
  W := EquationalRuleWitness system
  isInstance := EquationalRuleWitness.isInstance
  sound := EquationalRuleWitness.isInstance_sound
  complete := EquationalRuleWitness.isInstance_complete

end Mettapedia.UniversalAlgebra
