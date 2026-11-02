import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedSolutionGluing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder

/-!
# Consistency under fresh-local, shared-capture instantiation

The existing scoped-variable map is used on both sides of every equation.
Solutions lift to a fresh use and pull back from it. Several uses combine
through the existing compatible-family gluing theorem, not through independent
Boolean satisfiability tests that forget captured-variable agreement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedEquationInstantiation

open Mettapedia.Logic.LP

variable {signature : LPSignature} {Private Shared : Type}

abbrev Source := Term (signature.withVars (Private ⊕ Shared))
abbrev Active := Term (signature.withVars (ScopedVar Private ⊕ Shared))

def equationAt (scope : Nat) (equation : Equation (Source (signature := signature) (Private := Private) (Shared := Shared))) :
    Equation (Active (signature := signature) (Private := Private) (Shared := Shared)) :=
  (ScopedVariables.termAt scope equation.1, ScopedVariables.termAt scope equation.2)

def storeAt (scope : Nat)
    (store : EquationStore (Source (signature := signature) (Private := Private) (Shared := Shared))) :=
  store.map (equationAt scope)

def forgetName : ScopedVar Private ⊕ Shared → Private ⊕ Shared := Sum.map ScopedVar.name id

theorem forget_variableAt (scope : Nat) (name : Private ⊕ Shared) :
    forgetName (ScopedVariables.variableAt scope name) = name := by
  cases name <;> rfl

def liftAssignment (scope : Nat) (assignment : Subst (signature.withVars (Private ⊕ Shared))) :
    Subst (signature.withVars (ScopedVar Private ⊕ Shared)) :=
  fun name => ScopedVariables.termAt scope (assignment (forgetName name))

def pullAssignment (scope : Nat) (assignment : Subst (signature.withVars (ScopedVar Private ⊕ Shared))) :
    Subst (signature.withVars (Private ⊕ Shared)) :=
  fun name => Term.renameVars (σ := signature.withVars (ScopedVar Private ⊕ Shared))
    forgetName (assignment (ScopedVariables.variableAt scope name))

theorem lift_apply (scope : Nat) (assignment : Subst (signature.withVars (Private ⊕ Shared)))
    (term : Source (signature := signature) (Private := Private) (Shared := Shared)) :
    (liftAssignment scope assignment).applyTerm (ScopedVariables.termAt scope term) =
      ScopedVariables.termAt scope (assignment.applyTerm term) := by
  induction term with
  | var name =>
      simp only [ScopedVariables.termAt, Term.renameVars, Subst.applyTerm,
        liftAssignment, forget_variableAt]
  | const constant => rfl
  | app function arguments ih =>
      simp only [ScopedVariables.termAt, Term.renameVars, Subst.applyTerm] at ih ⊢
      congr 1
      funext i
      exact ih i

theorem pull_apply (scope : Nat) (assignment : Subst (signature.withVars (ScopedVar Private ⊕ Shared)))
    (term : Source (signature := signature) (Private := Private) (Shared := Shared)) :
    (pullAssignment scope assignment).applyTerm term =
      (assignment.applyTerm (ScopedVariables.termAt scope term)).renameVars forgetName := by
  induction term with
  | var name => rfl
  | const constant => rfl
  | app function arguments ih =>
      simp only [ScopedVariables.termAt, Term.renameVars, Subst.applyTerm] at ih ⊢
      congr 1
      funext i
      exact ih i

theorem consistent_iff (scope : Nat)
    (store : EquationStore (Source (signature := signature) (Private := Private) (Shared := Shared))) :
    (FirstOrder.action (signature.withVars (ScopedVar Private ⊕ Shared))).Consistent (storeAt scope store) ↔
      (FirstOrder.action (signature.withVars (Private ⊕ Shared))).Consistent store := by
  constructor
  · rintro ⟨assignment, models⟩
    refine ⟨pullAssignment scope assignment, fun equation member => ?_⟩
    have solved := models (equationAt scope equation) (List.mem_map.mpr ⟨equation, member, rfl⟩)
    change (pullAssignment scope assignment).applyTerm equation.1 =
      (pullAssignment scope assignment).applyTerm equation.2
    rw [pull_apply, pull_apply]
    exact congrArg (Term.renameVars forgetName) solved
  · rintro ⟨assignment, models⟩
    refine ⟨liftAssignment scope assignment, fun equation member => ?_⟩
    change equation ∈ store.map (equationAt scope) at member
    obtain ⟨original, originalMember, same⟩ := List.mem_map.mp member
    subst equation
    change (liftAssignment scope assignment).applyTerm (ScopedVariables.termAt scope original.1) =
      (liftAssignment scope assignment).applyTerm (ScopedVariables.termAt scope original.2)
    rw [lift_apply, lift_apply]
    exact congrArg (ScopedVariables.termAt scope) (models original originalMember)

variable [DecidableEq Private] [DecidableEq Shared]

/-- The equation-store reading of the existing scoped gluing theorem.
Agreement on captured identities is retained as an explicit obligation. -/
theorem family_consistent_iff {n : Nat} (scopeOf : Fin n → Nat)
    (fresh : Function.Injective scopeOf)
    (stores : Fin n → EquationStore (Source (signature := signature) (Private := Private) (Shared := Shared))) :
    (FirstOrder.action (signature.withVars (ScopedVar Private ⊕ Shared))).Consistent
      ((List.finRange n).flatMap fun i => storeAt (scopeOf i) (stores i)) ↔
      ∃ family : Fin n → Subst (signature.withVars (ScopedVar Private ⊕ Shared)),
        (∀ i, ScopedSolutionGluing.Solves (family i) (scopeOf i) (stores i)) ∧
        ∀ i j shared, family i (.inr shared) = family j (.inr shared) := by
  rw [← ScopedSolutionGluing.glue scopeOf fresh stores]
  constructor
  · rintro ⟨assignment, models⟩
    refine ⟨assignment, fun i equation member => ?_⟩
    exact models (equationAt (scopeOf i) equation) (List.mem_flatMap.mpr
      ⟨i, List.mem_finRange i, List.mem_map.mpr ⟨equation, member, rfl⟩⟩)
  · rintro ⟨assignment, models⟩
    refine ⟨assignment, fun equation member => ?_⟩
    obtain ⟨i, _, member⟩ := List.mem_flatMap.mp member
    change equation ∈ (stores i).map (equationAt (scopeOf i)) at member
    obtain ⟨original, originalMember, same⟩ := List.mem_map.mp member
    subst equation
    exact models i original originalMember

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedEquationInstantiation
