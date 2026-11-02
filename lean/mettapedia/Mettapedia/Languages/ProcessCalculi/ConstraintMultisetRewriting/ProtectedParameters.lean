import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder
import Mettapedia.Logic.LP.RigidUnification

/-!
# Protected parameters in a two-sided first-order profile

The substitution carrier records which identities are rigid. Both sides of
equations still unify; protecting an eigenparameter does not turn unification
into one-sided matching. The implementation reuses rigid unification's
encoding into the existing LP terms and its total solver.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProtectedParameters

open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.RigidUnification

universe u v
variable {signature : LPSignature.{u, u, v, u}}

abbrev Assignment (rigid : signature.vars → Prop) :=
  {σ : Subst signature // Fixes rigid σ}

def identity (rigid : signature.vars → Prop) : Assignment rigid :=
  ⟨Subst.id signature, fun _ _ => rfl⟩

def compose (rigid : signature.vars → Prop) (outer inner : Assignment rigid) :
    Assignment rigid := by
  refine ⟨outer.val.comp inner.val, ?_⟩
  intro variableName isRigid
  change outer.val.applyTerm (inner.val variableName) = .var variableName
  rw [inner.property variableName isRigid]
  exact outer.property variableName isRigid

def action (rigid : signature.vars → Prop) :
    SubstitutionAction (Term signature) (Assignment rigid) where
  E := Eq
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  apply := fun σ => σ.val.applyTerm
  identity := identity rigid
  compose := compose rigid
  apply_identity := Subst.applyTerm_id
  apply_compose := fun outer inner => Subst.applyTerm_comp outer.val inner.val
  preserves := fun σ {_ _} same => congrArg σ.val.applyTerm same

theorem parameter_fixed (rigid : signature.vars → Prop) (σ : Assignment rigid)
    (name : signature.vars) (isRigid : rigid name) :
    (action rigid).apply σ (.var name) = .var name := σ.property name isRigid

theorem supported_term_fixed [DecidableEq signature.vars]
    (rigid : signature.vars → Prop) (σ : Assignment rigid) (term : Term signature)
    (supported : ∀ name ∈ term.freeVars, rigid name) :
    (action rigid).apply σ term = term := by
  induction term with
  | var name => exact parameter_fixed rigid σ name (supported name (by simp [Term.freeVars]))
  | const _ => rfl
  | app symbol arguments ih =>
    change Term.app symbol (fun i => σ.val.applyTerm (arguments i)) = Term.app symbol arguments
    congr 1
    funext i
    apply ih i
    intro name member
    exact supported name (by simp [Term.freeVars]; exact ⟨i, member⟩)

variable (rigid : signature.vars → Prop) [DecidablePred rigid]
  [DecidableEq signature.vars] [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols]

theorem accepted_principal (store : EquationStore (Term signature))
    (answer : Subst signature) (accepted : solve rigid store = some answer) :
    ∃ permitted : Assignment rigid, permitted.val = answer ∧
      (action rigid).Principal store permitted := by
  obtain ⟨fixed, sound⟩ := solve_sound rigid store answer accepted
  refine ⟨⟨answer, fixed⟩, rfl, sound, ?_⟩
  intro candidate solved
  obtain ⟨factor, factorFixed, factors⟩ :=
    solve_mgu rigid store answer candidate.val accepted candidate.property solved
  refine ⟨⟨factor, factorFixed⟩, fun term => ?_⟩
  change candidate.val.applyTerm term = (factor.comp answer).applyTerm term
  exact congrArg (fun σ : Subst signature => σ.applyTerm term) factors

theorem accepted_iff_consistent (store : EquationStore (Term signature)) :
    (∃ answer, solve rigid store = some answer) ↔ (action rigid).Consistent store := by
  constructor
  · rintro ⟨answer, accepted⟩
    obtain ⟨permitted, _, principal⟩ := accepted_principal rigid store answer accepted
    exact ⟨permitted, principal.sound⟩
  · rintro ⟨answer, solved⟩
    exact solve_complete rigid store ⟨answer.val, answer.property, solved⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProtectedParameters
