import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProtectedParameters
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

/-!
# Binding authority follows resolved dependencies

Protecting the variable at the root of an observation is insufficient when
its current value contains other shared variables. A permitted residual
substitution preserves the observation when it fixes every variable in that
resolved value. The counterexample shows why this closure is necessary.

This is the substitution law required of an authority boundary; it does not
assert that a native publication path already enforces that boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BindingAuthority

open Mettapedia.Logic.LP

universe u v

section General

variable {signature : LPSignature.{u, u, v, u}} [DecidableEq signature.vars]

/-- The support must be read after the incoming bindings have been applied. -/
theorem resolved_observation_unchanged (rigid : signature.vars → Prop)
    (incoming : Subst signature) (later : ProtectedParameters.Assignment rigid)
    (observed : Term signature)
    (protectedSupport : ∀ name ∈ (incoming.applyTerm observed).freeVars, rigid name) :
    (later.val.comp incoming).applyTerm observed = incoming.applyTerm observed := by
  rw [Subst.applyTerm_comp]
  exact ProtectedParameters.supported_term_fixed rigid later (incoming.applyTerm observed)
    protectedSupport

end General

namespace Controls

abbrev signature := ConstraintMultisetRewriting.Controls.signature

def rigid (name : Nat) : Prop := name = 0
def incoming : Subst signature := Subst.single 0 (.var 1)
def later : Subst signature := Subst.single 1 (.const 7)

theorem root_identity_is_protected : RigidUnification.Fixes rigid later := by
  intro name isRigid
  have same : name = 0 := isRigid
  subst name
  rfl

theorem protected_root_can_still_observe_a_change :
    incoming.applyTerm (.var 0) = .var 1 ∧
    (later.comp incoming).applyTerm (.var 0) = .const 7 := ⟨rfl, rfl⟩

/-- The failed support obligation identifies the actual missing dependency. -/
theorem protected_root_is_not_dependency_closure :
    ¬ ∀ name ∈ (incoming.applyTerm (.var 0)).freeVars, rigid name := by
  intro closed
  have impossible := closed 1 (by simp [incoming, Subst.applyTerm, Subst.single, Term.freeVars])
  exact Nat.noConfusion impossible

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BindingAuthority
