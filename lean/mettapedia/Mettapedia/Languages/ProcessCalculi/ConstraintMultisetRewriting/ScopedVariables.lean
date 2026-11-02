import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep
import Mettapedia.Logic.LP.StandardizeApart

/-!
# Fresh rule locals and captured shared variables

The existing LP renaming operation copies schema-local variables into an
activation scope and preserves captured variables. Two uses of the same
stored schema therefore share only explicitly captured variables, even if
their source locals have the same printed names. Checks and tells are copied
with the take, read and output terms.

This is the first-order freshening profile. Binding signatures and their
contextual support restrictions remain a separate profile obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedVariables

open Mettapedia.Logic.LP

variable {Local Shared : Type*} {signature : LPSignature}

/-- Local variables receive an activation identity; captured variables keep
their original identity. Rigid parameters may be carried by the signature's
constants or by the protected-parameter profile. -/
def variableAt (scope : Nat) : Local ⊕ Shared → ScopedVar Local ⊕ Shared
  | .inl localName => .inl (ScopedVar.at scope localName)
  | .inr sharedName => .inr sharedName

def termAt (scope : Nat) (term : Term (signature.withVars (Local ⊕ Shared))) :
    Term (signature.withVars (ScopedVar Local ⊕ Shared)) :=
  Term.renameVars (σ := signature.withVars (Local ⊕ Shared)) (variableAt scope) term

def ruleAt (scope : Nat) (rule : RuleInstance (Term (signature.withVars (Local ⊕ Shared)))) :
    RuleInstance (Term (signature.withVars (ScopedVar Local ⊕ Shared))) :=
  rule.map (termAt scope)

theorem variableAt_injective (scope : Nat) :
    Function.Injective (variableAt (Local := Local) (Shared := Shared) scope) := by
  let back : ScopedVar Local ⊕ Shared → Local ⊕ Shared := Sum.map ScopedVar.name id
  have inverse : Function.LeftInverse back (variableAt scope) := by
    intro name
    cases name <;> rfl
  exact inverse.injective

variable [DecidableEq Local] [DecidableEq Shared]

theorem local_scope (scope : Nat) (term : Term (signature.withVars (Local ⊕ Shared)))
    (localName : ScopedVar Local) (member : Sum.inl localName ∈ (termAt scope term).freeVars) :
    localName.scope = scope := by
  obtain ⟨original, _, image⟩ :=
    (Term.mem_freeVars_renameVars (σ := signature.withVars (Local ⊕ Shared))
      (variableAt scope) term (.inl localName)).mp member
  cases original with
  | inl name =>
    have same : ScopedVar.at scope name = localName := Sum.inl.inj image
    exact congrArg ScopedVar.scope same.symm
  | inr name => cases image

theorem captured_iff (scope : Nat) (term : Term (signature.withVars (Local ⊕ Shared)))
    (sharedName : Shared) :
    Sum.inr sharedName ∈ (termAt scope term).freeVars ↔ Sum.inr sharedName ∈ term.freeVars := by
  rw [termAt, Term.mem_freeVars_renameVars (σ := signature.withVars (Local ⊕ Shared))]
  constructor
  · rintro ⟨original, member, image⟩
    cases original with
    | inl _ => cases image
    | inr name =>
      have same : name = sharedName := Sum.inr.inj image
      exact same ▸ member
  · intro member
    exact ⟨.inr sharedName, member, rfl⟩

/-- Fresh uses cannot accidentally alias a schema-local variable. -/
theorem different_activations_only_share_captures {leftScope rightScope : Nat}
    (different : leftScope ≠ rightScope)
    (left right : Term (signature.withVars (Local ⊕ Shared)))
    (name : ScopedVar Local ⊕ Shared)
    (inLeft : name ∈ (termAt leftScope left).freeVars)
    (inRight : name ∈ (termAt rightScope right).freeVars) :
    ∃ sharedName : Shared, name = .inr sharedName := by
  cases name with
  | inr sharedName => exact ⟨sharedName, rfl⟩
  | inl localName =>
    exact False.elim (different ((local_scope leftScope left localName inLeft).symm.trans
      (local_scope rightScope right localName inRight)))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedVariables
