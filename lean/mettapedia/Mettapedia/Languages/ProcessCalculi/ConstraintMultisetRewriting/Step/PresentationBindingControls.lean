import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationRuleExecution

/-! # Binding-sensitive controls for the interpreted payloads

The actual ambient-substitution action cannot solve an equation by capturing
an enclosing binder. The positive twin substitutes a closed structural value.
Both sides are ordinary encoded payloads, with their field depths retained.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Payloads.BindingControls

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns

def bind (body : Payloads.Term) : Payloads.Term := .node (.symbol 0) (.cons 1 body .nil)
def captured : Payloads.Term := bind (.idx 0)
def ambient : Payloads.Term := bind (.idx 1)
def closedValue : Payloads.Term := .node (.name 8) .nil

theorem bound_index_fixed (substitution : Nat → Payloads.Term) :
    BindingTrees.action.apply substitution captured = captured := rfl

theorem ambient_index_lifted (substitution : Nat → Payloads.Term) :
    BindingTrees.action.apply substitution ambient = bind (Term.lift 0 1 (substitution 0)) := by
  simp only [BindingTrees.action, ambient, bind, substitute_node, substitute_fields_cons,
    substitute_fields_nil, Term.substituteMany_idx, underBinders_eq]
  rfl

private theorem lift_cannot_capture (term : Payloads.Term) : Term.lift 0 1 term ≠ .idx 0 := by
  cases term <;> simp [Term.lift]

theorem capture_equation_unsolvable :
    ¬ BindingTrees.action.Consistent [(ambient, captured)] := by
  rintro ⟨substitution, solved⟩
  have same := solved (ambient, captured) (List.mem_singleton_self _)
  change BindingTrees.action.apply substitution ambient =
    BindingTrees.action.apply substitution captured at same
  rw [ambient_index_lifted, bound_index_fixed] at same
  have body := (Fields.cons.inj (Term.node.inj same).2).2.1
  exact lift_cannot_capture (substitution 0) body

theorem closed_substitution_solves :
    BindingTrees.action.Consistent [(ambient, bind closedValue)] := by
  refine ⟨fun _ => closedValue, ?_⟩
  intro equation member
  have same := List.mem_singleton.mp member
  subst equation
  rfl

theorem encoded_equation_retains_the_capture_obstruction :
    readEquations (equationsPattern [(ambient, captured)]) = some [(ambient, captured)] ∧
      ¬ BindingTrees.action.Consistent [(ambient, captured)] :=
  ⟨readEquations_pattern _, capture_equation_unsolvable⟩

/-- The ambient variable is well scoped when the ambient frame supplies it;
the negative equation fails because of capture, not because of malformed syntax. -/
theorem both_terms_well_scoped :
    Admitted unarySignature 1 ambient ∧ Admitted unarySignature 1 captured := by decide +kernel

/-- A sufficient ambient depth cannot excuse a wrong constructor field signature. -/
theorem wrong_depth_still_refused_with_ambient_variable :
    readAdmitted unarySignature 1 (termPattern wrongFieldDepth) = none := by
  simp [readAdmitted, readTerm_pattern, Admitted, wrongFieldDepth, unarySignature,
    Term.conforms, Term.Fields.conforms]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Payloads.BindingControls
