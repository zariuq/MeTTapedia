import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalAnswers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReachControls

/-! # Zero-fuel conditional answers retain their constraint; erasure admits a wrong value -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalAnswers.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching
open SchematicReach.Controls (spaceSignature DataOperator symbol)

abbrev base := spaceSignature
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := by
  change DecidableEq (DataOperator ⊕ Operator (SchematicReach.spaceDeclaration
    SchematicReach.Controls.dataSignature () (Name := Nat)) sort)
  infer_instance

abbrev declaration (_ : Nat) : MetaArity base := ([], ())
def value : SchematicReach.Closed declaration := generator declaration 0
def problem : ContextualResidual.Problem declaration := [(observe value, observe (symbol 1))]
def update := ContextualFrameWorklist.identity problem
def conditional := ofUpdate update value

theorem the_actual_zero_fuel_result_keeps_the_equation :
    ContextualFrameWorklist.run 0 declaration problem = .residual update ∧ update.remaining = problem := ⟨rfl, rfl⟩

private theorem instantiate_symbol {V Next : Type} {decl : V → MetaArity base} {next : Next → MetaArity base}
    (assignment : Assignment decl next) (number : Nat) : instantiate assignment (symbol number) = symbol number := rfl

theorem the_pending_answer_accepts_its_required_value : conditional.Instances declaration (symbol 1) := by
  apply (ofUpdate_exact update value declaration (symbol 1)).mpr
  refine ⟨Extension.identity declaration, (fun _ => symbol 1), ?_, ?_⟩
  · apply (ContextualResidual.models_observed_iff _ _ _).mpr
    rw [value, instantiate_generator, instantiate_symbol]
  · rw [value, instantiate_generator]
    rfl

theorem erasing_the_obligation_admits_the_wrong_value :
    ContextualPublication.Instances update.declaration conditional.value declaration (symbol 2) := by
  refine ⟨Extension.identity declaration, (fun _ => symbol 2), ?_⟩
  change instantiate (fun _ : Nat => (symbol 2 : SchematicReach.Closed declaration))
    (instantiate (generator declaration) value) = _
  rw [instantiate_identity, value, instantiate_generator]
  rfl

theorem the_conditional_answer_refuses_that_wrong_value : ¬ conditional.Instances declaration (symbol 2) := by
  intro matched
  obtain ⟨extension, candidate, model, same⟩ := (ofUpdate_exact update value declaration (symbol 2)).mp matched
  have required := (ContextualResidual.models_observed_iff candidate value (symbol 1)).mp model
  rw [value, instantiate_generator, instantiate_symbol] at required same
  have impossible : (1 : Nat) = 2 := SchematicReach.Controls.symbol_injective (required.symm.trans same)
  omega

theorem an_independent_value_can_be_returned_with_unfinished_obligations :
    update.remaining ≠ [] ∧ (ofUpdate update (symbol 7)).Instances declaration (symbol 7) := by
  refine ⟨by decide +kernel, ?_⟩
  apply (ofUpdate_exact update (symbol 7) declaration (symbol 7)).mpr
  refine ⟨Extension.identity declaration, (fun _ => symbol 1), ?_, rfl⟩
  apply (ContextualResidual.models_observed_iff _ _ _).mpr
  rw [value, instantiate_generator, instantiate_symbol]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalAnswers.Controls
