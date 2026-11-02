import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualInteractionFactors
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedStep

/-! # The existing contextual firing and its independently executable resource factor -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFactorization

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open ContextualActivatedStep
open ContextualInteractionFactors

universe u
variable {S : Signature} {Local Shared : Type} {O : Type u} [DecidableEq O]
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
  (occupied : Finset Nat) (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
  (rule : RuleInstance (Term (Mettapedia.OSLF.Binding.ContextualFamily.signature S
    (source locals captures)) Γ sort))
  (rows : O → ContextualStoredRows.Row locals captures Γ sort)
  (before : Configuration (Term (Mettapedia.OSLF.Binding.ContextualFamily.signature S captures) Γ sort) O)
  (outputs : O → Term (Mettapedia.OSLF.Binding.ContextualFamily.signature S (target locals captures)) Γ sort)

/-- The resource operator computes the actual physical successor of the existing step. -/
theorem valid_runs_resource_operator
    (valid : ContextualGuardedStep.Valid locals captures occupied selection rule rows before outputs) :
    ResourceOccupation.commit selection.taken selection.read selection.made before.present =
      some (result locals captures occupied selection rule rows before).present :=
  Admitted.resource_result locals captures
    ((ContextualGuardedStep.valid_iff_factors locals captures occupied selection rule rows before outputs).mp valid)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFactorization
