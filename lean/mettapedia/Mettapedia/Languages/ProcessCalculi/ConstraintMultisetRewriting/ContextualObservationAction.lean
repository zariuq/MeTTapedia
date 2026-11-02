import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EquationStore
import Mettapedia.OSLF.Syntax.ContextualFamilyObservations

/-!
# A common equation carrier for all contextual term indices

Context and result-sort metadata allow one equation store to hold subproblems
under different binder prefixes. Its substitution action is contextual
instantiation on the existing binding terms. Equality reflects the complete
metadata, so incompatible context or sort tags cannot be silently identified.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualObservationAction

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V : Type} (declaration : V → MetaArity S)

def action : SubstitutionAction (Observation S declaration) (Assignment declaration declaration) where
  E := Eq
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  apply := instantiateObservation
  identity := generator declaration
  compose := Assignment.compose
  apply_identity := instantiateObservation_identity
  apply_compose := fun outer inner observation => (instantiateObservation_comp inner outer observation).symm
  preserves := fun assignment {_ _} same => congrArg (instantiateObservation assignment) same

theorem solves_observed_iff (assignment : Assignment declaration declaration)
    {Γ : Ctx S} {sort : S.Srt} (left right : Term (signature S declaration) Γ sort) :
    (action declaration).Solves assignment (observe left, observe right) ↔
      instantiate assignment left = instantiate assignment right := by
  change observe (instantiate assignment left) = observe (instantiate assignment right) ↔ _
  exact ⟨fun same => observe_injective (S := S) (source := declaration) same, congrArg observe⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualObservationAction
