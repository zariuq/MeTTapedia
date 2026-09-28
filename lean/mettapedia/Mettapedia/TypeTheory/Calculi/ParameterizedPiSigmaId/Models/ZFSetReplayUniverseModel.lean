import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayInterpretation

/-!
# Universe closure assumptions for the replay set interpretation

The head interpretation must realize the selected primitive universe rules.
This package concerns only sets, their membership and the existing Pi, Sigma
and identity codes. It does not assume soundness of typing replay, conversion,
declarations or certificate comparison.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open Mettapedia.Logic.HOL.Embedding
open ZFSetTraceProducts (tracePiSet)
open ZFSetDependentProducts (sigmaSet)
open ZFSetTraceProofDecoding (truthCode)

universe u
variable {Head : Type}

/-- Primitive closure for a particular universe-rule package and head valuation.
The family closure hypotheses are required only on the interpreted domain. -/
structure UniverseModel (R : Rules Head) (heads : Head → ZFSet.{u}) : Prop where
  headTyping_mem : ∀ {head level}, R.headTyping head level → heads head ∈ heads level
  cumulative_subset : ∀ {lower upper}, R.cumulative lower upper → heads lower ⊆ heads upper
  pi_mem : ∀ {domainLevel bodyLevel level}, R.join domainLevel bodyLevel level →
    ∀ {A : ZFSet.{u}}, A ∈ heads domainLevel →
    ∀ B : ZFSet.{u} → ZFSet.{u}, (∀ x ∈ A, B x ∈ heads bodyLevel) →
      tracePiSet A B ∈ heads level
  sigma_mem : ∀ {domainLevel bodyLevel level}, R.join domainLevel bodyLevel level →
    ∀ {A : ZFSet.{u}}, A ∈ heads domainLevel →
    ∀ B : ZFSet.{u} → ZFSet.{u}, (∀ x ∈ A, B x ∈ heads bodyLevel) →
      sigmaSet A B ∈ heads level
  identity_mem : ∀ {level}, R.isUniverse level → ∀ P : Prop, truthCode P ∈ heads level

/-- A head that types itself cannot be realized in this well-founded set model.
In particular the primitive obligations are not automatic for arbitrary rules. -/
theorem UniverseModel.headTyping_irrefl {R : Rules Head} {heads : Head → ZFSet.{u}}
    (model : UniverseModel R heads) (head : Head) : ¬ R.headTyping head head := by
  intro typed
  exact ZFSet.mem_irrefl (heads head) (model.headTyping_mem typed)

#print axioms UniverseModel.headTyping_irrefl

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
