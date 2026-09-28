import Mettapedia.Languages.Agda.Adequacy.AdministrativeCanonization
import Mettapedia.Languages.Agda.Adequacy.AdministrativeComponentTransport

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.Canonization

open Mettapedia.OSLF.Binding
open Structural
open Structural.Statics (RawContext TypeParameter TypeBody)
open Structural.AdministrativeStatics

/-- Actual source component derivations are transported back to the original
native components. The right codomain is first moved to the left raw domain.
No injectivity theorem is assumed or derived from syntax alone. -/
noncomputable def transportObservedPiComponents {n : Nat}
    {Γ : RawContext n} {Δ : StaticSpecification.RawContext n}
    {A A' : TypeParameter n} {B B' : TypeBody n}
    {a a' : StaticSpecification.Ty n} {b b' : StaticSpecification.TyAbs n}
    (equal : CoreDerivation (Statics.typeEqual Γ (Statics.piType A B).code (Statics.piType A' B').code))
    (contextObserved : Observation.context Γ = some Δ)
    (leftDomain : Observation.type A.code = some a)
    (rightDomain : Observation.type A'.code = some a')
    (leftBody : Observation.typeBody B = some b)
    (rightBody : Observation.typeBody B' = some b')
    (domain : StaticSpecification.TypeEq Δ a a')
    (codomain : StaticSpecification.TypeEq (Δ.snoc a) b.open b'.open) :
    CoreDerivation (Statics.typeEqual Γ A.code A'.code) ×
      CoreDerivation (Statics.typeEqual (Γ.snoc A.code) B.open.code B'.open.code) := by
  let left := equal.typeEndpoints.left.formationPiParts
  let right := equal.typeEndpoints.right.formationPiParts
  let base := (context equal.contextOfTypeEquality).returnAt contextObserved
  let domainEquality := ComponentTransport.bridgeTypeEquality base
    ((formation left.1).at leftDomain) ((formation right.1).at rightDomain) domain
  let rightCodomain := administrativeOperations.changeLastFormation right.1 left.1
    domainEquality.typeSymmetry right.2
  let extended := (context left.2.contextOfFormation).returnAt
    (Observation.context_snoc contextObserved leftDomain)
  exact ⟨domainEquality, ComponentTransport.bridgeTypeEquality extended
    ((formation left.2).at (Observation.typeBody_open_observed leftBody))
    ((formation rightCodomain).at (Observation.typeBody_open_observed rightBody)) codomain⟩

end Mettapedia.Languages.Agda.StaticAdequacy.Canonization
