import Mettapedia.Languages.Agda.Adequacy.AdministrativeCanonizationComponents
import Mettapedia.Languages.Agda.SourceMetatheory.PiInjectivity

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.AdministrativePreservation

open Structural
open Structural.Statics (RawContext TypeParameter TypeBody)
open Structural.AdministrativeStatics

noncomputable def piInjectivity {n : Nat} {Γ : RawContext n}
    {A A' : TypeParameter n} {B B' : TypeBody n}
    (equal : CoreDerivation (Statics.typeEqual Γ (Statics.piType A B).code (Statics.piType A' B').code)) :
    CoreDerivation (Statics.typeEqual Γ A.code A'.code) ×
      CoreDerivation (Statics.typeEqual (Γ.snoc A.code) B.open.code B'.open.code) := by
  let reflected := AdministrativeReflection.reflectTypeEquality equal
  let first := Observation.piView A B reflected.2.leftObserved
  let second := Observation.piView A' B' reflected.2.rightObserved
  have source : StaticSpecification.TypeEq reflected.1.value
      (StaticSpecification.Ty.pi first.domain first.body) (StaticSpecification.Ty.pi second.domain second.body) :=
    (congrArg₂ (StaticSpecification.TypeEq reflected.1.value) first.result_eq second.result_eq).mp reflected.2.proof
  let components := SourceMetatheory.LogicalRelation.sourcePiInjectivity source
  exact Canonization.transportObservedPiComponents equal reflected.1.observed
    first.domain_eq second.domain_eq first.body_eq second.body_eq components.1 components.2

end Mettapedia.Languages.Agda.StaticAdequacy.AdministrativePreservation
