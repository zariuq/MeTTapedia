import Mettapedia.Languages.Agda.Adequacy.AdministrativeBeta
import Mettapedia.Languages.Agda.Structural.AdministrativeCompatibleResults

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.AdministrativePreservation

open Mettapedia.OSLF.Binding
open Structural
open Structural.Statics (RawTm RawTy RawContext RawSub)
open Structural.AdministrativeStatics

noncomputable def betaCases : StablePreservation.BetaCases where
  binding _ _ _ _ _ := betaBinding
  nonbinding _ _ _ _ _ := betaNonbinding

noncomputable def compatible {n : Nat} {s : Srt} {source target : Term sig (scope n) s}
    (step : Step source target) : StablePreservation.StableAction source target :=
  StablePreservation.compatible betaCases step

noncomputable def termCertificate {n : Nat} {source target : RawTm n} (step : Step source target) :
    Preservation.TermCertificate source target := StablePreservation.conditionalTermCertificate betaCases step

noncomputable def typeCertificate {n : Nat} {source target : RawTy n} (step : Step source target) :
    Preservation.TypeCertificate source target where
  step := step
  equality := (StablePreservation.conditionalTypeCertificate betaCases step).equality

noncomputable def spineCertificate {n : Nat} {source target : Spine (scope n)} (step : Step source target) :
    Preservation.SpineCertificate source target := StablePreservation.conditionalSpineCertificate betaCases step

noncomputable def termEquality {n : Nat} {Γ : RawContext n} {source target : RawTm n} {A : RawTy n}
    (step : Step source target) (typed : CoreDerivation (Statics.typed Γ source A)) :
    CoreDerivation (Statics.termEqual Γ source target A) := (termCertificate step).equality Γ A typed

noncomputable def termPreservation {n : Nat} {Γ : RawContext n} {source target : RawTm n} {A : RawTy n}
    (step : Step source target) (typed : CoreDerivation (Statics.typed Γ source A)) :
    CoreDerivation (Statics.typed Γ target A) := (termEquality step typed).termEndpoints.right

noncomputable def typeEquality {n : Nat} {Γ : RawContext n} {source target : RawTy n}
    (step : Step source target) (formed : CoreDerivation (Statics.formed Γ source)) :
    CoreDerivation (Statics.typeEqual Γ source target) := (typeCertificate step).equality Γ formed

noncomputable def typePreservation {n : Nat} {Γ : RawContext n} {source target : RawTy n}
    (step : Step source target) (formed : CoreDerivation (Statics.formed Γ source)) :
    CoreDerivation (Statics.formed Γ target) := (typeEquality step formed).typeEndpoints.right

noncomputable def spineEquality {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    {source target : Spine (scope n)} (step : Step source target) (action : Action Γ A source B) :
    SpineEq Γ A source target B := (spineCertificate step).equality Γ A B action

noncomputable def spinePreservation {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    {source target : Spine (scope n)} (step : Step source target) (action : Action Γ A source B)
    (input : CoreDerivation (Statics.formed Γ A)) : Action Γ A target B :=
  ((spineEquality step action).endpoints input).right

end Mettapedia.Languages.Agda.StaticAdequacy.AdministrativePreservation
