import Mettapedia.Languages.Agda.Structural.AdministrativeCompatibleFold

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.StablePreservation

open Mettapedia.OSLF.Binding
open Statics (RawTm RawTy RawContext)
open Preservation

noncomputable def compatibleAtIdentity (beta : BetaCases) {n : Nat} {s : Srt}
    {source target : Term sig (scope n) s} (step : Step source target) : TypedAction source target := by
  have action := compatible beta step (Telescope.identity (S := sig) .term n)
  exact (congrArg₂ (fun (first second : Term sig (scope n) s) => TypedAction first second)
    (Telescope.bind_identity source) (Telescope.bind_identity target)).mp action

noncomputable def conditionalTermCertificate (beta : BetaCases) {n : Nat} {source target : RawTm n}
    (step : Step source target) : TermCertificate source target where
  step := step
  equality := compatibleAtIdentity beta step

noncomputable def conditionalTypeCertificate (beta : BetaCases) {n : Nat} {source target : RawTy n}
    (step : Step source target) : TypeCertificate source target where
  step := step
  equality := compatibleAtIdentity beta step

noncomputable def conditionalSpineCertificate (beta : BetaCases) {n : Nat} {source target : Spine (scope n)}
    (step : Step source target) : SpineCertificate source target where
  step := step
  equality := compatibleAtIdentity beta step

noncomputable def conditionalTermPreservation (beta : BetaCases) {n : Nat} {source target : RawTm n}
    (step : Step source target) {Γ : RawContext n} {A : RawTy n}
    (typing : CoreDerivation (Statics.typed Γ source A)) : CoreDerivation (Statics.typed Γ target A) :=
  (conditionalTermCertificate beta step).typing typing

noncomputable def conditionalTypePreservation (beta : BetaCases) {n : Nat} {source target : RawTy n}
    (step : Step source target) {Γ : RawContext n}
    (formed : CoreDerivation (Statics.formed Γ source)) : CoreDerivation (Statics.formed Γ target) :=
  ((conditionalTypeCertificate beta step).equality Γ formed).typeEndpoints.right

noncomputable def conditionalSpinePreservation (beta : BetaCases) {n : Nat} {source target : Spine (scope n)}
    (step : Step source target) {Γ : RawContext n} {A B : RawTy n}
    (action : Action Γ A source B) (formed : CoreDerivation (Statics.formed Γ A)) : Action Γ A target B :=
  (conditionalSpineCertificate beta step).action action formed

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.StablePreservation
