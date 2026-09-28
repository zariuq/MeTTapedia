import Mettapedia.Languages.Agda.Structural.AdministrativeBinderPreservation

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.StablePreservation

open Mettapedia.OSLF.Binding
open Statics (RawTm RawTy RawContext)
open Preservation

structure StableTermCertificate {n : Nat} (source target : RawTm n) where
  step : Step source target
  equality : ∀ {m : Nat} (σ : Statics.RawSub n m) (Γ : RawContext m) (A : RawTy m),
    CoreDerivation (Statics.typed Γ (bind σ source) A) →
      CoreDerivation (Statics.termEqual Γ (bind σ source) (bind σ target) A)

noncomputable def StableTermCertificate.atSubstitution {n m : Nat} {source target : RawTm n}
    (certificate : StableTermCertificate source target) (σ : Statics.RawSub n m) :
    TermCertificate (bind σ source) (bind σ target) where
  step := Step.substitute σ certificate.step
  equality := certificate.equality σ

noncomputable def stableEmpty {n : Nat} (head : RawTm n) : StableTermCertificate (eliminate head nil) head where
  step := .root (.eliminateEmpty head)
  equality σ Γ A tree := (Preservation.eliminateEmpty (bind σ head)).equality Γ A tree

noncomputable def stableNonbinding {n : Nat} {first second : RawTm n}
    (certificate : StableTermCertificate first second) : TermCertificate (lamNoAbs first) (lamNoAbs second) := by
  have original : TermCertificate first second := {
    step := certificate.step
    equality := fun Γ A tree => by
      have image := certificate.equality (Telescope.identity (S := sig) .term n) Γ A
      simp only [Telescope.bind_identity first, Telescope.bind_identity second] at image
      exact image tree }
  exact lambdaNoAbs original (certificate.atSubstitution (Telescope.projection (S := sig) .term n))

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.StablePreservation
