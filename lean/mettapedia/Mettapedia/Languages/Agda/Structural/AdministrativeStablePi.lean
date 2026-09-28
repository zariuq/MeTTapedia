import Mettapedia.Languages.Agda.Structural.AdministrativeStableActions

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.StablePreservation

open Mettapedia.OSLF.Binding
open Preservation
open Statics (RawTy TypeParameter)

noncomputable def piDomainAction {n : Nat} {first second : RawTy n} (codomain : RawTy (n + 1))
    (step : Step first second) (action : StableAction first second) :
    StableAction (pi first codomain) (pi second codomain) := by
  intro m σ Γ T tree
  change CoreDerivation (Statics.typed Γ (pi (bind σ first) (bind (Telescope.lift σ) codomain)) T) at tree
  change CoreDerivation (Statics.termEqual Γ (pi (bind σ first) (bind (Telescope.lift σ) codomain))
    (pi (bind σ second) (bind (Telescope.lift σ) codomain)) T)
  let parts := (CoreDerivation.constructorView tree).piBind _ _ rfl
  have original : CoreDerivation (Statics.typed Γ (pi parts.first.code parts.second.code) T) := by
    simpa only [parts.domainBoundary, parts.codomainBoundary] using tree
  have certificate : TypeCertificate parts.first.code (bind σ second) := by
    simpa only [parts.domainBoundary] using typeAt step action σ
  let target := typeCodeStep certificate.step
  have converted : TypeCertificate parts.first.code (TypeParameter.mk parts.first.level target.next).code := by
    simpa only [target.boundary] using certificate
  have result := (piDomain (A := parts.first) (A' := ⟨parts.first.level, target.next⟩)
    (.bind parts.second) converted).equality Γ T original
  simp only [Statics.TypeBody.pi, ← parts.domainBoundary, ← parts.codomainBoundary, ← target.boundary] at result
  exact result

noncomputable def piNoAbsDomainAction {n : Nat} {first second : RawTy n} (codomain : RawTy n)
    (step : Step first second) (action : StableAction first second) :
    StableAction (piNoAbs first codomain) (piNoAbs second codomain) := by
  intro m σ Γ T tree
  change CoreDerivation (Statics.typed Γ (piNoAbs (bind σ first) (bind σ codomain)) T) at tree
  change CoreDerivation (Statics.termEqual Γ (piNoAbs (bind σ first) (bind σ codomain))
    (piNoAbs (bind σ second) (bind σ codomain)) T)
  let parts := (CoreDerivation.constructorView tree).piNoBind _ _ rfl
  have original : CoreDerivation (Statics.typed Γ (piNoAbs parts.first.code parts.second.code) T) := by
    simpa only [parts.domainBoundary, parts.codomainBoundary] using tree
  have certificate : TypeCertificate parts.first.code (bind σ second) := by
    simpa only [parts.domainBoundary] using typeAt step action σ
  let target := typeCodeStep certificate.step
  have converted : TypeCertificate parts.first.code (TypeParameter.mk parts.first.level target.next).code := by
    simpa only [target.boundary] using certificate
  have result := (piDomain (A := parts.first) (A' := ⟨parts.first.level, target.next⟩)
    (.noBind parts.second) converted).equality Γ T original
  simp only [Statics.TypeBody.pi, ← parts.domainBoundary, ← parts.codomainBoundary, ← target.boundary] at result
  exact result

noncomputable def piCodomainAction {n : Nat} (domain : RawTy n) {first second : RawTy (n + 1)}
    (step : Step first second) (action : StableAction first second) :
    StableAction (pi domain first) (pi domain second) := by
  intro m σ Γ T tree
  change CoreDerivation (Statics.typed Γ (pi (bind σ domain) (bind (Telescope.lift σ) first)) T) at tree
  change CoreDerivation (Statics.termEqual Γ (pi (bind σ domain) (bind (Telescope.lift σ) first))
    (pi (bind σ domain) (bind (Telescope.lift σ) second)) T)
  let parts := (CoreDerivation.constructorView tree).piBind _ _ rfl
  have original : CoreDerivation (Statics.typed Γ (pi parts.first.code parts.second.code) T) := by
    simpa only [parts.domainBoundary, parts.codomainBoundary] using tree
  have certificate : TypeCertificate parts.second.code (bind (Telescope.lift σ) second) := by
    exact (congrArg (fun A : RawTy (m + 1) => TypeCertificate A (bind (Telescope.lift σ) second))
      parts.codomainBoundary).mp (typeAt step action (Telescope.lift σ))
  let target := typeCodeStep certificate.step
  have converted : TypeCertificate parts.second.code (TypeParameter.mk parts.second.level target.next).code := by
    simpa only [target.boundary] using certificate
  have result := (piCodomain parts.first (B := parts.second) (B' := ⟨parts.second.level, target.next⟩)
    converted).equality Γ T original
  simp only [← parts.domainBoundary, ← parts.codomainBoundary, ← target.boundary] at result
  exact result

noncomputable def piNoAbsCodomainAction {n : Nat} (domain : RawTy n) {first second : RawTy n}
    (step : Step first second) (action : StableAction first second) :
    StableAction (piNoAbs domain first) (piNoAbs domain second) := by
  intro m σ Γ T tree
  change CoreDerivation (Statics.typed Γ (piNoAbs (bind σ domain) (bind σ first)) T) at tree
  change CoreDerivation (Statics.termEqual Γ (piNoAbs (bind σ domain) (bind σ first))
    (piNoAbs (bind σ domain) (bind σ second)) T)
  let parts := (CoreDerivation.constructorView tree).piNoBind _ _ rfl
  have original : CoreDerivation (Statics.typed Γ (piNoAbs parts.first.code parts.second.code) T) := by
    simpa only [parts.domainBoundary, parts.codomainBoundary] using tree
  have certificate : TypeCertificate parts.second.code (bind σ second) := by
    simpa only [parts.codomainBoundary] using typeAt step action σ
  let target := typeCodeStep certificate.step
  have converted : TypeCertificate parts.second.code (TypeParameter.mk parts.second.level target.next).code := by
    simpa only [target.boundary] using certificate
  have opened : TypeCertificate parts.second.weaken.code
      (TypeParameter.weaken (TypeParameter.mk parts.second.level target.next)).code := by
    change TypeCertificate (bind (Telescope.projection (S := sig) .term m) parts.second.code)
      (bind (Telescope.projection (S := sig) .term m) (TypeParameter.mk parts.second.level target.next).code)
    simpa only [parts.codomainBoundary, target.boundary] using openedTypeAt step action σ
  have result := (piNoAbsCodomain parts.first (B := parts.second) (B' := ⟨parts.second.level, target.next⟩)
    converted opened).equality Γ T original
  simp only [← parts.domainBoundary, ← parts.codomainBoundary, ← target.boundary] at result
  exact result

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.StablePreservation
