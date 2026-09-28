import Mettapedia.Languages.Agda.Structural.AdministrativeConstructorGeneration
import Mettapedia.Languages.Agda.Structural.AdministrativeTypePreservation

/-!
# Native preservation under lambda and Pi binders

The constructors act on arbitrary converted typing histories. They use native
lambda/Pi congruence and the original conversion chains. Nonbinding bodies
consume explicit certificates for their opened syntax in the extended context;
no strengthening operation or Pi injectivity is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Preservation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Statics (RawTm TypeParameter TypeBody)

noncomputable def lambdaBind {n : Nat} {first second : RawTm (n + 1)}
    (certificate : TermCertificate first second) : TermCertificate (lam first) (lam second) where
  step := by
    change CompatibleDerivations.Step Root
      (.op Op.lam (.cons first .nil)) (.op Op.lam (.cons second .nil))
    apply CompatibleDerivations.Step.congr (R := Root) Op.lam
    apply CompatibleDerivations.ArgsStep.head
    exact certificate.step
  equality Γ A tree := by
    let parts := CoreDerivation.lambdaParts (body := .bind first) tree
    apply parts.conversions.termEquality
    exact administrativeOperations.lambdaCongruence (first := .bind first) (second := .bind second)
      parts.domainFormed parts.codomainFormed parts.bodyTyped (certificate.typing parts.bodyTyped)
      (certificate.equality (Γ.snoc parts.domain.code) parts.codomain.open.code parts.bodyTyped)

noncomputable def lambdaNoAbs {n : Nat} {first second : RawTm n}
    (certificate : TermCertificate first second)
    (opened : TermCertificate (bind (Telescope.projection (S := sig) .term n) first)
      (bind (Telescope.projection (S := sig) .term n) second)) :
    TermCertificate (lamNoAbs first) (lamNoAbs second) where
  step := by
    change CompatibleDerivations.Step Root
      (.op Op.lamNoAbs (.cons first .nil)) (.op Op.lamNoAbs (.cons second .nil))
    apply CompatibleDerivations.Step.congr (R := Root) Op.lamNoAbs
    apply CompatibleDerivations.ArgsStep.head
    exact certificate.step
  equality Γ A tree := by
    let parts := CoreDerivation.lambdaParts (body := .noBind first) tree
    apply parts.conversions.termEquality
    exact administrativeOperations.lambdaCongruence (first := .noBind first) (second := .noBind second)
      parts.domainFormed parts.codomainFormed parts.bodyTyped (opened.typing parts.bodyTyped)
      (opened.equality (Γ.snoc parts.domain.code) parts.codomain.open.code parts.bodyTyped)

noncomputable def piDomain {n : Nat} {A A' : TypeParameter n} (B : TypeBody n)
    (certificate : TypeCertificate A.code A'.code) : TermCertificate (B.pi A) (B.pi A') where
  step := by
    cases B with
    | bind body =>
        apply CompatibleDerivations.Step.congr (R := Root) Op.pi
        apply CompatibleDerivations.ArgsStep.head
        exact certificate.step
    | noBind body =>
        apply CompatibleDerivations.Step.congr (R := Root) Op.piNoAbs
        apply CompatibleDerivations.ArgsStep.head
        exact certificate.step
  equality Γ _ tree := by
    let parts := CoreDerivation.piTypingParts tree
    apply parts.conversions.termEquality
    exact Derivation.core (.piCongruence Γ A A' B B)
      (consEvidence CoreDerivation parts.domainFormed
        (consEvidence CoreDerivation (certificate.equality Γ parts.domainFormed)
          (consEvidence CoreDerivation parts.codomainFormed.typeReflexivity (noEvidence CoreDerivation))))

noncomputable def piCodomain {n : Nat} (A : TypeParameter n) {B B' : TypeParameter (n + 1)}
    (certificate : TypeCertificate B.code B'.code) : TermCertificate (pi A.code B.code) (pi A.code B'.code) where
  step := by
    apply CompatibleDerivations.Step.congr (R := Root) Op.pi
    apply CompatibleDerivations.ArgsStep.tail
    apply CompatibleDerivations.ArgsStep.head
    exact certificate.step
  equality Γ _ tree := by
    let parts := CoreDerivation.piTypingParts (B := .bind B) tree
    apply parts.conversions.termEquality
    exact Derivation.core (.piCongruence Γ A A (.bind B) (.bind B'))
      (consEvidence CoreDerivation parts.domainFormed
        (consEvidence CoreDerivation parts.domainFormed.typeReflexivity
          (consEvidence CoreDerivation (certificate.equality (Γ.snoc A.code) parts.codomainFormed)
            (noEvidence CoreDerivation))))

noncomputable def piNoAbsCodomain {n : Nat} (A : TypeParameter n) {B B' : TypeParameter n}
    (certificate : TypeCertificate B.code B'.code)
    (opened : TypeCertificate B.weaken.code B'.weaken.code) :
    TermCertificate (piNoAbs A.code B.code) (piNoAbs A.code B'.code) where
  step := by
    apply CompatibleDerivations.Step.congr (R := Root) Op.piNoAbs
    apply CompatibleDerivations.ArgsStep.tail
    apply CompatibleDerivations.ArgsStep.head
    exact certificate.step
  equality Γ _ tree := by
    let parts := CoreDerivation.piTypingParts (B := .noBind B) tree
    apply parts.conversions.termEquality
    exact Derivation.core (.piCongruence Γ A A (.noBind B) (.noBind B'))
      (consEvidence CoreDerivation parts.domainFormed
        (consEvidence CoreDerivation parts.domainFormed.typeReflexivity
          (consEvidence CoreDerivation (opened.equality (Γ.snoc A.code) parts.codomainFormed)
            (noEvidence CoreDerivation))))

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Preservation
