import Mettapedia.Languages.MeTTa.PureKernel.SubjectReduction
import Mettapedia.Languages.MeTTa.PureKernel.DeclarationSpec

namespace Mettapedia.Languages.MeTTa.PureKernel.Assembly

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Typing
open Mettapedia.Languages.MeTTa.PureKernel.SubjectReduction
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSpec
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics

/-- Kernel-level typed language bundle over scoped terms (`PureTm`). -/
structure TypedKernelDef where
  hasType : ∀ {n}, Ctx n → PureTm n → PureTm n → Prop
  reduces : ∀ {n}, PureTm n → PureTm n → Prop
  subject_reduction :
    ∀ {n} {Γ : Ctx n} {t t' A : PureTm n},
      hasType Γ t A → reduces t t' → hasType Γ t' A

/-- MeTTa-Pure kernel packaged as a typed language definition. -/
def mettaPureKernelTyped : TypedKernelDef where
  hasType := @HasType
  reduces := @Red
  subject_reduction := by
    intro n Γ t t' A ht hr
    exact subject_reduction (Γ := Γ) (t := t) (t' := t') (A := A) ht hr

theorem mettaPureKernel_subject_reduction
    {n : Nat} {Γ : Ctx n} {t t' A : PureTm n}
    (ht : mettaPureKernelTyped.hasType Γ t A)
    (hr : mettaPureKernelTyped.reduces t t') :
    mettaPureKernelTyped.hasType Γ t' A :=
  mettaPureKernelTyped.subject_reduction ht hr

/-- Checked non-unfolding declaration signatures packaged as a typed kernel.
This is the current assumption-free declaration-side assembly: ordered checked
specs, no declaration values, and declaration-aware one-step subject reduction. -/
def checkedNoValuesDeclKernelTyped
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none) :
    TypedKernelDef where
  hasType := @HasTypeDecl (envOfSpecs specs)
  reduces := @RedDecl (envOfSpecs specs)
  subject_reduction := by
    intro n Γ t t' A ht hr
    exact hSig.redDecl_step_preserves_type_of_all_none hNone ht hr

theorem checkedNoValuesDeclKernel_subject_reduction
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    {n : Nat} {Γ : Ctx n} {t t' A : PureTm n}
    (ht : (checkedNoValuesDeclKernelTyped hSig hNone).hasType Γ t A)
    (hr : (checkedNoValuesDeclKernelTyped hSig hNone).reduces t t') :
    (checkedNoValuesDeclKernelTyped hSig hNone).hasType Γ t' A :=
  (checkedNoValuesDeclKernelTyped hSig hNone).subject_reduction ht hr

/-- Checked declaration signatures packaged as a typed kernel under an
explicit declaration-aware Church-Rosser hypothesis.

This is the current honest value-bearing declaration-side assembly: ordered
checked specs plus declaration-aware one-step subject reduction, without yet
claiming a normalization/decision layer. -/
def checkedChurchRosserDeclKernelTyped
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hCR : DeclChurchRosser (envOfSpecs specs)) :
    TypedKernelDef where
  hasType := @HasTypeDecl (envOfSpecs specs)
  reduces := @RedDecl (envOfSpecs specs)
  subject_reduction := by
    intro n Γ t t' A ht hr
    have hWf : DeclEnvWellFormed (envOfSpecs specs) :=
      envOfSpecs_wellFormed_of_specObligations specs hSig.obligations
    exact
      DeclarationSemantics.redDecl_step_preserves_type_of_church_rosser
        (E := envOfSpecs specs)
        (hCR := hCR)
        (hWf := hWf)
        (ht := ht)
        (hr := hr)

theorem checkedChurchRosserDeclKernel_subject_reduction
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hCR : DeclChurchRosser (envOfSpecs specs))
    {n : Nat} {Γ : Ctx n} {t t' A : PureTm n}
    (ht : (checkedChurchRosserDeclKernelTyped hSig hCR).hasType Γ t A)
    (hr : (checkedChurchRosserDeclKernelTyped hSig hCR).reduces t t') :
    (checkedChurchRosserDeclKernelTyped hSig hCR).hasType Γ t' A :=
  (checkedChurchRosserDeclKernelTyped hSig hCR).subject_reduction ht hr

theorem checkedNoValuesDeclKernel_star_subject_reduction
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    {n : Nat} {Γ : Ctx n} {t u A : PureTm n}
    (ht : HasTypeDecl (envOfSpecs specs) Γ t A)
    (hs : RedStarDecl (envOfSpecs specs) t u) :
    HasTypeDecl (envOfSpecs specs) Γ u A :=
  hSig.redStarDecl_preserves_type_of_all_none hNone ht hs

theorem checkedNoValuesDeclKernel_sound_confluent_and_conversion
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none) :
    (∀ {Γ : Ctx n} {t u A : PureTm n},
      HasTypeDecl (envOfSpecs specs) Γ t A →
      RedStarDecl (envOfSpecs specs) t u →
      HasTypeDecl (envOfSpecs specs) Γ u A) ∧
    (∀ {s t₁ t₂ : PureTm n},
      RedStarDecl (envOfSpecs specs) s t₁ →
      RedStarDecl (envOfSpecs specs) s t₂ →
      ∃ u,
        RedStarDecl (envOfSpecs specs) t₁ u ∧
        RedStarDecl (envOfSpecs specs) t₂ u) ∧
    (∀ {s t : PureTm n},
      ConvDecl (envOfSpecs specs) s t →
      ∃ u,
        RedStarDecl (envOfSpecs specs) s u ∧
        RedStarDecl (envOfSpecs specs) t u) ∧
    (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
      ConvDecl (envOfSpecs specs) (.pi A B) (.pi A' B') →
        ConvDecl (envOfSpecs specs) A A' ∧
        ConvDecl (envOfSpecs specs) B B') ∧
    (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
      ConvDecl (envOfSpecs specs) (.sigma A B) (.sigma A' B') →
        ConvDecl (envOfSpecs specs) A A' ∧
        ConvDecl (envOfSpecs specs) B B') ∧
    (∀ {A B : PureTm n} {w : DefEqDeclWitness (envOfSpecs specs) A B},
      hSig.defEqByNormalizationDeclOfAllNone? hNone A B = some w →
      ConvDecl (envOfSpecs specs) A B) ∧
    (∀ {A B : PureTm n},
      hSig.defEqByNormalizationDeclOfAllNone? hNone A B ≠ none →
      ConvDecl (envOfSpecs specs) A B) := by
  exact hSig.decl_sound_confluent_and_conversion_of_all_none hNone

theorem checkedChurchRosserDeclKernel_sound_confluent_and_injective
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hCR : DeclChurchRosser (envOfSpecs specs)) :
    (∀ {Γ : Ctx n} {t u A : PureTm n},
      HasTypeDecl (envOfSpecs specs) Γ t A →
      RedStarDecl (envOfSpecs specs) t u →
      HasTypeDecl (envOfSpecs specs) Γ u A) ∧
    (∀ {s t₁ t₂ : PureTm n},
      RedStarDecl (envOfSpecs specs) s t₁ →
      RedStarDecl (envOfSpecs specs) s t₂ →
      ∃ u,
        RedStarDecl (envOfSpecs specs) t₁ u ∧
        RedStarDecl (envOfSpecs specs) t₂ u) ∧
    (∀ {s t : PureTm n},
      ConvDecl (envOfSpecs specs) s t →
      ∃ u,
        RedStarDecl (envOfSpecs specs) s u ∧
        RedStarDecl (envOfSpecs specs) t u) ∧
    (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
      ConvDecl (envOfSpecs specs) (.pi A B) (.pi A' B') →
        ConvDecl (envOfSpecs specs) A A' ∧
        ConvDecl (envOfSpecs specs) B B') ∧
    (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
      ConvDecl (envOfSpecs specs) (.sigma A B) (.sigma A' B') →
        ConvDecl (envOfSpecs specs) A A' ∧
        ConvDecl (envOfSpecs specs) B B') := by
  exact hSig.decl_sound_confluent_and_injectivity_of_church_rosser hCR

theorem checkedChurchRosserDeclKernel_sound_confluent_and_injective_of_all_none
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none) :
    (∀ {Γ : Ctx n} {t u A : PureTm n},
      HasTypeDecl (envOfSpecs specs) Γ t A →
      RedStarDecl (envOfSpecs specs) t u →
      HasTypeDecl (envOfSpecs specs) Γ u A) ∧
    (∀ {s t₁ t₂ : PureTm n},
      RedStarDecl (envOfSpecs specs) s t₁ →
      RedStarDecl (envOfSpecs specs) s t₂ →
      ∃ u,
        RedStarDecl (envOfSpecs specs) t₁ u ∧
        RedStarDecl (envOfSpecs specs) t₂ u) ∧
    (∀ {s t : PureTm n},
      ConvDecl (envOfSpecs specs) s t →
      ∃ u,
        RedStarDecl (envOfSpecs specs) s u ∧
        RedStarDecl (envOfSpecs specs) t u) ∧
    (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
      ConvDecl (envOfSpecs specs) (.pi A B) (.pi A' B') →
        ConvDecl (envOfSpecs specs) A A' ∧
        ConvDecl (envOfSpecs specs) B B') ∧
    (∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
      ConvDecl (envOfSpecs specs) (.sigma A B) (.sigma A' B') →
        ConvDecl (envOfSpecs specs) A A' ∧
        ConvDecl (envOfSpecs specs) B B') := by
  exact
    checkedChurchRosserDeclKernel_sound_confluent_and_injective
      hSig
      (hSig.declChurchRosser_of_all_none hNone)

/-- Packaged assumption-free declaration-side boundary for ordered checked
non-unfolding signatures.

This is the strongest fully discharged declaration-aware interface currently
available: typed kernel surface, star-level subject reduction, confluence via
common reducts, Pi/Sigma injectivity, and normalization-backed conversion
soundness. It is intentionally restricted to the all-none slice. -/
structure CheckedNoValuesDeclKernelBoundary
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none) where
  typed : TypedKernelDef
  typed_eq : typed = checkedNoValuesDeclKernelTyped hSig hNone
  starSubjectReduction :
    ∀ {Γ : Ctx n} {t u A : PureTm n},
      HasTypeDecl (envOfSpecs specs) Γ t A →
      RedStarDecl (envOfSpecs specs) t u →
      HasTypeDecl (envOfSpecs specs) Γ u A
  confluence :
    ∀ {s t₁ t₂ : PureTm n},
      RedStarDecl (envOfSpecs specs) s t₁ →
      RedStarDecl (envOfSpecs specs) s t₂ →
      ∃ u,
        RedStarDecl (envOfSpecs specs) t₁ u ∧
        RedStarDecl (envOfSpecs specs) t₂ u
  commonReduct :
    ∀ {s t : PureTm n},
      ConvDecl (envOfSpecs specs) s t →
      ∃ u,
        RedStarDecl (envOfSpecs specs) s u ∧
        RedStarDecl (envOfSpecs specs) t u
  piInjective :
    ∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
      ConvDecl (envOfSpecs specs) (.pi A B) (.pi A' B') →
      ConvDecl (envOfSpecs specs) A A' ∧
        ConvDecl (envOfSpecs specs) B B'
  sigmaInjective :
    ∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
      ConvDecl (envOfSpecs specs) (.sigma A B) (.sigma A' B') →
      ConvDecl (envOfSpecs specs) A A' ∧
        ConvDecl (envOfSpecs specs) B B'
  defEqSound :
    ∀ {A B : PureTm n} {w : DefEqDeclWitness (envOfSpecs specs) A B},
      hSig.defEqByNormalizationDeclOfAllNone? hNone A B = some w →
      ConvDecl (envOfSpecs specs) A B
  defEqNeNone :
    ∀ {A B : PureTm n},
      hSig.defEqByNormalizationDeclOfAllNone? hNone A B ≠ none →
      ConvDecl (envOfSpecs specs) A B

/-- Packaged declaration-side boundary for ordered checked signatures under an
explicit declaration-aware Church-Rosser hypothesis.

This is the current strongest generic value-bearing interface we can state
honestly: typed kernel surface, star-level subject reduction, confluence via
common reducts, and Pi/Sigma injectivity. Normalization-backed conversion is
intentionally not bundled here, because that layer is only discharged on the
all-none slice at present. -/
structure CheckedChurchRosserDeclKernelBoundary
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hCR : DeclChurchRosser (envOfSpecs specs)) where
  typed : TypedKernelDef
  typed_eq : typed = checkedChurchRosserDeclKernelTyped hSig hCR
  starSubjectReduction :
    ∀ {Γ : Ctx n} {t u A : PureTm n},
      HasTypeDecl (envOfSpecs specs) Γ t A →
      RedStarDecl (envOfSpecs specs) t u →
      HasTypeDecl (envOfSpecs specs) Γ u A
  confluence :
    ∀ {s t₁ t₂ : PureTm n},
      RedStarDecl (envOfSpecs specs) s t₁ →
      RedStarDecl (envOfSpecs specs) s t₂ →
      ∃ u,
        RedStarDecl (envOfSpecs specs) t₁ u ∧
        RedStarDecl (envOfSpecs specs) t₂ u
  commonReduct :
    ∀ {s t : PureTm n},
      ConvDecl (envOfSpecs specs) s t →
      ∃ u,
        RedStarDecl (envOfSpecs specs) s u ∧
        RedStarDecl (envOfSpecs specs) t u
  piInjective :
    ∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
      ConvDecl (envOfSpecs specs) (.pi A B) (.pi A' B') →
      ConvDecl (envOfSpecs specs) A A' ∧
        ConvDecl (envOfSpecs specs) B B'
  sigmaInjective :
    ∀ {A A' : PureTm n} {B B' : PureTm (n + 1)},
      ConvDecl (envOfSpecs specs) (.sigma A B) (.sigma A' B') →
      ConvDecl (envOfSpecs specs) A A' ∧
        ConvDecl (envOfSpecs specs) B B'

/-- Assemble the value-bearing declaration kernel boundary directly from the
checked spec-level Church-Rosser package. This keeps the typed frontier synced
with the lower declaration package instead of re-deriving the same fields
piecemeal. -/
def checkedChurchRosserDeclKernelBoundaryOfPackage
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hPkg : DeclSpecChurchRosserPackage specs) :
    CheckedChurchRosserDeclKernelBoundary hSig hPkg.declChurchRosser := by
  exact
    { typed := checkedChurchRosserDeclKernelTyped hSig hPkg.declChurchRosser
      typed_eq := rfl
      starSubjectReduction := hPkg.starPreservation
      confluence := hPkg.starConfluence
      commonReduct := hPkg.declChurchRosser
      piInjective := hPkg.piInjective
      sigmaInjective := hPkg.sigmaInjective }

/-- Assemble the strongest assumption-free declaration kernel boundary directly
from the checked spec-level all-none package. This packages the normalization
soundness layer together with the declaration-aware SR/confluence spine. -/
def checkedNoValuesDeclKernelBoundaryOfPackage
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hPkg : DeclSpecAndNoValuesPackage specs hNone) :
    CheckedNoValuesDeclKernelBoundary hSig hNone := by
  exact
    { typed := checkedNoValuesDeclKernelTyped hSig hNone
      typed_eq := rfl
      starSubjectReduction := hPkg.asChurchRosser.starPreservation
      confluence := hPkg.asChurchRosser.starConfluence
      commonReduct := hPkg.asChurchRosser.declChurchRosser
      piInjective := hPkg.asChurchRosser.piInjective
      sigmaInjective := hPkg.asChurchRosser.sigmaInjective
      defEqSound := hPkg.normalization.1
      defEqNeNone := hPkg.normalization.2 }

def checkedChurchRosserDeclKernelBoundary
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hCR : DeclChurchRosser (envOfSpecs specs)) :
    CheckedChurchRosserDeclKernelBoundary hSig hCR := by
  simpa [checkedChurchRosserDeclKernelBoundaryOfPackage,
    DeclSpecChurchRosserPackage.declChurchRosser] using
    checkedChurchRosserDeclKernelBoundaryOfPackage
      hSig
      (hSig.declSpecChurchRosserPackage_of_church_rosser hCR)

def checkedNoValuesDeclKernelBoundary
    {specs : List DeclSpec}
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none) :
    CheckedNoValuesDeclKernelBoundary hSig hNone := by
  exact
    checkedNoValuesDeclKernelBoundaryOfPackage
      hSig hNone
      (hSig.declSpecAndNoValuesPackage_of_all_none hNone)

/-- Recover the spec-level Church-Rosser package from the assembled
value-bearing declaration kernel boundary. This is the converse view to
`checkedChurchRosserDeclKernelBoundaryOfPackage`: the assembly layer adds no
new metatheory, it simply re-exposes the same SR/confluence interface. -/
def CheckedChurchRosserDeclKernelBoundary.toDeclSpecChurchRosserPackage
    {specs : List DeclSpec}
    {hSig : SignatureWellFormed specs}
    {hCR : DeclChurchRosser (envOfSpecs specs)}
    (hBoundary : CheckedChurchRosserDeclKernelBoundary hSig hCR) :
    DeclSpecChurchRosserPackage specs := by
  refine ⟨?_, hBoundary.starSubjectReduction, hBoundary.confluence,
    hBoundary.commonReduct, hBoundary.piInjective, hBoundary.sigmaInjective⟩
  exact envOfSpecs_wellFormed_of_specObligations specs hSig.obligations

/-- Recover the strongest assumption-free spec package from the assembled
all-none declaration kernel boundary. This keeps the normalization-backed
conversion service available to later interface theorems without re-proving
it from the raw fields. -/
def CheckedNoValuesDeclKernelBoundary.toDeclSpecAndNoValuesPackage
    {specs : List DeclSpec}
    {hSig : SignatureWellFormed specs}
    {hNone : ∀ s ∈ specs, s.value? = none}
    (hBoundary : CheckedNoValuesDeclKernelBoundary hSig hNone) :
    DeclSpecAndNoValuesPackage specs hNone := by
  exact
    ⟨ ⟨ envOfSpecs_wellFormed_of_specObligations specs hSig.obligations
      , hBoundary.starSubjectReduction
      , hBoundary.confluence
      , hBoundary.commonReduct
      , hBoundary.piInjective
      , hBoundary.sigmaInjective
      ⟩
    , ⟨hBoundary.defEqSound, hBoundary.defEqNeNone⟩
    ⟩

/-- Forget the normalization-specific fields on the all-none slice and reuse
the resulting package through the generic Church-Rosser boundary interface.

This records the real architectural relation between the two frontiers: the
assumption-free all-none boundary is stronger, and therefore refines the
current value-bearing Church-Rosser boundary rather than competing with it. -/
def CheckedNoValuesDeclKernelBoundary.asChurchRosserBoundary
    {specs : List DeclSpec}
    {hSig : SignatureWellFormed specs}
    {hNone : ∀ s ∈ specs, s.value? = none}
    (hBoundary : CheckedNoValuesDeclKernelBoundary hSig hNone) :
    CheckedChurchRosserDeclKernelBoundary
      hSig
      (hSig.declChurchRosser_of_all_none hNone) where
  typed :=
    checkedChurchRosserDeclKernelTyped
      hSig
      (hSig.declChurchRosser_of_all_none hNone)
  typed_eq := rfl
  starSubjectReduction := hBoundary.starSubjectReduction
  confluence := hBoundary.confluence
  commonReduct := hBoundary.commonReduct
  piInjective := hBoundary.piInjective
  sigmaInjective := hBoundary.sigmaInjective

end Mettapedia.Languages.MeTTa.PureKernel.Assembly
