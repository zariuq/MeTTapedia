import Mettapedia.GSLT.LanguageDef.NIKMetalogic

/-!
# Lean as a NIK guest: Lean4Lean/Lean4Less integration boundary

This module is a theorem-bearing integration skeleton.  It states the exact
objects and commuting laws required to turn a Lean-like kernel into a NIK
guest while keeping equality-policy translation separate from proof checking.
It does not claim that the external Lean4Lean or Lean4Less implementations
have already discharged these laws.

The split is deliberate:

* a native proof system retains Lean expressions as proof objects;
* a computing kernel decides the independently stated declaration judgment;
* exact NIK parity follows fibrewise, without decoding or tag erasure;
* proof irrelevance, K-like reduction, and quotients form an explicit equality
  profile package rather than becoming properties of NIK;
* a Lean-to-Lean-minus translation must insert explicit transports and prove
  judgment preservation;
* universe levels cross the boundary through an order embedding.
-/

namespace Mettapedia.Languages.Lean.Lean4LessNIKGuest

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic

universe uExpr uDecl uLevel

/-! ## Equality profile packages -/

/-- Definitional-equality features relevant to the present Lean4Less
translation boundary. -/
inductive EqualityFeature where
  | proofIrrelevance
  | kLikeReduction
  | quotients
  deriving DecidableEq, Repr

/-- A named package of kernel equality features. -/
structure EqualityProfile where
  name : String
  enabled : Finset EqualityFeature

/-- The selected ordinary Lean profile.  This is a profile description, not
an implementation of Lean's full conversion algorithm. -/
def leanProfile : EqualityProfile where
  name := "lean"
  enabled := {.proofIrrelevance, .kLikeReduction, .quotients}

/-- The currently relevant Lean-minus target eliminates definitional proof
irrelevance and K-like reduction while retaining quotient support explicitly. -/
def leanMinusProfile : EqualityProfile where
  name := "lean-minus-pi-klr"
  enabled := {.quotients}

/-- Profile extension is feature inclusion.  It orders equality packages,
not logical strength or consistency strength. -/
def EqualityProfile.Extends (stronger weaker : EqualityProfile) : Prop :=
  weaker.enabled ⊆ stronger.enabled

theorem lean_extends_leanMinus : leanProfile.Extends leanMinusProfile := by
  intro feature member
  simp [leanMinusProfile] at member
  subst feature
  simp [leanProfile]

/-- The extension is strict: Lean-minus does not silently regain proof
irrelevance or K-like reduction. -/
theorem leanMinus_does_not_extend_lean :
    ¬ leanMinusProfile.Extends leanProfile := by
  intro hExtends
  have impossible := hExtends (by simp [leanProfile] :
    EqualityFeature.proofIrrelevance ∈ leanProfile.enabled)
  simp [leanMinusProfile] at impossible

theorem equality_profiles_are_distinct : leanProfile ≠ leanMinusProfile := by
  intro equal
  have sameFeatures := congrArg EqualityProfile.enabled equal
  have proofIrrelevanceInMinus :
      EqualityFeature.proofIrrelevance ∈ leanMinusProfile.enabled := by
    rw [← sameFeatures]
    simp [leanProfile]
  simp [leanMinusProfile] at proofIrrelevanceInMinus

/-! ## The independently stated guest judgment -/

/-- The minimal semantic contract extracted from a Lean-like kernel.  The
judgment is stated before the Boolean checker, and conversion is separately
decided. -/
structure GuestKernelSpec where
  Expr : Type uExpr
  Declaration : Type uDecl
  Converts : Expr → Expr → Prop
  judges : Expr → Declaration → Prop
  decideConversion : Expr → Expr → Bool
  decideJudgment : Declaration → Expr → Bool
  conversion_correct : ∀ left right,
    decideConversion left right = true ↔ Converts left right
  judgment_correct : ∀ declaration proof,
    decideJudgment declaration proof = true ↔ judges proof declaration
  /-- Nondegeneracy: some submitted proof/declaration pair is rejected. -/
  rejects : ∃ declaration proof,
    decideJudgment declaration proof = false

namespace GuestKernelSpec

/-- Lean terms are the guest's native proof objects; declarations are claims. -/
def proofSystem (spec : GuestKernelSpec) :
    NativeProofSystem spec.Declaration where
  ProofObject := spec.Expr
  Judges := spec.judges

/-- The kernel recomputes the native judgment directly. -/
def nativeKernel (spec : GuestKernelSpec) :
    NativeProofKernel spec.proofSystem where
  decide := spec.decideJudgment
  correct := spec.judgment_correct

/-- Conversion is exposed as a computing sub-judgment, not as certificate
content. -/
def decidedConversion (spec : GuestKernelSpec) :
    DecidedRelation spec.Expr spec.Converts where
  decide := spec.decideConversion
  correct := spec.conversion_correct

/-- A computing Lean guest obtains exact proof-fibre parity automatically:
the primary certificate is the native proof term itself. -/
def exactParity (spec : GuestKernelSpec) :
    CertificateEquivalence spec.nativeKernel.toChecker spec.proofSystem :=
  spec.nativeKernel.certificateEquivalence

/-- The resulting NIK checker is exact for inhabitation of the native Lean
proof fibre. -/
theorem authority (spec : GuestKernelSpec) :
    spec.nativeKernel.toChecker.Authority
      (fun declaration => Nonempty (spec.proofSystem.ProofFibre declaration)) :=
  spec.nativeKernel.authority

/-- Exact parity retains proof identity; no decode-only weakening is used. -/
def accepted_fibre_equiv_native_fibre (spec : GuestKernelSpec)
    (declaration : spec.Declaration) :
    AcceptedCertificateFibre spec.nativeKernel.toChecker declaration ≃
      spec.proofSystem.ProofFibre declaration :=
  (spec.exactParity).fibreEquiv declaration

end GuestKernelSpec

/-! ## Profile translation and explicit casts -/

/-- A typed translation between two equality profiles over the same
declaration language.  `translate` may insert explicit transports; the
preservation theorem is the actual adequacy obligation. -/
structure ProfileTranslation
    (source target : EqualityProfile)
    (sourceKernel targetKernel : GuestKernelSpec) where
  translate : sourceKernel.Expr → targetKernel.Expr
  declarationMap : sourceKernel.Declaration → targetKernel.Declaration
  preservesJudgment : ∀ {proof declaration},
    sourceKernel.judges proof declaration →
      targetKernel.judges (translate proof) (declarationMap declaration)
  sourceExtendsTarget : source.Extends target

namespace ProfileTranslation

/-- A verified profile translation maps every accepted native proof to an
accepted target proof, with target conversion recomputed by the target
kernel. -/
theorem mapsAccepted
    {source target : EqualityProfile}
    {sourceKernel targetKernel : GuestKernelSpec}
    (translation : ProfileTranslation source target sourceKernel targetKernel)
    {declaration : sourceKernel.Declaration}
    (proof : sourceKernel.proofSystem.ProofFibre declaration) :
    targetKernel.judges (translation.translate proof.1)
      (translation.declarationMap declaration) :=
  translation.preservesJudgment proof.2

end ProfileTranslation

/-- Exact shape of the external Lean4Less obligation: ordinary Lean terms are
translated into the weaker PI/KLR-eliminated profile, and every native
judgment is preserved by explicit transports. -/
abbrev LeanToLeanMinusTranslation
    (leanKernel leanMinusKernel : GuestKernelSpec) :=
  ProfileTranslation leanProfile leanMinusProfile leanKernel leanMinusKernel

/-! ## Universe transport -/

/-- Universe levels cross an authority/profile boundary through an order
embedding.  Monotonicity alone would permit distinct levels to collapse; the
reflection law rules that out. -/
structure UniverseEmbedding
    (sourceLevel targetLevel : Type uLevel)
    [Preorder sourceLevel] [Preorder targetLevel] where
  map : sourceLevel → targetLevel
  preserves : ∀ {lower upper}, lower ≤ upper → map lower ≤ map upper
  reflects : ∀ {lower upper}, map lower ≤ map upper → lower ≤ upper

namespace UniverseEmbedding

theorem injective
    {sourceLevel targetLevel : Type uLevel}
    [PartialOrder sourceLevel] [PartialOrder targetLevel]
    (embedding : UniverseEmbedding sourceLevel targetLevel) :
    Function.Injective embedding.map := by
  intro left right equal
  apply le_antisymm
  · exact embedding.reflects (by rw [equal])
  · exact embedding.reflects (by rw [equal])

/-- Identity is a non-collapsing universe map and supplies the initial
statement shape when source and target share Lean's level algebra. -/
def identity (Level : Type uLevel) [Preorder Level] :
    UniverseEmbedding Level Level where
  map := _root_.id
  preserves := fun related => related
  reflects := fun related => related

end UniverseEmbedding

/-! ## Complete bounded integration package -/

/-- Everything needed for a Lean-as-guest integration claim.  The structure
is intentionally uninhabited here: a real instance must import or re-present
the external kernel, prove its Boolean correctness, supply the PI/KLR
translation, and map universes without collapse. -/
structure LeanAsGuestPackage where
  leanKernel : GuestKernelSpec
  leanMinusKernel : GuestKernelSpec
  translation : LeanToLeanMinusTranslation leanKernel leanMinusKernel
  /-- Lean4Less translates between two equality policies over the same
  expression and declaration syntax.  These equalities prevent the
  nontriviality witness below from being discharged merely because the two
  carriers happened to have different types. -/
  expressionCarrier : leanMinusKernel.Expr = leanKernel.Expr
  declarationCarrier : leanMinusKernel.Declaration = leanKernel.Declaration
  Level : Type uLevel
  levelOrder : PartialOrder Level
  universes : @UniverseEmbedding Level Level levelOrder.toPreorder
    levelOrder.toPreorder
  /-- The profile translation has a real source term whose representation
  changes; this blocks an identity-translation masquerade. -/
  translationNontrivial : ∃ proof,
    cast expressionCarrier (translation.translate proof) ≠ proof

/-- A completed package immediately supplies both exact NIK parity squares. -/
theorem package_has_exact_parity (package : LeanAsGuestPackage) :
    Nonempty
        (CertificateEquivalence package.leanKernel.nativeKernel.toChecker
          package.leanKernel.proofSystem) ∧
      Nonempty
        (CertificateEquivalence package.leanMinusKernel.nativeKernel.toChecker
          package.leanMinusKernel.proofSystem) :=
  ⟨⟨package.leanKernel.exactParity⟩,
    ⟨package.leanMinusKernel.exactParity⟩⟩

/-- Equality-profile difference is orthogonal to NIK proof-fibre parity: the
two exact guest kernels may coexist without changing the NIK waist. -/
theorem profile_change_does_not_change_parity_standard
    (package : LeanAsGuestPackage) :
    leanProfile ≠ leanMinusProfile ∧
      Nonempty
        (CertificateEquivalence package.leanKernel.nativeKernel.toChecker
          package.leanKernel.proofSystem) ∧
      Nonempty
        (CertificateEquivalence package.leanMinusKernel.nativeKernel.toChecker
          package.leanMinusKernel.proofSystem) :=
  ⟨equality_profiles_are_distinct,
    (package_has_exact_parity package).1,
    (package_has_exact_parity package).2⟩

end Mettapedia.Languages.Lean.Lean4LessNIKGuest
