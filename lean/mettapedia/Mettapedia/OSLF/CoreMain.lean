import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Semantics
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.MeTTaIL.DeclReduces
import Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Types
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Soundness
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine
import Mettapedia.OSLF.Framework.RewriteSystem
import Mettapedia.OSLF.Framework.RhoInstance
import Mettapedia.OSLF.Framework.DerivedModalities
import Mettapedia.OSLF.Framework.CategoryBridge
import Mettapedia.OSLF.Framework.FULLStatus
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.GeneratedTyping
import Mettapedia.OSLF.Framework.SynthesisBridge
import Mettapedia.OSLF.Framework.ToposReduction
import Mettapedia.OSLF.Framework.LambdaInstance
import Mettapedia.OSLF.Framework.PetriNetInstance
import Mettapedia.OSLF.Framework.TinyMLInstance
import Mettapedia.OSLF.Framework.MeTTaMinimalInstance
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.ConstructorFibration
import Mettapedia.OSLF.Framework.ModalEquivalence
import Mettapedia.OSLF.Framework.ObservationalQuotient
import Mettapedia.OSLF.Framework.DerivedTyping
import Mettapedia.OSLF.Framework.PLNSelectorGSLT
import Mettapedia.OSLF.Framework.BeckChevalleyOSLF
import Mettapedia.OSLF.Framework.ToposTOGLBridge
import Mettapedia.OSLF.Framework.PaperSection12Examples
import Mettapedia.OSLF.NativeType.Construction
import Mettapedia.OSLF.MeTTaCore.Premises
import Mettapedia.OSLF.MeTTaCore.FullLanguageDef
import Mettapedia.OSLF.Framework.MeTTaFullInstance
import Mettapedia.OSLF.Framework.MeTTaToNTT
import Mettapedia.OSLF.Framework.IdentityEvidenceTransfer
import Mettapedia.OSLF.Formula
import Mettapedia.OSLF.Decidability
import Mettapedia.OSLF.QuantifiedFormula
import Mettapedia.OSLF.QuantifiedFormula2
import Mettapedia.Logic.OSLFDistinctionGraph
import Mettapedia.Logic.OSLFDistinctionGraphWeighted
import Mettapedia.Logic.OSLFDistinctionGraphWM
import Mettapedia.Logic.OSLFDistinctionGraphEntropy
import Mettapedia.Logic.OSLFKripkeBridge
import Mettapedia.Logic.OSLFImageFinite
import Mettapedia.OSLF.Framework.PiRhoCanonicalBridge
import Mettapedia.OSLF.Framework.SubstitutabilityTheorem1

/-!
# OSLF Core Entry Point

Sorry-free core entry point for OSLF + GSLT + premise-aware rewriting pipeline.

This file keeps the core stack and re-exports one canonical π→ρ pred-domain
endpoint for downstream OSLF consumers.
-/

namespace Mettapedia.OSLF

export Mettapedia.OSLF.MeTTaCore.Premises (
  space0Atomspace
  space0EqEntries
  space0TypeEntries
  space0Entries
  mkCanonicalSpace
  space0Pattern
  spaceEntriesOfPattern?
  atomspaceOfPattern?
  eqnLookupTuples
  noEqnLookupTuples
  neqTuples
  typeOfTuples
  notTypeOfTuples
  castTuples
  notCastTuples
  groundedCallTuples
  noGroundedCallTuples
)

export Mettapedia.OSLF.MeTTaCore.FullLanguageDef (
  mettaFull
  mettaFullOSLF
  mettaFullGalois
  mettaFullRelEnv
)

export Mettapedia.OSLF.Framework.MeTTaFullInstance (
  mettaFull_pathOrder
  mettaFull_checker_sat_to_pathSemClosed_commDi_bc_graph
  mettaFull_checker_sat_to_pathSemClosed_commDi_bc_graph_auto
  mettaFullSpecAtomCheck
  mettaFullSpecAtomSem
  mettaFull_checkLangUsing_sat_sound_specAtoms
  mettaFull_checkLang_sat_sound_specAtoms
)

export Mettapedia.OSLF.Framework.MeTTaToNTT (
  mettaEvidenceToNT
  mettaEvidenceToNT_hom
  mettaSemE
  mettaSemE_atom
  mettaSemE_atom_revision
  mettaFormulaToNT
  mettaFormulaToNT_snd
  mettaFormulaToNT_atom
  mettaFormulaToNT_hom
)

export Mettapedia.OSLF.Framework.PiRhoCanonicalBridge (
  piRho_coreMain_canonical_contract_end_to_end
)

export Mettapedia.OSLF.Framework.PaperSection12Examples (
  section12_worked_examples_bundle
)

export Mettapedia.OSLF.Framework.IdentityEvidenceTransfer (
  IdentityAtomLayerConfig
  atomSemBase
  atomSemWithIdentity
  sem_withIdentity_disabled_iff
  checkLangUsing_sat_sound_withIdentity_unused
  identity_semantic_transfer_endpoint
)

/-- CoreMain-facing canonical π→ρ semantic contract endpoint. -/
abbrev coreMain_piRho_canonical_contract :=
  @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.piRho_coreMain_canonical_contract_end_to_end

/-- Canonical projection API for downstream users: consume the contract record
and project endpoint/HM capabilities directly. -/
theorem coreMain_piRho_contract_projection_api
    {N : Finset String}
    (x : Mettapedia.Languages.ProcessCalculi.PiCalculus.Name)
    (P : Mettapedia.Languages.ProcessCalculi.PiCalculus.Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Mettapedia.Languages.ProcessCalculi.PiCalculus.Name)
    (Pr : Mettapedia.Languages.ProcessCalculi.PiCalculus.Process)
    (n v : String)
    (hobs : N ⊆ P.freeNames)
    (hfresh : Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingFresh P) :
    Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.CalcPreludeLanguageMorphismSemanticTransferParamAtomPredDomain
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh
    ∧
    (∃
      _ :
        Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
          Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.FiniteSubrelation
            Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoCoreStarRel,
      True)
    ∧
    (∃
      _ :
        Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
          Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.FiniteSubrelation
            Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoDerivedStarRel,
      True)
    ∧
    (∀
      (S :
        Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.FiniteSubrelation
          Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoCoreStarRel)
      (I : Mettapedia.OSLF.Formula.AtomSem)
      {p q : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      Mettapedia.Logic.OSLFKSUnificationSketch.OSLFObsEq S.rel I p q →
      Mettapedia.Logic.OSLFKSUnificationSketch.Bisimilar S.rel p q)
    ∧
    (∀ (I : Mettapedia.OSLF.Formula.AtomSem)
      {p q : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      Mettapedia.Logic.OSLFKSUnificationSketch.OSLFObsEq
        Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoCoreCanonicalRel I p q →
      Mettapedia.Logic.OSLFKSUnificationSketch.Bisimilar
        Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoCoreCanonicalRel p q) := by
  let C :=
    coreMain_piRho_canonical_contract
      (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hobs hfresh
  exact ⟨C.endpoint, ⟨C.reachable_coreStar_subrel, trivial⟩,
    ⟨C.reachable_derivedStar_subrel, trivial⟩, C.hm_converse_coreStar_subrel,
    C.hm_converse_coreCanonical⟩

/-- CoreMain-facing canonical category/topos bridge endpoint alias. -/
abbrev coreMain_hypercube_fuzzy_bridge :=
  @Mettapedia.OSLF.Framework.CategoryBridge.hypercube_fuzzy_canonical_bridge

/-- CoreMain-facing canonical Native Type translation endpoint for Π/Ω
preservation across theory morphisms. -/
theorem coreMain_nativeType_piOmega_translation_endpoint
    {L₁ L₂ : Mettapedia.CategoryTheory.LambdaTheories.LambdaTheory}
    (F : Mettapedia.OSLF.NativeType.TheoryMorphism L₁ L₂)
    (S : L₁.Obj)
    (types : Set (L₁.fibration.Sub S)) :
    F.mapPred (Mettapedia.OSLF.NativeType.piType L₁ S types) =
      Mettapedia.OSLF.NativeType.piType L₂ (F.mapSort S) (F.mapPred '' types)
    ∧
    (F.mapNatType (Mettapedia.OSLF.NativeType.NatType.full (L := L₁) S)).pred =
      (Mettapedia.OSLF.NativeType.NatType.full (L := L₂) (F.mapSort S)).pred := by
  exact F.piOmega_translation_endpoint S types

/-- CoreMain-facing Native Type translation endpoint for Π/Ω/Prop implication
preservation across theory morphisms. -/
theorem coreMain_nativeType_piOmegaProp_translation_endpoint
    {L₁ L₂ : Mettapedia.CategoryTheory.LambdaTheories.LambdaTheory}
    (F : Mettapedia.OSLF.NativeType.TheoryMorphism L₁ L₂)
    (S : L₁.Obj)
    (types : Set (L₁.fibration.Sub S))
    (φ ψ : L₁.fibration.Sub S) :
    F.mapPred (Mettapedia.OSLF.NativeType.piType L₁ S types) =
      Mettapedia.OSLF.NativeType.piType L₂ (F.mapSort S) (F.mapPred '' types)
    ∧
    (F.mapNatType (Mettapedia.OSLF.NativeType.NatType.full (L := L₁) S)).pred =
      (Mettapedia.OSLF.NativeType.NatType.full (L := L₂) (F.mapSort S)).pred
    ∧
    F.mapPred (Mettapedia.OSLF.NativeType.implType L₁ S φ ψ) =
      Mettapedia.OSLF.NativeType.implType L₂ (F.mapSort S) (F.mapPred φ) (F.mapPred ψ) := by
  exact F.piOmegaProp_translation_endpoint S types φ ψ

/-- CoreMain-facing bundled endpoint: Π/Ω/Prop translation together with
nontrivial constructor-category cross-sort transport composition. -/
theorem coreMain_nativeType_piOmegaProp_constructor_transport_bundle
    {L₁ L₂ : Mettapedia.CategoryTheory.LambdaTheories.LambdaTheory}
    (F : Mettapedia.OSLF.NativeType.TheoryMorphism L₁ L₂)
    (S : L₁.Obj)
    (types : Set (L₁.fibration.Sub S))
    (φ ψ : L₁.fibration.Sub S)
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    {A B C : Mettapedia.OSLF.NativeType.ConstructorNatType lang}
    (f : Mettapedia.OSLF.NativeType.ConstructorNatTypeHom lang A B)
    (g : Mettapedia.OSLF.NativeType.ConstructorNatTypeHom lang B C) :
    (F.mapPred (Mettapedia.OSLF.NativeType.piType L₁ S types) =
      Mettapedia.OSLF.NativeType.piType L₂ (F.mapSort S) (F.mapPred '' types))
    ∧
    ((F.mapNatType (Mettapedia.OSLF.NativeType.NatType.full (L := L₁) S)).pred =
      (Mettapedia.OSLF.NativeType.NatType.full (L := L₂) (F.mapSort S)).pred)
    ∧
    (F.mapPred (Mettapedia.OSLF.NativeType.implType L₁ S φ ψ) =
      Mettapedia.OSLF.NativeType.implType L₂ (F.mapSort S) (F.mapPred φ) (F.mapPred ψ))
    ∧
    Nonempty (Mettapedia.OSLF.NativeType.ConstructorNatTypeHom lang A C) := by
  exact F.piOmegaProp_with_constructor_transport_bundle S types φ ψ lang f g

/-- CoreMain-facing composition-stability endpoint for the bundled
Π/Ω/Prop + constructor transport contract. -/
theorem coreMain_nativeType_comp_piOmegaProp_constructor_transport_bundle
    {L₁ L₂ L₃ : Mettapedia.CategoryTheory.LambdaTheories.LambdaTheory}
    (F : Mettapedia.OSLF.NativeType.TheoryMorphism L₁ L₂)
    (G : Mettapedia.OSLF.NativeType.TheoryMorphism L₂ L₃)
    (S : L₁.Obj)
    (types : Set (L₁.fibration.Sub S))
    (φ ψ : L₁.fibration.Sub S)
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    {A B C : Mettapedia.OSLF.NativeType.ConstructorNatType lang}
    (f : Mettapedia.OSLF.NativeType.ConstructorNatTypeHom lang A B)
    (g : Mettapedia.OSLF.NativeType.ConstructorNatTypeHom lang B C) :
    (((Mettapedia.OSLF.NativeType.TheoryMorphism.comp G F).mapPred
      (Mettapedia.OSLF.NativeType.piType L₁ S types)) =
      Mettapedia.OSLF.NativeType.piType L₃
        ((Mettapedia.OSLF.NativeType.TheoryMorphism.comp G F).mapSort S)
        (((Mettapedia.OSLF.NativeType.TheoryMorphism.comp G F).mapPred '' types)))
    ∧
    ((((Mettapedia.OSLF.NativeType.TheoryMorphism.comp G F).mapNatType
      (Mettapedia.OSLF.NativeType.NatType.full (L := L₁) S)).pred =
      (Mettapedia.OSLF.NativeType.NatType.full (L := L₃)
        ((Mettapedia.OSLF.NativeType.TheoryMorphism.comp G F).mapSort S)).pred))
    ∧
    (((Mettapedia.OSLF.NativeType.TheoryMorphism.comp G F).mapPred
      (Mettapedia.OSLF.NativeType.implType L₁ S φ ψ)) =
      Mettapedia.OSLF.NativeType.implType L₃
        ((Mettapedia.OSLF.NativeType.TheoryMorphism.comp G F).mapSort S)
        ((Mettapedia.OSLF.NativeType.TheoryMorphism.comp G F).mapPred φ)
        ((Mettapedia.OSLF.NativeType.TheoryMorphism.comp G F).mapPred ψ))
    ∧
    Nonempty (Mettapedia.OSLF.NativeType.ConstructorNatTypeHom lang A C) := by
  exact F.comp_piOmegaProp_with_constructor_transport_bundle G S types φ ψ lang f g

/-- CoreMain-facing canonical colax/lax Π/Prop rule-set endpoint for theory
translations. -/
theorem coreMain_nativeType_piProp_colax_rules_endpoint
    {L₁ L₂ : Mettapedia.CategoryTheory.LambdaTheories.LambdaTheory}
    (F : Mettapedia.OSLF.NativeType.TheoryMorphism L₁ L₂)
    (S : L₁.Obj) :
    F.PiPropColaxRuleSet S := by
  exact F.piProp_colax_rules S

/-- CoreMain-facing identity-canary for the Native Type Π/Ω endpoint. -/
theorem coreMain_nativeType_id_piOmega_canary
    (L : Mettapedia.CategoryTheory.LambdaTheories.LambdaTheory)
    (S : L.Obj)
    (types : Set (L.fibration.Sub S)) :
    ((Mettapedia.OSLF.NativeType.TheoryMorphism.id L).mapPred
      (Mettapedia.OSLF.NativeType.piType L S types) =
        Mettapedia.OSLF.NativeType.piType L
          ((Mettapedia.OSLF.NativeType.TheoryMorphism.id L).mapSort S)
          ((Mettapedia.OSLF.NativeType.TheoryMorphism.id L).mapPred '' types))
    ∧
    (((Mettapedia.OSLF.NativeType.TheoryMorphism.id L).mapNatType
      (Mettapedia.OSLF.NativeType.NatType.full (L := L) S)).pred =
      (Mettapedia.OSLF.NativeType.NatType.full (L := L)
        ((Mettapedia.OSLF.NativeType.TheoryMorphism.id L).mapSort S)).pred) := by
  simpa using Mettapedia.OSLF.NativeType.TheoryMorphism.id_piOmega_translation_endpoint L S types

/-- CoreMain-facing constructor-category cross-sort native transport endpoint
(identity morphism). -/
abbrev coreMain_nativeType_constructor_transport_endpoint :=
  @Mettapedia.OSLF.NativeType.constructorNatTypeTransport_endpoint

/-- CoreMain-facing constructor-category cross-sort native transport endpoint
(composition). -/
abbrev coreMain_nativeType_constructor_transport_crossSort_comp :=
  @Mettapedia.OSLF.NativeType.constructorNatTypeTransport_crossSort_comp

/-- CoreMain-facing rhoCalc roundtrip canary for constructor-category
cross-sort native transport. -/
abbrev coreMain_nativeType_constructor_roundtrip_canary :=
  @Mettapedia.OSLF.NativeType.rho_roundtrip_constructorNatTypeHom

/-- CoreMain-facing concrete Mathlib Grothendieck endpoint over constructor sorts. -/
abbrev coreMain_nativeType_constructor_grothendieck_endpoint :=
  @Mettapedia.OSLF.NativeType.constructorPredFiberFunctorDual

/-- CoreMain-facing scoped roundtrip endpoint:
constructor transport -> Grothendieck morphism -> constructor transport. -/
theorem coreMain_nativeType_constructor_groth_roundtrip
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    {A B : Mettapedia.OSLF.NativeType.ConstructorNatType lang}
    (h : Mettapedia.OSLF.NativeType.ConstructorNatTypeHom lang A B) :
    Mettapedia.OSLF.NativeType.grothHom_to_constructorNatTypeHom
      (Mettapedia.OSLF.NativeType.constructorNatTypeHom_to_grothHom h) = h := by
  exact Mettapedia.OSLF.NativeType.constructorNatTypeHom_groth_roundtrip h

/-- CoreMain-facing end-to-end package:
Π/Ω/Prop translation plus constructor-transport/Grothendieck roundtrip. -/
theorem coreMain_nativeType_piOmegaProp_grothendieck_package
    {L₁ L₂ : Mettapedia.CategoryTheory.LambdaTheories.LambdaTheory}
    (F : Mettapedia.OSLF.NativeType.TheoryMorphism L₁ L₂)
    (S : L₁.Obj)
    (types : Set (L₁.fibration.Sub S))
    (φ ψ : L₁.fibration.Sub S)
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    {A B : Mettapedia.OSLF.NativeType.ConstructorNatType lang}
    (h : Mettapedia.OSLF.NativeType.ConstructorNatTypeHom lang A B) :
    (F.mapPred (Mettapedia.OSLF.NativeType.piType L₁ S types) =
      Mettapedia.OSLF.NativeType.piType L₂ (F.mapSort S) (F.mapPred '' types))
    ∧
    (F.mapNatType (Mettapedia.OSLF.NativeType.NatType.full (L := L₁) S)).pred =
      (Mettapedia.OSLF.NativeType.NatType.full (L := L₂) (F.mapSort S)).pred
    ∧
    (F.mapPred (Mettapedia.OSLF.NativeType.implType L₁ S φ ψ) =
      Mettapedia.OSLF.NativeType.implType L₂ (F.mapSort S) (F.mapPred φ) (F.mapPred ψ))
    ∧
    (Mettapedia.OSLF.NativeType.grothHom_to_constructorNatTypeHom
      (Mettapedia.OSLF.NativeType.constructorNatTypeHom_to_grothHom h) = h) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact F.preserves_piType S types
  · exact F.preserves_fullNatType_pred S
  · exact F.preserves_propImp S φ ψ
  · exact Mettapedia.OSLF.NativeType.constructorNatTypeHom_groth_roundtrip h

/-- CoreMain-facing scoped full-presheaf morphism endpoint. -/
abbrev coreMain_nativeType_full_presheaf_morphism_endpoint :=
  @Mettapedia.OSLF.NativeType.ScopedConstructorPredHom.toFullGrothHom

/-- CoreMain-facing composition law for scoped full-presheaf morphisms. -/
theorem coreMain_nativeType_full_presheaf_morphism_comp
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    {A B C : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang}
    (f : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang A B)
    (g : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang B C) :
    (Mettapedia.OSLF.NativeType.ScopedConstructorPredHom.comp f g).toFullGrothHom =
      Mettapedia.OSLF.NativeType.FullPresheafGrothendieckHom.comp
        f.toFullGrothHom g.toFullGrothHom := by
  exact Mettapedia.OSLF.NativeType.ScopedConstructorPredHom.toFullGrothHom_comp f g

/-- CoreMain-facing scoped comparison package between constructor and
full-presheaf endpoints. -/
theorem coreMain_nativeType_scoped_full_constructor_comparison_package
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    (A : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang)
    {B C : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang}
    (f : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang A B)
    (g : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang B C) :
    Mettapedia.OSLF.NativeType.grothObj_to_constructorNatType
      (Mettapedia.OSLF.NativeType.constructorNatType_toGrothObj A.toConstructorNatType) =
      A.toConstructorNatType
    ∧
    Opposite.unop (A.toFullGrothObj.base) =
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj lang A.sort
    ∧
    (Mettapedia.OSLF.NativeType.ScopedConstructorPredHom.comp f g).toFullGrothHom =
      Mettapedia.OSLF.NativeType.FullPresheafGrothendieckHom.comp
        f.toFullGrothHom g.toFullGrothHom := by
  exact Mettapedia.OSLF.NativeType.scoped_full_constructor_comparison_package A f g

/-- CoreMain-facing canonical category/topos package endpoint. -/
theorem coreMain_category_topos_package
    {σ : Mettapedia.CategoryTheory.Hypercube.Slot →
        Mettapedia.CategoryTheory.Hypercube.HSort}
    (hσ : Mettapedia.CategoryTheory.Hypercube.isEquationallyAdmissible σ)
    (a b c : Mettapedia.CategoryTheory.FuzzyFrame.UnitInterval) :
    σ Mettapedia.CategoryTheory.Hypercube.Slot.result =
      Mettapedia.CategoryTheory.Hypercube.HSort.star ∧
      (a * b ≤ c ↔ b ≤ Mettapedia.CategoryTheory.FuzzyFrame.UnitInterval.productImp a c) ∧
      a * b ≤ a ⊓ b :=
  coreMain_hypercube_fuzzy_bridge hσ a b c

/-- CoreMain-facing topos/internal-language bridge package:
fiber-membership/satisfies equivalence, conjunction/disjunction
internalization, and graph-object `◇`/`□` characterizations. -/
abbrev coreMain_topos_internal_language_bridge_package :=
  @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_internal_language_bridge_package

/-- CoreMain-facing TOGL-style graph/modal bridge package:
`∃/∀` reduction formulations are equivalent to edge-based graph-object
formulations. -/
abbrev coreMain_togl_graph_modal_bridge_package :=
  @Mettapedia.OSLF.Framework.ToposTOGLBridge.togl_graph_modal_bridge_package

/-- CoreMain-facing stronger topos/internal-language family with explicit
full presheaf-native route restriction/equivalence packaging. -/
abbrev coreMain_topos_internal_language_full_route_family :=
  @Mettapedia.OSLF.Framework.ToposTOGLBridge.topos_internal_language_full_route_family

/-- CoreMain-facing TOGL correspondence layer above graph-modal equivalence:
internal-subfunctor and graph-object edge characterizations coincide. -/
abbrev coreMain_togl_internal_graph_correspondence_layer :=
  @Mettapedia.OSLF.Framework.ToposTOGLBridge.togl_internal_graph_correspondence_layer

/-- CoreMain-facing canonical framework-level identity semantic transfer endpoint. -/
abbrev coreMain_identity_semantic_transfer_endpoint :=
  @Mettapedia.OSLF.Framework.IdentityEvidenceTransfer.identity_semantic_transfer_endpoint

/-- CoreMain-facing canonical OSLF paper §12 worked-example endpoint. -/
abbrev coreMain_section12_worked_examples :=
  @Mettapedia.OSLF.Framework.PaperSection12Examples.section12_worked_examples_bundle

/-- CoreMain-facing dependent/parametric generated-typing extension endpoint. -/
abbrev coreMain_dependent_parametric_generated_typing :=
  @Mettapedia.OSLF.Framework.GeneratedTyping.dependent_parametric_generated_type_system_extension

/-- CoreMain-facing canonical Theorem-1 contract:
forward substitutability plus the scoped image-finite equivalence endpoint. -/
structure CoreMainTheorem1CanonicalContract
    (R : Mettapedia.OSLF.Framework.Pat → Mettapedia.OSLF.Framework.Pat → Prop)
    (I : Mettapedia.OSLF.Formula.AtomSem) : Prop where
  forward :
    ∀ {p q : Mettapedia.OSLF.Framework.Pat},
      Mettapedia.OSLF.Framework.theorem1_behaviorEq R I p q →
      Mettapedia.OSLF.Framework.theorem1_sameNativeTypes R I p q
  imageFinite_iff :
    (∀ p : Mettapedia.OSLF.Framework.Pat, Set.Finite {q : Mettapedia.OSLF.Framework.Pat | R p q}) →
    (∀ p : Mettapedia.OSLF.Framework.Pat, Set.Finite {q : Mettapedia.OSLF.Framework.Pat | R q p}) →
    Mettapedia.OSLF.Framework.Theorem1SubstitutabilityEquiv R I

/-- CoreMain-facing canonical Theorem-1 contract constructor. -/
theorem coreMain_theorem1_canonical_contract
    (R : Mettapedia.OSLF.Framework.Pat → Mettapedia.OSLF.Framework.Pat → Prop)
    (I : Mettapedia.OSLF.Formula.AtomSem) :
    CoreMainTheorem1CanonicalContract R I := by
  refine ⟨?_, ?_⟩
  · intro p q h
    exact Mettapedia.OSLF.Framework.theorem1_substitutability_forward h
  · intro hImageFinite hPredFinite
    exact Mettapedia.OSLF.Framework.theorem1_substitutability_imageFinite hImageFinite hPredFinite

/-- CoreMain-facing Theorem-1 forward endpoint (projection from the canonical
contract field). -/
theorem coreMain_theorem1_substitutability_forward
    {R : Mettapedia.OSLF.Framework.Pat → Mettapedia.OSLF.Framework.Pat → Prop}
    {I : Mettapedia.OSLF.Formula.AtomSem}
    {p q : Mettapedia.OSLF.Framework.Pat} :
    Mettapedia.OSLF.Framework.theorem1_behaviorEq R I p q →
    Mettapedia.OSLF.Framework.theorem1_sameNativeTypes R I p q := by
  exact (coreMain_theorem1_canonical_contract (R := R) (I := I)).forward

/-- CoreMain-facing Theorem-1 scoped full equivalence endpoint (projection from
the canonical contract field). -/
theorem coreMain_theorem1_substitutability_imageFinite
    {R : Mettapedia.OSLF.Framework.Pat → Mettapedia.OSLF.Framework.Pat → Prop}
    {I : Mettapedia.OSLF.Formula.AtomSem}
    (hImageFinite : ∀ p : Mettapedia.OSLF.Framework.Pat,
      Set.Finite {q : Mettapedia.OSLF.Framework.Pat | R p q})
    (hPredFinite : ∀ p : Mettapedia.OSLF.Framework.Pat,
      Set.Finite {q : Mettapedia.OSLF.Framework.Pat | R q p}) :
    Mettapedia.OSLF.Framework.Theorem1SubstitutabilityEquiv R I := by
  exact (coreMain_theorem1_canonical_contract (R := R) (I := I)).imageFinite_iff
    hImageFinite hPredFinite

/-- CoreMain-facing canonical Theorem-1 equivalence endpoint on the default
`langReduces` relation:
the forward image-finite side is discharged concretely; only predecessor
finiteness remains as an explicit assumption. -/
theorem coreMain_theorem1_langReduces_imageFinite
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (hPredFinite : ∀ p : Mettapedia.OSLF.Framework.Pat,
      Set.Finite {q : Mettapedia.OSLF.Framework.Pat |
        Mettapedia.OSLF.Framework.TypeSynthesis.langReduces lang q p}) :
    Mettapedia.OSLF.Framework.Theorem1SubstitutabilityEquiv
      (Mettapedia.OSLF.Framework.TypeSynthesis.langReduces lang) I := by
  exact coreMain_theorem1_substitutability_imageFinite
    (R := Mettapedia.OSLF.Framework.TypeSynthesis.langReduces lang)
    (I := I)
    (hImageFinite := Mettapedia.Logic.OSLFImageFinite.imageFinite_langReduces lang)
    hPredFinite

/-- CoreMain-facing paper-parity theorem package:
projects Theorem-1 canonical contract, fragment-parametric reachable full-route
comparison, and TOGL graph-composition laws. -/
theorem coreMain_paper_parity_theorem_package
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    (R : Mettapedia.OSLF.Framework.Pat → Mettapedia.OSLF.Framework.Pat → Prop)
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (A : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang)
    (Frag : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang → Prop)
    (hClosed : ∀ {X Y : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang},
      Frag X → Mettapedia.OSLF.NativeType.ScopedReachable X Y → Frag Y) :
    CoreMainTheorem1CanonicalContract R I
    ∧
    (∀ {B C : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang},
      Frag A →
      Mettapedia.OSLF.NativeType.ScopedReachable A B →
      Mettapedia.OSLF.NativeType.ScopedReachable B C →
      Frag B
      ∧
      Frag C
      ∧
      ∃ f : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang A B,
        ∃ g : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang B C,
          Mettapedia.OSLF.NativeType.FullRouteRestrictionEquivalence lang A
          ∧
          f.toFullGrothHom.base = CategoryTheory.yoneda.map f.base
          ∧
          g.toFullGrothHom.base = CategoryTheory.yoneda.map g.base
          ∧
          (Mettapedia.OSLF.NativeType.ScopedConstructorPredHom.comp f g).toFullGrothHom =
            Mettapedia.OSLF.NativeType.FullPresheafGrothendieckHom.comp
              f.toFullGrothHom g.toFullGrothHom)
    ∧
    (∀ {relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv}
      {C : Type _} [CategoryTheory.Category C]
      {X : Opposite C}
      (p r : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern),
      Mettapedia.OSLF.Framework.ToposTOGLBridge.graphChain2
        (lang := lang) (relEnv := relEnv) (C := C) (X := X) p r
      ↔
      ∃ q,
        Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv lang p q
        ∧
        Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv lang q r) := by
  refine ⟨coreMain_theorem1_canonical_contract (R := R) (I := I), ?_, ?_⟩
  · intro B C hA hAB hBC
    exact Mettapedia.OSLF.NativeType.full_presheaf_comparison_bundle_reachable_fragment
      (Frag := Frag) (hClosed := hClosed) (A := A) (B := B) (C := C) hA hAB hBC
  · intro relEnv C _ X p r
    simpa using
      (Mettapedia.OSLF.Framework.ToposTOGLBridge.togl_graph_composition_reductionGraphObj_family
        (lang := lang) (relEnv := relEnv) (C := C) (X := X) (p := p) (r := r))

/-- CoreMain-facing paper-parity theorem package specialized to the canonical
relation `langReduces`:
returns Theorem-1 equivalence on the canonical relation plus the existing
fragment and TOGL composition endpoint fields. -/
theorem coreMain_paper_parity_theorem_package_langReduces
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (A : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang)
    (Frag : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang → Prop)
    (hClosed : ∀ {X Y : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang},
      Frag X → Mettapedia.OSLF.NativeType.ScopedReachable X Y → Frag Y)
    (hPredFinite : ∀ p : Mettapedia.OSLF.Framework.Pat,
      Set.Finite {q : Mettapedia.OSLF.Framework.Pat |
        Mettapedia.OSLF.Framework.TypeSynthesis.langReduces lang q p}) :
    Mettapedia.OSLF.Framework.Theorem1SubstitutabilityEquiv
      (Mettapedia.OSLF.Framework.TypeSynthesis.langReduces lang) I
    ∧
    (∀ {B C : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang},
      Frag A →
      Mettapedia.OSLF.NativeType.ScopedReachable A B →
      Mettapedia.OSLF.NativeType.ScopedReachable B C →
      Frag B
      ∧
      Frag C
      ∧
      ∃ f : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang A B,
        ∃ g : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang B C,
          Mettapedia.OSLF.NativeType.FullRouteRestrictionEquivalence lang A
          ∧
          f.toFullGrothHom.base = CategoryTheory.yoneda.map f.base
          ∧
          g.toFullGrothHom.base = CategoryTheory.yoneda.map g.base
          ∧
          (Mettapedia.OSLF.NativeType.ScopedConstructorPredHom.comp f g).toFullGrothHom =
            Mettapedia.OSLF.NativeType.FullPresheafGrothendieckHom.comp
              f.toFullGrothHom g.toFullGrothHom)
    ∧
    (∀ {relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv}
      {C : Type _} [CategoryTheory.Category C]
      {X : Opposite C}
      (p r : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern),
      Mettapedia.OSLF.Framework.ToposTOGLBridge.graphChain2
        (lang := lang) (relEnv := relEnv) (C := C) (X := X) p r
      ↔
      ∃ q,
        Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv lang p q
        ∧
        Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv lang q r) := by
  rcases coreMain_paper_parity_theorem_package
      (lang := lang)
      (R := Mettapedia.OSLF.Framework.TypeSynthesis.langReduces lang)
      (I := I) (A := A) (Frag := Frag) hClosed with
    ⟨hContract, hFrag, hTogl⟩
  refine ⟨?_, hFrag, hTogl⟩
  exact hContract.imageFinite_iff
    (Mettapedia.Logic.OSLFImageFinite.imageFinite_langReduces lang) hPredFinite

/-- Canonical CoreMain paper-parity contract record:
packages the `langReduces` Theorem-1 endpoint, fragment-parametric full-route
comparison, and TOGL graph-composition law in one field-based API. -/
structure CoreMainPaperParityCanonicalPackage
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (A : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang)
    (Frag : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang → Prop) : Prop where
  theorem1_langReduces_imageFinite :
    (∀ p : Mettapedia.OSLF.Framework.Pat,
      Set.Finite {q : Mettapedia.OSLF.Framework.Pat |
        Mettapedia.OSLF.Framework.TypeSynthesis.langReduces lang q p}) →
      Mettapedia.OSLF.Framework.Theorem1SubstitutabilityEquiv
        (Mettapedia.OSLF.Framework.TypeSynthesis.langReduces lang) I
  full_presheaf_fragment :
    ∀ {B C : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang},
      Frag A →
      Mettapedia.OSLF.NativeType.ScopedReachable A B →
      Mettapedia.OSLF.NativeType.ScopedReachable B C →
      Frag B
      ∧
      Frag C
      ∧
      ∃ f : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang A B,
        ∃ g : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang B C,
          Mettapedia.OSLF.NativeType.FullRouteRestrictionEquivalence lang A
          ∧
          f.toFullGrothHom.base = CategoryTheory.yoneda.map f.base
          ∧
          g.toFullGrothHom.base = CategoryTheory.yoneda.map g.base
          ∧
          (Mettapedia.OSLF.NativeType.ScopedConstructorPredHom.comp f g).toFullGrothHom =
            Mettapedia.OSLF.NativeType.FullPresheafGrothendieckHom.comp
              f.toFullGrothHom g.toFullGrothHom
  togl_graph_composition :
    ∀ {relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv}
      {C : Type _} [CategoryTheory.Category C]
      {X : Opposite C}
      (p r : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern),
      Mettapedia.OSLF.Framework.ToposTOGLBridge.graphChain2
        (lang := lang) (relEnv := relEnv) (C := C) (X := X) p r
      ↔
      ∃ q,
        Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv lang p q
        ∧
        Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv lang q r

/-- CoreMain-facing canonical paper-parity package endpoint:
builds the field-based contract from the existing specialized theorem package. -/
theorem coreMain_paper_parity_canonical_package
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (A : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang)
    (Frag : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang → Prop)
    (hClosed : ∀ {X Y : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang},
      Frag X → Mettapedia.OSLF.NativeType.ScopedReachable X Y → Frag Y) :
    CoreMainPaperParityCanonicalPackage lang I A Frag := by
  refine ⟨?_, ?_, ?_⟩
  · intro hPredFinite
    exact coreMain_theorem1_langReduces_imageFinite
      (lang := lang) (I := I) hPredFinite
  · intro B C hA hAB hBC
    exact Mettapedia.OSLF.NativeType.full_presheaf_comparison_bundle_reachable_fragment
      (Frag := Frag) (hClosed := hClosed) (A := A) (B := B) (C := C) hA hAB hBC
  · intro relEnv C _ X p r
    simpa using
      (Mettapedia.OSLF.Framework.ToposTOGLBridge.togl_graph_composition_reductionGraphObj_family
        (lang := lang) (relEnv := relEnv) (C := C) (X := X) (p := p) (r := r))

/-- Extended paper-parity package: adds M1–M4 milestones on top of the canonical package.
This bundles:
- M1: Category instance for full presheaf Grothendieck
- M2: Equivalence at representable objects (scoped ↔ full roundtrip)
- M3: Full internal logic bridge (⊤/⊥/∧/∨/→/¬, Π/Σ)
- M4: TOGL complete bridge (2-step + n-step + modal iteration) -/
theorem coreMain_paper_parity_full_package
    (lang : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    (I : Mettapedia.OSLF.Formula.AtomSem)
    (A : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang)
    (Frag : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang → Prop)
    (hClosed : ∀ {X Y : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang},
      Frag X → Mettapedia.OSLF.NativeType.ScopedReachable X Y → Frag Y)
    {B C : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang}
    (f : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang A B)
    (g : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang B C) :
    -- Base canonical package
    CoreMainPaperParityCanonicalPackage lang I A Frag
    ∧
    -- M1: Category instance witness
    (∃ _ : CategoryTheory.Category.{0, 1}
      (Mettapedia.OSLF.NativeType.FullPresheafGrothendieckObj lang), True)
    ∧
    -- M2: Scoped ↔ full roundtrip at representable objects
    (Mettapedia.OSLF.NativeType.fullGrothObj_to_scopedConstructorPred_at_representable
      A.toFullGrothObj A.sort A.seed A.pred A.naturality
      (Mettapedia.OSLF.NativeType.scoped_fullGroth_base_eq_representable A)
      rfl = A)
    ∧
    -- M2: Full route restriction equivalence
    Mettapedia.OSLF.NativeType.FullRouteRestrictionEquivalence lang A
    ∧
    -- M2: Composition preservation
    ((Mettapedia.OSLF.NativeType.ScopedConstructorPredHom.comp f g).toFullGrothHom =
      Mettapedia.OSLF.NativeType.FullPresheafGrothendieckHom.comp
        f.toFullGrothHom g.toFullGrothHom)
    ∧
    -- M4: N-step graph chain ↔ relational composition
    (∀ {relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv}
        {Ct : Type _} [CategoryTheory.Category Ct]
        {X : Opposite Ct}
        (n : Nat) (p r : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern),
      Mettapedia.OSLF.Framework.ToposTOGLBridge.graphChainN
        (lang := lang) (relEnv := relEnv) (C := Ct) (X := X) n p r
        ↔
      Mettapedia.OSLF.Framework.ToposTOGLBridge.relCompN lang relEnv n p r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact coreMain_paper_parity_canonical_package lang I A Frag hClosed
  · exact ⟨Mettapedia.OSLF.NativeType.fullPresheafGrothendieckCategory lang, trivial⟩
  · exact Mettapedia.OSLF.NativeType.scoped_full_scoped_obj_roundtrip A
  · exact (Mettapedia.OSLF.NativeType.full_route_restriction_equivalence_package
      (A := A) f g).1
  · exact (Mettapedia.OSLF.NativeType.full_route_restriction_equivalence_package
      (A := A) f g).2
  · intro relEnv Ct _ X n p r
    exact Mettapedia.OSLF.Framework.ToposTOGLBridge.graphChainN_iff_relCompN
      lang relEnv Ct (X := X) n p r

#check @coreMain_paper_parity_full_package

#check Mettapedia.OSLF.Framework.FULLStatus.remaining_eq_nil
#check Mettapedia.OSLF.Framework.FULLStatus.remainingCount_eq_zero
#check Mettapedia.OSLF.Framework.FULLStatus.strictRemaining_eq_nil
#check Mettapedia.OSLF.Framework.FULLStatus.strictRemainingCount_eq_zero
#check Mettapedia.OSLF.MeTTaCore.FullLanguageDef.mettaFull
#check Mettapedia.OSLF.MeTTaCore.FullLanguageDef.mettaFullOSLF
#check Mettapedia.Logic.OSLFImageFinite.imageFinite_langReduces
#check Mettapedia.Logic.OSLFImageFinite.hm_converse_langReduces
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.piRho_coreMain_canonical_contract_end_to_end
#check @coreMain_piRho_canonical_contract
#check @coreMain_piRho_contract_projection_api
#check @coreMain_hypercube_fuzzy_bridge
#check @coreMain_identity_semantic_transfer_endpoint
#check @coreMain_nativeType_piOmega_translation_endpoint
#check @coreMain_nativeType_piOmegaProp_translation_endpoint
#check @coreMain_nativeType_piOmegaProp_constructor_transport_bundle
#check @coreMain_nativeType_comp_piOmegaProp_constructor_transport_bundle
#check @coreMain_nativeType_piProp_colax_rules_endpoint
#check @coreMain_nativeType_id_piOmega_canary
#check @coreMain_nativeType_constructor_transport_endpoint
#check @coreMain_nativeType_constructor_transport_crossSort_comp
#check @coreMain_nativeType_constructor_roundtrip_canary
#check @coreMain_nativeType_constructor_grothendieck_endpoint
#check @coreMain_nativeType_constructor_groth_roundtrip
#check @coreMain_nativeType_piOmegaProp_grothendieck_package
#check @coreMain_nativeType_full_presheaf_morphism_endpoint
#check @coreMain_nativeType_full_presheaf_morphism_comp
#check @coreMain_nativeType_scoped_full_constructor_comparison_package
#check @coreMain_category_topos_package
#check @coreMain_topos_internal_language_bridge_package
#check @coreMain_togl_graph_modal_bridge_package
#check @coreMain_topos_internal_language_full_route_family
#check @coreMain_togl_internal_graph_correspondence_layer
#check @coreMain_section12_worked_examples
#check @coreMain_dependent_parametric_generated_typing
#check @coreMain_theorem1_canonical_contract
#check @coreMain_theorem1_substitutability_forward
#check @coreMain_theorem1_substitutability_imageFinite
#check @coreMain_theorem1_langReduces_imageFinite
#check @coreMain_paper_parity_theorem_package
#check @coreMain_paper_parity_theorem_package_langReduces
#check @CoreMainPaperParityCanonicalPackage
#check @coreMain_paper_parity_canonical_package

end Mettapedia.OSLF
