import Mettapedia.OSLF.Framework.LanguagePresheafSharing
import Mettapedia.OSLF.Framework.WMCalculusSemantics
import Mettapedia.OSLF.PresheafNativeType.PresheafSemantics
import Mettapedia.OSLF.PresheafNativeType.InternalLanguage

/-!
# World-model observations in the native predicate fibration

An observation on sorted world-model terms determines a subfunctor of the
language's program presheaf. If the observation respects behavioral agreement,
the subfunctor is closed under the operational lambda theory's pointwise
rewrite relation. The closure theorem works in any presheaf context and
commutes with substitution into that context.

The predicate includes only patterns encoding a term of the selected WM sort.
No interpretation of an arbitrary pattern or dependent identity type is
postulated.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusNativeObservation

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.LangMorphism
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.ToposReduction
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.LanguagePresheafSharing
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusContextEncoding
open Mettapedia.OSLF.Framework.WMCalculusEncoding
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.PresheafNativeType
open Mettapedia.GSLT.Topos

/-- The authored contextual WM presentation shared by the operational and
presheaf constructions. -/
private abbrev wmLanguage : LanguageDef :=
  wmExtVertexLanguageDefWithCong wmExtVertexMinimal

/-- An observation is insensitive to the behavioral agreement appropriate to
its WM sort. At the state sort this tests all semantic queries, while at the
other two sorts agreement is equality. -/
def ObservationInvariant {State Query V : Type}
    (R : WMReading State Query V) (s : WMSort)
    (P : SortValue State Query V s → Prop) : Prop :=
  ∀ a b, R.Agree s a b → P a → P b

/-- A WM observation is an actual native predicate on the constant program
presheaf of the authored contextual language. -/
def observationPredicate {State Query V : Type}
    (R : WMReading State Query V) (s : WMSort)
    (P : SortValue State Query V s → Prop) :
    Subfunctor (languageProgramObj wmLanguage) where
  obj X := { p | ∃ t : WMTerm s, encodeWM t = p.down ∧ P (R.denote t) }
  map := by
    intro X Y f p hp
    exact hp

/-- The observation predicate as an object of the full presheaf predicate
category. Its carrier is the language's real program object. -/
def observationNativeType {State Query V : Type}
    (R : WMReading State Query V) (s : WMSort)
    (P : SortValue State Query V s → Prop) :
    FullPresheafGrothendieckObj wmLanguage where
  base := Opposite.op (languageProgramObj wmLanguage)
  fiber := observationPredicate R s P

/-- On an encoded typed term, native-predicate membership is exactly its
semantic observation. Encoder injectivity excludes unrelated witnesses. -/
theorem observationPredicate_encoded_iff {State Query V : Type}
    (R : WMReading State Query V) (s : WMSort)
    (P : SortValue State Query V s → Prop)
    (X : Opposite (ConstructorObj wmLanguage)) (term : WMTerm s) :
    (ULift.up (encodeWM term) : (languageProgramObj wmLanguage).obj X) ∈
      (observationPredicate R s P).obj X ↔ P (R.denote term) := by
  constructor
  · rintro ⟨witness, encoded, observed⟩
    have equal : witness = term := encodeWM_injective encoded
    simpa only [equal] using observed
  · intro observed
    exact ⟨term, rfl, observed⟩

/-- The same observation fiber over an arbitrary presheaf context, pulled
back along a generalized program term. -/
def observationInContext {State Query V : Type}
    (R : WMReading State Query V) (s : WMSort)
    (P : SortValue State Query V s → Prop)
    (Γ : languagePresheafObj wmLanguage)
    (program : Γ ⟶ languageProgramObj wmLanguage) :
    FullPresheafGrothendieckObj wmLanguage where
  base := Opposite.op Γ
  fiber := (observationPredicate R s P).preimage program

/-- A contextual WM rewrite transports every observation invariant under
behavioral agreement. Completeness of the typed encoding ensures that the
target remains an encoded term of the same sort. -/
theorem observationPredicate_step {State Query V : Type}
    (R : WMReading State Query V) (laws : R.CoreLaws)
    (s : WMSort) (P : SortValue State Query V s → Prop)
    (stable : ObservationInvariant R s P)
    {source target : Pattern}
    (step : langSemanticReduces wmLanguage source target)
    {X : Opposite (ConstructorObj wmLanguage)}
    (member : (ULift.up source : (languageProgramObj wmLanguage).obj X) ∈
      (observationPredicate R s P).obj X) :
    (ULift.up target : (languageProgramObj wmLanguage).obj X) ∈
      (observationPredicate R s P).obj X := by
  obtain ⟨term, encoded, observed⟩ := member
  have stepTerm : langSemanticReduces wmLanguage (encodeWM term) target := by
    simpa only [encoded] using step
  obtain ⟨reduct, encoded, agree⟩ :=
    laws.contextual_step_agrees term stepTerm
  exact ⟨reduct, encoded, stable _ _ agree observed⟩

/-- The same native observation is closed under every finite contextual
computation of the authored WM presentation. -/
theorem observationPredicate_star {State Query V : Type}
    (R : WMReading State Query V) (laws : R.CoreLaws)
    (s : WMSort) (P : SortValue State Query V s → Prop)
    (stable : ObservationInvariant R s P)
    {source target : Pattern}
    (steps : LangReducesStar wmLanguage source target)
    {X : Opposite (ConstructorObj wmLanguage)}
    (member : (ULift.up source : (languageProgramObj wmLanguage).obj X) ∈
      (observationPredicate R s P).obj X) :
    (ULift.up target : (languageProgramObj wmLanguage).obj X) ∈
      (observationPredicate R s P).obj X := by
  obtain ⟨term, encoded, observed⟩ := member
  have reductions : LangReducesStar wmLanguage (encodeWM term) target := by
    simpa only [encoded] using steps
  obtain ⟨reduct, encoded, agree⟩ :=
    laws.contextual_reduct_agrees term reductions
  exact ⟨reduct, encoded, stable _ _ agree observed⟩

/-- A rewrite of generalized program terms preserves the native observation
predicate after pulling it back to any presheaf context. -/
theorem observationPredicate_rewrite {State Query V : Type}
    (R : WMReading State Query V) (laws : R.CoreLaws)
    (s : WMSort) (P : SortValue State Query V s → Prop)
    (stable : ObservationInvariant R s P)
    {Γ : languagePresheafObj wmLanguage}
    {p q : Γ ⟶ languageProgramObj wmLanguage}
    (step : (languageOperationalLambdaTheory wmLanguage).rewriteRel p q) :
    (observationPredicate R s P).preimage p ≤
      (observationPredicate R s P).preimage q := by
  intro X x member
  have semantic : langSemanticReduces wmLanguage
      (p.app X x).down (q.app X x).down :=
    (mem_reductionSubfunctorUsing_iff
      (C := ConstructorObj wmLanguage)
      (relEnv := RelationEnv.empty) (lang := wmLanguage)
      (X := X) (p := (p.app X x).down) (q := (q.app X x).down)).mp
        (step X x)
  change (p.app X x) ∈ (observationPredicate R s P).obj X at member
  change (q.app X x) ∈ (observationPredicate R s P).obj X
  exact observationPredicate_step R laws s P stable semantic member

/-- A computational step maps actual inhabitants of the source
comprehension to inhabitants of the target comprehension. -/
def observationRewriteComprehensionMap {State Query V : Type}
    (R : WMReading State Query V) (laws : R.CoreLaws)
    (s : WMSort) (P : SortValue State Query V s → Prop)
    (stable : ObservationInvariant R s P)
    {Γ : languagePresheafObj wmLanguage}
    {p q : Γ ⟶ languageProgramObj wmLanguage}
    (step : (languageOperationalLambdaTheory wmLanguage).rewriteRel p q) :
    ((observationPredicate R s P).preimage p).toFunctor ⟶
      ((observationPredicate R s P).preimage q).toFunctor where
  app X := TypeCat.ofHom (fun inhabitant =>
    ⟨inhabitant.1,
      (observationPredicate_rewrite R laws s P stable step) X inhabitant.2⟩)
  naturality := by
    intro X Y f
    apply ConcreteCategory.hom_injective
    apply TypeCat.Fun.ext
    funext inhabitant
    apply Subtype.ext
    rfl

/-- Comprehension transport commutes with both inclusions into the
original context. This square is the extensional substitution action of a
WM rewrite on inhabitants, not equality of the two native types. -/
theorem observationRewriteComprehension_square {State Query V : Type}
    (R : WMReading State Query V) (laws : R.CoreLaws)
    (s : WMSort) (P : SortValue State Query V s → Prop)
    (stable : ObservationInvariant R s P)
    {Γ : languagePresheafObj wmLanguage}
    {p q : Γ ⟶ languageProgramObj wmLanguage}
    (step : (languageOperationalLambdaTheory wmLanguage).rewriteRel p q) :
    observationRewriteComprehensionMap R laws s P stable step ≫
      ((observationPredicate R s P).preimage q).ι =
        ((observationPredicate R s P).preimage p).ι := by
  ext X inhabitant
  rfl

/-- Reindexing by a change of context preserves the observational rewrite
law. This is the dependent substitution equation for this predicate. -/
theorem observationPredicate_rewrite_subst {State Query V : Type}
    (R : WMReading State Query V) (laws : R.CoreLaws)
    (s : WMSort) (P : SortValue State Query V s → Prop)
    (stable : ObservationInvariant R s P)
    {Γ Δ : languagePresheafObj wmLanguage}
    (σ : Δ ⟶ Γ) {p q : Γ ⟶ languageProgramObj wmLanguage}
    (step : (languageOperationalLambdaTheory wmLanguage).rewriteRel p q) :
    (observationPredicate R s P).preimage (σ ≫ p) ≤
      (observationPredicate R s P).preimage (σ ≫ q) := by
  exact observationPredicate_rewrite R laws s P stable
    ((languageOperationalLambdaTheory wmLanguage).rewriteRel_nat σ p q step)

/-- A map of presheaf contexts is the dependent context in the existing
indexed-adjoint machinery. -/
def observationDependentContext {Γ Δ : languagePresheafObj wmLanguage}
    (σ : Δ ⟶ Γ) :
    PresheafDepCtx (C := ConstructorObj wmLanguage) where
  A := Δ
  B := Γ
  f := σ

/-- Existential dependent quantification along a context map preserves a
WM observation under computation. The content is the contextual WM
preservation theorem before applying the indexed Σ monotonicity law. -/
theorem observationSigmaRewrite {State Query V : Type}
    (R : WMReading State Query V) (laws : R.CoreLaws)
    (s : WMSort) (P : SortValue State Query V s → Prop)
    (stable : ObservationInvariant R s P)
    {Γ Δ : languagePresheafObj wmLanguage}
    (σ : Δ ⟶ Γ) {p q : Γ ⟶ languageProgramObj wmLanguage}
    (step : (languageOperationalLambdaTheory wmLanguage).rewriteRel p q) :
    (observationDependentContext σ).sigmaForm
      ((observationPredicate R s P).preimage (σ ≫ p)) ≤
    (observationDependentContext σ).sigmaForm
      ((observationPredicate R s P).preimage (σ ≫ q)) := by
  exact (presheafChangeOfBase (ConstructorObj wmLanguage)).directImage_mono σ
    (observationPredicate_rewrite_subst R laws s P stable σ step)

/-- Universal dependent quantification along a context map preserves a
WM observation under computation. -/
theorem observationPiRewrite {State Query V : Type}
    (R : WMReading State Query V) (laws : R.CoreLaws)
    (s : WMSort) (P : SortValue State Query V s → Prop)
    (stable : ObservationInvariant R s P)
    {Γ Δ : languagePresheafObj wmLanguage}
    (σ : Δ ⟶ Γ) {p q : Γ ⟶ languageProgramObj wmLanguage}
    (step : (languageOperationalLambdaTheory wmLanguage).rewriteRel p q) :
    (observationDependentContext σ).piForm
      ((observationPredicate R s P).preimage (σ ≫ p)) ≤
    (observationDependentContext σ).piForm
      ((observationPredicate R s P).preimage (σ ≫ q)) := by
  exact (presheafChangeOfBase (ConstructorObj wmLanguage)).universalImage_mono σ
    (observationPredicate_rewrite_subst R laws s P stable σ step)

/-- A rewrite induces a real morphism between the dependent observation
families over the same context. The fiber component is contextual WM subject
reduction, rather than an identification of the source and target programs. -/
def observationRewriteTransport {State Query V : Type}
    (R : WMReading State Query V) (laws : R.CoreLaws)
    (s : WMSort) (P : SortValue State Query V s → Prop)
    (stable : ObservationInvariant R s P)
    {Γ : languagePresheafObj wmLanguage}
    {p q : Γ ⟶ languageProgramObj wmLanguage}
    (step : (languageOperationalLambdaTheory wmLanguage).rewriteRel p q) :
    FullPresheafGrothendieckHom wmLanguage
      (observationInContext R s P Γ p)
      (observationInContext R s P Γ q) where
  base := 𝟙 Γ
  fiberLe := by
    change (observationPredicate R s P).preimage p ≤
      CategoryTheory.Subfunctor.preimage
        ((observationPredicate R s P).preimage q) (𝟙 Γ)
    simpa only [CategoryTheory.Subfunctor.preimage_id] using
      (observationPredicate_rewrite R laws s P stable step)

/-- Reindexing is a morphism of native observation families, not only a
pointwise substitution equation. -/
def observationReindex {State Query V : Type}
    (R : WMReading State Query V) (s : WMSort)
    (P : SortValue State Query V s → Prop)
    {Γ Δ : languagePresheafObj wmLanguage}
    (σ : Δ ⟶ Γ) (p : Γ ⟶ languageProgramObj wmLanguage) :
    FullPresheafGrothendieckHom wmLanguage
      (observationInContext R s P Δ (σ ≫ p))
      (observationInContext R s P Γ p) where
  base := σ
  fiberLe := by
    simp only [observationInContext, CategoryTheory.Subfunctor.preimage_comp]
    exact le_refl _

/-- The dependent comprehension of the observation predicate recovers
precisely that predicate by the established image/comprehension adjunction. -/
theorem observationComprehension_image {State Query V : Type}
    (R : WMReading State Query V) (s : WMSort)
    (P : SortValue State Query V s → Prop) :
    imagePredicate (observationPredicate R s P).ι =
      observationPredicate R s P :=
  image_comprehension_roundtrip (languageProgramObj wmLanguage)
    (observationPredicate R s P)

/-- Comprehension of an observation after reindexing to a context has
exactly the reindexed observation as its image. -/
theorem observationContextComprehension_image {State Query V : Type}
    (R : WMReading State Query V) (s : WMSort)
    (P : SortValue State Query V s → Prop)
    (Γ : languagePresheafObj wmLanguage)
    (p : Γ ⟶ languageProgramObj wmLanguage) :
    imagePredicate (observationInContext R s P Γ p).fiber.ι =
      (observationInContext R s P Γ p).fiber :=
  image_comprehension_roundtrip Γ (observationInContext R s P Γ p).fiber

/-- Equality of evidence values is a rewrite-stable native observation. -/
theorem evidence_eq_invariant {State Query V : Type}
    (R : WMReading State Query V) (value : V) :
    ObservationInvariant R .evidence (fun actual => actual = value) := by
  intro a b agree equal
  exact agree.symm ▸ equal

/-- A fixed-query state observation is stable under behavioral agreement. -/
theorem state_query_eq_invariant {State Query V : Type}
    (R : WMReading State Query V) (query : Query) (value : V) :
    ObservationInvariant R .state
      (fun state => R.extract state query = value) := by
  intro a b agree equal
  exact (agree query).symm ▸ equal

end Mettapedia.OSLF.Framework.WMCalculusNativeObservation
