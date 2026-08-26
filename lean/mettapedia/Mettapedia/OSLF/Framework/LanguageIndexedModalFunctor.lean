import Mathlib.CategoryTheory.EssentialImage
import Mathlib.Data.List.MinMax
import Mathlib.Order.Hom.CompleteLattice
import Mettapedia.GSLT.Core.ProofRelevantPresentation
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis
import Mettapedia.OSLF.Framework.ModeTheory
import Mettapedia.OSLF.NativeType.Construction

/-!
# Language-Indexed OSLF Functor and Effective Structure

This module packages two related functorial transport layers.

The first is the established witness transport over
`LanguageMorphism _ _ Eq`:

- predicate pullback along language morphisms,
- identity/composition laws,
- modal witness transport via `preserves_diamond`.

The second gives the exact abstract categorical statement.  A map of
operational theories must preserve steps and lift both outgoing and incoming
steps at image states.  Such bounded maps make inverse image commute with
both OSLF modalities, and therefore induce a contravariant functor from
operational GSLTs to modal native predicate theories.

Native type theories are not assumed to be literally a syntactic subcategory
of GSLTs.  Given a separate reification functor, the reified native theories
form its essential image, and reified OSLF is ordinary functor composition.
Natural transformations compare two such constructions; OSLF itself is the
functor.
-/

namespace Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.LangMorphism
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open CategoryTheory
open scoped CategoryTheory

abbrev LanguageEqHom (L₁ L₂ : LanguageDef) := LanguageMorphism L₁ L₂ Eq

/-- Predicate pullback along a language morphism. -/
def predPullback {L₁ L₂ : LanguageDef}
    (m : LanguageEqHom L₁ L₂) :
    (Pattern → Prop) → (Pattern → Prop) :=
  fun ψ p => ψ (m.mapTerm p)

@[simp] theorem predPullback_id (L : LanguageDef) (ψ : Pattern → Prop) :
    predPullback (idLanguageMorphism L) ψ = ψ := by
  funext p
  rfl

@[simp] theorem predPullback_comp
    {L₁ L₂ L₃ : LanguageDef}
    (m₁₂ : LanguageEqHom L₁ L₂)
    (m₂₃ : LanguageEqHom L₂ L₃)
    (ψ : Pattern → Prop) :
    predPullback (composeLanguageMorphism m₁₂ m₂₃) ψ =
      predPullback m₁₂ (predPullback m₂₃ ψ) := by
  funext p
  rfl

/-- Minimal functor package for language-indexed predicate transport. -/
structure IndexedPredFunctor where
  mapHom : ∀ {L₁ L₂ : LanguageDef}, LanguageEqHom L₁ L₂ →
    ((Pattern → Prop) → (Pattern → Prop))
  map_id : ∀ (L : LanguageDef) (ψ : Pattern → Prop),
    mapHom (idLanguageMorphism L) ψ = ψ
  map_comp :
    ∀ {L₁ L₂ L₃ : LanguageDef}
      (m₁₂ : LanguageEqHom L₁ L₂)
      (m₂₃ : LanguageEqHom L₂ L₃)
      (ψ : Pattern → Prop),
      mapHom (composeLanguageMorphism m₁₂ m₂₃) ψ =
        mapHom m₁₂ (mapHom m₂₃ ψ)

/-- Canonical pullback functor on predicates induced by language morphisms. -/
def runtimePredicatePullbackFunctor : IndexedPredFunctor where
  mapHom := fun {_ _} m => predPullback m
  map_id := predPullback_id
  map_comp := predPullback_comp

/-- Diamond witness transport along an Eq-language morphism. -/
theorem diamond_witness_transport
    {L₁ L₂ : LanguageDef}
    (m : LanguageEqHom L₁ L₂)
    {φ : Pattern → Prop} {p : Pattern}
    (h : langDiamond L₁ φ p) :
    ∃ q, langReduces L₁ p q ∧ φ q ∧
      ∃ T, LangReducesStar L₂ (m.mapTerm p) T ∧ T = m.mapTerm q := by
  simpa using
    (LanguageMorphism.preserves_diamond (m := m) (φ := φ) (p := p) h)

/-- Composition-level form of diamond witness transport. -/
theorem diamond_witness_transport_comp
    {L₁ L₂ L₃ : LanguageDef}
    (m₁₂ : LanguageEqHom L₁ L₂)
    (m₂₃ : LanguageEqHom L₂ L₃)
    {φ : Pattern → Prop} {p : Pattern}
    (h : langDiamond L₁ φ p) :
    ∃ q, langReduces L₁ p q ∧ φ q ∧
      ∃ T, LangReducesStar L₃
        ((composeLanguageMorphism m₁₂ m₂₃).mapTerm p) T ∧
        T = (composeLanguageMorphism m₁₂ m₂₃).mapTerm q := by
  simpa using
    (LanguageMorphism.preserves_diamond
      (m := composeLanguageMorphism m₁₂ m₂₃)
      (φ := φ) (p := p) h)

/-! ## Exact modal operational morphisms

`CoveredTranslation` already supplies the outgoing back condition.  OSLF's
right adjoint is predecessor-universal, so exact box transport additionally
needs an incoming back condition.  Together these are the two legs of a
bounded morphism of the proposition-valued reduction graph.  They are
surjectivity-on-fibres, or weak-pullback, conditions for the source and target
legs of the reduction span.  Equivalence of proof fibres over fixed mapped
endpoints is strictly stronger than proposition-valued coverage there, but is
an independent axis from incoming coverage; it is handled separately by
`ExactTranslation`.
-/

universe uTerm uC vC uN vN uR vR

/-- A covered operational translation with local reflection of every target
step entering an image state.  Outgoing coverage controls diamond; incoming
coverage controls box. -/
structure ModalTranslation (source target : GSLT.{uTerm})
    extends CoveredTranslation source target where
  liftIncoming : ∀ {sourceTerm targetTerm},
    target.Step targetTerm (mapTerm sourceTerm) →
      ∃ sourcePredecessor,
        source.Step sourcePredecessor sourceTerm ∧
          mapTerm sourcePredecessor = targetTerm

namespace ModalTranslation

@[ext]
theorem ext {source target : GSLT.{uTerm}}
    {first second : ModalTranslation source target}
    (mapTerm : first.mapTerm = second.mapTerm) : first = second := by
  cases first with
  | mk firstCovered firstIncoming =>
      cases second with
      | mk secondCovered secondIncoming =>
          have coveredEq : firstCovered = secondCovered := by
            apply CoveredTranslation.ext
            exact mapTerm
          cases coveredEq
          rfl

/-- Identity is bounded in both directions. -/
def id (theory : GSLT.{uTerm}) : ModalTranslation theory theory where
  toCoveredTranslation := CoveredTranslation.id theory
  liftIncoming := by
    intro sourceTerm targetTerm step
    exact ⟨targetTerm, step, rfl⟩

/-- Bounded operational translations compose, retaining both lifted stages. -/
def comp {first middle last : GSLT.{uTerm}}
    (earlier : ModalTranslation first middle)
    (later : ModalTranslation middle last) :
    ModalTranslation first last where
  toCoveredTranslation :=
    earlier.toCoveredTranslation.comp later.toCoveredTranslation
  liftIncoming := by
    intro sourceTerm targetTerm step
    obtain ⟨middlePredecessor, middleStep, middleEq⟩ :=
      later.liftIncoming step
    obtain ⟨sourcePredecessor, sourceStep, sourceEq⟩ :=
      earlier.liftIncoming middleStep
    exact ⟨sourcePredecessor, sourceStep,
      (congrArg later.mapTerm sourceEq).trans middleEq⟩

end ModalTranslation

/-- The category on which exact modal OSLF transport is functorial. -/
structure ModallyCoveredTheory where
  theory : GSLT.{uTerm}

instance : CategoryTheory.Category ModallyCoveredTheory where
  Hom source target := ModalTranslation source.theory target.theory
  id source := ModalTranslation.id source.theory
  comp earlier later := earlier.comp later
  id_comp morphism := by
    apply ModalTranslation.ext
    rfl
  comp_id morphism := by
    apply ModalTranslation.ext
    rfl
  assoc first second third := by
    apply ModalTranslation.ext
    rfl

/-- Forget incoming coverage while retaining exact outgoing coverage. -/
def forgetIncoming :
    CategoryTheory.Functor ModallyCoveredTheory.{uTerm} CoveredTheory.{uTerm} where
  obj object := ⟨object.theory⟩
  map translation := translation.toCoveredTranslation
  map_id object := by
    apply CoveredTranslation.ext
    rfl
  map_comp earlier later := by
    apply CoveredTranslation.ext
    rfl

/-! ## The target category of modal native predicate theories -/

/-- The modal predicate fragment generated by the operational half of OSLF.
The richer spatial/fibred native-type construction is supplied separately by
`NativeType.nativeTypeFunctor`. -/
structure ModalPredicateTheory where
  State : Type uTerm
  diamond : Set State → Set State
  box : Set State → Set State
  galois : GaloisConnection diamond box

namespace ModalPredicateTheory

/-- A native-theory morphism maps predicates while commuting exactly with
both generated modalities. -/
structure Hom (source target : ModalPredicateTheory.{uTerm}) where
  mapPred : CompleteLatticeHom (Set source.State) (Set target.State)
  map_diamond : ∀ predicate,
    mapPred (source.diamond predicate) = target.diamond (mapPred predicate)
  map_box : ∀ predicate,
    mapPred (source.box predicate) = target.box (mapPred predicate)

namespace Hom

@[ext]
theorem ext {source target : ModalPredicateTheory.{uTerm}}
    {first second : Hom source target}
    (mapPred : first.mapPred = second.mapPred) : first = second := by
  cases first
  cases second
  cases mapPred
  rfl

def id (theory : ModalPredicateTheory.{uTerm}) : Hom theory theory where
  mapPred := CompleteLatticeHom.id _
  map_diamond := by intros; rfl
  map_box := by intros; rfl

def comp {first middle last : ModalPredicateTheory.{uTerm}}
    (earlier : Hom first middle) (later : Hom middle last) : Hom first last where
  mapPred := later.mapPred.comp earlier.mapPred
  map_diamond := by
    intro predicate
    change later.mapPred (earlier.mapPred (first.diamond predicate)) =
      last.diamond (later.mapPred (earlier.mapPred predicate))
    rw [earlier.map_diamond, later.map_diamond]
  map_box := by
    intro predicate
    change later.mapPred (earlier.mapPred (first.box predicate)) =
      last.box (later.mapPred (earlier.mapPred predicate))
    rw [earlier.map_box, later.map_box]

end Hom

instance : CategoryTheory.Category ModalPredicateTheory where
  Hom := Hom
  id := Hom.id
  comp earlier later := Hom.comp earlier later
  id_comp morphism := by
    apply Hom.ext
    rfl
  comp_id morphism := by
    apply Hom.ext
    rfl
  assoc first second third := by
    apply Hom.ext
    rfl

end ModalPredicateTheory

/-- The operational modal fragment generated by one abstract GSLT. -/
def oslfModalObject (theory : GSLT.{uTerm}) : ModalPredicateTheory.{uTerm} where
  State := theory.Term
  diamond := gsltDiamond theory
  box := gsltBox theory
  galois := gsltGalois theory

/-- The categorical modal object is a reduct of the existing `gsltOSLF`
construction, not a second semantics. -/
theorem oslfModalObject_agrees_gsltOSLF (theory : GSLT.{uTerm}) :
    (oslfModalObject theory).diamond = (gsltOSLF theory).diamond ∧
      (oslfModalObject theory).box = (gsltOSLF theory).box :=
  ⟨rfl, rfl⟩

namespace CoveredTranslation

/-- Outgoing coverage is precisely the equality needed for diamond
change-of-base. -/
theorem preimage_diamond {source target : GSLT.{uTerm}}
    (translation : CoveredTranslation source target)
    (predicate : Set target.Term) :
    Set.preimage translation.mapTerm (gsltDiamond target predicate) =
      gsltDiamond source (Set.preimage translation.mapTerm predicate) := by
  ext sourceTerm
  constructor
  · intro targetDiamond
    change gsltDiamond target predicate (translation.mapTerm sourceTerm) at targetDiamond
    obtain ⟨targetTerm, targetStep, targetMeaning⟩ :=
      (gsltDiamond_spec target predicate (translation.mapTerm sourceTerm)).mp
        targetDiamond
    obtain ⟨sourceTarget, sourceStep, targetEq⟩ :=
      translation.cover.liftStep targetStep
    apply (gsltDiamond_spec source
      (Set.preimage translation.mapTerm predicate) sourceTerm).mpr
    refine ⟨sourceTarget, sourceStep, ?_⟩
    change predicate (translation.mapTerm sourceTarget)
    simpa [targetEq] using targetMeaning
  · intro sourceDiamond
    change gsltDiamond source (Set.preimage translation.mapTerm predicate)
      sourceTerm at sourceDiamond
    obtain ⟨sourceTarget, sourceStep, targetMeaning⟩ :=
      (gsltDiamond_spec source
        (Set.preimage translation.mapTerm predicate) sourceTerm).mp sourceDiamond
    change gsltDiamond target predicate (translation.mapTerm sourceTerm)
    apply (gsltDiamond_spec target predicate
      (translation.mapTerm sourceTerm)).mpr
    exact ⟨translation.mapTerm sourceTarget,
      translation.cover.mapStep sourceStep, targetMeaning⟩

end CoveredTranslation

namespace OperationalTranslation

/-- Exact diamond change-of-base reconstructs the outgoing back condition.
Thus the target cannot hide an invented successor at an image state. -/
def coverOfDiamondCommutation {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target)
    (commutes : ∀ predicate : Set target.Term,
      Set.preimage translation.mapTerm (gsltDiamond target predicate) =
        gsltDiamond source (Set.preimage translation.mapTerm predicate)) :
    StepCover source target translation.mapTerm where
  mapStep := translation.mapStep
  liftStep := by
    intro sourceTerm targetTerm targetStep
    let predicate : Set target.Term := Set.singleton targetTerm
    have targetWitness :
        sourceTerm ∈ Set.preimage translation.mapTerm
          (gsltDiamond target predicate) := by
      change gsltDiamond target predicate (translation.mapTerm sourceTerm)
      exact (gsltDiamond_spec target predicate
        (translation.mapTerm sourceTerm)).mpr
          ⟨targetTerm, targetStep, Set.mem_singleton targetTerm⟩
    have sourceWitness :
        gsltDiamond source
          (Set.preimage translation.mapTerm predicate) sourceTerm := by
      rw [← commutes predicate]
      exact targetWitness
    obtain ⟨sourceTarget, sourceStep, imageInSingleton⟩ :=
      (gsltDiamond_spec source
        (Set.preimage translation.mapTerm predicate) sourceTerm).mp
          sourceWitness
    exact ⟨sourceTarget, sourceStep,
      Set.mem_singleton_iff.mp imageInSingleton⟩

/-- A forward operational translation commutes with every diamond exactly
iff it admits outgoing local coverage. -/
theorem diamondCommutation_iff_covered
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target) :
    (∀ predicate : Set target.Term,
      Set.preimage translation.mapTerm (gsltDiamond target predicate) =
        gsltDiamond source (Set.preimage translation.mapTerm predicate)) ↔
      Nonempty (StepCover source target translation.mapTerm) := by
  constructor
  · intro commutes
    exact ⟨coverOfDiamondCommutation translation commutes⟩
  · rintro ⟨cover⟩ predicate
    let covered : CoveredTranslation source target :=
      { mapTerm := translation.mapTerm
        mapEquiv := translation.mapEquiv
        cover := cover }
    exact LanguageIndexedModalFunctor.CoveredTranslation.preimage_diamond
      covered predicate

end OperationalTranslation

namespace ModalTranslation

/-- Incoming coverage is precisely the equality needed for box
change-of-base. -/
theorem preimage_box {source target : GSLT.{uTerm}}
    (translation : ModalTranslation source target)
    (predicate : Set target.Term) :
    Set.preimage translation.mapTerm (gsltBox target predicate) =
      gsltBox source (Set.preimage translation.mapTerm predicate) := by
  ext sourceTerm
  constructor
  · intro targetBox
    change gsltBox target predicate (translation.mapTerm sourceTerm) at targetBox
    apply (gsltBox_spec source
      (Set.preimage translation.mapTerm predicate) sourceTerm).mpr
    intro sourcePredecessor sourceStep
    exact (gsltBox_spec target predicate
      (translation.mapTerm sourceTerm)).mp targetBox
        (translation.mapTerm sourcePredecessor)
        (translation.cover.mapStep sourceStep)
  · intro sourceBox
    change gsltBox source (Set.preimage translation.mapTerm predicate)
      sourceTerm at sourceBox
    apply (gsltBox_spec target predicate
      (translation.mapTerm sourceTerm)).mpr
    intro targetPredecessor targetStep
    obtain ⟨sourcePredecessor, sourceStep, predecessorEq⟩ :=
      translation.liftIncoming targetStep
    have sourceMeaning :=
      (gsltBox_spec source (Set.preimage translation.mapTerm predicate)
        sourceTerm).mp sourceBox sourcePredecessor sourceStep
    change predicate (translation.mapTerm sourcePredecessor) at sourceMeaning
    simpa [predecessorEq] using sourceMeaning

end ModalTranslation

namespace CoveredTranslation

/-- Exact box change-of-base reconstructs the incoming back condition.  The
predicate used in the proof is the image of all authored predecessors. -/
theorem incomingCoverageOfBoxCommutation
    {source target : GSLT.{uTerm}}
    (translation : CoveredTranslation source target)
    (commutes : ∀ predicate : Set target.Term,
      Set.preimage translation.mapTerm (gsltBox target predicate) =
        gsltBox source (Set.preimage translation.mapTerm predicate)) :
    ∀ {sourceTerm targetTerm},
      target.Step targetTerm (translation.mapTerm sourceTerm) →
        ∃ sourcePredecessor,
          source.Step sourcePredecessor sourceTerm ∧
            translation.mapTerm sourcePredecessor = targetTerm := by
  intro sourceTerm targetTerm targetStep
  let predecessorImage : Set target.Term := fun candidate =>
    ∃ sourcePredecessor,
      source.Step sourcePredecessor sourceTerm ∧
        translation.mapTerm sourcePredecessor = candidate
  have sourceBox :
      gsltBox source
        (Set.preimage translation.mapTerm predecessorImage) sourceTerm := by
    apply (gsltBox_spec source
      (Set.preimage translation.mapTerm predecessorImage) sourceTerm).mpr
    intro sourcePredecessor sourceStep
    exact ⟨sourcePredecessor, sourceStep, rfl⟩
  have targetBox :
      gsltBox target predecessorImage
        (translation.mapTerm sourceTerm) := by
    have sourceMembership :
        gsltBox source
          (Set.preimage translation.mapTerm predecessorImage) sourceTerm := sourceBox
    rw [← commutes predecessorImage] at sourceMembership
    exact sourceMembership
  exact (gsltBox_spec target predecessorImage
    (translation.mapTerm sourceTerm)).mp targetBox targetTerm targetStep

/-- An outgoing-covered translation commutes with every box exactly iff it
also admits incoming local coverage. -/
theorem boxCommutation_iff_incomingCovered
    {source target : GSLT.{uTerm}}
    (translation : CoveredTranslation source target) :
    (∀ predicate : Set target.Term,
      Set.preimage translation.mapTerm (gsltBox target predicate) =
        gsltBox source (Set.preimage translation.mapTerm predicate)) ↔
      (∀ {sourceTerm targetTerm},
        target.Step targetTerm (translation.mapTerm sourceTerm) →
          ∃ sourcePredecessor,
            source.Step sourcePredecessor sourceTerm ∧
              translation.mapTerm sourcePredecessor = targetTerm) := by
  constructor
  · exact incomingCoverageOfBoxCommutation translation
  · intro incoming predicate
    let modal : ModalTranslation source target :=
      { toCoveredTranslation := translation
        liftIncoming := incoming }
    exact LanguageIndexedModalFunctor.ModalTranslation.preimage_box
      modal predicate

end CoveredTranslation

namespace OperationalTranslation

/-- Exact transport of both OSLF modalities is equivalent to extending the
forward translation to a bounded operational map.  This packages the two
separate back conditions into the categorical morphism used by
`oslfModalFunctor`. -/
theorem modalCommutation_iff_hasModalExtension
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target) :
    ((∀ predicate : Set target.Term,
        Set.preimage translation.mapTerm (gsltDiamond target predicate) =
          gsltDiamond source (Set.preimage translation.mapTerm predicate)) ∧
      (∀ predicate : Set target.Term,
        Set.preimage translation.mapTerm (gsltBox target predicate) =
          gsltBox source (Set.preimage translation.mapTerm predicate))) ↔
      ∃ modal : ModalTranslation source target,
        modal.toCoveredTranslation.toOperational = translation := by
  constructor
  · rintro ⟨diamondCommutes, boxCommutes⟩
    let covered : CoveredTranslation source target :=
      { mapTerm := translation.mapTerm
        mapEquiv := translation.mapEquiv
        cover :=
          LanguageIndexedModalFunctor.OperationalTranslation.coverOfDiamondCommutation
            translation diamondCommutes }
    let modal : ModalTranslation source target :=
      { toCoveredTranslation := covered
        liftIncoming :=
          LanguageIndexedModalFunctor.CoveredTranslation.incomingCoverageOfBoxCommutation
            covered boxCommutes }
    refine ⟨modal, ?_⟩
    apply Mettapedia.GSLT.IndexedOperational.OperationalTranslation.ext
    rfl
  · rintro ⟨modal, agrees⟩
    have mapAgrees : modal.mapTerm = translation.mapTerm :=
      congrArg OperationalTranslation.mapTerm agrees
    constructor
    · intro predicate
      simpa [mapAgrees] using
        (LanguageIndexedModalFunctor.CoveredTranslation.preimage_diamond
          modal.toCoveredTranslation predicate)
    · intro predicate
      simpa [mapAgrees] using
        (LanguageIndexedModalFunctor.ModalTranslation.preimage_box
          modal predicate)

end OperationalTranslation

namespace ModalTranslation

/-- Pullback along a bounded operational map is an exact modal native-theory
morphism. -/
def pullback {source target : GSLT.{uTerm}}
    (translation : ModalTranslation source target) :
    ModalPredicateTheory.Hom (oslfModalObject target) (oslfModalObject source) where
  mapPred := CompleteLatticeHom.setPreimage translation.mapTerm
  map_diamond := LanguageIndexedModalFunctor.CoveredTranslation.preimage_diamond
    translation.toCoveredTranslation
  map_box := LanguageIndexedModalFunctor.ModalTranslation.preimage_box translation

end ModalTranslation

/-- The exact operational part of OSLF is a contravariant functor.  The
variance is forced by predicate pullback. -/
def oslfModalFunctor :
    CategoryTheory.Functor
      (ModallyCoveredTheory.{uTerm})ᵒᵖ ModalPredicateTheory.{uTerm} where
  obj object := oslfModalObject object.unop.theory
  map translation := translation.unop.pullback
  map_id object := by
    apply ModalPredicateTheory.Hom.ext
    rfl
  map_comp earlier later := by
    apply ModalPredicateTheory.Hom.ext
    rfl

/-! ## Reification and the categorical status of native presentations -/

/-- If native theories are reified into a syntactic category, their exact
subcategory is the essential image of that reification functor. -/
abbrev ReifiedNativeTheory
    {Native : Type uN} {Reified : Type uR}
    [CategoryTheory.Category.{vN} Native]
    [CategoryTheory.Category.{vR} Reified]
    (reify : CategoryTheory.Functor Native Reified) :=
  reify.EssImageSubcategory

/-- The native-type categories generated by the established NTT functor form
its essential image in `Cat`; they are not literally a subcategory of GSLTs. -/
abbrev NativeTypeEssentialImage :=
  Mettapedia.OSLF.NativeType.nativeTypeFunctor.EssImageSubcategory

/-- Every native-type category generated from a lambda theory belongs to the
actual NTT functor's essential image. -/
theorem nativeType_obj_mem_essentialImage
    (theory : Mettapedia.CategoryTheory.LambdaTheories.LambdaTheory) :
    Mettapedia.OSLF.NativeType.nativeTypeFunctor.essImage
      (Mettapedia.OSLF.NativeType.nativeTypeFunctor.obj theory) :=
  CategoryTheory.Functor.obj_mem_essImage
    Mettapedia.OSLF.NativeType.nativeTypeFunctor theory

/-- Reifying an OSLF construction is ordinary composition of functors. -/
def reifiedOSLF
    {Source : Type uC} {Native : Type uN} {Reified : Type uR}
    [CategoryTheory.Category.{vC} Source]
    [CategoryTheory.Category.{vN} Native]
    [CategoryTheory.Category.{vR} Reified]
    (oslf : CategoryTheory.Functor Source Native)
    (reify : CategoryTheory.Functor Native Reified) :
    CategoryTheory.Functor Source Reified :=
  CategoryTheory.Functor.comp oslf reify

/-- Every reified OSLF object lies in the essential image of native-theory
reification.  No converse is claimed without an explicit reification
completeness theorem. -/
theorem reifiedOSLF_obj_mem_essentialImage
    {Source : Type uC} {Native : Type uN} {Reified : Type uR}
    [CategoryTheory.Category.{vC} Source]
    [CategoryTheory.Category.{vN} Native]
    [CategoryTheory.Category.{vR} Reified]
    (oslf : CategoryTheory.Functor Source Native)
    (reify : CategoryTheory.Functor Native Reified) (source : Source) :
    reify.essImage ((reifiedOSLF oslf reify).obj source) := by
  exact CategoryTheory.Functor.obj_mem_essImage reify (oslf.obj source)

/-- A natural transformation is the correct object for comparing two OSLF
constructions with the same source and target categories. -/
abbrev OSLFComparison
    {Source : Type uC} {Native : Type uN}
    [CategoryTheory.Category.{vC} Source]
    [CategoryTheory.Category.{vN} Native]
    (first second : CategoryTheory.Functor Source Native) :=
  first ⟶ second

/-! ## Proof-bearing effectiveness requirements for native kernels

OSLF generates semantics for every GSLT.  Execution requires additional
guest-owned structure.  The following interfaces state algorithms together
with exactness laws; they are not capability labels and confer no authority
by themselves.
-/

namespace EffectiveStructure

/-- An exact decision procedure for the one-step judgment. -/
structure StepDecision (theory : GSLT.{uTerm}) where
  decideStep : theory.Term → theory.Term → Bool
  correct : ∀ source target,
    decideStep source target = true ↔ theory.Step source target

/-- An exact decision procedure for authored structural equations. -/
structure EquationDecision (theory : GSLT.{uTerm}) where
  decideEquiv : theory.Term → theory.Term → Bool
  correct : ∀ left right,
    decideEquiv left right = true ↔ theory.Equiv left right

/-- A finite extensional enumeration of all one-step successors.  It does not
by itself retain multiple proof occurrences with equal endpoints. -/
structure SuccessorEnumeration (theory : GSLT.{uTerm}) where
  successors : theory.Term → List theory.Term
  mem_iff : ∀ source target,
    target ∈ successors source ↔ theory.Step source target

/-- A finite extensional enumeration of all one-step predecessors. -/
structure PredecessorEnumeration (theory : GSLT.{uTerm}) where
  predecessors : theory.Term → List theory.Term
  mem_iff : ∀ source target,
    source ∈ predecessors target ↔ theory.Step source target

/-- A canonicalizer whose equality test is sound and complete for the
authored equation relation. -/
structure CanonicalEquationNormalizer (theory : GSLT.{uTerm}) where
  normalize : theory.Term → theory.Term
  sound : ∀ term, theory.Equiv term (normalize term)
  complete : ∀ left right,
    theory.Equiv left right ↔ normalize left = normalize right

/-- An executable normalizer for operational reduction. -/
structure ReductionNormalizer (theory : GSLT.{uTerm}) where
  normalize : theory.Term → theory.Term
  reduces : ∀ term, theory.MultiStep term (normalize term)
  normal : ∀ term, theory.IsNormalForm (normalize term)
  unique : ∀ {term result}, theory.MultiStep term result →
    theory.IsNormalForm result → theory.Equiv result (normalize term)

/-- Closure laws required before a kernel may construct steps under the
guest's own contexts. -/
structure ContextualClosure (theory : GSLT.{uTerm})
    (Context : Type*) (plug : Context → theory.Term → theory.Term) where
  mapEquiv : ∀ context {left right}, theory.Equiv left right →
    theory.Equiv (plug context left) (plug context right)
  mapStep : ∀ context {source target}, theory.Step source target →
    theory.Step (plug context source) (plug context target)

/-- Closure laws required before a kernel may construct guest judgments after
substitution. -/
structure SubstitutionClosure (theory : GSLT.{uTerm})
    (Substitution : Type*)
    (applySubstitution : Substitution → theory.Term → theory.Term) where
  mapEquiv : ∀ substitution {left right}, theory.Equiv left right →
    theory.Equiv (applySubstitution substitution left)
      (applySubstitution substitution right)
  mapStep : ∀ substitution {source target}, theory.Step source target →
    theory.Step (applySubstitution substitution source)
      (applySubstitution substitution target)

namespace SuccessorEnumeration

/-- Exact finite successor enumeration yields a direct step decision whenever
term equality is decidable. -/
def toStepDecision {theory : GSLT.{uTerm}}
    (enumeration : SuccessorEnumeration theory)
    [DecidableEq theory.Term] : StepDecision theory where
  decideStep source target := decide (target ∈ enumeration.successors source)
  correct := by
    intro source target
    simp [enumeration.mem_iff]

end SuccessorEnumeration

namespace CanonicalEquationNormalizer

/-- A canonical equation normalizer yields exact equation decision whenever
normal-form equality is decidable. -/
def toEquationDecision {theory : GSLT.{uTerm}}
    (normalizer : CanonicalEquationNormalizer theory)
    [DecidableEq theory.Term] : EquationDecision theory where
  decideEquiv left right := decide (normalizer.normalize left = normalizer.normalize right)
  correct := by
    intro left right
    simp [normalizer.complete]

end CanonicalEquationNormalizer

/-- Exact endpoint semantics and proof-relevant semantics are separate
requirements.  A proof-relevant native implementation must be compared by an
`ExactTranslation`, not merely by equality of proposition-valued steps. -/
abbrev ProofRelevantRequirement :=
  Mettapedia.GSLT.ProofRelevantPresentation.ExactTranslation

end EffectiveStructure

/-! ## Positive and negative controls -/

namespace Canary

@[reducible] private def discreteUnit : GSLT where
  Term := Unit
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun _ _ => False
  rewrites_resp_left := by
    intro _ _ _ _ impossible
    exact impossible.elim
  rewrites_resp_right := by
    intro _ _ _ impossible _
    exact impossible.elim

@[reducible] private def outgoingExtra : GSLT where
  Term := Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => source = false ∧ target = true
  rewrites_resp_left := by
    intro source source' target sourceEq step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step targetEq
    subst target'
    exact step

/-- A forward-only map can ignore an invented outgoing target edge. -/
private def forwardToOutgoingExtra :
    OperationalTranslation discreteUnit outgoingExtra where
  mapTerm := fun _ => false
  mapEquiv := by
    intro left right equal
    cases left
    cases right
    rfl
  mapStep := by
    intro source target impossible
    exact impossible.elim

/-- Forward preservation alone does not make diamond commute with pullback. -/
theorem forward_only_does_not_preserve_diamond :
    Set.preimage forwardToOutgoingExtra.mapTerm
        (gsltDiamond outgoingExtra (Set.singleton true)) ≠
      gsltDiamond discreteUnit
        (Set.preimage forwardToOutgoingExtra.mapTerm (Set.singleton true)) := by
  intro equalSets
  have observed :
      () ∈ Set.preimage forwardToOutgoingExtra.mapTerm
        (gsltDiamond outgoingExtra (Set.singleton true)) := by
    change gsltDiamond outgoingExtra (Set.singleton true) false
    apply (gsltDiamond_spec outgoingExtra (Set.singleton true) false).mpr
    exact ⟨true, ⟨rfl, rfl⟩, Set.mem_singleton true⟩
  rw [equalSets] at observed
  change gsltDiamond discreteUnit
    (Set.preimage forwardToOutgoingExtra.mapTerm (Set.singleton true)) () at observed
  obtain ⟨target, impossible, _⟩ :=
    (gsltDiamond_spec discreteUnit _ ()).mp observed
  exact impossible.elim

@[reducible] private def incomingExtra : GSLT where
  Term := Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => source = true ∧ target = false
  rewrites_resp_left := by
    intro source source' target sourceEq step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step targetEq
    subst target'
    exact step

/-- Outgoing coverage alone can still miss an incoming target edge. -/
private def coveredToIncomingExtra :
    CoveredTranslation discreteUnit incomingExtra where
  mapTerm := fun _ => false
  mapEquiv := by
    intro left right equal
    cases left
    cases right
    rfl
  cover :=
    { mapStep := by
        intro source target impossible
        exact impossible.elim
      liftStep := by
        intro source target step
        exact (Bool.false_ne_true step.1).elim }

/-- Outgoing coverage is insufficient for exact box transport. -/
theorem outgoing_coverage_does_not_preserve_box :
    Set.preimage coveredToIncomingExtra.mapTerm
        (gsltBox incomingExtra (Set.singleton false)) ≠
      gsltBox discreteUnit
        (Set.preimage coveredToIncomingExtra.mapTerm (Set.singleton false)) := by
  intro equalSets
  have sourceBox :
      gsltBox discreteUnit
        (Set.preimage coveredToIncomingExtra.mapTerm (Set.singleton false)) () := by
    apply (gsltBox_spec discreteUnit _ ()).mpr
    intro source impossible
    exact impossible.elim
  rw [← equalSets] at sourceBox
  change gsltBox incomingExtra (Set.singleton false) false at sourceBox
  have trueIsFalse :=
    (gsltBox_spec incomingExtra (Set.singleton false) false).mp sourceBox
      true ⟨rfl, rfl⟩
  exact Bool.false_ne_true (Set.mem_singleton_iff.mp trueIsFalse).symm

/-- There is no incoming-complete extension of the same covered map. -/
theorem no_modal_extension_of_incoming_gap :
    ¬ ∃ translation : ModalTranslation discreteUnit incomingExtra,
      translation.mapTerm = coveredToIncomingExtra.mapTerm := by
  rintro ⟨translation, sameMap⟩
  have mappedUnit : translation.mapTerm () = false := by
    exact congrFun sameMap ()
  have targetStep : incomingExtra.Step true (translation.mapTerm ()) := by
    change true = true ∧ translation.mapTerm () = false
    exact ⟨rfl, mappedUnit⟩
  obtain ⟨sourcePredecessor, impossible, _⟩ :=
    translation.liftIncoming targetStep
  exact impossible.elim

@[reducible] private def completeNat : GSLT where
  Term := Nat
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun _ _ => True
  rewrites_resp_left := by
    intro source source' target sourceEq _
    subst source'
    exact ⟨target, trivial, rfl⟩
  rewrites_resp_right := by
    intros
    trivial

/-- The complete relation on naturals has an exact direct step decision. -/
def completeNatStepDecision : EffectiveStructure.StepDecision completeNat where
  decideStep _ _ := true
  correct := by
    intros
    simp [GSLT.Step]

/-- No finite list can enumerate all successors of one state in the complete
relation on naturals. -/
theorem completeNat_has_no_finite_successor_enumeration :
    ¬ Nonempty (EffectiveStructure.SuccessorEnumeration completeNat) := by
  rintro ⟨enumeration⟩
  let bound := (enumeration.successors 0).foldr max 0
  have member : bound + 1 ∈ enumeration.successors 0 :=
    (enumeration.mem_iff 0 (bound + 1)).mpr trivial
  have impossible : bound + 1 ≤ bound :=
    List.le_max_of_le' 0 member (le_refl (bound + 1))
  exact (Nat.not_succ_le_self bound) impossible

/-- Direct decision and finite relational search are genuinely distinct
kernel requirements. -/
theorem direct_decision_does_not_imply_finite_search :
    Nonempty (EffectiveStructure.StepDecision completeNat) ∧
      ¬ Nonempty (EffectiveStructure.SuccessorEnumeration completeNat) :=
  ⟨⟨completeNatStepDecision⟩, completeNat_has_no_finite_successor_enumeration⟩

end Canary

#print axioms CoveredTranslation.preimage_diamond
#print axioms OperationalTranslation.diamondCommutation_iff_covered
#print axioms ModalTranslation.preimage_box
#print axioms CoveredTranslation.boxCommutation_iff_incomingCovered
#print axioms OperationalTranslation.modalCommutation_iff_hasModalExtension
#print axioms oslfModalFunctor
#print axioms oslfModalObject_agrees_gsltOSLF
#print axioms nativeType_obj_mem_essentialImage
#print axioms reifiedOSLF_obj_mem_essentialImage
#print axioms Canary.forward_only_does_not_preserve_diamond
#print axioms Canary.outgoing_coverage_does_not_preserve_box
#print axioms Canary.completeNat_has_no_finite_successor_enumeration

end Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
