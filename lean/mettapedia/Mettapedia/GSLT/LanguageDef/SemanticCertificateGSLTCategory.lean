import Mettapedia.GSLT.LanguageDef.CompletenessSpectrum
import Mettapedia.GSLT.LanguageDef.CertificateGSLTInterpretation
import Mettapedia.GSLT.Core.Ultrainfinite

/-!
# Exact semantic CertificateGSLTs and their interpretations

The ordinary category of CertificateGSLT presentations remembers derivation-valued
rule interpretations but not the semantic meaning for which a presentation is
an authority.  This module defines the fixed-meaning category needed before a
filtered growth construction can claim to preserve proof authority.

Objects are validated presentations with two-sided adequacy for one independent
meaning.  Morphisms are derivation-valued interpretations whose judgment
encoding commutes exactly.  They transport proof objects forward.  Because
both endpoints are semantically exact, theorem *existence* is also reflected;
this does not manufacture a backward translation of proof objects.

This is one honest component of the richer authority category.  It does not
assert that filtered colimits exist or are created by the underlying CertificateGSLT
category, and therefore does not yet claim an `Ind` completion.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.Semantic

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CompletenessSpectrum

universe uClaim uTarget uThird uIndex

/-- A CertificateGSLT presentation with exact authority for a fixed independent
semantic meaning. -/
structure ExactObject (Claim : Type uClaim) (Meaning : Claim → Prop) where
  toCertificateGSLT : CertificateGSLT.Object
  adequacy : ExactJudgmentPresentation Claim Meaning toCertificateGSLT.presentation

namespace ExactObject

variable {Claim : Type uClaim} {Meaning : Claim → Prop}

/-- The judgment pattern used by this semantic presentation. -/
abbrev encode (object : ExactObject Claim Meaning) : Claim → Pattern :=
  object.adequacy.toJudgmentPresentationAdequacy.encode

/-- Exactness is the object-level theoremhood/meaning correspondence. -/
theorem derivation_iff_meaning (object : ExactObject Claim Meaning)
    (claim : Claim) :
    Nonempty (Derivation object.toCertificateGSLT.presentation (object.encode claim)) ↔
      Meaning claim := by
  constructor
  · exact object.adequacy.toJudgmentPresentationAdequacy.derivation_sound claim
  · exact object.adequacy.derivation_complete claim

/-- Any two exact presentations of the same meaning agree on theorem
existence, even before choosing an interpretation between their proof terms. -/
theorem theoremhood_iff (source target : ExactObject Claim Meaning)
    (claim : Claim) :
    Nonempty (Derivation source.toCertificateGSLT.presentation (source.encode claim)) ↔
      Nonempty (Derivation target.toCertificateGSLT.presentation (target.encode claim)) := by
  rw [source.derivation_iff_meaning, target.derivation_iff_meaning]

end ExactObject

/-! ## Semantic variance -/

/-- A theorem-preserving translation between two independently stated
meanings.  Reflection is deliberately not included: a translation may map a
source theory into a strictly stronger target theory. -/
structure MeaningTranslation
    {SourceClaim : Type uClaim} {TargetClaim : Type uTarget}
    (SourceMeaning : SourceClaim → Prop) (TargetMeaning : TargetClaim → Prop) where
  mapClaim : SourceClaim → TargetClaim
  preserves : ∀ claim, SourceMeaning claim → TargetMeaning (mapClaim claim)

namespace MeaningTranslation

variable {SourceClaim : Type uClaim} {TargetClaim : Type uTarget}
variable {ThirdClaim : Type uThird}
variable {SourceMeaning : SourceClaim → Prop} {TargetMeaning : TargetClaim → Prop}
variable {ThirdMeaning : ThirdClaim → Prop}

/-- Reflection says that the target adds no theorems on the image of the
translation.  It is independent of forward preservation. -/
def Reflects
    (translation : MeaningTranslation SourceMeaning TargetMeaning) : Prop :=
  ∀ claim, TargetMeaning (translation.mapClaim claim) → SourceMeaning claim

/-- Two-sided semantic exactness of a translation. -/
def Exact
    (translation : MeaningTranslation SourceMeaning TargetMeaning) : Prop :=
  Reflects translation

/-- Identity preserves and reflects meaning. -/
def id (Meaning : SourceClaim → Prop) : MeaningTranslation Meaning Meaning where
  mapClaim := fun claim => claim
  preserves := fun _ meaningful => meaningful

theorem id_reflects (Meaning : SourceClaim → Prop) :
    Reflects (id Meaning) :=
  fun _ meaningful => meaningful

/-- The composite of theorem-preserving translations is theorem-preserving. -/
def comp
    (first : MeaningTranslation SourceMeaning TargetMeaning)
    (second : MeaningTranslation TargetMeaning ThirdMeaning) :
    MeaningTranslation SourceMeaning ThirdMeaning where
  mapClaim := second.mapClaim ∘ first.mapClaim
  preserves := fun claim meaningful =>
    second.preserves (first.mapClaim claim) (first.preserves claim meaningful)

/-- Reflection composes independently of preservation. -/
theorem comp_reflects
    (first : MeaningTranslation SourceMeaning TargetMeaning)
    (second : MeaningTranslation TargetMeaning ThirdMeaning)
    (firstReflects : Reflects first) (secondReflects : Reflects second) :
    Reflects (comp first second) := by
  intro claim meaningful
  exact firstReflects claim (secondReflects (first.mapClaim claim) meaningful)

namespace Canary

/-- A small source meaning with exactly one meaningful Boolean claim. -/
def narrowMeaning (claim : Bool) : Prop := claim = true

/-- A strictly broader target meaning in which both Boolean claims hold. -/
def broadMeaning (_claim : Bool) : Prop := True

/-- Inclusion into a broader theory preserves every source theorem. -/
def broadening : MeaningTranslation narrowMeaning broadMeaning where
  mapClaim := fun claim => claim
  preserves := fun _ _ => True.intro

/-- Forward theorem preservation does not imply reflection. -/
theorem broadening_not_reflects : ¬ Reflects broadening := by
  intro reflects
  exact Bool.false_ne_true (reflects false True.intro)

end Canary

end MeaningTranslation

/-- A semantic morphism retains a derivation-valued rule interpretation and
requires the independently chosen claim encoding to commute exactly. -/
structure Morphism {Claim : Type uClaim} {Meaning : Claim → Prop}
    (source target : ExactObject Claim Meaning) where
  interpretation : Interpretation source.toCertificateGSLT target.toCertificateGSLT
  encode_commutes : ∀ claim, source.encode claim = target.encode claim

namespace Morphism

variable {Claim : Type uClaim} {Meaning : Claim → Prop}
variable {source middle target : ExactObject Claim Meaning}

/-- Identity retains every proof and every claim encoding. -/
def id (object : ExactObject Claim Meaning) : Morphism object object where
  interpretation := Interpretation.id object.toCertificateGSLT
  encode_commutes := fun _ => rfl

/-- Composition is recursive CertificateGSLT interpretation followed by equality of
the semantic claim encodings. -/
def comp (earlier : Morphism source middle) (later : Morphism middle target) :
    Morphism source target where
  interpretation := Interpretation.comp earlier.interpretation later.interpretation
  encode_commutes := fun claim =>
    (earlier.encode_commutes claim).trans (later.encode_commutes claim)

/-- Morphisms are determined by their proof interpretation; equality proofs
for encoding commutation are proof-irrelevant. -/
@[ext] theorem ext (first second : Morphism source target)
    (equal : first.interpretation = second.interpretation) :
    first = second := by
  cases first
  cases second
  cases equal
  rfl

/-- Transport a proof of an encoded semantic claim through an interpretation. -/
def mapClaimDerivation (morphism : Morphism source target) (claim : Claim)
    (derivation :
      Derivation source.toCertificateGSLT.presentation (source.encode claim)) :
    Derivation target.toCertificateGSLT.presentation (target.encode claim) :=
  morphism.encode_commutes claim ▸
    morphism.interpretation.mapDerivation derivation

/-- Forward proof transport preserves theoremhood with the proof term retained. -/
theorem maps_theoremhood (morphism : Morphism source target) (claim : Claim) :
    Nonempty (Derivation source.toCertificateGSLT.presentation (source.encode claim)) →
      Nonempty (Derivation target.toCertificateGSLT.presentation (target.encode claim)) := by
  rintro ⟨derivation⟩
  exact ⟨morphism.mapClaimDerivation claim derivation⟩

/-- Semantic exactness reflects theorem existence across a morphism.  This is
weaker than a backward proof translation: the source witness is reconstructed
from semantic completeness rather than extracted from the target proof. -/
theorem theoremhood_iff (_morphism : Morphism source target) (claim : Claim) :
    Nonempty (Derivation source.toCertificateGSLT.presentation (source.encode claim)) ↔
      Nonempty (Derivation target.toCertificateGSLT.presentation (target.encode claim)) :=
  source.theoremhood_iff target claim

end Morphism

/-- Exact semantic presentations and encoding-preserving interpretations form
a genuine category. -/
instance {Claim : Type uClaim} {Meaning : Claim → Prop} :
    CategoryTheory.Category (ExactObject Claim Meaning) where
  Hom := Morphism
  id := Morphism.id
  comp := Morphism.comp
  id_comp morphism := by
    apply Morphism.ext
    apply Interpretation.ext
    intro ruleInstance premises conclusion application
    simp only [Morphism.comp, Morphism.id, Interpretation.comp,
      Interpretation.mapOpen, Interpretation.id]
    rw [Interpretation.mapOpenList_assumptionEnvironment,
      OpenDerivation.bind_assumptionEnvironment]
  comp_id morphism := by
    apply Morphism.ext
    apply Interpretation.ext
    intro ruleInstance premises conclusion application
    exact Interpretation.id_mapOpen
      (morphism.interpretation.onRule ruleInstance application)
  assoc first second third := by
    apply Morphism.ext
    apply Interpretation.ext
    intro ruleInstance premises conclusion application
    exact (Interpretation.comp_mapOpen second.interpretation third.interpretation
      (first.interpretation.onRule ruleInstance application)).symm

/-! ## The total category over varying meanings -/

namespace Total

/-- An exact proof authority together with its own claim language and
independent semantic meaning. -/
structure Object where
  Claim : Type uClaim
  Meaning : Claim → Prop
  toCertificateGSLT : CertificateGSLT.Object
  adequacy : ExactJudgmentPresentation Claim Meaning toCertificateGSLT.presentation

namespace Object

/-- The claim encoding selected by an exact authority. -/
abbrev encode (object : Object) : object.Claim → Pattern :=
  object.adequacy.toJudgmentPresentationAdequacy.encode

/-- Object exactness identifies derivability and meaning. -/
theorem derivation_iff_meaning (object : Object) (claim : object.Claim) :
    Nonempty (Derivation object.toCertificateGSLT.presentation (object.encode claim)) ↔
      object.Meaning claim := by
  constructor
  · exact object.adequacy.toJudgmentPresentationAdequacy.derivation_sound claim
  · exact object.adequacy.derivation_complete claim

end Object

/-- A total semantic morphism maps claims and recursively maps proof objects.
The encoding square must commute.  Meaning preservation is derived below from
the two exactness theorems; it is not an additional trusted field. -/
structure Morphism (source target : Object.{uClaim}) where
  mapClaim : source.Claim → target.Claim
  interpretation : Interpretation source.toCertificateGSLT target.toCertificateGSLT
  encode_commutes : ∀ claim, source.encode claim = target.encode (mapClaim claim)

namespace Morphism

variable {source middle target : Object.{uClaim}}

/-- Identity maps both claims and proof objects identically. -/
def id (object : Object.{uClaim}) : Morphism object object where
  mapClaim := fun claim => claim
  interpretation := Interpretation.id object.toCertificateGSLT
  encode_commutes := fun _ => rfl

/-- Composition maps claims and recursively substitutes proof interpretations. -/
def comp (first : Morphism source middle) (second : Morphism middle target) :
    Morphism source target where
  mapClaim := second.mapClaim ∘ first.mapClaim
  interpretation := Interpretation.comp first.interpretation second.interpretation
  encode_commutes := fun claim =>
    (first.encode_commutes claim).trans
      (second.encode_commutes (first.mapClaim claim))

/-- Total morphisms are determined by their claim map and proof
interpretation. -/
@[ext] theorem ext (first second : Morphism source target)
    (claimMapEqual : first.mapClaim = second.mapClaim)
    (interpretationEqual : first.interpretation = second.interpretation) :
    first = second := by
  cases first
  cases second
  cases claimMapEqual
  cases interpretationEqual
  rfl

/-- Transport a proof of a source claim to a proof of its translated target
claim. -/
def mapClaimDerivation (morphism : Morphism source target)
    (claim : source.Claim)
    (derivation :
      Derivation source.toCertificateGSLT.presentation (source.encode claim)) :
    Derivation target.toCertificateGSLT.presentation
      (target.encode (morphism.mapClaim claim)) :=
  morphism.encode_commutes claim ▸
    morphism.interpretation.mapDerivation derivation

/-- Meaning preservation is forced by exact source/target authorities and the
proof translation. -/
theorem preservesMeaning (morphism : Morphism source target)
    (claim : source.Claim) :
    source.Meaning claim → target.Meaning (morphism.mapClaim claim) := by
  intro meaningful
  obtain ⟨derivation⟩ :=
    source.adequacy.derivation_complete claim meaningful
  exact target.adequacy.toJudgmentPresentationAdequacy.derivation_sound
    (morphism.mapClaim claim)
    ⟨morphism.mapClaimDerivation claim derivation⟩

/-- Every total morphism projects to a theorem-preserving semantic
translation. -/
def toMeaningTranslation (morphism : Morphism source target) :
    MeaningTranslation source.Meaning target.Meaning where
  mapClaim := morphism.mapClaim
  preserves := morphism.preservesMeaning

/-- Reflection remains an explicit property of a total morphism. -/
def Reflects (morphism : Morphism source target) : Prop :=
  MeaningTranslation.Reflects morphism.toMeaningTranslation

/-- A reflecting total morphism gives two-sided theorem-existence
correspondence on translated claims. -/
theorem theoremhood_iff_of_reflects (morphism : Morphism source target)
    (reflects : morphism.Reflects) (claim : source.Claim) :
    Nonempty (Derivation source.toCertificateGSLT.presentation (source.encode claim)) ↔
      Nonempty (Derivation target.toCertificateGSLT.presentation
        (target.encode (morphism.mapClaim claim))) := by
  constructor
  · rintro ⟨derivation⟩
    exact ⟨morphism.mapClaimDerivation claim derivation⟩
  · intro targetDerivation
    exact source.adequacy.derivation_complete claim
      (reflects claim
        (target.adequacy.toJudgmentPresentationAdequacy.derivation_sound
          (morphism.mapClaim claim) targetDerivation))

end Morphism

/-- Exact authorities over varying meanings and theorem-preserving proof
translations form a category. -/
instance : CategoryTheory.Category (Object.{uClaim}) where
  Hom := Morphism
  id := Morphism.id
  comp := Morphism.comp
  id_comp morphism := by
    apply Morphism.ext
    · rfl
    · apply Interpretation.ext
      intro ruleInstance premises conclusion application
      simp only [Morphism.comp, Morphism.id, Interpretation.comp,
        Interpretation.mapOpen, Interpretation.id]
      rw [Interpretation.mapOpenList_assumptionEnvironment,
        OpenDerivation.bind_assumptionEnvironment]
  comp_id morphism := by
    apply Morphism.ext
    · rfl
    · apply Interpretation.ext
      intro ruleInstance premises conclusion application
      exact Interpretation.id_mapOpen
        (morphism.interpretation.onRule ruleInstance application)
  assoc first second third := by
    apply Morphism.ext
    · rfl
    · apply Interpretation.ext
      intro ruleInstance premises conclusion application
      exact (Interpretation.comp_mapOpen second.interpretation third.interpretation
        (first.interpretation.onRule ruleInstance application)).symm

end Total

/-! ## Filtered growth inside the authority-preserving category -/

namespace Filtered

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory

variable {Claim : Type uClaim} {Meaning : Claim → Prop}

/-- A filtered growth presentation whose stages and apex all carry exact
authority for the same meaning.  This specializes the existing abstract
filtered-growth object to the authority-preserving category; it does not assert
that such colimits exist or are created by forgetting semantic structure. -/
abbrev Growth
    {Index : Type uIndex} [CategoryTheory.SmallCategory Index]
    [CategoryTheory.IsFiltered Index]
    (stages : CategoryTheory.Functor Index (ExactObject Claim Meaning)) :=
  Mettapedia.GSLT.Ultrainfinite.FilteredGrowth stages

/-- Any colimit already constructed in the exact semantic category has an apex
with exact theoremhood/meaning correspondence. -/
theorem apex_derivation_iff_meaning
    {Index : Type uIndex} [CategoryTheory.SmallCategory Index]
    [CategoryTheory.IsFiltered Index]
    {stages : CategoryTheory.Functor Index (ExactObject Claim Meaning)}
    (growth : Growth stages) (claim : Claim) :
    Nonempty
        (Derivation growth.cocone.pt.toCertificateGSLT.presentation
          (growth.cocone.pt.encode claim)) ↔
      Meaning claim :=
  growth.cocone.pt.derivation_iff_meaning claim

/-- Every map from a finitely presentable semantic authority factors through
one finite stage of a supplied filtered colimit. -/
theorem compact_factor
    {Index : Type uIndex} [CategoryTheory.SmallCategory Index]
    [CategoryTheory.IsFiltered Index]
    {stages : CategoryTheory.Functor Index (ExactObject Claim Meaning)}
    (growth : Growth stages)
    {probe : ExactObject Claim Meaning}
    [CategoryTheory.IsFinitelyPresentable.{uIndex} probe]
    (map : Morphism probe growth.cocone.pt) :
    ∃ (stage : Index) (through : Morphism probe (stages.obj stage)),
      CategoryTheory.CategoryStruct.comp through (growth.cocone.ι.app stage) = map :=
  Mettapedia.GSLT.Ultrainfinite.FilteredGrowth.compact_factor growth map

end Filtered

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.Semantic
