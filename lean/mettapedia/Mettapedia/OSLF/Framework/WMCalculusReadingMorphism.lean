import Mettapedia.OSLF.Framework.WMCalculusNativeObservation
import Mettapedia.OSLF.Framework.WMCalculusNativeAnswers

/-!
# Morphisms of world-model readings and native observations

A map between readings preserves the three sorts and the operations of the
authored WM calculus. The resulting denotation square commutes for every
sorted term. Native observations are natural in such maps: pulling an
observation back along the semantic map gives exactly the same predicate on
encoded programs.

Behavioral agreement is subtler. Agreement in the source tests every source
query, so its image agrees at every target query only when the query map
covers all target queries. This coverage is stated explicitly rather than
silently identifying the two observational quotients.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusReadingMorphism

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.LanguagePresheafSharing
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusNativeObservation
open Mettapedia.OSLF.Framework.WMCalculusNativeAnswers
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.PresheafNativeType

private abbrev wmLanguage : LanguageDef :=
  wmExtVertexLanguageDefWithCong wmExtVertexMinimal

/-- A homomorphism of the full sorted WM-reading signature. The valuations
are part of the commuting data, so this also relates actual named programs. -/
structure ReadingMorphism
    {State₁ Query₁ V₁ State₂ Query₂ V₂ : Type}
    (source : WMReading State₁ Query₁ V₁)
    (target : WMReading State₂ Query₂ V₂) where
  mapState : State₁ → State₂
  mapQuery : Query₁ → Query₂
  mapEvidence : V₁ → V₂
  revise_comm : ∀ a b,
    mapState (source.revise a b) =
      target.revise (mapState a) (mapState b)
  extract_comm : ∀ a q,
    mapEvidence (source.extract a q) =
      target.extract (mapState a) (mapQuery q)
  combine_comm : ∀ a b,
    mapEvidence (source.combine a b) =
      target.combine (mapEvidence a) (mapEvidence b)
  zero_comm : mapEvidence source.zero = target.zero
  world_comm : ∀ name, mapState (source.world name) = target.world name
  query_comm : ∀ name, mapQuery (source.query name) = target.query name

namespace ReadingMorphism

/-- A reading morphism is determined by its three sorted carrier maps;
the operation laws are propositions and carry no extra identity data. -/
theorem ext
    {S₁ Q₁ V₁ S₂ Q₂ V₂ : Type}
    {source : WMReading S₁ Q₁ V₁}
    {target : WMReading S₂ Q₂ V₂}
    (first second : ReadingMorphism source target)
    (state : first.mapState = second.mapState)
    (query : first.mapQuery = second.mapQuery)
    (evidence : first.mapEvidence = second.mapEvidence) :
    first = second := by
  cases first
  cases second
  cases state
  cases query
  cases evidence
  rfl

/-- Identity interpretation of a WM reading. -/
def id {State Query V : Type} (reading : WMReading State Query V) :
    ReadingMorphism reading reading where
  mapState := _root_.id
  mapQuery := _root_.id
  mapEvidence := _root_.id
  revise_comm _ _ := rfl
  extract_comm _ _ := rfl
  combine_comm _ _ := rfl
  zero_comm := rfl
  world_comm _ := rfl
  query_comm _ := rfl

/-- Composable semantic interpretations remain an interpretation of the
same authored WM syntax. -/
def comp
    {S₁ Q₁ V₁ S₂ Q₂ V₂ S₃ Q₃ V₃ : Type}
    {first : WMReading S₁ Q₁ V₁}
    {middle : WMReading S₂ Q₂ V₂}
    {last : WMReading S₃ Q₃ V₃}
    (f : ReadingMorphism first middle)
    (g : ReadingMorphism middle last) :
    ReadingMorphism first last where
  mapState := g.mapState ∘ f.mapState
  mapQuery := g.mapQuery ∘ f.mapQuery
  mapEvidence := g.mapEvidence ∘ f.mapEvidence
  revise_comm a b := by
    simp only [Function.comp_apply, f.revise_comm, g.revise_comm]
  extract_comm a q := by
    simp only [Function.comp_apply, f.extract_comm, g.extract_comm]
  combine_comm a b := by
    simp only [Function.comp_apply, f.combine_comm, g.combine_comm]
  zero_comm := by
    simp only [Function.comp_apply, f.zero_comm, g.zero_comm]
  world_comm name := by
    simp only [Function.comp_apply, f.world_comm, g.world_comm]
  query_comm name := by
    simp only [Function.comp_apply, f.query_comm, g.query_comm]

variable {State₁ Query₁ V₁ State₂ Query₂ V₂ : Type}
  {source : WMReading State₁ Query₁ V₁}
  {target : WMReading State₂ Query₂ V₂}
  (hom : ReadingMorphism source target)

/-- The semantic map for each sort. -/
def mapValue : (s : WMSort) →
    SortValue State₁ Query₁ V₁ s → SortValue State₂ Query₂ V₂ s
  | .state => hom.mapState
  | .query => hom.mapQuery
  | .evidence => hom.mapEvidence

/-- Interpretation of every typed WM program commutes with the reading
morphism, including nested revision and extraction. -/
theorem denote_map : ∀ {s : WMSort} (term : WMTerm s),
    hom.mapValue s (source.denote term) = target.denote term
  | _, .state name => hom.world_comm name
  | _, .query name => hom.query_comm name
  | _, .revise first second => by
      change hom.mapState (source.revise (source.denote first) (source.denote second)) =
        target.revise (target.denote first) (target.denote second)
      have first_map : hom.mapState (source.denote first) = target.denote first := by
        simpa only [mapValue] using (denote_map first)
      have second_map : hom.mapState (source.denote second) = target.denote second := by
        simpa only [mapValue] using (denote_map second)
      rw [hom.revise_comm, first_map, second_map]
  | _, .extract state query => by
      change hom.mapEvidence (source.extract (source.denote state) (source.denote query)) =
        target.extract (target.denote state) (target.denote query)
      have state_map : hom.mapState (source.denote state) = target.denote state := by
        simpa only [mapValue] using (denote_map state)
      have query_map : hom.mapQuery (source.denote query) = target.denote query := by
        simpa only [mapValue] using (denote_map query)
      rw [hom.extract_comm, state_map, query_map]
  | _, .combine first second => by
      change hom.mapEvidence (source.combine (source.denote first) (source.denote second)) =
        target.combine (target.denote first) (target.denote second)
      have first_map : hom.mapEvidence (source.denote first) = target.denote first := by
        simpa only [mapValue] using (denote_map first)
      have second_map : hom.mapEvidence (source.denote second) = target.denote second := by
        simpa only [mapValue] using (denote_map second)
      rw [hom.combine_comm, first_map, second_map]
  | _, .zero => hom.zero_comm

/-- A target observation pulled back along a reading morphism is the very
same native subfunctor on the authored program presheaf. This is stronger
than merely transporting its truth on named atoms. -/
theorem observationPredicate_map (s : WMSort)
    (P : SortValue State₂ Query₂ V₂ s → Prop) :
    observationPredicate source s (fun value => P (hom.mapValue s value)) =
      observationPredicate target s P := by
  ext X program
  constructor
  · rintro ⟨term, encoded, observed⟩
    exact ⟨term, encoded, by simpa only [hom.denote_map] using observed⟩
  · rintro ⟨term, encoded, observed⟩
    exact ⟨term, encoded, by simpa only [hom.denote_map] using observed⟩

/-- The same naturality equality holds at the object level of the full
native predicate fibration. -/
theorem observationNativeType_map (s : WMSort)
    (P : SortValue State₂ Query₂ V₂ s → Prop) :
    observationNativeType source s (fun value => P (hom.mapValue s value)) =
      observationNativeType target s P := by
  unfold observationNativeType
  rw [hom.observationPredicate_map]

/-- Naturality also survives dependent reindexing along a generalized
program in an arbitrary presheaf context. -/
theorem observationInContext_map (s : WMSort)
    (P : SortValue State₂ Query₂ V₂ s → Prop)
    {Γ : languagePresheafObj wmLanguage}
    (program : Γ ⟶ languageProgramObj wmLanguage) :
    observationInContext source s
      (fun value => P (hom.mapValue s value)) Γ program =
        observationInContext target s P Γ program := by
  unfold observationInContext
  rw [hom.observationPredicate_map]

/-- The semantic map on state-query contexts. -/
def stateQueryMap :
    stateQueryObj State₁ Query₁ ⟶ stateQueryObj State₂ Query₂ where
  app X := TypeCat.ofHom (fun pair =>
    (hom.mapState pair.1, hom.mapQuery pair.2))
  naturality := by
    intro X Y f
    rfl

/-- A reading morphism transports genuine inhabitants of the dependent
answer graph. The evidence coordinate is justified by `extract_comm`. -/
def answerGraphMap :
    (evidenceGraph source).toFunctor ⟶ (evidenceGraph target).toFunctor where
  app X := TypeCat.ofHom (fun answer =>
    ⟨((hom.mapState answer.1.1.1, hom.mapQuery answer.1.1.2),
        hom.mapEvidence answer.1.2),
      by
        change target.extract (hom.mapState answer.1.1.1)
          (hom.mapQuery answer.1.1.2) = hom.mapEvidence answer.1.2
        rw [← hom.extract_comm, answer.2]⟩)
  naturality := by
    intro X Y f
    apply ConcreteCategory.hom_injective
    apply TypeCat.Fun.ext
    funext answer
    apply Subtype.ext
    rfl

/-- Mapping an admissible answer and then forgetting its evidence is the
same as first forgetting evidence and mapping the state-query context. -/
theorem answerGraphMap_projection :
    hom.answerGraphMap ≫ graphToStateQuery target =
      graphToStateQuery source ≫ hom.stateQueryMap := by
  ext X answer
  rfl

/-- Mapping the extracted answer equals extracting after mapping the
state-query pair. This is the dependent-section naturality square. -/
theorem answerGraphMap_section :
    hom.stateQueryMap ≫ answerSection target =
      answerSection source ≫ hom.answerGraphMap := by
  ext X pair
  apply Subtype.ext
  exact congrArg (Prod.mk (hom.mapState pair.1, hom.mapQuery pair.2))
    (hom.extract_comm pair.1 pair.2).symm

/-- The dependent graph construction respects identity reading maps. -/
theorem answerGraphMap_id {State Query V : Type}
    (reading : WMReading State Query V) :
    (ReadingMorphism.id reading).answerGraphMap =
      𝟙 (evidenceGraph reading).toFunctor := by
  ext X answer
  apply Subtype.ext
  rfl

/-- The dependent graph construction also respects composition of
reading maps, so plugin chains transport answer inhabitants coherently. -/
theorem answerGraphMap_comp
    {S₃ Q₃ V₃ : Type} {third : WMReading S₃ Q₃ V₃}
    (next : ReadingMorphism target third) :
    (ReadingMorphism.comp hom next).answerGraphMap =
      hom.answerGraphMap ≫ next.answerGraphMap := by
  ext X answer
  apply Subtype.ext
  rfl

/-- Agreement is preserved by a reading morphism whose query map covers
every target query. No injectivity of evidence or state maps is required. -/
theorem agree_map (query_surjective : Function.Surjective hom.mapQuery) :
    ∀ (s : WMSort) {a b : SortValue State₁ Query₁ V₁ s},
      source.Agree s a b →
        target.Agree s (hom.mapValue s a) (hom.mapValue s b) := by
  intro s a b agree
  cases s with
  | state =>
      intro targetQuery
      obtain ⟨query, rfl⟩ := query_surjective targetQuery
      change target.extract (hom.mapState a) (hom.mapQuery query) =
        target.extract (hom.mapState b) (hom.mapQuery query)
      rw [← hom.extract_comm, ← hom.extract_comm, agree query]
  | query =>
      exact congrArg hom.mapQuery agree
  | evidence =>
      exact congrArg hom.mapEvidence agree

/-- Conversely, target agreement reflects source agreement when the query
and evidence maps distinguish their respective values. State reflection
uses evidence injectivity; it does not require target-query coverage. -/
theorem agree_reflect
    (query_injective : Function.Injective hom.mapQuery)
    (evidence_injective : Function.Injective hom.mapEvidence) :
    ∀ (s : WMSort) {a b : SortValue State₁ Query₁ V₁ s},
      target.Agree s (hom.mapValue s a) (hom.mapValue s b) →
        source.Agree s a b := by
  intro s a b agree
  cases s with
  | state =>
      intro query
      apply evidence_injective
      rw [hom.extract_comm, hom.extract_comm]
      exact agree (hom.mapQuery query)
  | query =>
      exact query_injective agree
  | evidence =>
      exact evidence_injective agree

/-- The observational quotients correspond exactly when the query map is
bijective and the evidence map is injective; literal state equality is not
asserted. -/
theorem agree_iff
    (query_surjective : Function.Surjective hom.mapQuery)
    (query_injective : Function.Injective hom.mapQuery)
    (evidence_injective : Function.Injective hom.mapEvidence)
    (s : WMSort) (a b : SortValue State₁ Query₁ V₁ s) :
    source.Agree s a b ↔
      target.Agree s (hom.mapValue s a) (hom.mapValue s b) :=
  ⟨hom.agree_map query_surjective s,
    hom.agree_reflect query_injective evidence_injective s⟩

/-- Query coverage is precisely the extra condition making invariance of
target observations pull back to source observations. -/
theorem observationInvariant_pullback
    (query_surjective : Function.Surjective hom.mapQuery)
    (s : WMSort) (P : SortValue State₂ Query₂ V₂ s → Prop)
    (stable : ObservationInvariant target s P) :
    ObservationInvariant source s
      (fun value => P (hom.mapValue s value)) := by
  intro a b agree observed
  exact stable _ _ (hom.agree_map query_surjective s agree) observed

end ReadingMorphism

namespace QueryCoverageControl

/-- A source that can ask only one uninformative query. -/
private def narrow : WMReading Bool Unit Bool where
  revise := (· || ·)
  extract := fun _ _ => false
  combine := (· || ·)
  zero := false
  world := fun _ => false
  query := fun _ => ()

/-- The target has a second query that can distinguish the two states. -/
private def wide : WMReading Bool Bool Bool where
  revise := (· || ·)
  extract := fun state query => state && query
  combine := (· || ·)
  zero := false
  world := fun _ => false
  query := fun _ => false

/-- Both readings obey the same WM-calculus core laws. -/
private theorem narrow_coreLaws : narrow.CoreLaws where
  extract_revise := by intros; rfl
  combine_comm := by intro a b; cases a <;> cases b <;> rfl
  combine_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  combine_zero := by intro a; cases a <;> rfl

private theorem wide_coreLaws : wide.CoreLaws where
  extract_revise := by
    intro a b query
    cases a <;> cases b <;> cases query <;> rfl
  combine_comm := by intro a b; cases a <;> cases b <;> rfl
  combine_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  combine_zero := by intro a; cases a <;> rfl

/-- The operation-preserving map exposes only the target's `false` query. -/
private def inclusion : ReadingMorphism narrow wide where
  mapState := _root_.id
  mapQuery := fun _ => false
  mapEvidence := _root_.id
  revise_comm _ _ := rfl
  extract_comm := by intro a query; cases a <;> cases query <;> rfl
  combine_comm _ _ := rfl
  zero_comm := rfl
  world_comm _ := rfl
  query_comm _ := rfl

/-- A valid morphism between lawful WM readings need not carry source
state agreement to target state agreement if target queries are not covered. -/
theorem agreement_not_preserved_without_query_coverage :
    ¬ (∀ a b : Bool, narrow.Agree .state a b →
      wide.Agree .state
        (inclusion.mapValue .state a) (inclusion.mapValue .state b)) := by
  intro preserves
  have sourceAgree : narrow.Agree .state true false := by
    intro query
    cases query
    rfl
  have targetAgree := preserves true false sourceAgree
  have contradiction := targetAgree true
  cases contradiction

end QueryCoverageControl

end Mettapedia.OSLF.Framework.WMCalculusReadingMorphism
