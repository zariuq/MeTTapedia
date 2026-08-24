import Mettapedia.Languages.MeTTa.PureKernel.Universe.IntrinsicMILSemanticAdequacy
import Mettapedia.Languages.MeTTa.PureKernel.Universe.RelationalEvidence
import Mettapedia.GSLT.LanguageDef.NIKRepresentedRouteObservation

/-!
# Exact finite native search for intrinsic relational hypotheses

A proof-relevant relation is not compiled by pretending it is a function from
sources to targets.  The native operation for a finite relation fibre maps a
typed source query to the complete occurrence bag of dependent answers
`Sigma target, evidence source target`.

`FiniteEvidenceFibre` is the capability that justifies this operation.  Its
finite index is equivalent to the complete dependent evidence fibre, so
materialization contains every semantic derivation exactly once.  The
capability composes under relational `Chain` by dependent Sigma: a composite
index retains the earlier occurrence and an index into the later fibre at its
exact intermediate target.

Intrinsic hypothesis programs consume this generic capability downstream.
Their native typing derivation and authored chain tree remain separate from
the provider, while NIK may retain the resulting represented query operation
at one dependency revision.  Relations without such a finite capability
remain meaningful and executable relationally.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe
namespace IntrinsicMILNativeSearch

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.GSLTIL.RouteEquipment
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKObservedRefinement
open Mettapedia.GSLT.Dynamics
open RelationalInternalLanguage.Semantic
open RelationalEvidence
open Presentation

universe u

abbrev ProofRel := RelationalInternalLanguage.Semantic.Rel

/-! ## Exact finite evidence fibres -/

/-- A finite index naming every target/derivation occurrence for one source.
The equivalence, rather than a mere support-completeness proposition, is what
retains proof multiplicity. -/
structure FiniteEvidenceFibre {Source Target : Type u}
    (relation : ProofRel Source Target) (source : Source) where
  Index : Type u
  indexFintype : Fintype Index
  occurrenceEquiv : Index ≃ AnswerOccurrence relation source

attribute [instance] FiniteEvidenceFibre.indexFintype

namespace FiniteEvidenceFibre

/-- Materialize the exact finite fibre as an unordered occurrence bag. -/
noncomputable def answers {Source Target : Type u}
    {relation : ProofRel Source Target} {source : Source}
    (fibre : FiniteEvidenceFibre relation source) :
    AnswerBag relation source := by
  classical
  exact (Finset.univ : Finset fibre.Index).1.map fibre.occurrenceEquiv

@[simp] theorem card_answers {Source Target : Type u}
    {relation : ProofRel Source Target} {source : Source}
    (fibre : FiniteEvidenceFibre relation source) :
    fibre.answers.card = Fintype.card fibre.Index := by
  classical
  simp [answers]

/-- Exact materialization never duplicates one semantic derivation value. -/
theorem answers_nodup {Source Target : Type u}
    {relation : ProofRel Source Target} {source : Source}
    (fibre : FiniteEvidenceFibre relation source) :
    fibre.answers.Nodup := by
  classical
  exact (Finset.nodup (Finset.univ : Finset fibre.Index)).map
    fibre.occurrenceEquiv.injective

/-- Every semantic target/derivation occurrence appears in the materialized
bag. -/
theorem mem_answers {Source Target : Type u}
    {relation : ProofRel Source Target} {source : Source}
    (fibre : FiniteEvidenceFibre relation source)
    (occurrence : AnswerOccurrence relation source) :
    occurrence ∈ fibre.answers := by
  classical
  refine Multiset.mem_map.mpr
    ⟨fibre.occurrenceEquiv.symm occurrence, by simp, ?_⟩
  exact fibre.occurrenceEquiv.apply_symm_apply occurrence

/-- The existing support-level completeness law follows from exact evidence
enumeration.  The converse does not hold: support completeness may forget
multiple derivations of one visible target. -/
theorem answers_complete {Source Target : Type u}
    {relation : ProofRel Source Target} {source : Source}
    (fibre : FiniteEvidenceFibre relation source) :
    AnswerBag.Complete fibre.answers := by
  intro target
  constructor
  · rintro ⟨derivation⟩
    let occurrence : AnswerOccurrence relation source :=
      ⟨target, derivation⟩
    exact ⟨occurrence, fibre.mem_answers occurrence, rfl⟩
  · exact AnswerBag.support_sound

end FiniteEvidenceFibre

/-- A native finite-search capability supplies one exact finite dependent
evidence fibre for every typed source query. -/
structure FiniteEvidenceProvider {Source Target : Type u}
    (relation : ProofRel Source Target) where
  fibre : (source : Source) → FiniteEvidenceFibre relation source

namespace FiniteEvidenceProvider

/-- A functional representation canonically supplies a one-occurrence exact
finite fibre at every source.  This embeds direct-map compilation into finite
proof-relevant search without identifying the two capabilities. -/
noncomputable def ofRepresentation {Source Target : Type u}
    {relation : ProofRel Source Target}
    (representation : Rel.Representation relation) :
    FiniteEvidenceProvider relation where
  fibre := fun source =>
    { Index := PUnit
      indexFintype := inferInstance
      occurrenceEquiv :=
        { toFun := fun _ =>
            ⟨representation.map source,
              (representation.exact source (representation.map source)).symm
                ⟨⟨rfl⟩⟩⟩
          invFun := fun _ => PUnit.unit
          left_inv := fun _ => rfl
          right_inv := by
            rintro ⟨target, evidence⟩
            have equal :
                (⟨representation.map source,
                    (representation.exact source
                      (representation.map source)).symm ⟨⟨rfl⟩⟩⟩ :
                  Sigma fun output => relation.evidence source output) =
                ⟨target, evidence⟩ :=
              (representation.deterministic source).allEq _ _
            cases equal
            rfl } }

/-- Functional representability is therefore sufficient for exact finite
search. -/
theorem nonempty_ofRepresentation {Source Target : Type u}
    {relation : ProofRel Source Target}
    (represented : Nonempty (Rel.Representation relation)) :
    Nonempty (FiniteEvidenceProvider relation) := by
  rcases represented with ⟨representation⟩
  exact ⟨ofRepresentation representation⟩

/-- Materialize the complete answer bag for a query. -/
noncomputable def answers {Source Target : Type u}
    {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) (source : Source) :
    AnswerBag relation source :=
  (provider.fibre source).answers

@[simp] theorem answers_complete {Source Target : Type u}
    {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) (source : Source) :
    AnswerBag.Complete (provider.answers source) :=
  (provider.fibre source).answers_complete

@[simp] theorem answers_nodup {Source Target : Type u}
    {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) (source : Source) :
    (provider.answers source).Nodup :=
  (provider.fibre source).answers_nodup

@[simp] theorem answers_card {Source Target : Type u}
    {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) (source : Source) :
    (provider.answers source).card =
      Fintype.card (provider.fibre source).Index :=
  (provider.fibre source).card_answers

/-! ## Closure under proof-relevant relational chaining -/

/-- A composite answer occurrence is exactly a dependent pair of an earlier
occurrence and a later occurrence at the earlier occurrence's retained
intermediate target. -/
def chainOccurrenceEquiv
    {First Middle Last : Type u}
    {earlier : ProofRel First Middle} {later : ProofRel Middle Last}
    (source : First) :
    (Sigma fun first : AnswerOccurrence earlier source =>
      AnswerOccurrence later first.target) ≃
      AnswerOccurrence (Rel.Chain earlier later) source where
  toFun indices := AnswerBag.chainOccurrence indices.1 indices.2
  invFun occurrence :=
    ⟨⟨occurrence.derivation.1, occurrence.derivation.2.1⟩,
      ⟨occurrence.target, occurrence.derivation.2.2⟩⟩
  left_inv indices := by
    rcases indices with ⟨⟨middle, earlierEvidence⟩,
      ⟨target, laterEvidence⟩⟩
    rfl
  right_inv occurrence := by
    rcases occurrence with ⟨target, middle, earlierEvidence, laterEvidence⟩
    rfl

/-- Exact finite fibres compose by dependent Sigma.  The composite index
retains the selected earlier occurrence and a later occurrence index at that
occurrence's exact intermediate target. -/
noncomputable def chainFibre
    {First Middle Last : Type u}
    {earlier : ProofRel First Middle} {later : ProofRel Middle Last}
    (earlierProvider : FiniteEvidenceProvider earlier)
    (laterProvider : FiniteEvidenceProvider later) (source : First) :
    FiniteEvidenceFibre (Rel.Chain earlier later) source := by
  classical
  let firstFibre := earlierProvider.fibre source
  let Index := Sigma fun firstIndex : firstFibre.Index =>
    (laterProvider.fibre
      (firstFibre.occurrenceEquiv firstIndex).target).Index
  letI : Fintype firstFibre.Index := firstFibre.indexFintype
  letI : ∀ firstIndex : firstFibre.Index,
      Fintype
        (laterProvider.fibre
          (firstFibre.occurrenceEquiv firstIndex).target).Index :=
    fun firstIndex =>
      (laterProvider.fibre
        (firstFibre.occurrenceEquiv firstIndex).target).indexFintype
  exact
    { Index := Index
      indexFintype := inferInstance
      occurrenceEquiv :=
        (Equiv.sigmaCongr firstFibre.occurrenceEquiv fun firstIndex =>
          (laterProvider.fibre
            (firstFibre.occurrenceEquiv firstIndex).target).occurrenceEquiv).trans
          (chainOccurrenceEquiv source) }

/-- Finite native relation search is closed under the intrinsic semantics of
`Chain`. -/
noncomputable def chain
    {First Middle Last : Type u}
    {earlier : ProofRel First Middle} {later : ProofRel Middle Last}
    (earlierProvider : FiniteEvidenceProvider earlier)
    (laterProvider : FiniteEvidenceProvider later) :
    FiniteEvidenceProvider (Rel.Chain earlier later) where
  fibre := chainFibre earlierProvider laterProvider

/-! ## Native query operation -/

/-- A materialized native search result retains its source query because the
answer occurrence type depends on that source. -/
structure SearchResult {Source Target : Type u}
    (relation : ProofRel Source Target) where
  source : Source
  answers : AnswerBag relation source

/-- The proof-carrying finite capability produces one complete materialized
result.  Proof construction happens outside the direct operation. -/
noncomputable def run {Source Target : Type u}
    {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) (source : Source) :
    SearchResult relation :=
  ⟨source, provider.answers source⟩

@[simp] theorem run_source {Source Target : Type u}
    {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) (source : Source) :
    (provider.run source).source = source :=
  rfl

@[simp] theorem run_answers {Source Target : Type u}
    {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) (source : Source) :
    (provider.run source).answers = provider.answers source :=
  rfl

/-- The direct native result remains exactly complete for the original
proof-relevant relation. -/
theorem run_complete {Source Target : Type u}
    {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) (source : Source) :
    AnswerBag.Complete (provider.run source).answers :=
  provider.answers_complete source

/-- The query operation is represented as a function graph without claiming
that the underlying relation from `Source` to `Target` is functional. -/
noncomputable def searchRelation {Source Target : Type u}
    {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) :
    ProofRel Source (SearchResult relation) :=
  Rel.graph provider.run

/-- Exact native finite search is a represented GSLT-IL route between the
discrete typed-query and materialized-result theories. -/
noncomputable def representedRoute {Source Target : Type u}
    {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) :
    RepresentedOperationalRoute (GSLT.discrete Source)
      (GSLT.discrete (SearchResult relation)) where
  related := (provider.searchRelation).toLoose
  representation := Rel.graphRepresentation provider.run
  mapEquiv := fun equal => congrArg provider.run equal
  mapStep := fun step => step.elim

@[simp] theorem representedRoute_map {Source Target : Type u}
    {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) :
    provider.representedRoute.representation.map = provider.run :=
  rfl

/-! ## Revision-indexed NIK admission of the native query operation -/

/-- NIK may retain the represented query-to-complete-bag route at one
dependency revision.  The output semantics is the exact direct image of the
selected source fibre; the independently declared observation may inspect
execution history without replacing that semantic result. -/
noncomputable def admitObservedAt
    {Source Target : Type} {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation)
    (dependencies : DependencySystem) (revision : dependencies.Revision)
    (sourceMeaning : Source → Prop)
    (targetDiscipline : GSLTObservation
      (GSLT.discrete (SearchResult relation))) :=
  provider.representedRoute.admitObservedImage dependencies revision
    sourceMeaning targetDiscipline

/-- Every selected source query maps into the admitted target semantic fibre.
This retains the exact source witness used by the direct-image semantics. -/
theorem run_has_image_meaning
    {Source Target : Type} {relation : ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation)
    (sourceMeaning : Source → Prop) (source : Source)
    (meaningful : sourceMeaning source) :
    provider.representedRoute.toOperationalTranslation.ImageMeaning
      sourceMeaning (provider.run source) :=
  ⟨source, meaningful, rfl⟩

end FiniteEvidenceProvider

/-! ## Intrinsic hypothesis programs consume the capability -/

abbrev ProgramFiniteSearchProvider
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    {quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context}
    {source target : vocabulary.SortCode} {term : Tower.Tm n}
    (program : IntrinsicMILSemanticAdequacy.Program quotation
      (source := source) (target := target) term) :=
  FiniteEvidenceProvider program.denotation

/-- Primitive finite-search capabilities for one semantic vocabulary.  This
is deliberately weaker than functional representability: a primitive may
have several target/evidence occurrences, provided that every source fibre is
finite and exactly enumerable. -/
structure PrimitiveFiniteSearchProviders
    (vocabulary : MILSchemaElaboration.Semantic.Vocabulary) where
  provide : ∀ {source target : vocabulary.SortCode}
      (symbol : vocabulary.Primitive source target),
    FiniteEvidenceProvider (vocabulary.meaning symbol)

/-- Direct representations of every primitive imply finite exact providers
for every primitive.  The converse is refuted below by a finite
nondeterministic vocabulary. -/
noncomputable def primitiveFiniteOfRepresentations
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    (representations :
      IntrinsicMILSemanticAdequacy.PrimitiveRepresentations vocabulary) :
    PrimitiveFiniteSearchProviders vocabulary where
  provide := fun symbol =>
    FiniteEvidenceProvider.ofRepresentation (representations.represent symbol)

/-- Exact finite native search is closed under every intrinsically typed
hypothesis program.  Primitive capabilities are the only assumptions;
`chain` derives the composite capability by dependent Sigma and therefore
retains intermediate values and both premise derivations. -/
noncomputable def programFiniteSearchProvider
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    {quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context}
    (primitiveProviders : PrimitiveFiniteSearchProviders vocabulary) :
    {source target : vocabulary.SortCode} → {term : Tower.Tm n} →
      (program : IntrinsicMILSemanticAdequacy.Program quotation
        (source := source) (target := target) term) →
      ProgramFiniteSearchProvider program
  | _, _, _, .primitive symbol => primitiveProviders.provide symbol
  | _, _, _, .chain earlier later =>
      (programFiniteSearchProvider primitiveProviders earlier).chain
        (programFiniteSearchProvider primitiveProviders later)

/-- The structurally derived native provider remains complete for the exact
proof-relevant denotation of the authored intrinsic program. -/
theorem programFiniteSearch_complete
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    {quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context}
    {source target : vocabulary.SortCode} {term : Tower.Tm n}
    (program : IntrinsicMILSemanticAdequacy.Program quotation
      (source := source) (target := target) term)
    (primitiveProviders : PrimitiveFiniteSearchProviders vocabulary)
    (input : vocabulary.Carrier source) :
    AnswerBag.Complete
      ((programFiniteSearchProvider primitiveProviders program).run input).answers :=
  (programFiniteSearchProvider primitiveProviders program).run_complete input

/-- An intrinsic hypothesis with an exact finite provider supplies the common
represented native-search route.  Its tower typing derivation remains the
independent `Program.hasType` projection. -/
noncomputable def programNativeSearchRoute
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    {quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context}
    {source target : vocabulary.SortCode} {term : Tower.Tm n}
    (program : IntrinsicMILSemanticAdequacy.Program quotation
      (source := source) (target := target) term)
    (provider : ProgramFiniteSearchProvider program) :
    RepresentedOperationalRoute
      (GSLT.discrete (vocabulary.Carrier source))
      (GSLT.discrete
        (FiniteEvidenceProvider.SearchResult program.denotation)) :=
  provider.representedRoute

@[simp] theorem nativeSearchRoute_map
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    {quotation : IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary
      context}
    {source target : vocabulary.SortCode} {term : Tower.Tm n}
    (program : IntrinsicMILSemanticAdequacy.Program quotation
      (source := source) (target := target) term)
    (provider : ProgramFiniteSearchProvider program) :
    (programNativeSearchRoute program provider).representation.map = provider.run :=
  rfl

/-! ## Separating controls -/

namespace Canary

/-- A genuinely nondeterministic relation with two visible results. -/
def choice : ProofRel Unit Bool where
  evidence _ _ := Unit

def choiceFibre : FiniteEvidenceFibre choice () where
  Index := Bool
  indexFintype := inferInstance
  occurrenceEquiv := {
    toFun target := ⟨target, ()⟩
    invFun occurrence := occurrence.target
    left_inv _ := rfl
    right_inv occurrence := by
      cases occurrence
      congr }

def choiceProvider : FiniteEvidenceProvider choice where
  fibre _ := choiceFibre

/-- The trace readout is deliberately orthogonal to the semantic result bag:
on this discrete native operation it observes zero internal steps, while the
target meaning and result object retain the complete proof fibre. -/
def choiceTrace : GSLTObservation
    (GSLT.discrete (FiniteEvidenceProvider.SearchResult choice)) where
  collection :=
    { Container := List
        (GSLT.discrete
          (FiniteEvidenceProvider.SearchResult choice)).LabeledStep
      collect := some }
  Value := Nat
  readout := List.length

def choiceDependencies : DependencySystem where
  Revision := Bool
  Dependency := Unit
  Value := Bool
  read revision _ := revision

noncomputable def admittedChoice :=
  choiceProvider.admitObservedAt choiceDependencies false (fun _ => True)
    choiceTrace

noncomputable def activeChoice : admittedChoice.Active false :=
  admittedChoice.activate (choiceDependencies.sameDependencies_refl false)

/-- Native finite search supports nondeterminism without falsely representing
the underlying relation as a function. -/
theorem choice_search_without_direct_representation :
    (choiceProvider.run ()).answers.card = 2 ∧
      ¬ Nonempty (Rel.Representation choice) := by
  constructor
  · simp [FiniteEvidenceProvider.run, FiniteEvidenceProvider.answers,
      choiceProvider, choiceFibre]
  · exact RelationalInternalLanguage.Semantic.Canary.choice_not_representable

/-- After currentness is established, active NIK execution is exactly the
native query operation and still returns both proof occurrences. -/
theorem active_choice_runs_complete_native_search :
    (activeChoice.run ()).answers.card = 2 := by
  change (choiceProvider.run ()).answers.card = 2
  exact choice_search_without_direct_representation.1

/-- The admitted result remains in the exact semantic image and its answer
bag is complete for the original nondeterministic relation. -/
theorem active_choice_result_is_exact_and_complete :
    choiceProvider.representedRoute.toOperationalTranslation.ImageMeaning
        (fun _ => True) (activeChoice.run ()) ∧
      AnswerBag.Complete (activeChoice.run ()).answers := by
  constructor
  · change choiceProvider.representedRoute.toOperationalTranslation.ImageMeaning
      (fun _ => True) (choiceProvider.run ())
    exact choiceProvider.run_has_image_meaning (fun _ => True) () trivial
  · change AnswerBag.Complete (choiceProvider.run ()).answers
    exact choiceProvider.run_complete ()

/-- A relevant dependency change prevents use of the stored native search;
the raw relation and its finite provider remain independently meaningful. -/
theorem relevant_change_prevents_native_search_activation :
    ¬ admittedChoice.Active true := by
  rintro ⟨current⟩
  have changed := current ()
  simp [choiceDependencies] at changed

/-- A deterministic second stage used to exercise finite relational chain. -/
def tag : ProofRel Bool Bool := Rel.graph Bool.not

def tagFibre (source : Bool) : FiniteEvidenceFibre tag source where
  Index := Unit
  indexFintype := inferInstance
  occurrenceEquiv := {
    toFun _ := ⟨Bool.not source, ⟨⟨rfl⟩⟩⟩
    invFun _ := ()
    left_inv _ := rfl
    right_inv occurrence := by
      rcases occurrence with ⟨target, ⟨⟨equal⟩⟩⟩
      cases equal
      rfl }

def tagProvider : FiniteEvidenceProvider tag where
  fibre := tagFibre

noncomputable def chainedProvider :
    FiniteEvidenceProvider (Rel.Chain choice tag) :=
  choiceProvider.chain tagProvider

/-- The compositional provider retains both nondeterministic middle choices
and therefore materializes two composite proof occurrences. -/
theorem chained_search_retains_both_middle_occurrences :
    (chainedProvider.run ()).answers.card = 2 := by
  simp [chainedProvider, FiniteEvidenceProvider.run,
    FiniteEvidenceProvider.answers, FiniteEvidenceProvider.chain,
    FiniteEvidenceProvider.chainFibre, choiceProvider, choiceFibre,
    tagProvider, tagFibre]
  decide

/-- An infinite proof fibre remains a valid relation but cannot acquire the
finite native-search capability. -/
def infinitelyManyProofs : ProofRel Unit Unit where
  evidence _ _ := Nat

theorem no_finite_provider_for_infinite_fibre :
    ¬ Nonempty (FiniteEvidenceProvider infinitelyManyProofs) := by
  rintro ⟨provider⟩
  let fibre := provider.fibre ()
  let occurrenceEquivNat : AnswerOccurrence infinitelyManyProofs () ≃ Nat :=
    { toFun := fun occurrence => occurrence.derivation
      invFun := fun evidence => ⟨(), evidence⟩
      left_inv := by
        rintro ⟨target, evidence⟩
        cases target
        rfl
      right_inv := fun _ => rfl }
  let indexEquivNat : fibre.Index ≃ Nat :=
    fibre.occurrenceEquiv.trans occurrenceEquivNat
  letI : Fintype Nat := Fintype.ofEquiv fibre.Index indexEquivNat
  exact not_finite Nat

/-- The existing nondeterministic intrinsic vocabulary earns finite native
search for its primitive even though it cannot earn functional
representability. -/
def nondeterministicPrimitiveProviders :
    PrimitiveFiniteSearchProviders
      IntrinsicMILSemanticAdequacy.NondeterministicCanary.vocabulary where
  provide := fun {source} {target} symbol => by
    cases symbol
    exact choiceProvider

/-- Finite exact enumeration and direct-map compilation are genuinely
different capabilities.  NIK may license the former without falsely
licensing the latter. -/
theorem finite_search_does_not_imply_direct_representation :
    Nonempty
        (PrimitiveFiniteSearchProviders
          IntrinsicMILSemanticAdequacy.NondeterministicCanary.vocabulary) ∧
      ¬ Nonempty
        (IntrinsicMILSemanticAdequacy.PrimitiveRepresentations
          IntrinsicMILSemanticAdequacy.NondeterministicCanary.vocabulary) :=
  ⟨⟨nondeterministicPrimitiveProviders⟩,
    IntrinsicMILSemanticAdequacy.NondeterministicCanary.no_primitiveRepresentations⟩

inductive InfinitePrimitive : Unit → Unit → Type where
  | enumerate : InfinitePrimitive () ()

def infiniteVocabulary : MILSchemaElaboration.Semantic.Vocabulary where
  SortCode := Unit
  Carrier := fun _ => Unit
  Primitive := InfinitePrimitive
  meaning := fun {source} {target} symbol => by
    cases symbol
    exact infinitelyManyProofs

/-- A valid intrinsic vocabulary need not support finite native search.  An
infinite evidence fibre stays in the relational execution layer. -/
theorem infinite_vocabulary_has_no_primitive_finite_search :
    ¬ Nonempty (PrimitiveFiniteSearchProviders infiniteVocabulary) := by
  rintro ⟨providers⟩
  exact no_finite_provider_for_infinite_fibre
    ⟨providers.provide (source := ()) (target := ())
      InfinitePrimitive.enumerate⟩

end Canary

#print axioms FiniteEvidenceFibre.answers_complete
#print axioms FiniteEvidenceProvider.chain
#print axioms FiniteEvidenceProvider.ofRepresentation
#print axioms FiniteEvidenceProvider.nonempty_ofRepresentation
#print axioms FiniteEvidenceProvider.run_complete
#print axioms FiniteEvidenceProvider.representedRoute
#print axioms FiniteEvidenceProvider.run_has_image_meaning
#print axioms programNativeSearchRoute
#print axioms Canary.choice_search_without_direct_representation
#print axioms Canary.active_choice_runs_complete_native_search
#print axioms Canary.active_choice_result_is_exact_and_complete
#print axioms Canary.relevant_change_prevents_native_search_activation
#print axioms Canary.chained_search_retains_both_middle_occurrences
#print axioms Canary.no_finite_provider_for_infinite_fibre
#print axioms programFiniteSearchProvider
#print axioms programFiniteSearch_complete
#print axioms primitiveFiniteOfRepresentations
#print axioms Canary.finite_search_does_not_imply_direct_representation
#print axioms Canary.infinite_vocabulary_has_no_primitive_finite_search

end IntrinsicMILNativeSearch
end Mettapedia.Languages.MeTTa.PureKernel.Universe
