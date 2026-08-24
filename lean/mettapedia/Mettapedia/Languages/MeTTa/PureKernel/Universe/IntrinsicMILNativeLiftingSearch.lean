import Mettapedia.Languages.MeTTa.PureKernel.Universe.IntrinsicMILNativeListSearch
import Mettapedia.Languages.MeTTa.PureKernel.Universe.NativeRelationLifting

/-!
# Exact native search through declared proof-relevant relation liftings

Strict positivity supplies structural recursion, but it does not by itself say
that a relation lifting has finite proof fibres.  This module isolates the
additional capability precisely:

* a `FiniteSearchLifting` maps every exact finite element provider to an exact
  finite provider over the data former;
* a separate `RepresentationLifting` maps functional representations to direct
  representations;
* both capabilities compose structurally through the generic higher-order
  hypothesis language, including carrier reindexing;
* native polynomial List supplies both capabilities using its already-proved
  structural relator;
* an infinitary strictly-positive product supplies a compositional relation
  lifting but cannot preserve finite search.

Thus declaration-generated native families may earn the strongest justified
search realization without making List primitive and without confusing strict
positivity with finitarity.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe
namespace IntrinsicMILNativeLiftingSearch

open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.TypeTheory.IndexedPolynomial
open RelationalInternalLanguage.Semantic
open RelationalEvidence
open IntrinsicMILNativeSearch
open NativeRelationLifting

universe u

/-! ## Exact finite providers and representations respect carrier equivalence -/

/-- `AnswerOccurrence` is the named record form of its dependent target/evidence
sum. -/
def occurrenceSigmaEquiv {Source Target : Type u}
    (relation : IntrinsicMILNativeSearch.ProofRel Source Target)
    (source : Source) :
    AnswerOccurrence relation source ≃
      (Sigma fun target => relation.evidence source target) where
  toFun occurrence := ⟨occurrence.target, occurrence.derivation⟩
  invFun occurrence := ⟨occurrence.1, occurrence.2⟩
  left_inv := by rintro ⟨target, derivation⟩; rfl
  right_inv := by rintro ⟨target, derivation⟩; rfl

/-- Reindexing target carriers gives an exact equivalence of complete
target/derivation occurrences. -/
noncomputable def reindexOccurrenceEquiv
    {Source Target ReindexedSource ReindexedTarget : Type u}
    (sourceEquiv : ReindexedSource ≃ Source)
    (targetEquiv : ReindexedTarget ≃ Target)
    (relation : IntrinsicMILNativeSearch.ProofRel Source Target)
    (source : ReindexedSource) :
    AnswerOccurrence relation (sourceEquiv source) ≃
      AnswerOccurrence
        (NativeRelationLifting.reindex sourceEquiv targetEquiv relation) source := by
  let targetSigmaEquiv :
      (Sigma fun target : Target =>
        relation.evidence (sourceEquiv source) target) ≃
      (Sigma fun target : ReindexedTarget =>
        relation.evidence (sourceEquiv source) (targetEquiv target)) :=
    Equiv.sigmaCongr targetEquiv.symm (fun target =>
      Equiv.cast
        (congrArg (relation.evidence (sourceEquiv source))
          (targetEquiv.apply_symm_apply target).symm))
  exact
    (occurrenceSigmaEquiv relation (sourceEquiv source)).trans
      (targetSigmaEquiv.trans
        (occurrenceSigmaEquiv
          (NativeRelationLifting.reindex sourceEquiv targetEquiv relation)
          source).symm)

/-- Exact finite search transports across the carrier equivalences declared by
a lifted vocabulary. -/
noncomputable def reindexProvider
    {Source Target ReindexedSource ReindexedTarget : Type u}
    (sourceEquiv : ReindexedSource ≃ Source)
    (targetEquiv : ReindexedTarget ≃ Target)
    {relation : IntrinsicMILNativeSearch.ProofRel Source Target}
    (provider : FiniteEvidenceProvider relation) :
    FiniteEvidenceProvider
      (NativeRelationLifting.reindex sourceEquiv targetEquiv relation) where
  fibre := fun source =>
    let original := provider.fibre (sourceEquiv source)
    { Index := original.Index
      indexFintype := original.indexFintype
      occurrenceEquiv := original.occurrenceEquiv.trans
        (reindexOccurrenceEquiv sourceEquiv targetEquiv relation source) }

/-- Functional representation likewise transports across carrier
equivalences. -/
noncomputable def reindexRepresentation
    {Source Target ReindexedSource ReindexedTarget : Type u}
    (sourceEquiv : ReindexedSource ≃ Source)
    (targetEquiv : ReindexedTarget ≃ Target)
    {relation : IntrinsicMILNativeSearch.ProofRel Source Target}
    (representation : Rel.Representation relation) :
    Rel.Representation
      (NativeRelationLifting.reindex sourceEquiv targetEquiv relation) where
  map source := targetEquiv.symm (representation.map (sourceEquiv source))
  exact source target :=
    (representation.exact (sourceEquiv source) (targetEquiv target)).trans
      { toFun := fun witness =>
          ⟨⟨(congrArg targetEquiv.symm witness.down.down).trans
            (targetEquiv.symm_apply_apply target)⟩⟩
        invFun := fun witness =>
          ⟨⟨(targetEquiv.apply_symm_apply
              (representation.map (sourceEquiv source))).symm.trans
            (congrArg targetEquiv witness.down.down)⟩⟩
        left_inv := fun first =>
          (instSubsingletonEqWitness _ _).allEq _ first
        right_inv := fun first =>
          (instSubsingletonEqWitness _ _).allEq _ first }

/-! ## Capabilities of a declared relation lifting -/

/-- A proof-relevant relation lifting preserves exact finite native search.
This is stronger than compositionality and weaker than requiring every lifted
relation to be functional. -/
structure FiniteSearchLifting
    (ObjectMap : Type u → Type u)
    (lifting : CompositionalLifting ObjectMap) where
  provide : ∀ {Source Target : Type u}
      (relation : IntrinsicMILNativeSearch.ProofRel Source Target),
    FiniteEvidenceProvider relation →
      FiniteEvidenceProvider (lifting.lift relation)

/-- Functional representations may be preserved independently of finite
search.  Keeping the capabilities separate allows finite nondeterminism. -/
structure RepresentationLifting
    (ObjectMap : Type u → Type u)
    (lifting : CompositionalLifting ObjectMap) where
  represent : ∀ {Source Target : Type u}
      (relation : IntrinsicMILNativeSearch.ProofRel Source Target),
    Rel.Representation relation → Rel.Representation (lifting.lift relation)

/-- Native polynomial List earns finite-search preservation structurally. -/
noncomputable def listFiniteSearchLifting :
    FiniteSearchLifting NativeIndexedFamilies.Semantic.List listLifting where
  provide := fun _ provider =>
    IntrinsicMILNativeListSearch.mapRelProvider provider

/-- Native polynomial List separately earns functional-representation
preservation. -/
noncomputable def listRepresentationLifting :
    RepresentationLifting NativeIndexedFamilies.Semantic.List listLifting where
  represent := fun _ representation =>
    IntrinsicMILNativeListSearch.mapRelRepresentation representation

/-! ## Generic higher-order hypotheses consume the capabilities -/

structure LiftedPrimitiveFiniteSearchProviders
    {ObjectMap : Type u → Type u}
    {lifting : CompositionalLifting ObjectMap}
    (vocabulary : LiftedVocabulary ObjectMap lifting) where
  provide : ∀ {source target : vocabulary.SortCode}
      (symbol : vocabulary.Primitive source target),
    FiniteEvidenceProvider (vocabulary.meaning symbol)

structure LiftedPrimitiveRepresentations
    {ObjectMap : Type u → Type u}
    {lifting : CompositionalLifting ObjectMap}
    (vocabulary : LiftedVocabulary ObjectMap lifting) where
  represent : ∀ {source target : vocabulary.SortCode}
      (symbol : vocabulary.Primitive source target),
    Rel.Representation (vocabulary.meaning symbol)

/-- Exact finite search is derived by structural recursion over any generic
higher-order hypothesis.  The lift case uses only the declared data-former
capability and the vocabulary's carrier equivalences. -/
noncomputable def hypothesisFiniteSearchProvider
    {ObjectMap : Type u → Type u}
    {lifting : CompositionalLifting ObjectMap}
    {vocabulary : LiftedVocabulary ObjectMap lifting}
    (primitiveProviders : LiftedPrimitiveFiniteSearchProviders vocabulary)
    (liftProvider : FiniteSearchLifting ObjectMap lifting) :
    {source target : vocabulary.SortCode} →
      (hypothesis : Hypothesis vocabulary source target) →
        FiniteEvidenceProvider hypothesis.denote
  | _, _, .primitive symbol => primitiveProviders.provide symbol
  | _, _, .chain earlier later =>
      (hypothesisFiniteSearchProvider primitiveProviders liftProvider earlier).chain
        (hypothesisFiniteSearchProvider primitiveProviders liftProvider later)
  | _, _, .lift (source := elementSource) (target := elementTarget) element =>
      reindexProvider (vocabulary.liftCarrier elementSource)
        (vocabulary.liftCarrier elementTarget)
        (liftProvider.provide element.denote
          (hypothesisFiniteSearchProvider primitiveProviders liftProvider element))

/-- Direct functional realization is derived independently. -/
noncomputable def hypothesisRepresentation
    {ObjectMap : Type u → Type u}
    {lifting : CompositionalLifting ObjectMap}
    {vocabulary : LiftedVocabulary ObjectMap lifting}
    (primitiveRepresentations : LiftedPrimitiveRepresentations vocabulary)
    (liftRepresentation : RepresentationLifting ObjectMap lifting) :
    {source target : vocabulary.SortCode} →
      (hypothesis : Hypothesis vocabulary source target) →
        Rel.Representation hypothesis.denote
  | _, _, .primitive symbol => primitiveRepresentations.represent symbol
  | _, _, .chain earlier later =>
      Rel.chainRepresentation
        (hypothesisRepresentation primitiveRepresentations liftRepresentation earlier)
        (hypothesisRepresentation primitiveRepresentations liftRepresentation later)
  | _, _, .lift (source := elementSource) (target := elementTarget) element =>
      reindexRepresentation (vocabulary.liftCarrier elementSource)
        (vocabulary.liftCarrier elementTarget)
        (liftRepresentation.represent element.denote
          (hypothesisRepresentation primitiveRepresentations liftRepresentation
            element))

theorem hypothesisFiniteSearch_complete
    {ObjectMap : Type u → Type u}
    {lifting : CompositionalLifting ObjectMap}
    {vocabulary : LiftedVocabulary ObjectMap lifting}
    (primitiveProviders : LiftedPrimitiveFiniteSearchProviders vocabulary)
    (liftProvider : FiniteSearchLifting ObjectMap lifting)
    {source target : vocabulary.SortCode}
    (hypothesis : Hypothesis vocabulary source target)
    (input : vocabulary.Carrier source) :
    AnswerBag.Complete
      ((hypothesisFiniteSearchProvider primitiveProviders liftProvider hypothesis).run
        input).answers :=
  (hypothesisFiniteSearchProvider primitiveProviders liftProvider hypothesis).run_complete
    input

/-! ## Positive List instances -/

namespace Canary

inductive BranchSort where
  | input
  | output
  | list (element : BranchSort)
  deriving DecidableEq, Repr

def BranchCarrier : BranchSort → Type
  | .input => Unit
  | .output => Bool
  | .list element => NativeIndexedFamilies.Semantic.List (BranchCarrier element)

inductive BranchPrimitive : BranchSort → BranchSort → Type where
  | choose : BranchPrimitive .input .output

def branchMeaning : {source target : BranchSort} →
    BranchPrimitive source target →
      RelationalInternalLanguage.Semantic.Rel
        (BranchCarrier source) (BranchCarrier target)
  | _, _, .choose => IntrinsicMILNativeSearch.Canary.choice

def branchVocabulary :
    LiftedVocabulary NativeIndexedFamilies.Semantic.List listLifting where
  SortCode := BranchSort
  Carrier := BranchCarrier
  Primitive := BranchPrimitive
  meaning := branchMeaning
  liftSort := .list
  liftCarrier := fun _ => Equiv.refl _

def branchPrimitiveProviders :
    LiftedPrimitiveFiniteSearchProviders branchVocabulary where
  provide := fun {_source} {_target} symbol =>
    match symbol with
    | BranchPrimitive.choose =>
        IntrinsicMILNativeSearch.Canary.choiceProvider

def liftedChoice : Hypothesis branchVocabulary
    (BranchSort.list BranchSort.input) (BranchSort.list BranchSort.output) :=
  .lift (.primitive BranchPrimitive.choose)

noncomputable def liftedChoiceProvider :
    FiniteEvidenceProvider liftedChoice.denote :=
  hypothesisFiniteSearchProvider branchPrimitiveProviders
    listFiniteSearchLifting liftedChoice

/-- The generic higher-order recursion reaches the actual List provider and
retains both branches. -/
theorem generic_list_lifting_retains_two_occurrences :
    (liftedChoiceProvider.run ListExample.singletonUnit).answers.card = 2 := by
  change (liftedChoiceProvider.answers ListExample.singletonUnit).card = 2
  rw [FiniteEvidenceProvider.answers_card]
  change Fintype.card (Bool × PUnit) = 2
  decide

inductive DirectSort where
  | atom
  | list (element : DirectSort)
  deriving DecidableEq, Repr

def DirectCarrier : DirectSort → Type
  | .atom => Bool
  | .list element => NativeIndexedFamilies.Semantic.List (DirectCarrier element)

inductive DirectPrimitive : DirectSort → DirectSort → Type where
  | toggle : DirectPrimitive .atom .atom

def directMeaning : {source target : DirectSort} →
    DirectPrimitive source target →
      RelationalInternalLanguage.Semantic.Rel
        (DirectCarrier source) (DirectCarrier target)
  | _, _, .toggle => Rel.graph Bool.not

def directVocabulary :
    LiftedVocabulary NativeIndexedFamilies.Semantic.List listLifting where
  SortCode := DirectSort
  Carrier := DirectCarrier
  Primitive := DirectPrimitive
  meaning := directMeaning
  liftSort := .list
  liftCarrier := fun _ => Equiv.refl _

noncomputable def directPrimitiveProviders :
    LiftedPrimitiveFiniteSearchProviders directVocabulary where
  provide := fun {_source} {_target} symbol =>
    match symbol with
    | DirectPrimitive.toggle =>
        FiniteEvidenceProvider.ofRepresentation
          (Rel.graphRepresentation Bool.not)

def directPrimitiveRepresentations :
    LiftedPrimitiveRepresentations directVocabulary where
  represent := fun {_source} {_target} symbol =>
    match symbol with
    | DirectPrimitive.toggle => Rel.graphRepresentation Bool.not

def liftedToggle : Hypothesis directVocabulary
    (DirectSort.list DirectSort.atom) (DirectSort.list DirectSort.atom) :=
  .lift (.primitive DirectPrimitive.toggle)

noncomputable def liftedToggleProvider :
    FiniteEvidenceProvider liftedToggle.denote :=
  hypothesisFiniteSearchProvider directPrimitiveProviders
    listFiniteSearchLifting liftedToggle

noncomputable def liftedToggleRepresentation :
    Rel.Representation liftedToggle.denote :=
  hypothesisRepresentation directPrimitiveRepresentations
    listRepresentationLifting liftedToggle

@[simp] theorem liftedToggleRepresentation_map :
    liftedToggleRepresentation.map =
      NativeIndexedFamilies.Semantic.map Bool.not :=
  rfl

/-! ## Strict positivity is not finitarity -/

/-- The one-layer infinitary product is a strictly-positive indexed
polynomial: its recursive family occurs only as the codomain selected by each
natural-number position. -/
def infinitaryProductPolynomial :
    Mettapedia.TypeTheory.IndexedPolynomial Unit (fun _ => Unit) where
  Shape := fun _ _ => Unit
  Position := fun _ => Nat
  next := fun _ _ => ()

/-- Its extension is the positive reader/product functor. -/
def infinitaryProductExtensionEquiv (Element : Type u) :
    infinitaryProductPolynomial.Extension (fun _ _ => Element) () () ≃
      (Nat → Element) :=
  { toFun := fun input => input.2
    invFun := fun children => ⟨(), children⟩
    left_inv := by rintro ⟨shape, children⟩; cases shape; rfl
    right_inv := fun _ => rfl }

/-- Pointwise relation lifting through the infinitary positive product is
compositionally lawful. -/
noncomputable def readerLifting : CompositionalLifting (fun Object : Type u =>
    Nat → Object) where
  lift := fun relation =>
    ⟨fun source target => ∀ position, relation.evidence
      (source position) (target position)⟩
  identity := by
    intro Object source target
    exact
      { toFun := fun pointwise =>
          ⟨⟨funext fun position => (pointwise position).down.down⟩⟩
        invFun := fun equal position =>
          ⟨⟨congrFun equal.down.down position⟩⟩
        left_inv := by
          intro pointwise
          funext position
          exact (instSubsingletonEqWitness _ _).allEq _ (pointwise position)
        right_inv := fun equal => (instSubsingletonEqWitness _ _).allEq _ equal }
  chain := by
    intro First Middle Last earlier later source target
    exact
      { toFun := fun pointwise =>
          ⟨fun position => (pointwise position).1,
            (fun position => (pointwise position).2.1),
            (fun position => (pointwise position).2.2)⟩
        invFun := fun composite position =>
          ⟨composite.1 position, composite.2.1 position,
            composite.2.2 position⟩
        left_inv := by
          intro pointwise
          funext position
          cases occurrence : pointwise position with
          | mk middle evidence =>
              cases evidence
              simp [occurrence]
        right_inv := by
          rintro ⟨middle, first, second⟩
          rfl }

def spike (index position : Nat) : Bool := decide (position = index)

theorem spike_injective : Function.Injective spike := by
  intro first second equal
  by_contra distinct
  have atFirst := congrFun equal first
  simp [spike, distinct] at atFirst

def readerSource : Nat → Unit := fun _ => ()

def spikeOccurrence (index : Nat) :
    AnswerOccurrence
      (readerLifting.lift IntrinsicMILNativeSearch.Canary.choice)
      readerSource :=
  ⟨spike index, fun _ => ()⟩

theorem spikeOccurrence_injective : Function.Injective spikeOccurrence := by
  intro first second equal
  apply spike_injective
  exact congrArg AnswerOccurrence.target equal

/-- Two finite choices at every natural-number position produce an infinite
complete occurrence fibre. -/
theorem reader_choice_has_no_finite_provider :
    ¬ Nonempty
      (FiniteEvidenceProvider
        (readerLifting.lift IntrinsicMILNativeSearch.Canary.choice)) := by
  rintro ⟨provider⟩
  let fibre := provider.fibre readerSource
  letI : Fintype
      (AnswerOccurrence
        (readerLifting.lift IntrinsicMILNativeSearch.Canary.choice)
        readerSource) :=
    Fintype.ofEquiv fibre.Index fibre.occurrenceEquiv
  letI : Fintype Nat :=
    Fintype.ofInjective spikeOccurrence spikeOccurrence_injective
  exact not_finite Nat

/-- Compositional proof-relevant lifting therefore does not imply preservation
of exact finite search, even for a strictly-positive polynomial extension. -/
theorem compositional_lifting_does_not_imply_finite_search :
    ¬ Nonempty (FiniteSearchLifting (fun Object : Type => Nat → Object)
      readerLifting.{0}) := by
  rintro ⟨finiteLifting⟩
  exact reader_choice_has_no_finite_provider
    ⟨finiteLifting.provide IntrinsicMILNativeSearch.Canary.choice
      IntrinsicMILNativeSearch.Canary.choiceProvider⟩

end Canary

#print axioms reindexProvider
#print axioms reindexRepresentation
#print axioms listFiniteSearchLifting
#print axioms listRepresentationLifting
#print axioms hypothesisFiniteSearchProvider
#print axioms hypothesisRepresentation
#print axioms Canary.generic_list_lifting_retains_two_occurrences
#print axioms Canary.liftedToggleRepresentation
#print axioms Canary.readerLifting
#print axioms Canary.compositional_lifting_does_not_imply_finite_search

end IntrinsicMILNativeLiftingSearch
end Mettapedia.Languages.MeTTa.PureKernel.Universe
