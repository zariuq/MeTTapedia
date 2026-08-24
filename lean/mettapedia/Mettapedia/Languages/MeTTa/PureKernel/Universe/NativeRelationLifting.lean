import Mettapedia.Languages.MeTTa.PureKernel.Universe.MILSchemaElaboration

/-!
# Proof-relevant relation lifting for higher-order Prime programs

A higher-order relational program may lift a relation through a data former,
but that operation is not an extra logical primitive.  It is a capability of
the data former.  This module isolates the capability required by Prime:

* the lifting retains proof fibres;
* identity relations lift to identity relations;
* relational composition lifts to relational composition, including the
  complete intermediate container and every component witness.

The native polynomial List supplies the first nontrivial instance.  The
composition theorem is stronger than support preservation: both sides are
equivalent as types of derivations.  A generic higher-order hypothesis
language can therefore use any such lifting; List is only one instance.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe
namespace NativeRelationLifting

open Mettapedia.TypeTheory.IndexedPolynomial
open RelationalInternalLanguage

universe u

/-! ## Exact composition for the native List relator -/

namespace ListComposition

open ListExample

/-- Distribute a pointwise proof-relevant composite through a List spine.
The result retains one intermediate List and both complete derivation spines. -/
def splitChain {Source Middle Target : Type u}
    (earlier : Source → Middle → Type u)
    (later : Middle → Target → Type u) :
    {source : List Source} → {target : List Target} →
      ListRel (fun left right =>
        Sigma fun middle => earlier left middle × later middle right)
        source target →
      Sigma fun middle : List Middle =>
        ListRel earlier source middle × ListRel later middle target
  | [], [], .nil => ⟨[], .nil, .nil⟩
  | _ :: _, _ :: _, .cons ⟨middle, earlierHead, laterHead⟩ tail =>
      let tailSplit := splitChain earlier later tail
      ⟨middle :: tailSplit.1,
        .cons earlierHead tailSplit.2.1,
        .cons laterHead tailSplit.2.2⟩

/-- Fuse two List-relator spines sharing the exact same intermediate List. -/
def mergeChain {Source Middle Target : Type u}
    (earlier : Source → Middle → Type u)
    (later : Middle → Target → Type u) :
    {source : List Source} → {target : List Target} →
      (Sigma fun middle : List Middle =>
        ListRel earlier source middle × ListRel later middle target) →
      ListRel (fun left right =>
        Sigma fun middle => earlier left middle × later middle right)
        source target
  | [], [], ⟨[], .nil, .nil⟩ => .nil
  | [], _ :: _, ⟨middle, earlierEvidence, laterEvidence⟩ => by
      cases earlierEvidence
      cases laterEvidence
  | _ :: _, [], ⟨middle, earlierEvidence, laterEvidence⟩ => by
      cases earlierEvidence
      cases laterEvidence
  | _ :: _, _ :: _,
      ⟨middle :: _, .cons earlierHead earlierTail,
        .cons laterHead laterTail⟩ =>
      .cons ⟨middle, earlierHead, laterHead⟩
        (mergeChain earlier later ⟨_, earlierTail, laterTail⟩)

theorem mergeChain_splitChain {Source Middle Target : Type u}
    (earlier : Source → Middle → Type u)
    (later : Middle → Target → Type u)
    {source : List Source} {target : List Target}
    (evidence : ListRel (fun left right =>
      Sigma fun middle => earlier left middle × later middle right)
      source target) :
    mergeChain earlier later (splitChain earlier later evidence) = evidence := by
  induction evidence with
  | nil => rfl
  | cons head tail hypothesis =>
      rcases head with ⟨middle, earlierHead, laterHead⟩
      simp only [splitChain, mergeChain]
      rw [hypothesis]

theorem splitChain_mergeChain {Source Middle Target : Type u}
    (earlier : Source → Middle → Type u)
    (later : Middle → Target → Type u)
    {source : List Source} {middle : List Middle} {target : List Target}
    (earlierEvidence : ListRel earlier source middle)
    (laterEvidence : ListRel later middle target) :
    splitChain earlier later
        (mergeChain earlier later
          ⟨middle, earlierEvidence, laterEvidence⟩) =
      ⟨middle, earlierEvidence, laterEvidence⟩ := by
  induction earlierEvidence generalizing target with
  | nil =>
      cases laterEvidence
      rfl
  | cons earlierHead earlierTail hypothesis =>
      cases laterEvidence with
      | cons laterHead laterTail =>
          simp only [mergeChain, splitChain]
          rw [hypothesis laterTail]

/-- Pointwise relational composition commutes exactly with List lifting. -/
def chainEquiv {Source Middle Target : Type u}
    (earlier : Source → Middle → Type u)
    (later : Middle → Target → Type u)
    (source : List Source) (target : List Target) :
    ListRel (fun left right =>
      Sigma fun middle => earlier left middle × later middle right)
        source target ≃
      (Sigma fun middle : List Middle =>
        ListRel earlier source middle × ListRel later middle target) where
  toFun := splitChain earlier later
  invFun := mergeChain earlier later
  left_inv := mergeChain_splitChain earlier later
  right_inv := by
    rintro ⟨middle, earlierEvidence, laterEvidence⟩
    exact splitChain_mergeChain earlier later earlierEvidence laterEvidence

/-! ## Transport from ordinary Lists to the native polynomial List -/

/-- Reindex the intermediate ordinary List along the proved polynomial-List
representation equivalence. -/
noncomputable def middleRepresentationEquiv
    {Source Middle Target : Type u}
    (earlier : Source → Middle → Type u)
    (later : Middle → Target → Type u)
    (source : List Source) (target : List Target) :
    (Sigma fun middle : List Middle =>
      ListRel earlier source middle × ListRel later middle target) ≃
    (Sigma fun middle : ListExample.ListP Middle =>
      ListRel earlier source (ListExample.toList middle) ×
      ListRel later (ListExample.toList middle) target) :=
  Equiv.sigmaCongr (ListExample.equivList Middle).symm (fun middle =>
    Equiv.cast (by
      simp [ListExample.equivList]))

/-- The native polynomial List relator preserves proof-relevant relational
composition.  The equivalence keeps the entire intermediate polynomial List,
not only pointwise existential witnesses. -/
noncomputable def polynomialChainEquiv
    {Source Middle Target : Type u}
    (earlier : Source → Middle → Type u)
    (later : Middle → Target → Type u)
    (source : ListExample.ListP Source)
    (target : ListExample.ListP Target) :
    ListExample.mapRel (fun left right =>
      Sigma fun middle => earlier left middle × later middle right)
        source target ≃
      (Sigma fun middle : ListExample.ListP Middle =>
        ListExample.mapRel earlier source middle ×
          ListExample.mapRel later middle target) :=
  (chainEquiv earlier later (ListExample.toList source)
    (ListExample.toList target)).trans
      (middleRepresentationEquiv earlier later
        (ListExample.toList source) (ListExample.toList target))

end ListComposition

/-! ## The capability exposed to higher-order relational syntax -/

/-- A proof-relevant data former may be used as a higher-order relational
lifting exactly when it preserves identity and relational composition
fibrewise.  These are equivalences of evidence types, not propositions about
Boolean support.

The structure deliberately does not claim strict equality: proof-relevant
composition is associative and unital through coherent equivalences. -/
structure CompositionalLifting (ObjectMap : Type u → Type u) where
  lift : {Source Target : Type u} →
    Semantic.Rel Source Target → Semantic.Rel (ObjectMap Source) (ObjectMap Target)
  identity : ∀ (Object : Type u) (source target : ObjectMap Object),
    (lift (Semantic.Rel.graph id)).evidence source target ≃
      (Semantic.Rel.graph id).evidence source target
  chain : ∀ {First Middle Last : Type u}
    (earlier : Semantic.Rel First Middle)
    (later : Semantic.Rel Middle Last)
    (source : ObjectMap First) (target : ObjectMap Last),
    (lift (Semantic.Rel.Chain earlier later)).evidence source target ≃
      (Semantic.Rel.Chain (lift earlier) (lift later)).evidence source target

/-- The native polynomial List is a compositional proof-relevant lifting. -/
noncomputable def listLifting :
    CompositionalLifting NativeIndexedFamilies.Semantic.List where
  lift := NativeIndexedFamilies.Semantic.mapRel
  identity := by
    intro Object source target
    change
      (NativeIndexedFamilies.Semantic.mapRel
        (Semantic.Rel.graph (fun value : Object => value))).evidence
          source target ≃
        (Semantic.Rel.graph
          (fun value : NativeIndexedFamilies.Semantic.List Object => value)).evidence
            source target
    refine
      (NativeIndexedFamilies.Semantic.mapRel_graph_equiv_graph_map
        (fun value : Object => value) source target).trans ?_
    exact
      { toFun := fun witness =>
          ⟨⟨(ListExample.map_id source).symm.trans witness.down.down⟩⟩
        invFun := fun witness =>
          ⟨⟨(ListExample.map_id source).trans witness.down.down⟩⟩
        left_inv := fun _ =>
          (Mettapedia.GSLT.LooseRelationEquipment.instSubsingletonEqWitness
            _ _).elim _ _
        right_inv := fun _ =>
          (Mettapedia.GSLT.LooseRelationEquipment.instSubsingletonEqWitness
            _ _).elim _ _ }
  chain := by
    intro First Middle Last earlier later source target
    exact ListComposition.polynomialChainEquiv earlier.evidence later.evidence
      source target

/-! ## A generic higher-order hypothesis language -/

/-- A semantic vocabulary equipped with one declared relation lifting.  The
carrier equivalence records how the vocabulary's lifted sort is represented;
the logical laws live in `lifting`, independently of those sort codes. -/
structure LiftedVocabulary
    (ObjectMap : Type u → Type u)
    (lifting : CompositionalLifting ObjectMap)
    extends MILSchemaElaboration.Semantic.Vocabulary.{u, u, u} where
  liftSort : SortCode → SortCode
  liftCarrier : ∀ sort, Carrier (liftSort sort) ≃ ObjectMap (Carrier sort)

/-- Reindex both endpoints of a relation along carrier equivalences. -/
def reindex {Source Target ReindexedSource ReindexedTarget : Type u}
    (source : ReindexedSource ≃ Source)
    (target : ReindexedTarget ≃ Target)
    (relation : Semantic.Rel Source Target) :
    Semantic.Rel ReindexedSource ReindexedTarget where
  evidence reindexedSource reindexedTarget :=
    relation.evidence (source reindexedSource) (target reindexedTarget)

/-- The free higher-order hypothesis language generated by primitive edges,
relational chaining, and a declared compositional lifting.  It is generic in
the data former: no ILP operation and no guest logic is privileged. -/
inductive Hypothesis
    {ObjectMap : Type u → Type u}
    {lifting : CompositionalLifting ObjectMap}
    (vocabulary : LiftedVocabulary ObjectMap lifting) :
    vocabulary.SortCode → vocabulary.SortCode → Type (u + 1) where
  | primitive {source target : vocabulary.SortCode}
      (symbol : vocabulary.Primitive source target) :
      Hypothesis vocabulary source target
  | chain {source middle target : vocabulary.SortCode}
      (earlier : Hypothesis vocabulary source middle)
      (later : Hypothesis vocabulary middle target) :
      Hypothesis vocabulary source target
  | lift {source target : vocabulary.SortCode}
      (element : Hypothesis vocabulary source target) :
      Hypothesis vocabulary (vocabulary.liftSort source)
        (vocabulary.liftSort target)

namespace Hypothesis

noncomputable def denote
    {ObjectMap : Type u → Type u}
    {lifting : CompositionalLifting ObjectMap}
    {vocabulary : LiftedVocabulary ObjectMap lifting}
    {source target : vocabulary.SortCode} :
    Hypothesis vocabulary source target →
      Semantic.Rel (vocabulary.Carrier source) (vocabulary.Carrier target)
  | .primitive symbol => vocabulary.meaning symbol
  | .chain earlier later => Semantic.Rel.Chain earlier.denote later.denote
  | .lift (source := source) (target := target) element =>
      reindex (vocabulary.liftCarrier source) (vocabulary.liftCarrier target)
        (lifting.lift element.denote)

@[simp] theorem denote_primitive
    {ObjectMap : Type u → Type u}
    {lifting : CompositionalLifting ObjectMap}
    {vocabulary : LiftedVocabulary ObjectMap lifting}
    {source target : vocabulary.SortCode}
    (symbol : vocabulary.Primitive source target) :
    (Hypothesis.primitive symbol : Hypothesis vocabulary source target).denote =
      vocabulary.meaning symbol :=
  rfl

@[simp] theorem denote_chain
    {ObjectMap : Type u → Type u}
    {lifting : CompositionalLifting ObjectMap}
    {vocabulary : LiftedVocabulary ObjectMap lifting}
    {source middle target : vocabulary.SortCode}
    (earlier : Hypothesis vocabulary source middle)
    (later : Hypothesis vocabulary middle target) :
    (Hypothesis.chain earlier later).denote =
      Semantic.Rel.Chain earlier.denote later.denote :=
  rfl

@[simp] theorem denote_lift
    {ObjectMap : Type u → Type u}
    {lifting : CompositionalLifting ObjectMap}
    {vocabulary : LiftedVocabulary ObjectMap lifting}
    {source target : vocabulary.SortCode}
    (element : Hypothesis vocabulary source target) :
    (Hypothesis.lift element).denote =
      reindex (vocabulary.liftCarrier source) (vocabulary.liftCarrier target)
        (lifting.lift element.denote) :=
  rfl

end Hypothesis

/-! ## List specialization and controls -/

/-- Existing higher-order MIL vocabularies are exactly List-lifted
vocabularies for the generic construction. -/
noncomputable def ofListVocabulary
    (vocabulary : MILSchemaElaboration.Semantic.HigherOrderVocabulary.{u, u, u}) :
    LiftedVocabulary NativeIndexedFamilies.Semantic.List listLifting where
  toVocabulary := vocabulary.toVocabulary
  liftSort := vocabulary.listSort
  liftCarrier := vocabulary.listCarrier

/-- Translate the earlier List-specific syntax into the generic lifting
language without changing any program tree. -/
noncomputable def ofListHypothesis
    {vocabulary : MILSchemaElaboration.Semantic.HigherOrderVocabulary.{u, u, u}} :
    {source target : vocabulary.SortCode} →
      MILSchemaElaboration.Semantic.HigherOrderHypothesis vocabulary source target →
      Hypothesis (ofListVocabulary vocabulary) source target
  | _, _, .primitive symbol => .primitive symbol
  | _, _, .chain earlier later =>
      .chain (ofListHypothesis earlier) (ofListHypothesis later)
  | _, _, .map element => .lift (ofListHypothesis element)

/-- The generic translation preserves the exact proof-relevant denotation of
every existing List-lifted hypothesis. -/
theorem ofListHypothesis_denote
    {vocabulary : MILSchemaElaboration.Semantic.HigherOrderVocabulary.{u, u, u}}
    {source target : vocabulary.SortCode}
    (hypothesis :
      MILSchemaElaboration.Semantic.HigherOrderHypothesis vocabulary source target) :
    (ofListHypothesis hypothesis).denote = hypothesis.denote := by
  induction hypothesis with
  | primitive symbol => rfl
  | chain earlier later earlierHypothesis laterHypothesis =>
      change Semantic.Rel.Chain (ofListHypothesis earlier).denote
          (ofListHypothesis later).denote =
        Semantic.Rel.Chain earlier.denote later.denote
      rw [earlierHypothesis, laterHypothesis]
      rfl
  | map element hypothesis =>
      change reindex (vocabulary.listCarrier _) (vocabulary.listCarrier _)
          (NativeIndexedFamilies.Semantic.mapRel
            (ofListHypothesis element).denote) =
        MILSchemaElaboration.Semantic.reindexRelation
          (vocabulary.listCarrier _) (vocabulary.listCarrier _)
          (NativeIndexedFamilies.Semantic.mapRel element.denote)
      rw [hypothesis]
      rfl

/-- Negative control: a lifted hypothesis changes both endpoint sort codes;
it cannot be silently reused at the unlifted endpoints when the codes differ. -/
theorem lift_changes_distinct_endpoint
    {ObjectMap : Type u → Type u}
    {lifting : CompositionalLifting ObjectMap}
    {vocabulary : LiftedVocabulary ObjectMap lifting}
    {source target : vocabulary.SortCode}
    (sourceDistinct : vocabulary.liftSort source ≠ source)
    : ¬ (vocabulary.liftSort source = source ∧
      Nonempty (Hypothesis vocabulary (vocabulary.liftSort source)
        (vocabulary.liftSort target))) := by
  rintro ⟨sameSource, _lifted⟩
  exact sourceDistinct sameSource

#print axioms ListComposition.chainEquiv
#print axioms ListComposition.polynomialChainEquiv
#print axioms listLifting
#print axioms ofListHypothesis_denote
#print axioms lift_changes_distinct_endpoint

end NativeRelationLifting
end Mettapedia.Languages.MeTTa.PureKernel.Universe
