import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.RelationalInternalLanguage
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeIndexedFamilies

/-!
# Typed meta-interpretive hypotheses in Prime

The MIL chain metarule is not ordinary function composition.  Its result at
endpoints `x` and `z` retains an intermediate `y` together with evidence for
both relational premises.  This module gives that metarule two matching
presentations:

* an intrinsic, universe-polymorphic Prime term with lexical `Pi` binders;
* an indexed semantic hypothesis language whose constructors rule out
  ill-sorted predicate substitutions before search or example testing.

The semantic hypothesis language is the typed search space.  Example fitness,
search order, and runtime admission are deliberately separate consumers.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower

namespace MILSchemaElaboration

open Presentation
open Presentation.SchemaElaboration
open RelationalInternalLanguage

/-! ## Intrinsic chain metarule -/

namespace Intrinsic

def leftEvidenceLevel : LevelExpr := .param 3
def rightEvidenceLevel : LevelExpr := .param 4

/-- The result fibre must retain the middle value as well as both premise
derivations. -/
def resultEvidenceLevel : LevelExpr :=
  .max beta (.max leftEvidenceLevel rightEvidenceLevel)

/-- `(Rel A B) -> (Rel B C) -> Rel A C` in the lexical type context
`A : U alpha, B : U beta, C : U gamma`.  Evidence levels are explicit, and
the output level includes the level of `B` because witnesses retain `y : B`. -/
def chainBodyType : Tower.Tm 3 :=
  .pi
    (RelationalInternalLanguage.Intrinsic.Rel
      (.var 2) (.var 1) leftEvidenceLevel)
    (.pi
      (RelationalInternalLanguage.Intrinsic.Rel
        (.var 2) (.var 1) rightEvidenceLevel)
      (RelationalInternalLanguage.Intrinsic.Rel
        (.var 4) (.var 2) resultEvidenceLevel))

/-- `fun q r x z => Sigma y, q x y × r y z`. -/
def chainBodyTerm : Tower.Tm 3 :=
  .lam (.lam (.lam (.lam
    (RelationalInternalLanguage.Intrinsic.Chain
      (.var 5) (.var 3) (.var 2) (.var 1) (.var 0)))))

/-- Closed, universe-polymorphic chain schema with lexical type binders. -/
def chainSchemaType : Tower.Tm 0 :=
  .pi (sortTm alpha)
    (.pi (sortTm beta)
      (.pi (sortTm gamma) chainBodyType))

def chainSchemaTerm : Tower.Tm 0 :=
  .lam (.lam (.lam chainBodyTerm))

def chainCtxABCQ : Tower.Ctx 4 :=
  .snoc composeCtxABC
    (RelationalInternalLanguage.Intrinsic.Rel
      (.var 2) (.var 1) leftEvidenceLevel)

def chainCtxABCQR : Tower.Ctx 5 :=
  .snoc chainCtxABCQ
    (RelationalInternalLanguage.Intrinsic.Rel
      (.var 2) (.var 1) rightEvidenceLevel)

def chainCtxABCQRX : Tower.Ctx 6 :=
  .snoc chainCtxABCQR (.var 4)

def chainCtxABCQRXZ : Tower.Ctx 7 :=
  .snoc chainCtxABCQRX (.var 3)

@[simp] theorem chainCtxABC_lookup_A :
    Ctx.lookup composeCtxABC 2 = sortTm alpha := by
  decide

@[simp] theorem chainCtxABC_lookup_B :
    Ctx.lookup composeCtxABC 1 = sortTm beta := by
  decide

@[simp] theorem chainCtxABC_lookup_C :
    Ctx.lookup composeCtxABC 0 = sortTm gamma := by
  decide

@[simp] theorem chainCtxABCQ_lookup_B :
    Ctx.lookup chainCtxABCQ 2 = sortTm beta := by
  decide

@[simp] theorem chainCtxABCQ_lookup_C :
    Ctx.lookup chainCtxABCQ 1 = sortTm gamma := by
  decide

@[simp] theorem chainCtxABCQR_lookup_A :
    Ctx.lookup chainCtxABCQR 4 = sortTm alpha := by
  decide

@[simp] theorem chainCtxABCQR_lookup_C :
    Ctx.lookup chainCtxABCQR 2 = sortTm gamma := by
  decide

@[simp] theorem chainCtxABCQRXZ_lookup_A :
    Ctx.lookup chainCtxABCQRXZ 6 = sortTm alpha := by
  decide

@[simp] theorem chainCtxABCQRXZ_lookup_B :
    Ctx.lookup chainCtxABCQRXZ 5 = sortTm beta := by
  decide

@[simp] theorem chainCtxABCQRXZ_lookup_C :
    Ctx.lookup chainCtxABCQRXZ 4 = sortTm gamma := by
  decide

@[simp] theorem chainCtxABCQRXZ_lookup_q :
    Ctx.lookup chainCtxABCQRXZ 3 =
      RelationalInternalLanguage.Intrinsic.Rel
        (.var 6) (.var 5) leftEvidenceLevel := by
  decide

@[simp] theorem chainCtxABCQRXZ_lookup_r :
    Ctx.lookup chainCtxABCQRXZ 2 =
      RelationalInternalLanguage.Intrinsic.Rel
        (.var 5) (.var 4) rightEvidenceLevel := by
  decide

@[simp] theorem chainCtxABCQRXZ_lookup_x :
    Ctx.lookup chainCtxABCQRXZ 1 = (.var 6 : Tower.Tm 7) := by
  decide

@[simp] theorem chainCtxABCQRXZ_lookup_z :
    Ctx.lookup chainCtxABCQRXZ 0 = (.var 4 : Tower.Tm 7) := by
  decide

def leftRelationLevel : LevelExpr :=
  .max alpha (.max beta (.succ leftEvidenceLevel))

def rightRelationLevel : LevelExpr :=
  .max beta (.max gamma (.succ rightEvidenceLevel))

def resultRelationLevel : LevelExpr :=
  .max alpha (.max gamma (.succ resultEvidenceLevel))

def chainBodyLevel : LevelExpr :=
  .max leftRelationLevel (.max rightRelationLevel resultRelationLevel)

def chainSchemaLevel : LevelExpr :=
  .max (.succ alpha)
    (.max (.succ beta) (.max (.succ gamma) chainBodyLevel))

theorem leftRelation_hasType :
    Tower.HasType composeCtxABC
      (RelationalInternalLanguage.Intrinsic.Rel
        (.var 2) (.var 1) leftEvidenceLevel)
      (sortTm leftRelationLevel) := by
  exact RelationalInternalLanguage.Intrinsic.Rel_hasType
    (Presentation.HasType.var 2) (Presentation.HasType.var 1)

theorem rightRelation_after_q_hasType :
    Tower.HasType chainCtxABCQ
      (RelationalInternalLanguage.Intrinsic.Rel
        (.var 2) (.var 1) rightEvidenceLevel)
      (sortTm rightRelationLevel) := by
  exact RelationalInternalLanguage.Intrinsic.Rel_hasType
    (Presentation.HasType.var 2) (Presentation.HasType.var 1)

theorem resultRelation_after_qr_hasType :
    Tower.HasType chainCtxABCQR
      (RelationalInternalLanguage.Intrinsic.Rel
        (.var 4) (.var 2) resultEvidenceLevel)
      (sortTm resultRelationLevel) := by
  exact RelationalInternalLanguage.Intrinsic.Rel_hasType
    (Presentation.HasType.var 4) (Presentation.HasType.var 2)

/-- The chain metarule signature is independently formed in the cumulative
Prime tower. -/
theorem chainBodyType_hasType :
    Tower.HasType composeCtxABC chainBodyType (sortTm chainBodyLevel) := by
  unfold chainBodyType chainBodyLevel
  apply Presentation.HasType.piForm leftRelation_hasType (.sort _)
  · apply Presentation.HasType.piForm rightRelation_after_q_hasType (.sort _)
    · exact resultRelation_after_qr_hasType
    · exact .sort resultRelationLevel
    · exact .sorts rightRelationLevel resultRelationLevel
  · exact .sort (.max rightRelationLevel resultRelationLevel)
  · exact .sorts leftRelationLevel
      (.max rightRelationLevel resultRelationLevel)

theorem chainEvidence_hasType :
    Tower.HasType chainCtxABCQRXZ
      (RelationalInternalLanguage.Intrinsic.Chain
        (.var 5) (.var 3) (.var 2) (.var 1) (.var 0))
      (sortTm resultEvidenceLevel) := by
  exact RelationalInternalLanguage.Intrinsic.Chain_hasType
    (sourceType := (.var 6 : Tower.Tm 7))
    (middleType := (.var 5 : Tower.Tm 7))
    (targetType := (.var 4 : Tower.Tm 7))
    (earlier := (.var 3 : Tower.Tm 7))
    (later := (.var 2 : Tower.Tm 7))
    (source := (.var 1 : Tower.Tm 7))
    (target := (.var 0 : Tower.Tm 7))
    (middleLevel := beta)
    (earlierLevel := leftEvidenceLevel)
    (laterLevel := rightEvidenceLevel)
    (by exact Presentation.HasType.var 5)
    (by exact Presentation.HasType.var 3)
    (by exact Presentation.HasType.var 2)
    (by exact Presentation.HasType.var 1)
    (by exact Presentation.HasType.var 0)

/-- The implementation of chain inhabits the exact witness-retaining
relational schema. -/
theorem chainBodyTerm_hasType :
    Tower.HasType composeCtxABC chainBodyTerm chainBodyType := by
  unfold chainBodyTerm chainBodyType
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  unfold RelationalInternalLanguage.Intrinsic.Rel
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  exact chainEvidence_hasType

theorem chainSchemaType_hasType :
    Tower.HasType (.nil : Tower.Ctx 0) chainSchemaType
      (sortTm chainSchemaLevel) := by
  unfold chainSchemaType chainSchemaLevel
  apply Presentation.HasType.piForm
  · exact .headType (.sort alpha)
  · exact .sort (.succ alpha)
  · apply Presentation.HasType.piForm
    · exact .headType (.sort beta)
    · exact .sort (.succ beta)
    · apply Presentation.HasType.piForm
      · exact .headType (.sort gamma)
      · exact .sort (.succ gamma)
      · exact chainBodyType_hasType
      · exact .sort chainBodyLevel
      · exact .sorts (.succ gamma) chainBodyLevel
    · exact .sort (.max (.succ gamma) chainBodyLevel)
    · exact .sorts (.succ beta) (.max (.succ gamma) chainBodyLevel)
  · exact .sort
      (.max (.succ beta) (.max (.succ gamma) chainBodyLevel))
  · exact .sorts (.succ alpha)
      (.max (.succ beta) (.max (.succ gamma) chainBodyLevel))

theorem chainSchemaTerm_hasType :
    Tower.HasType (.nil : Tower.Ctx 0) chainSchemaTerm chainSchemaType := by
  unfold chainSchemaTerm chainSchemaType
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  exact chainBodyTerm_hasType

/-- Replacing the middle type by the target type changes the schema.  The
intermediate fibre is a genuine index, not an annotation. -/
theorem chain_middle_index_is_not_erasable :
    chainBodyType ≠
      (.pi
        (RelationalInternalLanguage.Intrinsic.Rel
          (.var 2) (.var 0) leftEvidenceLevel)
        (.pi
          (RelationalInternalLanguage.Intrinsic.Rel
            (.var 2) (.var 1) rightEvidenceLevel)
          (RelationalInternalLanguage.Intrinsic.Rel
            (.var 4) (.var 2) resultEvidenceLevel)) : Tower.Tm 3) := by
  decide

end Intrinsic

/-! ## Indexed semantic hypothesis space -/

namespace Semantic

universe uSort uCarrier uPrimitive

/-- A typed MIL vocabulary.  Primitive symbols are indexed by their source
and target sorts, and interpretation keeps full proof-relevant fibres. -/
structure Vocabulary where
  SortCode : Type uSort
  Carrier : SortCode → Type uCarrier
  Primitive : SortCode → SortCode → Type uPrimitive
  meaning : {source target : SortCode} →
    Primitive source target →
      RelationalInternalLanguage.Semantic.Rel
        (Carrier source) (Carrier target)

/-- A type-indexed MIL hypothesis.  `chain` can only be formed when the first
target and second source are definitionally the same sort. -/
inductive Hypothesis
    (vocabulary : Vocabulary.{uSort, uCarrier, uPrimitive}) :
    vocabulary.SortCode → vocabulary.SortCode →
      Type (max (max uSort uCarrier) uPrimitive) where
  | primitive {source target : vocabulary.SortCode}
      (symbol : vocabulary.Primitive source target) :
      Hypothesis vocabulary source target
  | chain {source middle target : vocabulary.SortCode}
      (earlier : Hypothesis vocabulary source middle)
      (later : Hypothesis vocabulary middle target) :
      Hypothesis vocabulary source target

namespace Hypothesis

/-- Interpretation is homomorphic: a learned chain denotes the same
proof-relevant horizontal composition as Prime's relational core. -/
def denote {vocabulary : Vocabulary} {source target : vocabulary.SortCode} :
    Hypothesis vocabulary source target →
      RelationalInternalLanguage.Semantic.Rel
        (vocabulary.Carrier source) (vocabulary.Carrier target)
  | .primitive symbol => vocabulary.meaning symbol
  | .chain earlier later =>
      RelationalInternalLanguage.Semantic.Rel.Chain
        earlier.denote later.denote

@[simp] theorem denote_primitive {vocabulary : Vocabulary}
    {source target : vocabulary.SortCode}
    (symbol : vocabulary.Primitive source target) :
    (Hypothesis.primitive symbol).denote = vocabulary.meaning symbol :=
  rfl

@[simp] theorem denote_chain {vocabulary : Vocabulary}
    {source middle target : vocabulary.SortCode}
    (earlier : Hypothesis vocabulary source middle)
    (later : Hypothesis vocabulary middle target) :
    (Hypothesis.chain earlier later).denote =
      RelationalInternalLanguage.Semantic.Rel.Chain
        earlier.denote later.denote :=
  rfl

/-- A chain witness exposes the retained intermediate value and both premise
derivations exactly. -/
def chainEvidenceEquiv {vocabulary : Vocabulary}
    {source middle target : vocabulary.SortCode}
    (earlier : Hypothesis vocabulary source middle)
    (later : Hypothesis vocabulary middle target)
    (input : vocabulary.Carrier source)
    (output : vocabulary.Carrier target) :
    (Hypothesis.chain earlier later).denote.evidence input output ≃
      Sigma fun intermediate : vocabulary.Carrier middle =>
        earlier.denote.evidence input intermediate ×
          later.denote.evidence intermediate output :=
  Equiv.refl _

end Hypothesis

/-! ## Higher-order list lifting -/

/-- Additional structure for vocabularies whose sort language contains the
native Prime List former.  The equivalence is explicit so the sort code need
not be definitionally equal to a Lean type expression. -/
structure HigherOrderVocabulary extends Vocabulary where
  listSort : SortCode → SortCode
  listCarrier : ∀ sort,
    Carrier (listSort sort) ≃
      NativeIndexedFamilies.Semantic.List (Carrier sort)

/-- Reindex both endpoints of a proof-relevant relation along equivalences. -/
def reindexRelation {Source Target ReindexedSource ReindexedTarget : Type u}
    (source : ReindexedSource ≃ Source)
    (target : ReindexedTarget ≃ Target)
    (relation : RelationalInternalLanguage.Semantic.Rel Source Target) :
    RelationalInternalLanguage.Semantic.Rel ReindexedSource ReindexedTarget where
  evidence reindexedSource reindexedTarget :=
    relation.evidence (source reindexedSource) (target reindexedTarget)

/-- Higher-order MIL hypotheses add only the native relational List lifting.
`map` lifts evidence pointwise; it never assumes the element relation is a
function. -/
inductive HigherOrderHypothesis
    (vocabulary : HigherOrderVocabulary.{uSort, uCarrier, uPrimitive}) :
    vocabulary.SortCode → vocabulary.SortCode →
      Type (max (max uSort uCarrier) uPrimitive) where
  | primitive {source target : vocabulary.SortCode}
      (symbol : vocabulary.Primitive source target) :
      HigherOrderHypothesis vocabulary source target
  | chain {source middle target : vocabulary.SortCode}
      (earlier : HigherOrderHypothesis vocabulary source middle)
      (later : HigherOrderHypothesis vocabulary middle target) :
      HigherOrderHypothesis vocabulary source target
  | map {source target : vocabulary.SortCode}
      (element : HigherOrderHypothesis vocabulary source target) :
      HigherOrderHypothesis vocabulary
        (vocabulary.listSort source) (vocabulary.listSort target)

namespace HigherOrderHypothesis

noncomputable def denote
    {vocabulary : HigherOrderVocabulary}
    {source target : vocabulary.SortCode} :
    HigherOrderHypothesis vocabulary source target →
      RelationalInternalLanguage.Semantic.Rel
        (vocabulary.Carrier source) (vocabulary.Carrier target)
  | .primitive symbol => vocabulary.meaning symbol
  | .chain earlier later =>
      RelationalInternalLanguage.Semantic.Rel.Chain
        earlier.denote later.denote
  | .map (source := source) (target := target) element =>
      reindexRelation (vocabulary.listCarrier source)
        (vocabulary.listCarrier target)
        (NativeIndexedFamilies.Semantic.mapRel element.denote)

@[simp] theorem denote_primitive
    {vocabulary : HigherOrderVocabulary}
    {source target : vocabulary.SortCode}
    (symbol : vocabulary.Primitive source target) :
    (HigherOrderHypothesis.primitive symbol).denote =
      vocabulary.meaning symbol :=
  rfl

@[simp] theorem denote_chain
    {vocabulary : HigherOrderVocabulary}
    {source middle target : vocabulary.SortCode}
    (earlier : HigherOrderHypothesis vocabulary source middle)
    (later : HigherOrderHypothesis vocabulary middle target) :
    (HigherOrderHypothesis.chain earlier later).denote =
      RelationalInternalLanguage.Semantic.Rel.Chain
        earlier.denote later.denote :=
  rfl

@[simp] theorem denote_map
    {vocabulary : HigherOrderVocabulary}
    {source target : vocabulary.SortCode}
    (element : HigherOrderHypothesis vocabulary source target) :
    (HigherOrderHypothesis.map element).denote =
      reindexRelation (vocabulary.listCarrier source)
        (vocabulary.listCarrier target)
        (NativeIndexedFamilies.Semantic.mapRel element.denote) :=
  rfl

end HigherOrderHypothesis

/-! ## Grandparent canary -/

inductive ExampleSort where
  | person
  | number
  | list (element : ExampleSort)
deriving DecidableEq, Repr

inductive Person where
  | alice
  | bob
  | carol
deriving DecidableEq, Repr

def ExampleCarrier : ExampleSort → Type
  | .person => Person
  | .number => Nat
  | .list element =>
      NativeIndexedFamilies.Semantic.List (ExampleCarrier element)

inductive ExamplePrimitive : ExampleSort → ExampleSort → Type where
  | mother : ExamplePrimitive .person .person
  | father : ExamplePrimitive .person .person
  | successor : ExamplePrimitive .number .number

inductive MotherEvidence : Person → Person → Type where
  | alice_bob : MotherEvidence .alice .bob

inductive FatherEvidence : Person → Person → Type where
  | bob_carol : FatherEvidence .bob .carol

inductive SuccessorEvidence : Nat → Nat → Type where
  | step (source : Nat) : SuccessorEvidence source (source + 1)

def examplePrimitiveMeaning :
    {source target : ExampleSort} →
      ExamplePrimitive source target →
        RelationalInternalLanguage.Semantic.Rel
          (ExampleCarrier source) (ExampleCarrier target)
  | _, _, .mother => ⟨MotherEvidence⟩
  | _, _, .father => ⟨FatherEvidence⟩
  | _, _, .successor => ⟨SuccessorEvidence⟩

def exampleVocabulary : Vocabulary where
  SortCode := ExampleSort
  Carrier := ExampleCarrier
  Primitive := ExamplePrimitive
  meaning := examplePrimitiveMeaning

def exampleHigherOrderVocabulary : HigherOrderVocabulary where
  toVocabulary := exampleVocabulary
  listSort := .list
  listCarrier := fun _ => Equiv.refl _

def motherHypothesis :
    Hypothesis exampleVocabulary .person .person :=
  .primitive .mother

def fatherHypothesis :
    Hypothesis exampleVocabulary .person .person :=
  .primitive .father

def grandparentHypothesis :
    Hypothesis exampleVocabulary .person .person :=
  .chain motherHypothesis fatherHypothesis

/-- The learned chain retains Bob as the intermediate occurrence and retains
both source facts as evidence. -/
def grandparentEvidence :
    grandparentHypothesis.denote.evidence Person.alice Person.carol :=
  ⟨Person.bob, MotherEvidence.alice_bob, FatherEvidence.bob_carol⟩

theorem grandparent_intermediate_is_retained :
    Nonempty
      (Sigma fun intermediate : Person =>
        MotherEvidence Person.alice intermediate ×
          FatherEvidence intermediate Person.carol) :=
  ⟨⟨Person.bob, MotherEvidence.alice_bob, FatherEvidence.bob_carol⟩⟩

/-- Every hypothesis in this example vocabulary is endosorted, because all
primitive declarations are endosorted and chain preserves the shared index. -/
theorem exampleHypothesis_endpoints_eq
    {source target : ExampleSort}
    (hypothesis : Hypothesis exampleVocabulary source target) :
    source = target :=
  match hypothesis with
  | .primitive symbol => by cases symbol <;> rfl
  | .chain earlier later =>
      (exampleHypothesis_endpoints_eq earlier).trans
        (exampleHypothesis_endpoints_eq later)
termination_by sizeOf hypothesis

/-- A person-to-number candidate is absent from the typed hypothesis space;
it is not generated and then rejected by example testing. -/
theorem person_to_number_hypothesis_uninhabited :
    ¬ Nonempty (Hypothesis exampleVocabulary .person .number) := by
  rintro ⟨hypothesis⟩
  have impossible := exampleHypothesis_endpoints_eq hypothesis
  cases impossible

/-! ## Higher-order map canary -/

def successorHypothesis :
    HigherOrderHypothesis exampleHigherOrderVocabulary .number .number :=
  .primitive .successor

def twiceHypothesis :
    HigherOrderHypothesis exampleHigherOrderVocabulary .number .number :=
  .chain successorHypothesis successorHypothesis

def mapTwiceHypothesis :
    HigherOrderHypothesis exampleHigherOrderVocabulary
      (.list .number) (.list .number) :=
  .map twiceHypothesis

def oneList : NativeIndexedFamilies.Semantic.List Nat :=
  NativeIndexedFamilies.Semantic.cons 1
    NativeIndexedFamilies.Semantic.nil

def threeList : NativeIndexedFamilies.Semantic.List Nat :=
  NativeIndexedFamilies.Semantic.cons 3
    NativeIndexedFamilies.Semantic.nil

def one : exampleHigherOrderVocabulary.Carrier .number :=
  (1 : Nat)

def two : exampleHigherOrderVocabulary.Carrier .number :=
  (2 : Nat)

def three : exampleHigherOrderVocabulary.Carrier .number :=
  (3 : Nat)

def twiceOneEvidence :
    twiceHypothesis.denote.evidence one three :=
  ⟨two, SuccessorEvidence.step 1, SuccessorEvidence.step 2⟩

/-- Higher-order map retains the element-level chain evidence, including its
intermediate value, under the native List proof spine. -/
noncomputable def mapTwiceEvidence :
    mapTwiceHypothesis.denote.evidence oneList threeList :=
  Mettapedia.TypeTheory.IndexedPolynomial.ListExample.ListRel.cons
    twiceOneEvidence
    Mettapedia.TypeTheory.IndexedPolynomial.ListExample.ListRel.nil

theorem mapTwice_retains_element_chain :
    Nonempty (mapTwiceHypothesis.denote.evidence oneList threeList) :=
  ⟨mapTwiceEvidence⟩

theorem exampleHigherOrderHypothesis_endpoints_eq
    {source target : ExampleSort}
    (hypothesis : HigherOrderHypothesis
      exampleHigherOrderVocabulary source target) :
    source = target :=
  match hypothesis with
  | .primitive symbol => by cases symbol <;> rfl
  | .chain earlier later =>
      (exampleHigherOrderHypothesis_endpoints_eq earlier).trans
        (exampleHigherOrderHypothesis_endpoints_eq later)
  | .map element =>
      congrArg ExampleSort.list
        (exampleHigherOrderHypothesis_endpoints_eq element)
termination_by sizeOf hypothesis

/-- List lifting does not permit a person relation to masquerade as a
number-list relation. -/
theorem person_to_number_list_hypothesis_uninhabited :
    ¬ Nonempty
      (HigherOrderHypothesis exampleHigherOrderVocabulary
        .person (.list .number)) := by
  rintro ⟨hypothesis⟩
  have impossible := exampleHigherOrderHypothesis_endpoints_eq hypothesis
  cases impossible

end Semantic

#print axioms Intrinsic.chainSchemaType_hasType
#print axioms Intrinsic.chainSchemaTerm_hasType
#print axioms Intrinsic.chain_middle_index_is_not_erasable
#print axioms Semantic.grandparent_intermediate_is_retained
#print axioms Semantic.person_to_number_hypothesis_uninhabited
#print axioms Semantic.mapTwice_retains_element_chain
#print axioms Semantic.person_to_number_list_hypothesis_uninhabited

end MILSchemaElaboration

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
