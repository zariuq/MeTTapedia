import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveNativeListDeclarations
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.IntrinsicNativeListCanonicalSemantics

/-!
# Formation-sensitive admission of existing canonical native List spines

The existing `CanonicalList`, `CanonicalMapRel`, `encodeList`, `encodeMapRel`
and polynomial interpretation are reused unchanged. Additional proof-only
evidence checks each retained raw leaf in the formation-sensitive judgment;
it neither reconstructs different spine data nor casts raw typing into the
refined relation. The conclusion concerns finite constructor images, not
arbitrary inhabitants or the operational behavior of eliminators.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FormationSensitiveNativeList

open Presentation NativeIndexedFamilies IntrinsicCanonicalSemantics
open Mettapedia.TypeTheory.IndexedPolynomial

variable {n : Nat} {context : Tower.Ctx n}

/-- Refined formation is checked separately for each original element. -/
def ListTyping {element : Tower.Tm n} (list : CanonicalList context element) : Prop :=
  ∀ head ∈ list, Typing context head.term element

theorem ListTyping.nil {element : Tower.Tm n} :
    ListTyping ([] : CanonicalList context element) := by
  intro head membership
  cases membership

theorem ListTyping.cons {element : Tower.Tm n}
    {head : TypedTerm context element} {tail : CanonicalList context element}
    (headTyping : Typing context head.term element) (tailTyping : ListTyping tail) :
    ListTyping (head :: tail) := by
  intro candidate membership
  rcases List.mem_cons.mp membership with rfl | inTail
  · exact headTyping
  · exact tailTyping candidate inTail

theorem ListTyping.head {element : Tower.Tm n}
    {head : TypedTerm context element} {tail : CanonicalList context element}
    (typed : ListTyping (head :: tail)) : Typing context head.term element :=
  typed head (List.mem_cons_self ..)

theorem ListTyping.tail {element : Tower.Tm n}
    {head : TypedTerm context element} {tail : CanonicalList context element}
    (typed : ListTyping (head :: tail)) : ListTyping tail := by
  intro candidate membership
  exact typed candidate (List.mem_cons_of_mem _ membership)

/-- The exact existing raw List encoding has a refined typing derivation. -/
theorem encodeList_typing {element : Tower.Tm n}
    (elementTyping : Typing context element (sortTm Intrinsic.elementLevel))
    (list : CanonicalList context element) (leaves : ListTyping list) :
    Typing context (encodeList element list) (Intrinsic.listApp element) := by
  induction list with
  | nil => exact nilApp_hasType elementTyping
  | cons head tail ih =>
      exact consApp_hasType elementTyping leaves.head (ih leaves.tail)

theorem encodeList_judgment {element : Tower.Tm n}
    (formedContext : FormationSensitive.ContextFormation IntrinsicRelator.rules context)
    (elementTyping : Typing context element (sortTm Intrinsic.elementLevel))
    (list : CanonicalList context element) (leaves : ListTyping list) :
    FormationSensitive.Judgment IntrinsicRelator.rules context
      (encodeList element list) (Intrinsic.listApp element) :=
  ⟨formedContext, encodeList_typing elementTyping list leaves⟩

/-- Proof-only leaf obligations indexed by the original evidence spine.
Both endpoints and the exact raw relation witness are independently typed. -/
inductive EvidenceTyping {source target relation : Tower.Tm n} :
    {sourceList : CanonicalList context source} →
    {targetList : CanonicalList context target} →
    CanonicalMapRel relation sourceList targetList → Prop where
  | nil : EvidenceTyping .nil
  | cons {sourceHead : TypedTerm context source} {targetHead : TypedTerm context target}
      {sourceTail : CanonicalList context source} {targetTail : CanonicalList context target}
      {headEvidence : TypedRelationEvidence relation sourceHead targetHead}
      {tailEvidence : CanonicalMapRel relation sourceTail targetTail} :
      Typing context sourceHead.term source →
      Typing context targetHead.term target →
      Typing context headEvidence.term (.app (.app relation sourceHead.term) targetHead.term) →
      EvidenceTyping tailEvidence → EvidenceTyping (.cons headEvidence tailEvidence)

theorem EvidenceTyping.sourceList {source target relation : Tower.Tm n}
    {sourceList : CanonicalList context source} {targetList : CanonicalList context target}
    {evidence : CanonicalMapRel relation sourceList targetList}
    (typed : EvidenceTyping evidence) : ListTyping sourceList := by
  induction typed with
  | nil => exact ListTyping.nil
  | cons sourceTyping _ _ _ ih => exact ih.cons sourceTyping

theorem EvidenceTyping.targetList {source target relation : Tower.Tm n}
    {sourceList : CanonicalList context source} {targetList : CanonicalList context target}
    {evidence : CanonicalMapRel relation sourceList targetList}
    (typed : EvidenceTyping evidence) : ListTyping targetList := by
  induction typed with
  | nil => exact ListTyping.nil
  | cons _ targetTyping _ _ ih => exact ih.cons targetTyping

/-- Every finite canonical relational proof spine is admitted without changing
any argument or retained evidence term in the native encoding. -/
theorem encodeMapRel_typing {source target relation : Tower.Tm n}
    (sourceTyping : Typing context source (sortTm Intrinsic.elementLevel))
    (targetTyping : Typing context target (sortTm Intrinsic.elementLevel))
    (relationTyping : Typing context relation
      (.pi source (.pi (rename wk target) (sortTm Intrinsic.motiveLevel))))
    {sourceList : CanonicalList context source} {targetList : CanonicalList context target}
    (evidence : CanonicalMapRel relation sourceList targetList)
    (leaves : EvidenceTyping evidence) :
    Typing context (encodeMapRel evidence)
      (IntrinsicRelator.mapRelApp source target relation
        (encodeList source sourceList) (encodeList target targetList)) := by
  induction leaves with
  | nil => exact nilRelApp_hasType sourceTyping targetTyping relationTyping
  | @cons sourceHead targetHead sourceTail targetTail headEvidence tailEvidence
      sourceHeadTyping targetHeadTyping headTyping tailTyping ih =>
      exact consRelApp_hasType sourceTyping targetTyping relationTyping
        sourceHeadTyping targetHeadTyping
        (encodeList_typing sourceTyping sourceTail tailTyping.sourceList)
        (encodeList_typing targetTyping targetTail tailTyping.targetList)
        headTyping ih

theorem encodeMapRel_judgment {source target relation : Tower.Tm n}
    (formedContext : FormationSensitive.ContextFormation IntrinsicRelator.rules context)
    (sourceTyping : Typing context source (sortTm Intrinsic.elementLevel))
    (targetTyping : Typing context target (sortTm Intrinsic.elementLevel))
    (relationTyping : Typing context relation
      (.pi source (.pi (rename wk target) (sortTm Intrinsic.motiveLevel))))
    {sourceList : CanonicalList context source} {targetList : CanonicalList context target}
    (evidence : CanonicalMapRel relation sourceList targetList)
    (leaves : EvidenceTyping evidence) :
    FormationSensitive.Judgment IntrinsicRelator.rules context (encodeMapRel evidence)
      (IntrinsicRelator.mapRelApp source target relation
        (encodeList source sourceList) (encodeList target targetList)) :=
  ⟨formedContext, encodeMapRel_typing sourceTyping targetTyping relationTyping evidence leaves⟩

/-- Refined admission composes with the existing independently proved
canonical-to-polynomial evidence correspondence. The original evidence
remains the argument to both interpretations. -/
theorem encodeMapRel_judgment_and_semanticEvidence {source target relation : Tower.Tm n}
    (formedContext : FormationSensitive.ContextFormation IntrinsicRelator.rules context)
    (sourceTyping : Typing context source (sortTm Intrinsic.elementLevel))
    (targetTyping : Typing context target (sortTm Intrinsic.elementLevel))
    (relationTyping : Typing context relation
      (.pi source (.pi (rename wk target) (sortTm Intrinsic.motiveLevel))))
    {sourceList : CanonicalList context source} {targetList : CanonicalList context target}
    (evidence : CanonicalMapRel relation sourceList targetList)
    (leaves : EvidenceTyping evidence) :
    FormationSensitive.Judgment IntrinsicRelator.rules context (encodeMapRel evidence)
      (IntrinsicRelator.mapRelApp source target relation
        (encodeList source sourceList) (encodeList target targetList)) ∧
    Nonempty ((Semantic.mapRel (typedRelation relation)).evidence
      (interpretList sourceList) (interpretList targetList)) :=
  ⟨encodeMapRel_judgment formedContext sourceTyping targetTyping relationTyping evidence leaves,
    ⟨canonicalMapRelEquiv sourceList targetList evidence⟩⟩

/-- On fixed canonical endpoints, the unchanged native term and the existing
polynomial interpretation distinguish exactly the same evidence spines.
This is equality of receipts, not merely agreement of inhabited support. -/
theorem encodeMapRel_eq_iff_semanticEvidence_eq {source target relation : Tower.Tm n}
    {sourceList : CanonicalList context source} {targetList : CanonicalList context target}
    (first second : CanonicalMapRel relation sourceList targetList) :
    encodeMapRel first = encodeMapRel second ↔
      canonicalMapRelEquiv sourceList targetList first =
        canonicalMapRelEquiv sourceList targetList second := by
  constructor
  · intro equal
    exact congrArg (canonicalMapRelEquiv sourceList targetList)
      (encodeMapRel_injective sourceList targetList equal)
  · intro equal
    exact congrArg encodeMapRel
      ((canonicalMapRelEquiv sourceList targetList).injective equal)

/-! ## A two-element spine retaining different receipts at identical endpoints -/

namespace Examples

open IntrinsicRelator

def contextABRX : Tower.Ctx 4 := .snoc contextABR (.var 2)
def contextABRXY : Tower.Ctx 5 := .snoc contextABRX (.var 2)
def contextABRXYE : Tower.Ctx 6 :=
  .snoc contextABRXY (.app (.app (.var 2) (.var 1)) (.var 0))
def contextABRXYEE : Tower.Ctx 7 :=
  .snoc contextABRXYE (.app (.app (.var 3) (.var 2)) (.var 1))

theorem relation_fibre_formed : Typing contextABRXY
    (.app (.app (.var 2) (.var 1)) (.var 0)) (sortTm Intrinsic.motiveLevel) := by
  apply relationApp_hasType (source := (.var 4 : Tower.Tm 5))
    (target := .var 3) (relation := .var 2)
  · exact FormationSensitive.Typing.var 2
  · exact FormationSensitive.Typing.var 1
  · exact FormationSensitive.Typing.var 0

theorem context_formed : FormationSensitive.ContextFormation rules contextABRXYEE := by
  apply FormationSensitive.ContextFormation.snoc
  · apply FormationSensitive.ContextFormation.snoc
    · apply FormationSensitive.ContextFormation.snoc
      · apply FormationSensitive.ContextFormation.snoc
        · apply FormationSensitive.ContextFormation.snoc
          · exact .snoc (.snoc .nil (.headType (.sort Intrinsic.elementLevel))
              (.sort (.succ Intrinsic.elementLevel)))
              (.headType (.sort Intrinsic.elementLevel)) (.sort (.succ Intrinsic.elementLevel))
          · exact relationType_hasType
          · exact .sort relationTypeLevel
        · exact FormationSensitive.Typing.var 2
        · exact .sort Intrinsic.elementLevel
      · exact FormationSensitive.Typing.var 2
      · exact .sort Intrinsic.elementLevel
    · exact relation_fibre_formed
    · exact .sort Intrinsic.motiveLevel
  · exact relation_fibre_formed.weaken
  · exact .sort Intrinsic.motiveLevel

def sourceHead : TypedTerm contextABRXYEE (.var 6) :=
  ⟨.var 3, (FormationSensitive.Typing.var (R := rules) (Γ := contextABRXYEE) 3).toRaw⟩
def targetHead : TypedTerm contextABRXYEE (.var 5) :=
  ⟨.var 2, (FormationSensitive.Typing.var (R := rules) (Γ := contextABRXYEE) 2).toRaw⟩
def firstReceipt : TypedRelationEvidence (.var 4) sourceHead targetHead :=
  ⟨.var 1, (FormationSensitive.Typing.var (R := rules) (Γ := contextABRXYEE) 1).toRaw⟩
def secondReceipt : TypedRelationEvidence (.var 4) sourceHead targetHead :=
  ⟨.var 0, (FormationSensitive.Typing.var (R := rules) (Γ := contextABRXYEE) 0).toRaw⟩

def evidence : CanonicalMapRel (.var 4) [sourceHead, sourceHead] [targetHead, targetHead] :=
  .cons firstReceipt (.cons secondReceipt .nil)
def alteredEvidence : CanonicalMapRel (.var 4)
    [sourceHead, sourceHead] [targetHead, targetHead] :=
  .cons secondReceipt (.cons secondReceipt .nil)

theorem evidence_typed : EvidenceTyping evidence := by
  apply EvidenceTyping.cons
  · exact FormationSensitive.Typing.var 3
  · exact FormationSensitive.Typing.var 2
  · exact FormationSensitive.Typing.var 1
  · apply EvidenceTyping.cons
    · exact FormationSensitive.Typing.var 3
    · exact FormationSensitive.Typing.var 2
    · exact FormationSensitive.Typing.var 0
    · exact .nil

theorem two_element_admitted : FormationSensitive.Judgment rules contextABRXYEE
    (encodeMapRel evidence)
    (mapRelApp (.var 6) (.var 5) (.var 4)
      (encodeList (.var 6) [sourceHead, sourceHead])
      (encodeList (.var 5) [targetHead, targetHead])) :=
  encodeMapRel_judgment context_formed (FormationSensitive.Typing.var 6)
    (FormationSensitive.Typing.var 5) (FormationSensitive.Typing.var 4)
    evidence evidence_typed

/-- Equal endpoints do not allow replacing one retained relation receipt by
another while claiming the encoded native proof is unchanged. -/
theorem different_receipt_changes_native_term :
    encodeMapRel evidence ≠ encodeMapRel alteredEvidence := by
  apply encodedCons_ne_of_headTerm_ne
  decide

/-- A missing tail receipt cannot be filled by the empty constructor when
the actual source and target spines have different lengths. -/
theorem missing_tail_rejected :
    ¬ Nonempty (CanonicalMapRel (.var 4) [sourceHead, sourceHead] [targetHead]) := by
  rintro ⟨witness⟩
  cases witness with
  | cons _ tail => cases tail

end Examples

#print axioms encodeList_judgment
#print axioms encodeMapRel_judgment
#print axioms encodeMapRel_judgment_and_semanticEvidence
#print axioms encodeMapRel_eq_iff_semanticEvidence_eq
#print axioms Examples.context_formed
#print axioms Examples.two_element_admitted
#print axioms Examples.different_receipt_changes_native_term
#print axioms Examples.missing_tail_rejected

end FormationSensitiveNativeList
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
