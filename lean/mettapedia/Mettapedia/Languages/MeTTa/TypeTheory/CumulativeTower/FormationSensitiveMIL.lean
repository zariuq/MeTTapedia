import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveRegularity
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.IntrinsicMILSemanticAdequacy

/-!
# Formation-sensitive admission of intrinsic MIL programs

The existing hypothesis syntax and its independent relational denotation are
unchanged. Formation-sensitive leaf evidence and actual closed declaration
certificates admit every primitive/chain program. This does not authorize
arbitrary conversion, eliminator reduction, or higher-order lifting.

Only the family and its two constructors are used below; the dependent
eliminator declaration is not a dependency of constructor quotation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FormationSensitiveMIL

open Presentation Presentation.Declaration IntrinsicMILHypothesis

variable {n : Nat}

/-- The refined judgment uses exactly the existing native hypothesis rules. -/
abbrev Typing (context : Tower.Ctx n) (term type : Tower.Tm n) : Prop :=
  FormationSensitive.Typing IntrinsicMILHypothesis.rules context term type

/-! ## Closed formation certificates and constructor applications -/

theorem primitiveFamilyType_hasType :
    Typing contextS primitiveFamilyType
      (sortTm primitiveFamilyTypeLevel) := by
  unfold contextS primitiveFamilyType primitiveFamilyTypeLevel
  apply FormationSensitive.Typing.piForm
  · exact FormationSensitive.Typing.var 0
  · exact .sort sortLevel
  · apply FormationSensitive.Typing.piForm
    · exact FormationSensitive.Typing.var 1
    · exact .sort sortLevel
    · exact .headType (.sort primitiveLevel)
    · exact .sort (.succ primitiveLevel)
    · exact .sorts sortLevel (.succ primitiveLevel)
  · exact .sort (.max sortLevel (.succ primitiveLevel))
  · exact .sorts sortLevel (.max sortLevel (.succ primitiveLevel))

theorem hypothesisIndexType_hasType :
    Typing contextSP hypothesisIndexType
      (sortTm hypothesisIndexLevel) := by
  unfold contextSP hypothesisIndexType hypothesisIndexLevel
  apply FormationSensitive.Typing.piForm
  · exact FormationSensitive.Typing.var 1
  · exact .sort sortLevel
  · apply FormationSensitive.Typing.piForm
    · exact FormationSensitive.Typing.var 2
    · exact .sort sortLevel
    · exact .headType (.sort hypothesisLevel)
    · exact .sort (.succ hypothesisLevel)
    · exact .sorts sortLevel (.succ hypothesisLevel)
  · exact .sort (.max sortLevel (.succ hypothesisLevel))
  · exact .sorts sortLevel (.max sortLevel (.succ hypothesisLevel))

theorem hypothesisType_hasType :
    Typing (.nil : Tower.Ctx 0) hypothesisType
      (sortTm hypothesisDeclarationLevel) := by
  unfold hypothesisType hypothesisDeclarationLevel hypothesisAfterPrimitiveLevel
  apply FormationSensitive.Typing.piForm
  · exact .headType (.sort sortLevel)
  · exact .sort (.succ sortLevel)
  · apply FormationSensitive.Typing.piForm
    · exact primitiveFamilyType_hasType
    · exact .sort primitiveFamilyTypeLevel
    · exact hypothesisIndexType_hasType
    · exact .sort hypothesisIndexLevel
    · exact .sorts primitiveFamilyTypeLevel hypothesisIndexLevel
  · exact .sort hypothesisAfterPrimitiveLevel
  · exact .sorts (.succ sortLevel) hypothesisAfterPrimitiveLevel

theorem hypothesisConstant_hasType {context : Tower.Ctx n} :
    Typing context (.const hypothesisName) (liftClosed hypothesisType) := by
  apply FormationSensitive.Typing.const (u := .sort hypothesisDeclarationLevel)
  · change combinedType Tower.rules rawSignature hypothesisName = some hypothesisType
    apply combinedType_of_signature
    · rfl
    · exact typeOf_hypothesis
  · exact hypothesisType_hasType
  · exact .sort hypothesisDeclarationLevel

theorem hypothesisApp_hasType {context : Tower.Ctx n}
    {sorts primitives source target : Tower.Tm n}
    (sortsTyping : Typing context sorts (sortTm sortLevel))
    (primitivesTyping : Typing context primitives
      (.pi sorts (.pi (Presentation.rename wk sorts)
        (sortTm primitiveLevel))))
    (sourceTyping : Typing context source sorts)
    (targetTyping : Typing context target sorts) :
    Typing context (hypothesisApp sorts primitives source target)
      (sortTm hypothesisLevel) := by
  have afterSorts := FormationSensitive.Typing.appElim
    (hypothesisConstant_hasType (context := context)) sortsTyping
  have afterPrimitives := FormationSensitive.Typing.appElim afterSorts
    primitivesTyping
  change Typing context _
    (Presentation.subst (subst0 primitives)
      (Presentation.subst (liftSub (subst0 sorts))
        (Presentation.rename (liftRen (liftRen Fin.elim0))
          hypothesisIndexType))) at afterPrimitives
  rw [instantiateTwo_hypothesisIndexType sorts primitives] at afterPrimitives
  have afterSource := FormationSensitive.Typing.appElim afterPrimitives sourceTyping
  have targetTypingExpected : Typing context target
      (Presentation.inst0 source (Presentation.rename wk sorts)) := by
    rw [Presentation.inst0_rename_wk]
    exact targetTyping
  have afterTarget := FormationSensitive.Typing.appElim afterSource
    targetTypingExpected
  exact afterTarget

theorem primitiveFamilyApp_hasType {context : Tower.Ctx n}
    {sorts primitives source target : Tower.Tm n}
    (primitivesTyping : Typing context primitives
      (.pi sorts (.pi (Presentation.rename wk sorts)
        (sortTm primitiveLevel))))
    (sourceTyping : Typing context source sorts)
    (targetTyping : Typing context target sorts) :
    Typing context (.app (.app primitives source) target)
      (sortTm primitiveLevel) := by
  have afterSource := FormationSensitive.Typing.appElim primitivesTyping sourceTyping
  have targetTypingExpected : Typing context target
      (Presentation.inst0 source (Presentation.rename wk sorts)) := by
    rw [Presentation.inst0_rename_wk]
    exact targetTyping
  exact FormationSensitive.Typing.appElim afterSource targetTypingExpected

theorem primitiveBodyType_hasType :
    Typing contextSP primitiveBodyType (sortTm primitiveBodyLevel) := by
  unfold primitiveBodyType primitiveBodyLevel primitiveAfterTargetLevel
    primitiveAfterSymbolLevel
  apply FormationSensitive.Typing.piForm
  · exact FormationSensitive.Typing.var 1
  · exact .sort sortLevel
  · apply FormationSensitive.Typing.piForm
    · exact FormationSensitive.Typing.var 2
    · exact .sort sortLevel
    · apply FormationSensitive.Typing.piForm
      · apply primitiveFamilyApp_hasType
        · exact FormationSensitive.Typing.var 2
        · exact FormationSensitive.Typing.var 1
        · exact FormationSensitive.Typing.var 0
      · exact .sort primitiveLevel
      · apply hypothesisApp_hasType
        · exact FormationSensitive.Typing.var 4
        · exact FormationSensitive.Typing.var 3
        · exact FormationSensitive.Typing.var 2
        · exact FormationSensitive.Typing.var 1
      · exact .sort hypothesisLevel
      · exact .sorts primitiveLevel hypothesisLevel
    · exact .sort primitiveAfterSymbolLevel
    · exact .sorts sortLevel primitiveAfterSymbolLevel
  · exact .sort primitiveAfterTargetLevel
  · exact .sorts sortLevel primitiveAfterTargetLevel

theorem primitiveType_hasType :
    Typing (.nil : Tower.Ctx 0) primitiveType
      (sortTm primitiveDeclarationLevel) := by
  unfold primitiveType primitiveDeclarationLevel primitiveAfterPrimitiveLevel
  apply FormationSensitive.Typing.piForm
  · exact .headType (.sort sortLevel)
  · exact .sort (.succ sortLevel)
  · apply FormationSensitive.Typing.piForm
    · exact primitiveFamilyType_hasType
    · exact .sort primitiveFamilyTypeLevel
    · exact primitiveBodyType_hasType
    · exact .sort primitiveBodyLevel
    · exact .sorts primitiveFamilyTypeLevel primitiveBodyLevel
  · exact .sort primitiveAfterPrimitiveLevel
  · exact .sorts (.succ sortLevel) primitiveAfterPrimitiveLevel

theorem primitiveConstant_hasType {context : Tower.Ctx n} :
    Typing context (.const primitiveName) (liftClosed primitiveType) := by
  apply FormationSensitive.Typing.const (u := .sort primitiveDeclarationLevel)
  · change combinedType Tower.rules rawSignature primitiveName = some primitiveType
    apply combinedType_of_signature
    · rfl
    · exact typeOf_primitive
  · exact primitiveType_hasType
  · exact .sort primitiveDeclarationLevel

theorem primitiveApp_hasType {context : Tower.Ctx n}
    {sorts primitives source target symbol : Tower.Tm n}
    (sortsTyping : Typing context sorts (sortTm sortLevel))
    (primitivesTyping : Typing context primitives
      (.pi sorts (.pi (Presentation.rename wk sorts)
        (sortTm primitiveLevel))))
    (sourceTyping : Typing context source sorts)
    (targetTyping : Typing context target sorts)
    (symbolTyping : Typing context symbol
      (.app (.app primitives source) target)) :
    Typing context (primitiveApp sorts primitives source target symbol)
      (hypothesisApp sorts primitives source target) := by
  have afterSorts := FormationSensitive.Typing.appElim
    (primitiveConstant_hasType (context := context)) sortsTyping
  have afterPrimitives := FormationSensitive.Typing.appElim afterSorts
    primitivesTyping
  change Typing context _
    (Presentation.subst (subst0 primitives)
      (Presentation.subst (liftSub (subst0 sorts))
        (Presentation.rename (liftRen (liftRen Fin.elim0))
          primitiveBodyType))) at afterPrimitives
  rw [instantiateTwo_primitiveBodyType sorts primitives] at afterPrimitives
  have afterSource := FormationSensitive.Typing.appElim afterPrimitives sourceTyping
  have targetTypingExpected : Typing context target
      (Presentation.inst0 source (Presentation.rename wk sorts)) := by
    rw [Presentation.inst0_rename_wk]
    exact targetTyping
  have afterTarget := FormationSensitive.Typing.appElim afterSource
    targetTypingExpected
  have symbolTypingExpected : Typing context symbol
      (Presentation.subst (subst0 target)
        (Presentation.subst (liftSub (subst0 source))
          (.app (.app (weaken2 primitives) (.var 1)) (.var 0)))) := by
    rw [instantiatePrimitiveSymbolType]
    exact symbolTyping
  have afterSymbol := FormationSensitive.Typing.appElim afterTarget
    symbolTypingExpected
  change Typing context _
    (Presentation.subst (subst0 symbol)
      (Presentation.subst (liftSub (subst0 target))
        (Presentation.subst (liftSub (liftSub (subst0 source)))
          (hypothesisApp (weaken3 sorts) (weaken3 primitives)
            (.var 2) (.var 1))))) at afterSymbol
  rw [instantiatePrimitiveResult sorts primitives source target symbol]
    at afterSymbol
  exact afterSymbol

theorem chainBodyType_hasType :
    Typing contextSP chainBodyType (sortTm chainBodyLevel) := by
  unfold chainBodyType chainBodyLevel chainAfterMiddleLevel
    chainAfterTargetLevel chainAfterEarlierLevel chainAfterLaterLevel
  apply FormationSensitive.Typing.piForm
  · exact FormationSensitive.Typing.var 1
  · exact .sort sortLevel
  · apply FormationSensitive.Typing.piForm
    · exact FormationSensitive.Typing.var 2
    · exact .sort sortLevel
    · apply FormationSensitive.Typing.piForm
      · exact FormationSensitive.Typing.var 3
      · exact .sort sortLevel
      · apply FormationSensitive.Typing.piForm
        · apply hypothesisApp_hasType
          · exact FormationSensitive.Typing.var 4
          · exact FormationSensitive.Typing.var 3
          · exact FormationSensitive.Typing.var 2
          · exact FormationSensitive.Typing.var 1
        · exact .sort hypothesisLevel
        · apply FormationSensitive.Typing.piForm
          · apply hypothesisApp_hasType
            · exact FormationSensitive.Typing.var 5
            · exact FormationSensitive.Typing.var 4
            · exact FormationSensitive.Typing.var 2
            · exact FormationSensitive.Typing.var 1
          · exact .sort hypothesisLevel
          · apply hypothesisApp_hasType
            · exact FormationSensitive.Typing.var 6
            · exact FormationSensitive.Typing.var 5
            · exact FormationSensitive.Typing.var 4
            · exact FormationSensitive.Typing.var 2
          · exact .sort hypothesisLevel
          · exact .sorts hypothesisLevel hypothesisLevel
        · exact .sort chainAfterLaterLevel
        · exact .sorts hypothesisLevel chainAfterLaterLevel
      · exact .sort chainAfterEarlierLevel
      · exact .sorts sortLevel chainAfterEarlierLevel
    · exact .sort chainAfterTargetLevel
    · exact .sorts sortLevel chainAfterTargetLevel
  · exact .sort chainAfterMiddleLevel
  · exact .sorts sortLevel chainAfterMiddleLevel

theorem chainType_hasType :
    Typing (.nil : Tower.Ctx 0) chainType
      (sortTm chainDeclarationLevel) := by
  unfold chainType chainDeclarationLevel chainAfterPrimitiveLevel
  apply FormationSensitive.Typing.piForm
  · exact .headType (.sort sortLevel)
  · exact .sort (.succ sortLevel)
  · apply FormationSensitive.Typing.piForm
    · exact primitiveFamilyType_hasType
    · exact .sort primitiveFamilyTypeLevel
    · exact chainBodyType_hasType
    · exact .sort chainBodyLevel
    · exact .sorts primitiveFamilyTypeLevel chainBodyLevel
  · exact .sort chainAfterPrimitiveLevel
  · exact .sorts (.succ sortLevel) chainAfterPrimitiveLevel

theorem chainConstant_hasType {context : Tower.Ctx n} :
    Typing context (.const chainName) (liftClosed chainType) := by
  apply FormationSensitive.Typing.const (u := .sort chainDeclarationLevel)
  · change combinedType Tower.rules rawSignature chainName = some chainType
    apply combinedType_of_signature
    · rfl
    · exact typeOf_chain
  · exact chainType_hasType
  · exact .sort chainDeclarationLevel

theorem chainApp_hasType {context : Tower.Ctx n}
    {sorts primitives source middle target earlier later : Tower.Tm n}
    (sortsTyping : Typing context sorts (sortTm sortLevel))
    (primitivesTyping : Typing context primitives
      (.pi sorts (.pi (Presentation.rename wk sorts)
        (sortTm primitiveLevel))))
    (sourceTyping : Typing context source sorts)
    (middleTyping : Typing context middle sorts)
    (targetTyping : Typing context target sorts)
    (earlierTyping : Typing context earlier
      (hypothesisApp sorts primitives source middle))
    (laterTyping : Typing context later
      (hypothesisApp sorts primitives middle target)) :
    Typing context
      (chainApp sorts primitives source middle target earlier later)
      (hypothesisApp sorts primitives source target) := by
  have afterSorts := FormationSensitive.Typing.appElim
    (chainConstant_hasType (context := context)) sortsTyping
  have afterPrimitives := FormationSensitive.Typing.appElim afterSorts
    primitivesTyping
  change Typing context _
    (Presentation.subst (subst0 primitives)
      (Presentation.subst (liftSub (subst0 sorts))
        (Presentation.rename (liftRen (liftRen Fin.elim0))
          chainBodyType))) at afterPrimitives
  rw [instantiateTwo_chainBodyType sorts primitives] at afterPrimitives
  have afterSource := FormationSensitive.Typing.appElim afterPrimitives sourceTyping
  have middleTypingExpected : Typing context middle
      (Presentation.inst0 source (weaken1 sorts)) := by
    change Typing context middle
      (Presentation.inst0 source (Presentation.rename wk sorts))
    rw [Presentation.inst0_rename_wk]
    exact middleTyping
  have afterMiddle := FormationSensitive.Typing.appElim afterSource
    middleTypingExpected
  have targetTypingExpected : Typing context target
      (Presentation.subst (subst0 middle)
        (Presentation.subst (liftSub (subst0 source)) (weaken2 sorts))) := by
    rw [instantiateTwo_weaken2]
    exact targetTyping
  have afterTarget := FormationSensitive.Typing.appElim afterMiddle
    targetTypingExpected
  have earlierTypingExpected : Typing context earlier
      (Presentation.subst (subst0 target)
        (Presentation.subst (liftSub (subst0 middle))
          (Presentation.subst (liftSub (liftSub (subst0 source)))
            (hypothesisApp (weaken3 sorts) (weaken3 primitives)
              (.var 2) (.var 1))))) := by
    rw [instantiateChainEarlier]
    exact earlierTyping
  have afterEarlier := FormationSensitive.Typing.appElim afterTarget
    earlierTypingExpected
  have laterTypingExpected : Typing context later
      (Presentation.subst (subst0 earlier)
        (Presentation.subst (liftSub (subst0 target))
          (Presentation.subst (liftSub (liftSub (subst0 middle)))
            (Presentation.subst
              (liftSub (liftSub (liftSub (subst0 source))))
              (hypothesisApp (weaken4 sorts) (weaken4 primitives)
                (.var 2) (.var 1)))))) := by
    rw [instantiateChainLater]
    exact laterTyping
  have afterLater := FormationSensitive.Typing.appElim afterEarlier
    laterTypingExpected
  change Typing context _
    (Presentation.subst (subst0 later)
      (Presentation.subst (liftSub (subst0 earlier))
        (Presentation.subst (liftSub (liftSub (subst0 target)))
          (Presentation.subst
            (liftSub (liftSub (liftSub (subst0 middle))))
            (Presentation.subst
              (liftSub (liftSub (liftSub (liftSub (subst0 source)))))
              (hypothesisApp (weaken5 sorts) (weaken5 primitives)
                (.var 4) (.var 2))))))) at afterLater
  rw [instantiateChainResult sorts primitives source middle target earlier later]
    at afterLater
  exact afterLater

/-! ## Admission over the existing quotation and program data -/

universe uSort uCarrier uPrimitive

/-- Independently checked refined typing for the four leaves of an existing
quotation. No final program typing or semantic agreement is assumed. -/
structure QuotationTyping
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary.{uSort, uCarrier, uPrimitive}}
    {context : Tower.Ctx n}
    (quotation : TypedVocabularyQuotation vocabulary context) : Prop where
  sortsTyping : Typing context quotation.sorts (sortTm sortLevel)
  primitivesTyping : Typing context quotation.primitives
    (.pi quotation.sorts (.pi (rename wk quotation.sorts) (sortTm primitiveLevel)))
  sortCodeTyping : ∀ sort, Typing context (quotation.sortCode sort) quotation.sorts
  primitiveCodeTyping : ∀ {source target}
    (symbol : vocabulary.Primitive source target),
    Typing context (quotation.primitiveCode symbol)
      (.app (.app quotation.primitives (quotation.sortCode source))
        (quotation.sortCode target))

end FormationSensitiveMIL

namespace IntrinsicMILSemanticAdequacy.Program

open Presentation FormationSensitiveMIL IntrinsicMILHypothesis

variable {n : Nat}
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    {quotation : TypedVocabularyQuotation vocabulary context}
    {source target : vocabulary.SortCode} {term : Tower.Tm n}

/-- Structural admission retains all formation premises throughout the
derivation; raw typing is not used to construct refined evidence. -/
theorem formationSensitiveTyping
    (program : Program quotation (source := source) (target := target) term)
    (leaves : QuotationTyping quotation) :
    FormationSensitiveMIL.Typing context term
      (hypothesisApp quotation.sorts quotation.primitives
        (quotation.sortCode source) (quotation.sortCode target)) := by
  induction program with
  | primitive symbol =>
      exact FormationSensitiveMIL.primitiveApp_hasType leaves.sortsTyping
        leaves.primitivesTyping (leaves.sortCodeTyping _) (leaves.sortCodeTyping _)
        (leaves.primitiveCodeTyping symbol)
  | chain earlier later earlierTyping laterTyping =>
      exact FormationSensitiveMIL.chainApp_hasType leaves.sortsTyping
        leaves.primitivesTyping (leaves.sortCodeTyping _) (leaves.sortCodeTyping _)
        (leaves.sortCodeTyping _) earlierTyping laterTyping

/-- The complete admission judgment includes a refined formed telescope. -/
theorem formationSensitiveJudgment
    (program : Program quotation (source := source) (target := target) term)
    (leaves : QuotationTyping quotation)
    (formedContext : FormationSensitive.ContextFormation rules context) :
    FormationSensitive.Judgment rules context term
      (hypothesisApp quotation.sorts quotation.primitives
        (quotation.sortCode source) (quotation.sortCode target)) :=
  ⟨formedContext, program.formationSensitiveTyping leaves⟩

/-- Admission preserves the existing independent evidence equivalence:
neither program identity nor either evidence fibre is replaced. -/
theorem formationSensitiveJudgment_and_semanticAdequacy
    (program : Program quotation (source := source) (target := target) term)
    (leaves : QuotationTyping quotation)
    (formedContext : FormationSensitive.ContextFormation rules context) :
    FormationSensitive.Judgment rules context term
      (hypothesisApp quotation.sorts quotation.primitives
        (quotation.sortCode source) (quotation.sortCode target)) ∧
    program.denotation = program.toHypothesis.denote :=
  ⟨program.formationSensitiveJudgment leaves formedContext,
    program.denotation_eq_toHypothesis⟩

end IntrinsicMILSemanticAdequacy.Program

namespace FormationSensitiveMIL

open Presentation IntrinsicMILHypothesis IntrinsicMILSemanticAdequacy

variable {n : Nat}

/-- Every semantic primitive/chain hypothesis has an admitted quotation,
at the original indexed endpoints. -/
theorem quoteHypothesis_judgment
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    (quotation : TypedVocabularyQuotation vocabulary context)
    (leaves : QuotationTyping quotation)
    (formedContext : FormationSensitive.ContextFormation rules context)
    {source target : vocabulary.SortCode}
    (hypothesis : MILSchemaElaboration.Semantic.Hypothesis vocabulary source target) :
    FormationSensitive.Judgment rules context (quoteHypothesis quotation hypothesis)
      (hypothesisApp quotation.sorts quotation.primitives
        (quotation.sortCode source) (quotation.sortCode target)) :=
  (Program.ofHypothesis quotation hypothesis).formationSensitiveJudgment leaves formedContext

/-! ## Concrete successor-chain admission and unsupported-leaf rejection -/

namespace Examples

def vocabulary : MILSchemaElaboration.Semantic.Vocabulary where
  SortCode := Unit
  Carrier := fun _ => Nat
  Primitive := fun _ _ => Unit
  meaning := fun _ => RelationalInternalLanguage.Semantic.Rel.graph Nat.succ

/-- A sort and primitive family, a sort code, and one primitive at that code. -/
def contextSPA : Tower.Ctx 3 := .snoc contextSP (.var 1)

def contextSPAP : Tower.Ctx 4 :=
  .snoc contextSPA (.app (.app (.var 1) (.var 0)) (.var 0))

theorem context_formed : FormationSensitive.ContextFormation rules contextSPAP := by
  apply FormationSensitive.ContextFormation.snoc
  · apply FormationSensitive.ContextFormation.snoc
    · apply FormationSensitive.ContextFormation.snoc
      · exact .snoc .nil (.headType (.sort sortLevel)) (.sort (.succ sortLevel))
      · exact primitiveFamilyType_hasType
      · exact .sort primitiveFamilyTypeLevel
    · exact FormationSensitive.Typing.var 1
    · exact .sort sortLevel
  · apply primitiveFamilyApp_hasType
    · exact FormationSensitive.Typing.var 1
    · exact FormationSensitive.Typing.var 0
    · exact FormationSensitive.Typing.var 0
  · exact .sort primitiveLevel

def quotation : TypedVocabularyQuotation vocabulary contextSPAP where
  sorts := .var 3
  primitives := .var 2
  sortCode := fun _ => .var 1
  primitiveCode := fun _ => .var 0
  sortsTyping := (FormationSensitive.Typing.var (R := rules) (Γ := contextSPAP) 3).toRaw
  primitivesTyping := (FormationSensitive.Typing.var (R := rules) (Γ := contextSPAP) 2).toRaw
  sortCodeTyping := fun _ =>
    (FormationSensitive.Typing.var (R := rules) (Γ := contextSPAP) 1).toRaw
  primitiveCodeTyping := fun _ =>
    (FormationSensitive.Typing.var (R := rules) (Γ := contextSPAP) 0).toRaw

theorem quotation_typed : QuotationTyping quotation where
  sortsTyping := FormationSensitive.Typing.var 3
  primitivesTyping := FormationSensitive.Typing.var 2
  sortCodeTyping := fun _ => FormationSensitive.Typing.var 1
  primitiveCodeTyping := fun _ => FormationSensitive.Typing.var 0

def twice : MILSchemaElaboration.Semantic.Hypothesis vocabulary () () :=
  .chain (middle := ()) (.primitive ()) (.primitive ())

def twiceProgram : Program quotation (source := ()) (target := ())
    (quoteHypothesis quotation twice) :=
  Program.ofHypothesis quotation twice

theorem twice_admitted : FormationSensitive.Judgment rules contextSPAP
    (quoteHypothesis quotation twice)
    (hypothesisApp (.var 3) (.var 2) (.var 1) (.var 1)) :=
  twiceProgram.formationSensitiveJudgment quotation_typed context_formed

def twice_receipt : twiceProgram.denotation.evidence (0 : Nat) (2 : Nat) :=
  ⟨(1 : Nat), ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩⟩

theorem twice_no_wrong_receipt :
    ¬ Nonempty (twiceProgram.denotation.evidence (0 : Nat) (3 : Nat)) := by
  rintro ⟨⟨middle, first, second⟩⟩
  have firstEq : Nat.succ 0 = middle := first.down.down
  have secondEq : Nat.succ middle = 3 := second.down.down
  omega

def missingName : DeclName := `Prime.Hypothesis.missingPrimitive

/-- The actual declaration environment cannot admit an undeclared primitive,
even by converting its displayed type afterward. -/
theorem missing_primitive_rejected {context : Tower.Ctx n} {type : Tower.Tm n} :
    ¬ Typing context (.const missingName) type := by
  intro typed
  obtain ⟨declaredType, sortHead, known, _, _⟩ := typed.constFormation
  have absent : rules.constantType missingName = none := by decide
  rw [absent] at known
  cases known

end Examples

#print axioms hypothesisType_hasType
#print axioms primitiveType_hasType
#print axioms chainType_hasType
#print axioms primitiveApp_hasType
#print axioms chainApp_hasType
#print axioms IntrinsicMILSemanticAdequacy.Program.formationSensitiveJudgment
#print axioms IntrinsicMILSemanticAdequacy.Program.formationSensitiveJudgment_and_semanticAdequacy
#print axioms quoteHypothesis_judgment
#print axioms Examples.twice_admitted
#print axioms Examples.twice_no_wrong_receipt
#print axioms Examples.missing_primitive_rejected

end FormationSensitiveMIL
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
