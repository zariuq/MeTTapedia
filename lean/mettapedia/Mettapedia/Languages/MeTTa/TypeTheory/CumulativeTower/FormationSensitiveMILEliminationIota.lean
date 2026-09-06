import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveMILElimination

/-!
# Refined admission of the existing MIL dependent iota schemas

The original primitive and chain schemas retain their exact source, reduct,
displayed motive, and Type-valued rule receipt. Both endpoint typings are
proved independently with formation-sensitive rules in formed telescopes.
Typed substitution therefore admits every refined instance of these schemas.

This is typed schema admission, not subject reduction from arbitrary raw
typing. In particular, no confluence result for combined beta/iota conversion
is assumed or established here. The negative control concerns the actual
iota generator, not equality modulo arbitrary conversion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FormationSensitiveMILElimination

open Presentation Presentation.Declaration IntrinsicMILHypothesis
open FormationSensitiveMIL (Typing)

variable {n : Nat}

/-! ## Formation of the actual schema telescopes -/

theorem contextSP_formed :
    FormationSensitive.ContextFormation rules contextSP :=
  .snoc
    (.snoc .nil (.headType (.sort sortLevel)) (.sort (.succ sortLevel)))
    FormationSensitiveMIL.primitiveFamilyType_hasType
    (.sort primitiveFamilyTypeLevel)

theorem contextSPMPrimitiveChain_formed :
    FormationSensitive.ContextFormation rules contextSPMPrimitiveChain :=
  .snoc
    (.snoc
      (.snoc contextSP_formed motiveType_hasType (.sort motiveDeclarationLevel))
      primitiveCaseType_hasType (.sort primitiveCaseLevel))
    chainCaseType_hasType (.sort chainCaseLevel)

theorem primitiveContext_formed :
    FormationSensitive.ContextFormation rules contextSPMPCSourceTargetSymbol := by
  apply FormationSensitive.ContextFormation.snoc
  · exact .snoc
      (.snoc contextSPMPrimitiveChain_formed
        (FormationSensitive.Typing.var 4) (.sort sortLevel))
      (FormationSensitive.Typing.var 5) (.sort sortLevel)
  · apply FormationSensitiveMIL.primitiveFamilyApp_hasType
    · exact FormationSensitive.Typing.var 5
    · exact FormationSensitive.Typing.var 1
    · exact FormationSensitive.Typing.var 0
  · exact .sort primitiveLevel

theorem chainContext_formed :
    FormationSensitive.ContextFormation rules
      contextSPMPCChainSourceMiddleTargetEarlierLater := by
  apply FormationSensitive.ContextFormation.snoc
  · apply FormationSensitive.ContextFormation.snoc
    · exact .snoc
        (.snoc
          (.snoc contextSPMPrimitiveChain_formed
            (FormationSensitive.Typing.var 4) (.sort sortLevel))
          (FormationSensitive.Typing.var 5) (.sort sortLevel))
        (FormationSensitive.Typing.var 6) (.sort sortLevel)
    · apply FormationSensitiveMIL.hypothesisApp_hasType
      · exact FormationSensitive.Typing.var 7
      · exact FormationSensitive.Typing.var 6
      · exact FormationSensitive.Typing.var 2
      · exact FormationSensitive.Typing.var 1
    · exact .sort hypothesisLevel
  · apply FormationSensitiveMIL.hypothesisApp_hasType
    · exact FormationSensitive.Typing.var 8
    · exact FormationSensitive.Typing.var 7
    · exact FormationSensitive.Typing.var 2
    · exact FormationSensitive.Typing.var 1
  · exact .sort hypothesisLevel

/-! ## Independent refined endpoint typings -/

theorem primitiveIotaLeft_hasType :
    Typing contextSPMPCSourceTargetSymbol primitiveIotaLeft
      primitiveIotaResultType := by
  have evidenceTyping : Typing contextSPMPCSourceTargetSymbol
      primitiveIotaEvidenceTerm
      (hypothesisApp (.var 7) (.var 6) (.var 2) (.var 1)) := by
    apply FormationSensitiveMIL.primitiveApp_hasType
    · exact FormationSensitive.Typing.var 7
    · exact FormationSensitive.Typing.var 6
    · exact FormationSensitive.Typing.var 2
    · exact FormationSensitive.Typing.var 1
    · exact FormationSensitive.Typing.var 0
  have afterSource := FormationSensitive.Typing.appElim
    eliminateAtPrimitiveParameters_hasType
    (FormationSensitive.Typing.var 2)
  have afterTarget := FormationSensitive.Typing.appElim afterSource (by
    convert (FormationSensitive.Typing.var 1 : Typing
      contextSPMPCSourceTargetSymbol (.var 1) (.var 7)) using 1
    all_goals decide)
  have afterEvidence := FormationSensitive.Typing.appElim afterTarget (by
    convert evidenceTyping using 1
    all_goals decide)
  convert afterEvidence using 1
  all_goals decide

theorem primitiveIotaRight_hasType :
    Typing contextSPMPCSourceTargetSymbol primitiveIotaRight
      primitiveIotaResultType := by
  have primitiveCaseTyping : Typing contextSPMPCSourceTargetSymbol
      (.var 4) (weaken5 primitiveCaseType) :=
    FormationSensitive.Typing.var 4
  have afterSource := FormationSensitive.Typing.appElim primitiveCaseTyping
    (FormationSensitive.Typing.var 2)
  have afterTarget := FormationSensitive.Typing.appElim afterSource (by
    convert (FormationSensitive.Typing.var 1 : Typing
      contextSPMPCSourceTargetSymbol (.var 1) (.var 7)) using 1
    all_goals decide)
  have afterSymbol := FormationSensitive.Typing.appElim afterTarget (by
    convert (FormationSensitive.Typing.var 0 : Typing
      contextSPMPCSourceTargetSymbol (.var 0)
        (.app (.app (.var 6) (.var 2)) (.var 1))) using 1
    all_goals decide)
  convert afterSymbol using 1
  all_goals decide

theorem chainIotaLeft_hasType :
    Typing contextSPMPCChainSourceMiddleTargetEarlierLater chainIotaLeft
      chainIotaResultType := by
  have evidenceTyping : Typing
      contextSPMPCChainSourceMiddleTargetEarlierLater chainIotaEvidenceTerm
      (hypothesisApp (.var 9) (.var 8) (.var 4) (.var 2)) := by
    apply FormationSensitiveMIL.chainApp_hasType
    · exact FormationSensitive.Typing.var 9
    · exact FormationSensitive.Typing.var 8
    · exact FormationSensitive.Typing.var 4
    · exact FormationSensitive.Typing.var 3
    · exact FormationSensitive.Typing.var 2
    · exact FormationSensitive.Typing.var 1
    · exact FormationSensitive.Typing.var 0
  have afterSource := FormationSensitive.Typing.appElim
    eliminateAtChainParameters_hasType (FormationSensitive.Typing.var 4)
  have afterTarget := FormationSensitive.Typing.appElim afterSource (by
    convert (FormationSensitive.Typing.var 2 : Typing
      contextSPMPCChainSourceMiddleTargetEarlierLater (.var 2)
        (.var 9)) using 1
    all_goals decide)
  have afterEvidence := FormationSensitive.Typing.appElim afterTarget (by
    convert evidenceTyping using 1
    all_goals decide)
  convert afterEvidence using 1
  all_goals decide

/-- The chain branch consumes two recursively computed inhabitants of the
motive at the exact earlier and later hypothesis receipts. -/
theorem chainIotaRight_hasType :
    Typing contextSPMPCChainSourceMiddleTargetEarlierLater chainIotaRight
      chainIotaResultType := by
  have earlierEvidenceTyping : Typing
      contextSPMPCChainSourceMiddleTargetEarlierLater (.var 1)
      (hypothesisApp (.var 9) (.var 8) (.var 4) (.var 3)) :=
    FormationSensitive.Typing.var 1
  have laterEvidenceTyping : Typing
      contextSPMPCChainSourceMiddleTargetEarlierLater (.var 0)
      (hypothesisApp (.var 9) (.var 8) (.var 3) (.var 2)) :=
    FormationSensitive.Typing.var 0
  have earlierRecursiveTyping : Typing
      contextSPMPCChainSourceMiddleTargetEarlierLater
      chainIotaEarlierRecursive
      (motiveApp (.var 7) (.var 4) (.var 3) (.var 1)) := by
    have afterSource := FormationSensitive.Typing.appElim
      eliminateAtChainParameters_hasType (FormationSensitive.Typing.var 4)
    have afterMiddle := FormationSensitive.Typing.appElim afterSource (by
      convert (FormationSensitive.Typing.var 3 : Typing
        contextSPMPCChainSourceMiddleTargetEarlierLater (.var 3)
          (.var 9)) using 1
      all_goals decide)
    have afterEvidence := FormationSensitive.Typing.appElim afterMiddle (by
      convert earlierEvidenceTyping using 1
      all_goals decide)
    convert afterEvidence using 1
    all_goals decide
  have laterRecursiveTyping : Typing
      contextSPMPCChainSourceMiddleTargetEarlierLater
      chainIotaLaterRecursive
      (motiveApp (.var 7) (.var 3) (.var 2) (.var 0)) := by
    have afterMiddle := FormationSensitive.Typing.appElim
      eliminateAtChainParameters_hasType (FormationSensitive.Typing.var 3)
    have afterTarget := FormationSensitive.Typing.appElim afterMiddle (by
      convert (FormationSensitive.Typing.var 2 : Typing
        contextSPMPCChainSourceMiddleTargetEarlierLater (.var 2)
          (.var 9)) using 1
      all_goals decide)
    have afterEvidence := FormationSensitive.Typing.appElim afterTarget (by
      convert laterEvidenceTyping using 1
      all_goals decide)
    convert afterEvidence using 1
    all_goals decide
  have chainCaseTyping : Typing
      contextSPMPCChainSourceMiddleTargetEarlierLater (.var 5)
      (weaken6 chainCaseType) :=
    FormationSensitive.Typing.var 5
  have afterSource := FormationSensitive.Typing.appElim chainCaseTyping
    (FormationSensitive.Typing.var 4)
  have afterMiddle := FormationSensitive.Typing.appElim afterSource (by
    convert (FormationSensitive.Typing.var 3 : Typing
      contextSPMPCChainSourceMiddleTargetEarlierLater (.var 3)
        (.var 9)) using 1
    all_goals decide)
  have afterTarget := FormationSensitive.Typing.appElim afterMiddle (by
    convert (FormationSensitive.Typing.var 2 : Typing
      contextSPMPCChainSourceMiddleTargetEarlierLater (.var 2)
        (.var 9)) using 1
    all_goals decide)
  have afterEarlier := FormationSensitive.Typing.appElim afterTarget (by
    convert earlierEvidenceTyping using 1
    all_goals decide)
  have afterLater := FormationSensitive.Typing.appElim afterEarlier (by
    convert laterEvidenceTyping using 1
    all_goals decide)
  have afterEarlierIH := FormationSensitive.Typing.appElim afterLater (by
    convert earlierRecursiveTyping using 1
    all_goals decide)
  have afterLaterIH := FormationSensitive.Typing.appElim afterEarlierIH (by
    convert laterRecursiveTyping using 1
    all_goals decide)
  convert afterLaterIH using 1
  all_goals decide

theorem primitiveIota_judgments :
    FormationSensitive.Judgment rules contextSPMPCSourceTargetSymbol
      primitiveIotaLeft primitiveIotaResultType ∧
    FormationSensitive.Judgment rules contextSPMPCSourceTargetSymbol
      primitiveIotaRight primitiveIotaResultType :=
  ⟨⟨primitiveContext_formed, primitiveIotaLeft_hasType⟩,
    ⟨primitiveContext_formed, primitiveIotaRight_hasType⟩⟩

theorem chainIota_judgments :
    FormationSensitive.Judgment rules contextSPMPCChainSourceMiddleTargetEarlierLater
      chainIotaLeft chainIotaResultType ∧
    FormationSensitive.Judgment rules contextSPMPCChainSourceMiddleTargetEarlierLater
      chainIotaRight chainIotaResultType :=
  ⟨⟨chainContext_formed, chainIotaLeft_hasType⟩,
    ⟨chainContext_formed, chainIotaRight_hasType⟩⟩

/-! ## All formation-sensitive substitution instances -/

theorem primitiveIota_substitute {context : Tower.Ctx n}
    {substitution : Sub Tower.Head 8 n}
    (formed : FormationSensitive.ContextFormation rules context)
    (typed : FormationSensitive.CtxMor rules contextSPMPCSourceTargetSymbol
      context substitution) :
    FormationSensitive.Judgment rules context
      (subst substitution primitiveIotaLeft) (subst substitution primitiveIotaResultType) ∧
    FormationSensitive.Judgment rules context
      (subst substitution primitiveIotaRight) (subst substitution primitiveIotaResultType) :=
  ⟨primitiveIota_judgments.1.substitute formed typed,
    primitiveIota_judgments.2.substitute formed typed⟩

theorem chainIota_substitute {context : Tower.Ctx n}
    {substitution : Sub Tower.Head 10 n}
    (formed : FormationSensitive.ContextFormation rules context)
    (typed : FormationSensitive.CtxMor rules
      contextSPMPCChainSourceMiddleTargetEarlierLater context substitution) :
    FormationSensitive.Judgment rules context
      (subst substitution chainIotaLeft) (subst substitution chainIotaResultType) ∧
    FormationSensitive.Judgment rules context
      (subst substitution chainIotaRight) (subst substitution chainIotaResultType) :=
  ⟨chainIota_judgments.1.substitute formed typed,
    chainIota_judgments.2.substitute formed typed⟩

/-- The existing informative receipt is retained as a value, not replaced by
the proposition that some iota step exists. -/
def primitiveIota_substitutedReceipt {context : Tower.Ctx n}
    (substitution : Sub Tower.Head 8 n)
    (typed : FormationSensitive.CtxMor rules contextSPMPCSourceTargetSymbol
      context substitution) :
    TypedIotaReceipt context (subst substitution primitiveIotaLeft)
      (subst substitution primitiveIotaRight) (subst substitution primitiveIotaResultType) :=
  primitiveIotaReceipt.substitute substitution typed.toRaw

def chainIota_substitutedReceipt {context : Tower.Ctx n}
    (substitution : Sub Tower.Head 10 n)
    (typed : FormationSensitive.CtxMor rules
      contextSPMPCChainSourceMiddleTargetEarlierLater context substitution) :
    TypedIotaReceipt context (subst substitution chainIotaLeft)
      (subst substitution chainIotaRight) (subst substitution chainIotaResultType) :=
  chainIotaReceipt.substitute substitution typed.toRaw

/-! ## Exact-receipt boundary of the declared generator -/

/-- A fixed native iota redex determines its reduct. This property is only
about these two root generators, not the contextual or conversion closure. -/
theorem iota_target_unique {left first second : Tower.Tm n}
    (one : IotaEvidence n left first) (two : IotaEvidence n left second) :
    first = second := by
  cases one <;> cases two <;> rfl

/-- An altered branch call replaces the earlier induction result with a
second copy of the later one, leaving all the other arguments unchanged. -/
def chainIotaDuplicatedLater : Tower.Tm 10 :=
  .app
    (.app
      (.app
        (.app
          (.app
            (.app
              (.app (.var 5) (.var 4)) (.var 3)) (.var 2)) (.var 1)) (.var 0))
      chainIotaLaterRecursive)
    chainIotaLaterRecursive

theorem chainIota_no_duplicated_later :
    ¬ Nonempty (IotaEvidence 10 chainIotaLeft chainIotaDuplicatedLater) := by
  rintro ⟨altered⟩
  have same := iota_target_unique chainIotaReceipt.evidence altered
  exact (by decide : chainIotaRight ≠ chainIotaDuplicatedLater) same

/-- Equality of displayed motive applications cannot silently drop the exact
receipt argument. This is raw syntax equality, not conversion reflection. -/
theorem motiveApp_receipt_injective (motive source target : Tower.Tm n) :
    Function.Injective (motiveApp motive source target) := by
  intro first second equal
  exact Tm.app.inj equal |>.2

/-! ## Two distinct hypothesis receipts at the same endpoints -/

namespace ReceiptConsumer

/-- One sort code and two hypotheses with exactly the same source and target,
over the already formed eliminator parameters. -/
def context : Tower.Ctx 8 :=
  .snoc
    (.snoc
      (.snoc contextSPMPrimitiveChain (.var 4))
      (hypothesisApp (.var 5) (.var 4) (.var 0) (.var 0)))
    (hypothesisApp (.var 6) (.var 5) (.var 1) (.var 1))

theorem context_formed : FormationSensitive.ContextFormation rules context := by
  apply FormationSensitive.ContextFormation.snoc
  · apply FormationSensitive.ContextFormation.snoc
    · exact .snoc contextSPMPrimitiveChain_formed
        (FormationSensitive.Typing.var 4) (.sort sortLevel)
    · apply FormationSensitiveMIL.hypothesisApp_hasType
      · exact FormationSensitive.Typing.var 5
      · exact FormationSensitive.Typing.var 4
      · exact FormationSensitive.Typing.var 0
      · exact FormationSensitive.Typing.var 0
    · exact .sort hypothesisLevel
  · apply FormationSensitiveMIL.hypothesisApp_hasType
    · exact FormationSensitive.Typing.var 6
    · exact FormationSensitive.Typing.var 5
    · exact FormationSensitive.Typing.var 1
    · exact FormationSensitive.Typing.var 1
  · exact .sort hypothesisLevel

/-- Identify the three endpoint codes, but keep the two hypothesis receipts
distinct. The Boolean chooses their order in the constructor and branch. -/
def substitution (reverseReceipts : Bool) : Sub Tower.Head 10 8 :=
  if reverseReceipts then
    ![.var 1, .var 0, .var 2, .var 2, .var 2,
      .var 3, .var 4, .var 5, .var 6, .var 7]
  else
    ![.var 0, .var 1, .var 2, .var 2, .var 2,
      .var 3, .var 4, .var 5, .var 6, .var 7]

theorem substitution_typed (reverseReceipts : Bool) :
    FormationSensitive.CtxMor rules
      contextSPMPCChainSourceMiddleTargetEarlierLater context
      (substitution reverseReceipts) := by
  intro index
  cases reverseReceipts <;> fin_cases index <;>
    exact FormationSensitive.Typing.var _

def left (reverseReceipts : Bool) : Tower.Tm 8 :=
  subst (substitution reverseReceipts) chainIotaLeft

def right (reverseReceipts : Bool) : Tower.Tm 8 :=
  subst (substitution reverseReceipts) chainIotaRight

def resultType (reverseReceipts : Bool) : Tower.Tm 8 :=
  subst (substitution reverseReceipts) chainIotaResultType

/-- Both orders are admitted, with the motive applied to the exact resulting
hypothesis rather than merely its shared endpoint codes. -/
theorem admitted (reverseReceipts : Bool) :
    FormationSensitive.Judgment rules context (left reverseReceipts)
      (resultType reverseReceipts) ∧
    FormationSensitive.Judgment rules context (right reverseReceipts)
      (resultType reverseReceipts) :=
  chainIota_substitute context_formed (substitution_typed reverseReceipts)

/-- The actual original iota witness, with its parameter substitution. -/
def receipt (reverseReceipts : Bool) :
    TypedIotaReceipt context (left reverseReceipts) (right reverseReceipts)
      (resultType reverseReceipts) :=
  chainIota_substitutedReceipt (substitution reverseReceipts)
    (substitution_typed reverseReceipts)

theorem resultType_exact (reverseReceipts : Bool) :
    resultType reverseReceipts =
      motiveApp (.var 5) (.var 2) (.var 2)
        (if reverseReceipts then
          chainApp (.var 7) (.var 6) (.var 2) (.var 2) (.var 2) (.var 0) (.var 1)
        else
          chainApp (.var 7) (.var 6) (.var 2) (.var 2) (.var 2) (.var 1) (.var 0)) := by
  cases reverseReceipts <;> decide

/-- The same endpoint codes do not force the same displayed motive type.
This distinguishes raw dependent types; it makes no claim about their
inequality modulo the full conversion relation. -/
theorem resultTypes_distinct : resultType false ≠ resultType true := by decide

/-- A branch result for the opposite receipt order cannot be substituted for
the result licensed by this redex's actual iota generator. -/
theorem no_crossed_receipt :
    ¬ Nonempty (IotaEvidence 8 (left false) (right true)) := by
  rintro ⟨crossed⟩
  have equal := iota_target_unique (receipt false).evidence crossed
  exact (by decide : right false ≠ right true) equal

end ReceiptConsumer

#print axioms primitiveIota_judgments
#print axioms chainIota_judgments
#print axioms primitiveIota_substitute
#print axioms chainIota_substitute
#print axioms primitiveIota_substitutedReceipt
#print axioms chainIota_substitutedReceipt
#print axioms iota_target_unique
#print axioms chainIota_no_duplicated_later
#print axioms motiveApp_receipt_injective
#print axioms ReceiptConsumer.admitted
#print axioms ReceiptConsumer.receipt
#print axioms ReceiptConsumer.resultTypes_distinct
#print axioms ReceiptConsumer.no_crossed_receipt

end FormationSensitiveMILElimination
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
