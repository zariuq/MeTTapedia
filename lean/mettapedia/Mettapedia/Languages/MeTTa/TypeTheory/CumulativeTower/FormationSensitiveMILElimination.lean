import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveMIL

/-!
# Formation-sensitive admission of the native MIL dependent eliminator

The motive and both branches are the existing declaration's actual dependent
types. In particular, motives see the exact hypothesis term, and the chain
branch receives induction hypotheses indexed by its two constituent receipts.
All closed declaration and application evidence below uses the refined
judgment independently of the old raw typing certificates.

These formation/application proofs use no object-language conversion.
They do not establish confluence or arbitrary subject reduction for the
declaration's combined beta/iota computation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FormationSensitiveMILElimination

open Presentation Presentation.Declaration IntrinsicMILHypothesis
open FormationSensitiveMIL (Typing)

variable {n : Nat}

/-! ## Actual motive, branch, and closed declaration formation -/

theorem motiveType_hasType :
    Typing contextSP motiveType (sortTm motiveDeclarationLevel) := by
  unfold motiveType motiveDeclarationLevel motiveAfterTargetLevel
    motiveAfterHypothesisLevel
  apply FormationSensitive.Typing.piForm
  · exact FormationSensitive.Typing.var 1
  · exact .sort sortLevel
  · apply FormationSensitive.Typing.piForm
    · exact FormationSensitive.Typing.var 2
    · exact .sort sortLevel
    · apply FormationSensitive.Typing.piForm
      · apply FormationSensitiveMIL.hypothesisApp_hasType
        · exact FormationSensitive.Typing.var 3
        · exact FormationSensitive.Typing.var 2
        · exact FormationSensitive.Typing.var 1
        · exact FormationSensitive.Typing.var 0
      · exact .sort hypothesisLevel
      · exact .headType (.sort eliminationLevel)
      · exact .sort (.succ eliminationLevel)
      · exact .sorts hypothesisLevel (.succ eliminationLevel)
    · exact .sort motiveAfterHypothesisLevel
    · exact .sorts sortLevel motiveAfterHypothesisLevel
  · exact .sort motiveAfterTargetLevel
  · exact .sorts sortLevel motiveAfterTargetLevel

theorem motiveApp_hasType {context : Tower.Ctx n}
    {sorts primitives motive source target hypothesis : Tower.Tm n}
    (motiveTyping : Typing context motive
      (motiveTypeAt sorts primitives))
    (sourceTyping : Typing context source sorts)
    (targetTyping : Typing context target sorts)
    (hypothesisTyping : Typing context hypothesis
      (hypothesisApp sorts primitives source target)) :
    Typing context (motiveApp motive source target hypothesis)
      (sortTm eliminationLevel) := by
  have afterSource := FormationSensitive.Typing.appElim motiveTyping sourceTyping
  have targetTypingExpected : Typing context target
      (Presentation.inst0 source (weaken1 sorts)) := by
    change Typing context target
      (Presentation.inst0 source (Presentation.rename wk sorts))
    rw [Presentation.inst0_rename_wk]
    exact targetTyping
  have afterTarget := FormationSensitive.Typing.appElim afterSource
    targetTypingExpected
  have hypothesisTypingExpected : Typing context hypothesis
      (Presentation.subst (subst0 target)
        (Presentation.subst (liftSub (subst0 source))
          (hypothesisApp (weaken2 sorts) (weaken2 primitives)
            (.var 1) (.var 0)))) := by
    rw [instantiateMotiveEvidenceType]
    exact hypothesisTyping
  have afterHypothesis := FormationSensitive.Typing.appElim afterTarget
    hypothesisTypingExpected
  exact afterHypothesis

theorem primitiveCaseType_hasType :
    Typing contextSPM primitiveCaseType (sortTm primitiveCaseLevel) := by
  unfold primitiveCaseType primitiveCaseLevel primitiveCaseAfterTargetLevel
    primitiveCaseAfterSymbolLevel
  apply FormationSensitive.Typing.piForm
  · exact FormationSensitive.Typing.var 2
  · exact .sort sortLevel
  · apply FormationSensitive.Typing.piForm
    · exact FormationSensitive.Typing.var 3
    · exact .sort sortLevel
    · apply FormationSensitive.Typing.piForm
      · apply FormationSensitiveMIL.primitiveFamilyApp_hasType
        · exact FormationSensitive.Typing.var 3
        · exact FormationSensitive.Typing.var 1
        · exact FormationSensitive.Typing.var 0
      · exact .sort primitiveLevel
      · apply motiveApp_hasType (sorts := .var 5) (primitives := .var 4)
        · exact FormationSensitive.Typing.var 3
        · exact FormationSensitive.Typing.var 2
        · exact FormationSensitive.Typing.var 1
        · apply FormationSensitiveMIL.primitiveApp_hasType
          · exact FormationSensitive.Typing.var 5
          · exact FormationSensitive.Typing.var 4
          · exact FormationSensitive.Typing.var 2
          · exact FormationSensitive.Typing.var 1
          · exact FormationSensitive.Typing.var 0
      · exact .sort eliminationLevel
      · exact .sorts primitiveLevel eliminationLevel
    · exact .sort primitiveCaseAfterSymbolLevel
    · exact .sorts sortLevel primitiveCaseAfterSymbolLevel
  · exact .sort primitiveCaseAfterTargetLevel
  · exact .sorts sortLevel primitiveCaseAfterTargetLevel

theorem chainCaseType_hasType :
    Typing contextSPMPrimitive chainCaseType (sortTm chainCaseLevel) := by
  unfold chainCaseType chainCaseLevel chainCaseAfterMiddleLevel
    chainCaseAfterTargetLevel chainCaseAfterEarlierLevel
    chainCaseAfterLaterLevel chainCaseAfterEarlierIHLevel
    chainCaseAfterLaterIHLevel
  apply FormationSensitive.Typing.piForm
  · exact FormationSensitive.Typing.var 3
  · exact .sort sortLevel
  · apply FormationSensitive.Typing.piForm
    · exact FormationSensitive.Typing.var 4
    · exact .sort sortLevel
    · apply FormationSensitive.Typing.piForm
      · exact FormationSensitive.Typing.var 5
      · exact .sort sortLevel
      · apply FormationSensitive.Typing.piForm
        · apply FormationSensitiveMIL.hypothesisApp_hasType
          · exact FormationSensitive.Typing.var 6
          · exact FormationSensitive.Typing.var 5
          · exact FormationSensitive.Typing.var 2
          · exact FormationSensitive.Typing.var 1
        · exact .sort hypothesisLevel
        · apply FormationSensitive.Typing.piForm
          · apply FormationSensitiveMIL.hypothesisApp_hasType
            · exact FormationSensitive.Typing.var 7
            · exact FormationSensitive.Typing.var 6
            · exact FormationSensitive.Typing.var 2
            · exact FormationSensitive.Typing.var 1
          · exact .sort hypothesisLevel
          · apply FormationSensitive.Typing.piForm
            · apply motiveApp_hasType (sorts := .var 8)
                (primitives := .var 7)
              · exact FormationSensitive.Typing.var 6
              · exact FormationSensitive.Typing.var 4
              · exact FormationSensitive.Typing.var 3
              · exact FormationSensitive.Typing.var 1
            · exact .sort eliminationLevel
            · apply FormationSensitive.Typing.piForm
              · apply motiveApp_hasType (sorts := .var 9)
                  (primitives := .var 8)
                · exact FormationSensitive.Typing.var 7
                · exact FormationSensitive.Typing.var 4
                · exact FormationSensitive.Typing.var 3
                · exact FormationSensitive.Typing.var 1
              · exact .sort eliminationLevel
              · apply motiveApp_hasType (sorts := .var 10)
                  (primitives := .var 9)
                · exact FormationSensitive.Typing.var 8
                · exact FormationSensitive.Typing.var 6
                · exact FormationSensitive.Typing.var 4
                · apply FormationSensitiveMIL.chainApp_hasType
                  · exact FormationSensitive.Typing.var 10
                  · exact FormationSensitive.Typing.var 9
                  · exact FormationSensitive.Typing.var 6
                  · exact FormationSensitive.Typing.var 5
                  · exact FormationSensitive.Typing.var 4
                  · exact FormationSensitive.Typing.var 3
                  · exact FormationSensitive.Typing.var 2
              · exact .sort eliminationLevel
              · exact .sorts eliminationLevel eliminationLevel
            · exact .sort chainCaseAfterLaterIHLevel
            · exact .sorts eliminationLevel chainCaseAfterLaterIHLevel
          · exact .sort chainCaseAfterEarlierIHLevel
          · exact .sorts hypothesisLevel chainCaseAfterEarlierIHLevel
        · exact .sort chainCaseAfterLaterLevel
        · exact .sorts hypothesisLevel chainCaseAfterLaterLevel
      · exact .sort chainCaseAfterEarlierLevel
      · exact .sorts sortLevel chainCaseAfterEarlierLevel
    · exact .sort chainCaseAfterTargetLevel
    · exact .sorts sortLevel chainCaseAfterTargetLevel
  · exact .sort chainCaseAfterMiddleLevel
  · exact .sorts sortLevel chainCaseAfterMiddleLevel

theorem eliminateResultType_hasType :
    Typing contextSPMPrimitiveChain eliminateResultType
      (sortTm eliminateResultLevel) := by
  unfold eliminateResultType eliminateResultLevel eliminateAfterTargetLevel
    eliminateAfterHypothesisLevel
  apply FormationSensitive.Typing.piForm
  · exact FormationSensitive.Typing.var 4
  · exact .sort sortLevel
  · apply FormationSensitive.Typing.piForm
    · exact FormationSensitive.Typing.var 5
    · exact .sort sortLevel
    · apply FormationSensitive.Typing.piForm
      · apply FormationSensitiveMIL.hypothesisApp_hasType
        · exact FormationSensitive.Typing.var 6
        · exact FormationSensitive.Typing.var 5
        · exact FormationSensitive.Typing.var 1
        · exact FormationSensitive.Typing.var 0
      · exact .sort hypothesisLevel
      · apply motiveApp_hasType (sorts := .var 7)
          (primitives := .var 6)
        · exact FormationSensitive.Typing.var 5
        · exact FormationSensitive.Typing.var 2
        · exact FormationSensitive.Typing.var 1
        · exact FormationSensitive.Typing.var 0
      · exact .sort eliminationLevel
      · exact .sorts hypothesisLevel eliminationLevel
    · exact .sort eliminateAfterHypothesisLevel
    · exact .sorts sortLevel eliminateAfterHypothesisLevel
  · exact .sort eliminateAfterTargetLevel
  · exact .sorts sortLevel eliminateAfterTargetLevel

theorem eliminateType_hasType :
    Typing (.nil : Tower.Ctx 0) eliminateType
      (sortTm eliminateDeclarationLevel) := by
  unfold eliminateType eliminateDeclarationLevel eliminateAfterPrimitiveLevel
    eliminateAfterMotiveLevel eliminateAfterPrimitiveCaseLevel
    eliminateAfterChainCaseLevel
  apply FormationSensitive.Typing.piForm
  · exact .headType (.sort sortLevel)
  · exact .sort (.succ sortLevel)
  · apply FormationSensitive.Typing.piForm
    · exact FormationSensitiveMIL.primitiveFamilyType_hasType
    · exact .sort primitiveFamilyTypeLevel
    · apply FormationSensitive.Typing.piForm
      · exact motiveType_hasType
      · exact .sort motiveDeclarationLevel
      · apply FormationSensitive.Typing.piForm
        · exact primitiveCaseType_hasType
        · exact .sort primitiveCaseLevel
        · apply FormationSensitive.Typing.piForm
          · exact chainCaseType_hasType
          · exact .sort chainCaseLevel
          · exact eliminateResultType_hasType
          · exact .sort eliminateResultLevel
          · exact .sorts chainCaseLevel eliminateResultLevel
        · exact .sort eliminateAfterChainCaseLevel
        · exact .sorts primitiveCaseLevel eliminateAfterChainCaseLevel
      · exact .sort eliminateAfterPrimitiveCaseLevel
      · exact .sorts motiveDeclarationLevel
          eliminateAfterPrimitiveCaseLevel
    · exact .sort eliminateAfterMotiveLevel
    · exact .sorts primitiveFamilyTypeLevel eliminateAfterMotiveLevel
  · exact .sort eliminateAfterPrimitiveLevel
  · exact .sorts (.succ sortLevel) eliminateAfterPrimitiveLevel

/-- The native eliminator constant is admitted by its actual lookup and
independently established closed declaration formation. -/
theorem eliminateConstant_hasType {context : Tower.Ctx n} :
    Typing context (.const eliminateName) (liftClosed eliminateType) := by
  apply FormationSensitive.Typing.const (u := .sort eliminateDeclarationLevel)
  · change combinedType Tower.rules rawSignature eliminateName = some eliminateType
    apply combinedType_of_signature
    · rfl
    · exact typeOf_eliminate
  · exact eliminateType_hasType
  · exact .sort eliminateDeclarationLevel

/-! ## Application to the original parameters and canonical telescopes -/

theorem eliminateAtParameters_hasType :
    Typing contextSPMPrimitiveChain eliminateAtParameters
      eliminateAtParametersType := by
  have afterSorts := FormationSensitive.Typing.appElim
    (eliminateConstant_hasType (context := contextSPMPrimitiveChain))
    (FormationSensitive.Typing.var 4)
  have afterPrimitives := FormationSensitive.Typing.appElim afterSorts
    (FormationSensitive.Typing.var 3)
  have afterMotive := FormationSensitive.Typing.appElim afterPrimitives
    (FormationSensitive.Typing.var 2)
  have afterPrimitive := FormationSensitive.Typing.appElim afterMotive
    (FormationSensitive.Typing.var 1)
  have afterChain := FormationSensitive.Typing.appElim afterPrimitive
    (FormationSensitive.Typing.var 0)
  convert afterChain using 1
  all_goals decide

theorem eliminateAtPrimitiveParameters_hasType :
    Typing contextSPMPCSourceTargetSymbol eliminateAtPrimitiveParameters
      eliminateAtPrimitiveParametersType := by
  have afterSource := eliminateAtParameters_hasType.weaken
    (extension := (.var 4 : Tower.Tm 5))
  have afterTarget := afterSource.weaken
    (extension := (.var 5 : Tower.Tm 6))
  have afterSymbol := afterTarget.weaken
    (extension :=
      (.app (.app (.var 5) (.var 1)) (.var 0) : Tower.Tm 7))
  unfold contextSPMPCSourceTargetSymbol contextSPMPCSourceTarget
    contextSPMPCSource eliminateAtPrimitiveParameters
    eliminateAtPrimitiveParametersType weaken3 weaken2 weaken1
  exact afterSymbol

theorem eliminateAtChainParameters_hasType :
    Typing contextSPMPCChainSourceMiddleTargetEarlierLater
      eliminateAtChainParameters eliminateAtChainParametersType := by
  have afterSource := eliminateAtParameters_hasType.weaken
    (extension := (.var 4 : Tower.Tm 5))
  have afterMiddle := afterSource.weaken
    (extension := (.var 5 : Tower.Tm 6))
  have afterTarget := afterMiddle.weaken
    (extension := (.var 6 : Tower.Tm 7))
  have afterEarlier := afterTarget.weaken
    (extension :=
      (hypothesisApp (.var 7) (.var 6) (.var 2) (.var 1) : Tower.Tm 8))
  have afterLater := afterEarlier.weaken
    (extension :=
      (hypothesisApp (.var 8) (.var 7) (.var 2) (.var 1) : Tower.Tm 9))
  unfold contextSPMPCChainSourceMiddleTargetEarlierLater
    contextSPMPCChainSourceMiddleTargetEarlier
    contextSPMPCChainSourceMiddleTarget contextSPMPCChainSourceMiddle
    contextSPMPCChainSource eliminateAtChainParameters
    eliminateAtChainParametersType weaken5 weaken4 weaken3 weaken2 weaken1
  exact afterLater

#print axioms motiveApp_hasType
#print axioms primitiveCaseType_hasType
#print axioms chainCaseType_hasType
#print axioms eliminateType_hasType
#print axioms eliminateAtParameters_hasType
#print axioms eliminateAtPrimitiveParameters_hasType
#print axioms eliminateAtChainParameters_hasType

end FormationSensitiveMILElimination
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
