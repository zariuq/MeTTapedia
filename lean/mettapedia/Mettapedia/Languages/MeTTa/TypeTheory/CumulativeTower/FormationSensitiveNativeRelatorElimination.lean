import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveNativeListDeclarations

/-!
# Formation-sensitive proof-relevant List relator elimination

The original combined List, identity and mapRel rules are unchanged. The
eliminator motive depends on both list indices and the selected relational
evidence. Declaration formation and both canonical iota endpoints are
derived in the formation-sensitive judgment, without using raw typing
receipts. Typed substitution retains the informative root evidence.

This leaf establishes declaration and schema admission, not confluence,
normalization or unrestricted subject reduction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FormationSensitiveNativeRelatorElimination

open Presentation Presentation.Declaration NativeIndexedFamilies RussellTarski
open IntrinsicRelator
open FormationSensitiveNativeList (Typing)

variable {n : Nat}

theorem motiveApp_hasType {context : Tower.Ctx n}
    {source target relation motive sourceList targetList evidence : Tower.Tm n}
    (motiveTyping : Typing context motive
      (motiveTypeAt source target relation))
    (sourceListTyping : Typing context sourceList
      (Intrinsic.listApp source))
    (targetListTyping : Typing context targetList
      (Intrinsic.listApp target))
    (evidenceTyping : Typing context evidence
      (mapRelApp source target relation sourceList targetList)) :
    Typing context
      (motiveApp motive sourceList targetList evidence)
      (sortTm eliminationLevel) := by
  have afterSource := FormationSensitive.Typing.appElim motiveTyping
    sourceListTyping
  have afterSourceNormalized :
      Typing context (.app motive sourceList)
        (motiveAfterSourceType source target relation sourceList) := by
    simpa only [motiveTypeAt, motiveAfterSourceType, Presentation.inst0,
      Presentation.subst, mapRelApp, Intrinsic.listApp,
      instantiateOne_weaken1, instantiateUnderOne_weaken2,
      liftSub_subst0_one, Presentation.liftSub_zero, sortTm]
      using afterSource
  have afterTarget := FormationSensitive.Typing.appElim afterSourceNormalized
    targetListTyping
  have afterTargetNormalized :
      Typing context (.app (.app motive sourceList) targetList)
        (.pi (mapRelApp source target relation sourceList targetList)
          (sortTm eliminationLevel)) := by
    simpa only [motiveAfterSourceType, Presentation.inst0,
      Presentation.subst, mapRelApp, Intrinsic.listApp,
      instantiateOne_weaken1, Presentation.subst0_zero, sortTm]
      using afterTarget
  have afterEvidence := FormationSensitive.Typing.appElim afterTargetNormalized
    evidenceTyping
  simpa [motiveApp, Presentation.inst0, sortTm, Presentation.subst]
    using afterEvidence

theorem motiveType_hasType :
    Typing contextABR motiveType (sortTm motiveTypeLevel) := by
  unfold motiveType motiveTypeLevel motiveAfterTargetListLevel
    motiveAfterEvidenceLevel
  apply FormationSensitive.Typing.piForm
  · apply FormationSensitiveNativeList.listApp_hasType
    exact FormationSensitive.Typing.var 2
  · exact .sort Intrinsic.elementLevel
  · apply FormationSensitive.Typing.piForm
    · apply FormationSensitiveNativeList.listApp_hasType
      exact FormationSensitive.Typing.var 2
    · exact .sort Intrinsic.elementLevel
    · apply FormationSensitive.Typing.piForm
      · apply FormationSensitiveNativeList.mapRelApp_hasType
        · exact FormationSensitive.Typing.var 4
        · exact FormationSensitive.Typing.var 3
        · exact FormationSensitive.Typing.var 2
        · exact FormationSensitive.Typing.var 1
        · exact FormationSensitive.Typing.var 0
      · exact .sort Intrinsic.motiveLevel
      · exact .headType (.sort eliminationLevel)
      · exact .sort (.succ eliminationLevel)
      · exact .sorts Intrinsic.motiveLevel (.succ eliminationLevel)
    · exact .sort motiveAfterEvidenceLevel
    · exact .sorts Intrinsic.elementLevel motiveAfterEvidenceLevel
  · exact .sort motiveAfterTargetListLevel
  · exact .sorts Intrinsic.elementLevel motiveAfterTargetListLevel

theorem nilCaseType_hasType :
    Typing contextABRP nilCaseType (sortTm eliminationLevel) := by
  unfold nilCaseType contextABRP
  apply motiveApp_hasType (source := (.var 3 : Tower.Tm 4))
    (target := .var 2) (relation := .var 1)
  · exact FormationSensitive.Typing.var 0
  · apply FormationSensitiveNativeList.nilApp_hasType
    exact FormationSensitive.Typing.var 3
  · apply FormationSensitiveNativeList.nilApp_hasType
    exact FormationSensitive.Typing.var 2
  · apply FormationSensitiveNativeList.nilRelApp_hasType
    · exact FormationSensitive.Typing.var 3
    · exact FormationSensitive.Typing.var 2
    · exact FormationSensitive.Typing.var 1

theorem consCaseType_hasType :
    Typing contextABRPZ consCaseType (sortTm consCaseLevel) := by
  unfold consCaseType consCaseLevel consCaseAfterTargetHeadLevel
    consCaseAfterSourceTailLevel consCaseAfterTargetTailLevel
    consCaseAfterHeadEvidenceLevel consCaseAfterTailEvidenceLevel
    consCaseAfterRecursiveLevel
  apply FormationSensitive.Typing.piForm
  · exact FormationSensitive.Typing.var 4
  · exact .sort Intrinsic.elementLevel
  · apply FormationSensitive.Typing.piForm
    · exact FormationSensitive.Typing.var 4
    · exact .sort Intrinsic.elementLevel
    · apply FormationSensitive.Typing.piForm
      · apply FormationSensitiveNativeList.listApp_hasType
        exact FormationSensitive.Typing.var 6
      · exact .sort Intrinsic.elementLevel
      · apply FormationSensitive.Typing.piForm
        · apply FormationSensitiveNativeList.listApp_hasType
          exact FormationSensitive.Typing.var 6
        · exact .sort Intrinsic.elementLevel
        · apply FormationSensitive.Typing.piForm
          · apply FormationSensitiveNativeList.relationApp_hasType
              (source := (.var 8 : Tower.Tm 9))
              (target := .var 7) (relation := .var 6)
              (sourceTerm := .var 3) (targetTerm := .var 2)
            · exact FormationSensitive.Typing.var 6
            · exact FormationSensitive.Typing.var 3
            · exact FormationSensitive.Typing.var 2
          · exact .sort Intrinsic.motiveLevel
          · apply FormationSensitive.Typing.piForm
            · apply FormationSensitiveNativeList.mapRelApp_hasType
              · exact FormationSensitive.Typing.var 9
              · exact FormationSensitive.Typing.var 8
              · exact FormationSensitive.Typing.var 7
              · exact FormationSensitive.Typing.var 2
              · exact FormationSensitive.Typing.var 1
            · exact .sort Intrinsic.motiveLevel
            · apply FormationSensitive.Typing.piForm
              · apply motiveApp_hasType
                  (source := (.var 10 : Tower.Tm 11))
                  (target := .var 9) (relation := .var 8)
                · exact FormationSensitive.Typing.var 7
                · exact FormationSensitive.Typing.var 3
                · exact FormationSensitive.Typing.var 2
                · exact FormationSensitive.Typing.var 0
              · exact .sort eliminationLevel
              · apply motiveApp_hasType
                  (source := (.var 11 : Tower.Tm 12))
                  (target := .var 10) (relation := .var 9)
                · exact FormationSensitive.Typing.var 8
                · apply FormationSensitiveNativeList.consApp_hasType
                  · exact FormationSensitive.Typing.var 11
                  · exact FormationSensitive.Typing.var 6
                  · exact FormationSensitive.Typing.var 4
                · apply FormationSensitiveNativeList.consApp_hasType
                  · exact FormationSensitive.Typing.var 10
                  · exact FormationSensitive.Typing.var 5
                  · exact FormationSensitive.Typing.var 3
                · apply FormationSensitiveNativeList.consRelApp_hasType
                  · exact FormationSensitive.Typing.var 11
                  · exact FormationSensitive.Typing.var 10
                  · exact FormationSensitive.Typing.var 9
                  · exact FormationSensitive.Typing.var 6
                  · exact FormationSensitive.Typing.var 5
                  · exact FormationSensitive.Typing.var 4
                  · exact FormationSensitive.Typing.var 3
                  · exact FormationSensitive.Typing.var 2
                  · exact FormationSensitive.Typing.var 1
              · exact .sort eliminationLevel
              · exact .sorts eliminationLevel eliminationLevel
            · exact .sort consCaseAfterRecursiveLevel
            · exact .sorts Intrinsic.motiveLevel
                consCaseAfterRecursiveLevel
          · exact .sort consCaseAfterTailEvidenceLevel
          · exact .sorts Intrinsic.motiveLevel
              consCaseAfterTailEvidenceLevel
        · exact .sort consCaseAfterHeadEvidenceLevel
        · exact .sorts Intrinsic.elementLevel
            consCaseAfterHeadEvidenceLevel
      · exact .sort consCaseAfterTargetTailLevel
      · exact .sorts Intrinsic.elementLevel consCaseAfterTargetTailLevel
    · exact .sort consCaseAfterSourceTailLevel
    · exact .sorts Intrinsic.elementLevel consCaseAfterSourceTailLevel
  · exact .sort consCaseAfterTargetHeadLevel
  · exact .sorts Intrinsic.elementLevel consCaseAfterTargetHeadLevel

theorem eliminateResultType_hasType :
    Typing contextABRPZS eliminateResultType
      (sortTm eliminateResultLevel) := by
  unfold eliminateResultType eliminateResultLevel eliminateAfterTargetListLevel
    eliminateAfterEvidenceLevel
  apply FormationSensitive.Typing.piForm
  · apply FormationSensitiveNativeList.listApp_hasType
    exact FormationSensitive.Typing.var 5
  · exact .sort Intrinsic.elementLevel
  · apply FormationSensitive.Typing.piForm
    · apply FormationSensitiveNativeList.listApp_hasType
      exact FormationSensitive.Typing.var 5
    · exact .sort Intrinsic.elementLevel
    · apply FormationSensitive.Typing.piForm
      · apply FormationSensitiveNativeList.mapRelApp_hasType
        · exact FormationSensitive.Typing.var 7
        · exact FormationSensitive.Typing.var 6
        · exact FormationSensitive.Typing.var 5
        · exact FormationSensitive.Typing.var 1
        · exact FormationSensitive.Typing.var 0
      · exact .sort Intrinsic.motiveLevel
      · apply motiveApp_hasType
          (source := (.var 8 : Tower.Tm 9))
          (target := .var 7) (relation := .var 6)
        · exact FormationSensitive.Typing.var 5
        · exact FormationSensitive.Typing.var 2
        · exact FormationSensitive.Typing.var 1
        · exact FormationSensitive.Typing.var 0
      · exact .sort eliminationLevel
      · exact .sorts Intrinsic.motiveLevel eliminationLevel
    · exact .sort eliminateAfterEvidenceLevel
    · exact .sorts Intrinsic.elementLevel eliminateAfterEvidenceLevel
  · exact .sort eliminateAfterTargetListLevel
  · exact .sorts Intrinsic.elementLevel eliminateAfterTargetListLevel

theorem eliminateType_hasType :
    Typing (.nil : Tower.Ctx 0) eliminateType
      (sortTm eliminateDeclarationLevel) := by
  unfold eliminateType eliminateDeclarationLevel eliminateAfterTargetLevel
    eliminateAfterRelationLevel eliminateAfterMotiveLevel
    eliminateAfterNilCaseLevel eliminateAfterConsCaseLevel
  apply FormationSensitive.Typing.piForm
  · exact .headType (.sort Intrinsic.elementLevel)
  · exact .sort (.succ Intrinsic.elementLevel)
  · apply FormationSensitive.Typing.piForm
    · exact .headType (.sort Intrinsic.elementLevel)
    · exact .sort (.succ Intrinsic.elementLevel)
    · apply FormationSensitive.Typing.piForm
      · exact FormationSensitiveNativeList.relationType_hasType
      · exact .sort relationTypeLevel
      · apply FormationSensitive.Typing.piForm
        · exact motiveType_hasType
        · exact .sort motiveTypeLevel
        · apply FormationSensitive.Typing.piForm
          · exact nilCaseType_hasType
          · exact .sort eliminationLevel
          · apply FormationSensitive.Typing.piForm
            · exact consCaseType_hasType
            · exact .sort consCaseLevel
            · exact eliminateResultType_hasType
            · exact .sort eliminateResultLevel
            · exact .sorts consCaseLevel eliminateResultLevel
          · exact .sort eliminateAfterConsCaseLevel
          · exact .sorts eliminationLevel eliminateAfterConsCaseLevel
        · exact .sort eliminateAfterNilCaseLevel
        · exact .sorts motiveTypeLevel eliminateAfterNilCaseLevel
      · exact .sort eliminateAfterMotiveLevel
      · exact .sorts relationTypeLevel eliminateAfterMotiveLevel
    · exact .sort eliminateAfterRelationLevel
    · exact .sorts (.succ Intrinsic.elementLevel)
        eliminateAfterRelationLevel
  · exact .sort eliminateAfterTargetLevel
  · exact .sorts (.succ Intrinsic.elementLevel) eliminateAfterTargetLevel

theorem eliminateConstant_hasType {context : Tower.Ctx n} :
    Typing context (.const eliminateName) (liftClosed eliminateType) := by
  apply FormationSensitive.Typing.const (u := .sort eliminateDeclarationLevel)
  · decide
  · exact eliminateType_hasType
  · exact .sort eliminateDeclarationLevel

theorem eliminateAtParameters_hasType :
    Typing contextABRPZS eliminateAtParameters
      eliminateAtParametersType := by
  have sourceTyping :
      Typing contextABRPZS (.var 5)
        (sortTm Intrinsic.elementLevel) :=
    FormationSensitive.Typing.var 5
  have targetTyping :
      Typing contextABRPZS (.var 4)
        (sortTm Intrinsic.elementLevel) :=
    FormationSensitive.Typing.var 4
  have relationTyping :
      Typing contextABRPZS (.var 3)
        (.pi (.var 5)
          (.pi (Presentation.rename wk (.var 4))
            (sortTm Intrinsic.motiveLevel))) :=
    FormationSensitive.Typing.var 3
  have motiveTyping :
      Typing contextABRPZS (.var 2)
        (motiveTypeAt (.var 5) (.var 4) (.var 3)) := by
    exact FormationSensitive.Typing.var 2
  have nilCaseTyping :
      Typing contextABRPZS (.var 1)
        (Presentation.rename wk (Presentation.rename wk nilCaseType)) := by
    exact FormationSensitive.Typing.var 1
  have consCaseTyping :
      Typing contextABRPZS (.var 0)
        (Presentation.rename wk consCaseType) := by
    exact FormationSensitive.Typing.var 0
  have afterSource := FormationSensitive.Typing.appElim
    (eliminateConstant_hasType (context := contextABRPZS)) sourceTyping
  have afterTarget := FormationSensitive.Typing.appElim afterSource targetTyping
  have afterRelation := FormationSensitive.Typing.appElim afterTarget relationTyping
  have afterMotive := FormationSensitive.Typing.appElim afterRelation motiveTyping
  have afterNil := FormationSensitive.Typing.appElim afterMotive nilCaseTyping
  have afterCons := FormationSensitive.Typing.appElim afterNil consCaseTyping
  convert afterCons using 1 <;> decide

theorem eliminateAtConsParameters_hasType :
    Typing contextABRPZSSourceTargetHeadSourceTargetTailHeadTail
      eliminateAtConsParameters eliminateAtConsParametersType := by
  have afterSourceHead := eliminateAtParameters_hasType.weaken
    (extension := (.var 5 : Tower.Tm 6))
  have afterTargetHead := afterSourceHead.weaken
    (extension := (.var 5 : Tower.Tm 7))
  have afterSourceTail := afterTargetHead.weaken
    (extension := Intrinsic.listApp (.var 7 : Tower.Tm 8))
  have afterTargetTail := afterSourceTail.weaken
    (extension := Intrinsic.listApp (.var 7 : Tower.Tm 9))
  have afterHeadEvidence := afterTargetTail.weaken
    (extension :=
      (.app (.app (.var 7) (.var 3)) (.var 2) : Tower.Tm 10))
  have afterTailEvidence := afterHeadEvidence.weaken
    (extension :=
      (mapRelApp (.var 10) (.var 9) (.var 8) (.var 2) (.var 1) :
        Tower.Tm 11))
  unfold contextABRPZSSourceTargetHeadSourceTargetTailHeadTail
    contextABRPZSSourceTargetHeadSourceTargetTailHead
    contextABRPZSSourceTargetHeadSourceTargetTail
    contextABRPZSSourceTargetHeadSourceTail
    contextABRPZSSourceTargetHead contextABRPZSSourceHead
    eliminateAtConsParameters eliminateAtConsParametersType weaken6 weaken5
    weaken4 weaken3 weaken2 weaken1
  exact afterTailEvidence

theorem contextABR_formed :
    FormationSensitive.ContextFormation rules contextABR :=
  .snoc
    (.snoc
      (.snoc .nil (.headType (.sort Intrinsic.elementLevel))
        (.sort (.succ Intrinsic.elementLevel)))
      (.headType (.sort Intrinsic.elementLevel))
      (.sort (.succ Intrinsic.elementLevel)))
    FormationSensitiveNativeList.relationType_hasType (.sort relationTypeLevel)

theorem contextABRPZS_formed :
    FormationSensitive.ContextFormation rules contextABRPZS :=
  .snoc
    (.snoc
      (.snoc contextABR_formed motiveType_hasType (.sort motiveTypeLevel))
      nilCaseType_hasType (.sort eliminationLevel))
    consCaseType_hasType (.sort consCaseLevel)

theorem consContext_formed :
    FormationSensitive.ContextFormation rules
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail := by
  have sourceHead : FormationSensitive.ContextFormation rules
      contextABRPZSSourceHead :=
    .snoc contextABRPZS_formed (FormationSensitive.Typing.var 5)
      (.sort Intrinsic.elementLevel)
  have targetHead : FormationSensitive.ContextFormation rules
      contextABRPZSSourceTargetHead :=
    .snoc sourceHead (FormationSensitive.Typing.var 5)
      (.sort Intrinsic.elementLevel)
  have sourceTail : FormationSensitive.ContextFormation rules
      contextABRPZSSourceTargetHeadSourceTail :=
    .snoc targetHead
      (FormationSensitiveNativeList.listApp_hasType (FormationSensitive.Typing.var 7))
      (.sort Intrinsic.elementLevel)
  have targetTail : FormationSensitive.ContextFormation rules
      contextABRPZSSourceTargetHeadSourceTargetTail :=
    .snoc sourceTail
      (FormationSensitiveNativeList.listApp_hasType (FormationSensitive.Typing.var 7))
      (.sort Intrinsic.elementLevel)
  have headEvidence : FormationSensitive.ContextFormation rules
      contextABRPZSSourceTargetHeadSourceTargetTailHead := by
    apply FormationSensitive.ContextFormation.snoc targetTail
    · apply FormationSensitiveNativeList.relationApp_hasType
        (source := (.var 9 : Tower.Tm 10)) (target := .var 8)
      · exact FormationSensitive.Typing.var 7
      · exact FormationSensitive.Typing.var 3
      · exact FormationSensitive.Typing.var 2
    · exact .sort Intrinsic.motiveLevel
  apply FormationSensitive.ContextFormation.snoc headEvidence
  · apply FormationSensitiveNativeList.mapRelApp_hasType
    · exact FormationSensitive.Typing.var 10
    · exact FormationSensitive.Typing.var 9
    · exact FormationSensitive.Typing.var 8
    · exact FormationSensitive.Typing.var 2
    · exact FormationSensitive.Typing.var 1
  · exact .sort Intrinsic.motiveLevel

theorem nilIotaLeft_hasType :
    Typing contextABRPZS nilIotaLeft nilIotaResultType := by
  have sourceTyping :
      Typing contextABRPZS (.var 5)
        (sortTm Intrinsic.elementLevel) :=
    FormationSensitive.Typing.var 5
  have targetTyping :
      Typing contextABRPZS (.var 4)
        (sortTm Intrinsic.elementLevel) :=
    FormationSensitive.Typing.var 4
  have sourceListTyping := FormationSensitiveNativeList.nilApp_hasType sourceTyping
  have targetListTyping := FormationSensitiveNativeList.nilApp_hasType targetTyping
  have evidenceTyping := FormationSensitiveNativeList.nilRelApp_hasType sourceTyping targetTyping
    (FormationSensitive.Typing.var 3)
  have afterSource := FormationSensitive.Typing.appElim
    eliminateAtParameters_hasType sourceListTyping
  have afterTarget := FormationSensitive.Typing.appElim afterSource
    targetListTyping
  have result := FormationSensitive.Typing.appElim afterTarget evidenceTyping
  convert result using 1 <;> decide
theorem nilIotaRight_hasType :
    Typing contextABRPZS nilIotaRight nilIotaResultType :=
  FormationSensitive.Typing.var 1

theorem consIotaLeft_hasType :
    Typing contextABRPZSSourceTargetHeadSourceTargetTailHeadTail
      consIotaLeft consIotaResultType := by
  have sourceTyping : Typing
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 11)
      (sortTm Intrinsic.elementLevel) :=
    FormationSensitive.Typing.var 11
  have targetTyping : Typing
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 10)
      (sortTm Intrinsic.elementLevel) :=
    FormationSensitive.Typing.var 10
  have sourceHeadTyping : Typing
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 5)
      (.var 11) := FormationSensitive.Typing.var 5
  have targetHeadTyping : Typing
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 4)
      (.var 10) := FormationSensitive.Typing.var 4
  have sourceTailTyping : Typing
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 3)
      (Intrinsic.listApp (.var 11)) := FormationSensitive.Typing.var 3
  have targetTailTyping : Typing
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 2)
      (Intrinsic.listApp (.var 10)) := FormationSensitive.Typing.var 2
  have headEvidenceTyping : Typing
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 1)
      (.app (.app (.var 9) (.var 5)) (.var 4)) :=
    FormationSensitive.Typing.var 1
  have tailEvidenceTyping : Typing
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 0)
      (mapRelApp (.var 11) (.var 10) (.var 9) (.var 3) (.var 2)) :=
    FormationSensitive.Typing.var 0
  have sourceListTyping := FormationSensitiveNativeList.consApp_hasType sourceTyping sourceHeadTyping
    sourceTailTyping
  have targetListTyping := FormationSensitiveNativeList.consApp_hasType targetTyping targetHeadTyping
    targetTailTyping
  have evidenceTyping := FormationSensitiveNativeList.consRelApp_hasType sourceTyping targetTyping
    (FormationSensitive.Typing.var 9) sourceHeadTyping targetHeadTyping
    sourceTailTyping targetTailTyping headEvidenceTyping tailEvidenceTyping
  have afterSource := FormationSensitive.Typing.appElim
    eliminateAtConsParameters_hasType sourceListTyping
  have afterTarget := FormationSensitive.Typing.appElim afterSource
    targetListTyping
  have result := FormationSensitive.Typing.appElim afterTarget evidenceTyping
  convert result using 1 <;> decide
/-- Both relation witnesses, both indices and the recursive result at the
selected tail evidence remain in the branch application. -/
theorem consIotaRight_hasType :
    Typing contextABRPZSSourceTargetHeadSourceTargetTailHeadTail
      consIotaRight consIotaResultType := by
  have sourceHeadTyping : Typing
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 5)
      (.var 11) := FormationSensitive.Typing.var 5
  have targetHeadTyping : Typing
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 4)
      (.var 10) := FormationSensitive.Typing.var 4
  have sourceTailTyping : Typing
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 3)
      (Intrinsic.listApp (.var 11)) := FormationSensitive.Typing.var 3
  have targetTailTyping : Typing
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 2)
      (Intrinsic.listApp (.var 10)) := FormationSensitive.Typing.var 2
  have headEvidenceTyping : Typing
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 1)
      (.app (.app (.var 9) (.var 5)) (.var 4)) :=
    FormationSensitive.Typing.var 1
  have tailEvidenceTyping : Typing
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 0)
      (mapRelApp (.var 11) (.var 10) (.var 9) (.var 3) (.var 2)) :=
    FormationSensitive.Typing.var 0
  have consCaseTyping : Typing
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 6)
      (Presentation.rename wk (weaken6 consCaseType)) :=
    FormationSensitive.Typing.var 6
  have recursiveAfterSource := FormationSensitive.Typing.appElim
    eliminateAtConsParameters_hasType sourceTailTyping
  have recursiveAfterTarget := FormationSensitive.Typing.appElim
    recursiveAfterSource targetTailTyping
  have recursiveTyping := FormationSensitive.Typing.appElim
    recursiveAfterTarget tailEvidenceTyping
  have afterSourceHead := FormationSensitive.Typing.appElim consCaseTyping
    sourceHeadTyping
  have afterTargetHead := FormationSensitive.Typing.appElim afterSourceHead
    targetHeadTyping
  have afterSourceTail := FormationSensitive.Typing.appElim afterTargetHead
    sourceTailTyping
  have afterTargetTail := FormationSensitive.Typing.appElim afterSourceTail
    targetTailTyping
  have afterHeadEvidence := FormationSensitive.Typing.appElim afterTargetTail
    headEvidenceTyping
  have afterTailEvidence := FormationSensitive.Typing.appElim afterHeadEvidence
    tailEvidenceTyping
  have result := FormationSensitive.Typing.appElim afterTailEvidence
    recursiveTyping
  convert result using 1 <;> decide
theorem nilIota_judgments :
    FormationSensitive.Judgment rules contextABRPZS nilIotaLeft nilIotaResultType ∧
    FormationSensitive.Judgment rules contextABRPZS nilIotaRight nilIotaResultType :=
  ⟨⟨contextABRPZS_formed, nilIotaLeft_hasType⟩,
    ⟨contextABRPZS_formed, nilIotaRight_hasType⟩⟩

theorem consIota_judgments :
    FormationSensitive.Judgment rules
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail consIotaLeft consIotaResultType ∧
    FormationSensitive.Judgment rules
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail consIotaRight consIotaResultType :=
  ⟨⟨consContext_formed, consIotaLeft_hasType⟩,
    ⟨consContext_formed, consIotaRight_hasType⟩⟩

theorem nilIota_substitute {context : Tower.Ctx n} {substitution : Sub Tower.Head 6 n}
    (formed : FormationSensitive.ContextFormation rules context)
    (typed : FormationSensitive.CtxMor rules contextABRPZS context substitution) :
    FormationSensitive.Judgment rules context
      (subst substitution nilIotaLeft) (subst substitution nilIotaResultType) ∧
    FormationSensitive.Judgment rules context
      (subst substitution nilIotaRight) (subst substitution nilIotaResultType) :=
  ⟨nilIota_judgments.1.substitute formed typed,
    nilIota_judgments.2.substitute formed typed⟩

theorem consIota_substitute {context : Tower.Ctx n} {substitution : Sub Tower.Head 12 n}
    (formed : FormationSensitive.ContextFormation rules context)
    (typed : FormationSensitive.CtxMor rules
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail context substitution) :
    FormationSensitive.Judgment rules context
      (subst substitution consIotaLeft) (subst substitution consIotaResultType) ∧
    FormationSensitive.Judgment rules context
      (subst substitution consIotaRight) (subst substitution consIotaResultType) :=
  ⟨consIota_judgments.1.substitute formed typed,
    consIota_judgments.2.substitute formed typed⟩

def nilIota_substitutedEvidence (substitution : Sub Tower.Head 6 n) :
    IotaEvidence n (subst substitution nilIotaLeft) (subst substitution nilIotaRight) :=
  (IotaEvidence.nil (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)).substitute
    substitution

def consIota_substitutedEvidence (substitution : Sub Tower.Head 12 n) :
    IotaEvidence n (subst substitution consIotaLeft) (subst substitution consIotaRight) :=
  (IotaEvidence.cons (.var 11) (.var 10) (.var 9) (.var 8) (.var 7) (.var 6)
    (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)).substitute substitution

theorem nilIota_substitutedRoot (substitution : Sub Tower.Head 6 n) :
    rules.computation.step (subst substitution nilIotaLeft) (subst substitution nilIotaRight) :=
  .declared ⟨.rel (nilIota_substitutedEvidence substitution)⟩

theorem consIota_substitutedRoot (substitution : Sub Tower.Head 12 n) :
    rules.computation.step (subst substitution consIotaLeft) (subst substitution consIotaRight) :=
  .declared ⟨.rel (consIota_substitutedEvidence substitution)⟩

#print axioms contextABRPZS_formed
#print axioms consContext_formed
#print axioms nilIota_judgments
#print axioms consIota_judgments
#print axioms nilIota_substitute
#print axioms consIota_substitute
#print axioms nilIota_substitutedRoot
#print axioms consIota_substitutedRoot

#print axioms motiveType_hasType
#print axioms consCaseType_hasType
#print axioms eliminateType_hasType
#print axioms eliminateAtParameters_hasType
#print axioms eliminateAtConsParameters_hasType

#print axioms motiveApp_hasType
#print axioms nilCaseType_hasType
#print axioms eliminateResultType_hasType
#print axioms eliminateConstant_hasType
#print axioms contextABR_formed
#print axioms nilIotaLeft_hasType
#print axioms nilIotaRight_hasType
#print axioms consIotaLeft_hasType
#print axioms consIotaRight_hasType

end FormationSensitiveNativeRelatorElimination
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
