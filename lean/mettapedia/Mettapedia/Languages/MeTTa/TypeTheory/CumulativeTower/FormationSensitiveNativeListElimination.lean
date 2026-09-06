import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveNativeListDeclarations

/-!
# Formation-sensitive admission of the native List eliminator

The existing List/mapRel rule package and original List declaration are
unchanged. Motive and branch formation are proved with refined typing,
independently of the earlier raw certificates. Both canonical iota endpoints
are admitted in their correctly formed telescopes. Typed substitution admits
every instance in a formed ambient context, retaining the selected branch,
head, tail, recursive call and dependent result.

These are declaration and schema obligations. They do not establish
confluence, normalization, or subject reduction for arbitrary combined-profile
programs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FormationSensitiveNativeListElimination

open Presentation Presentation.Declaration NativeIndexedFamilies RussellTarski
open Intrinsic
open FormationSensitiveNativeList (Typing)

variable {n : Nat}

theorem motiveApp_hasType {context : Tower.Ctx n}
    {element motive list : Tower.Tm n}
    (motiveTyping : Typing context motive
      (.pi (listApp element) (sortTm motiveLevel)))
    (listTyping : Typing context list (listApp element)) :
    Typing context (.app motive list) (sortTm motiveLevel) := by
  have application := FormationSensitive.Typing.appElim motiveTyping listTyping
  simpa [sortTm, Presentation.inst0, Presentation.subst] using application

theorem motiveType_hasType :
    Typing contextA motiveType (sortTm motiveTypeLevel) := by
  unfold contextA motiveType motiveTypeLevel
  apply FormationSensitive.Typing.piForm
  · apply FormationSensitiveNativeList.listApp_hasType
    exact FormationSensitive.Typing.var 0
  · exact .sort elementLevel
  · exact .headType (.sort motiveLevel)
  · exact .sort (.succ motiveLevel)
  · exact .sorts elementLevel (.succ motiveLevel)

theorem nilCaseType_hasType :
    Typing contextAP nilCaseType (sortTm motiveLevel) := by
  unfold contextAP nilCaseType
  apply motiveApp_hasType
  · exact FormationSensitive.Typing.var 0
  · apply FormationSensitiveNativeList.nilApp_hasType
    exact FormationSensitive.Typing.var 1

theorem consCaseType_hasType :
    Typing contextAPZ consCaseType (sortTm consCaseLevel) := by
  unfold consCaseType consCaseLevel consCaseTailLevel consCaseInnerLevel
  apply FormationSensitive.Typing.piForm
  · exact FormationSensitive.Typing.var 2
  · exact .sort elementLevel
  · apply FormationSensitive.Typing.piForm
    · apply FormationSensitiveNativeList.listApp_hasType
      exact FormationSensitive.Typing.var 3
    · exact .sort elementLevel
    · apply FormationSensitive.Typing.piForm
      · apply motiveApp_hasType
        · exact FormationSensitive.Typing.var 3
        · exact FormationSensitive.Typing.var 0
      · exact .sort motiveLevel
      · apply motiveApp_hasType
        · exact FormationSensitive.Typing.var 4
        · apply FormationSensitiveNativeList.consApp_hasType
          · exact FormationSensitive.Typing.var 5
          · exact FormationSensitive.Typing.var 2
          · exact FormationSensitive.Typing.var 1
      · exact .sort motiveLevel
      · exact .sorts motiveLevel motiveLevel
    · exact .sort (.max motiveLevel motiveLevel)
    · exact .sorts elementLevel (.max motiveLevel motiveLevel)
  · exact .sort (.max elementLevel (.max motiveLevel motiveLevel))
  · exact .sorts elementLevel
      (.max elementLevel (.max motiveLevel motiveLevel))

theorem eliminateResultType_hasType :
    Typing contextAPZS eliminateResultType
      (sortTm eliminateResultLevel) := by
  unfold contextAPZS eliminateResultType eliminateResultLevel
  apply FormationSensitive.Typing.piForm
  · apply FormationSensitiveNativeList.listApp_hasType
    exact FormationSensitive.Typing.var 3
  · exact .sort elementLevel
  · apply motiveApp_hasType
    · exact FormationSensitive.Typing.var 3
    · exact FormationSensitive.Typing.var 0
  · exact .sort motiveLevel
  · exact .sorts elementLevel motiveLevel

theorem eliminateType_hasType :
    Typing (.nil : Tower.Ctx 0) eliminateType
      (sortTm eliminateDeclarationLevel) := by
  unfold eliminateType eliminateDeclarationLevel eliminateAfterMotiveLevel
    eliminateAfterNilLevel eliminateAfterConsLevel
  apply FormationSensitive.Typing.piForm
  · exact .headType (.sort elementLevel)
  · exact .sort (.succ elementLevel)
  · apply FormationSensitive.Typing.piForm
    · exact motiveType_hasType
    · exact .sort motiveTypeLevel
    · apply FormationSensitive.Typing.piForm
      · exact nilCaseType_hasType
      · exact .sort motiveLevel
      · apply FormationSensitive.Typing.piForm
        · exact consCaseType_hasType
        · exact .sort consCaseLevel
        · exact eliminateResultType_hasType
        · exact .sort eliminateResultLevel
        · exact .sorts consCaseLevel eliminateResultLevel
      · exact .sort (.max consCaseLevel eliminateResultLevel)
      · exact .sorts motiveLevel
          (.max consCaseLevel eliminateResultLevel)
    · exact .sort
        (.max motiveLevel (.max consCaseLevel eliminateResultLevel))
    · exact .sorts motiveTypeLevel
        (.max motiveLevel (.max consCaseLevel eliminateResultLevel))
  · exact .sort
      (.max motiveTypeLevel
        (.max motiveLevel (.max consCaseLevel eliminateResultLevel)))
  · exact .sorts (.succ elementLevel)
      (.max motiveTypeLevel
        (.max motiveLevel (.max consCaseLevel eliminateResultLevel)))

theorem eliminateConstant_hasType {context : Tower.Ctx n} :
    Typing context (.const eliminateName) (liftClosed eliminateType) := by
  apply FormationSensitive.Typing.const (u := .sort eliminateDeclarationLevel)
  · decide
  · exact eliminateType_hasType
  · exact .sort eliminateDeclarationLevel

theorem eliminateAtParameters_hasType :
    Typing contextAPZS eliminateAtParameters eliminateAtParametersType := by
  have elementTyping :
      Typing contextAPZS (.var 3) (sortTm elementLevel) := by
    exact FormationSensitive.Typing.var 3
  have motiveTyping :
      Typing contextAPZS (.var 2)
        (.pi (listApp (.var 3)) (sortTm motiveLevel)) := by
    exact FormationSensitive.Typing.var 2
  have nilCaseTyping :
      Typing contextAPZS (.var 1)
        (.app (.var 2) (nilApp (.var 3))) := by
    exact FormationSensitive.Typing.var 1
  have consCaseTyping :
      Typing contextAPZS (.var 0)
        (Presentation.rename wk consCaseType) := by
    exact FormationSensitive.Typing.var 0
  have afterElement := FormationSensitive.Typing.appElim
    (eliminateConstant_hasType (context := contextAPZS)) elementTyping
  have afterMotive := FormationSensitive.Typing.appElim afterElement motiveTyping
  have afterNil := FormationSensitive.Typing.appElim afterMotive nilCaseTyping
  have afterCons := FormationSensitive.Typing.appElim afterNil consCaseTyping
  convert afterCons using 1 <;> decide

theorem eliminateAtConsParameters_hasType :
    Typing contextAPZSHeadTail eliminateAtConsParameters
      eliminateAtConsParametersType := by
  have afterHead := eliminateAtParameters_hasType.weaken
    (extension := (.var 3 : Tower.Tm 4))
  have weakened := afterHead.weaken
    (extension := listApp (.var 4 : Tower.Tm 5))
  unfold contextAPZSHeadTail contextAPZSHead
  convert weakened using 1 <;> decide

theorem contextAPZS_formed :
    FormationSensitive.ContextFormation IntrinsicRelator.rules contextAPZS :=
  .snoc
    (.snoc
      (.snoc
        (.snoc .nil (.headType (.sort elementLevel)) (.sort (.succ elementLevel)))
        motiveType_hasType (.sort motiveTypeLevel))
      nilCaseType_hasType (.sort motiveLevel))
    consCaseType_hasType (.sort consCaseLevel)

theorem contextAPZSHeadTail_formed :
    FormationSensitive.ContextFormation IntrinsicRelator.rules contextAPZSHeadTail := by
  apply FormationSensitive.ContextFormation.snoc
  · exact .snoc contextAPZS_formed (FormationSensitive.Typing.var 3) (.sort elementLevel)
  · apply FormationSensitiveNativeList.listApp_hasType
    exact FormationSensitive.Typing.var 4
  · exact .sort elementLevel

theorem nilIotaLeft_hasType :
    Typing contextAPZS nilIotaLeft nilIotaResultType := by
  have listTyping := FormationSensitiveNativeList.nilApp_hasType
    (FormationSensitive.Typing.var 3 :
      Typing contextAPZS (.var 3) (sortTm elementLevel))
  have result := FormationSensitive.Typing.appElim eliminateAtParameters_hasType listTyping
  convert result using 1 <;> decide

theorem nilIotaRight_hasType :
    Typing contextAPZS nilIotaRight nilIotaResultType :=
  FormationSensitive.Typing.var 1

theorem consIotaLeft_hasType :
    Typing contextAPZSHeadTail consIotaLeft consIotaResultType := by
  have listTyping := FormationSensitiveNativeList.consApp_hasType
    (FormationSensitive.Typing.var 5 :
      Typing contextAPZSHeadTail (.var 5) (sortTm elementLevel))
    (FormationSensitive.Typing.var 1) (FormationSensitive.Typing.var 0)
  have result := FormationSensitive.Typing.appElim eliminateAtConsParameters_hasType listTyping
  convert result using 1 <;> decide

/-- The step consumes the recursive result at the same tail, not at an
arbitrary list with the same element type. -/
theorem consIotaRight_hasType :
    Typing contextAPZSHeadTail consIotaRight consIotaResultType := by
  have headTyping : Typing contextAPZSHeadTail (.var 1) (.var 5) :=
    FormationSensitive.Typing.var 1
  have tailTyping : Typing contextAPZSHeadTail (.var 0) (listApp (.var 5)) :=
    FormationSensitive.Typing.var 0
  have consCaseTyping : Typing contextAPZSHeadTail (.var 2)
      (rename wk (rename wk (rename wk consCaseType))) :=
    FormationSensitive.Typing.var 2
  have recursiveTyping := FormationSensitive.Typing.appElim
    eliminateAtConsParameters_hasType tailTyping
  have afterHead := FormationSensitive.Typing.appElim consCaseTyping headTyping
  have afterTail := FormationSensitive.Typing.appElim afterHead tailTyping
  have result := FormationSensitive.Typing.appElim afterTail recursiveTyping
  convert result using 1 <;> decide

theorem nilIota_judgments :
    FormationSensitive.Judgment IntrinsicRelator.rules contextAPZS
      nilIotaLeft nilIotaResultType ∧
    FormationSensitive.Judgment IntrinsicRelator.rules contextAPZS
      nilIotaRight nilIotaResultType :=
  ⟨⟨contextAPZS_formed, nilIotaLeft_hasType⟩,
    ⟨contextAPZS_formed, nilIotaRight_hasType⟩⟩

theorem consIota_judgments :
    FormationSensitive.Judgment IntrinsicRelator.rules contextAPZSHeadTail
      consIotaLeft consIotaResultType ∧
    FormationSensitive.Judgment IntrinsicRelator.rules contextAPZSHeadTail
      consIotaRight consIotaResultType :=
  ⟨⟨contextAPZSHeadTail_formed, consIotaLeft_hasType⟩,
    ⟨contextAPZSHeadTail_formed, consIotaRight_hasType⟩⟩

theorem nilIota_substitute {context : Tower.Ctx n}
    {substitution : Sub Tower.Head 4 n}
    (formed : FormationSensitive.ContextFormation IntrinsicRelator.rules context)
    (typed : FormationSensitive.CtxMor IntrinsicRelator.rules contextAPZS context substitution) :
    FormationSensitive.Judgment IntrinsicRelator.rules context
      (subst substitution nilIotaLeft) (subst substitution nilIotaResultType) ∧
    FormationSensitive.Judgment IntrinsicRelator.rules context
      (subst substitution nilIotaRight) (subst substitution nilIotaResultType) :=
  ⟨nilIota_judgments.1.substitute formed typed, nilIota_judgments.2.substitute formed typed⟩

theorem consIota_substitute {context : Tower.Ctx n}
    {substitution : Sub Tower.Head 6 n}
    (formed : FormationSensitive.ContextFormation IntrinsicRelator.rules context)
    (typed : FormationSensitive.CtxMor IntrinsicRelator.rules
      contextAPZSHeadTail context substitution) :
    FormationSensitive.Judgment IntrinsicRelator.rules context
      (subst substitution consIotaLeft) (subst substitution consIotaResultType) ∧
    FormationSensitive.Judgment IntrinsicRelator.rules context
      (subst substitution consIotaRight) (subst substitution consIotaResultType) :=
  ⟨consIota_judgments.1.substitute formed typed, consIota_judgments.2.substitute formed typed⟩

/-- The original informative generator is retained under substitution. -/
def nilIota_substitutedEvidence (substitution : Sub Tower.Head 4 n) :
    Intrinsic.IotaEvidence n
      (subst substitution nilIotaLeft) (subst substitution nilIotaRight) :=
  (Intrinsic.IotaEvidence.nil (.var 3) (.var 2) (.var 1) (.var 0)).substitute substitution

def consIota_substitutedEvidence (substitution : Sub Tower.Head 6 n) :
    Intrinsic.IotaEvidence n
      (subst substitution consIotaLeft) (subst substitution consIotaRight) :=
  (Intrinsic.IotaEvidence.cons (.var 5) (.var 4) (.var 3) (.var 2)
    (.var 1) (.var 0)).substitute substitution

theorem nilIota_substitutedRoot (substitution : Sub Tower.Head 4 n) :
    IntrinsicRelator.rules.computation.step
      (subst substitution nilIotaLeft) (subst substitution nilIotaRight) :=
  .declared ⟨.list (nilIota_substitutedEvidence substitution)⟩

theorem consIota_substitutedRoot (substitution : Sub Tower.Head 6 n) :
    IntrinsicRelator.rules.computation.step
      (subst substitution consIotaLeft) (subst substitution consIotaRight) :=
  .declared ⟨.list (consIota_substitutedEvidence substitution)⟩

#print axioms eliminateType_hasType
#print axioms nilIota_judgments
#print axioms consIota_judgments
#print axioms nilIota_substitute
#print axioms consIota_substitute
#print axioms nilIota_substitutedRoot
#print axioms consIota_substitutedRoot

end FormationSensitiveNativeListElimination
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
