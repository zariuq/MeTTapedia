import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveRegularity
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.IntrinsicNativeListRelator

/-!
# Formation-sensitive native List and mapRel constructors

The actual combined List/mapRel declaration environment is retained. Each
used constant has a closed formation certificate in the refined judgment.
These certificates and applications do not authorize arbitrary eliminator
equations, normalization, or the entire declaration signature.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FormationSensitiveNativeList

open Presentation Presentation.Declaration Presentation.SchemaElaboration
open NativeIndexedFamilies RussellTarski
open IntrinsicRelator

variable {n : Nat}

abbrev Typing (context : Tower.Ctx n) (term type : Tower.Tm n) : Prop :=
  FormationSensitive.Typing IntrinsicRelator.rules context term type

section ListDeclarations

open Intrinsic

theorem listType_hasType :
    Typing (.nil : Tower.Ctx 0) listType
      (sortTm listDeclarationLevel) := by
  unfold listType listDeclarationLevel
  apply FormationSensitive.Typing.piForm
  · exact .headType (.sort elementLevel)
  · exact .sort (.succ elementLevel)
  · exact .headType (.sort elementLevel)
  · exact .sort (.succ elementLevel)
  · exact .sorts (.succ elementLevel) (.succ elementLevel)

theorem listConstant_hasType {context : Tower.Ctx n} :
    Typing context (.const listName) (liftClosed listType) := by
  apply FormationSensitive.Typing.const (u := .sort listDeclarationLevel)
  · decide
  · exact listType_hasType
  · exact .sort listDeclarationLevel

theorem listApp_hasType {context : Tower.Ctx n} {element : Tower.Tm n}
    (elementTyping : Typing context element
      (sortTm Intrinsic.elementLevel)) :
    Typing context (Intrinsic.listApp element)
      (sortTm Intrinsic.elementLevel) := by
  have listTyping : Typing context (.const Intrinsic.listName)
      (liftClosed Intrinsic.listType) :=
    listConstant_hasType
  have application := FormationSensitive.Typing.appElim listTyping elementTyping
  simpa [Intrinsic.listType, Intrinsic.listApp, liftClosed, sortTm,
    Presentation.rename, Presentation.inst0, Presentation.subst] using
    application

theorem nilType_hasType :
    Typing (.nil : Tower.Ctx 0) nilType
      (sortTm nilDeclarationLevel) := by
  unfold nilType nilDeclarationLevel
  apply FormationSensitive.Typing.piForm
  · exact .headType (.sort elementLevel)
  · exact .sort (.succ elementLevel)
  · apply listApp_hasType
    exact FormationSensitive.Typing.var 0
  · exact .sort elementLevel
  · exact .sorts (.succ elementLevel) elementLevel

theorem nilConstant_hasType {context : Tower.Ctx n} :
    Typing context (.const nilName) (liftClosed nilType) := by
  apply FormationSensitive.Typing.const (u := .sort nilDeclarationLevel)
  · decide
  · exact nilType_hasType
  · exact .sort nilDeclarationLevel

theorem nilApp_hasType {context : Tower.Ctx n} {element : Tower.Tm n}
    (elementTyping : Typing context element
      (sortTm Intrinsic.elementLevel)) :
    Typing context (Intrinsic.nilApp element)
      (Intrinsic.listApp element) := by
  have nilTyping : Typing context (.const Intrinsic.nilName)
      (liftClosed Intrinsic.nilType) :=
    nilConstant_hasType
  have application := FormationSensitive.Typing.appElim nilTyping elementTyping
  simpa [Intrinsic.nilType, Intrinsic.nilApp, Intrinsic.listApp, liftClosed,
    sortTm, Presentation.rename, Presentation.inst0, Presentation.subst,
    Presentation.subst0, Presentation.liftRen, Presentation.liftSub] using
    application

theorem consBodyType_hasType :
    Typing (.snoc (.nil : Tower.Ctx 0) (sortTm elementLevel))
      consBodyType (sortTm consBodyLevel) := by
  unfold consBodyType consBodyLevel
  apply FormationSensitive.Typing.piForm
  · exact FormationSensitive.Typing.var 0
  · exact .sort elementLevel
  · apply FormationSensitive.Typing.piForm
    · apply listApp_hasType
      exact FormationSensitive.Typing.var 1
    · exact .sort elementLevel
    · apply listApp_hasType
      exact FormationSensitive.Typing.var 2
    · exact .sort elementLevel
    · exact .sorts elementLevel elementLevel
  · exact .sort (.max elementLevel elementLevel)
  · exact .sorts elementLevel (.max elementLevel elementLevel)

theorem consType_hasType :
    Typing (.nil : Tower.Ctx 0) consType
      (sortTm consDeclarationLevel) := by
  unfold consType consDeclarationLevel
  apply FormationSensitive.Typing.piForm
  · exact .headType (.sort elementLevel)
  · exact .sort (.succ elementLevel)
  · exact consBodyType_hasType
  · exact .sort consBodyLevel
  · exact .sorts (.succ elementLevel) consBodyLevel

theorem consConstant_hasType {context : Tower.Ctx n} :
    Typing context (.const consName) (liftClosed consType) := by
  apply FormationSensitive.Typing.const (u := .sort consDeclarationLevel)
  · decide
  · exact consType_hasType
  · exact .sort consDeclarationLevel

theorem consApp_hasType {context : Tower.Ctx n}
    {element head tail : Tower.Tm n}
    (elementTyping : Typing context element
      (sortTm Intrinsic.elementLevel))
    (headTyping : Typing context head element)
    (tailTyping : Typing context tail (Intrinsic.listApp element)) :
    Typing context (Intrinsic.consApp element head tail)
      (Intrinsic.listApp element) := by
  have consBodyAsArrows :
      Intrinsic.consBodyType =
        arrow (.var 0)
          (arrow (Intrinsic.listApp (.var 0))
            (Intrinsic.listApp (.var 0))) := by
    decide
  have consTyping : Typing context (.const Intrinsic.consName)
      (liftClosed Intrinsic.consType) :=
    consConstant_hasType
  have first := FormationSensitive.Typing.appElim consTyping elementTyping
  have firstNormalized :
      Typing context
        (.app (.const Intrinsic.consName) element)
        (arrow element
          (arrow (Intrinsic.listApp element)
            (Intrinsic.listApp element))) := by
    simpa [Intrinsic.consType, consBodyAsArrows, liftClosed,
      Presentation.inst0, Presentation.subst0] using first
  have second := FormationSensitive.Typing.appElim firstNormalized headTyping
  have secondNormalized :
      Typing context
        (.app (.app (.const Intrinsic.consName) element) head)
        (arrow (Intrinsic.listApp element)
          (Intrinsic.listApp element)) := by
    simpa only [Presentation.inst0_rename_wk] using second
  have third := FormationSensitive.Typing.appElim secondNormalized tailTyping
  simpa only [Intrinsic.consApp, arrow,
    Presentation.inst0_rename_wk] using third

end ListDeclarations

theorem relationApp_hasType {context : Tower.Ctx n}
    {source target relation sourceTerm targetTerm : Tower.Tm n}
    (relationTyping : Typing context relation
      (.pi source (.pi (Presentation.rename wk target)
        (sortTm Intrinsic.motiveLevel))))
    (sourceTermTyping : Typing context sourceTerm source)
    (targetTermTyping : Typing context targetTerm target) :
    Typing context (.app (.app relation sourceTerm) targetTerm)
      (sortTm Intrinsic.motiveLevel) := by
  have afterSource := FormationSensitive.Typing.appElim relationTyping
    sourceTermTyping
  have afterSourceNormalized :
      Typing context (.app relation sourceTerm)
        (.pi target (sortTm Intrinsic.motiveLevel)) := by
    have targetInstantiation :
        Presentation.inst0 sourceTerm
            (.pi (Presentation.rename wk target)
              (sortTm Intrinsic.motiveLevel)) =
          .pi target (sortTm Intrinsic.motiveLevel) := by
      simp [Presentation.inst0, sortTm, Presentation.subst]
      exact Presentation.inst0_rename_wk sourceTerm target
    rw [targetInstantiation] at afterSource
    exact afterSource
  have afterTarget := FormationSensitive.Typing.appElim afterSourceNormalized
    targetTermTyping
  change Typing context (.app (.app relation sourceTerm) targetTerm)
    (Presentation.inst0 targetTerm (sortTm Intrinsic.motiveLevel))
    at afterTarget
  simpa [Presentation.inst0, sortTm, Presentation.subst] using afterTarget

theorem relationType_hasType :
    Typing contextAB relationType (sortTm relationTypeLevel) := by
  unfold relationType relationTypeLevel contextAB contextA
  apply FormationSensitive.Typing.piForm
  · exact FormationSensitive.Typing.var 1
  · exact .sort Intrinsic.elementLevel
  · apply FormationSensitive.Typing.piForm
    · exact FormationSensitive.Typing.var 1
    · exact .sort Intrinsic.elementLevel
    · exact .headType (.sort Intrinsic.motiveLevel)
    · exact .sort (.succ Intrinsic.motiveLevel)
    · exact .sorts Intrinsic.elementLevel (.succ Intrinsic.motiveLevel)
  · exact .sort
      (.max Intrinsic.elementLevel (.succ Intrinsic.motiveLevel))
  · exact .sorts Intrinsic.elementLevel
      (.max Intrinsic.elementLevel (.succ Intrinsic.motiveLevel))

theorem mapRelType_hasType :
    Typing (.nil : Tower.Ctx 0) mapRelType
      (sortTm familyDeclarationLevel) := by
  unfold mapRelType mapRelIndexType familyDeclarationLevel familyAfterTargetLevel
    familyAfterRelationLevel familyIndicesLevel
  apply FormationSensitive.Typing.piForm
  · exact .headType (.sort Intrinsic.elementLevel)
  · exact .sort (.succ Intrinsic.elementLevel)
  · apply FormationSensitive.Typing.piForm
    · exact .headType (.sort Intrinsic.elementLevel)
    · exact .sort (.succ Intrinsic.elementLevel)
    · apply FormationSensitive.Typing.piForm
      · exact relationType_hasType
      · exact .sort relationTypeLevel
      · apply FormationSensitive.Typing.piForm
        · apply listApp_hasType
          exact FormationSensitive.Typing.var 2
        · exact .sort Intrinsic.elementLevel
        · apply FormationSensitive.Typing.piForm
          · apply listApp_hasType
            exact FormationSensitive.Typing.var 2
          · exact .sort Intrinsic.elementLevel
          · exact .headType (.sort Intrinsic.motiveLevel)
          · exact .sort (.succ Intrinsic.motiveLevel)
          · exact .sorts Intrinsic.elementLevel
              (.succ Intrinsic.motiveLevel)
        · exact .sort
            (.max Intrinsic.elementLevel (.succ Intrinsic.motiveLevel))
        · exact .sorts Intrinsic.elementLevel
            (.max Intrinsic.elementLevel (.succ Intrinsic.motiveLevel))
      · exact .sort familyIndicesLevel
      · exact .sorts relationTypeLevel familyIndicesLevel
    · exact .sort familyAfterRelationLevel
    · exact .sorts (.succ Intrinsic.elementLevel)
        familyAfterRelationLevel
  · exact .sort familyAfterTargetLevel
  · exact .sorts (.succ Intrinsic.elementLevel) familyAfterTargetLevel

theorem mapRelConstant_hasType {context : Tower.Ctx n} :
    Typing context (.const mapRelName) (liftClosed mapRelType) := by
  apply FormationSensitive.Typing.const (u := .sort familyDeclarationLevel)
  · decide
  · exact mapRelType_hasType
  · exact .sort familyDeclarationLevel

theorem mapRelApp_hasType {context : Tower.Ctx n}
    {source target relation sourceList targetList : Tower.Tm n}
    (sourceTyping : Typing context source
      (sortTm Intrinsic.elementLevel))
    (targetTyping : Typing context target
      (sortTm Intrinsic.elementLevel))
    (relationTyping : Typing context relation
      (.pi source (.pi (Presentation.rename wk target)
        (sortTm Intrinsic.motiveLevel))))
    (sourceListTyping : Typing context sourceList
      (Intrinsic.listApp source))
    (targetListTyping : Typing context targetList
      (Intrinsic.listApp target)) :
    Typing context
      (mapRelApp source target relation sourceList targetList)
      (sortTm Intrinsic.motiveLevel) := by
  have afterSource := FormationSensitive.Typing.appElim
    (mapRelConstant_hasType (context := context)) sourceTyping
  have afterTarget := FormationSensitive.Typing.appElim afterSource targetTyping
  have relationTypingExpected :
      Typing context relation
        (Presentation.subst (subst0 target)
          (Presentation.subst (liftSub (subst0 source))
            (Presentation.rename (liftRen (liftRen Fin.elim0))
              relationType))) := by
    rw [instantiateTwo_relationType]
    exact relationTyping
  have afterRelation := FormationSensitive.Typing.appElim afterTarget
    relationTypingExpected
  change Typing context _
    (Presentation.subst (subst0 relation)
      (Presentation.subst (liftSub (subst0 target))
        (Presentation.subst (liftSub (liftSub (subst0 source)))
          (Presentation.rename
            (liftRen (liftRen (liftRen Fin.elim0)))
            mapRelIndexType)))) at afterRelation
  rw [instantiateThree_mapRelIndexType source target relation]
    at afterRelation
  have afterSourceList := FormationSensitive.Typing.appElim afterRelation
    sourceListTyping
  have targetBinderInstantiation :
      Presentation.inst0 sourceList
          (.pi (Intrinsic.listApp (Presentation.rename wk target))
            (sortTm Intrinsic.motiveLevel)) =
        .pi (Intrinsic.listApp target)
          (sortTm Intrinsic.motiveLevel) := by
    simp [Presentation.inst0, Intrinsic.listApp, sortTm,
      Presentation.subst]
    exact Presentation.inst0_rename_wk sourceList target
  rw [targetBinderInstantiation] at afterSourceList
  have afterSourceListNormalized :
      Typing context
        (.app
          (.app
            (.app
              (.app (.const mapRelName) source)
              target)
            relation)
          sourceList)
        (.pi (Intrinsic.listApp target)
          (sortTm Intrinsic.motiveLevel)) := by
    simpa only [Presentation.inst0_rename_wk] using afterSourceList
  have afterTargetList := FormationSensitive.Typing.appElim
    afterSourceListNormalized
    targetListTyping
  have resultInstantiation :
      Presentation.inst0 targetList (sortTm Intrinsic.motiveLevel) =
        sortTm Intrinsic.motiveLevel := by
    rfl
  rw [resultInstantiation] at afterTargetList
  exact afterTargetList

theorem nilRelType_hasType :
    Typing (.nil : Tower.Ctx 0) nilRelType
      (sortTm nilRelDeclarationLevel) := by
  unfold nilRelType nilRelDeclarationLevel nilRelAfterTargetLevel
    nilRelAfterRelationLevel
  apply FormationSensitive.Typing.piForm
  · exact .headType (.sort Intrinsic.elementLevel)
  · exact .sort (.succ Intrinsic.elementLevel)
  · apply FormationSensitive.Typing.piForm
    · exact .headType (.sort Intrinsic.elementLevel)
    · exact .sort (.succ Intrinsic.elementLevel)
    · apply FormationSensitive.Typing.piForm
      · exact relationType_hasType
      · exact .sort relationTypeLevel
      · apply mapRelApp_hasType
        · exact FormationSensitive.Typing.var 2
        · exact FormationSensitive.Typing.var 1
        · exact FormationSensitive.Typing.var 0
        · apply nilApp_hasType
          exact FormationSensitive.Typing.var 2
        · apply nilApp_hasType
          exact FormationSensitive.Typing.var 1
      · exact .sort Intrinsic.motiveLevel
      · exact .sorts relationTypeLevel Intrinsic.motiveLevel
    · exact .sort nilRelAfterRelationLevel
    · exact .sorts (.succ Intrinsic.elementLevel)
        nilRelAfterRelationLevel
  · exact .sort nilRelAfterTargetLevel
  · exact .sorts (.succ Intrinsic.elementLevel) nilRelAfterTargetLevel

theorem nilRelConstant_hasType {context : Tower.Ctx n} :
    Typing context (.const nilRelName) (liftClosed nilRelType) := by
  apply FormationSensitive.Typing.const (u := .sort nilRelDeclarationLevel)
  · decide
  · exact nilRelType_hasType
  · exact .sort nilRelDeclarationLevel

theorem nilRelApp_hasType {context : Tower.Ctx n}
    {source target relation : Tower.Tm n}
    (sourceTyping : Typing context source
      (sortTm Intrinsic.elementLevel))
    (targetTyping : Typing context target
      (sortTm Intrinsic.elementLevel))
    (relationTyping : Typing context relation
      (.pi source (.pi (Presentation.rename wk target)
        (sortTm Intrinsic.motiveLevel)))) :
    Typing context (nilRelApp source target relation)
      (mapRelApp source target relation
        (Intrinsic.nilApp source) (Intrinsic.nilApp target)) := by
  have afterSource := FormationSensitive.Typing.appElim
    (nilRelConstant_hasType (context := context)) sourceTyping
  have afterTarget := FormationSensitive.Typing.appElim afterSource targetTyping
  have relationTypingExpected :
      Typing context relation
        (Presentation.subst (subst0 target)
          (Presentation.subst (liftSub (subst0 source))
            (Presentation.rename (liftRen (liftRen Fin.elim0))
              relationType))) := by
    rw [instantiateTwo_relationType]
    exact relationTyping
  have afterRelation := FormationSensitive.Typing.appElim afterTarget
    relationTypingExpected
  change Typing context _
    (Presentation.subst (subst0 relation)
      (Presentation.subst (liftSub (subst0 target))
        (Presentation.subst (liftSub (liftSub (subst0 source)))
          (Presentation.rename
            (liftRen (liftRen (liftRen Fin.elim0)))
            nilRelBodyType)))) at afterRelation
  rw [instantiateThree_nilRelBodyType source target relation]
    at afterRelation
  exact afterRelation

theorem consRelBodyType_hasType :
    Typing contextABR consRelBodyType (sortTm consRelBodyLevel) := by
  unfold consRelBodyType consRelBodyLevel consRelAfterTargetHeadLevel
    consRelAfterSourceTailLevel consRelAfterTargetTailLevel
    consRelAfterHeadEvidenceLevel consRelAfterTailEvidenceLevel
  apply FormationSensitive.Typing.piForm
  · exact FormationSensitive.Typing.var 2
  · exact .sort Intrinsic.elementLevel
  · apply FormationSensitive.Typing.piForm
    · exact FormationSensitive.Typing.var 2
    · exact .sort Intrinsic.elementLevel
    · apply FormationSensitive.Typing.piForm
      · apply listApp_hasType
        exact FormationSensitive.Typing.var 4
      · exact .sort Intrinsic.elementLevel
      · apply FormationSensitive.Typing.piForm
        · apply listApp_hasType
          exact FormationSensitive.Typing.var 4
        · exact .sort Intrinsic.elementLevel
        · apply FormationSensitive.Typing.piForm
          · apply relationApp_hasType
              (source := (.var 6 : Tower.Tm 7))
              (target := .var 5) (relation := .var 4)
              (sourceTerm := .var 3) (targetTerm := .var 2)
            · exact FormationSensitive.Typing.var 4
            · exact FormationSensitive.Typing.var 3
            · exact FormationSensitive.Typing.var 2
          · exact .sort Intrinsic.motiveLevel
          · apply FormationSensitive.Typing.piForm
            · apply mapRelApp_hasType
              · exact FormationSensitive.Typing.var 7
              · exact FormationSensitive.Typing.var 6
              · exact FormationSensitive.Typing.var 5
              · exact FormationSensitive.Typing.var 2
              · exact FormationSensitive.Typing.var 1
            · exact .sort Intrinsic.motiveLevel
            · apply mapRelApp_hasType
              · exact FormationSensitive.Typing.var 8
              · exact FormationSensitive.Typing.var 7
              · exact FormationSensitive.Typing.var 6
              · apply consApp_hasType
                · exact FormationSensitive.Typing.var 8
                · exact FormationSensitive.Typing.var 5
                · exact FormationSensitive.Typing.var 3
              · apply consApp_hasType
                · exact FormationSensitive.Typing.var 7
                · exact FormationSensitive.Typing.var 4
                · exact FormationSensitive.Typing.var 2
            · exact .sort Intrinsic.motiveLevel
            · exact .sorts Intrinsic.motiveLevel
                Intrinsic.motiveLevel
          · exact .sort consRelAfterTailEvidenceLevel
          · exact .sorts Intrinsic.motiveLevel
              consRelAfterTailEvidenceLevel
        · exact .sort consRelAfterHeadEvidenceLevel
        · exact .sorts Intrinsic.elementLevel
            consRelAfterHeadEvidenceLevel
      · exact .sort consRelAfterTargetTailLevel
      · exact .sorts Intrinsic.elementLevel
          consRelAfterTargetTailLevel
    · exact .sort consRelAfterSourceTailLevel
    · exact .sorts Intrinsic.elementLevel consRelAfterSourceTailLevel
  · exact .sort consRelAfterTargetHeadLevel
  · exact .sorts Intrinsic.elementLevel consRelAfterTargetHeadLevel

theorem consRelType_hasType :
    Typing (.nil : Tower.Ctx 0) consRelType
      (sortTm consRelDeclarationLevel) := by
  unfold consRelType consRelDeclarationLevel consRelAfterOuterTargetLevel
    consRelAfterRelationLevel
  apply FormationSensitive.Typing.piForm
  · exact .headType (.sort Intrinsic.elementLevel)
  · exact .sort (.succ Intrinsic.elementLevel)
  · apply FormationSensitive.Typing.piForm
    · exact .headType (.sort Intrinsic.elementLevel)
    · exact .sort (.succ Intrinsic.elementLevel)
    · apply FormationSensitive.Typing.piForm
      · exact relationType_hasType
      · exact .sort relationTypeLevel
      · exact consRelBodyType_hasType
      · exact .sort consRelBodyLevel
      · exact .sorts relationTypeLevel consRelBodyLevel
    · exact .sort consRelAfterRelationLevel
    · exact .sorts (.succ Intrinsic.elementLevel)
        consRelAfterRelationLevel
  · exact .sort consRelAfterOuterTargetLevel
  · exact .sorts (.succ Intrinsic.elementLevel)
      consRelAfterOuterTargetLevel

theorem consRelConstant_hasType {context : Tower.Ctx n} :
    Typing context (.const consRelName) (liftClosed consRelType) := by
  apply FormationSensitive.Typing.const (u := .sort consRelDeclarationLevel)
  · decide
  · exact consRelType_hasType
  · exact .sort consRelDeclarationLevel

theorem consRelApp_hasType {context : Tower.Ctx n}
    {source target relation sourceHead targetHead sourceTail targetTail
      headEvidence tailEvidence : Tower.Tm n}
    (sourceTyping : Typing context source
      (sortTm Intrinsic.elementLevel))
    (targetTyping : Typing context target
      (sortTm Intrinsic.elementLevel))
    (relationTyping : Typing context relation
      (.pi source (.pi (Presentation.rename wk target)
        (sortTm Intrinsic.motiveLevel))))
    (sourceHeadTyping : Typing context sourceHead source)
    (targetHeadTyping : Typing context targetHead target)
    (sourceTailTyping : Typing context sourceTail
      (Intrinsic.listApp source))
    (targetTailTyping : Typing context targetTail
      (Intrinsic.listApp target))
    (headEvidenceTyping : Typing context headEvidence
      (.app (.app relation sourceHead) targetHead))
    (tailEvidenceTyping : Typing context tailEvidence
      (mapRelApp source target relation sourceTail targetTail)) :
    Typing context
      (consRelApp source target relation sourceHead targetHead sourceTail
        targetTail headEvidence tailEvidence)
      (mapRelApp source target relation
        (Intrinsic.consApp source sourceHead sourceTail)
        (Intrinsic.consApp target targetHead targetTail)) := by
  have afterSource := FormationSensitive.Typing.appElim
    (consRelConstant_hasType (context := context)) sourceTyping
  have afterTarget := FormationSensitive.Typing.appElim afterSource targetTyping
  have relationTypingExpected :
      Typing context relation
        (Presentation.subst (subst0 target)
          (Presentation.subst (liftSub (subst0 source))
            (Presentation.rename (liftRen (liftRen Fin.elim0))
              relationType))) := by
    rw [instantiateTwo_relationType]
    exact relationTyping
  have afterRelation := FormationSensitive.Typing.appElim afterTarget
    relationTypingExpected
  change Typing context _
    (Presentation.subst (subst0 relation)
      (Presentation.subst (liftSub (subst0 target))
        (Presentation.subst (liftSub (liftSub (subst0 source)))
          (Presentation.rename
            (liftRen (liftRen (liftRen Fin.elim0)))
            consRelBodyType)))) at afterRelation
  rw [instantiateThree_consRelBodyType source target relation]
    at afterRelation
  have afterSourceHead := FormationSensitive.Typing.appElim afterRelation
    sourceHeadTyping
  have targetHeadTypingExpected :
      Typing context targetHead
        (Presentation.inst0 sourceHead (weaken1 target)) := by
    rw [weaken1, Presentation.inst0_rename_wk]
    exact targetHeadTyping
  have afterTargetHead := FormationSensitive.Typing.appElim afterSourceHead
    targetHeadTypingExpected
  have sourceTailTypingExpected :
      Typing context sourceTail
        (Presentation.subst (subst0 targetHead)
          (Presentation.subst (liftSub (subst0 sourceHead))
            (Intrinsic.listApp (weaken2 source)))) := by
    change Typing context sourceTail
      (Presentation.subst (subst0 targetHead)
        (Presentation.subst (liftSub (subst0 sourceHead))
          (weaken2 (Intrinsic.listApp source))))
    rw [instantiateTwo_weaken2]
    exact sourceTailTyping
  have afterSourceTail := FormationSensitive.Typing.appElim afterTargetHead
    sourceTailTypingExpected
  have targetTailTypingExpected :
      Typing context targetTail
        (Presentation.subst (subst0 sourceTail)
          (Presentation.subst (liftSub (subst0 targetHead))
            (Presentation.subst (liftSub (liftSub (subst0 sourceHead)))
              (Intrinsic.listApp (weaken3 target))))) := by
    change Typing context targetTail
      (Presentation.subst (subst0 sourceTail)
        (Presentation.subst (liftSub (subst0 targetHead))
          (Presentation.subst (liftSub (liftSub (subst0 sourceHead)))
            (weaken3 (Intrinsic.listApp target)))))
    rw [instantiateThree_weaken3]
    exact targetTailTyping
  have afterTargetTail := FormationSensitive.Typing.appElim afterSourceTail
    targetTailTypingExpected
  have headEvidenceTypingExpected :
      Typing context headEvidence
        (Presentation.subst (subst0 targetTail)
          (Presentation.subst (liftSub (subst0 sourceTail))
            (Presentation.subst (liftSub (liftSub (subst0 targetHead)))
              (Presentation.subst
                (liftSub (liftSub (liftSub (subst0 sourceHead))))
                (.app (.app (weaken4 relation) (.var 3)) (.var 2)))))) := by
    rw [instantiateFour_headRelation]
    exact headEvidenceTyping
  have afterHeadEvidence := FormationSensitive.Typing.appElim afterTargetTail
    headEvidenceTypingExpected
  have tailEvidenceTypingExpected :
      Typing context tailEvidence
        (instantiateFive sourceHead targetHead sourceTail targetTail
          headEvidence
          (mapRelApp (weaken5 source) (weaken5 target) (weaken5 relation)
            (.var 2) (.var 1))) := by
    rw [instantiateFive_mapRelTail]
    exact tailEvidenceTyping
  have afterTailEvidence := FormationSensitive.Typing.appElim afterHeadEvidence
    tailEvidenceTypingExpected
  change Typing context _
    (instantiateSix sourceHead targetHead sourceTail targetTail headEvidence
      tailEvidence
      (mapRelApp (weaken6 source) (weaken6 target) (weaken6 relation)
        (Intrinsic.consApp (weaken6 source) (.var 5) (.var 3))
        (Intrinsic.consApp (weaken6 target) (.var 4) (.var 2))))
    at afterTailEvidence
  rw [instantiateSix_consResult] at afterTailEvidence
  exact afterTailEvidence

#print axioms listType_hasType
#print axioms nilType_hasType
#print axioms consType_hasType
#print axioms mapRelType_hasType
#print axioms nilRelType_hasType
#print axioms consRelType_hasType
#print axioms consApp_hasType
#print axioms consRelApp_hasType

end FormationSensitiveNativeList
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
