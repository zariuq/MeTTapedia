import Mettapedia.Languages.MeTTa.PureKernel.Universe.IntrinsicNativeListMaps

/-!
# Intrinsic proof-relevant List relator

This module presents `mapRel` as a native strictly-positive indexed family.
Its three parameters are a source type, a target type, and a proof-relevant
relation; its two indices are the source and target Lists.  Consequently a
family inhabitant retains one relation witness per pair of heads and one
recursive witness per pair of tails.

The semantic polynomial relator remains the interpretation target.  The
declaration below supplies the object-language syntax and positivity evidence
without identifying relational evidence with Boolean support.  A semantic-CwF
interpretation of raw Prime syntax is not constructed here, so this module does
not yet identify the intrinsic declaration with that target by model adequacy.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe
namespace NativeIndexedFamilies
namespace IntrinsicRelator

open Presentation
open Presentation.SchemaElaboration
open Presentation.Declaration
open Presentation.Declaration.IndexedFamily
open Presentation.Declaration.ComputationAuthority
open RussellTarski

/-! ## Family and constructor syntax -/

def mapRelName : DeclName := `Prime.List.mapRel
def nilRelName : DeclName := `Prime.List.mapRel.nil
def consRelName : DeclName := `Prime.List.mapRel.cons
def eliminateName : DeclName := `Prime.List.mapRel.eliminate

/-- In context `A,B`, a proof-relevant relation has type
`Pi a : A, Pi b : B, U rho`. -/
def relationType : Tower.Tm 2 :=
  .pi (.var 1) (.pi (.var 1) (sortTm Intrinsic.motiveLevel))

def mapRelApp (source target relation sourceList targetList : Tower.Tm n) :
    Tower.Tm n :=
  .app
    (.app
      (.app
        (.app
          (.app (.const mapRelName) source)
          target)
        relation)
      sourceList)
    targetList

/-- `mapRel : Pi A B (R : A -> B -> U rho), List A -> List B -> U rho`. -/
def mapRelIndexType : Tower.Tm 3 :=
  .pi (Intrinsic.listApp (.var 2))
    (.pi (Intrinsic.listApp (.var 2))
      (sortTm Intrinsic.motiveLevel))

def mapRelType : Tower.Tm 0 :=
  .pi (sortTm Intrinsic.elementLevel)
    (.pi (sortTm Intrinsic.elementLevel)
      (.pi relationType mapRelIndexType))

def nilRelApp (source target relation : Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app (.const nilRelName) source)
      target)
    relation

/-- The empty Lists are related without erasing the chosen relation
parameter. -/
def nilRelBodyType : Tower.Tm 3 :=
  mapRelApp (.var 2) (.var 1) (.var 0)
    (Intrinsic.nilApp (.var 2)) (Intrinsic.nilApp (.var 1))

def nilRelType : Tower.Tm 0 :=
  .pi (sortTm Intrinsic.elementLevel)
    (.pi (sortTm Intrinsic.elementLevel)
      (.pi relationType nilRelBodyType))

def consRelApp (source target relation sourceHead targetHead sourceTail
    targetTail headEvidence tailEvidence : Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app
        (.app
          (.app
            (.app
              (.app
                (.app
                  (.app (.const consRelName) source)
                  target)
                relation)
              sourceHead)
            targetHead)
          sourceTail)
        targetTail)
      headEvidence)
    tailEvidence

/-- Below `A,B,R`, the cons constructor retains both the head-relation
witness and the recursive tail witness. -/
def consRelBodyType : Tower.Tm 3 :=
  .pi (.var 2)
    (.pi (.var 2)
      (.pi (Intrinsic.listApp (.var 4))
        (.pi (Intrinsic.listApp (.var 4))
          (.pi (.app (.app (.var 4) (.var 3)) (.var 2))
            (.pi
              (mapRelApp (.var 7) (.var 6) (.var 5)
                (.var 2) (.var 1))
              (mapRelApp (.var 8) (.var 7) (.var 6)
                (Intrinsic.consApp (.var 8) (.var 5) (.var 3))
                (Intrinsic.consApp (.var 7) (.var 4) (.var 2))))))))

def consRelType : Tower.Tm 0 :=
  .pi (sortTm Intrinsic.elementLevel)
    (.pi (sortTm Intrinsic.elementLevel)
      (.pi relationType consRelBodyType))

/-! ## Dependent elimination -/

def eliminationLevel : LevelExpr := .param 2

/-- In context `A,B,R`, motives depend on both List indices and on the exact
proof-relevant `mapRel` inhabitant. -/
def motiveType : Tower.Tm 3 :=
  .pi (Intrinsic.listApp (.var 2))
    (.pi (Intrinsic.listApp (.var 2))
      (.pi
        (mapRelApp (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))
        (sortTm eliminationLevel)))

def motiveApp (motive sourceList targetList evidence : Tower.Tm n) :
    Tower.Tm n :=
  .app (.app (.app motive sourceList) targetList) evidence

/-- In context `A,B,R,P`, the empty branch targets the exact `nilRel`
inhabitant. -/
def nilCaseType : Tower.Tm 4 :=
  motiveApp (.var 0)
    (Intrinsic.nilApp (.var 3))
    (Intrinsic.nilApp (.var 2))
    (nilRelApp (.var 3) (.var 2) (.var 1))

/-- In context `A,B,R,P,z`, the cons branch receives the head witness, the
tail witness, and a recursive motive witness before producing the motive at
the constructed Lists and constructed relational evidence. -/
def consCaseType : Tower.Tm 5 :=
  .pi (.var 4)
    (.pi (.var 4)
      (.pi (Intrinsic.listApp (.var 6))
        (.pi (Intrinsic.listApp (.var 6))
          (.pi (.app (.app (.var 6) (.var 3)) (.var 2))
            (.pi
              (mapRelApp (.var 9) (.var 8) (.var 7)
                (.var 2) (.var 1))
              (.pi
                (motiveApp (.var 7) (.var 3) (.var 2) (.var 0))
                (motiveApp (.var 8)
                  (Intrinsic.consApp (.var 11) (.var 6) (.var 4))
                  (Intrinsic.consApp (.var 10) (.var 5) (.var 3))
                  (consRelApp (.var 11) (.var 10) (.var 9)
                    (.var 6) (.var 5) (.var 4) (.var 3)
                    (.var 2) (.var 1)))))))))

/-- In context `A,B,R,P,z,s`, dependent elimination covers every pair of
List indices and every retained `mapRel` derivation. -/
def eliminateResultType : Tower.Tm 6 :=
  .pi (Intrinsic.listApp (.var 5))
    (.pi (Intrinsic.listApp (.var 5))
      (.pi
        (mapRelApp (.var 7) (.var 6) (.var 5) (.var 1) (.var 0))
        (motiveApp (.var 5) (.var 2) (.var 1) (.var 0))))

def eliminateType : Tower.Tm 0 :=
  .pi (sortTm Intrinsic.elementLevel)
    (.pi (sortTm Intrinsic.elementLevel)
      (.pi relationType
        (.pi motiveType
          (.pi nilCaseType
            (.pi consCaseType eliminateResultType)))))

def eliminateApp (source target relation motive nilCase consCase sourceList
    targetList evidence : Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app
        (.app
          (.app
            (.app
              (.app
                (.app
                  (.app (.const eliminateName) source)
                  target)
                relation)
              motive)
            nilCase)
          consCase)
        sourceList)
      targetList)
    evidence

/-! ## Proof-relevant computation generators -/

inductive IotaEvidence (n : Nat) : Tower.Tm n → Tower.Tm n → Type where
  | nil (source target relation motive nilCase consCase : Tower.Tm n) :
      IotaEvidence n
        (eliminateApp source target relation motive nilCase consCase
          (Intrinsic.nilApp source) (Intrinsic.nilApp target)
          (nilRelApp source target relation))
        nilCase
  | cons (source target relation motive nilCase consCase sourceHead
      targetHead sourceTail targetTail headEvidence tailEvidence :
      Tower.Tm n) :
      IotaEvidence n
        (eliminateApp source target relation motive nilCase consCase
          (Intrinsic.consApp source sourceHead sourceTail)
          (Intrinsic.consApp target targetHead targetTail)
          (consRelApp source target relation sourceHead targetHead
            sourceTail targetTail headEvidence tailEvidence))
        (.app
          (.app
            (.app
              (.app
                (.app
                  (.app
                    (.app consCase sourceHead)
                    targetHead)
                  sourceTail)
                targetTail)
              headEvidence)
            tailEvidence)
          (eliminateApp source target relation motive nilCase consCase
            sourceTail targetTail tailEvidence))

def IotaEvidence.rename {left right : Tower.Tm n}
    (evidence : IotaEvidence n left right) (renameMap : Ren n m) :
    IotaEvidence m (Presentation.rename renameMap left)
      (Presentation.rename renameMap right) := by
  cases evidence with
  | nil => exact .nil _ _ _ _ _ _
  | cons => exact .cons _ _ _ _ _ _ _ _ _ _ _ _

def IotaEvidence.substitute {left right : Tower.Tm n}
    (evidence : IotaEvidence n left right)
    (substitution : Sub Tower.Head n m) :
    IotaEvidence m (Presentation.subst substitution left)
      (Presentation.subst substitution right) := by
  cases evidence with
  | nil => exact .nil _ _ _ _ _ _
  | cons => exact .cons _ _ _ _ _ _ _ _ _ _ _ _

def proofRelevantIotaComputation :
    ProofRelevantRootComputation Tower.Head where
  Evidence := IotaEvidence _
  rename := by
    intro n m renameMap left right evidence
    exact evidence.rename renameMap
  substitute := by
    intro n m substitution left right evidence
    exact evidence.substitute substitution

def iotaComputation : RootComputation Tower.Head :=
  proofRelevantIotaComputation.support

/-! ## Combined native declaration signature -/

/-- List and relational computation coexist without quotienting either
receipt family. -/
inductive CombinedIotaEvidence (n : Nat) :
    Tower.Tm n → Tower.Tm n → Type where
  | list {left right : Tower.Tm n} :
      Intrinsic.IotaEvidence n left right →
        CombinedIotaEvidence n left right
  | rel {left right : Tower.Tm n} :
      IotaEvidence n left right → CombinedIotaEvidence n left right

def CombinedIotaEvidence.rename {left right : Tower.Tm n}
    (evidence : CombinedIotaEvidence n left right) (renameMap : Ren n m) :
    CombinedIotaEvidence m (Presentation.rename renameMap left)
      (Presentation.rename renameMap right) := by
  cases evidence with
  | list evidence => exact .list (evidence.rename renameMap)
  | rel evidence => exact .rel (evidence.rename renameMap)

def CombinedIotaEvidence.substitute {left right : Tower.Tm n}
    (evidence : CombinedIotaEvidence n left right)
    (substitution : Sub Tower.Head n m) :
    CombinedIotaEvidence m (Presentation.subst substitution left)
      (Presentation.subst substitution right) := by
  cases evidence with
  | list evidence => exact .list (evidence.substitute substitution)
  | rel evidence => exact .rel (evidence.substitute substitution)

def combinedProofRelevantIotaComputation :
    ProofRelevantRootComputation Tower.Head where
  Evidence := CombinedIotaEvidence _
  rename := by
    intro n m renameMap left right evidence
    exact evidence.rename renameMap
  substitute := by
    intro n m substitution left right evidence
    exact evidence.substitute substitution

def mapRelEntry : Entry Tower.Head := { type := mapRelType }
def nilRelEntry : Entry Tower.Head := { type := nilRelType }
def consRelEntry : Entry Tower.Head := { type := consRelType }
def eliminateEntry : Entry Tower.Head := { type := eliminateType }

/-- The relational family extends the native List signature in place.  The
four new declarations are distinct; all pre-existing List entries remain
available with their original types. -/
def rawSignature : Signature Tower.Head where
  entries := fun name =>
    if name = mapRelName then some mapRelEntry
    else if name = nilRelName then some nilRelEntry
    else if name = consRelName then some consRelEntry
    else if name = eliminateName then some eliminateEntry
    else Intrinsic.rawSignature.entries name
  computation := combinedProofRelevantIotaComputation.support

abbrev rules : Rules Tower.Head :=
  extendRules Tower.rules rawSignature

@[simp] theorem typeOf_mapRel :
    rawSignature.typeOf? mapRelName = some mapRelType := by
  simp [rawSignature, Signature.typeOf?, mapRelEntry, mapRelName]

@[simp] theorem typeOf_nilRel :
    rawSignature.typeOf? nilRelName = some nilRelType := by
  simp [rawSignature, Signature.typeOf?, nilRelEntry, mapRelName, nilRelName]

@[simp] theorem typeOf_consRel :
    rawSignature.typeOf? consRelName = some consRelType := by
  simp [rawSignature, Signature.typeOf?, consRelEntry, mapRelName, nilRelName,
    consRelName]

@[simp] theorem typeOf_eliminate :
    rawSignature.typeOf? eliminateName = some eliminateType := by
  simp [rawSignature, Signature.typeOf?, eliminateEntry, mapRelName,
    nilRelName, consRelName, eliminateName]

@[simp] theorem intrinsicEntries_mapRel_none :
    Intrinsic.rawSignature.entries mapRelName = none := by
  simp [Intrinsic.rawSignature, Intrinsic.declarations, Signature.ofList,
    Signature.insert, Signature.empty, mapRelName,
    Intrinsic.listName, Intrinsic.nilName, Intrinsic.consName,
    Intrinsic.eliminateName, Intrinsic.identityEliminateName]

@[simp] theorem intrinsicEntries_nilRel_none :
    Intrinsic.rawSignature.entries nilRelName = none := by
  simp [Intrinsic.rawSignature, Intrinsic.declarations, Signature.ofList,
    Signature.insert, Signature.empty, nilRelName,
    Intrinsic.listName, Intrinsic.nilName, Intrinsic.consName,
    Intrinsic.eliminateName, Intrinsic.identityEliminateName]

@[simp] theorem intrinsicEntries_consRel_none :
    Intrinsic.rawSignature.entries consRelName = none := by
  simp [Intrinsic.rawSignature, Intrinsic.declarations, Signature.ofList,
    Signature.insert, Signature.empty, consRelName,
    Intrinsic.listName, Intrinsic.nilName, Intrinsic.consName,
    Intrinsic.eliminateName, Intrinsic.identityEliminateName]

@[simp] theorem intrinsicEntries_relEliminate_none :
    Intrinsic.rawSignature.entries eliminateName = none := by
  simp [Intrinsic.rawSignature, Intrinsic.declarations, Signature.ofList,
    Signature.insert, Signature.empty, eliminateName,
    Intrinsic.listName, Intrinsic.nilName, Intrinsic.consName,
    Intrinsic.eliminateName, Intrinsic.identityEliminateName]

def listSignatureExtension :
    Intrinsic.rawSignature.Extends rawSignature where
  entries := by
    intro name entry prior
    by_cases mapRel : name = mapRelName
    · subst name
      simp at prior
    by_cases nilRel : name = nilRelName
    · subst name
      simp at prior
    by_cases consRel : name = consRelName
    · subst name
      simp at prior
    by_cases relEliminate : name = eliminateName
    · subst name
      simp at prior
    simp [rawSignature, mapRel, nilRel, consRel, relEliminate, prior]
  computation := by
    intro n left right step
    rcases step with ⟨evidence⟩
    exact ⟨.list evidence⟩

def includeListTyping {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typing : Intrinsic.HasType context term type) :
    HasType rules context term type :=
  Presentation.Declaration.HasType.monoSignature Tower.rules
    listSignatureExtension typing

theorem listApp_hasType {context : Tower.Ctx n} {element : Tower.Tm n}
    (elementTyping : HasType rules context element
      (sortTm Intrinsic.elementLevel)) :
    HasType rules context (Intrinsic.listApp element)
      (sortTm Intrinsic.elementLevel) := by
  have listTyping : HasType rules context (.const Intrinsic.listName)
      (liftClosed Intrinsic.listType) :=
    includeListTyping (Intrinsic.listConstant_hasType (context := context))
  have application := Presentation.HasType.appElim listTyping elementTyping
  simpa [Intrinsic.listType, Intrinsic.listApp, liftClosed, sortTm,
    Presentation.rename, Presentation.inst0, Presentation.subst] using
    application

theorem nilApp_hasType {context : Tower.Ctx n} {element : Tower.Tm n}
    (elementTyping : HasType rules context element
      (sortTm Intrinsic.elementLevel)) :
    HasType rules context (Intrinsic.nilApp element)
      (Intrinsic.listApp element) := by
  have nilTyping : HasType rules context (.const Intrinsic.nilName)
      (liftClosed Intrinsic.nilType) :=
    includeListTyping (Intrinsic.nilConstant_hasType (context := context))
  have application := Presentation.HasType.appElim nilTyping elementTyping
  simpa [Intrinsic.nilType, Intrinsic.nilApp, Intrinsic.listApp, liftClosed,
    sortTm, Presentation.rename, Presentation.inst0, Presentation.subst,
    Presentation.subst0, Presentation.liftRen, Presentation.liftSub] using
    application

theorem consApp_hasType {context : Tower.Ctx n}
    {element head tail : Tower.Tm n}
    (elementTyping : HasType rules context element
      (sortTm Intrinsic.elementLevel))
    (headTyping : HasType rules context head element)
    (tailTyping : HasType rules context tail (Intrinsic.listApp element)) :
    HasType rules context (Intrinsic.consApp element head tail)
      (Intrinsic.listApp element) := by
  have consBodyAsArrows :
      Intrinsic.consBodyType =
        arrow (.var 0)
          (arrow (Intrinsic.listApp (.var 0))
            (Intrinsic.listApp (.var 0))) := by
    decide
  have consTyping : HasType rules context (.const Intrinsic.consName)
      (liftClosed Intrinsic.consType) :=
    includeListTyping (Intrinsic.consConstant_hasType (context := context))
  have first := Presentation.HasType.appElim consTyping elementTyping
  have firstNormalized :
      HasType rules context
        (.app (.const Intrinsic.consName) element)
        (arrow element
          (arrow (Intrinsic.listApp element)
            (Intrinsic.listApp element))) := by
    simpa [Intrinsic.consType, consBodyAsArrows, liftClosed,
      Presentation.inst0, Presentation.subst0] using first
  have second := Presentation.HasType.appElim firstNormalized headTyping
  have secondNormalized :
      HasType rules context
        (.app (.app (.const Intrinsic.consName) element) head)
        (arrow (Intrinsic.listApp element)
          (Intrinsic.listApp element)) := by
    simpa only [Presentation.inst0_rename_wk] using second
  have third := Presentation.HasType.appElim secondNormalized tailTyping
  simpa only [Intrinsic.consApp, arrow,
    Presentation.inst0_rename_wk] using third

theorem relationApp_hasType {context : Tower.Ctx n}
    {source target relation sourceTerm targetTerm : Tower.Tm n}
    (relationTyping : HasType rules context relation
      (.pi source (.pi (Presentation.rename wk target)
        (sortTm Intrinsic.motiveLevel))))
    (sourceTermTyping : HasType rules context sourceTerm source)
    (targetTermTyping : HasType rules context targetTerm target) :
    HasType rules context (.app (.app relation sourceTerm) targetTerm)
      (sortTm Intrinsic.motiveLevel) := by
  have afterSource := Presentation.HasType.appElim relationTyping
    sourceTermTyping
  have afterSourceNormalized :
      HasType rules context (.app relation sourceTerm)
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
  have afterTarget := Presentation.HasType.appElim afterSourceNormalized
    targetTermTyping
  change HasType rules context (.app (.app relation sourceTerm) targetTerm)
    (Presentation.inst0 targetTerm (sortTm Intrinsic.motiveLevel))
    at afterTarget
  simpa [Presentation.inst0, sortTm, Presentation.subst] using afterTarget

def contextA : Tower.Ctx 1 :=
  .snoc .nil (sortTm Intrinsic.elementLevel)

def contextAB : Tower.Ctx 2 :=
  .snoc contextA (sortTm Intrinsic.elementLevel)

def contextABR : Tower.Ctx 3 :=
  .snoc contextAB relationType

def contextABRXs : Tower.Ctx 4 :=
  .snoc contextABR (Intrinsic.listApp (.var 2))

def relationTypeLevel : LevelExpr :=
  .max Intrinsic.elementLevel
    (.max Intrinsic.elementLevel (.succ Intrinsic.motiveLevel))

theorem relationType_hasType :
    HasType rules contextAB relationType (sortTm relationTypeLevel) := by
  unfold relationType relationTypeLevel contextAB contextA
  apply Presentation.HasType.piForm
  · exact Presentation.HasType.var 1
  · exact .sort Intrinsic.elementLevel
  · apply Presentation.HasType.piForm
    · exact Presentation.HasType.var 1
    · exact .sort Intrinsic.elementLevel
    · exact .headType (.sort Intrinsic.motiveLevel)
    · exact .sort (.succ Intrinsic.motiveLevel)
    · exact .sorts Intrinsic.elementLevel (.succ Intrinsic.motiveLevel)
  · exact .sort
      (.max Intrinsic.elementLevel (.succ Intrinsic.motiveLevel))
  · exact .sorts Intrinsic.elementLevel
      (.max Intrinsic.elementLevel (.succ Intrinsic.motiveLevel))

def familyIndicesLevel : LevelExpr :=
  .max Intrinsic.elementLevel
    (.max Intrinsic.elementLevel (.succ Intrinsic.motiveLevel))

def familyAfterRelationLevel : LevelExpr :=
  .max relationTypeLevel familyIndicesLevel

def familyAfterTargetLevel : LevelExpr :=
  .max (.succ Intrinsic.elementLevel) familyAfterRelationLevel

def familyDeclarationLevel : LevelExpr :=
  .max (.succ Intrinsic.elementLevel) familyAfterTargetLevel

/-- The five-argument relation lifting is itself a formed family type. -/
theorem mapRelType_hasType :
    HasType rules (.nil : Tower.Ctx 0) mapRelType
      (sortTm familyDeclarationLevel) := by
  unfold mapRelType mapRelIndexType familyDeclarationLevel familyAfterTargetLevel
    familyAfterRelationLevel familyIndicesLevel
  apply Presentation.HasType.piForm
  · exact .headType (.sort Intrinsic.elementLevel)
  · exact .sort (.succ Intrinsic.elementLevel)
  · apply Presentation.HasType.piForm
    · exact .headType (.sort Intrinsic.elementLevel)
    · exact .sort (.succ Intrinsic.elementLevel)
    · apply Presentation.HasType.piForm
      · exact relationType_hasType
      · exact .sort relationTypeLevel
      · apply Presentation.HasType.piForm
        · apply listApp_hasType
          exact Presentation.HasType.var 2
        · exact .sort Intrinsic.elementLevel
        · apply Presentation.HasType.piForm
          · apply listApp_hasType
            exact Presentation.HasType.var 2
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
    HasType rules context (.const mapRelName) (liftClosed mapRelType) := by
  apply Presentation.HasType.const
  change combinedType Tower.rules rawSignature mapRelName = some mapRelType
  apply combinedType_of_signature
  · rfl
  · exact typeOf_mapRel

theorem instantiateTwo_relationType
    (source target : Tower.Tm n) :
    Presentation.subst (subst0 target)
        (Presentation.subst (liftSub (subst0 source))
          (Presentation.rename (liftRen (liftRen Fin.elim0))
            relationType)) =
      .pi source
        (.pi (Presentation.rename wk target)
          (sortTm Intrinsic.motiveLevel)) := by
  rw [Intrinsic.instantiateTwo_eq_subst source target relationType]
  rfl

theorem instantiateThree_mapRelIndexType
    (source target relation : Tower.Tm n) :
    Presentation.subst (subst0 relation)
        (Presentation.subst (liftSub (subst0 target))
          (Presentation.subst (liftSub (liftSub (subst0 source)))
            (Presentation.rename
              (liftRen (liftRen (liftRen Fin.elim0)))
              mapRelIndexType))) =
      .pi (Intrinsic.listApp source)
        (.pi (Intrinsic.listApp (Presentation.rename wk target))
          (sortTm Intrinsic.motiveLevel)) := by
  rw [Intrinsic.instantiateThree_eq_subst source target relation
    mapRelIndexType]
  rfl

/-- Applying the family former preserves all five authored arguments and
returns a type in the relation-evidence universe. -/
theorem mapRelApp_hasType {context : Tower.Ctx n}
    {source target relation sourceList targetList : Tower.Tm n}
    (sourceTyping : HasType rules context source
      (sortTm Intrinsic.elementLevel))
    (targetTyping : HasType rules context target
      (sortTm Intrinsic.elementLevel))
    (relationTyping : HasType rules context relation
      (.pi source (.pi (Presentation.rename wk target)
        (sortTm Intrinsic.motiveLevel))))
    (sourceListTyping : HasType rules context sourceList
      (Intrinsic.listApp source))
    (targetListTyping : HasType rules context targetList
      (Intrinsic.listApp target)) :
    HasType rules context
      (mapRelApp source target relation sourceList targetList)
      (sortTm Intrinsic.motiveLevel) := by
  have afterSource := Presentation.HasType.appElim
    (mapRelConstant_hasType (context := context)) sourceTyping
  have afterTarget := Presentation.HasType.appElim afterSource targetTyping
  have relationTypingExpected :
      HasType rules context relation
        (Presentation.subst (subst0 target)
          (Presentation.subst (liftSub (subst0 source))
            (Presentation.rename (liftRen (liftRen Fin.elim0))
              relationType))) := by
    rw [instantiateTwo_relationType]
    exact relationTyping
  have afterRelation := Presentation.HasType.appElim afterTarget
    relationTypingExpected
  change HasType rules context _
    (Presentation.subst (subst0 relation)
      (Presentation.subst (liftSub (subst0 target))
        (Presentation.subst (liftSub (liftSub (subst0 source)))
          (Presentation.rename
            (liftRen (liftRen (liftRen Fin.elim0)))
            mapRelIndexType)))) at afterRelation
  rw [instantiateThree_mapRelIndexType source target relation]
    at afterRelation
  have afterSourceList := Presentation.HasType.appElim afterRelation
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
      HasType rules context
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
  have afterTargetList := Presentation.HasType.appElim
    afterSourceListNormalized
    targetListTyping
  have resultInstantiation :
      Presentation.inst0 targetList (sortTm Intrinsic.motiveLevel) =
        sortTm Intrinsic.motiveLevel := by
    rfl
  rw [resultInstantiation] at afterTargetList
  exact afterTargetList

theorem nilRelConstant_hasType {context : Tower.Ctx n} :
    HasType rules context (.const nilRelName) (liftClosed nilRelType) := by
  apply Presentation.HasType.const
  change combinedType Tower.rules rawSignature nilRelName = some nilRelType
  apply combinedType_of_signature
  · rfl
  · exact typeOf_nilRel

theorem instantiateThree_nilRelBodyType
    (source target relation : Tower.Tm n) :
    Presentation.subst (subst0 relation)
        (Presentation.subst (liftSub (subst0 target))
          (Presentation.subst (liftSub (liftSub (subst0 source)))
            (Presentation.rename
              (liftRen (liftRen (liftRen Fin.elim0)))
              nilRelBodyType))) =
      mapRelApp source target relation
        (Intrinsic.nilApp source) (Intrinsic.nilApp target) := by
  rw [Intrinsic.instantiateThree_eq_subst source target relation
    nilRelBodyType]
  rfl

theorem nilRelApp_hasType {context : Tower.Ctx n}
    {source target relation : Tower.Tm n}
    (sourceTyping : HasType rules context source
      (sortTm Intrinsic.elementLevel))
    (targetTyping : HasType rules context target
      (sortTm Intrinsic.elementLevel))
    (relationTyping : HasType rules context relation
      (.pi source (.pi (Presentation.rename wk target)
        (sortTm Intrinsic.motiveLevel)))) :
    HasType rules context (nilRelApp source target relation)
      (mapRelApp source target relation
        (Intrinsic.nilApp source) (Intrinsic.nilApp target)) := by
  have afterSource := Presentation.HasType.appElim
    (nilRelConstant_hasType (context := context)) sourceTyping
  have afterTarget := Presentation.HasType.appElim afterSource targetTyping
  have relationTypingExpected :
      HasType rules context relation
        (Presentation.subst (subst0 target)
          (Presentation.subst (liftSub (subst0 source))
            (Presentation.rename (liftRen (liftRen Fin.elim0))
              relationType))) := by
    rw [instantiateTwo_relationType]
    exact relationTyping
  have afterRelation := Presentation.HasType.appElim afterTarget
    relationTypingExpected
  change HasType rules context _
    (Presentation.subst (subst0 relation)
      (Presentation.subst (liftSub (subst0 target))
        (Presentation.subst (liftSub (liftSub (subst0 source)))
          (Presentation.rename
            (liftRen (liftRen (liftRen Fin.elim0)))
            nilRelBodyType)))) at afterRelation
  rw [instantiateThree_nilRelBodyType source target relation]
    at afterRelation
  exact afterRelation

theorem consRelConstant_hasType {context : Tower.Ctx n} :
    HasType rules context (.const consRelName) (liftClosed consRelType) := by
  apply Presentation.HasType.const
  change combinedType Tower.rules rawSignature consRelName = some consRelType
  apply combinedType_of_signature
  · rfl
  · exact typeOf_consRel

def weaken1 (term : Tower.Tm n) : Tower.Tm (n + 1) :=
  Presentation.rename wk term

def weaken2 (term : Tower.Tm n) : Tower.Tm (n + 2) :=
  Presentation.rename wk (weaken1 term)

def weaken3 (term : Tower.Tm n) : Tower.Tm (n + 3) :=
  Presentation.rename wk (weaken2 term)

def weaken4 (term : Tower.Tm n) : Tower.Tm (n + 4) :=
  Presentation.rename wk (weaken3 term)

def weaken5 (term : Tower.Tm n) : Tower.Tm (n + 5) :=
  Presentation.rename wk (weaken4 term)

def weaken6 (term : Tower.Tm n) : Tower.Tm (n + 6) :=
  Presentation.rename wk (weaken5 term)

@[simp] theorem instantiateOne_weaken1
    (argument term : Tower.Tm n) :
    Presentation.subst (subst0 argument) (weaken1 term) = term := by
  exact Presentation.inst0_rename_wk argument term

@[simp] theorem instantiateUnderOne_weaken2
    (argument term : Tower.Tm n) :
    Presentation.subst (liftSub (subst0 argument)) (weaken2 term) =
      weaken1 term := by
  unfold weaken2
  rw [Presentation.subst_liftSub_wk, instantiateOne_weaken1]
  rfl

@[simp] theorem liftSub_subst0_one (argument : Tower.Tm n) :
    liftSub (subst0 argument) (1 : Fin (n + 2)) = weaken1 argument := by
  rfl

@[simp] theorem instantiateTwo_weaken2
    (first second term : Tower.Tm n) :
    Presentation.subst (subst0 second)
        (Presentation.subst (liftSub (subst0 first)) (weaken2 term)) =
      term := by
  unfold weaken2 weaken1
  rw [Presentation.subst_liftSub_wk]
  rw [show Presentation.subst (subst0 first)
      (Presentation.rename wk term) = term from
    Presentation.inst0_rename_wk first term]
  exact Presentation.inst0_rename_wk second term

@[simp] theorem instantiateThree_weaken3
    (first second third term : Tower.Tm n) :
    Presentation.subst (subst0 third)
        (Presentation.subst (liftSub (subst0 second))
          (Presentation.subst (liftSub (liftSub (subst0 first)))
            (weaken3 term))) =
      term := by
  unfold weaken3
  rw [Presentation.subst_liftSub_wk]
  rw [Presentation.subst_liftSub_wk]
  rw [instantiateTwo_weaken2]
  exact Presentation.inst0_rename_wk third term

@[simp] theorem instantiateFour_weaken4
    (first second third fourth term : Tower.Tm n) :
    Presentation.subst (subst0 fourth)
        (Presentation.subst (liftSub (subst0 third))
          (Presentation.subst (liftSub (liftSub (subst0 second)))
            (Presentation.subst
              (liftSub (liftSub (liftSub (subst0 first))))
              (weaken4 term)))) =
      term := by
  unfold weaken4
  rw [Presentation.subst_liftSub_wk]
  rw [Presentation.subst_liftSub_wk]
  rw [Presentation.subst_liftSub_wk]
  rw [instantiateThree_weaken3]
  exact Presentation.inst0_rename_wk fourth term

@[simp] theorem instantiateFour_varThree
    (sourceHead targetHead sourceTail targetTail : Tower.Tm n) :
    Presentation.subst (subst0 targetTail)
        (Presentation.subst (liftSub (subst0 sourceTail))
          (Presentation.subst (liftSub (liftSub (subst0 targetHead)))
            (Presentation.subst
              (liftSub (liftSub (liftSub (subst0 sourceHead))))
              (.var 3)))) =
      sourceHead := by
  change Presentation.subst (subst0 targetTail)
      (Presentation.subst (liftSub (subst0 sourceTail))
        (Presentation.subst (liftSub (liftSub (subst0 targetHead)))
          (weaken3 sourceHead))) = sourceHead
  exact instantiateThree_weaken3 targetHead sourceTail targetTail sourceHead

@[simp] theorem instantiateFour_varTwo
    (sourceHead targetHead sourceTail targetTail : Tower.Tm n) :
    Presentation.subst (subst0 targetTail)
        (Presentation.subst (liftSub (subst0 sourceTail))
          (Presentation.subst (liftSub (liftSub (subst0 targetHead)))
            (Presentation.subst
              (liftSub (liftSub (liftSub (subst0 sourceHead))))
              (.var 2)))) =
      targetHead := by
  change Presentation.subst (subst0 targetTail)
      (Presentation.subst (liftSub (subst0 sourceTail))
        (weaken2 targetHead)) = targetHead
  exact instantiateTwo_weaken2 sourceTail targetTail targetHead

@[simp] theorem instantiateFour_headRelation
    (sourceHead targetHead sourceTail targetTail relation : Tower.Tm n) :
    Presentation.subst (subst0 targetTail)
        (Presentation.subst (liftSub (subst0 sourceTail))
          (Presentation.subst (liftSub (liftSub (subst0 targetHead)))
            (Presentation.subst
              (liftSub (liftSub (liftSub (subst0 sourceHead))))
              (.app (.app (weaken4 relation) (.var 3)) (.var 2))))) =
      .app (.app relation sourceHead) targetHead := by
  change
    Presentation.Tm.app
      (Presentation.Tm.app
        (Presentation.subst (subst0 targetTail)
          (Presentation.subst (liftSub (subst0 sourceTail))
            (Presentation.subst (liftSub (liftSub (subst0 targetHead)))
              (Presentation.subst
                (liftSub (liftSub (liftSub (subst0 sourceHead))))
                (weaken4 relation)))))
        (Presentation.subst (subst0 targetTail)
          (Presentation.subst (liftSub (subst0 sourceTail))
            (Presentation.subst (liftSub (liftSub (subst0 targetHead)))
              (Presentation.subst
                (liftSub (liftSub (liftSub (subst0 sourceHead))))
                (.var 3))))))
      (Presentation.subst (subst0 targetTail)
        (Presentation.subst (liftSub (subst0 sourceTail))
          (Presentation.subst (liftSub (liftSub (subst0 targetHead)))
            (Presentation.subst
              (liftSub (liftSub (liftSub (subst0 sourceHead))))
              (.var 2))))) =
      Presentation.Tm.app (Presentation.Tm.app relation sourceHead) targetHead
  rw [instantiateFour_weaken4, instantiateFour_varThree,
    instantiateFour_varTwo]

def instantiateFive
    (first second third fourth fifth : Tower.Tm n)
    (body : Tower.Tm (n + 5)) : Tower.Tm n :=
  Presentation.subst (subst0 fifth)
    (Presentation.subst (liftSub (subst0 fourth))
      (Presentation.subst (liftSub (liftSub (subst0 third)))
        (Presentation.subst
          (liftSub (liftSub (liftSub (subst0 second))))
          (Presentation.subst
            (liftSub (liftSub (liftSub (liftSub (subst0 first)))))
            body))))

@[simp] theorem instantiateFive_app
    (first second third fourth fifth : Tower.Tm n)
    (function argument : Tower.Tm (n + 5)) :
    instantiateFive first second third fourth fifth
        (.app function argument) =
      .app
        (instantiateFive first second third fourth fifth function)
        (instantiateFive first second third fourth fifth argument) := by
  rfl

@[simp] theorem instantiateFive_const
    (first second third fourth fifth : Tower.Tm n) (name : DeclName) :
    instantiateFive first second third fourth fifth (.const name) =
      (.const name : Tower.Tm n) := by
  rfl

@[simp] theorem instantiateFive_weaken5
    (first second third fourth fifth term : Tower.Tm n) :
    instantiateFive first second third fourth fifth (weaken5 term) = term := by
  unfold instantiateFive weaken5
  rw [Presentation.subst_liftSub_wk]
  rw [Presentation.subst_liftSub_wk]
  rw [Presentation.subst_liftSub_wk]
  rw [Presentation.subst_liftSub_wk]
  rw [instantiateFour_weaken4]
  exact Presentation.inst0_rename_wk fifth term

@[simp] theorem instantiateFive_varTwo
    (sourceHead targetHead sourceTail targetTail headEvidence : Tower.Tm n) :
    instantiateFive sourceHead targetHead sourceTail targetTail headEvidence
        (.var 2) =
      sourceTail := by
  change Presentation.subst (subst0 headEvidence)
      (Presentation.subst (liftSub (subst0 targetTail))
        (weaken2 sourceTail)) = sourceTail
  exact instantiateTwo_weaken2 targetTail headEvidence sourceTail

@[simp] theorem instantiateFive_varOne
    (sourceHead targetHead sourceTail targetTail headEvidence : Tower.Tm n) :
    instantiateFive sourceHead targetHead sourceTail targetTail headEvidence
        (.var 1) =
      targetTail := by
  change Presentation.subst (subst0 headEvidence) (weaken1 targetTail) =
    targetTail
  exact Presentation.inst0_rename_wk headEvidence targetTail

@[simp] theorem instantiateFive_mapRelTail
    (source target relation sourceHead targetHead sourceTail targetTail
      headEvidence : Tower.Tm n) :
    instantiateFive sourceHead targetHead sourceTail targetTail headEvidence
        (mapRelApp (weaken5 source) (weaken5 target) (weaken5 relation)
          (.var 2) (.var 1)) =
      mapRelApp source target relation sourceTail targetTail := by
  simp only [mapRelApp, instantiateFive_app, instantiateFive_weaken5,
    instantiateFive_const, instantiateFive_varTwo, instantiateFive_varOne]

def instantiateSix
    (first second third fourth fifth sixth : Tower.Tm n)
    (body : Tower.Tm (n + 6)) : Tower.Tm n :=
  Presentation.subst (subst0 sixth)
    (Presentation.subst (liftSub (subst0 fifth))
      (Presentation.subst (liftSub (liftSub (subst0 fourth)))
        (Presentation.subst
          (liftSub (liftSub (liftSub (subst0 third))))
          (Presentation.subst
            (liftSub (liftSub (liftSub (liftSub (subst0 second)))))
            (Presentation.subst
              (liftSub
                (liftSub (liftSub (liftSub (liftSub (subst0 first))))))
              body)))))

@[simp] theorem instantiateSix_app
    (first second third fourth fifth sixth : Tower.Tm n)
    (function argument : Tower.Tm (n + 6)) :
    instantiateSix first second third fourth fifth sixth
        (.app function argument) =
      .app
        (instantiateSix first second third fourth fifth sixth function)
        (instantiateSix first second third fourth fifth sixth argument) := by
  rfl

@[simp] theorem instantiateSix_const
    (first second third fourth fifth sixth : Tower.Tm n) (name : DeclName) :
    instantiateSix first second third fourth fifth sixth (.const name) =
      (.const name : Tower.Tm n) := by
  rfl

@[simp] theorem instantiateSix_weaken6
    (first second third fourth fifth sixth term : Tower.Tm n) :
    instantiateSix first second third fourth fifth sixth (weaken6 term) =
      term := by
  unfold instantiateSix weaken6
  rw [Presentation.subst_liftSub_wk]
  rw [Presentation.subst_liftSub_wk]
  rw [Presentation.subst_liftSub_wk]
  rw [Presentation.subst_liftSub_wk]
  rw [Presentation.subst_liftSub_wk]
  change Presentation.subst (subst0 sixth)
    (Presentation.rename wk
      (instantiateFive first second third fourth fifth (weaken5 term))) =
    term
  rw [instantiateFive_weaken5]
  exact Presentation.inst0_rename_wk sixth term

@[simp] theorem instantiateSix_varFive
    (sourceHead targetHead sourceTail targetTail headEvidence tailEvidence :
      Tower.Tm n) :
    instantiateSix sourceHead targetHead sourceTail targetTail headEvidence
        tailEvidence (.var 5) =
      sourceHead := by
  change instantiateFive targetHead sourceTail targetTail headEvidence
      tailEvidence (weaken5 sourceHead) = sourceHead
  exact instantiateFive_weaken5 targetHead sourceTail targetTail headEvidence
    tailEvidence sourceHead

@[simp] theorem instantiateSix_varFour
    (sourceHead targetHead sourceTail targetTail headEvidence tailEvidence :
      Tower.Tm n) :
    instantiateSix sourceHead targetHead sourceTail targetTail headEvidence
        tailEvidence (.var 4) =
      targetHead := by
  change Presentation.subst (subst0 tailEvidence)
      (Presentation.subst (liftSub (subst0 headEvidence))
        (Presentation.subst (liftSub (liftSub (subst0 targetTail)))
          (Presentation.subst
            (liftSub (liftSub (liftSub (subst0 sourceTail))))
            (weaken4 targetHead)))) = targetHead
  exact instantiateFour_weaken4 sourceTail targetTail headEvidence
    tailEvidence targetHead

@[simp] theorem instantiateSix_varThree
    (sourceHead targetHead sourceTail targetTail headEvidence tailEvidence :
      Tower.Tm n) :
    instantiateSix sourceHead targetHead sourceTail targetTail headEvidence
        tailEvidence (.var 3) =
      sourceTail := by
  change Presentation.subst (subst0 tailEvidence)
      (Presentation.subst (liftSub (subst0 headEvidence))
        (Presentation.subst (liftSub (liftSub (subst0 targetTail)))
          (weaken3 sourceTail))) = sourceTail
  exact instantiateThree_weaken3 targetTail headEvidence tailEvidence
    sourceTail

@[simp] theorem instantiateSix_varTwo
    (sourceHead targetHead sourceTail targetTail headEvidence tailEvidence :
      Tower.Tm n) :
    instantiateSix sourceHead targetHead sourceTail targetTail headEvidence
        tailEvidence (.var 2) =
      targetTail := by
  change Presentation.subst (subst0 tailEvidence)
      (Presentation.subst (liftSub (subst0 headEvidence))
        (weaken2 targetTail)) = targetTail
  exact instantiateTwo_weaken2 headEvidence tailEvidence targetTail

@[simp] theorem instantiateSix_consResult
    (source target relation sourceHead targetHead sourceTail targetTail
      headEvidence tailEvidence : Tower.Tm n) :
    instantiateSix sourceHead targetHead sourceTail targetTail headEvidence
        tailEvidence
        (mapRelApp (weaken6 source) (weaken6 target) (weaken6 relation)
          (Intrinsic.consApp (weaken6 source) (.var 5) (.var 3))
          (Intrinsic.consApp (weaken6 target) (.var 4) (.var 2))) =
      mapRelApp source target relation
        (Intrinsic.consApp source sourceHead sourceTail)
        (Intrinsic.consApp target targetHead targetTail) := by
  simp only [mapRelApp, Intrinsic.consApp, instantiateSix_app,
    instantiateSix_const, instantiateSix_weaken6, instantiateSix_varFive,
    instantiateSix_varFour, instantiateSix_varThree, instantiateSix_varTwo]

/-- The constructor telescope after substituting its three parameters. -/
def consRelBodyAt (source target relation : Tower.Tm n) : Tower.Tm n :=
  .pi source
    (.pi (weaken1 target)
      (.pi (Intrinsic.listApp (weaken2 source))
        (.pi (Intrinsic.listApp (weaken3 target))
          (.pi (.app (.app (weaken4 relation) (.var 3)) (.var 2))
            (.pi
              (mapRelApp (weaken5 source) (weaken5 target)
                (weaken5 relation) (.var 2) (.var 1))
              (mapRelApp (weaken6 source) (weaken6 target)
                (weaken6 relation)
                (Intrinsic.consApp (weaken6 source) (.var 5) (.var 3))
                (Intrinsic.consApp (weaken6 target) (.var 4) (.var 2))))))))

theorem instantiateThree_consRelBodyType
    (source target relation : Tower.Tm n) :
    Presentation.subst (subst0 relation)
        (Presentation.subst (liftSub (subst0 target))
          (Presentation.subst (liftSub (liftSub (subst0 source)))
            (Presentation.rename
              (liftRen (liftRen (liftRen Fin.elim0)))
              consRelBodyType))) =
      consRelBodyAt source target relation := by
  rw [Intrinsic.instantiateThree_eq_subst source target relation
    consRelBodyType]
  rfl

theorem consRelApp_hasType {context : Tower.Ctx n}
    {source target relation sourceHead targetHead sourceTail targetTail
      headEvidence tailEvidence : Tower.Tm n}
    (sourceTyping : HasType rules context source
      (sortTm Intrinsic.elementLevel))
    (targetTyping : HasType rules context target
      (sortTm Intrinsic.elementLevel))
    (relationTyping : HasType rules context relation
      (.pi source (.pi (Presentation.rename wk target)
        (sortTm Intrinsic.motiveLevel))))
    (sourceHeadTyping : HasType rules context sourceHead source)
    (targetHeadTyping : HasType rules context targetHead target)
    (sourceTailTyping : HasType rules context sourceTail
      (Intrinsic.listApp source))
    (targetTailTyping : HasType rules context targetTail
      (Intrinsic.listApp target))
    (headEvidenceTyping : HasType rules context headEvidence
      (.app (.app relation sourceHead) targetHead))
    (tailEvidenceTyping : HasType rules context tailEvidence
      (mapRelApp source target relation sourceTail targetTail)) :
    HasType rules context
      (consRelApp source target relation sourceHead targetHead sourceTail
        targetTail headEvidence tailEvidence)
      (mapRelApp source target relation
        (Intrinsic.consApp source sourceHead sourceTail)
        (Intrinsic.consApp target targetHead targetTail)) := by
  have afterSource := Presentation.HasType.appElim
    (consRelConstant_hasType (context := context)) sourceTyping
  have afterTarget := Presentation.HasType.appElim afterSource targetTyping
  have relationTypingExpected :
      HasType rules context relation
        (Presentation.subst (subst0 target)
          (Presentation.subst (liftSub (subst0 source))
            (Presentation.rename (liftRen (liftRen Fin.elim0))
              relationType))) := by
    rw [instantiateTwo_relationType]
    exact relationTyping
  have afterRelation := Presentation.HasType.appElim afterTarget
    relationTypingExpected
  change HasType rules context _
    (Presentation.subst (subst0 relation)
      (Presentation.subst (liftSub (subst0 target))
        (Presentation.subst (liftSub (liftSub (subst0 source)))
          (Presentation.rename
            (liftRen (liftRen (liftRen Fin.elim0)))
            consRelBodyType)))) at afterRelation
  rw [instantiateThree_consRelBodyType source target relation]
    at afterRelation
  have afterSourceHead := Presentation.HasType.appElim afterRelation
    sourceHeadTyping
  have targetHeadTypingExpected :
      HasType rules context targetHead
        (Presentation.inst0 sourceHead (weaken1 target)) := by
    rw [weaken1, Presentation.inst0_rename_wk]
    exact targetHeadTyping
  have afterTargetHead := Presentation.HasType.appElim afterSourceHead
    targetHeadTypingExpected
  have sourceTailTypingExpected :
      HasType rules context sourceTail
        (Presentation.subst (subst0 targetHead)
          (Presentation.subst (liftSub (subst0 sourceHead))
            (Intrinsic.listApp (weaken2 source)))) := by
    change HasType rules context sourceTail
      (Presentation.subst (subst0 targetHead)
        (Presentation.subst (liftSub (subst0 sourceHead))
          (weaken2 (Intrinsic.listApp source))))
    rw [instantiateTwo_weaken2]
    exact sourceTailTyping
  have afterSourceTail := Presentation.HasType.appElim afterTargetHead
    sourceTailTypingExpected
  have targetTailTypingExpected :
      HasType rules context targetTail
        (Presentation.subst (subst0 sourceTail)
          (Presentation.subst (liftSub (subst0 targetHead))
            (Presentation.subst (liftSub (liftSub (subst0 sourceHead)))
              (Intrinsic.listApp (weaken3 target))))) := by
    change HasType rules context targetTail
      (Presentation.subst (subst0 sourceTail)
        (Presentation.subst (liftSub (subst0 targetHead))
          (Presentation.subst (liftSub (liftSub (subst0 sourceHead)))
            (weaken3 (Intrinsic.listApp target)))))
    rw [instantiateThree_weaken3]
    exact targetTailTyping
  have afterTargetTail := Presentation.HasType.appElim afterSourceTail
    targetTailTypingExpected
  have headEvidenceTypingExpected :
      HasType rules context headEvidence
        (Presentation.subst (subst0 targetTail)
          (Presentation.subst (liftSub (subst0 sourceTail))
            (Presentation.subst (liftSub (liftSub (subst0 targetHead)))
              (Presentation.subst
                (liftSub (liftSub (liftSub (subst0 sourceHead))))
                (.app (.app (weaken4 relation) (.var 3)) (.var 2)))))) := by
    rw [instantiateFour_headRelation]
    exact headEvidenceTyping
  have afterHeadEvidence := Presentation.HasType.appElim afterTargetTail
    headEvidenceTypingExpected
  have tailEvidenceTypingExpected :
      HasType rules context tailEvidence
        (instantiateFive sourceHead targetHead sourceTail targetTail
          headEvidence
          (mapRelApp (weaken5 source) (weaken5 target) (weaken5 relation)
            (.var 2) (.var 1))) := by
    rw [instantiateFive_mapRelTail]
    exact tailEvidenceTyping
  have afterTailEvidence := Presentation.HasType.appElim afterHeadEvidence
    tailEvidenceTypingExpected
  change HasType rules context _
    (instantiateSix sourceHead targetHead sourceTail targetTail headEvidence
      tailEvidence
      (mapRelApp (weaken6 source) (weaken6 target) (weaken6 relation)
        (Intrinsic.consApp (weaken6 source) (.var 5) (.var 3))
        (Intrinsic.consApp (weaken6 target) (.var 4) (.var 2))))
    at afterTailEvidence
  rw [instantiateSix_consResult] at afterTailEvidence
  exact afterTailEvidence

def motiveTypeAt (source target relation : Tower.Tm n) : Tower.Tm n :=
  .pi (Intrinsic.listApp source)
    (.pi (Intrinsic.listApp (weaken1 target))
      (.pi
        (mapRelApp (weaken2 source) (weaken2 target) (weaken2 relation)
          (.var 1) (.var 0))
        (sortTm eliminationLevel)))

def motiveAfterSourceType
    (source target relation sourceList : Tower.Tm n) : Tower.Tm n :=
  .pi (Intrinsic.listApp target)
    (.pi
      (mapRelApp (weaken1 source) (weaken1 target) (weaken1 relation)
        (weaken1 sourceList) (.var 0))
      (sortTm eliminationLevel))

theorem motiveApp_hasType {context : Tower.Ctx n}
    {source target relation motive sourceList targetList evidence : Tower.Tm n}
    (motiveTyping : HasType rules context motive
      (motiveTypeAt source target relation))
    (sourceListTyping : HasType rules context sourceList
      (Intrinsic.listApp source))
    (targetListTyping : HasType rules context targetList
      (Intrinsic.listApp target))
    (evidenceTyping : HasType rules context evidence
      (mapRelApp source target relation sourceList targetList)) :
    HasType rules context
      (motiveApp motive sourceList targetList evidence)
      (sortTm eliminationLevel) := by
  have afterSource := Presentation.HasType.appElim motiveTyping
    sourceListTyping
  have afterSourceNormalized :
      HasType rules context (.app motive sourceList)
        (motiveAfterSourceType source target relation sourceList) := by
    simpa only [motiveTypeAt, motiveAfterSourceType, Presentation.inst0,
      Presentation.subst, mapRelApp, Intrinsic.listApp,
      instantiateOne_weaken1, instantiateUnderOne_weaken2,
      liftSub_subst0_one, Presentation.liftSub_zero, sortTm]
      using afterSource
  have afterTarget := Presentation.HasType.appElim afterSourceNormalized
    targetListTyping
  have afterTargetNormalized :
      HasType rules context (.app (.app motive sourceList) targetList)
        (.pi (mapRelApp source target relation sourceList targetList)
          (sortTm eliminationLevel)) := by
    simpa only [motiveAfterSourceType, Presentation.inst0,
      Presentation.subst, mapRelApp, Intrinsic.listApp,
      instantiateOne_weaken1, Presentation.subst0_zero, sortTm]
      using afterTarget
  have afterEvidence := Presentation.HasType.appElim afterTargetNormalized
    evidenceTyping
  simpa [motiveApp, Presentation.inst0, sortTm, Presentation.subst]
    using afterEvidence

def contextABRP : Tower.Ctx 4 :=
  .snoc contextABR motiveType

def contextABRPZ : Tower.Ctx 5 :=
  .snoc contextABRP nilCaseType

def contextABRPZS : Tower.Ctx 6 :=
  .snoc contextABRPZ consCaseType

def motiveAfterEvidenceLevel : LevelExpr :=
  .max Intrinsic.motiveLevel (.succ eliminationLevel)

def motiveAfterTargetListLevel : LevelExpr :=
  .max Intrinsic.elementLevel motiveAfterEvidenceLevel

def motiveTypeLevel : LevelExpr :=
  .max Intrinsic.elementLevel motiveAfterTargetListLevel

theorem motiveType_hasType :
    HasType rules contextABR motiveType (sortTm motiveTypeLevel) := by
  unfold motiveType motiveTypeLevel motiveAfterTargetListLevel
    motiveAfterEvidenceLevel
  apply Presentation.HasType.piForm
  · apply listApp_hasType
    exact Presentation.HasType.var 2
  · exact .sort Intrinsic.elementLevel
  · apply Presentation.HasType.piForm
    · apply listApp_hasType
      exact Presentation.HasType.var 2
    · exact .sort Intrinsic.elementLevel
    · apply Presentation.HasType.piForm
      · apply mapRelApp_hasType
        · exact Presentation.HasType.var 4
        · exact Presentation.HasType.var 3
        · exact Presentation.HasType.var 2
        · exact Presentation.HasType.var 1
        · exact Presentation.HasType.var 0
      · exact .sort Intrinsic.motiveLevel
      · exact .headType (.sort eliminationLevel)
      · exact .sort (.succ eliminationLevel)
      · exact .sorts Intrinsic.motiveLevel (.succ eliminationLevel)
    · exact .sort motiveAfterEvidenceLevel
    · exact .sorts Intrinsic.elementLevel motiveAfterEvidenceLevel
  · exact .sort motiveAfterTargetListLevel
  · exact .sorts Intrinsic.elementLevel motiveAfterTargetListLevel

theorem nilCaseType_hasType :
    HasType rules contextABRP nilCaseType (sortTm eliminationLevel) := by
  unfold nilCaseType contextABRP
  apply motiveApp_hasType (source := (.var 3 : Tower.Tm 4))
    (target := .var 2) (relation := .var 1)
  · exact Presentation.HasType.var 0
  · apply nilApp_hasType
    exact Presentation.HasType.var 3
  · apply nilApp_hasType
    exact Presentation.HasType.var 2
  · apply nilRelApp_hasType
    · exact Presentation.HasType.var 3
    · exact Presentation.HasType.var 2
    · exact Presentation.HasType.var 1

def consCaseAfterRecursiveLevel : LevelExpr :=
  .max eliminationLevel eliminationLevel

def consCaseAfterTailEvidenceLevel : LevelExpr :=
  .max Intrinsic.motiveLevel consCaseAfterRecursiveLevel

def consCaseAfterHeadEvidenceLevel : LevelExpr :=
  .max Intrinsic.motiveLevel consCaseAfterTailEvidenceLevel

def consCaseAfterTargetTailLevel : LevelExpr :=
  .max Intrinsic.elementLevel consCaseAfterHeadEvidenceLevel

def consCaseAfterSourceTailLevel : LevelExpr :=
  .max Intrinsic.elementLevel consCaseAfterTargetTailLevel

def consCaseAfterTargetHeadLevel : LevelExpr :=
  .max Intrinsic.elementLevel consCaseAfterSourceTailLevel

def consCaseLevel : LevelExpr :=
  .max Intrinsic.elementLevel consCaseAfterTargetHeadLevel

theorem consCaseType_hasType :
    HasType rules contextABRPZ consCaseType (sortTm consCaseLevel) := by
  unfold consCaseType consCaseLevel consCaseAfterTargetHeadLevel
    consCaseAfterSourceTailLevel consCaseAfterTargetTailLevel
    consCaseAfterHeadEvidenceLevel consCaseAfterTailEvidenceLevel
    consCaseAfterRecursiveLevel
  apply Presentation.HasType.piForm
  · exact Presentation.HasType.var 4
  · exact .sort Intrinsic.elementLevel
  · apply Presentation.HasType.piForm
    · exact Presentation.HasType.var 4
    · exact .sort Intrinsic.elementLevel
    · apply Presentation.HasType.piForm
      · apply listApp_hasType
        exact Presentation.HasType.var 6
      · exact .sort Intrinsic.elementLevel
      · apply Presentation.HasType.piForm
        · apply listApp_hasType
          exact Presentation.HasType.var 6
        · exact .sort Intrinsic.elementLevel
        · apply Presentation.HasType.piForm
          · apply relationApp_hasType
              (source := (.var 8 : Tower.Tm 9))
              (target := .var 7) (relation := .var 6)
              (sourceTerm := .var 3) (targetTerm := .var 2)
            · exact Presentation.HasType.var 6
            · exact Presentation.HasType.var 3
            · exact Presentation.HasType.var 2
          · exact .sort Intrinsic.motiveLevel
          · apply Presentation.HasType.piForm
            · apply mapRelApp_hasType
              · exact Presentation.HasType.var 9
              · exact Presentation.HasType.var 8
              · exact Presentation.HasType.var 7
              · exact Presentation.HasType.var 2
              · exact Presentation.HasType.var 1
            · exact .sort Intrinsic.motiveLevel
            · apply Presentation.HasType.piForm
              · apply motiveApp_hasType
                  (source := (.var 10 : Tower.Tm 11))
                  (target := .var 9) (relation := .var 8)
                · exact Presentation.HasType.var 7
                · exact Presentation.HasType.var 3
                · exact Presentation.HasType.var 2
                · exact Presentation.HasType.var 0
              · exact .sort eliminationLevel
              · apply motiveApp_hasType
                  (source := (.var 11 : Tower.Tm 12))
                  (target := .var 10) (relation := .var 9)
                · exact Presentation.HasType.var 8
                · apply consApp_hasType
                  · exact Presentation.HasType.var 11
                  · exact Presentation.HasType.var 6
                  · exact Presentation.HasType.var 4
                · apply consApp_hasType
                  · exact Presentation.HasType.var 10
                  · exact Presentation.HasType.var 5
                  · exact Presentation.HasType.var 3
                · apply consRelApp_hasType
                  · exact Presentation.HasType.var 11
                  · exact Presentation.HasType.var 10
                  · exact Presentation.HasType.var 9
                  · exact Presentation.HasType.var 6
                  · exact Presentation.HasType.var 5
                  · exact Presentation.HasType.var 4
                  · exact Presentation.HasType.var 3
                  · exact Presentation.HasType.var 2
                  · exact Presentation.HasType.var 1
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

def eliminateAfterEvidenceLevel : LevelExpr :=
  .max Intrinsic.motiveLevel eliminationLevel

def eliminateAfterTargetListLevel : LevelExpr :=
  .max Intrinsic.elementLevel eliminateAfterEvidenceLevel

def eliminateResultLevel : LevelExpr :=
  .max Intrinsic.elementLevel eliminateAfterTargetListLevel

theorem eliminateResultType_hasType :
    HasType rules contextABRPZS eliminateResultType
      (sortTm eliminateResultLevel) := by
  unfold eliminateResultType eliminateResultLevel eliminateAfterTargetListLevel
    eliminateAfterEvidenceLevel
  apply Presentation.HasType.piForm
  · apply listApp_hasType
    exact Presentation.HasType.var 5
  · exact .sort Intrinsic.elementLevel
  · apply Presentation.HasType.piForm
    · apply listApp_hasType
      exact Presentation.HasType.var 5
    · exact .sort Intrinsic.elementLevel
    · apply Presentation.HasType.piForm
      · apply mapRelApp_hasType
        · exact Presentation.HasType.var 7
        · exact Presentation.HasType.var 6
        · exact Presentation.HasType.var 5
        · exact Presentation.HasType.var 1
        · exact Presentation.HasType.var 0
      · exact .sort Intrinsic.motiveLevel
      · apply motiveApp_hasType
          (source := (.var 8 : Tower.Tm 9))
          (target := .var 7) (relation := .var 6)
        · exact Presentation.HasType.var 5
        · exact Presentation.HasType.var 2
        · exact Presentation.HasType.var 1
        · exact Presentation.HasType.var 0
      · exact .sort eliminationLevel
      · exact .sorts Intrinsic.motiveLevel eliminationLevel
    · exact .sort eliminateAfterEvidenceLevel
    · exact .sorts Intrinsic.elementLevel eliminateAfterEvidenceLevel
  · exact .sort eliminateAfterTargetListLevel
  · exact .sorts Intrinsic.elementLevel eliminateAfterTargetListLevel

def eliminateAfterConsCaseLevel : LevelExpr :=
  .max consCaseLevel eliminateResultLevel

def eliminateAfterNilCaseLevel : LevelExpr :=
  .max eliminationLevel eliminateAfterConsCaseLevel

def eliminateAfterMotiveLevel : LevelExpr :=
  .max motiveTypeLevel eliminateAfterNilCaseLevel

def eliminateAfterRelationLevel : LevelExpr :=
  .max relationTypeLevel eliminateAfterMotiveLevel

def eliminateAfterTargetLevel : LevelExpr :=
  .max (.succ Intrinsic.elementLevel) eliminateAfterRelationLevel

def eliminateDeclarationLevel : LevelExpr :=
  .max (.succ Intrinsic.elementLevel) eliminateAfterTargetLevel

theorem eliminateType_hasType :
    HasType rules (.nil : Tower.Ctx 0) eliminateType
      (sortTm eliminateDeclarationLevel) := by
  unfold eliminateType eliminateDeclarationLevel eliminateAfterTargetLevel
    eliminateAfterRelationLevel eliminateAfterMotiveLevel
    eliminateAfterNilCaseLevel eliminateAfterConsCaseLevel
  apply Presentation.HasType.piForm
  · exact .headType (.sort Intrinsic.elementLevel)
  · exact .sort (.succ Intrinsic.elementLevel)
  · apply Presentation.HasType.piForm
    · exact .headType (.sort Intrinsic.elementLevel)
    · exact .sort (.succ Intrinsic.elementLevel)
    · apply Presentation.HasType.piForm
      · exact relationType_hasType
      · exact .sort relationTypeLevel
      · apply Presentation.HasType.piForm
        · exact motiveType_hasType
        · exact .sort motiveTypeLevel
        · apply Presentation.HasType.piForm
          · exact nilCaseType_hasType
          · exact .sort eliminationLevel
          · apply Presentation.HasType.piForm
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

def nilRelAfterRelationLevel : LevelExpr :=
  .max relationTypeLevel Intrinsic.motiveLevel

def nilRelAfterTargetLevel : LevelExpr :=
  .max (.succ Intrinsic.elementLevel) nilRelAfterRelationLevel

def nilRelDeclarationLevel : LevelExpr :=
  .max (.succ Intrinsic.elementLevel) nilRelAfterTargetLevel

theorem nilRelType_hasType :
    HasType rules (.nil : Tower.Ctx 0) nilRelType
      (sortTm nilRelDeclarationLevel) := by
  unfold nilRelType nilRelDeclarationLevel nilRelAfterTargetLevel
    nilRelAfterRelationLevel
  apply Presentation.HasType.piForm
  · exact .headType (.sort Intrinsic.elementLevel)
  · exact .sort (.succ Intrinsic.elementLevel)
  · apply Presentation.HasType.piForm
    · exact .headType (.sort Intrinsic.elementLevel)
    · exact .sort (.succ Intrinsic.elementLevel)
    · apply Presentation.HasType.piForm
      · exact relationType_hasType
      · exact .sort relationTypeLevel
      · apply mapRelApp_hasType
        · exact Presentation.HasType.var 2
        · exact Presentation.HasType.var 1
        · exact Presentation.HasType.var 0
        · apply nilApp_hasType
          exact Presentation.HasType.var 2
        · apply nilApp_hasType
          exact Presentation.HasType.var 1
      · exact .sort Intrinsic.motiveLevel
      · exact .sorts relationTypeLevel Intrinsic.motiveLevel
    · exact .sort nilRelAfterRelationLevel
    · exact .sorts (.succ Intrinsic.elementLevel)
        nilRelAfterRelationLevel
  · exact .sort nilRelAfterTargetLevel
  · exact .sorts (.succ Intrinsic.elementLevel) nilRelAfterTargetLevel

def consRelAfterTailEvidenceLevel : LevelExpr :=
  .max Intrinsic.motiveLevel Intrinsic.motiveLevel

def consRelAfterHeadEvidenceLevel : LevelExpr :=
  .max Intrinsic.motiveLevel consRelAfterTailEvidenceLevel

def consRelAfterTargetTailLevel : LevelExpr :=
  .max Intrinsic.elementLevel consRelAfterHeadEvidenceLevel

def consRelAfterSourceTailLevel : LevelExpr :=
  .max Intrinsic.elementLevel consRelAfterTargetTailLevel

def consRelAfterTargetHeadLevel : LevelExpr :=
  .max Intrinsic.elementLevel consRelAfterSourceTailLevel

def consRelBodyLevel : LevelExpr :=
  .max Intrinsic.elementLevel consRelAfterTargetHeadLevel

/-- Every constructor field is formed in its exact telescope.  The recursive
field and result both inhabit the evidence universe, while List data remains
in the element universe. -/
theorem consRelBodyType_hasType :
    HasType rules contextABR consRelBodyType (sortTm consRelBodyLevel) := by
  unfold consRelBodyType consRelBodyLevel consRelAfterTargetHeadLevel
    consRelAfterSourceTailLevel consRelAfterTargetTailLevel
    consRelAfterHeadEvidenceLevel consRelAfterTailEvidenceLevel
  apply Presentation.HasType.piForm
  · exact Presentation.HasType.var 2
  · exact .sort Intrinsic.elementLevel
  · apply Presentation.HasType.piForm
    · exact Presentation.HasType.var 2
    · exact .sort Intrinsic.elementLevel
    · apply Presentation.HasType.piForm
      · apply listApp_hasType
        exact Presentation.HasType.var 4
      · exact .sort Intrinsic.elementLevel
      · apply Presentation.HasType.piForm
        · apply listApp_hasType
          exact Presentation.HasType.var 4
        · exact .sort Intrinsic.elementLevel
        · apply Presentation.HasType.piForm
          · apply relationApp_hasType
              (source := (.var 6 : Tower.Tm 7))
              (target := .var 5) (relation := .var 4)
              (sourceTerm := .var 3) (targetTerm := .var 2)
            · exact Presentation.HasType.var 4
            · exact Presentation.HasType.var 3
            · exact Presentation.HasType.var 2
          · exact .sort Intrinsic.motiveLevel
          · apply Presentation.HasType.piForm
            · apply mapRelApp_hasType
              · exact Presentation.HasType.var 7
              · exact Presentation.HasType.var 6
              · exact Presentation.HasType.var 5
              · exact Presentation.HasType.var 2
              · exact Presentation.HasType.var 1
            · exact .sort Intrinsic.motiveLevel
            · apply mapRelApp_hasType
              · exact Presentation.HasType.var 8
              · exact Presentation.HasType.var 7
              · exact Presentation.HasType.var 6
              · apply consApp_hasType
                · exact Presentation.HasType.var 8
                · exact Presentation.HasType.var 5
                · exact Presentation.HasType.var 3
              · apply consApp_hasType
                · exact Presentation.HasType.var 7
                · exact Presentation.HasType.var 4
                · exact Presentation.HasType.var 2
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

def consRelAfterRelationLevel : LevelExpr :=
  .max relationTypeLevel consRelBodyLevel

def consRelAfterOuterTargetLevel : LevelExpr :=
  .max (.succ Intrinsic.elementLevel) consRelAfterRelationLevel

def consRelDeclarationLevel : LevelExpr :=
  .max (.succ Intrinsic.elementLevel) consRelAfterOuterTargetLevel

theorem consRelType_hasType :
    HasType rules (.nil : Tower.Ctx 0) consRelType
      (sortTm consRelDeclarationLevel) := by
  unfold consRelType consRelDeclarationLevel consRelAfterOuterTargetLevel
    consRelAfterRelationLevel
  apply Presentation.HasType.piForm
  · exact .headType (.sort Intrinsic.elementLevel)
  · exact .sort (.succ Intrinsic.elementLevel)
  · apply Presentation.HasType.piForm
    · exact .headType (.sort Intrinsic.elementLevel)
    · exact .sort (.succ Intrinsic.elementLevel)
    · apply Presentation.HasType.piForm
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

@[simp] theorem rawSignature_valueOf_none (name : DeclName) :
    rawSignature.valueOf? name = none := by
  by_cases isMapRel : name = mapRelName
  · subst name
    simp [rawSignature, Signature.valueOf?, mapRelEntry]
  by_cases isNilRel : name = nilRelName
  · subst name
    simp [rawSignature, Signature.valueOf?, nilRelEntry, isMapRel]
  by_cases isConsRel : name = consRelName
  · subst name
    simp [rawSignature, Signature.valueOf?, consRelEntry, isMapRel,
      isNilRel]
  by_cases isEliminate : name = eliminateName
  · subst name
    simp [rawSignature, Signature.valueOf?, eliminateEntry, isMapRel,
      isNilRel, isConsRel]
  · have entriesEquality :
        rawSignature.entries name = Intrinsic.rawSignature.entries name := by
      simp [rawSignature, isMapRel, isNilRel, isConsRel, isEliminate]
    unfold Signature.valueOf?
    rw [entriesEquality]
    exact Intrinsic.rawSignature_valueOf_none name

theorem rawSignature_types_formed {name : DeclName} {type : Tower.Tm 0}
    (lookup : rawSignature.typeOf? name = some type) :
    ∃ level : Tower.Head,
      Tower.rules.isUniverse level ∧
      HasType rules (.nil : Tower.Ctx 0) type (.head level) := by
  by_cases isMapRel : name = mapRelName
  · subst name
    have typeEquality : type = mapRelType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort familyDeclarationLevel, .sort familyDeclarationLevel,
      mapRelType_hasType⟩
  by_cases isNilRel : name = nilRelName
  · subst name
    have typeEquality : type = nilRelType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort nilRelDeclarationLevel, .sort nilRelDeclarationLevel,
      nilRelType_hasType⟩
  by_cases isConsRel : name = consRelName
  · subst name
    have typeEquality : type = consRelType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort consRelDeclarationLevel, .sort consRelDeclarationLevel,
      consRelType_hasType⟩
  by_cases isEliminate : name = eliminateName
  · subst name
    have typeEquality : type = eliminateType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort eliminateDeclarationLevel,
      .sort eliminateDeclarationLevel, eliminateType_hasType⟩
  · have intrinsicLookup :
        Intrinsic.rawSignature.typeOf? name = some type := by
      have entriesEquality :
          rawSignature.entries name = Intrinsic.rawSignature.entries name := by
        simp [rawSignature, isMapRel, isNilRel, isConsRel, isEliminate]
      unfold Signature.typeOf? at lookup ⊢
      rw [entriesEquality] at lookup
      exact lookup
    rcases Intrinsic.rawSignature_formed.types intrinsicLookup with
      ⟨level, isUniverseWitness, typing⟩
    exact ⟨level, isUniverseWitness, includeListTyping typing⟩

theorem rawSignature_fresh {name : DeclName} {entry : Entry Tower.Head}
    (_lookup : rawSignature.entries name = some entry) :
    Tower.rules.constantType name = none :=
  rfl

def rawSignature_formed : rawSignature.Formed Tower.rules where
  fresh := rawSignature_fresh
  types := rawSignature_types_formed
  values := by
    intro name type value _typeLookup valueLookup
    rw [rawSignature_valueOf_none] at valueLookup
    cases valueLookup
  noSelfDelta := by
    intro name value valueLookup
    rw [rawSignature_valueOf_none] at valueLookup
    cases valueLookup

theorem eliminateConstant_hasType {context : Tower.Ctx n} :
    HasType rules context (.const eliminateName) (liftClosed eliminateType) := by
  apply Presentation.HasType.const
  change combinedType Tower.rules rawSignature eliminateName =
    some eliminateType
  apply combinedType_of_signature
  · rfl
  · exact typeOf_eliminate

def eliminateAtParameters : Tower.Tm 6 :=
  .app
    (.app
      (.app
        (.app
          (.app
            (.app (.const eliminateName) (.var 5))
            (.var 4))
          (.var 3))
        (.var 2))
      (.var 1))
    (.var 0)

def eliminateAtParametersType : Tower.Tm 6 :=
  eliminateResultType

theorem eliminateAtParameters_hasType :
    HasType rules contextABRPZS eliminateAtParameters
      eliminateAtParametersType := by
  have sourceTyping :
      HasType rules contextABRPZS (.var 5)
        (sortTm Intrinsic.elementLevel) :=
    Presentation.HasType.var 5
  have targetTyping :
      HasType rules contextABRPZS (.var 4)
        (sortTm Intrinsic.elementLevel) :=
    Presentation.HasType.var 4
  have relationTyping :
      HasType rules contextABRPZS (.var 3)
        (.pi (.var 5)
          (.pi (Presentation.rename wk (.var 4))
            (sortTm Intrinsic.motiveLevel))) :=
    Presentation.HasType.var 3
  have motiveTyping :
      HasType rules contextABRPZS (.var 2)
        (motiveTypeAt (.var 5) (.var 4) (.var 3)) := by
    exact Presentation.HasType.var 2
  have nilCaseTyping :
      HasType rules contextABRPZS (.var 1)
        (Presentation.rename wk (Presentation.rename wk nilCaseType)) := by
    exact Presentation.HasType.var 1
  have consCaseTyping :
      HasType rules contextABRPZS (.var 0)
        (Presentation.rename wk consCaseType) := by
    exact Presentation.HasType.var 0
  have afterSource := Presentation.HasType.appElim
    (eliminateConstant_hasType (context := contextABRPZS)) sourceTyping
  have afterTarget := Presentation.HasType.appElim afterSource targetTyping
  have afterRelation := Presentation.HasType.appElim afterTarget relationTyping
  have afterMotive := Presentation.HasType.appElim afterRelation motiveTyping
  have afterNil := Presentation.HasType.appElim afterMotive nilCaseTyping
  have afterCons := Presentation.HasType.appElim afterNil consCaseTyping
  convert afterCons using 1 <;> decide

abbrev TypedIotaReceipt (context : Tower.Ctx n)
    (left right type : Tower.Tm n) : Type :=
  ProofRelevantStepReceipt Tower.rules rawSignature
    combinedProofRelevantIotaComputation context left right type

def nilIotaLeft : Tower.Tm 6 :=
  .app
    (.app
      (.app eliminateAtParameters (Intrinsic.nilApp (.var 5)))
      (Intrinsic.nilApp (.var 4)))
    (nilRelApp (.var 5) (.var 4) (.var 3))

def nilIotaRight : Tower.Tm 6 := .var 1

def nilIotaResultType : Tower.Tm 6 :=
  motiveApp (.var 2)
    (Intrinsic.nilApp (.var 5))
    (Intrinsic.nilApp (.var 4))
    (nilRelApp (.var 5) (.var 4) (.var 3))

def nilIotaReceipt :
    TypedIotaReceipt contextABRPZS nilIotaLeft nilIotaRight
      nilIotaResultType where
  sourceTyping := by
    have sourceTyping :
        HasType rules contextABRPZS (.var 5)
          (sortTm Intrinsic.elementLevel) :=
      Presentation.HasType.var 5
    have targetTyping :
        HasType rules contextABRPZS (.var 4)
          (sortTm Intrinsic.elementLevel) :=
      Presentation.HasType.var 4
    have sourceListTyping := nilApp_hasType sourceTyping
    have targetListTyping := nilApp_hasType targetTyping
    have evidenceTyping := nilRelApp_hasType sourceTyping targetTyping
      (Presentation.HasType.var 3)
    have afterSource := Presentation.HasType.appElim
      eliminateAtParameters_hasType sourceListTyping
    have afterTarget := Presentation.HasType.appElim afterSource
      targetListTyping
    have result := Presentation.HasType.appElim afterTarget evidenceTyping
    convert result using 1 <;> decide
  targetTyping := by
    exact Presentation.HasType.var 1
  evidence := .rel (.nil (.var 5) (.var 4) (.var 3) (.var 2) (.var 1)
    (.var 0))

def contextABRPZSSourceHead : Tower.Ctx 7 :=
  .snoc contextABRPZS (.var 5)

def contextABRPZSSourceTargetHead : Tower.Ctx 8 :=
  .snoc contextABRPZSSourceHead (.var 5)

def contextABRPZSSourceTargetHeadSourceTail : Tower.Ctx 9 :=
  .snoc contextABRPZSSourceTargetHead (Intrinsic.listApp (.var 7))

def contextABRPZSSourceTargetHeadSourceTargetTail : Tower.Ctx 10 :=
  .snoc contextABRPZSSourceTargetHeadSourceTail
    (Intrinsic.listApp (.var 7))

def contextABRPZSSourceTargetHeadSourceTargetTailHead : Tower.Ctx 11 :=
  .snoc contextABRPZSSourceTargetHeadSourceTargetTail
    (.app (.app (.var 7) (.var 3)) (.var 2))

def contextABRPZSSourceTargetHeadSourceTargetTailHeadTail : Tower.Ctx 12 :=
  .snoc contextABRPZSSourceTargetHeadSourceTargetTailHead
    (mapRelApp (.var 10) (.var 9) (.var 8) (.var 2) (.var 1))

def eliminateAtConsParameters : Tower.Tm 12 :=
  weaken6 eliminateAtParameters

def eliminateAtConsParametersType : Tower.Tm 12 :=
  weaken6 eliminateAtParametersType

theorem eliminateAtConsParameters_hasType :
    HasType rules contextABRPZSSourceTargetHeadSourceTargetTailHeadTail
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

def consIotaLeft : Tower.Tm 12 :=
  .app
    (.app
      (.app eliminateAtConsParameters
        (Intrinsic.consApp (.var 11) (.var 5) (.var 3)))
      (Intrinsic.consApp (.var 10) (.var 4) (.var 2)))
    (consRelApp (.var 11) (.var 10) (.var 9)
      (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))

def consIotaRight : Tower.Tm 12 :=
  .app
    (.app
      (.app
        (.app
          (.app
            (.app
              (.app (.var 6) (.var 5))
              (.var 4))
            (.var 3))
          (.var 2))
        (.var 1))
      (.var 0))
    (.app
      (.app
        (.app eliminateAtConsParameters (.var 3))
        (.var 2))
      (.var 0))

def consIotaResultType : Tower.Tm 12 :=
  motiveApp (.var 8)
    (Intrinsic.consApp (.var 11) (.var 5) (.var 3))
    (Intrinsic.consApp (.var 10) (.var 4) (.var 2))
    (consRelApp (.var 11) (.var 10) (.var 9)
      (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))

def consIotaReceipt :
    TypedIotaReceipt
      contextABRPZSSourceTargetHeadSourceTargetTailHeadTail
      consIotaLeft consIotaRight consIotaResultType where
  sourceTyping := by
    have sourceTyping : HasType rules
        contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 11)
        (sortTm Intrinsic.elementLevel) :=
      Presentation.HasType.var 11
    have targetTyping : HasType rules
        contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 10)
        (sortTm Intrinsic.elementLevel) :=
      Presentation.HasType.var 10
    have sourceHeadTyping : HasType rules
        contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 5)
        (.var 11) := Presentation.HasType.var 5
    have targetHeadTyping : HasType rules
        contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 4)
        (.var 10) := Presentation.HasType.var 4
    have sourceTailTyping : HasType rules
        contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 3)
        (Intrinsic.listApp (.var 11)) := Presentation.HasType.var 3
    have targetTailTyping : HasType rules
        contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 2)
        (Intrinsic.listApp (.var 10)) := Presentation.HasType.var 2
    have headEvidenceTyping : HasType rules
        contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 1)
        (.app (.app (.var 9) (.var 5)) (.var 4)) :=
      Presentation.HasType.var 1
    have tailEvidenceTyping : HasType rules
        contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 0)
        (mapRelApp (.var 11) (.var 10) (.var 9) (.var 3) (.var 2)) :=
      Presentation.HasType.var 0
    have sourceListTyping := consApp_hasType sourceTyping sourceHeadTyping
      sourceTailTyping
    have targetListTyping := consApp_hasType targetTyping targetHeadTyping
      targetTailTyping
    have evidenceTyping := consRelApp_hasType sourceTyping targetTyping
      (Presentation.HasType.var 9) sourceHeadTyping targetHeadTyping
      sourceTailTyping targetTailTyping headEvidenceTyping tailEvidenceTyping
    have afterSource := Presentation.HasType.appElim
      eliminateAtConsParameters_hasType sourceListTyping
    have afterTarget := Presentation.HasType.appElim afterSource
      targetListTyping
    have result := Presentation.HasType.appElim afterTarget evidenceTyping
    convert result using 1 <;> decide
  targetTyping := by
    have sourceHeadTyping : HasType rules
        contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 5)
        (.var 11) := Presentation.HasType.var 5
    have targetHeadTyping : HasType rules
        contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 4)
        (.var 10) := Presentation.HasType.var 4
    have sourceTailTyping : HasType rules
        contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 3)
        (Intrinsic.listApp (.var 11)) := Presentation.HasType.var 3
    have targetTailTyping : HasType rules
        contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 2)
        (Intrinsic.listApp (.var 10)) := Presentation.HasType.var 2
    have headEvidenceTyping : HasType rules
        contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 1)
        (.app (.app (.var 9) (.var 5)) (.var 4)) :=
      Presentation.HasType.var 1
    have tailEvidenceTyping : HasType rules
        contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 0)
        (mapRelApp (.var 11) (.var 10) (.var 9) (.var 3) (.var 2)) :=
      Presentation.HasType.var 0
    have consCaseTyping : HasType rules
        contextABRPZSSourceTargetHeadSourceTargetTailHeadTail (.var 6)
        (Presentation.rename wk (weaken6 consCaseType)) :=
      Presentation.HasType.var 6
    have recursiveAfterSource := Presentation.HasType.appElim
      eliminateAtConsParameters_hasType sourceTailTyping
    have recursiveAfterTarget := Presentation.HasType.appElim
      recursiveAfterSource targetTailTyping
    have recursiveTyping := Presentation.HasType.appElim
      recursiveAfterTarget tailEvidenceTyping
    have afterSourceHead := Presentation.HasType.appElim consCaseTyping
      sourceHeadTyping
    have afterTargetHead := Presentation.HasType.appElim afterSourceHead
      targetHeadTyping
    have afterSourceTail := Presentation.HasType.appElim afterTargetHead
      sourceTailTyping
    have afterTargetTail := Presentation.HasType.appElim afterSourceTail
      targetTailTyping
    have afterHeadEvidence := Presentation.HasType.appElim afterTargetTail
      headEvidenceTyping
    have afterTailEvidence := Presentation.HasType.appElim afterHeadEvidence
      tailEvidenceTyping
    have result := Presentation.HasType.appElim afterTailEvidence
      recursiveTyping
    convert result using 1 <;> decide
  evidence := .rel (.cons (.var 11) (.var 10) (.var 9) (.var 8)
    (.var 7) (.var 6) (.var 5) (.var 4) (.var 3) (.var 2) (.var 1)
    (.var 0))

/-! ## Structural positivity -/

def freeListApp {element : Tower.Tm n}
    (elementFree : FreeOf mapRelName element) :
    FreeOf mapRelName (Intrinsic.listApp element) :=
  .app (.const (by decide)) elementFree

def freeNilApp {element : Tower.Tm n}
    (elementFree : FreeOf mapRelName element) :
    FreeOf mapRelName (Intrinsic.nilApp element) :=
  .app (.const (by decide)) elementFree

def freeConsApp {element head tail : Tower.Tm n}
    (elementFree : FreeOf mapRelName element)
    (headFree : FreeOf mapRelName head)
    (tailFree : FreeOf mapRelName tail) :
    FreeOf mapRelName (Intrinsic.consApp element head tail) :=
  .app (.app (.app (.const (by decide)) elementFree) headFree) tailFree

def freeRelationApplication {relation source target : Tower.Tm n}
    (relationFree : FreeOf mapRelName relation)
    (sourceFree : FreeOf mapRelName source)
    (targetFree : FreeOf mapRelName target) :
    FreeOf mapRelName (.app (.app relation source) target) :=
  .app (.app relationFree sourceFree) targetFree

def mapRelFamilyApplication
    (source target relation sourceList targetList : Tower.Tm n)
    (sourceFree : FreeOf mapRelName source)
    (targetFree : FreeOf mapRelName target)
    (relationFree : FreeOf mapRelName relation)
    (sourceListFree : FreeOf mapRelName sourceList)
    (targetListFree : FreeOf mapRelName targetList) :
    FamilyApplication mapRelName 5
      (mapRelApp source target relation sourceList targetList) :=
  .intro [source, target, relation, sourceList, targetList] rfl (by
    intro argument membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl
    · exact sourceFree
    · exact targetFree
    · exact relationFree
    · exact sourceListFree
    · exact targetListFree) rfl

def relationTypeFree : FreeOf mapRelName relationType := by
  unfold relationType
  exact .pi (.var 1) (.pi (.var 1) (.head _))

/-- `nilRel` is a constructor of the full five-argument family, not a bare
family constant or an endpoint-only proposition. -/
def nilRelConstructorPositive :
    ConstructorType mapRelName 5 nilRelType := by
  unfold nilRelType nilRelBodyType
  exact .field (.free (.head _))
    (.field (.free (.head _))
      (.field (.free relationTypeFree)
        (.result
          (mapRelFamilyApplication (.var 2) (.var 1) (.var 0)
            (Intrinsic.nilApp (.var 2)) (Intrinsic.nilApp (.var 1))
            (.var 2) (.var 1) (.var 0)
            (freeNilApp (.var 2)) (freeNilApp (.var 1))))))

/-- The cons constructor is strictly positive.  Its recursive evidence field
is a complete five-argument family application; the head relation evidence
is family-free. -/
def consRelConstructorPositive :
    ConstructorType mapRelName 5 consRelType := by
  unfold consRelType consRelBodyType
  exact .field (.free (.head _))
    (.field (.free (.head _))
      (.field (.free relationTypeFree)
        (.field (.free (.var 2))
          (.field (.free (.var 2))
            (.field (.free (freeListApp (.var 4)))
              (.field (.free (freeListApp (.var 4)))
                (.field
                  (.free
                    (freeRelationApplication (.var 4) (.var 3) (.var 2)))
                  (.field
                    (.recursive
                      (mapRelFamilyApplication
                        (.var 7) (.var 6) (.var 5) (.var 2) (.var 1)
                        (.var 7) (.var 6) (.var 5) (.var 2) (.var 1)))
                    (.result
                      (mapRelFamilyApplication
                        (.var 8) (.var 7) (.var 6)
                        (Intrinsic.consApp (.var 8) (.var 5) (.var 3))
                        (Intrinsic.consApp (.var 7) (.var 4) (.var 2))
                        (.var 8) (.var 7) (.var 6)
                        (freeConsApp (.var 8) (.var 5) (.var 3))
                        (freeConsApp (.var 7) (.var 4) (.var 2))))))))))))

def nilRelConstructorSpec :
    ConstructorSpec rawSignature mapRelName 5 where
  name := nilRelName
  type := nilRelType
  declared := typeOf_nilRel
  positive := nilRelConstructorPositive

def consRelConstructorSpec :
    ConstructorSpec rawSignature mapRelName 5 where
  name := consRelName
  type := consRelType
  declared := typeOf_consRel
  positive := consRelConstructorPositive

def mapRelConstructors :
    List (ConstructorSpec rawSignature mapRelName 5) :=
  [nilRelConstructorSpec, consRelConstructorSpec]

def mapRelEliminatorSpec : EliminatorSpec rawSignature where
  name := eliminateName
  type := eliminateType
  declared := typeOf_eliminate

def nilIotaSchema :
    IotaSchema Tower.rules rawSignature combinedProofRelevantIotaComputation
      6 where
  context := contextABRPZS
  left := nilIotaLeft
  right := nilIotaRight
  type := nilIotaResultType
  receipt := nilIotaReceipt

def consIotaSchema :
    IotaSchema Tower.rules rawSignature combinedProofRelevantIotaComputation
      12 where
  context := contextABRPZSSourceTargetHeadSourceTargetTailHeadTail
  left := consIotaLeft
  right := consIotaRight
  type := consIotaResultType
  receipt := consIotaReceipt

def eliminateAtParameters_applicationHead :
    ApplicationHead eliminateName eliminateAtParameters :=
  .app (.app (.app (.app (.app (.app .const)))))

noncomputable def eliminateAtConsParameters_applicationHead :
    ApplicationHead eliminateName eliminateAtConsParameters := by
  unfold eliminateAtConsParameters weaken6 weaken5 weaken4 weaken3 weaken2
    weaken1
  exact ((((((eliminateAtParameters_applicationHead.rename wk).rename wk).rename
    wk).rename wk).rename wk).rename wk)

def nilRelApp_constantOccurrence
    (source target relation : Tower.Tm n) :
    ConstantOccurrence nilRelName (nilRelApp source target relation) :=
  .appFunction (.appFunction (.appFunction .here))

def consRelApp_constantOccurrence
    (source target relation sourceHead targetHead sourceTail targetTail
      headEvidence tailEvidence : Tower.Tm n) :
    ConstantOccurrence consRelName
      (consRelApp source target relation sourceHead targetHead sourceTail
        targetTail headEvidence tailEvidence) :=
  .appFunction
    (.appFunction
      (.appFunction
        (.appFunction
          (.appFunction
            (.appFunction
              (.appFunction
                (.appFunction
                  (.appFunction .here))))))))

def nilIotaClause :
    IotaClause Tower.rules rawSignature combinedProofRelevantIotaComputation
      (mapRelConstructors.map ConstructorSpec.name)
      mapRelEliminatorSpec.name where
  constructorName := nilRelName
  constructorDeclared := by
    simp [mapRelConstructors, nilRelConstructorSpec]
  arity := 6
  schema := nilIotaSchema
  eliminatorHead := .app (.app (.app eliminateAtParameters_applicationHead))
  constructorOccurrence :=
    .appArgument (nilRelApp_constantOccurrence (.var 5) (.var 4) (.var 3))

noncomputable def consIotaClause :
    IotaClause Tower.rules rawSignature combinedProofRelevantIotaComputation
      (mapRelConstructors.map ConstructorSpec.name)
      mapRelEliminatorSpec.name where
  constructorName := consRelName
  constructorDeclared := by
    simp [mapRelConstructors, nilRelConstructorSpec, consRelConstructorSpec]
  arity := 12
  schema := consIotaSchema
  eliminatorHead := .app (.app (.app eliminateAtConsParameters_applicationHead))
  constructorOccurrence :=
    .appArgument
      (consRelApp_constantOccurrence (.var 11) (.var 10) (.var 9)
        (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))

noncomputable def mapRelIotaClauses :
    List
      (IotaClause Tower.rules rawSignature combinedProofRelevantIotaComputation
        (mapRelConstructors.map ConstructorSpec.name)
        mapRelEliminatorSpec.name) :=
  [nilIotaClause, consIotaClause]

noncomputable def mapRelCandidate : Candidate Tower.rules where
  signature := rawSignature
  formed := rawSignature_formed
  computation := combinedProofRelevantIotaComputation
  computationSupport := rfl
  familyName := mapRelName
  familyParameterCount := 3
  familyIndexCount := 2
  familyType := mapRelType
  familyDeclared := typeOf_mapRel
  constructors := mapRelConstructors
  constructorNamesNodup := by
    change [nilRelName, consRelName].Nodup
    decide
  familyNotConstructor := by
    intro constructor membership
    simp only [mapRelConstructors, List.mem_cons, List.not_mem_nil, or_false]
      at membership
    rcases membership with rfl | rfl <;> decide
  eliminator := mapRelEliminatorSpec
  eliminatorNotFamily := by decide
  eliminatorNotConstructor := by
    intro constructor membership
    simp only [mapRelConstructors, List.mem_cons, List.not_mem_nil, or_false]
      at membership
    rcases membership with rfl | rfl <;> decide
  iotaClauses := mapRelIotaClauses
  constructorsComputed := by
    intro constructorName membership
    simp [mapRelConstructors, nilRelConstructorSpec, consRelConstructorSpec]
      at membership
    rcases membership with rfl | rfl <;>
      simp [mapRelIotaClauses, nilIotaClause, consIotaClause]

/-! ## Positive and negative controls -/

def canonicalNilFamilyApplication :
    FamilyApplication mapRelName 5 nilRelBodyType := by
  unfold nilRelBodyType
  exact mapRelFamilyApplication (.var 2) (.var 1) (.var 0)
    (Intrinsic.nilApp (.var 2)) (Intrinsic.nilApp (.var 1))
    (.var 2) (.var 1) (.var 0)
    (freeNilApp (.var 2)) (freeNilApp (.var 1))

def recursiveDomainCanary : Tower.Tm 5 :=
  mapRelApp (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

def recursiveDomainApplication :
    FamilyApplication mapRelName 5 recursiveDomainCanary := by
  unfold recursiveDomainCanary
  exact mapRelFamilyApplication (.var 4) (.var 3) (.var 2) (.var 1)
    (.var 0) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

theorem recursiveMapRelInFunctionDomain_not_strictlyPositive :
    StrictlyPositive mapRelName 5
      (.pi recursiveDomainCanary (.var 0)) → False := by
  exact recursivePiDomain_not_strictlyPositive recursiveDomainApplication
    (.var 0)

def partialMapRelApplication : Tower.Tm 0 :=
  .app (.const mapRelName) (sortTm Intrinsic.elementLevel)

/-- Number of arguments on the outer application spine. -/
def applicationSpineLength : Tower.Tm n → Nat
  | .app function _ => applicationSpineLength function + 1
  | _ => 0

theorem applicationSpineLength_applyArgs (function : Tower.Tm n)
    (arguments : List (Tower.Tm n)) :
    applicationSpineLength (applyArgs function arguments) =
      applicationSpineLength function + arguments.length := by
  induction arguments generalizing function with
  | nil => simp [applyArgs]
  | cons argument rest ih =>
      rw [applyArgs_cons, ih]
      simp only [applicationSpineLength, List.length_cons]
      omega

theorem partialMapRelApplication_not_familyApplication :
    FamilyApplication mapRelName 5 partialMapRelApplication → False := by
  rintro ⟨arguments, length, _free, equation⟩
  have spineEquality := congrArg applicationSpineLength equation
  rw [applicationSpineLength_applyArgs] at spineEquality
  simp [partialMapRelApplication, applicationSpineLength, length]
    at spineEquality

/-! ## Axiom audit -/

#print axioms mapRelFamilyApplication
#print axioms nilRelConstructorPositive
#print axioms consRelConstructorPositive
#print axioms motiveApp_hasType
#print axioms consRelApp_hasType
#print axioms motiveType_hasType
#print axioms consCaseType_hasType
#print axioms eliminateType_hasType
#print axioms rawSignature_formed
#print axioms nilIotaReceipt
#print axioms consIotaReceipt
#print axioms mapRelCandidate
#print axioms canonicalNilFamilyApplication
#print axioms recursiveMapRelInFunctionDomain_not_strictlyPositive
#print axioms partialMapRelApplication_not_familyApplication

end IntrinsicRelator
end NativeIndexedFamilies
end Mettapedia.Languages.MeTTa.PureKernel.Universe
