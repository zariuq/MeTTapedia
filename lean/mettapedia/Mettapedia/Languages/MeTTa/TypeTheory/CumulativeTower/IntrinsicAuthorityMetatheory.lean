import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.IntrinsicReceiptMetatheory

/-!
# Intrinsic authority values

This module prepares the object-language authority layer above intrinsic
outcomes, runs, and receipts.  It first installs a native empty family: sound
negative authority evidence must eliminate an asserted judgment into an
actually empty type, not into a Boolean flag or a metalanguage proposition.

The authority record is then ordinary dependent data.  It retains an outcome
signature, a family expressing what each judgment means, and proof-relevant
positive and negative soundness maps.  The construction is universe
stratified and guest-independent.  External Lean authorities are models of
these values; they are not definitions of the object-language notion.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace InternalAuthorityMetatheory
namespace Intrinsic

open Presentation
open Presentation.SchemaElaboration
open Presentation.Declaration
open Presentation.Declaration.ComputationAuthority
open Presentation.Declaration.IndexedFamily

/-! ## A native empty family -/

def emptyLevel : LevelExpr := .param 13
def emptyMotiveLevel : LevelExpr := .param 14

def emptyName : DeclName := `Prime.Empty
def emptyEliminateName : DeclName := `Prime.Empty.eliminate

def emptyType : Tower.Tm 0 := sortTm emptyLevel

def emptyEliminateBodyType : Tower.Tm 1 :=
  .pi (.const emptyName) (.var 1)

def emptyEliminateType : Tower.Tm 0 :=
  .pi (sortTm emptyMotiveLevel) emptyEliminateBodyType

/-- Empty has no computation generators because it has no constructors. -/
inductive EmptyIotaEvidence (n : Nat) :
    Tower.Tm n → Tower.Tm n → Type

def EmptyIotaEvidence.rename {left right : Tower.Tm n}
    (evidence : EmptyIotaEvidence n left right) (renameMap : Ren n m) :
    EmptyIotaEvidence m (Presentation.rename renameMap left)
      (Presentation.rename renameMap right) :=
  nomatch evidence

def EmptyIotaEvidence.substitute {left right : Tower.Tm n}
    (evidence : EmptyIotaEvidence n left right)
    (substitution : Sub Tower.Head n m) :
    EmptyIotaEvidence m (Presentation.subst substitution left)
      (Presentation.subst substitution right) :=
  nomatch evidence

def proofRelevantEmptyComputation :
    ProofRelevantRootComputation Tower.Head where
  Evidence := EmptyIotaEvidence _
  rename := by
    intro n m renameMap left right evidence
    exact evidence.rename renameMap
  substitute := by
    intro n m substitution left right evidence
    exact evidence.substitute substitution

def emptyComputation : RootComputation Tower.Head :=
  proofRelevantEmptyComputation.support

def emptyDeclarations : List (DeclName × Entry Tower.Head) :=
  [(emptyName, { type := emptyType }),
   (emptyEliminateName, { type := emptyEliminateType })]

def rawEmptySignature : Signature Tower.Head where
  entries := (Signature.ofList emptyDeclarations).entries
  computation := emptyComputation

abbrev emptyRules : Rules Tower.Head :=
  extendRules receiptRules rawEmptySignature

@[simp] theorem typeOf_empty :
    rawEmptySignature.typeOf? emptyName = some emptyType := by
  simp [rawEmptySignature, emptyDeclarations, emptyName,
    emptyEliminateName, Signature.ofList, Signature.insert,
    Signature.typeOf?]

@[simp] theorem typeOf_emptyEliminate :
    rawEmptySignature.typeOf? emptyEliminateName =
      some emptyEliminateType := by
  simp [rawEmptySignature, emptyDeclarations, emptyName,
    emptyEliminateName, Signature.ofList, Signature.insert,
    Signature.typeOf?]

abbrev EmptyHasType {n : Nat} :=
  @Presentation.HasType Tower.Head emptyRules n

def includeReceiptTyping {context : Tower.Ctx n}
    {term type : Tower.Tm n}
    (typing : ReceiptHasType context term type) :
    EmptyHasType context term type :=
  Presentation.Declaration.HasType.includeSignature receiptRules
    rawEmptySignature typing

private theorem declaredEmptyConstant_hasType
    {name : DeclName} {type : Tower.Tm 0}
    (lookup : rawEmptySignature.typeOf? name = some type)
    {context : Tower.Ctx n} :
    EmptyHasType context (.const name) (liftClosed type) := by
  apply Presentation.HasType.const
  change combinedType receiptRules rawEmptySignature name = some type
  apply combinedType_of_signature
  · by_cases isEmpty : name = emptyName
    · subst name
      simp [receiptRules, runRules, outcomeRules, extendRules, combinedType,
        Tower.rules, rawReceiptSignature, receiptDeclarations,
        rawRunSignature, runDeclarations, rawOutcomeSignature,
        outcomeDeclarations, emptyName, receiptName, receiptMakeName,
        receiptEliminateName, runName, runOkName, runFaultName,
        runEliminateName, outcomeName, establishedName, refutedName,
        outsideFragmentName, incompleteName, outcomeEliminateName,
        Signature.typeOf?, Signature.ofList, Signature.insert,
        Signature.empty]
    by_cases isEliminate : name = emptyEliminateName
    · subst name
      simp [receiptRules, runRules, outcomeRules, extendRules, combinedType,
        Tower.rules, rawReceiptSignature, receiptDeclarations,
        rawRunSignature, runDeclarations, rawOutcomeSignature,
        outcomeDeclarations, emptyEliminateName, receiptName,
        receiptMakeName, receiptEliminateName, runName, runOkName,
        runFaultName, runEliminateName, outcomeName, establishedName,
        refutedName, outsideFragmentName, incompleteName,
        outcomeEliminateName, Signature.typeOf?, Signature.ofList,
        Signature.insert, Signature.empty]
    · simp [rawEmptySignature, emptyDeclarations, Signature.typeOf?,
        Signature.ofList, Signature.insert, Signature.empty, isEmpty,
        isEliminate] at lookup
  · exact lookup

theorem emptyConstant_hasType {context : Tower.Ctx n} :
    EmptyHasType context (.const emptyName) (liftClosed emptyType) :=
  declaredEmptyConstant_hasType typeOf_empty

theorem emptyEliminateConstant_hasType {context : Tower.Ctx n} :
    EmptyHasType context (.const emptyEliminateName)
      (liftClosed emptyEliminateType) :=
  declaredEmptyConstant_hasType typeOf_emptyEliminate

def emptyEliminateBodyLevel : LevelExpr :=
  .max emptyLevel emptyMotiveLevel

def emptyEliminateDeclarationLevel : LevelExpr :=
  .max (.succ emptyMotiveLevel) emptyEliminateBodyLevel

def emptyContextX : Tower.Ctx 1 :=
  .snoc .nil (sortTm emptyMotiveLevel)

theorem emptyType_hasType :
    EmptyHasType (.nil : Tower.Ctx 0) emptyType
      (sortTm (.succ emptyLevel)) := by
  exact Presentation.HasType.headType (Tower.HeadTyping.sort emptyLevel)

theorem emptyEliminateBodyType_hasType :
    EmptyHasType emptyContextX emptyEliminateBodyType
      (sortTm emptyEliminateBodyLevel) := by
  unfold emptyContextX emptyEliminateBodyType emptyEliminateBodyLevel
  apply Presentation.HasType.piForm
  · simpa [emptyType, liftClosed, sortTm, Presentation.rename] using
      (emptyConstant_hasType (context :=
        (.snoc (.nil : Tower.Ctx 0) (sortTm emptyMotiveLevel))))
  · exact Tower.IsUniverse.sort emptyLevel
  · exact Presentation.HasType.var 1
  · exact Tower.IsUniverse.sort emptyMotiveLevel
  · exact Tower.Join.sorts emptyLevel emptyMotiveLevel

theorem emptyEliminateType_hasType :
    EmptyHasType (.nil : Tower.Ctx 0) emptyEliminateType
      (sortTm emptyEliminateDeclarationLevel) := by
  unfold emptyEliminateType emptyEliminateDeclarationLevel
  apply Presentation.HasType.piForm
      (Presentation.HasType.headType
        (Tower.HeadTyping.sort emptyMotiveLevel))
      (Tower.IsUniverse.sort (.succ emptyMotiveLevel))
  · exact emptyEliminateBodyType_hasType
  · exact Tower.IsUniverse.sort emptyEliminateBodyLevel
  · exact Tower.Join.sorts (.succ emptyMotiveLevel)
      emptyEliminateBodyLevel

@[simp] theorem rawEmptySignature_valueOf_none (name : DeclName) :
    rawEmptySignature.valueOf? name = none := by
  by_cases isEmpty : name = emptyName
  · subst name
    simp [rawEmptySignature, emptyDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty]
  by_cases isEliminate : name = emptyEliminateName
  · subst name
    simp [rawEmptySignature, emptyDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isEmpty]
  · simp [rawEmptySignature, emptyDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isEmpty,
      isEliminate]

theorem rawEmptySignature_types_formed {name : DeclName}
    {type : Tower.Tm 0}
    (lookup : rawEmptySignature.typeOf? name = some type) :
    ∃ level : Tower.Head,
      receiptRules.isUniverse level ∧
      EmptyHasType (.nil : Tower.Ctx 0) type (.head level) := by
  by_cases isEmpty : name = emptyName
  · subst name
    have typeEquality : type = emptyType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort (.succ emptyLevel), .sort (.succ emptyLevel),
      emptyType_hasType⟩
  by_cases isEliminate : name = emptyEliminateName
  · subst name
    have typeEquality : type = emptyEliminateType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort emptyEliminateDeclarationLevel,
      .sort emptyEliminateDeclarationLevel,
      emptyEliminateType_hasType⟩
  · simp [rawEmptySignature, emptyDeclarations, Signature.typeOf?,
      Signature.ofList, Signature.insert, Signature.empty, isEmpty,
      isEliminate] at lookup

theorem rawEmptySignature_fresh {name : DeclName}
    {entry : Entry Tower.Head}
    (lookup : rawEmptySignature.entries name = some entry) :
    receiptRules.constantType name = none := by
  by_cases isEmpty : name = emptyName
  · subst name
    simp [receiptRules, runRules, outcomeRules, extendRules, combinedType,
      Tower.rules, rawReceiptSignature, receiptDeclarations,
      rawRunSignature, runDeclarations, rawOutcomeSignature,
      outcomeDeclarations, emptyName, receiptName, receiptMakeName,
      receiptEliminateName, runName, runOkName, runFaultName,
      runEliminateName, outcomeName, establishedName, refutedName,
      outsideFragmentName, incompleteName, outcomeEliminateName,
      Signature.typeOf?, Signature.ofList, Signature.insert,
      Signature.empty]
  by_cases isEliminate : name = emptyEliminateName
  · subst name
    simp [receiptRules, runRules, outcomeRules, extendRules, combinedType,
      Tower.rules, rawReceiptSignature, receiptDeclarations,
      rawRunSignature, runDeclarations, rawOutcomeSignature,
      outcomeDeclarations, emptyEliminateName, receiptName,
      receiptMakeName, receiptEliminateName, runName, runOkName,
      runFaultName, runEliminateName, outcomeName, establishedName,
      refutedName, outsideFragmentName, incompleteName,
      outcomeEliminateName, Signature.typeOf?, Signature.ofList,
      Signature.insert, Signature.empty]
  · simp [rawEmptySignature, emptyDeclarations, Signature.ofList,
      Signature.insert, Signature.empty, isEmpty, isEliminate] at lookup

def rawEmptySignature_formed : rawEmptySignature.Formed receiptRules where
  fresh := rawEmptySignature_fresh
  types := rawEmptySignature_types_formed
  values := by
    intro name type value _typeLookup valueLookup
    rw [rawEmptySignature_valueOf_none] at valueLookup
    cases valueLookup
  noSelfDelta := by
    intro name value valueLookup
    rw [rawEmptySignature_valueOf_none] at valueLookup
    cases valueLookup

def emptyEliminatorSpec : EliminatorSpec rawEmptySignature where
  name := emptyEliminateName
  type := emptyEliminateType
  declared := typeOf_emptyEliminate

def emptyConstructors :
    List (ConstructorSpec rawEmptySignature emptyName 0) :=
  []

noncomputable def emptyIotaClauses :
    List (IotaClause receiptRules rawEmptySignature
      proofRelevantEmptyComputation
      (emptyConstructors.map ConstructorSpec.name)
      emptyEliminatorSpec.name) :=
  []

/-- Empty is a genuine zero-constructor family.  Its eliminator is formed,
but there is no fabricated computation rule or inhabitant. -/
noncomputable def emptyCandidate : Candidate receiptRules where
  signature := rawEmptySignature
  formed := rawEmptySignature_formed
  computation := proofRelevantEmptyComputation
  computationSupport := rfl
  familyName := emptyName
  familyParameterCount := 0
  familyIndexCount := 0
  familyType := emptyType
  familyDeclared := typeOf_empty
  constructors := emptyConstructors
  constructorNamesNodup := by simp [emptyConstructors]
  familyNotConstructor := by simp [emptyConstructors]
  eliminator := emptyEliminatorSpec
  eliminatorNotFamily := by decide
  eliminatorNotConstructor := by simp [emptyConstructors]
  iotaClauses := emptyIotaClauses
  constructorsComputed := by simp [emptyConstructors]

/-- Positive control: from an assumed empty inhabitant, the native eliminator
produces a term in any selected motive. -/
def emptyContextXE : Tower.Ctx 2 :=
  .snoc emptyContextX (.const emptyName)

def emptyEliminateExample : Tower.Tm 2 :=
  .app (.app (.const emptyEliminateName) (.var 1)) (.var 0)

theorem emptyEliminateExample_hasType :
    EmptyHasType emptyContextXE emptyEliminateExample (.var 1) := by
  have afterMotive := Presentation.HasType.appElim
    (emptyEliminateConstant_hasType (context := emptyContextXE))
    (Presentation.HasType.var 1)
  have eliminated := Presentation.HasType.appElim afterMotive
    (Presentation.HasType.var 0)
  convert eliminated using 1
  all_goals decide

/-- Negative control: the declaration exposes no constructor name at all. -/
theorem empty_has_no_constructor
    (name : DeclName) :
    name ∉ emptyConstructors.map ConstructorSpec.name := by
  simp [emptyConstructors]

/-! ## Sound first-class authority records -/

/-- The meaning assigned to a judgment may inhabit a universe independent of
the positive and negative evidence families. -/
def authorityHoldsLevel : LevelExpr := .param 15

def authorityEvidenceTailLevel : LevelExpr :=
  .max evidenceLevel authorityHoldsLevel

def authorityEvidenceSoundLevel : LevelExpr :=
  .max judgmentLevel authorityEvidenceTailLevel

def authorityObstructionEmptyLevel : LevelExpr :=
  .max authorityHoldsLevel emptyLevel

def authorityObstructionTailLevel : LevelExpr :=
  .max obstructionLevel authorityObstructionEmptyLevel

def authorityObstructionSoundLevel : LevelExpr :=
  .max judgmentLevel authorityObstructionTailLevel

def authoritySoundnessBundleLevel : LevelExpr :=
  .max authorityEvidenceSoundLevel authorityObstructionSoundLevel

def authorityBodyLevel : LevelExpr :=
  .max (familyLevel authorityHoldsLevel) authoritySoundnessBundleLevel

def authoritySignatureLevel : LevelExpr :=
  .max signatureLevel authorityBodyLevel

/-- A meaning family for the judgments exposed by one outcome signature. -/
def authorityHoldsFamilyType (signature : Tower.Tm n) : Tower.Tm n :=
  familyType authorityHoldsLevel (signatureJudgment signature)

/-- Positive evidence must construct the judgment's meaning. -/
def authorityEvidenceSoundType (signature holds : Tower.Tm n) : Tower.Tm n :=
  .pi (signatureJudgment signature)
    (.pi
      (.app
        (signatureEvidence (Presentation.rename wk signature))
        (.var 0))
      (.app
        (Presentation.rename wk (Presentation.rename wk holds))
        (.var 1)))

/-- A checked obstruction and an asserted meaning eliminate into native
Empty.  This is data, not a hidden appeal to Lean's `Prop`. -/
def authorityObstructionSoundType
    (signature holds : Tower.Tm n) : Tower.Tm n :=
  .pi (signatureJudgment signature)
    (.pi
      (.app
        (signatureObstruction (Presentation.rename wk signature))
        (.var 0))
      (.pi
        (.app
          (Presentation.rename wk
            (Presentation.rename wk holds))
          (.var 1))
        (.const emptyName)))

@[simp] theorem subst_liftSub_two_weaken_two
    (substitution : Sub Tower.Head n m) (term : Tower.Tm n) :
    Presentation.subst
        (Presentation.liftSub (Presentation.liftSub substitution))
        (Presentation.rename wk (Presentation.rename wk term)) =
      Presentation.rename wk
        (Presentation.rename wk
          (Presentation.subst substitution term)) := by
  rw [Presentation.subst_liftSub_wk, Presentation.subst_liftSub_wk]

@[simp] theorem liftSub_two_at_one
    (substitution : Sub Tower.Head n m) :
    Presentation.liftSub (Presentation.liftSub substitution) (1 : Fin (n + 2)) =
      (.var 1 : Tower.Tm (m + 2)) := by
  rfl

@[simp] theorem subst_authorityEvidenceSoundType
    (substitution : Sub Tower.Head n m) (signature holds : Tower.Tm n) :
    Presentation.subst substitution
        (authorityEvidenceSoundType signature holds) =
      authorityEvidenceSoundType
        (Presentation.subst substitution signature)
        (Presentation.subst substitution holds) := by
  simp [authorityEvidenceSoundType, Presentation.subst]
  calc
    Presentation.subst
          (Presentation.liftSub (Presentation.liftSub substitution))
          (Presentation.rename (fun i => wk (wk i)) holds) =
        Presentation.subst
          (Presentation.liftSub (Presentation.liftSub substitution))
          (Presentation.rename wk (Presentation.rename wk holds)) := by
            congr 1
            exact (Presentation.rename_comp wk wk holds).symm
    _ = Presentation.rename wk
          (Presentation.rename wk
            (Presentation.subst substitution holds)) :=
      subst_liftSub_two_weaken_two substitution holds
    _ = Presentation.rename (fun i => wk (wk i))
          (Presentation.subst substitution holds) :=
      Presentation.rename_comp wk wk
        (Presentation.subst substitution holds)

@[simp] theorem subst_authorityObstructionSoundType
    (substitution : Sub Tower.Head n m) (signature holds : Tower.Tm n) :
    Presentation.subst substitution
        (authorityObstructionSoundType signature holds) =
      authorityObstructionSoundType
        (Presentation.subst substitution signature)
        (Presentation.subst substitution holds) := by
  simp [authorityObstructionSoundType, Presentation.subst]
  calc
    Presentation.subst
          (Presentation.liftSub (Presentation.liftSub substitution))
          (Presentation.rename (fun i => wk (wk i)) holds) =
        Presentation.subst
          (Presentation.liftSub (Presentation.liftSub substitution))
          (Presentation.rename wk (Presentation.rename wk holds)) := by
            congr 1
            exact (Presentation.rename_comp wk wk holds).symm
    _ = Presentation.rename wk
          (Presentation.rename wk
            (Presentation.subst substitution holds)) :=
      subst_liftSub_two_weaken_two substitution holds
    _ = Presentation.rename (fun i => wk (wk i))
          (Presentation.subst substitution holds) :=
      Presentation.rename_comp wk wk
        (Presentation.subst substitution holds)

/-- Below the outcome-signature field, authority is a dependent record of
meaning and the two polarity-specific soundness maps. -/
def authoritySignatureBody : Tower.Tm 1 :=
  .sigma (authorityHoldsFamilyType (.var 0))
    (.sigma (authorityEvidenceSoundType (.var 1) (.var 0))
      (authorityObstructionSoundType (.var 2) (.var 1)))

/-- A first-class authority is an informative extension of an outcome
signature, not a decision function. -/
def authoritySignatureType : Tower.Tm 0 :=
  .sigma outcomeSignatureType authoritySignatureBody

def authorityOutcomeSignature (authority : Tower.Tm n) : Tower.Tm n :=
  .fst authority

def authorityHolds (authority : Tower.Tm n) : Tower.Tm n :=
  .fst (.snd authority)

def authorityEvidenceSound (authority : Tower.Tm n) : Tower.Tm n :=
  .fst (.snd (.snd authority))

def authorityObstructionSound (authority : Tower.Tm n) : Tower.Tm n :=
  .snd (.snd (.snd authority))

@[simp] theorem rename_authorityHoldsFamilyType (renameMap : Ren n m)
    (signature : Tower.Tm n) :
    Presentation.rename renameMap (authorityHoldsFamilyType signature) =
      authorityHoldsFamilyType (Presentation.rename renameMap signature) :=
  rfl

@[simp] theorem subst_authorityHoldsFamilyType
    (substitution : Sub Tower.Head n m) (signature : Tower.Tm n) :
    Presentation.subst substitution (authorityHoldsFamilyType signature) =
      authorityHoldsFamilyType
        (Presentation.subst substitution signature) :=
  rfl

@[simp] theorem rename_authorityOutcomeSignature (renameMap : Ren n m)
    (authority : Tower.Tm n) :
    Presentation.rename renameMap (authorityOutcomeSignature authority) =
      authorityOutcomeSignature
        (Presentation.rename renameMap authority) :=
  rfl

@[simp] theorem rename_authorityHolds (renameMap : Ren n m)
    (authority : Tower.Tm n) :
    Presentation.rename renameMap (authorityHolds authority) =
      authorityHolds (Presentation.rename renameMap authority) :=
  rfl

@[simp] theorem rename_authorityEvidenceSound (renameMap : Ren n m)
    (authority : Tower.Tm n) :
    Presentation.rename renameMap (authorityEvidenceSound authority) =
      authorityEvidenceSound (Presentation.rename renameMap authority) :=
  rfl

@[simp] theorem rename_authorityObstructionSound (renameMap : Ren n m)
    (authority : Tower.Tm n) :
    Presentation.rename renameMap (authorityObstructionSound authority) =
      authorityObstructionSound
        (Presentation.rename renameMap authority) :=
  rfl

@[simp] theorem subst_authorityOutcomeSignature
    (substitution : Sub Tower.Head n m) (authority : Tower.Tm n) :
    Presentation.subst substitution (authorityOutcomeSignature authority) =
      authorityOutcomeSignature
        (Presentation.subst substitution authority) :=
  rfl

@[simp] theorem subst_authorityHolds
    (substitution : Sub Tower.Head n m) (authority : Tower.Tm n) :
    Presentation.subst substitution (authorityHolds authority) =
      authorityHolds (Presentation.subst substitution authority) :=
  rfl

@[simp] theorem subst_authorityEvidenceSound
    (substitution : Sub Tower.Head n m) (authority : Tower.Tm n) :
    Presentation.subst substitution (authorityEvidenceSound authority) =
      authorityEvidenceSound
        (Presentation.subst substitution authority) :=
  rfl

@[simp] theorem subst_authorityObstructionSound
    (substitution : Sub Tower.Head n m) (authority : Tower.Tm n) :
    Presentation.subst substitution (authorityObstructionSound authority) =
      authorityObstructionSound
        (Presentation.subst substitution authority) :=
  rfl

theorem outcomeSignatureType_hasEmptyType :
    EmptyHasType (.nil : Tower.Ctx 0) outcomeSignatureType
      (sortTm signatureLevel) :=
  includeReceiptTyping
    (includeRunTyping
      (includeOutcomeTyping outcomeSignatureType_hasIntrinsicType))

def authorityContextS : Tower.Ctx 1 :=
  .snoc .nil outcomeSignatureType

def authorityContextSH : Tower.Ctx 2 :=
  .snoc authorityContextS (authorityHoldsFamilyType (.var 0))

def authorityContextSHE : Tower.Ctx 3 :=
  .snoc authorityContextSH
    (authorityEvidenceSoundType (.var 1) (.var 0))

def authorityContextSHEO : Tower.Ctx 4 :=
  .snoc authorityContextSHE
    (authorityObstructionSoundType (.var 2) (.var 1))

theorem authoritySignatureVar_hasType :
    EmptyHasType authorityContextS (.var 0)
      (liftClosed outcomeSignatureType) := by
  have variableTyping :=
    (Presentation.HasType.var (R := emptyRules)
      (Γ := authorityContextS) (0 : Fin 1))
  have lookupEquality :
      Presentation.Ctx.lookup authorityContextS (0 : Fin 1) =
        liftClosed outcomeSignatureType := by
    decide
  simpa only [lookupEquality] using variableTyping

theorem familyType_hasEmptyType {context : Tower.Ctx n}
    (payload : LevelExpr) {judgmentType : Tower.Tm n}
    (judgmentTyping : EmptyHasType context judgmentType
      (sortTm judgmentLevel)) :
    EmptyHasType context (familyType payload judgmentType)
      (sortTm (familyLevel payload)) := by
  unfold familyType familyLevel
  apply Presentation.HasType.piForm judgmentTyping
      (Tower.IsUniverse.sort judgmentLevel)
  · exact Presentation.HasType.headType (Tower.HeadTyping.sort payload)
  · exact Tower.IsUniverse.sort (.succ payload)
  · exact Tower.Join.sorts judgmentLevel (.succ payload)

theorem authorityHoldsFamilyType_hasType :
    EmptyHasType authorityContextS
      (authorityHoldsFamilyType (.var 0))
      (sortTm (familyLevel authorityHoldsLevel)) := by
  apply familyType_hasEmptyType authorityHoldsLevel
  exact signatureJudgment_hasType authoritySignatureVar_hasType

theorem authorityEvidenceSoundType_hasType :
    EmptyHasType authorityContextSH
      (authorityEvidenceSoundType (.var 1) (.var 0))
      (sortTm authorityEvidenceSoundLevel) := by
  unfold authorityContextSH authorityContextS
    authorityEvidenceSoundType authorityEvidenceSoundLevel
    authorityEvidenceTailLevel
  apply Presentation.HasType.piForm
  · exact signatureJudgment_hasType
      (Presentation.HasType.var 1)
  · exact Tower.IsUniverse.sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply familyApp_hasType
      · exact signatureEvidence_hasType
          (Presentation.HasType.var 2)
      · exact Presentation.HasType.var 0
    · exact Tower.IsUniverse.sort evidenceLevel
    · apply familyApp_hasType
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · exact Tower.IsUniverse.sort authorityHoldsLevel
    · exact Tower.Join.sorts evidenceLevel authorityHoldsLevel
  · exact Tower.IsUniverse.sort authorityEvidenceTailLevel
  · exact Tower.Join.sorts judgmentLevel authorityEvidenceTailLevel

theorem authorityObstructionSoundType_hasType :
    EmptyHasType authorityContextSHE
      (authorityObstructionSoundType (.var 2) (.var 1))
      (sortTm authorityObstructionSoundLevel) := by
  unfold authorityContextSHE authorityContextSH authorityContextS
    authorityObstructionSoundType authorityObstructionSoundLevel
    authorityObstructionTailLevel authorityObstructionEmptyLevel
  apply Presentation.HasType.piForm
  · exact signatureJudgment_hasType
      (Presentation.HasType.var 2)
  · exact Tower.IsUniverse.sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply familyApp_hasType
      · exact signatureObstruction_hasType
          (Presentation.HasType.var 3)
      · exact Presentation.HasType.var 0
    · exact Tower.IsUniverse.sort obstructionLevel
    · apply Presentation.HasType.piForm
      · apply familyApp_hasType
        · exact Presentation.HasType.var 3
        · exact Presentation.HasType.var 1
      · exact Tower.IsUniverse.sort authorityHoldsLevel
      · simpa [emptyType, liftClosed, sortTm, Presentation.rename] using
          (emptyConstant_hasType (context := _))
      · exact Tower.IsUniverse.sort emptyLevel
      · exact Tower.Join.sorts authorityHoldsLevel emptyLevel
    · exact Tower.IsUniverse.sort authorityObstructionEmptyLevel
    · exact Tower.Join.sorts obstructionLevel
        authorityObstructionEmptyLevel
  · exact Tower.IsUniverse.sort authorityObstructionTailLevel
  · exact Tower.Join.sorts judgmentLevel authorityObstructionTailLevel

theorem authoritySignatureBody_hasType :
    EmptyHasType authorityContextS authoritySignatureBody
      (sortTm authorityBodyLevel) := by
  unfold authoritySignatureBody authorityBodyLevel
    authoritySoundnessBundleLevel
  apply Presentation.HasType.sigmaForm authorityHoldsFamilyType_hasType
      (Tower.IsUniverse.sort (familyLevel authorityHoldsLevel))
  · apply Presentation.HasType.sigmaForm
        authorityEvidenceSoundType_hasType
        (Tower.IsUniverse.sort authorityEvidenceSoundLevel)
    · exact authorityObstructionSoundType_hasType
    · exact Tower.IsUniverse.sort authorityObstructionSoundLevel
    · exact Tower.Join.sorts authorityEvidenceSoundLevel
        authorityObstructionSoundLevel
  · exact Tower.IsUniverse.sort authoritySoundnessBundleLevel
  · exact Tower.Join.sorts (familyLevel authorityHoldsLevel)
      authoritySoundnessBundleLevel

theorem authoritySignatureType_hasType :
    EmptyHasType (.nil : Tower.Ctx 0) authoritySignatureType
      (sortTm authoritySignatureLevel) := by
  unfold authoritySignatureType authoritySignatureLevel
  apply Presentation.HasType.sigmaForm outcomeSignatureType_hasEmptyType
      (Tower.IsUniverse.sort signatureLevel)
  · exact authoritySignatureBody_hasType
  · exact Tower.IsUniverse.sort authorityBodyLevel
  · exact Tower.Join.sorts signatureLevel authorityBodyLevel

/-- Positive control: independently typed authority components assemble into
one first-class value. -/
def parameterAuthorityValue : Tower.Tm 4 :=
  .pair (.var 3) (.pair (.var 2) (.pair (.var 1) (.var 0)))

theorem parameterAuthorityValue_hasType :
    EmptyHasType authorityContextSHEO parameterAuthorityValue
      (liftClosed authoritySignatureType) := by
  unfold parameterAuthorityValue authorityContextSHEO authorityContextSHE
    authorityContextSH authorityContextS authoritySignatureType
    authoritySignatureBody
  apply Presentation.HasType.pairIntro (Presentation.HasType.var 3)
  apply Presentation.HasType.pairIntro (Presentation.HasType.var 2)
  apply Presentation.HasType.pairIntro (Presentation.HasType.var 1)
  exact Presentation.HasType.var 0

/-! ### Projection and use laws -/

def authoritySoundnessBodyAfterOutcomeSignature
    (signature : Tower.Tm n) : Tower.Tm (n + 1) :=
  .sigma
    (authorityEvidenceSoundType
      (Presentation.rename wk signature) (.var 0))
    (authorityObstructionSoundType
      (Presentation.rename wk (Presentation.rename wk signature))
      (.var 1))

def authorityAfterOutcomeSignature
    (signature : Tower.Tm n) : Tower.Tm n :=
  .sigma (authorityHoldsFamilyType signature)
    (authoritySoundnessBodyAfterOutcomeSignature signature)

def authorityAfterHolds
    (signature holds : Tower.Tm n) : Tower.Tm n :=
  .sigma (authorityEvidenceSoundType signature holds)
    (authorityObstructionSoundType
      (Presentation.rename wk signature)
      (Presentation.rename wk holds))

theorem authoritySignatureBody_asSuccessiveTails :
    authoritySignatureBody = authorityAfterOutcomeSignature (.var 0) := by
  rfl

@[simp] theorem substitute_authoritySignatureBody
    (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature)
        authoritySignatureBody =
      authorityAfterOutcomeSignature signature := by
  rfl

@[simp] theorem substitute_authoritySoundnessBodyAfterOutcomeSignature
    (signature holds : Tower.Tm n) :
    Presentation.inst0 holds
        (authoritySoundnessBodyAfterOutcomeSignature signature) =
      authorityAfterHolds signature holds := by
  unfold authoritySoundnessBodyAfterOutcomeSignature authorityAfterHolds
  simp only [Presentation.inst0, Presentation.subst,
    subst_authorityEvidenceSoundType,
    subst_authorityObstructionSoundType, open_weakened_under_zero,
    open_weakened_under_one, Presentation.subst0_zero,
    liftSub_one_subst0_at_one]

theorem authorityOutcomeSignature_hasType {context : Tower.Ctx n}
    {authority : Tower.Tm n}
    (authorityTyping : EmptyHasType context authority
      (liftClosed authoritySignatureType)) :
    EmptyHasType context (authorityOutcomeSignature authority)
      (liftClosed outcomeSignatureType) := by
  have projection := Presentation.HasType.fstElim authorityTyping
  simpa [authorityOutcomeSignature, authoritySignatureType, liftClosed,
    sortTm, Presentation.rename] using projection

theorem authorityTail_hasType {context : Tower.Ctx n}
    {authority : Tower.Tm n}
    (authorityTyping : EmptyHasType context authority
      (liftClosed authoritySignatureType)) :
    EmptyHasType context (.snd authority)
      (authorityAfterOutcomeSignature
        (authorityOutcomeSignature authority)) := by
  have projection := Presentation.HasType.sndElim authorityTyping
  simpa only [authoritySignatureType, liftClosed,
    inst0_rename_liftRen_elim0, substitute_authoritySignatureBody,
    authorityOutcomeSignature] using projection

theorem authorityHolds_hasType {context : Tower.Ctx n}
    {authority : Tower.Tm n}
    (authorityTyping : EmptyHasType context authority
      (liftClosed authoritySignatureType)) :
    EmptyHasType context (authorityHolds authority)
      (authorityHoldsFamilyType
        (authorityOutcomeSignature authority)) := by
  have projection :=
    Presentation.HasType.fstElim (authorityTail_hasType authorityTyping)
  simpa [authorityHolds, authorityAfterOutcomeSignature] using projection

theorem authoritySoundnessTail_hasType {context : Tower.Ctx n}
    {authority : Tower.Tm n}
    (authorityTyping : EmptyHasType context authority
      (liftClosed authoritySignatureType)) :
    EmptyHasType context (.snd (.snd authority))
      (authorityAfterHolds (authorityOutcomeSignature authority)
        (authorityHolds authority)) := by
  have projection :=
    Presentation.HasType.sndElim (authorityTail_hasType authorityTyping)
  simpa only [authorityAfterOutcomeSignature,
    substitute_authoritySoundnessBodyAfterOutcomeSignature,
    authorityOutcomeSignature, authorityHolds] using projection

theorem authorityEvidenceSound_hasType {context : Tower.Ctx n}
    {authority : Tower.Tm n}
    (authorityTyping : EmptyHasType context authority
      (liftClosed authoritySignatureType)) :
    EmptyHasType context (authorityEvidenceSound authority)
      (authorityEvidenceSoundType
        (authorityOutcomeSignature authority)
        (authorityHolds authority)) := by
  have projection := Presentation.HasType.fstElim
    (authoritySoundnessTail_hasType authorityTyping)
  simpa [authorityEvidenceSound, authorityAfterHolds] using projection

theorem authorityObstructionSound_hasType {context : Tower.Ctx n}
    {authority : Tower.Tm n}
    (authorityTyping : EmptyHasType context authority
      (liftClosed authoritySignatureType)) :
    EmptyHasType context (authorityObstructionSound authority)
      (authorityObstructionSoundType
        (authorityOutcomeSignature authority)
        (authorityHolds authority)) := by
  have projection := Presentation.HasType.sndElim
    (authoritySoundnessTail_hasType authorityTyping)
  simpa [authorityObstructionSound, authorityAfterHolds,
    Presentation.inst0, Presentation.subst] using projection

@[simp] theorem inst0_signatureEvidenceApp_wk
    (argument signature : Tower.Tm n) :
    Presentation.inst0 argument
        (.app
          (signatureEvidence (Presentation.rename wk signature))
          (.var 0)) =
      .app (signatureEvidence signature) argument := by
  simp [Presentation.inst0, Presentation.subst]

@[simp] theorem inst0_signatureObstructionApp_wk
    (argument signature : Tower.Tm n) :
    Presentation.inst0 argument
        (.app
          (signatureObstruction (Presentation.rename wk signature))
          (.var 0)) =
      .app (signatureObstruction signature) argument := by
  simp [Presentation.inst0, Presentation.subst]

@[simp] theorem open_weakened_under_two_successive_arguments
    (laterArgument judgment term : Tower.Tm n) :
    Presentation.subst
        (fun i => Presentation.subst
          (Presentation.subst0 laterArgument)
          (Presentation.liftSub (Presentation.subst0 judgment) i))
        (Presentation.rename (fun i => wk (wk i)) term) =
      term := by
  calc
    Presentation.subst
          (fun i => Presentation.subst
            (Presentation.subst0 laterArgument)
            (Presentation.liftSub (Presentation.subst0 judgment) i))
          (Presentation.rename (fun i => wk (wk i)) term) =
        Presentation.subst
          (fun i => Presentation.subst
            (Presentation.subst0 laterArgument)
            (Presentation.liftSub (Presentation.subst0 judgment)
              ((fun j => wk (wk j)) i)))
          term := by
            exact Presentation.subst_rename _ _ term
    _ = Presentation.subst Presentation.ids term := by
      apply Presentation.subst_ext
      intro i
      rfl
    _ = term := Presentation.subst_ids term

@[simp] theorem instantiate_holdsApplication
    (laterArgument judgment holds : Tower.Tm n) :
    Presentation.inst0 laterArgument
        (Presentation.subst
          (Presentation.liftSub (Presentation.subst0 judgment))
          (.app
            (Presentation.rename wk (Presentation.rename wk holds))
            (.var 1))) =
      .app holds judgment := by
  simp [Presentation.inst0, Presentation.subst]

def authorityEvidenceSoundApp
    (authority judgment evidence : Tower.Tm n) : Tower.Tm n :=
  .app (.app (authorityEvidenceSound authority) judgment) evidence

def authorityObstructionSoundApp
    (authority judgment obstruction holds : Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app (authorityObstructionSound authority) judgment)
      obstruction)
    holds

theorem authorityEvidenceSoundApp_hasType {context : Tower.Ctx n}
    {authority judgment evidence : Tower.Tm n}
    (authorityTyping : EmptyHasType context authority
      (liftClosed authoritySignatureType))
    (judgmentTyping : EmptyHasType context judgment
      (signatureJudgment (authorityOutcomeSignature authority)))
    (evidenceTyping : EmptyHasType context evidence
      (.app
        (signatureEvidence (authorityOutcomeSignature authority))
        judgment)) :
    EmptyHasType context
      (authorityEvidenceSoundApp authority judgment evidence)
      (.app (authorityHolds authority) judgment) := by
  have afterJudgment := Presentation.HasType.appElim
    (authorityEvidenceSound_hasType authorityTyping) judgmentTyping
  have evidenceTypingOpened :
      EmptyHasType context evidence
        (Presentation.inst0 judgment
          (.app
            (signatureEvidence
              (Presentation.rename wk
                (authorityOutcomeSignature authority)))
            (.var 0))) := by
    simpa only [inst0_signatureEvidenceApp_wk] using evidenceTyping
  have afterEvidence := Presentation.HasType.appElim afterJudgment
    evidenceTypingOpened
  simpa [authorityEvidenceSoundApp, authorityEvidenceSoundType,
    Presentation.inst0, Presentation.subst] using afterEvidence

theorem authorityObstructionSoundApp_hasType {context : Tower.Ctx n}
    {authority judgment obstruction holds : Tower.Tm n}
    (authorityTyping : EmptyHasType context authority
      (liftClosed authoritySignatureType))
    (judgmentTyping : EmptyHasType context judgment
      (signatureJudgment (authorityOutcomeSignature authority)))
    (obstructionTyping : EmptyHasType context obstruction
      (.app
        (signatureObstruction (authorityOutcomeSignature authority))
        judgment))
    (holdsTyping : EmptyHasType context holds
      (.app (authorityHolds authority) judgment)) :
    EmptyHasType context
      (authorityObstructionSoundApp authority judgment obstruction holds)
      (.const emptyName) := by
  have afterJudgment := Presentation.HasType.appElim
    (authorityObstructionSound_hasType authorityTyping) judgmentTyping
  have obstructionTypingOpened :
      EmptyHasType context obstruction
        (Presentation.inst0 judgment
          (.app
            (signatureObstruction
              (Presentation.rename wk
                (authorityOutcomeSignature authority)))
            (.var 0))) := by
    simpa only [inst0_signatureObstructionApp_wk] using obstructionTyping
  have afterObstruction := Presentation.HasType.appElim afterJudgment
    obstructionTypingOpened
  have holdsTypingOpened :
      EmptyHasType context holds
        (Presentation.inst0 obstruction
          (Presentation.subst
            (Presentation.liftSub (Presentation.subst0 judgment))
            (.app
              (Presentation.rename wk
                (Presentation.rename wk
                  (authorityHolds authority)))
              (.var 1)))) := by
    simpa only [instantiate_holdsApplication] using holdsTyping
  have contradiction := Presentation.HasType.appElim afterObstruction
    holdsTypingOpened
  simpa [authorityObstructionSoundApp, authorityObstructionSoundType,
    Presentation.inst0, Presentation.subst] using contradiction

/-- A positive witness and checked obstruction for the same judgment yield a
native Empty term through the authority's two retained maps. -/
def authorityDisjointnessTerm
    (authority judgment evidence obstruction : Tower.Tm n) : Tower.Tm n :=
  authorityObstructionSoundApp authority judgment obstruction
    (authorityEvidenceSoundApp authority judgment evidence)

theorem authorityDisjointnessTerm_hasType {context : Tower.Ctx n}
    {authority judgment evidence obstruction : Tower.Tm n}
    (authorityTyping : EmptyHasType context authority
      (liftClosed authoritySignatureType))
    (judgmentTyping : EmptyHasType context judgment
      (signatureJudgment (authorityOutcomeSignature authority)))
    (evidenceTyping : EmptyHasType context evidence
      (.app
        (signatureEvidence (authorityOutcomeSignature authority))
        judgment))
    (obstructionTyping : EmptyHasType context obstruction
      (.app
        (signatureObstruction (authorityOutcomeSignature authority))
        judgment)) :
    EmptyHasType context
      (authorityDisjointnessTerm authority judgment evidence obstruction)
      (.const emptyName) := by
  apply authorityObstructionSoundApp_hasType authorityTyping judgmentTyping
    obstructionTyping
  exact authorityEvidenceSoundApp_hasType authorityTyping judgmentTyping
    evidenceTyping

/-! ## Axiom audit -/

#print axioms rawEmptySignature_formed
#print axioms emptyCandidate
#print axioms emptyEliminateExample_hasType
#print axioms empty_has_no_constructor
#print axioms authoritySignatureType_hasType
#print axioms parameterAuthorityValue_hasType
#print axioms authorityOutcomeSignature_hasType
#print axioms authorityEvidenceSoundApp_hasType
#print axioms authorityObstructionSoundApp_hasType
#print axioms authorityDisjointnessTerm_hasType

end Intrinsic
end InternalAuthorityMetatheory
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
