import Mettapedia.Languages.MeTTa.PureKernel.Universe.InternalAuthorityMetatheory

/-!
# Intrinsic authority runs

This module adds the operational layer above the intrinsic, evidence-bearing
`Outcome` family.  A run signature is first-class data consisting of an
outcome signature and a judgment-indexed family of operational faults.  The
successful constructor contains an intrinsic outcome; the fault constructor
is disjoint from it.  Thus failure surrounds semantic outcomes without
becoming a fifth semantic verdict.

The construction is generic in the outcome signature and fault family.  Prime
is one later interpretation, not a premise of the declaration.  As with the
intrinsic outcome family, formation, strict positivity, and exact typed iota
schemas produce a candidate.  Raw conversion authority remains separate.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe
namespace InternalAuthorityMetatheory
namespace Intrinsic

open Presentation
open Presentation.SchemaElaboration
open Presentation.Declaration
open Presentation.Declaration.ComputationAuthority
open Presentation.Declaration.IndexedFamily

/-! ## First-class run signatures -/

/-- Operational failure may live at a universe independent of every semantic
outcome payload. -/
def runFailureLevel : LevelExpr := .param 6

/-- Run elimination may target an independently selected universe. -/
def runMotiveLevel : LevelExpr := .param 7

/-- In context `outcomeSignature`, the remaining run-signature component is
the judgment-indexed operational-failure family. -/
def runSignatureBody : Tower.Tm 1 :=
  familyType runFailureLevel (signatureJudgment (.var 0))

/-- `RunSignature := Sigma (S : OutcomeSignature), S.J -> U failure`.
Keeping `S` intact makes every semantic payload family recoverable from a run
signature without duplicating it. -/
def runSignatureType : Tower.Tm 0 :=
  .sigma outcomeSignatureType runSignatureBody

def runSignatureLevel : LevelExpr :=
  .max signatureLevel (familyLevel runFailureLevel)

theorem runSignatureBody_hasType :
    IntrinsicHasType outcomeContextS runSignatureBody
      (sortTm (familyLevel runFailureLevel)) := by
  unfold runSignatureBody
  have signatureVariable :
      Tower.HasType outcomeContextS (.var 0)
        (liftClosed outcomeSignatureType) := by
    have variableTyping :=
      (Presentation.HasType.var (R := Tower.rules)
        (Γ := outcomeContextS) (0 : Fin 1))
    have lookupEquality :
        Presentation.Ctx.lookup outcomeContextS (0 : Fin 1) =
          liftClosed outcomeSignatureType := by
      decide
    simpa only [lookupEquality] using variableTyping
  have formedInTower := familyType_hasType runFailureLevel
    (signatureJudgment_hasType signatureVariable)
  exact Presentation.Declaration.HasType.includeSignature Tower.rules
    rawOutcomeSignature formedInTower

theorem runSignatureType_hasType :
    IntrinsicHasType (.nil : Tower.Ctx 0) runSignatureType
      (sortTm runSignatureLevel) := by
  unfold runSignatureType runSignatureLevel
  apply Presentation.HasType.sigmaForm
  · exact outcomeSignatureType_hasIntrinsicType
  · exact .sort signatureLevel
  · exact runSignatureBody_hasType
  · exact .sort (familyLevel runFailureLevel)
  · exact .sorts signatureLevel (familyLevel runFailureLevel)

def runSignatureContextSF : Tower.Ctx 2 :=
  .snoc outcomeContextS runSignatureBody

/-- Positive control: an outcome signature and a typed failure family form a
first-class run signature value. -/
def parameterRunSignatureValue : Tower.Tm 2 :=
  .pair (.var 1) (.var 0)

theorem parameterRunSignatureValue_hasType :
    IntrinsicHasType runSignatureContextSF parameterRunSignatureValue
      (liftClosed runSignatureType) := by
  unfold parameterRunSignatureValue runSignatureContextSF runSignatureBody
    runSignatureType outcomeContextS
  apply Presentation.HasType.pairIntro
  · exact Presentation.HasType.var 1
  · exact Presentation.HasType.var 0

/-- The semantic signature underlying one run signature. -/
def runOutcomeSignature (signature : Tower.Tm n) : Tower.Tm n :=
  .fst signature

/-- Operational faults are a judgment-indexed family, not a semantic outcome
constructor. -/
def runFailureFamily (signature : Tower.Tm n) : Tower.Tm n :=
  .snd signature

def runJudgment (signature : Tower.Tm n) : Tower.Tm n :=
  signatureJudgment (runOutcomeSignature signature)

@[simp] theorem rename_runOutcomeSignature (renameMap : Ren n m)
    (signature : Tower.Tm n) :
    Presentation.rename renameMap (runOutcomeSignature signature) =
      runOutcomeSignature (Presentation.rename renameMap signature) := rfl

@[simp] theorem rename_runFailureFamily (renameMap : Ren n m)
    (signature : Tower.Tm n) :
    Presentation.rename renameMap (runFailureFamily signature) =
      runFailureFamily (Presentation.rename renameMap signature) := rfl

@[simp] theorem rename_runJudgment (renameMap : Ren n m)
    (signature : Tower.Tm n) :
    Presentation.rename renameMap (runJudgment signature) =
      runJudgment (Presentation.rename renameMap signature) := rfl

@[simp] theorem subst_runOutcomeSignature
    (substitution : Sub Tower.Head n m) (signature : Tower.Tm n) :
    Presentation.subst substitution (runOutcomeSignature signature) =
      runOutcomeSignature (Presentation.subst substitution signature) := rfl

@[simp] theorem subst_runFailureFamily
    (substitution : Sub Tower.Head n m) (signature : Tower.Tm n) :
    Presentation.subst substitution (runFailureFamily signature) =
      runFailureFamily (Presentation.subst substitution signature) := rfl

@[simp] theorem subst_runJudgment
    (substitution : Sub Tower.Head n m) (signature : Tower.Tm n) :
    Presentation.subst substitution (runJudgment signature) =
      runJudgment (Presentation.subst substitution signature) := rfl

@[simp] theorem substitute_runSignatureBody
    (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature) runSignatureBody =
      familyType runFailureLevel
        (signatureJudgment signature) := by
  simp [runSignatureBody]

theorem runOutcomeSignature_hasType {rules : Rules Tower.Head}
    {context : Tower.Ctx n} {signature : Tower.Tm n}
    (signatureTyping : Presentation.HasType rules context signature
      (liftClosed runSignatureType)) :
    Presentation.HasType rules context (runOutcomeSignature signature)
      (liftClosed outcomeSignatureType) := by
  have projection := Presentation.HasType.fstElim signatureTyping
  simpa [runOutcomeSignature, runSignatureType, liftClosed,
    Presentation.rename] using projection

theorem runFailureFamily_hasType {rules : Rules Tower.Head}
    {context : Tower.Ctx n} {signature : Tower.Tm n}
    (signatureTyping : Presentation.HasType rules context signature
      (liftClosed runSignatureType)) :
    Presentation.HasType rules context (runFailureFamily signature)
      (familyType runFailureLevel (runJudgment signature)) := by
  have projection := Presentation.HasType.sndElim signatureTyping
  simpa only [runFailureFamily, runJudgment, runOutcomeSignature,
    runSignatureType, liftClosed, inst0_rename_liftRen_elim0,
    substitute_runSignatureBody] using projection

theorem runJudgment_hasType {rules : Rules Tower.Head}
    {context : Tower.Ctx n} {signature : Tower.Tm n}
    (signatureTyping : Presentation.HasType rules context signature
      (liftClosed runSignatureType)) :
    Presentation.HasType rules context (runJudgment signature)
      (sortTm judgmentLevel) :=
  signatureJudgment_hasType (runOutcomeSignature_hasType signatureTyping)

theorem runOutcomeApp_hasType {context : Tower.Ctx n}
    {signature judgment : Tower.Tm n}
    (signatureTyping : IntrinsicHasType context signature
      (liftClosed runSignatureType))
    (judgmentTyping : IntrinsicHasType context judgment
      (runJudgment signature)) :
    IntrinsicHasType context
      (outcomeApp (runOutcomeSignature signature) judgment)
      (sortTm outcomeLevel) := by
  apply outcomeApp_hasType
  · exact runOutcomeSignature_hasType signatureTyping
  · simpa [runJudgment] using judgmentTyping

/-! ## The intrinsic indexed run family -/

def runName : DeclName := `Prime.Authority.Run
def runOkName : DeclName := `Prime.Authority.Run.ok
def runFaultName : DeclName := `Prime.Authority.Run.fault
def runEliminateName : DeclName := `Prime.Authority.Run.eliminate

def runLevel : LevelExpr := .max outcomeLevel runFailureLevel

def runApp (signature judgment : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.const runName) signature) judgment

def runOkApp (signature judgment outcome : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.const runOkName) signature) judgment) outcome

def runFaultApp (signature judgment failure : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.const runFaultName) signature) judgment) failure

def runEliminateApp (signature motive okCase faultCase judgment run :
    Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app
        (.app
          (.app
            (.app (.const runEliminateName) signature)
            motive)
          okCase)
        faultCase)
      judgment)
    run

@[simp] theorem rename_runApp (renameMap : Ren n m)
    (signature judgment : Tower.Tm n) :
    Presentation.rename renameMap (runApp signature judgment) =
      runApp (Presentation.rename renameMap signature)
        (Presentation.rename renameMap judgment) := rfl

@[simp] theorem subst_runApp (substitution : Sub Tower.Head n m)
    (signature judgment : Tower.Tm n) :
    Presentation.subst substitution (runApp signature judgment) =
      runApp (Presentation.subst substitution signature)
        (Presentation.subst substitution judgment) := rfl

/-- `Run : (signature : RunSignature) -> signature.J -> U`. -/
def runType : Tower.Tm 0 :=
  .pi runSignatureType
    (.pi (runJudgment (.var 0)) (sortTm runLevel))

def runOkBodyType : Tower.Tm 1 :=
  .pi (runJudgment (.var 0))
    (arrow
      (outcomeApp (runOutcomeSignature (.var 1)) (.var 0))
      (runApp (.var 1) (.var 0)))

def runOkType : Tower.Tm 0 :=
  .pi runSignatureType runOkBodyType

def runFaultBodyType : Tower.Tm 1 :=
  .pi (runJudgment (.var 0))
    (arrow
      (.app (runFailureFamily (.var 1)) (.var 0))
      (runApp (.var 1) (.var 0)))

def runFaultType : Tower.Tm 0 :=
  .pi runSignatureType runFaultBodyType

def runMotiveType : Tower.Tm 1 :=
  .pi (runJudgment (.var 0))
    (.pi (runApp (.var 1) (.var 0)) (sortTm runMotiveLevel))

def runOkCaseType : Tower.Tm 2 :=
  .pi (runJudgment (.var 1))
    (.pi (outcomeApp (runOutcomeSignature (.var 2)) (.var 0))
      (.app
        (.app (.var 2) (.var 1))
        (runOkApp (.var 3) (.var 1) (.var 0))))

def runFaultCaseType : Tower.Tm 2 :=
  .pi (runJudgment (.var 1))
    (.pi (.app (runFailureFamily (.var 2)) (.var 0))
      (.app
        (.app (.var 2) (.var 1))
        (runFaultApp (.var 3) (.var 1) (.var 0))))

def runEliminateResultType : Tower.Tm 2 :=
  .pi (runJudgment (.var 1))
    (.pi (runApp (.var 2) (.var 0))
      (.app (.app (.var 2) (.var 1)) (.var 0)))

def runEliminateBodyType : Tower.Tm 1 :=
  .pi runMotiveType
    (.pi runOkCaseType
      (.pi (Presentation.rename wk runFaultCaseType)
        (Presentation.rename wk
          (Presentation.rename wk runEliminateResultType))))

def runEliminateType : Tower.Tm 0 :=
  .pi runSignatureType runEliminateBodyType

/-! ## Proof-relevant computation generators -/

inductive RunIotaEvidence (n : Nat) :
    Tower.Tm n → Tower.Tm n → Type where
  | ok (signature motive okCase faultCase judgment outcome : Tower.Tm n) :
      RunIotaEvidence n
        (runEliminateApp signature motive okCase faultCase judgment
          (runOkApp signature judgment outcome))
        (.app (.app okCase judgment) outcome)
  | fault (signature motive okCase faultCase judgment failure : Tower.Tm n) :
      RunIotaEvidence n
        (runEliminateApp signature motive okCase faultCase judgment
          (runFaultApp signature judgment failure))
        (.app (.app faultCase judgment) failure)

def RunIotaEvidence.rename {left right : Tower.Tm n}
    (step : RunIotaEvidence n left right) (renameMap : Ren n m) :
    RunIotaEvidence m (Presentation.rename renameMap left)
      (Presentation.rename renameMap right) := by
  cases step with
  | ok => exact .ok _ _ _ _ _ _
  | fault => exact .fault _ _ _ _ _ _

def RunIotaEvidence.substitute {left right : Tower.Tm n}
    (step : RunIotaEvidence n left right)
    (substitution : Sub Tower.Head n m) :
    RunIotaEvidence m (Presentation.subst substitution left)
      (Presentation.subst substitution right) := by
  cases step with
  | ok => exact .ok _ _ _ _ _ _
  | fault => exact .fault _ _ _ _ _ _

def proofRelevantRunComputation :
    ProofRelevantRootComputation Tower.Head where
  Evidence := RunIotaEvidence _
  rename := by
    intro n m renameMap left right step
    exact step.rename renameMap
  substitute := by
    intro n m substitution left right step
    exact step.substitute substitution

def runComputation : RootComputation Tower.Head :=
  proofRelevantRunComputation.support

/-! ## Declaration signature layered over intrinsic Outcome -/

def runDeclarations : List (DeclName × Entry Tower.Head) :=
  [(runName, { type := runType }),
   (runOkName, { type := runOkType }),
   (runFaultName, { type := runFaultType }),
   (runEliminateName, { type := runEliminateType })]

def rawRunSignature : Signature Tower.Head where
  entries := (Signature.ofList runDeclarations).entries
  computation := runComputation

abbrev runRules : Rules Tower.Head :=
  extendRules outcomeRules rawRunSignature

@[simp] theorem typeOf_run :
    rawRunSignature.typeOf? runName = some runType := by
  simp [rawRunSignature, runDeclarations, runName, runOkName, runFaultName,
    runEliminateName, Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_runOk :
    rawRunSignature.typeOf? runOkName = some runOkType := by
  simp [rawRunSignature, runDeclarations, runName, runOkName, runFaultName,
    runEliminateName, Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_runFault :
    rawRunSignature.typeOf? runFaultName = some runFaultType := by
  simp [rawRunSignature, runDeclarations, runName, runOkName, runFaultName,
    runEliminateName, Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_runEliminate :
    rawRunSignature.typeOf? runEliminateName = some runEliminateType := by
  simp [rawRunSignature, runDeclarations, runName, runOkName, runFaultName,
    runEliminateName, Signature.ofList, Signature.insert, Signature.typeOf?]

/-! ## Typing in the declaration-extended calculus -/

abbrev RunHasType {n : Nat} :=
  @Presentation.HasType Tower.Head runRules n

def includeOutcomeTyping {context : Tower.Ctx n}
    {term type : Tower.Tm n}
    (typing : IntrinsicHasType context term type) :
    RunHasType context term type :=
  Presentation.Declaration.HasType.includeSignature outcomeRules
    rawRunSignature typing

private theorem declaredRunConstant_hasType
    {name : DeclName} {type : Tower.Tm 0}
    (lookup : rawRunSignature.typeOf? name = some type)
    {context : Tower.Ctx n} :
    RunHasType context (.const name) (liftClosed type) := by
  apply Presentation.HasType.const
  change combinedType outcomeRules rawRunSignature name = some type
  apply combinedType_of_signature
  · by_cases isRun : name = runName
    · subst name
      simp [outcomeRules, extendRules, combinedType, Tower.rules,
        rawOutcomeSignature,
        outcomeDeclarations, runName, outcomeName, establishedName,
        refutedName, outsideFragmentName, incompleteName,
        outcomeEliminateName, Signature.typeOf?, Signature.ofList,
        Signature.insert, Signature.empty]
    by_cases isOk : name = runOkName
    · subst name
      simp [outcomeRules, extendRules, combinedType, Tower.rules,
        rawOutcomeSignature,
        outcomeDeclarations, runOkName, outcomeName, establishedName,
        refutedName, outsideFragmentName, incompleteName,
        outcomeEliminateName, Signature.typeOf?, Signature.ofList,
        Signature.insert, Signature.empty]
    by_cases isFault : name = runFaultName
    · subst name
      simp [outcomeRules, extendRules, combinedType, Tower.rules,
        rawOutcomeSignature,
        outcomeDeclarations, runFaultName, outcomeName, establishedName,
        refutedName, outsideFragmentName, incompleteName,
        outcomeEliminateName, Signature.typeOf?, Signature.ofList,
        Signature.insert, Signature.empty]
    by_cases isEliminate : name = runEliminateName
    · subst name
      simp [outcomeRules, extendRules, combinedType, Tower.rules,
        rawOutcomeSignature,
        outcomeDeclarations, runEliminateName, outcomeName, establishedName,
        refutedName, outsideFragmentName, incompleteName,
        outcomeEliminateName, Signature.typeOf?, Signature.ofList,
        Signature.insert, Signature.empty]
    · simp [rawRunSignature, runDeclarations, Signature.typeOf?,
        Signature.ofList, Signature.insert, Signature.empty, isRun, isOk,
        isFault, isEliminate] at lookup
  · exact lookup

theorem runConstant_hasType {context : Tower.Ctx n} :
    RunHasType context (.const runName) (liftClosed runType) :=
  declaredRunConstant_hasType typeOf_run

theorem runOkConstant_hasType {context : Tower.Ctx n} :
    RunHasType context (.const runOkName) (liftClosed runOkType) :=
  declaredRunConstant_hasType typeOf_runOk

theorem runFaultConstant_hasType {context : Tower.Ctx n} :
    RunHasType context (.const runFaultName) (liftClosed runFaultType) :=
  declaredRunConstant_hasType typeOf_runFault

theorem runEliminateConstant_hasType {context : Tower.Ctx n} :
    RunHasType context (.const runEliminateName)
      (liftClosed runEliminateType) :=
  declaredRunConstant_hasType typeOf_runEliminate

theorem outcomeConstant_hasRunType {context : Tower.Ctx n} :
    RunHasType context (.const outcomeName) (liftClosed outcomeType) :=
  includeOutcomeTyping outcomeConstant_hasType

theorem runSignatureType_hasRunType :
    RunHasType (.nil : Tower.Ctx 0) runSignatureType
      (sortTm runSignatureLevel) :=
  includeOutcomeTyping runSignatureType_hasType

theorem runOutcomeApp_hasRunType {context : Tower.Ctx n}
    {signature judgment : Tower.Tm n}
    (signatureTyping : RunHasType context signature
      (liftClosed runSignatureType))
    (judgmentTyping : RunHasType context judgment
      (runJudgment signature)) :
    RunHasType context
      (outcomeApp (runOutcomeSignature signature) judgment)
      (sortTm outcomeLevel) := by
  apply outcomeApp_hasTypeWith outcomeConstant_hasRunType
  · exact runOutcomeSignature_hasType signatureTyping
  · simpa [runJudgment] using judgmentTyping

theorem runFailureApp_hasRunType {context : Tower.Ctx n}
    {signature judgment : Tower.Tm n}
    (signatureTyping : RunHasType context signature
      (liftClosed runSignatureType))
    (judgmentTyping : RunHasType context judgment
      (runJudgment signature)) :
    RunHasType context (.app (runFailureFamily signature) judgment)
      (sortTm runFailureLevel) := by
  apply familyApp_hasType
  · exact runFailureFamily_hasType signatureTyping
  · exact judgmentTyping

theorem runApp_hasTypeWith {rules : Rules Tower.Head}
    {context : Tower.Ctx n}
    {signature judgment : Tower.Tm n}
    (runTyping : Presentation.HasType rules context (.const runName)
      (liftClosed runType))
    (signatureTyping : Presentation.HasType rules context signature
      (liftClosed runSignatureType))
    (judgmentTyping : Presentation.HasType rules context judgment
      (runJudgment signature)) :
    Presentation.HasType rules context (runApp signature judgment)
      (sortTm runLevel) := by
  have afterSignature := Presentation.HasType.appElim
    runTyping signatureTyping
  have afterJudgment := Presentation.HasType.appElim afterSignature
    judgmentTyping
  simpa [runType, runApp, runJudgment, liftClosed, sortTm,
    Presentation.rename, Presentation.inst0, Presentation.subst,
    Presentation.subst0, Presentation.liftSub] using afterJudgment

theorem runApp_hasType {context : Tower.Ctx n}
    {signature judgment : Tower.Tm n}
    (signatureTyping : RunHasType context signature
      (liftClosed runSignatureType))
    (judgmentTyping : RunHasType context judgment
      (runJudgment signature)) :
    RunHasType context (runApp signature judgment) (sortTm runLevel) :=
  runApp_hasTypeWith (runConstant_hasType (context := context))
    signatureTyping judgmentTyping

def runOkAtSignatureType (signature : Tower.Tm n) : Tower.Tm n :=
  .pi (runJudgment signature)
    (arrow
      (outcomeApp
        (runOutcomeSignature (Presentation.rename wk signature)) (.var 0))
      (runApp (Presentation.rename wk signature) (.var 0)))

def runFaultAtSignatureType (signature : Tower.Tm n) : Tower.Tm n :=
  .pi (runJudgment signature)
    (arrow
      (.app (runFailureFamily (Presentation.rename wk signature)) (.var 0))
      (runApp (Presentation.rename wk signature) (.var 0)))

@[simp] theorem substitute_runOkBodyType (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature) runOkBodyType =
      runOkAtSignatureType signature := by
  simp [runOkBodyType, runOkAtSignatureType, Presentation.subst]

@[simp] theorem substitute_runFaultBodyType (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature) runFaultBodyType =
      runFaultAtSignatureType signature := by
  simp [runFaultBodyType, runFaultAtSignatureType, Presentation.subst]

@[simp] theorem inst0_runOutcomeApplication_wk
    (argument signature : Tower.Tm n) :
    Presentation.inst0 argument
        (outcomeApp
          (runOutcomeSignature (Presentation.rename wk signature)) (.var 0)) =
      outcomeApp (runOutcomeSignature signature) argument := by
  change outcomeApp
      (runOutcomeSignature
        (Presentation.inst0 argument (Presentation.rename wk signature)))
      argument = outcomeApp (runOutcomeSignature signature) argument
  rw [inst0_rename_wk]

@[simp] theorem inst0_runFailureApplication_wk
    (argument signature : Tower.Tm n) :
    Presentation.inst0 argument
        (Presentation.Tm.app
          (runFailureFamily (Presentation.rename wk signature)) (.var 0)) =
      Presentation.Tm.app (runFailureFamily signature) argument := by
  change Presentation.Tm.app
      (runFailureFamily
        (Presentation.inst0 argument (Presentation.rename wk signature)))
      argument = Presentation.Tm.app (runFailureFamily signature) argument
  rw [inst0_rename_wk]

@[simp] theorem inst0_runApplication_wk
    (argument signature : Tower.Tm n) :
    Presentation.inst0 argument
        (runApp (Presentation.rename wk signature) (.var 0)) =
      runApp signature argument := by
  change runApp
      (Presentation.inst0 argument (Presentation.rename wk signature))
      argument = runApp signature argument
  rw [inst0_rename_wk]

theorem runOkApp_hasType {context : Tower.Ctx n}
    {signature judgment outcome : Tower.Tm n}
    (signatureTyping : RunHasType context signature
      (liftClosed runSignatureType))
    (judgmentTyping : RunHasType context judgment
      (runJudgment signature))
    (outcomeTyping : RunHasType context outcome
      (outcomeApp (runOutcomeSignature signature) judgment)) :
    RunHasType context (runOkApp signature judgment outcome)
      (runApp signature judgment) := by
  have afterSignature := Presentation.HasType.appElim
    (runOkConstant_hasType (context := context)) signatureTyping
  have afterSignatureNormalized :
      RunHasType context (.app (.const runOkName) signature)
        (runOkAtSignatureType signature) := by
    simpa only [runOkType, liftClosed, inst0_rename_liftRen_elim0,
      substitute_runOkBodyType] using afterSignature
  have afterJudgment := Presentation.HasType.appElim afterSignatureNormalized
    judgmentTyping
  have afterJudgmentNormalized :
      RunHasType context
        (.app (.app (.const runOkName) signature) judgment)
        (arrow
          (outcomeApp (runOutcomeSignature signature) judgment)
          (runApp signature judgment)) := by
    simpa only [runOkAtSignatureType, inst0_arrow,
      inst0_runOutcomeApplication_wk, inst0_runApplication_wk] using
      afterJudgment
  have afterOutcome := Presentation.HasType.appElim afterJudgmentNormalized
    outcomeTyping
  simpa only [runOkApp, arrow, inst0_rename_wk] using afterOutcome

theorem runFaultApp_hasType {context : Tower.Ctx n}
    {signature judgment failure : Tower.Tm n}
    (signatureTyping : RunHasType context signature
      (liftClosed runSignatureType))
    (judgmentTyping : RunHasType context judgment
      (runJudgment signature))
    (failureTyping : RunHasType context failure
      (.app (runFailureFamily signature) judgment)) :
    RunHasType context (runFaultApp signature judgment failure)
      (runApp signature judgment) := by
  have afterSignature := Presentation.HasType.appElim
    (runFaultConstant_hasType (context := context)) signatureTyping
  have afterSignatureNormalized :
      RunHasType context (.app (.const runFaultName) signature)
        (runFaultAtSignatureType signature) := by
    simpa only [runFaultType, liftClosed, inst0_rename_liftRen_elim0,
      substitute_runFaultBodyType] using afterSignature
  have afterJudgment := Presentation.HasType.appElim afterSignatureNormalized
    judgmentTyping
  have afterJudgmentNormalized :
      RunHasType context
        (.app (.app (.const runFaultName) signature) judgment)
        (arrow (.app (runFailureFamily signature) judgment)
          (runApp signature judgment)) := by
    simpa only [runFaultAtSignatureType, inst0_arrow,
      inst0_runFailureApplication_wk, inst0_runApplication_wk] using
      afterJudgment
  have afterFailure := Presentation.HasType.appElim afterJudgmentNormalized
    failureTyping
  simpa only [runFaultApp, arrow, inst0_rename_wk] using afterFailure

/-! ### Family and constructor formation -/

def runContextR : Tower.Ctx 1 :=
  .snoc .nil runSignatureType

def runContextRJ : Tower.Ctx 2 :=
  .snoc runContextR (runJudgment (.var 0))

def runContextRJO : Tower.Ctx 3 :=
  .snoc runContextRJ
    (outcomeApp (runOutcomeSignature (.var 1)) (.var 0))

def runContextRJF : Tower.Ctx 3 :=
  .snoc runContextRJ
    (.app (runFailureFamily (.var 1)) (.var 0))

theorem runSignatureVar_hasType :
    RunHasType runContextR (.var 0) (liftClosed runSignatureType) := by
  have variableTyping :=
    (Presentation.HasType.var (R := runRules)
      (Γ := runContextR) (0 : Fin 1))
  have lookupEquality :
      Presentation.Ctx.lookup runContextR (0 : Fin 1) =
        liftClosed runSignatureType := by
    decide
  simpa only [lookupEquality] using variableTyping

theorem runSignatureVarInRJ_hasType :
    RunHasType runContextRJ (.var 1) (liftClosed runSignatureType) := by
  exact Presentation.HasType.var 1

theorem runJudgmentVar_hasType :
    RunHasType runContextRJ (.var 0) (runJudgment (.var 1)) := by
  exact Presentation.HasType.var 0

def runBodyLevel : LevelExpr :=
  .max judgmentLevel (.succ runLevel)

def runDeclarationLevel : LevelExpr :=
  .max runSignatureLevel runBodyLevel

theorem runType_hasType :
    RunHasType (.nil : Tower.Ctx 0) runType
      (sortTm runDeclarationLevel) := by
  unfold runType runDeclarationLevel runBodyLevel
  apply Presentation.HasType.piForm
  · exact runSignatureType_hasRunType
  · exact .sort runSignatureLevel
  · apply Presentation.HasType.piForm
    · apply runJudgment_hasType
      exact runSignatureVar_hasType
    · exact .sort judgmentLevel
    · exact .headType (.sort runLevel)
    · exact .sort (.succ runLevel)
    · exact .sorts judgmentLevel (.succ runLevel)
  · exact .sort runBodyLevel
  · exact .sorts runSignatureLevel runBodyLevel

def runOkWitnessLevel : LevelExpr :=
  .max outcomeLevel runLevel

def runOkBodyLevel : LevelExpr :=
  .max judgmentLevel runOkWitnessLevel

def runOkDeclarationLevel : LevelExpr :=
  .max runSignatureLevel runOkBodyLevel

theorem runOkBodyType_hasType :
    RunHasType runContextR runOkBodyType (sortTm runOkBodyLevel) := by
  unfold runOkBodyType runOkBodyLevel runOkWitnessLevel arrow
  apply Presentation.HasType.piForm
  · apply runJudgment_hasType
    exact runSignatureVar_hasType
  · exact .sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply runOutcomeApp_hasRunType
      · exact runSignatureVarInRJ_hasType
      · exact runJudgmentVar_hasType
    · exact .sort outcomeLevel
    · apply runApp_hasType
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · exact .sort runLevel
    · exact .sorts outcomeLevel runLevel
  · exact .sort runOkWitnessLevel
  · exact .sorts judgmentLevel runOkWitnessLevel

theorem runOkType_hasType :
    RunHasType (.nil : Tower.Ctx 0) runOkType
      (sortTm runOkDeclarationLevel) := by
  unfold runOkType runOkDeclarationLevel
  apply Presentation.HasType.piForm
  · exact runSignatureType_hasRunType
  · exact .sort runSignatureLevel
  · exact runOkBodyType_hasType
  · exact .sort runOkBodyLevel
  · exact .sorts runSignatureLevel runOkBodyLevel

def runFaultWitnessLevel : LevelExpr :=
  .max runFailureLevel runLevel

def runFaultBodyLevel : LevelExpr :=
  .max judgmentLevel runFaultWitnessLevel

def runFaultDeclarationLevel : LevelExpr :=
  .max runSignatureLevel runFaultBodyLevel

theorem runFaultBodyType_hasType :
    RunHasType runContextR runFaultBodyType
      (sortTm runFaultBodyLevel) := by
  unfold runFaultBodyType runFaultBodyLevel runFaultWitnessLevel arrow
  apply Presentation.HasType.piForm
  · apply runJudgment_hasType
    exact runSignatureVar_hasType
  · exact .sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply runFailureApp_hasRunType
      · exact runSignatureVarInRJ_hasType
      · exact runJudgmentVar_hasType
    · exact .sort runFailureLevel
    · apply runApp_hasType
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · exact .sort runLevel
    · exact .sorts runFailureLevel runLevel
  · exact .sort runFaultWitnessLevel
  · exact .sorts judgmentLevel runFaultWitnessLevel

theorem runFaultType_hasType :
    RunHasType (.nil : Tower.Ctx 0) runFaultType
      (sortTm runFaultDeclarationLevel) := by
  unfold runFaultType runFaultDeclarationLevel
  apply Presentation.HasType.piForm
  · exact runSignatureType_hasRunType
  · exact .sort runSignatureLevel
  · exact runFaultBodyType_hasType
  · exact .sort runFaultBodyLevel
  · exact .sorts runSignatureLevel runFaultBodyLevel

/-! ### Formation of the dependent run eliminator -/

def runMotiveAtSignatureType (signature : Tower.Tm n) : Tower.Tm n :=
  .pi (runJudgment signature)
    (.pi (runApp (Presentation.rename wk signature) (.var 0))
      (sortTm runMotiveLevel))

theorem runMotiveType_asAtSignature :
    runMotiveType = runMotiveAtSignatureType (.var 0) := by
  decide

def runContextRJR : Tower.Ctx 3 :=
  .snoc runContextRJ (runApp (.var 1) (.var 0))

def runMotiveInnerLevel : LevelExpr :=
  .max runLevel (.succ runMotiveLevel)

def runMotiveTypeLevel : LevelExpr :=
  .max judgmentLevel runMotiveInnerLevel

theorem runMotiveType_hasType :
    RunHasType runContextR runMotiveType
      (sortTm runMotiveTypeLevel) := by
  rw [runMotiveType_asAtSignature]
  unfold runMotiveAtSignatureType runMotiveTypeLevel runMotiveInnerLevel
  apply Presentation.HasType.piForm
  · apply runJudgment_hasType
    exact runSignatureVar_hasType
  · exact .sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply runApp_hasType
      · exact runSignatureVarInRJ_hasType
      · exact runJudgmentVar_hasType
    · exact .sort runLevel
    · exact .headType (.sort runMotiveLevel)
    · exact .sort (.succ runMotiveLevel)
    · exact .sorts runLevel (.succ runMotiveLevel)
  · exact .sort runMotiveInnerLevel
  · exact .sorts judgmentLevel runMotiveInnerLevel

@[simp] theorem inst0_runMotiveAfterJudgment
    (judgment signature : Tower.Tm n) :
    Presentation.inst0 judgment
        (.pi (runApp (Presentation.rename wk signature) (.var 0))
          (sortTm runMotiveLevel)) =
      .pi (runApp signature judgment) (sortTm runMotiveLevel) := by
  change Presentation.Tm.pi
      (Presentation.inst0 judgment
        (runApp (Presentation.rename wk signature) (.var 0)))
      (sortTm runMotiveLevel) =
    Presentation.Tm.pi (runApp signature judgment)
      (sortTm runMotiveLevel)
  rw [inst0_runApplication_wk]

theorem runMotiveApp_hasType {context : Tower.Ctx n}
    {signature motive judgment run : Tower.Tm n}
    (motiveTyping : RunHasType context motive
      (runMotiveAtSignatureType signature))
    (judgmentTyping : RunHasType context judgment
      (runJudgment signature))
    (runTyping : RunHasType context run (runApp signature judgment)) :
    RunHasType context (.app (.app motive judgment) run)
      (sortTm runMotiveLevel) := by
  have afterJudgment := Presentation.HasType.appElim motiveTyping
    judgmentTyping
  have afterJudgmentNormalized :
      RunHasType context (.app motive judgment)
        (.pi (runApp signature judgment) (sortTm runMotiveLevel)) := by
    simpa only [runMotiveAtSignatureType,
      inst0_runMotiveAfterJudgment] using afterJudgment
  have afterRun := Presentation.HasType.appElim afterJudgmentNormalized
    runTyping
  simpa [sortTm, Presentation.inst0, Presentation.subst] using afterRun

def runContextRM : Tower.Ctx 2 :=
  .snoc runContextR runMotiveType

def runContextRMJ : Tower.Ctx 3 :=
  .snoc runContextRM (runJudgment (.var 1))

def runContextRMJO : Tower.Ctx 4 :=
  .snoc runContextRMJ
    (outcomeApp (runOutcomeSignature (.var 2)) (.var 0))

def runContextRMJF : Tower.Ctx 4 :=
  .snoc runContextRMJ
    (.app (runFailureFamily (.var 2)) (.var 0))

def runContextRMJR : Tower.Ctx 4 :=
  .snoc runContextRMJ (runApp (.var 2) (.var 0))

theorem runSignatureVarInRM_hasType :
    RunHasType runContextRM (.var 1) (liftClosed runSignatureType) := by
  have variableTyping :=
    (Presentation.HasType.var (R := runRules)
      (Γ := runContextRM) (1 : Fin 2))
  have lookupEquality :
      Presentation.Ctx.lookup runContextRM (1 : Fin 2) =
        liftClosed runSignatureType := by
    decide
  simpa only [lookupEquality] using variableTyping

theorem runMotiveVarInRM_hasType :
    RunHasType runContextRM (.var 0)
      (runMotiveAtSignatureType (.var 1)) := by
  have variableTyping :=
    (Presentation.HasType.var (R := runRules)
      (Γ := runContextRM) (0 : Fin 2))
  have lookupEquality :
      Presentation.Ctx.lookup runContextRM (0 : Fin 2) =
        runMotiveAtSignatureType (.var 1) := by
    decide
  simpa only [lookupEquality] using variableTyping

theorem runSignatureVarInRMJ_hasType :
    RunHasType runContextRMJ (.var 2) (liftClosed runSignatureType) := by
  exact Presentation.HasType.var 2

theorem runJudgmentVarInRMJ_hasType :
    RunHasType runContextRMJ (.var 0) (runJudgment (.var 2)) := by
  exact Presentation.HasType.var 0

theorem runOkCaseVariables :
    RunHasType runContextRMJO
      (runOkApp (.var 3) (.var 1) (.var 0))
      (runApp (.var 3) (.var 1)) := by
  apply runOkApp_hasType
  · exact Presentation.HasType.var 3
  · exact Presentation.HasType.var 1
  · exact Presentation.HasType.var 0

theorem runFaultCaseVariables :
    RunHasType runContextRMJF
      (runFaultApp (.var 3) (.var 1) (.var 0))
      (runApp (.var 3) (.var 1)) := by
  apply runFaultApp_hasType
  · exact Presentation.HasType.var 3
  · exact Presentation.HasType.var 1
  · exact Presentation.HasType.var 0

def runOkCaseWitnessLevel : LevelExpr :=
  .max outcomeLevel runMotiveLevel

def runOkCaseLevel : LevelExpr :=
  .max judgmentLevel runOkCaseWitnessLevel

theorem runOkCaseType_hasType :
    RunHasType runContextRM runOkCaseType
      (sortTm runOkCaseLevel) := by
  unfold runOkCaseType runOkCaseLevel runOkCaseWitnessLevel
  apply Presentation.HasType.piForm
  · apply runJudgment_hasType
    exact runSignatureVarInRM_hasType
  · exact .sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply runOutcomeApp_hasRunType
      · exact runSignatureVarInRMJ_hasType
      · exact runJudgmentVarInRMJ_hasType
    · exact .sort outcomeLevel
    · apply runMotiveApp_hasType
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
      · exact runOkCaseVariables
    · exact .sort runMotiveLevel
    · exact .sorts outcomeLevel runMotiveLevel
  · exact .sort runOkCaseWitnessLevel
  · exact .sorts judgmentLevel runOkCaseWitnessLevel

def runFaultCaseWitnessLevel : LevelExpr :=
  .max runFailureLevel runMotiveLevel

def runFaultCaseLevel : LevelExpr :=
  .max judgmentLevel runFaultCaseWitnessLevel

theorem runFaultCaseType_hasType :
    RunHasType runContextRM runFaultCaseType
      (sortTm runFaultCaseLevel) := by
  unfold runFaultCaseType runFaultCaseLevel runFaultCaseWitnessLevel
  apply Presentation.HasType.piForm
  · apply runJudgment_hasType
    exact runSignatureVarInRM_hasType
  · exact .sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply runFailureApp_hasRunType
      · exact runSignatureVarInRMJ_hasType
      · exact runJudgmentVarInRMJ_hasType
    · exact .sort runFailureLevel
    · apply runMotiveApp_hasType
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
      · exact runFaultCaseVariables
    · exact .sort runMotiveLevel
    · exact .sorts runFailureLevel runMotiveLevel
  · exact .sort runFaultCaseWitnessLevel
  · exact .sorts judgmentLevel runFaultCaseWitnessLevel

def runEliminateInnerLevel : LevelExpr :=
  .max runLevel runMotiveLevel

def runEliminateResultLevel : LevelExpr :=
  .max judgmentLevel runEliminateInnerLevel

theorem runEliminateResultType_hasType :
    RunHasType runContextRM runEliminateResultType
      (sortTm runEliminateResultLevel) := by
  unfold runEliminateResultType runEliminateResultLevel
    runEliminateInnerLevel
  apply Presentation.HasType.piForm
  · apply runJudgment_hasType
    exact runSignatureVarInRM_hasType
  · exact .sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply runApp_hasType
      · exact runSignatureVarInRMJ_hasType
      · exact runJudgmentVarInRMJ_hasType
    · exact .sort runLevel
    · apply runMotiveApp_hasType
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0
    · exact .sort runMotiveLevel
    · exact .sorts runLevel runMotiveLevel
  · exact .sort runEliminateInnerLevel
  · exact .sorts judgmentLevel runEliminateInnerLevel

def runContextRMK : Tower.Ctx 3 :=
  .snoc runContextRM runOkCaseType

def runContextRMKF : Tower.Ctx 4 :=
  .snoc runContextRMK (Presentation.rename wk runFaultCaseType)

theorem runFaultCaseTypeInRMK_hasType :
    RunHasType runContextRMK (Presentation.rename wk runFaultCaseType)
      (sortTm runFaultCaseLevel) := by
  simpa [runContextRMK, sortTm, Presentation.rename] using
    runFaultCaseType_hasType.weaken (extension := runOkCaseType)

theorem runEliminateResultTypeInRMKF_hasType :
    RunHasType runContextRMKF
      (Presentation.rename wk
        (Presentation.rename wk runEliminateResultType))
      (sortTm runEliminateResultLevel) := by
  have first := runEliminateResultType_hasType.weaken
    (extension := runOkCaseType)
  have second := first.weaken
    (extension := Presentation.rename wk runFaultCaseType)
  simpa [runContextRMK, runContextRMKF, sortTm,
    Presentation.rename] using second

def runAfterFaultLevel : LevelExpr :=
  .max runFaultCaseLevel runEliminateResultLevel

def runAfterOkLevel : LevelExpr :=
  .max runOkCaseLevel runAfterFaultLevel

def runEliminateBodyLevel : LevelExpr :=
  .max runMotiveTypeLevel runAfterOkLevel

def runEliminateDeclarationLevel : LevelExpr :=
  .max runSignatureLevel runEliminateBodyLevel

theorem runEliminateBodyType_hasType :
    RunHasType runContextR runEliminateBodyType
      (sortTm runEliminateBodyLevel) := by
  unfold runEliminateBodyType runEliminateBodyLevel runAfterOkLevel
    runAfterFaultLevel
  apply Presentation.HasType.piForm
  · exact runMotiveType_hasType
  · exact .sort runMotiveTypeLevel
  · apply Presentation.HasType.piForm
    · exact runOkCaseType_hasType
    · exact .sort runOkCaseLevel
    · apply Presentation.HasType.piForm
      · exact runFaultCaseTypeInRMK_hasType
      · exact .sort runFaultCaseLevel
      · exact runEliminateResultTypeInRMKF_hasType
      · exact .sort runEliminateResultLevel
      · exact .sorts runFaultCaseLevel runEliminateResultLevel
    · exact .sort runAfterFaultLevel
    · exact .sorts runOkCaseLevel runAfterFaultLevel
  · exact .sort runAfterOkLevel
  · exact .sorts runMotiveTypeLevel runAfterOkLevel

theorem runEliminateType_hasType :
    RunHasType (.nil : Tower.Ctx 0) runEliminateType
      (sortTm runEliminateDeclarationLevel) := by
  unfold runEliminateType runEliminateDeclarationLevel
  apply Presentation.HasType.piForm
  · exact runSignatureType_hasRunType
  · exact .sort runSignatureLevel
  · exact runEliminateBodyType_hasType
  · exact .sort runEliminateBodyLevel
  · exact .sorts runSignatureLevel runEliminateBodyLevel

/-! ### Formed declaration signature -/

@[simp] theorem rawRunSignature_valueOf_none (name : DeclName) :
    rawRunSignature.valueOf? name = none := by
  by_cases isRun : name = runName
  · subst name
    simp [rawRunSignature, runDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty]
  by_cases isOk : name = runOkName
  · subst name
    simp [rawRunSignature, runDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isRun]
  by_cases isFault : name = runFaultName
  · subst name
    simp [rawRunSignature, runDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isRun, isOk]
  by_cases isEliminate : name = runEliminateName
  · subst name
    simp [rawRunSignature, runDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isRun, isOk,
      isFault]
  · simp [rawRunSignature, runDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isRun, isOk,
      isFault, isEliminate]

theorem rawRunSignature_types_formed {name : DeclName}
    {type : Tower.Tm 0}
    (lookup : rawRunSignature.typeOf? name = some type) :
    ∃ level : Tower.Head,
      outcomeRules.isUniverse level ∧
      RunHasType (.nil : Tower.Ctx 0) type (.head level) := by
  by_cases isRun : name = runName
  · subst name
    have typeEquality : type = runType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort runDeclarationLevel, .sort runDeclarationLevel,
      runType_hasType⟩
  by_cases isOk : name = runOkName
  · subst name
    have typeEquality : type = runOkType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort runOkDeclarationLevel, .sort runOkDeclarationLevel,
      runOkType_hasType⟩
  by_cases isFault : name = runFaultName
  · subst name
    have typeEquality : type = runFaultType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort runFaultDeclarationLevel, .sort runFaultDeclarationLevel,
      runFaultType_hasType⟩
  by_cases isEliminate : name = runEliminateName
  · subst name
    have typeEquality : type = runEliminateType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort runEliminateDeclarationLevel,
      .sort runEliminateDeclarationLevel, runEliminateType_hasType⟩
  · simp [rawRunSignature, runDeclarations, Signature.typeOf?,
      Signature.ofList, Signature.insert, Signature.empty, isRun, isOk,
      isFault, isEliminate] at lookup

theorem rawRunSignature_fresh {name : DeclName}
    {entry : Entry Tower.Head}
    (lookup : rawRunSignature.entries name = some entry) :
    outcomeRules.constantType name = none := by
  by_cases isRun : name = runName
  · subst name
    simp [outcomeRules, extendRules, combinedType, Tower.rules,
      rawOutcomeSignature, outcomeDeclarations, runName, outcomeName,
      establishedName, refutedName, outsideFragmentName, incompleteName,
      outcomeEliminateName, Signature.typeOf?, Signature.ofList,
      Signature.insert, Signature.empty]
  by_cases isOk : name = runOkName
  · subst name
    simp [outcomeRules, extendRules, combinedType, Tower.rules,
      rawOutcomeSignature, outcomeDeclarations, runOkName, outcomeName,
      establishedName, refutedName, outsideFragmentName, incompleteName,
      outcomeEliminateName, Signature.typeOf?, Signature.ofList,
      Signature.insert, Signature.empty]
  by_cases isFault : name = runFaultName
  · subst name
    simp [outcomeRules, extendRules, combinedType, Tower.rules,
      rawOutcomeSignature, outcomeDeclarations, runFaultName, outcomeName,
      establishedName, refutedName, outsideFragmentName, incompleteName,
      outcomeEliminateName, Signature.typeOf?, Signature.ofList,
      Signature.insert, Signature.empty]
  by_cases isEliminate : name = runEliminateName
  · subst name
    simp [outcomeRules, extendRules, combinedType, Tower.rules,
      rawOutcomeSignature, outcomeDeclarations, runEliminateName,
      outcomeName, establishedName, refutedName, outsideFragmentName,
      incompleteName, outcomeEliminateName, Signature.typeOf?,
      Signature.ofList, Signature.insert, Signature.empty]
  · simp [rawRunSignature, runDeclarations, Signature.ofList,
      Signature.insert, Signature.empty, isRun, isOk, isFault,
      isEliminate] at lookup

def rawRunSignature_formed : rawRunSignature.Formed outcomeRules where
  fresh := rawRunSignature_fresh
  types := rawRunSignature_types_formed
  values := by
    intro name type value _typeLookup valueLookup
    rw [rawRunSignature_valueOf_none] at valueLookup
    cases valueLookup
  noSelfDelta := by
    intro name value valueLookup
    rw [rawRunSignature_valueOf_none] at valueLookup
    cases valueLookup

/-! ### Strict positivity -/

def runFamilyApplication (signature judgment : Tower.Tm n)
    (signatureFree : FreeOf runName signature)
    (judgmentFree : FreeOf runName judgment) :
    FamilyApplication runName 2 (runApp signature judgment) :=
  .intro [signature, judgment] rfl (by
    intro argument membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl
    · exact signatureFree
    · exact judgmentFree) rfl

def outcomeSignatureTypeFreeOfRun : FreeOf runName outcomeSignatureType :=
  outcomeSignatureTypeFreeOf runName

/-- Like `OutcomeSignature`, `RunSignature` is structural and therefore free
of every prospective family name. -/
def runSignatureTypeFreeOf (family : DeclName) :
    FreeOf family runSignatureType := by
  unfold runSignatureType runSignatureBody familyType signatureJudgment
    sortTm
  exact .sigma (outcomeSignatureTypeFreeOf family)
    (.pi (.fst (.var 0)) (.head _))

def runSignatureTypeFree : FreeOf runName runSignatureType :=
  runSignatureTypeFreeOf runName

def runOkConstructorPositive :
    ConstructorType runName 2 runOkType := by
  unfold runOkType runOkBodyType arrow runJudgment runOutcomeSignature
    outcomeApp runApp
  exact .field (.free runSignatureTypeFree)
    (.field (.free (.fst (.fst (.var 0))))
      (.field
        (.free
          (.app
            (.app (.const (by decide : outcomeName ≠ runName))
              (.fst (.var 1)))
            (.var 0)))
        (.result (runFamilyApplication (.var 2) (.var 1)
          (.var 2) (.var 1)))))

def runFaultConstructorPositive :
    ConstructorType runName 2 runFaultType := by
  unfold runFaultType runFaultBodyType arrow runJudgment
    runOutcomeSignature runFailureFamily runApp
  exact .field (.free runSignatureTypeFree)
    (.field (.free (.fst (.fst (.var 0))))
      (.field
        (.free (.app (.snd (.var 1)) (.var 0)))
        (.result (runFamilyApplication (.var 2) (.var 1)
          (.var 2) (.var 1)))))

def runOkConstructorSpec :
    ConstructorSpec rawRunSignature runName 2 where
  name := runOkName
  type := runOkType
  declared := typeOf_runOk
  positive := runOkConstructorPositive

def runFaultConstructorSpec :
    ConstructorSpec rawRunSignature runName 2 where
  name := runFaultName
  type := runFaultType
  declared := typeOf_runFault
  positive := runFaultConstructorPositive

def runConstructors :
    List (ConstructorSpec rawRunSignature runName 2) :=
  [runOkConstructorSpec, runFaultConstructorSpec]

def runEliminatorSpec : EliminatorSpec rawRunSignature where
  name := runEliminateName
  type := runEliminateType
  declared := typeOf_runEliminate

/-- A run in a function domain is a negative occurrence even though the run
signature and judgment index themselves are family-free. -/
theorem runInFunctionDomain_not_strictlyPositive :
    StrictlyPositive runName 2
      (.pi (runApp (.var 1 : Tower.Tm 2) (.var 0)) (.var 0)) → False :=
  recursivePiDomain_not_strictlyPositive
    (runFamilyApplication (.var 1) (.var 0) (.var 1) (.var 0)) (.var 0)

/-! ### Canonical typed iota schemas -/

/-- The run eliminator after the signature, motive, and both branches have
been supplied in their declaration telescope. -/
def runEliminateAtParameters : Tower.Tm 4 :=
  .app
    (.app
      (.app
        (.app (.const runEliminateName) (.var 3))
        (.var 2))
      (.var 1))
    (.var 0)

def runEliminateAtParametersType : Tower.Tm 4 :=
  .pi (runJudgment (.var 3))
    (.pi (runApp (.var 4) (.var 0))
      (.app (.app (.var 4) (.var 1)) (.var 0)))

theorem runEliminateAtParameters_hasType :
    RunHasType runContextRMKF runEliminateAtParameters
      runEliminateAtParametersType := by
  have afterSignature := Presentation.HasType.appElim
    (runEliminateConstant_hasType (context := runContextRMKF))
    (Presentation.HasType.var 3)
  have afterMotive := Presentation.HasType.appElim afterSignature
    (Presentation.HasType.var 2)
  have afterOk := Presentation.HasType.appElim afterMotive
    (Presentation.HasType.var 1)
  have afterFault := Presentation.HasType.appElim afterOk
    (Presentation.HasType.var 0)
  convert afterFault using 1
  all_goals decide

def runContextRMKFJ : Tower.Ctx 5 :=
  .snoc runContextRMKF (runJudgment (.var 3))

def runOkIotaContext : Tower.Ctx 6 :=
  .snoc runContextRMKFJ
    (outcomeApp (runOutcomeSignature (.var 4)) (.var 0))

def runFaultIotaContext : Tower.Ctx 6 :=
  .snoc runContextRMKFJ
    (.app (runFailureFamily (.var 4)) (.var 0))

def runOkIotaRun : Tower.Tm 6 :=
  runOkApp (.var 5) (.var 1) (.var 0)

def runFaultIotaRun : Tower.Tm 6 :=
  runFaultApp (.var 5) (.var 1) (.var 0)

def runOkIotaLeft : Tower.Tm 6 :=
  .app
    (.app
      (Presentation.rename wk
        (Presentation.rename wk runEliminateAtParameters))
      (.var 1))
    runOkIotaRun

def runOkIotaRight : Tower.Tm 6 :=
  .app (.app (.var 3) (.var 1)) (.var 0)

def runOkIotaType : Tower.Tm 6 :=
  .app (.app (.var 4) (.var 1)) runOkIotaRun

def runFaultIotaLeft : Tower.Tm 6 :=
  .app
    (.app
      (Presentation.rename wk
        (Presentation.rename wk runEliminateAtParameters))
      (.var 1))
    runFaultIotaRun

def runFaultIotaRight : Tower.Tm 6 :=
  .app (.app (.var 2) (.var 1)) (.var 0)

def runFaultIotaType : Tower.Tm 6 :=
  .app (.app (.var 4) (.var 1)) runFaultIotaRun

abbrev RunTypedIotaReceipt (context : Tower.Ctx n)
    (left right type : Tower.Tm n) : Type :=
  ProofRelevantStepReceipt outcomeRules rawRunSignature
    proofRelevantRunComputation context left right type

theorem runOkIotaLeft_asEliminate :
    runOkIotaLeft =
      runEliminateApp (.var 5) (.var 4) (.var 3) (.var 2)
        (.var 1) (runOkApp (.var 5) (.var 1) (.var 0)) := by
  decide

theorem runOkIotaRight_asBranch :
    runOkIotaRight = .app (.app (.var 3) (.var 1)) (.var 0) :=
  rfl

def runOkIotaReceipt :
    RunTypedIotaReceipt runOkIotaContext runOkIotaLeft runOkIotaRight
      runOkIotaType where
  sourceTyping := by
    unfold runOkIotaContext runContextRMKFJ
    have judgmentTyping :
        RunHasType runOkIotaContext (.var 1)
          (runJudgment (.var 5)) := by
      exact Presentation.HasType.var 1
    have outcomeTyping :
        RunHasType runOkIotaContext (.var 0)
          (outcomeApp (runOutcomeSignature (.var 5)) (.var 1)) := by
      exact Presentation.HasType.var 0
    have constructedTyping := runOkApp_hasType
      (context := runOkIotaContext)
      (signature := (.var 5)) (judgment := (.var 1))
      (outcome := (.var 0)) (Presentation.HasType.var 5)
      judgmentTyping outcomeTyping
    have afterJudgmentBinder := runEliminateAtParameters_hasType.weaken
      (extension := runJudgment (.var 3))
    have weakened := afterJudgmentBinder.weaken
      (extension := outcomeApp (runOutcomeSignature (.var 4)) (.var 0))
    have afterJudgment := Presentation.HasType.appElim weakened
      judgmentTyping
    have source := Presentation.HasType.appElim afterJudgment
      constructedTyping
    convert source using 1
    all_goals decide
  targetTyping := by
    unfold runOkIotaContext runContextRMKFJ
    have judgmentTyping :
        RunHasType runOkIotaContext (.var 1)
          (runJudgment (.var 5)) := by
      exact Presentation.HasType.var 1
    have outcomeTyping :
        RunHasType runOkIotaContext (.var 0)
          (outcomeApp (runOutcomeSignature (.var 5)) (.var 1)) := by
      exact Presentation.HasType.var 0
    have afterJudgment := Presentation.HasType.appElim
      (Presentation.HasType.var (R := runRules)
        (Γ := runOkIotaContext) (3 : Fin 6)) judgmentTyping
    have target := Presentation.HasType.appElim afterJudgment outcomeTyping
    unfold runOkIotaContext runContextRMKFJ at target
    convert target using 1
    all_goals decide
  evidence := by
    change RunIotaEvidence 6 runOkIotaLeft runOkIotaRight
    rw [runOkIotaLeft_asEliminate, runOkIotaRight_asBranch]
    exact RunIotaEvidence.ok
      (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

theorem runFaultIotaLeft_asEliminate :
    runFaultIotaLeft =
      runEliminateApp (.var 5) (.var 4) (.var 3) (.var 2)
        (.var 1) (runFaultApp (.var 5) (.var 1) (.var 0)) := by
  decide

theorem runFaultIotaRight_asBranch :
    runFaultIotaRight = .app (.app (.var 2) (.var 1)) (.var 0) :=
  rfl

def runFaultIotaReceipt :
    RunTypedIotaReceipt runFaultIotaContext runFaultIotaLeft
      runFaultIotaRight runFaultIotaType where
  sourceTyping := by
    unfold runFaultIotaContext runContextRMKFJ
    have judgmentTyping :
        RunHasType runFaultIotaContext (.var 1)
          (runJudgment (.var 5)) := by
      exact Presentation.HasType.var 1
    have failureTyping :
        RunHasType runFaultIotaContext (.var 0)
          (.app (runFailureFamily (.var 5)) (.var 1)) := by
      exact Presentation.HasType.var 0
    have constructedTyping := runFaultApp_hasType
      (context := runFaultIotaContext)
      (signature := (.var 5)) (judgment := (.var 1))
      (failure := (.var 0)) (Presentation.HasType.var 5)
      judgmentTyping failureTyping
    have afterJudgmentBinder := runEliminateAtParameters_hasType.weaken
      (extension := runJudgment (.var 3))
    have weakened := afterJudgmentBinder.weaken
      (extension := .app (runFailureFamily (.var 4)) (.var 0))
    have afterJudgment := Presentation.HasType.appElim weakened
      judgmentTyping
    have source := Presentation.HasType.appElim afterJudgment
      constructedTyping
    convert source using 1
    all_goals decide
  targetTyping := by
    unfold runFaultIotaContext runContextRMKFJ
    have judgmentTyping :
        RunHasType runFaultIotaContext (.var 1)
          (runJudgment (.var 5)) := by
      exact Presentation.HasType.var 1
    have failureTyping :
        RunHasType runFaultIotaContext (.var 0)
          (.app (runFailureFamily (.var 5)) (.var 1)) := by
      exact Presentation.HasType.var 0
    have afterJudgment := Presentation.HasType.appElim
      (Presentation.HasType.var (R := runRules)
        (Γ := runFaultIotaContext) (2 : Fin 6)) judgmentTyping
    have target := Presentation.HasType.appElim afterJudgment failureTyping
    unfold runFaultIotaContext runContextRMKFJ at target
    convert target using 1
    all_goals decide
  evidence := by
    change RunIotaEvidence 6 runFaultIotaLeft runFaultIotaRight
    rw [runFaultIotaLeft_asEliminate, runFaultIotaRight_asBranch]
    exact RunIotaEvidence.fault
      (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

def runOkIotaSchema :
    IotaSchema outcomeRules rawRunSignature
      proofRelevantRunComputation 6 where
  context := runOkIotaContext
  left := runOkIotaLeft
  right := runOkIotaRight
  type := runOkIotaType
  receipt := runOkIotaReceipt

def runFaultIotaSchema :
    IotaSchema outcomeRules rawRunSignature
      proofRelevantRunComputation 6 where
  context := runFaultIotaContext
  left := runFaultIotaLeft
  right := runFaultIotaRight
  type := runFaultIotaType
  receipt := runFaultIotaReceipt

def runEliminateAtParameters_applicationHead :
    ApplicationHead runEliminateName runEliminateAtParameters :=
  .app (.app (.app (.app .const)))

noncomputable def runEliminateAtIota_applicationHead :
    ApplicationHead runEliminateName
      (Presentation.rename wk
        (Presentation.rename wk runEliminateAtParameters)) :=
  (runEliminateAtParameters_applicationHead.rename wk).rename wk

def runOkApp_constantOccurrence
    (signature judgment outcome : Tower.Tm n) :
    ConstantOccurrence runOkName
      (runOkApp signature judgment outcome) :=
  .appFunction (.appFunction (.appFunction .here))

def runFaultApp_constantOccurrence
    (signature judgment failure : Tower.Tm n) :
    ConstantOccurrence runFaultName
      (runFaultApp signature judgment failure) :=
  .appFunction (.appFunction (.appFunction .here))

noncomputable def runOkIotaClause :
    IotaClause outcomeRules rawRunSignature
      proofRelevantRunComputation
      (runConstructors.map ConstructorSpec.name)
      runEliminatorSpec.name where
  constructorName := runOkName
  constructorDeclared := by
    simp [runConstructors, runOkConstructorSpec]
  arity := 6
  schema := runOkIotaSchema
  eliminatorHead := .app (.app runEliminateAtIota_applicationHead)
  constructorOccurrence :=
    .appArgument
      (runOkApp_constantOccurrence (.var 5) (.var 1) (.var 0))

noncomputable def runFaultIotaClause :
    IotaClause outcomeRules rawRunSignature
      proofRelevantRunComputation
      (runConstructors.map ConstructorSpec.name)
      runEliminatorSpec.name where
  constructorName := runFaultName
  constructorDeclared := by
    simp [runConstructors, runOkConstructorSpec, runFaultConstructorSpec]
  arity := 6
  schema := runFaultIotaSchema
  eliminatorHead := .app (.app runEliminateAtIota_applicationHead)
  constructorOccurrence :=
    .appArgument
      (runFaultApp_constantOccurrence (.var 5) (.var 1) (.var 0))

noncomputable def runIotaClauses :
    List (IotaClause outcomeRules rawRunSignature
      proofRelevantRunComputation
      (runConstructors.map ConstructorSpec.name)
      runEliminatorSpec.name) :=
  [runOkIotaClause, runFaultIotaClause]

/-- A formed, strictly-positive intrinsic run family with exact typed
computation generators.  It is deliberately not promoted to `Authorized`
before raw preservation is proved for the selected confluence discipline. -/
noncomputable def runCandidate : Candidate outcomeRules where
  signature := rawRunSignature
  formed := rawRunSignature_formed
  computation := proofRelevantRunComputation
  computationSupport := rfl
  familyName := runName
  familyParameterCount := 1
  familyIndexCount := 1
  familyType := runType
  familyDeclared := typeOf_run
  constructors := runConstructors
  constructorNamesNodup := by
    change [runOkName, runFaultName].Nodup
    decide
  familyNotConstructor := by
    intro constructor membership
    simp only [runConstructors, List.mem_cons, List.not_mem_nil,
      or_false] at membership
    rcases membership with rfl | rfl <;> decide
  eliminator := runEliminatorSpec
  eliminatorNotFamily := by decide
  eliminatorNotConstructor := by
    intro constructor membership
    simp only [runConstructors, List.mem_cons, List.not_mem_nil,
      or_false] at membership
    rcases membership with rfl | rfl <;> decide
  iotaClauses := runIotaClauses
  constructorsComputed := by
    intro constructorName membership
    simp [runConstructors, runOkConstructorSpec,
      runFaultConstructorSpec] at membership
    rcases membership with rfl | rfl
    · simp [runIotaClauses, runOkIotaClause]
    · simp [runIotaClauses, runFaultIotaClause]

/-! ## Axiom audit -/

#print axioms runSignatureType_hasType
#print axioms parameterRunSignatureValue_hasType
#print axioms rawRunSignature_formed
#print axioms runOkIotaReceipt
#print axioms runFaultIotaReceipt
#print axioms runCandidate
#print axioms runInFunctionDomain_not_strictlyPositive

end Intrinsic
end InternalAuthorityMetatheory
end Mettapedia.Languages.MeTTa.PureKernel.Universe
