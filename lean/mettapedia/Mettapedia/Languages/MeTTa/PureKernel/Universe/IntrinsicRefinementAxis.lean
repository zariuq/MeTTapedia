import Mettapedia.Languages.MeTTa.PureKernel.Universe.IntrinsicAuthorityMetatheory

/-!
# Intrinsic refinement axes

Budget growth and authority growth are different sources of semantic
improvement.  This module internalizes that distinction as a native two-point
type with a dependent eliminator and proof-relevant computation evidence.
The type is intentionally independent of any judgment language or runtime.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe
namespace InternalAuthorityMetatheory
namespace Intrinsic

open Presentation
open Presentation.SchemaElaboration
open Presentation.Declaration
open Presentation.Declaration.ComputationAuthority
open Presentation.Declaration.IndexedFamily

def refinementAxisLevel : LevelExpr := Tower.zero
def refinementAxisMotiveLevel : LevelExpr := .param 17

def refinementAxisName : DeclName := `Prime.Authority.RefinementAxis
def refinementAxisBudgetName : DeclName :=
  `Prime.Authority.RefinementAxis.budget
def refinementAxisAuthorityName : DeclName :=
  `Prime.Authority.RefinementAxis.authority
def refinementAxisEliminateName : DeclName :=
  `Prime.Authority.RefinementAxis.eliminate

def refinementAxisTm : Tower.Tm n := .const refinementAxisName
def refinementAxisBudgetTm : Tower.Tm n := .const refinementAxisBudgetName
def refinementAxisAuthorityTm : Tower.Tm n :=
  .const refinementAxisAuthorityName

def refinementAxisEliminateApp
    (motive budgetCase authorityCase axis : Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app
        (.app (.const refinementAxisEliminateName) motive)
        budgetCase)
      authorityCase)
    axis

@[simp] theorem rename_refinementAxisTm (renameMap : Ren n m) :
    Presentation.rename renameMap (refinementAxisTm : Tower.Tm n) =
      refinementAxisTm :=
  rfl

@[simp] theorem subst_refinementAxisTm
    (substitution : Sub Tower.Head n m) :
    Presentation.subst substitution (refinementAxisTm : Tower.Tm n) =
      refinementAxisTm :=
  rfl

@[simp] theorem rename_refinementAxisBudgetTm (renameMap : Ren n m) :
    Presentation.rename renameMap
        (refinementAxisBudgetTm : Tower.Tm n) =
      refinementAxisBudgetTm :=
  rfl

@[simp] theorem subst_refinementAxisBudgetTm
    (substitution : Sub Tower.Head n m) :
    Presentation.subst substitution
        (refinementAxisBudgetTm : Tower.Tm n) =
      refinementAxisBudgetTm :=
  rfl

@[simp] theorem rename_refinementAxisAuthorityTm (renameMap : Ren n m) :
    Presentation.rename renameMap
        (refinementAxisAuthorityTm : Tower.Tm n) =
      refinementAxisAuthorityTm :=
  rfl

@[simp] theorem subst_refinementAxisAuthorityTm
    (substitution : Sub Tower.Head n m) :
    Presentation.subst substitution
        (refinementAxisAuthorityTm : Tower.Tm n) =
      refinementAxisAuthorityTm :=
  rfl

@[simp] theorem rename_refinementAxisEliminateApp (renameMap : Ren n m)
    (motive budgetCase authorityCase axis : Tower.Tm n) :
    Presentation.rename renameMap
        (refinementAxisEliminateApp motive budgetCase authorityCase axis) =
      refinementAxisEliminateApp
        (Presentation.rename renameMap motive)
        (Presentation.rename renameMap budgetCase)
        (Presentation.rename renameMap authorityCase)
        (Presentation.rename renameMap axis) :=
  rfl

@[simp] theorem subst_refinementAxisEliminateApp
    (substitution : Sub Tower.Head n m)
    (motive budgetCase authorityCase axis : Tower.Tm n) :
    Presentation.subst substitution
        (refinementAxisEliminateApp motive budgetCase authorityCase axis) =
      refinementAxisEliminateApp
        (Presentation.subst substitution motive)
        (Presentation.subst substitution budgetCase)
        (Presentation.subst substitution authorityCase)
        (Presentation.subst substitution axis) :=
  rfl

/-! ## Closed declaration types -/

def refinementAxisType : Tower.Tm 0 := sortTm refinementAxisLevel
def refinementAxisBudgetType : Tower.Tm 0 := refinementAxisTm
def refinementAxisAuthorityType : Tower.Tm 0 := refinementAxisTm

/-- `RefinementAxis → U ρ`. -/
def refinementAxisMotiveType : Tower.Tm 0 :=
  .pi refinementAxisTm (sortTm refinementAxisMotiveLevel)

/-- In context `P`, the budget branch has type `P budget`. -/
def refinementAxisBudgetCaseType : Tower.Tm 1 :=
  .app (.var 0) refinementAxisBudgetTm

/-- In context `P, budgetCase`, the authority branch has type
`P authority`. -/
def refinementAxisAuthorityCaseType : Tower.Tm 2 :=
  .app (.var 1) refinementAxisAuthorityTm

/-- In context `P, budgetCase, authorityCase`, elimination returns
`(axis : RefinementAxis) → P axis`. -/
def refinementAxisEliminateResultType : Tower.Tm 3 :=
  .pi refinementAxisTm (.app (.var 3) (.var 0))

def refinementAxisEliminateType : Tower.Tm 0 :=
  .pi refinementAxisMotiveType
    (.pi refinementAxisBudgetCaseType
      (.pi refinementAxisAuthorityCaseType
        refinementAxisEliminateResultType))

/-! ## Proof-relevant computation -/

inductive RefinementAxisIotaEvidence (n : Nat) :
    Tower.Tm n → Tower.Tm n → Type where
  | budget (motive budgetCase authorityCase : Tower.Tm n) :
      RefinementAxisIotaEvidence n
        (refinementAxisEliminateApp motive budgetCase authorityCase
          refinementAxisBudgetTm)
        budgetCase
  | authority (motive budgetCase authorityCase : Tower.Tm n) :
      RefinementAxisIotaEvidence n
        (refinementAxisEliminateApp motive budgetCase authorityCase
          refinementAxisAuthorityTm)
        authorityCase

def RefinementAxisIotaEvidence.rename {left right : Tower.Tm n}
    (evidence : RefinementAxisIotaEvidence n left right)
    (renameMap : Ren n m) :
    RefinementAxisIotaEvidence m
      (Presentation.rename renameMap left)
      (Presentation.rename renameMap right) := by
  cases evidence with
  | budget => exact .budget _ _ _
  | authority => exact .authority _ _ _

def RefinementAxisIotaEvidence.substitute {left right : Tower.Tm n}
    (evidence : RefinementAxisIotaEvidence n left right)
    (substitution : Sub Tower.Head n m) :
    RefinementAxisIotaEvidence m
      (Presentation.subst substitution left)
      (Presentation.subst substitution right) := by
  cases evidence with
  | budget => exact .budget _ _ _
  | authority => exact .authority _ _ _

def proofRelevantRefinementAxisComputation :
    ProofRelevantRootComputation Tower.Head where
  Evidence := RefinementAxisIotaEvidence _
  rename := by
    intro n m renameMap left right evidence
    exact evidence.rename renameMap
  substitute := by
    intro n m substitution left right evidence
    exact evidence.substitute substitution

def refinementAxisComputation : RootComputation Tower.Head :=
  proofRelevantRefinementAxisComputation.support

/-! ## Declaration signature -/

def refinementAxisDeclarations : List (DeclName × Entry Tower.Head) :=
  [(refinementAxisName, { type := refinementAxisType }),
   (refinementAxisBudgetName, { type := refinementAxisBudgetType }),
   (refinementAxisAuthorityName, { type := refinementAxisAuthorityType }),
   (refinementAxisEliminateName, { type := refinementAxisEliminateType })]

def rawRefinementAxisSignature : Signature Tower.Head where
  entries := (Signature.ofList refinementAxisDeclarations).entries
  computation := refinementAxisComputation

abbrev refinementAxisRules : Rules Tower.Head :=
  extendRules emptyRules rawRefinementAxisSignature

@[simp] theorem typeOf_refinementAxis :
    rawRefinementAxisSignature.typeOf? refinementAxisName =
      some refinementAxisType := by
  simp [rawRefinementAxisSignature, refinementAxisDeclarations,
    refinementAxisName, refinementAxisBudgetName,
    refinementAxisAuthorityName, refinementAxisEliminateName,
    Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_refinementAxisBudget :
    rawRefinementAxisSignature.typeOf? refinementAxisBudgetName =
      some refinementAxisBudgetType := by
  simp [rawRefinementAxisSignature, refinementAxisDeclarations,
    refinementAxisName, refinementAxisBudgetName,
    refinementAxisAuthorityName, refinementAxisEliminateName,
    Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_refinementAxisAuthority :
    rawRefinementAxisSignature.typeOf? refinementAxisAuthorityName =
      some refinementAxisAuthorityType := by
  simp [rawRefinementAxisSignature, refinementAxisDeclarations,
    refinementAxisName, refinementAxisBudgetName,
    refinementAxisAuthorityName, refinementAxisEliminateName,
    Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_refinementAxisEliminate :
    rawRefinementAxisSignature.typeOf? refinementAxisEliminateName =
      some refinementAxisEliminateType := by
  simp [rawRefinementAxisSignature, refinementAxisDeclarations,
    refinementAxisName, refinementAxisBudgetName,
    refinementAxisAuthorityName, refinementAxisEliminateName,
    Signature.ofList, Signature.insert, Signature.typeOf?]

abbrev RefinementAxisHasType {n : Nat} :=
  @Presentation.HasType Tower.Head refinementAxisRules n

def includeEmptyInRefinementAxis {context : Tower.Ctx n}
    {term type : Tower.Tm n}
    (typing : EmptyHasType context term type) :
    RefinementAxisHasType context term type :=
  Presentation.Declaration.HasType.includeSignature emptyRules
    rawRefinementAxisSignature typing

private theorem refinementAxisName_fresh :
    emptyRules.constantType refinementAxisName = none := by
  decide

private theorem refinementAxisBudgetName_fresh :
    emptyRules.constantType refinementAxisBudgetName = none := by
  decide

private theorem refinementAxisAuthorityName_fresh :
    emptyRules.constantType refinementAxisAuthorityName = none := by
  decide

private theorem refinementAxisEliminateName_fresh :
    emptyRules.constantType refinementAxisEliminateName = none := by
  decide

private theorem declaredRefinementAxisConstant_hasType
    {name : DeclName} {type : Tower.Tm 0}
    (lookup : rawRefinementAxisSignature.typeOf? name = some type)
    (fresh : emptyRules.constantType name = none)
    {context : Tower.Ctx n} :
    RefinementAxisHasType context (.const name) (liftClosed type) := by
  apply Presentation.HasType.const
  change combinedType emptyRules rawRefinementAxisSignature name = some type
  exact combinedType_of_signature emptyRules rawRefinementAxisSignature
    fresh lookup

theorem refinementAxisConstant_hasType {context : Tower.Ctx n} :
    RefinementAxisHasType context (.const refinementAxisName)
      (liftClosed refinementAxisType) :=
  declaredRefinementAxisConstant_hasType typeOf_refinementAxis
    refinementAxisName_fresh

theorem refinementAxisBudgetConstant_hasType {context : Tower.Ctx n} :
    RefinementAxisHasType context (.const refinementAxisBudgetName)
      (liftClosed refinementAxisBudgetType) :=
  declaredRefinementAxisConstant_hasType typeOf_refinementAxisBudget
    refinementAxisBudgetName_fresh

theorem refinementAxisAuthorityConstant_hasType {context : Tower.Ctx n} :
    RefinementAxisHasType context (.const refinementAxisAuthorityName)
      (liftClosed refinementAxisAuthorityType) :=
  declaredRefinementAxisConstant_hasType typeOf_refinementAxisAuthority
    refinementAxisAuthorityName_fresh

theorem refinementAxisEliminateConstant_hasType {context : Tower.Ctx n} :
    RefinementAxisHasType context (.const refinementAxisEliminateName)
      (liftClosed refinementAxisEliminateType) :=
  declaredRefinementAxisConstant_hasType typeOf_refinementAxisEliminate
    refinementAxisEliminateName_fresh

/-! ## Declaration formation -/

def refinementAxisContextP : Tower.Ctx 1 :=
  .snoc .nil refinementAxisMotiveType

def refinementAxisContextPB : Tower.Ctx 2 :=
  .snoc refinementAxisContextP refinementAxisBudgetCaseType

def refinementAxisContextPBA : Tower.Ctx 3 :=
  .snoc refinementAxisContextPB refinementAxisAuthorityCaseType

def refinementAxisMotiveTypeLevel : LevelExpr :=
  .max refinementAxisLevel (.succ refinementAxisMotiveLevel)

def refinementAxisEliminateResultLevel : LevelExpr :=
  .max refinementAxisLevel refinementAxisMotiveLevel

def refinementAxisEliminateAfterAuthorityLevel : LevelExpr :=
  .max refinementAxisMotiveLevel refinementAxisEliminateResultLevel

def refinementAxisEliminateAfterBudgetLevel : LevelExpr :=
  .max refinementAxisMotiveLevel
    refinementAxisEliminateAfterAuthorityLevel

def refinementAxisEliminateDeclarationLevel : LevelExpr :=
  .max refinementAxisMotiveTypeLevel
    refinementAxisEliminateAfterBudgetLevel

theorem refinementAxisType_hasType :
    RefinementAxisHasType (.nil : Tower.Ctx 0) refinementAxisType
      (sortTm (.succ refinementAxisLevel)) := by
  exact Presentation.HasType.headType
    (Tower.HeadTyping.sort refinementAxisLevel)

theorem refinementAxisTm_hasType {context : Tower.Ctx n} :
    RefinementAxisHasType context refinementAxisTm
      (sortTm refinementAxisLevel) := by
  simpa [refinementAxisTm, refinementAxisType, liftClosed, sortTm,
    Presentation.rename] using
    (refinementAxisConstant_hasType (context := context))

theorem refinementAxisBudgetTm_hasType {context : Tower.Ctx n} :
    RefinementAxisHasType context refinementAxisBudgetTm
      refinementAxisTm := by
  simpa [refinementAxisBudgetTm, refinementAxisBudgetType,
    refinementAxisTm, liftClosed, Presentation.rename] using
    (refinementAxisBudgetConstant_hasType (context := context))

theorem refinementAxisAuthorityTm_hasType {context : Tower.Ctx n} :
    RefinementAxisHasType context refinementAxisAuthorityTm
      refinementAxisTm := by
  simpa [refinementAxisAuthorityTm, refinementAxisAuthorityType,
    refinementAxisTm, liftClosed, Presentation.rename] using
    (refinementAxisAuthorityConstant_hasType (context := context))

theorem refinementAxisMotiveType_hasType :
    RefinementAxisHasType (.nil : Tower.Ctx 0) refinementAxisMotiveType
      (sortTm refinementAxisMotiveTypeLevel) := by
  unfold refinementAxisMotiveType refinementAxisMotiveTypeLevel
  apply Presentation.HasType.piForm
  · exact refinementAxisTm_hasType
  · exact Tower.IsUniverse.sort refinementAxisLevel
  · exact Presentation.HasType.headType
      (Tower.HeadTyping.sort refinementAxisMotiveLevel)
  · exact Tower.IsUniverse.sort (.succ refinementAxisMotiveLevel)
  · exact Tower.Join.sorts refinementAxisLevel
      (.succ refinementAxisMotiveLevel)

theorem refinementAxisBudgetCaseType_hasType :
    RefinementAxisHasType refinementAxisContextP
      refinementAxisBudgetCaseType (sortTm refinementAxisMotiveLevel) := by
  unfold refinementAxisContextP refinementAxisBudgetCaseType
  have result := Presentation.HasType.appElim
    (Presentation.HasType.var (R := refinementAxisRules)
      (Γ := .snoc (.nil : Tower.Ctx 0) refinementAxisMotiveType)
      (0 : Fin 1))
    (refinementAxisBudgetTm_hasType (context :=
      .snoc (.nil : Tower.Ctx 0) refinementAxisMotiveType))
  convert result using 1
  all_goals decide

theorem refinementAxisAuthorityCaseType_hasType :
    RefinementAxisHasType refinementAxisContextPB
      refinementAxisAuthorityCaseType (sortTm refinementAxisMotiveLevel) := by
  unfold refinementAxisContextPB refinementAxisContextP
    refinementAxisAuthorityCaseType
  have result := Presentation.HasType.appElim
    (Presentation.HasType.var (R := refinementAxisRules)
      (Γ := .snoc
        (.snoc (.nil : Tower.Ctx 0) refinementAxisMotiveType)
        refinementAxisBudgetCaseType)
      (1 : Fin 2))
    (refinementAxisAuthorityTm_hasType (context :=
      .snoc
        (.snoc (.nil : Tower.Ctx 0) refinementAxisMotiveType)
        refinementAxisBudgetCaseType))
  convert result using 1
  all_goals decide

theorem refinementAxisEliminateResultType_hasType :
    RefinementAxisHasType refinementAxisContextPBA
      refinementAxisEliminateResultType
      (sortTm refinementAxisEliminateResultLevel) := by
  unfold refinementAxisContextPBA refinementAxisContextPB
    refinementAxisContextP refinementAxisEliminateResultType
    refinementAxisEliminateResultLevel
  apply Presentation.HasType.piForm
  · exact refinementAxisTm_hasType
  · exact Tower.IsUniverse.sort refinementAxisLevel
  · have motiveTyping :
        RefinementAxisHasType
          (.snoc
            (.snoc
              (.snoc
                (.snoc (.nil : Tower.Ctx 0) refinementAxisMotiveType)
                refinementAxisBudgetCaseType)
              refinementAxisAuthorityCaseType)
            refinementAxisTm)
          (.var 3)
          (.pi refinementAxisTm (sortTm refinementAxisMotiveLevel)) := by
      convert
        (Presentation.HasType.var (R := refinementAxisRules)
          (Γ :=
            .snoc
              (.snoc
                (.snoc
                  (.snoc (.nil : Tower.Ctx 0) refinementAxisMotiveType)
                  refinementAxisBudgetCaseType)
                refinementAxisAuthorityCaseType)
              refinementAxisTm)
          (3 : Fin 4)) using 1
      all_goals decide
    have axisTyping :=
      (Presentation.HasType.var (R := refinementAxisRules)
        (Γ :=
          .snoc
            (.snoc
              (.snoc
                (.snoc (.nil : Tower.Ctx 0) refinementAxisMotiveType)
                refinementAxisBudgetCaseType)
              refinementAxisAuthorityCaseType)
            refinementAxisTm)
        (0 : Fin 4))
    have result := Presentation.HasType.appElim motiveTyping axisTyping
    simpa [sortTm, Presentation.inst0, Presentation.subst] using result
  · exact Tower.IsUniverse.sort refinementAxisMotiveLevel
  · exact Tower.Join.sorts refinementAxisLevel refinementAxisMotiveLevel

theorem refinementAxisEliminateType_hasType :
    RefinementAxisHasType (.nil : Tower.Ctx 0)
      refinementAxisEliminateType
      (sortTm refinementAxisEliminateDeclarationLevel) := by
  unfold refinementAxisEliminateType
    refinementAxisEliminateDeclarationLevel
    refinementAxisEliminateAfterBudgetLevel
    refinementAxisEliminateAfterAuthorityLevel
  apply Presentation.HasType.piForm
  · exact refinementAxisMotiveType_hasType
  · exact Tower.IsUniverse.sort refinementAxisMotiveTypeLevel
  · apply Presentation.HasType.piForm
    · exact refinementAxisBudgetCaseType_hasType
    · exact Tower.IsUniverse.sort refinementAxisMotiveLevel
    · apply Presentation.HasType.piForm
      · exact refinementAxisAuthorityCaseType_hasType
      · exact Tower.IsUniverse.sort refinementAxisMotiveLevel
      · exact refinementAxisEliminateResultType_hasType
      · exact Tower.IsUniverse.sort refinementAxisEliminateResultLevel
      · exact Tower.Join.sorts refinementAxisMotiveLevel
          refinementAxisEliminateResultLevel
    · exact Tower.IsUniverse.sort
        refinementAxisEliminateAfterAuthorityLevel
    · exact Tower.Join.sorts refinementAxisMotiveLevel
        refinementAxisEliminateAfterAuthorityLevel
  · exact Tower.IsUniverse.sort refinementAxisEliminateAfterBudgetLevel
  · exact Tower.Join.sorts refinementAxisMotiveTypeLevel
      refinementAxisEliminateAfterBudgetLevel

@[simp] theorem rawRefinementAxisSignature_valueOf_none (name : DeclName) :
    rawRefinementAxisSignature.valueOf? name = none := by
  by_cases isAxis : name = refinementAxisName
  · subst name
    simp [rawRefinementAxisSignature, refinementAxisDeclarations,
      Signature.valueOf?, Signature.ofList, Signature.insert,
      Signature.empty]
  by_cases isBudget : name = refinementAxisBudgetName
  · subst name
    simp [rawRefinementAxisSignature, refinementAxisDeclarations,
      Signature.valueOf?, Signature.ofList, Signature.insert,
      Signature.empty, isAxis]
  by_cases isAuthority : name = refinementAxisAuthorityName
  · subst name
    simp [rawRefinementAxisSignature, refinementAxisDeclarations,
      Signature.valueOf?, Signature.ofList, Signature.insert,
      Signature.empty, isAxis, isBudget]
  by_cases isEliminate : name = refinementAxisEliminateName
  · subst name
    simp [rawRefinementAxisSignature, refinementAxisDeclarations,
      Signature.valueOf?, Signature.ofList, Signature.insert,
      Signature.empty, isAxis, isBudget, isAuthority]
  · simp [rawRefinementAxisSignature, refinementAxisDeclarations,
      Signature.valueOf?, Signature.ofList, Signature.insert,
      Signature.empty, isAxis, isBudget, isAuthority, isEliminate]

theorem rawRefinementAxisSignature_types_formed
    {name : DeclName} {type : Tower.Tm 0}
    (lookup : rawRefinementAxisSignature.typeOf? name = some type) :
    ∃ level : Tower.Head,
      emptyRules.isUniverse level ∧
      RefinementAxisHasType (.nil : Tower.Ctx 0) type (.head level) := by
  by_cases isAxis : name = refinementAxisName
  · subst name
    have typeEquality : type = refinementAxisType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort (.succ refinementAxisLevel),
      .sort (.succ refinementAxisLevel), refinementAxisType_hasType⟩
  by_cases isBudget : name = refinementAxisBudgetName
  · subst name
    have typeEquality : type = refinementAxisBudgetType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort refinementAxisLevel, .sort refinementAxisLevel,
      refinementAxisTm_hasType⟩
  by_cases isAuthority : name = refinementAxisAuthorityName
  · subst name
    have typeEquality : type = refinementAxisAuthorityType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort refinementAxisLevel, .sort refinementAxisLevel,
      refinementAxisTm_hasType⟩
  by_cases isEliminate : name = refinementAxisEliminateName
  · subst name
    have typeEquality : type = refinementAxisEliminateType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort refinementAxisEliminateDeclarationLevel,
      .sort refinementAxisEliminateDeclarationLevel,
      refinementAxisEliminateType_hasType⟩
  · simp [rawRefinementAxisSignature, refinementAxisDeclarations,
      Signature.typeOf?, Signature.ofList, Signature.insert,
      Signature.empty, isAxis, isBudget, isAuthority, isEliminate] at lookup

theorem rawRefinementAxisSignature_fresh {name : DeclName}
    {entry : Entry Tower.Head}
    (lookup : rawRefinementAxisSignature.entries name = some entry) :
    emptyRules.constantType name = none := by
  by_cases isAxis : name = refinementAxisName
  · subst name
    exact refinementAxisName_fresh
  by_cases isBudget : name = refinementAxisBudgetName
  · subst name
    exact refinementAxisBudgetName_fresh
  by_cases isAuthority : name = refinementAxisAuthorityName
  · subst name
    exact refinementAxisAuthorityName_fresh
  by_cases isEliminate : name = refinementAxisEliminateName
  · subst name
    exact refinementAxisEliminateName_fresh
  · simp [rawRefinementAxisSignature, refinementAxisDeclarations,
      Signature.ofList, Signature.insert, Signature.empty, isAxis,
      isBudget, isAuthority, isEliminate] at lookup

def rawRefinementAxisSignature_formed :
    rawRefinementAxisSignature.Formed emptyRules where
  fresh := rawRefinementAxisSignature_fresh
  types := rawRefinementAxisSignature_types_formed
  values := by
    intro name type value _typeLookup valueLookup
    rw [rawRefinementAxisSignature_valueOf_none] at valueLookup
    cases valueLookup
  noSelfDelta := by
    intro name value valueLookup
    rw [rawRefinementAxisSignature_valueOf_none] at valueLookup
    cases valueLookup

/-! ## Canonical typed computation receipts -/

abbrev RefinementAxisTypedIotaReceipt (context : Tower.Ctx n)
    (left right type : Tower.Tm n) : Type :=
  ProofRelevantStepReceipt emptyRules rawRefinementAxisSignature
    proofRelevantRefinementAxisComputation context left right type

def refinementAxisEliminateAtParameters : Tower.Tm 3 :=
  .app
    (.app
      (.app (.const refinementAxisEliminateName) (.var 2))
      (.var 1))
    (.var 0)

theorem refinementAxisEliminateAtParameters_hasType :
    RefinementAxisHasType refinementAxisContextPBA
      refinementAxisEliminateAtParameters
      refinementAxisEliminateResultType := by
  have motiveTyping :
      RefinementAxisHasType refinementAxisContextPBA (.var 2)
        (.pi refinementAxisTm (sortTm refinementAxisMotiveLevel)) := by
    convert
      (Presentation.HasType.var (R := refinementAxisRules)
        (Γ := refinementAxisContextPBA) (2 : Fin 3)) using 1
    all_goals decide
  have budgetCaseTyping :
      RefinementAxisHasType refinementAxisContextPBA (.var 1)
        (.app (.var 2) refinementAxisBudgetTm) := by
    convert
      (Presentation.HasType.var (R := refinementAxisRules)
        (Γ := refinementAxisContextPBA) (1 : Fin 3)) using 1
    all_goals decide
  have authorityCaseTyping :
      RefinementAxisHasType refinementAxisContextPBA (.var 0)
        (.app (.var 2) refinementAxisAuthorityTm) := by
    exact Presentation.HasType.var 0
  have afterMotive := Presentation.HasType.appElim
    (refinementAxisEliminateConstant_hasType
      (context := refinementAxisContextPBA)) motiveTyping
  have afterBudget := Presentation.HasType.appElim
    afterMotive budgetCaseTyping
  have result := Presentation.HasType.appElim
    afterBudget authorityCaseTyping
  convert result using 1
  all_goals decide

def refinementAxisBudgetIotaLeft : Tower.Tm 3 :=
  .app refinementAxisEliminateAtParameters refinementAxisBudgetTm

def refinementAxisBudgetIotaRight : Tower.Tm 3 := .var 1

def refinementAxisBudgetIotaType : Tower.Tm 3 :=
  .app (.var 2) refinementAxisBudgetTm

def refinementAxisBudgetIotaReceipt :
    RefinementAxisTypedIotaReceipt refinementAxisContextPBA
      refinementAxisBudgetIotaLeft refinementAxisBudgetIotaRight
      refinementAxisBudgetIotaType where
  sourceTyping := by
    have result := Presentation.HasType.appElim
      refinementAxisEliminateAtParameters_hasType
      (refinementAxisBudgetTm_hasType
        (context := refinementAxisContextPBA))
    convert result using 1
    all_goals decide
  targetTyping := Presentation.HasType.var 1
  evidence := .budget (.var 2) (.var 1) (.var 0)

def refinementAxisAuthorityIotaLeft : Tower.Tm 3 :=
  .app refinementAxisEliminateAtParameters refinementAxisAuthorityTm

def refinementAxisAuthorityIotaRight : Tower.Tm 3 := .var 0

def refinementAxisAuthorityIotaType : Tower.Tm 3 :=
  .app (.var 2) refinementAxisAuthorityTm

def refinementAxisAuthorityIotaReceipt :
    RefinementAxisTypedIotaReceipt refinementAxisContextPBA
      refinementAxisAuthorityIotaLeft refinementAxisAuthorityIotaRight
      refinementAxisAuthorityIotaType where
  sourceTyping := by
    have result := Presentation.HasType.appElim
      refinementAxisEliminateAtParameters_hasType
      (refinementAxisAuthorityTm_hasType
        (context := refinementAxisContextPBA))
    convert result using 1
    all_goals decide
  targetTyping := Presentation.HasType.var 0
  evidence := .authority (.var 2) (.var 1) (.var 0)

/-! ## Strictly-positive family package -/

def refinementAxisFamilyApplication :
    FamilyApplication refinementAxisName 0
      (refinementAxisTm : Tower.Tm n) :=
  .intro [] rfl (by
    intro argument membership
    cases membership) rfl

def refinementAxisBudgetConstructorPositive :
    ConstructorType refinementAxisName 0 refinementAxisBudgetType := by
  unfold refinementAxisBudgetType
  exact .result refinementAxisFamilyApplication

def refinementAxisAuthorityConstructorPositive :
    ConstructorType refinementAxisName 0 refinementAxisAuthorityType := by
  unfold refinementAxisAuthorityType
  exact .result refinementAxisFamilyApplication

def refinementAxisBudgetConstructorSpec :
    ConstructorSpec rawRefinementAxisSignature refinementAxisName 0 where
  name := refinementAxisBudgetName
  type := refinementAxisBudgetType
  declared := typeOf_refinementAxisBudget
  positive := refinementAxisBudgetConstructorPositive

def refinementAxisAuthorityConstructorSpec :
    ConstructorSpec rawRefinementAxisSignature refinementAxisName 0 where
  name := refinementAxisAuthorityName
  type := refinementAxisAuthorityType
  declared := typeOf_refinementAxisAuthority
  positive := refinementAxisAuthorityConstructorPositive

def refinementAxisConstructors :
    List (ConstructorSpec rawRefinementAxisSignature
      refinementAxisName 0) :=
  [refinementAxisBudgetConstructorSpec,
    refinementAxisAuthorityConstructorSpec]

def refinementAxisEliminatorSpec :
    EliminatorSpec rawRefinementAxisSignature where
  name := refinementAxisEliminateName
  type := refinementAxisEliminateType
  declared := typeOf_refinementAxisEliminate

def refinementAxisBudgetIotaSchema :
    IotaSchema emptyRules rawRefinementAxisSignature
      proofRelevantRefinementAxisComputation 3 where
  context := refinementAxisContextPBA
  left := refinementAxisBudgetIotaLeft
  right := refinementAxisBudgetIotaRight
  type := refinementAxisBudgetIotaType
  receipt := refinementAxisBudgetIotaReceipt

def refinementAxisAuthorityIotaSchema :
    IotaSchema emptyRules rawRefinementAxisSignature
      proofRelevantRefinementAxisComputation 3 where
  context := refinementAxisContextPBA
  left := refinementAxisAuthorityIotaLeft
  right := refinementAxisAuthorityIotaRight
  type := refinementAxisAuthorityIotaType
  receipt := refinementAxisAuthorityIotaReceipt

def refinementAxisEliminateAtParameters_applicationHead :
    ApplicationHead refinementAxisEliminateName
      refinementAxisEliminateAtParameters :=
  .app (.app (.app .const))

def refinementAxisBudgetIotaClause :
    IotaClause emptyRules rawRefinementAxisSignature
      proofRelevantRefinementAxisComputation
      (refinementAxisConstructors.map ConstructorSpec.name)
      refinementAxisEliminatorSpec.name where
  constructorName := refinementAxisBudgetName
  constructorDeclared := by
    simp [refinementAxisConstructors,
      refinementAxisBudgetConstructorSpec]
  arity := 3
  schema := refinementAxisBudgetIotaSchema
  eliminatorHead :=
    .app refinementAxisEliminateAtParameters_applicationHead
  constructorOccurrence := .appArgument .here

def refinementAxisAuthorityIotaClause :
    IotaClause emptyRules rawRefinementAxisSignature
      proofRelevantRefinementAxisComputation
      (refinementAxisConstructors.map ConstructorSpec.name)
      refinementAxisEliminatorSpec.name where
  constructorName := refinementAxisAuthorityName
  constructorDeclared := by
    simp [refinementAxisConstructors,
      refinementAxisBudgetConstructorSpec,
      refinementAxisAuthorityConstructorSpec]
  arity := 3
  schema := refinementAxisAuthorityIotaSchema
  eliminatorHead :=
    .app refinementAxisEliminateAtParameters_applicationHead
  constructorOccurrence := .appArgument .here

noncomputable def refinementAxisIotaClauses :
    List (IotaClause emptyRules rawRefinementAxisSignature
      proofRelevantRefinementAxisComputation
      (refinementAxisConstructors.map ConstructorSpec.name)
      refinementAxisEliminatorSpec.name) :=
  [refinementAxisBudgetIotaClause, refinementAxisAuthorityIotaClause]

noncomputable def refinementAxisCandidate : Candidate emptyRules where
  signature := rawRefinementAxisSignature
  formed := rawRefinementAxisSignature_formed
  computation := proofRelevantRefinementAxisComputation
  computationSupport := rfl
  familyName := refinementAxisName
  familyParameterCount := 0
  familyIndexCount := 0
  familyType := refinementAxisType
  familyDeclared := typeOf_refinementAxis
  constructors := refinementAxisConstructors
  constructorNamesNodup := by
    change [refinementAxisBudgetName,
      refinementAxisAuthorityName].Nodup
    decide
  familyNotConstructor := by
    intro constructor membership
    simp only [refinementAxisConstructors, List.mem_cons,
      List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl <;> decide
  eliminator := refinementAxisEliminatorSpec
  eliminatorNotFamily := by decide
  eliminatorNotConstructor := by
    intro constructor membership
    simp only [refinementAxisConstructors, List.mem_cons,
      List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl <;> decide
  iotaClauses := refinementAxisIotaClauses
  constructorsComputed := by
    intro constructorName membership
    simp [refinementAxisConstructors,
      refinementAxisBudgetConstructorSpec,
      refinementAxisAuthorityConstructorSpec] at membership
    rcases membership with rfl | rfl <;>
      simp [refinementAxisIotaClauses,
        refinementAxisBudgetIotaClause,
        refinementAxisAuthorityIotaClause]

/-! ## Positive and negative controls -/

theorem refinementAxisBudget_ne_authority {n : Nat} :
    (refinementAxisBudgetTm (n := n) : Tower.Tm n) ≠
      (refinementAxisAuthorityTm (n := n) : Tower.Tm n) := by
  simp [refinementAxisBudgetTm, refinementAxisAuthorityTm,
    refinementAxisBudgetName, refinementAxisAuthorityName]

/-! ## Exact external carrier model -/

abbrev SemanticRefinementAxis :=
  Mettapedia.TypeTheory.AuthorityTheory.Outcome.RefinementAxis

/-- Canonical closed inhabitants of the native axis declaration.  This is
an evidence-bearing image predicate, not an endpoint-only Boolean test. -/
inductive RefinementAxisCanonical : Tower.Tm 0 → Type where
  | budget : RefinementAxisCanonical refinementAxisBudgetTm
  | authority : RefinementAxisCanonical refinementAxisAuthorityTm

/-- The informative carrier of a canonical code retains both the raw term
and the witness that it belongs to the native axis image. -/
abbrev RefinementAxisCode :=
  Σ term : Tower.Tm 0, RefinementAxisCanonical term

def encodeRefinementAxis : SemanticRefinementAxis → RefinementAxisCode
  | .budget => ⟨refinementAxisBudgetTm, .budget⟩
  | .authority => ⟨refinementAxisAuthorityTm, .authority⟩

def decodeRefinementAxis : RefinementAxisCode → SemanticRefinementAxis
  | ⟨_, .budget⟩ => .budget
  | ⟨_, .authority⟩ => .authority

@[simp] theorem decode_encode_refinementAxis
    (axis : SemanticRefinementAxis) :
    decodeRefinementAxis (encodeRefinementAxis axis) = axis := by
  cases axis <;> rfl

@[simp] theorem encode_decode_refinementAxis
    (code : RefinementAxisCode) :
    encodeRefinementAxis (decodeRefinementAxis code) = code := by
  rcases code with ⟨_, witness⟩
  cases witness <;> rfl

/-- Native canonical axis codes and the abstract semantic carrier are
exactly equivalent. -/
def refinementAxisCodeEquiv :
    RefinementAxisCode ≃ SemanticRefinementAxis where
  toFun := decodeRefinementAxis
  invFun := encodeRefinementAxis
  left_inv := encode_decode_refinementAxis
  right_inv := decode_encode_refinementAxis

theorem refinementAxisCanonical_exclusive
    {term : Tower.Tm 0}
    (budgetCode : term = refinementAxisBudgetTm)
    (authorityCode : term = refinementAxisAuthorityTm) : False := by
  exact refinementAxisBudget_ne_authority
    (budgetCode.symm.trans authorityCode)

#print axioms rawRefinementAxisSignature_formed
#print axioms refinementAxisBudgetIotaReceipt
#print axioms refinementAxisAuthorityIotaReceipt
#print axioms refinementAxisCandidate
#print axioms refinementAxisBudget_ne_authority
#print axioms refinementAxisCodeEquiv
#print axioms refinementAxisCanonical_exclusive

end Intrinsic
end InternalAuthorityMetatheory
end Mettapedia.Languages.MeTTa.PureKernel.Universe
