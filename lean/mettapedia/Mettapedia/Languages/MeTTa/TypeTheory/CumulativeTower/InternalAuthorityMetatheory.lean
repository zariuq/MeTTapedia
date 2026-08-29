import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.OutcomeContract
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.IndexedFamilyDeclaration
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SchemaElaboration

/-!
# Prime's authority metatheory as ordinary indexed data

The reusable authority algebra lives in `Mettapedia.TypeTheory.Authority`.
This module instantiates its type-valued, strictly-positive presentation with
Prime's exact judgment universe.  It proves that the existing external Lean
contracts are models of the resulting indexed outcome, run, and receipt data.

The generic semantic algebra and its Prime model remain separate from the
intrinsic declaration.  This module now constructs `Outcome` itself as a
formed, strictly-positive Prime family with a dependent eliminator and four
typed proof-relevant computation schemas.  Intrinsic `Run` and `Receipt`,
contextual universe codes, and raw subject preservation remain later layers.
Keeping those boundaries explicit prevents either a semantic model or a
formed candidate from masquerading as checked computational authority.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace InternalAuthorityMetatheory

open Mettapedia.TypeTheory.AuthorityTheory
open Presentation.OutcomeContract

/-! ## Intrinsic signature data in the cumulative Prime tower -/

namespace Intrinsic

open Presentation
open Presentation.SchemaElaboration
open Presentation.Declaration
open Presentation.Declaration.ComputationAuthority
open Presentation.Declaration.IndexedFamily

/-- Universe of judgments described by one internal authority signature. -/
def judgmentLevel : LevelExpr := .param 0

/-- The four payload families are independently universe-polymorphic.  A
common upper level is therefore an instance of this signature, not a ceiling
built into it. -/
def evidenceLevel : LevelExpr := .param 1
def obstructionLevel : LevelExpr := .param 2
def boundaryLevel : LevelExpr := .param 3
def frontierLevel : LevelExpr := .param 4

/-- The universe containing a family `J → U payload`. -/
def familyLevel (payload : LevelExpr) : LevelExpr :=
  .max judgmentLevel (.succ payload)

/-- The universe containing the complete outcome signature. -/
def boundaryFrontierLevel : LevelExpr :=
  .max (familyLevel boundaryLevel) (familyLevel frontierLevel)

def obstructionTailLevel : LevelExpr :=
  .max (familyLevel obstructionLevel) boundaryFrontierLevel

def familyBundleLevel : LevelExpr :=
  .max (familyLevel evidenceLevel) obstructionTailLevel

def signatureLevel : LevelExpr :=
  .max (.succ judgmentLevel) familyBundleLevel

/-- A type-valued payload family over a judgment type. -/
def familyType (payload : LevelExpr) (judgmentType : Tower.Tm n) :
    Tower.Tm n :=
  .pi judgmentType (sortTm payload)

@[simp] theorem rename_familyType (renameMap : Ren n m)
    (payload : LevelExpr) (judgmentType : Tower.Tm n) :
    Presentation.rename renameMap (familyType payload judgmentType) =
      familyType payload (Presentation.rename renameMap judgmentType) :=
  rfl

@[simp] theorem subst_familyType (substitution : Sub Tower.Head n m)
    (payload : LevelExpr) (judgmentType : Tower.Tm n) :
    Presentation.subst substitution (familyType payload judgmentType) =
      familyType payload (Presentation.subst substitution judgmentType) :=
  rfl

/-- `J → U payload` is itself a type in the predicted cumulative
universe. -/
theorem familyType_hasType {context : Tower.Ctx n}
    (payload : LevelExpr) {judgmentType : Tower.Tm n}
    (judgmentTyping : Tower.HasType context judgmentType
      (sortTm judgmentLevel)) :
    Tower.HasType context (familyType payload judgmentType)
      (sortTm (familyLevel payload)) := by
  unfold familyType familyLevel
  apply Presentation.HasType.piForm judgmentTyping (.sort judgmentLevel)
  · exact .headType (.sort payload)
  · exact .sort (.succ payload)
  · exact .sorts judgmentLevel (.succ payload)

/-- Contexts used to expose the five informative components of an outcome
signature.  In the final context their de Bruijn order is `F,B,O,E,J`. -/
def signatureContextJ : Tower.Ctx 1 :=
  .snoc .nil (sortTm judgmentLevel)

def signatureContextJE : Tower.Ctx 2 :=
  .snoc signatureContextJ (familyType evidenceLevel (.var 0))

def signatureContextJEO : Tower.Ctx 3 :=
  .snoc signatureContextJE (familyType obstructionLevel (.var 1))

def signatureContextJEOB : Tower.Ctx 4 :=
  .snoc signatureContextJEO (familyType boundaryLevel (.var 2))

def signatureContextJEOBF : Tower.Ctx 5 :=
  .snoc signatureContextJEOB (familyType frontierLevel (.var 3))

/-- After choosing `J`, an outcome signature retains four independently
typed payload families.  Nested dependent sums make the data inspectable by
ordinary Prime projections. -/
def outcomeSignatureBody : Tower.Tm 1 :=
  .sigma (familyType evidenceLevel (.var 0))
    (.sigma (familyType obstructionLevel (.var 1))
      (.sigma (familyType boundaryLevel (.var 2))
        (familyType frontierLevel (.var 3))))

/-- First-class outcome signatures are stratified data:
`Sigma (J : U judgmentLevel),
  (J → U evidenceLevel) × (J → U obstructionLevel) ×
  (J → U boundaryLevel) × (J → U frontierLevel)`. -/
def outcomeSignatureType : Tower.Tm 0 :=
  .sigma (sortTm judgmentLevel) outcomeSignatureBody

theorem outcomeSignatureBody_hasType :
    Tower.HasType signatureContextJ outcomeSignatureBody
      (sortTm familyBundleLevel) := by
  unfold outcomeSignatureBody signatureContextJ
  apply Presentation.HasType.sigmaForm
      (familyType_hasType evidenceLevel (Presentation.HasType.var 0))
      (.sort (familyLevel evidenceLevel))
  · apply Presentation.HasType.sigmaForm
        (familyType_hasType obstructionLevel (Presentation.HasType.var 1))
        (.sort (familyLevel obstructionLevel))
    · apply Presentation.HasType.sigmaForm
          (familyType_hasType boundaryLevel (Presentation.HasType.var 2))
          (.sort (familyLevel boundaryLevel))
      · exact familyType_hasType frontierLevel (Presentation.HasType.var 3)
      · exact .sort (familyLevel frontierLevel)
      · exact .sorts (familyLevel boundaryLevel) (familyLevel frontierLevel)
    · exact .sort boundaryFrontierLevel
    · exact .sorts (familyLevel obstructionLevel) boundaryFrontierLevel
  · exact .sort obstructionTailLevel
  · exact .sorts (familyLevel evidenceLevel) obstructionTailLevel

/-- The intrinsic outcome signature lives strictly above its judgment and
payload components in the cumulative tower. -/
theorem outcomeSignatureType_hasType :
    Tower.HasType (.nil : Tower.Ctx 0) outcomeSignatureType
      (sortTm signatureLevel) := by
  unfold outcomeSignatureType signatureLevel
  apply Presentation.HasType.sigmaForm
      (Presentation.HasType.headType (Tower.HeadTyping.sort judgmentLevel))
      (Tower.IsUniverse.sort (.succ judgmentLevel))
  · exact outcomeSignatureBody_hasType
  · exact .sort familyBundleLevel
  · exact .sorts (.succ judgmentLevel) familyBundleLevel

/-- The authored components reassemble into a first-class signature value.
This is the positive control that the intrinsic record is data rather than a
mere well-formed type expression. -/
def parameterSignatureValue : Tower.Tm 5 :=
  .pair (.var 4)
    (.pair (.var 3)
      (.pair (.var 2)
        (.pair (.var 1) (.var 0))))

theorem parameterSignatureValue_hasType :
    Tower.HasType signatureContextJEOBF parameterSignatureValue
      (liftClosed outcomeSignatureType) := by
  unfold parameterSignatureValue signatureContextJEOBF signatureContextJEOB
    signatureContextJEO signatureContextJE signatureContextJ
    outcomeSignatureType outcomeSignatureBody
  apply Presentation.HasType.pairIntro (Presentation.HasType.var 4)
  apply Presentation.HasType.pairIntro (Presentation.HasType.var 3)
  apply Presentation.HasType.pairIntro (Presentation.HasType.var 2)
  apply Presentation.HasType.pairIntro (Presentation.HasType.var 1)
  exact Presentation.HasType.var 0

/-! ## The intrinsic indexed outcome family -/

/-- Elimination may target an independently chosen universe. -/
def motiveLevel : LevelExpr := .param 5

/-- The smallest universe containing all four outcome payloads. -/
def outcomeLevel : LevelExpr :=
  .max evidenceLevel
    (.max obstructionLevel (.max boundaryLevel frontierLevel))

def outcomeName : DeclName := `Prime.Authority.Outcome
def establishedName : DeclName := `Prime.Authority.Outcome.established
def refutedName : DeclName := `Prime.Authority.Outcome.refuted
def outsideFragmentName : DeclName :=
  `Prime.Authority.Outcome.outsideFragment
def incompleteName : DeclName := `Prime.Authority.Outcome.incomplete
def outcomeEliminateName : DeclName := `Prime.Authority.Outcome.eliminate

/-! A first-class signature is the sole parameter of the outcome family.
The familiar judgment and four payload families are recovered by projection,
so authority signatures can themselves be stored, transformed, and compared
as Prime data. -/

def signatureJudgment (signature : Tower.Tm n) : Tower.Tm n :=
  .fst signature

def signatureEvidence (signature : Tower.Tm n) : Tower.Tm n :=
  .fst (.snd signature)

def signatureObstruction (signature : Tower.Tm n) : Tower.Tm n :=
  .fst (.snd (.snd signature))

def signatureBoundary (signature : Tower.Tm n) : Tower.Tm n :=
  .fst (.snd (.snd (.snd signature)))

def signatureFrontier (signature : Tower.Tm n) : Tower.Tm n :=
  .snd (.snd (.snd (.snd signature)))

@[simp] theorem rename_signatureJudgment (renameMap : Ren n m)
    (signature : Tower.Tm n) :
    Presentation.rename renameMap (signatureJudgment signature) =
      signatureJudgment (Presentation.rename renameMap signature) := rfl

@[simp] theorem rename_signatureEvidence (renameMap : Ren n m)
    (signature : Tower.Tm n) :
    Presentation.rename renameMap (signatureEvidence signature) =
      signatureEvidence (Presentation.rename renameMap signature) := rfl

@[simp] theorem rename_signatureObstruction (renameMap : Ren n m)
    (signature : Tower.Tm n) :
    Presentation.rename renameMap (signatureObstruction signature) =
      signatureObstruction (Presentation.rename renameMap signature) := rfl

@[simp] theorem rename_signatureBoundary (renameMap : Ren n m)
    (signature : Tower.Tm n) :
    Presentation.rename renameMap (signatureBoundary signature) =
      signatureBoundary (Presentation.rename renameMap signature) := rfl

@[simp] theorem rename_signatureFrontier (renameMap : Ren n m)
    (signature : Tower.Tm n) :
    Presentation.rename renameMap (signatureFrontier signature) =
      signatureFrontier (Presentation.rename renameMap signature) := rfl

@[simp] theorem subst_signatureJudgment (substitution : Sub Tower.Head n m)
    (signature : Tower.Tm n) :
    Presentation.subst substitution (signatureJudgment signature) =
      signatureJudgment (Presentation.subst substitution signature) := rfl

@[simp] theorem subst_signatureEvidence (substitution : Sub Tower.Head n m)
    (signature : Tower.Tm n) :
    Presentation.subst substitution (signatureEvidence signature) =
      signatureEvidence (Presentation.subst substitution signature) := rfl

@[simp] theorem subst_signatureObstruction
    (substitution : Sub Tower.Head n m) (signature : Tower.Tm n) :
    Presentation.subst substitution (signatureObstruction signature) =
      signatureObstruction (Presentation.subst substitution signature) := rfl

@[simp] theorem subst_signatureBoundary (substitution : Sub Tower.Head n m)
    (signature : Tower.Tm n) :
    Presentation.subst substitution (signatureBoundary signature) =
      signatureBoundary (Presentation.subst substitution signature) := rfl

@[simp] theorem subst_signatureFrontier (substitution : Sub Tower.Head n m)
    (signature : Tower.Tm n) :
    Presentation.subst substitution (signatureFrontier signature) =
      signatureFrontier (Presentation.subst substitution signature) := rfl

def outcomeApp (signature judgment : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.const outcomeName) signature) judgment

@[simp] theorem rename_outcomeApp (renameMap : Ren n m)
    (signature judgment : Tower.Tm n) :
    Presentation.rename renameMap (outcomeApp signature judgment) =
      outcomeApp (Presentation.rename renameMap signature)
        (Presentation.rename renameMap judgment) := rfl

@[simp] theorem subst_outcomeApp (substitution : Sub Tower.Head n m)
    (signature judgment : Tower.Tm n) :
    Presentation.subst substitution (outcomeApp signature judgment) =
      outcomeApp (Presentation.subst substitution signature)
        (Presentation.subst substitution judgment) := rfl

def establishedApp (signature judgment witness : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.const establishedName) signature) judgment) witness

def refutedApp (signature judgment witness : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.const refutedName) signature) judgment) witness

def outsideFragmentApp (signature judgment witness : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.const outsideFragmentName) signature) judgment) witness

def incompleteApp (signature judgment witness : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.const incompleteName) signature) judgment) witness

def outcomeEliminateApp (signature motive establishedCase refutedCase
    outsideCase incompleteCase judgment outcome : Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app
        (.app
          (.app
            (.app
              (.app
                (.app (.const outcomeEliminateName) signature)
                motive)
              establishedCase)
            refutedCase)
          outsideCase)
        incompleteCase)
      judgment)
    outcome

/-- `Outcome : (signature : OutcomeSignature) → signature.J → U ω`. -/
def outcomeType : Tower.Tm 0 :=
  .pi outcomeSignatureType
    (.pi (signatureJudgment (.var 0)) (sortTm outcomeLevel))

/-- Constructor types below the common signature binder. -/
def establishedBodyType : Tower.Tm 1 :=
  .pi (signatureJudgment (.var 0))
    (arrow (.app (signatureEvidence (.var 1)) (.var 0))
      (outcomeApp (.var 1) (.var 0)))

def establishedType : Tower.Tm 0 :=
  .pi outcomeSignatureType establishedBodyType

def refutedBodyType : Tower.Tm 1 :=
  .pi (signatureJudgment (.var 0))
    (arrow (.app (signatureObstruction (.var 1)) (.var 0))
      (outcomeApp (.var 1) (.var 0)))

def refutedType : Tower.Tm 0 :=
  .pi outcomeSignatureType refutedBodyType

def outsideFragmentBodyType : Tower.Tm 1 :=
  .pi (signatureJudgment (.var 0))
    (arrow (.app (signatureBoundary (.var 1)) (.var 0))
      (outcomeApp (.var 1) (.var 0)))

def outsideFragmentType : Tower.Tm 0 :=
  .pi outcomeSignatureType outsideFragmentBodyType

def incompleteBodyType : Tower.Tm 1 :=
  .pi (signatureJudgment (.var 0))
    (arrow (.app (signatureFrontier (.var 1)) (.var 0))
      (outcomeApp (.var 1) (.var 0)))

def incompleteType : Tower.Tm 0 :=
  .pi outcomeSignatureType incompleteBodyType

/-- In context `signature`, a motive observes the judgment and its outcome. -/
def outcomeMotiveType : Tower.Tm 1 :=
  .pi (signatureJudgment (.var 0))
    (.pi (outcomeApp (.var 1) (.var 0)) (sortTm motiveLevel))

/-- All branch types are authored in the common context `signature,motive`.
They are weakened only when assembled into the eliminator telescope. -/
def establishedCaseType : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (.app (signatureEvidence (.var 2)) (.var 0))
      (.app
        (.app (.var 2) (.var 1))
        (establishedApp (.var 3) (.var 1) (.var 0))))

def refutedCaseType : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (.app (signatureObstruction (.var 2)) (.var 0))
      (.app
        (.app (.var 2) (.var 1))
        (refutedApp (.var 3) (.var 1) (.var 0))))

def outsideFragmentCaseType : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (.app (signatureBoundary (.var 2)) (.var 0))
      (.app
        (.app (.var 2) (.var 1))
        (outsideFragmentApp (.var 3) (.var 1) (.var 0))))

def incompleteCaseType : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (.app (signatureFrontier (.var 2)) (.var 0))
      (.app
        (.app (.var 2) (.var 1))
        (incompleteApp (.var 3) (.var 1) (.var 0))))

def outcomeEliminateResultType : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (outcomeApp (.var 2) (.var 0))
      (.app (.app (.var 2) (.var 1)) (.var 0)))

def outcomeEliminateBodyType : Tower.Tm 1 :=
  .pi outcomeMotiveType
    (.pi establishedCaseType
      (.pi (Presentation.rename wk refutedCaseType)
        (.pi
          (Presentation.rename wk
            (Presentation.rename wk outsideFragmentCaseType))
          (.pi
            (Presentation.rename wk
              (Presentation.rename wk
                (Presentation.rename wk incompleteCaseType)))
            (Presentation.rename wk
              (Presentation.rename wk
                (Presentation.rename wk
                  (Presentation.rename wk outcomeEliminateResultType))))))))

def outcomeEliminateType : Tower.Tm 0 :=
  .pi outcomeSignatureType outcomeEliminateBodyType

/-! ### Proof-relevant computation generators -/

inductive OutcomeIotaEvidence (n : Nat) :
    Tower.Tm n → Tower.Tm n → Type where
  | established (signature motive establishedCase refutedCase outsideCase
      incompleteCase judgment witness : Tower.Tm n) :
      OutcomeIotaEvidence n
        (outcomeEliminateApp signature motive establishedCase refutedCase
          outsideCase incompleteCase judgment
          (establishedApp signature judgment witness))
        (.app (.app establishedCase judgment) witness)
  | refuted (signature motive establishedCase refutedCase outsideCase
      incompleteCase judgment witness : Tower.Tm n) :
      OutcomeIotaEvidence n
        (outcomeEliminateApp signature motive establishedCase refutedCase
          outsideCase incompleteCase judgment
          (refutedApp signature judgment witness))
        (.app (.app refutedCase judgment) witness)
  | outsideFragment (signature motive establishedCase refutedCase outsideCase
      incompleteCase judgment witness : Tower.Tm n) :
      OutcomeIotaEvidence n
        (outcomeEliminateApp signature motive establishedCase refutedCase
          outsideCase incompleteCase judgment
          (outsideFragmentApp signature judgment witness))
        (.app (.app outsideCase judgment) witness)
  | incomplete (signature motive establishedCase refutedCase outsideCase
      incompleteCase judgment witness : Tower.Tm n) :
      OutcomeIotaEvidence n
        (outcomeEliminateApp signature motive establishedCase refutedCase
          outsideCase incompleteCase judgment
          (incompleteApp signature judgment witness))
        (.app (.app incompleteCase judgment) witness)

def OutcomeIotaEvidence.rename {left right : Tower.Tm n}
    (step : OutcomeIotaEvidence n left right) (renameMap : Ren n m) :
    OutcomeIotaEvidence m (Presentation.rename renameMap left)
      (Presentation.rename renameMap right) := by
  cases step with
  | established => exact .established _ _ _ _ _ _ _ _
  | refuted => exact .refuted _ _ _ _ _ _ _ _
  | outsideFragment => exact .outsideFragment _ _ _ _ _ _ _ _
  | incomplete => exact .incomplete _ _ _ _ _ _ _ _

def OutcomeIotaEvidence.substitute {left right : Tower.Tm n}
    (step : OutcomeIotaEvidence n left right)
    (substitution : Sub Tower.Head n m) :
    OutcomeIotaEvidence m (Presentation.subst substitution left)
      (Presentation.subst substitution right) := by
  cases step with
  | established => exact .established _ _ _ _ _ _ _ _
  | refuted => exact .refuted _ _ _ _ _ _ _ _
  | outsideFragment => exact .outsideFragment _ _ _ _ _ _ _ _
  | incomplete => exact .incomplete _ _ _ _ _ _ _ _

def proofRelevantOutcomeComputation :
    ProofRelevantRootComputation Tower.Head where
  Evidence := OutcomeIotaEvidence _
  rename := by
    intro n m renameMap left right step
    exact step.rename renameMap
  substitute := by
    intro n m substitution left right step
    exact step.substitute substitution

def outcomeComputation : RootComputation Tower.Head :=
  proofRelevantOutcomeComputation.support

/-! ### Declaration signature -/

def outcomeDeclarations : List (DeclName × Entry Tower.Head) :=
  [(outcomeName, { type := outcomeType }),
   (establishedName, { type := establishedType }),
   (refutedName, { type := refutedType }),
   (outsideFragmentName, { type := outsideFragmentType }),
   (incompleteName, { type := incompleteType }),
   (outcomeEliminateName, { type := outcomeEliminateType })]

def rawOutcomeSignature : Signature Tower.Head where
  entries := (Signature.ofList outcomeDeclarations).entries
  computation := outcomeComputation

abbrev outcomeRules : Rules Tower.Head :=
  extendRules Tower.rules rawOutcomeSignature

@[simp] theorem typeOf_outcome :
    rawOutcomeSignature.typeOf? outcomeName = some outcomeType := by
  simp [rawOutcomeSignature, outcomeDeclarations, outcomeName,
    establishedName, refutedName, outsideFragmentName, incompleteName,
    outcomeEliminateName, Signature.ofList, Signature.insert,
    Signature.typeOf?]

@[simp] theorem typeOf_established :
    rawOutcomeSignature.typeOf? establishedName = some establishedType := by
  simp [rawOutcomeSignature, outcomeDeclarations, outcomeName,
    establishedName, refutedName, outsideFragmentName, incompleteName,
    outcomeEliminateName, Signature.ofList, Signature.insert,
    Signature.typeOf?]

@[simp] theorem typeOf_refuted :
    rawOutcomeSignature.typeOf? refutedName = some refutedType := by
  simp [rawOutcomeSignature, outcomeDeclarations, outcomeName,
    establishedName, refutedName, outsideFragmentName, incompleteName,
    outcomeEliminateName, Signature.ofList, Signature.insert,
    Signature.typeOf?]

@[simp] theorem typeOf_outsideFragment :
    rawOutcomeSignature.typeOf? outsideFragmentName =
      some outsideFragmentType := by
  simp [rawOutcomeSignature, outcomeDeclarations, outcomeName,
    establishedName, refutedName, outsideFragmentName, incompleteName,
    outcomeEliminateName, Signature.ofList, Signature.insert,
    Signature.typeOf?]

@[simp] theorem typeOf_incomplete :
    rawOutcomeSignature.typeOf? incompleteName = some incompleteType := by
  simp [rawOutcomeSignature, outcomeDeclarations, outcomeName,
    establishedName, refutedName, outsideFragmentName, incompleteName,
    outcomeEliminateName, Signature.ofList, Signature.insert,
    Signature.typeOf?]

@[simp] theorem typeOf_outcomeEliminate :
    rawOutcomeSignature.typeOf? outcomeEliminateName =
      some outcomeEliminateType := by
  simp [rawOutcomeSignature, outcomeDeclarations, outcomeName,
    establishedName, refutedName, outsideFragmentName, incompleteName,
    outcomeEliminateName, Signature.ofList, Signature.insert,
    Signature.typeOf?]

/-! ### Projection and application typing -/

abbrev IntrinsicHasType {n : Nat} :=
  @Presentation.HasType Tower.Head outcomeRules n

private theorem declaredOutcomeConstant_hasType
    {name : DeclName} {type : Tower.Tm 0}
    (lookup : rawOutcomeSignature.typeOf? name = some type)
    {context : Tower.Ctx n} :
    IntrinsicHasType context (.const name) (liftClosed type) := by
  apply Presentation.HasType.const
  change combinedType Tower.rules rawOutcomeSignature name = some type
  apply combinedType_of_signature
  · rfl
  · exact lookup

theorem outcomeConstant_hasType {context : Tower.Ctx n} :
    IntrinsicHasType context (.const outcomeName) (liftClosed outcomeType) :=
  declaredOutcomeConstant_hasType typeOf_outcome

theorem establishedConstant_hasType {context : Tower.Ctx n} :
    IntrinsicHasType context (.const establishedName)
      (liftClosed establishedType) :=
  declaredOutcomeConstant_hasType typeOf_established

theorem refutedConstant_hasType {context : Tower.Ctx n} :
    IntrinsicHasType context (.const refutedName) (liftClosed refutedType) :=
  declaredOutcomeConstant_hasType typeOf_refuted

theorem outsideFragmentConstant_hasType {context : Tower.Ctx n} :
    IntrinsicHasType context (.const outsideFragmentName)
      (liftClosed outsideFragmentType) :=
  declaredOutcomeConstant_hasType typeOf_outsideFragment

theorem incompleteConstant_hasType {context : Tower.Ctx n} :
    IntrinsicHasType context (.const incompleteName)
      (liftClosed incompleteType) :=
  declaredOutcomeConstant_hasType typeOf_incomplete

theorem outcomeEliminateConstant_hasType {context : Tower.Ctx n} :
    IntrinsicHasType context (.const outcomeEliminateName)
      (liftClosed outcomeEliminateType) :=
  declaredOutcomeConstant_hasType typeOf_outcomeEliminate

/-- Successive tails of the dependent signature record.  Writing each
codomain as an explicit weakening exposes the context-comprehension beta law
used by Σ projections. -/
def signatureAfterBoundary (judgmentType : Tower.Tm n) : Tower.Tm n :=
  familyType frontierLevel judgmentType

def signatureAfterObstruction (judgmentType : Tower.Tm n) : Tower.Tm n :=
  .sigma (familyType boundaryLevel judgmentType)
    (Presentation.rename wk (signatureAfterBoundary judgmentType))

def signatureAfterEvidence (judgmentType : Tower.Tm n) : Tower.Tm n :=
  .sigma (familyType obstructionLevel judgmentType)
    (Presentation.rename wk (signatureAfterObstruction judgmentType))

def signatureAfterJudgment (judgmentType : Tower.Tm n) : Tower.Tm n :=
  .sigma (familyType evidenceLevel judgmentType)
    (Presentation.rename wk (signatureAfterEvidence judgmentType))

@[simp] theorem subst_signatureAfterBoundary
    (substitution : Sub Tower.Head n m) (judgmentType : Tower.Tm n) :
    Presentation.subst substitution (signatureAfterBoundary judgmentType) =
      signatureAfterBoundary (Presentation.subst substitution judgmentType) := by
  simp [signatureAfterBoundary]

@[simp] theorem subst_signatureAfterObstruction
    (substitution : Sub Tower.Head n m) (judgmentType : Tower.Tm n) :
    Presentation.subst substitution
        (signatureAfterObstruction judgmentType) =
      signatureAfterObstruction
        (Presentation.subst substitution judgmentType) := by
  simp [signatureAfterObstruction, Presentation.subst]

@[simp] theorem subst_signatureAfterEvidence
    (substitution : Sub Tower.Head n m) (judgmentType : Tower.Tm n) :
    Presentation.subst substitution (signatureAfterEvidence judgmentType) =
      signatureAfterEvidence
        (Presentation.subst substitution judgmentType) := by
  simp [signatureAfterEvidence, Presentation.subst]

@[simp] theorem subst_signatureAfterJudgment
    (substitution : Sub Tower.Head n m) (judgmentType : Tower.Tm n) :
    Presentation.subst substitution (signatureAfterJudgment judgmentType) =
      signatureAfterJudgment
        (Presentation.subst substitution judgmentType) := by
  simp [signatureAfterJudgment, Presentation.subst]

theorem outcomeSignatureBody_asSuccessiveTails :
    outcomeSignatureBody = signatureAfterJudgment (.var 0) := by
  decide

@[simp] theorem substitute_outcomeSignatureBody
    (judgmentType : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => judgmentType)
      outcomeSignatureBody =
      signatureAfterJudgment judgmentType := by
  rw [outcomeSignatureBody_asSuccessiveTails]
  simp

theorem signatureJudgment_hasType {rules : Rules Tower.Head}
    {context : Tower.Ctx n}
    {signature : Tower.Tm n}
    (signatureTyping : Presentation.HasType rules context signature
      (liftClosed outcomeSignatureType)) :
    Presentation.HasType rules context (signatureJudgment signature)
      (sortTm judgmentLevel) := by
  have projection := Presentation.HasType.fstElim signatureTyping
  simpa [signatureJudgment, outcomeSignatureType, liftClosed, sortTm,
    Presentation.rename] using projection

theorem signatureEvidence_hasType {rules : Rules Tower.Head}
    {context : Tower.Ctx n}
    {signature : Tower.Tm n}
    (signatureTyping : Presentation.HasType rules context signature
      (liftClosed outcomeSignatureType)) :
    Presentation.HasType rules context (signatureEvidence signature)
      (familyType evidenceLevel (signatureJudgment signature)) := by
  have tail := Presentation.HasType.sndElim signatureTyping
  have tailTyping :
      Presentation.HasType rules context (.snd signature)
        (signatureAfterJudgment (.fst signature)) := by
    simpa only [outcomeSignatureType, liftClosed,
      inst0_rename_liftRen_elim0, substitute_outcomeSignatureBody] using tail
  simpa only [signatureEvidence, signatureJudgment,
    signatureAfterJudgment] using
    (Presentation.HasType.fstElim tailTyping)

theorem signatureObstruction_hasType {rules : Rules Tower.Head}
    {context : Tower.Ctx n}
    {signature : Tower.Tm n}
    (signatureTyping : Presentation.HasType rules context signature
      (liftClosed outcomeSignatureType)) :
    Presentation.HasType rules context (signatureObstruction signature)
      (familyType obstructionLevel (signatureJudgment signature)) := by
  have tail := Presentation.HasType.sndElim signatureTyping
  have tailTyping :
      Presentation.HasType rules context (.snd signature)
        (signatureAfterJudgment (.fst signature)) := by
    simpa only [outcomeSignatureType, liftClosed,
      inst0_rename_liftRen_elim0, substitute_outcomeSignatureBody] using tail
  have later := Presentation.HasType.sndElim tailTyping
  have laterTyping :
      Presentation.HasType rules context (.snd (.snd signature))
        (signatureAfterEvidence (.fst signature)) := by
    simpa only [signatureAfterJudgment, inst0_rename_wk] using later
  simpa only [signatureObstruction, signatureJudgment,
    signatureAfterEvidence] using
    (Presentation.HasType.fstElim laterTyping)

theorem signatureBoundary_hasType {rules : Rules Tower.Head}
    {context : Tower.Ctx n}
    {signature : Tower.Tm n}
    (signatureTyping : Presentation.HasType rules context signature
      (liftClosed outcomeSignatureType)) :
    Presentation.HasType rules context (signatureBoundary signature)
      (familyType boundaryLevel (signatureJudgment signature)) := by
  have tail := Presentation.HasType.sndElim signatureTyping
  have tailTyping :
      Presentation.HasType rules context (.snd signature)
        (signatureAfterJudgment (.fst signature)) := by
    simpa only [outcomeSignatureType, liftClosed,
      inst0_rename_liftRen_elim0, substitute_outcomeSignatureBody] using tail
  have obstructionTail := Presentation.HasType.sndElim tailTyping
  have obstructionTailTyping :
      Presentation.HasType rules context (.snd (.snd signature))
        (signatureAfterEvidence (.fst signature)) := by
    simpa only [signatureAfterJudgment, inst0_rename_wk] using obstructionTail
  have boundaryTail := Presentation.HasType.sndElim obstructionTailTyping
  have boundaryTailTyping :
      Presentation.HasType rules context (.snd (.snd (.snd signature)))
        (signatureAfterObstruction (.fst signature)) := by
    simpa only [signatureAfterEvidence, inst0_rename_wk] using boundaryTail
  simpa only [signatureBoundary, signatureJudgment,
    signatureAfterObstruction] using
    (Presentation.HasType.fstElim boundaryTailTyping)

theorem signatureFrontier_hasType {rules : Rules Tower.Head}
    {context : Tower.Ctx n}
    {signature : Tower.Tm n}
    (signatureTyping : Presentation.HasType rules context signature
      (liftClosed outcomeSignatureType)) :
    Presentation.HasType rules context (signatureFrontier signature)
      (familyType frontierLevel (signatureJudgment signature)) := by
  have tail := Presentation.HasType.sndElim signatureTyping
  have tailTyping :
      Presentation.HasType rules context (.snd signature)
        (signatureAfterJudgment (.fst signature)) := by
    simpa only [outcomeSignatureType, liftClosed,
      inst0_rename_liftRen_elim0, substitute_outcomeSignatureBody] using tail
  have obstructionTail := Presentation.HasType.sndElim tailTyping
  have obstructionTailTyping :
      Presentation.HasType rules context (.snd (.snd signature))
        (signatureAfterEvidence (.fst signature)) := by
    simpa only [signatureAfterJudgment, inst0_rename_wk] using obstructionTail
  have boundaryTail := Presentation.HasType.sndElim obstructionTailTyping
  have boundaryTailTyping :
      Presentation.HasType rules context (.snd (.snd (.snd signature)))
        (signatureAfterObstruction (.fst signature)) := by
    simpa only [signatureAfterEvidence, inst0_rename_wk] using boundaryTail
  have frontier := Presentation.HasType.sndElim boundaryTailTyping
  simpa only [signatureFrontier, signatureJudgment,
    signatureAfterObstruction, signatureAfterBoundary,
    inst0_rename_wk] using frontier

theorem familyApp_hasType {rules : Rules Tower.Head}
    {context : Tower.Ctx n}
    {payload : LevelExpr} {judgmentType family judgment : Tower.Tm n}
    (familyTyping : Presentation.HasType rules context family
      (familyType payload judgmentType))
    (judgmentTyping : Presentation.HasType rules context judgment judgmentType) :
    Presentation.HasType rules context (.app family judgment)
      (sortTm payload) := by
  have application := Presentation.HasType.appElim familyTyping judgmentTyping
  simpa [familyType, sortTm, Presentation.inst0, Presentation.subst] using
    application

theorem outcomeApp_hasTypeWith {rules : Rules Tower.Head}
    {context : Tower.Ctx n}
    {signature judgment : Tower.Tm n}
    (outcomeTyping : Presentation.HasType rules context (.const outcomeName)
      (liftClosed outcomeType))
    (signatureTyping : Presentation.HasType rules context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : Presentation.HasType rules context judgment
      (signatureJudgment signature)) :
    Presentation.HasType rules context (outcomeApp signature judgment)
      (sortTm outcomeLevel) := by
  have afterSignature := Presentation.HasType.appElim
    outcomeTyping signatureTyping
  have afterJudgment := Presentation.HasType.appElim afterSignature
    judgmentTyping
  simpa [outcomeType, outcomeApp, signatureJudgment, liftClosed, sortTm,
    Presentation.rename, Presentation.inst0, Presentation.subst,
    Presentation.subst0, Presentation.liftSub] using afterJudgment

theorem outcomeApp_hasType {context : Tower.Ctx n}
    {signature judgment : Tower.Tm n}
    (signatureTyping : IntrinsicHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : IntrinsicHasType context judgment
      (signatureJudgment signature)) :
    IntrinsicHasType context (outcomeApp signature judgment)
      (sortTm outcomeLevel) :=
  outcomeApp_hasTypeWith (outcomeConstant_hasType (context := context))
    signatureTyping judgmentTyping

/-- The constructor telescope after its signature parameter has been
instantiated.  The payload and result are nondependent in the final witness,
so the shared → constructor exposes both beta cancellations directly. -/
def constructorAtSignatureType (signature payloadFamily : Tower.Tm n) :
    Tower.Tm n :=
  .pi (signatureJudgment signature)
    (arrow
      (.app (Presentation.rename wk payloadFamily) (.var 0))
      (outcomeApp (Presentation.rename wk signature) (.var 0)))

/-- The unique old variable under one freshly introduced binder is the
weakened parameter.  Naming this finite-index fact keeps the signature
substitution laws independent of numeral normalization. -/
@[simp] theorem liftSub_singleParameter_one (term : Tower.Tm n) :
    Presentation.liftSub (fun _ : Fin 1 => term) (1 : Fin 2) =
      Presentation.rename wk term := by
  rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) by decide]
  rfl

@[simp] theorem inst0_familyApplication_wk (argument family : Tower.Tm n) :
    Presentation.inst0 argument
        (.app (Presentation.rename wk family) (.var 0)) =
      .app family argument := by
  calc
    Presentation.inst0 argument
        (.app (Presentation.rename wk family) (.var 0)) =
      .app
        (Presentation.inst0 argument (Presentation.rename wk family))
        (Presentation.inst0 argument (.var 0)) := rfl
    _ = .app family argument := by
      rw [inst0_rename_wk, Presentation.inst0_var_zero]

@[simp] theorem inst0_outcomeApplication_wk
    (argument signature : Tower.Tm n) :
    Presentation.inst0 argument
        (outcomeApp (Presentation.rename wk signature) (.var 0)) =
      outcomeApp signature argument := by
  calc
    Presentation.inst0 argument
        (outcomeApp (Presentation.rename wk signature) (.var 0)) =
      outcomeApp
        (Presentation.inst0 argument (Presentation.rename wk signature))
        (Presentation.inst0 argument (.var 0)) := rfl
    _ = outcomeApp signature argument := by
      rw [inst0_rename_wk, Presentation.inst0_var_zero]

@[simp] theorem inst0_signatureEvidenceApplication_wk
    (argument signature : Tower.Tm n) :
    Presentation.inst0 argument
        (.app (signatureEvidence (Presentation.rename wk signature))
          (.var 0)) =
      .app (signatureEvidence signature) argument := by
  change Presentation.inst0 argument
      (.app (Presentation.rename wk (signatureEvidence signature)) (.var 0)) =
    .app (signatureEvidence signature) argument
  exact inst0_familyApplication_wk argument (signatureEvidence signature)

@[simp] theorem inst0_signatureObstructionApplication_wk
    (argument signature : Tower.Tm n) :
    Presentation.inst0 argument
        (.app (signatureObstruction (Presentation.rename wk signature))
          (.var 0)) =
      .app (signatureObstruction signature) argument := by
  change Presentation.inst0 argument
      (.app (Presentation.rename wk (signatureObstruction signature)) (.var 0)) =
    .app (signatureObstruction signature) argument
  exact inst0_familyApplication_wk argument (signatureObstruction signature)

@[simp] theorem inst0_signatureBoundaryApplication_wk
    (argument signature : Tower.Tm n) :
    Presentation.inst0 argument
        (.app (signatureBoundary (Presentation.rename wk signature))
          (.var 0)) =
      .app (signatureBoundary signature) argument := by
  change Presentation.inst0 argument
      (.app (Presentation.rename wk (signatureBoundary signature)) (.var 0)) =
    .app (signatureBoundary signature) argument
  exact inst0_familyApplication_wk argument (signatureBoundary signature)

@[simp] theorem inst0_signatureFrontierApplication_wk
    (argument signature : Tower.Tm n) :
    Presentation.inst0 argument
        (.app (signatureFrontier (Presentation.rename wk signature))
          (.var 0)) =
      .app (signatureFrontier signature) argument := by
  change Presentation.inst0 argument
      (.app (Presentation.rename wk (signatureFrontier signature)) (.var 0)) =
    .app (signatureFrontier signature) argument
  exact inst0_familyApplication_wk argument (signatureFrontier signature)

@[simp] theorem substitute_establishedBodyType (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature) establishedBodyType =
      constructorAtSignatureType signature (signatureEvidence signature) := by
  simp [establishedBodyType, constructorAtSignatureType,
    Presentation.subst]

@[simp] theorem substitute_refutedBodyType (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature) refutedBodyType =
      constructorAtSignatureType signature
        (signatureObstruction signature) := by
  simp [refutedBodyType, constructorAtSignatureType, Presentation.subst]

@[simp] theorem substitute_outsideFragmentBodyType
    (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature)
        outsideFragmentBodyType =
      constructorAtSignatureType signature (signatureBoundary signature) := by
  simp [outsideFragmentBodyType, constructorAtSignatureType,
    Presentation.subst]

@[simp] theorem substitute_incompleteBodyType (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature) incompleteBodyType =
      constructorAtSignatureType signature (signatureFrontier signature) := by
  simp [incompleteBodyType, constructorAtSignatureType,
    Presentation.subst]

theorem establishedApp_hasType {context : Tower.Ctx n}
    {signature judgment witness : Tower.Tm n}
    (signatureTyping : IntrinsicHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : IntrinsicHasType context judgment
      (signatureJudgment signature))
    (witnessTyping : IntrinsicHasType context witness
      (.app (signatureEvidence signature) judgment)) :
    IntrinsicHasType context (establishedApp signature judgment witness)
      (outcomeApp signature judgment) := by
  have afterSignature := Presentation.HasType.appElim
    (establishedConstant_hasType (context := context)) signatureTyping
  have afterSignatureNormalized :
      IntrinsicHasType context (.app (.const establishedName) signature)
        (constructorAtSignatureType signature
          (signatureEvidence signature)) := by
    simpa only [establishedType, liftClosed,
      inst0_rename_liftRen_elim0, substitute_establishedBodyType] using
      afterSignature
  have afterJudgment := Presentation.HasType.appElim
    afterSignatureNormalized judgmentTyping
  have afterJudgmentNormalized :
      IntrinsicHasType context
        (.app (.app (.const establishedName) signature) judgment)
        (arrow (.app (signatureEvidence signature) judgment)
          (outcomeApp signature judgment)) := by
    simpa only [constructorAtSignatureType, inst0_arrow,
      inst0_signatureEvidenceApplication_wk, inst0_familyApplication_wk,
      inst0_outcomeApplication_wk] using afterJudgment
  have afterWitness := Presentation.HasType.appElim afterJudgmentNormalized
    witnessTyping
  simpa only [establishedApp, arrow, inst0_rename_wk] using afterWitness

theorem refutedApp_hasType {context : Tower.Ctx n}
    {signature judgment witness : Tower.Tm n}
    (signatureTyping : IntrinsicHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : IntrinsicHasType context judgment
      (signatureJudgment signature))
    (witnessTyping : IntrinsicHasType context witness
      (.app (signatureObstruction signature) judgment)) :
    IntrinsicHasType context (refutedApp signature judgment witness)
      (outcomeApp signature judgment) := by
  have afterSignature := Presentation.HasType.appElim
    (refutedConstant_hasType (context := context)) signatureTyping
  have afterSignatureNormalized :
      IntrinsicHasType context (.app (.const refutedName) signature)
        (constructorAtSignatureType signature
          (signatureObstruction signature)) := by
    simpa only [refutedType, liftClosed, inst0_rename_liftRen_elim0,
      substitute_refutedBodyType] using afterSignature
  have afterJudgment := Presentation.HasType.appElim
    afterSignatureNormalized judgmentTyping
  have afterJudgmentNormalized :
      IntrinsicHasType context
        (.app (.app (.const refutedName) signature) judgment)
        (arrow (.app (signatureObstruction signature) judgment)
          (outcomeApp signature judgment)) := by
    simpa only [constructorAtSignatureType, inst0_arrow,
      inst0_signatureObstructionApplication_wk, inst0_familyApplication_wk,
      inst0_outcomeApplication_wk] using afterJudgment
  have afterWitness := Presentation.HasType.appElim afterJudgmentNormalized
    witnessTyping
  simpa only [refutedApp, arrow, inst0_rename_wk] using afterWitness

theorem outsideFragmentApp_hasType {context : Tower.Ctx n}
    {signature judgment witness : Tower.Tm n}
    (signatureTyping : IntrinsicHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : IntrinsicHasType context judgment
      (signatureJudgment signature))
    (witnessTyping : IntrinsicHasType context witness
      (.app (signatureBoundary signature) judgment)) :
    IntrinsicHasType context (outsideFragmentApp signature judgment witness)
      (outcomeApp signature judgment) := by
  have afterSignature := Presentation.HasType.appElim
    (outsideFragmentConstant_hasType (context := context)) signatureTyping
  have afterSignatureNormalized :
      IntrinsicHasType context (.app (.const outsideFragmentName) signature)
        (constructorAtSignatureType signature
          (signatureBoundary signature)) := by
    simpa only [outsideFragmentType, liftClosed,
      inst0_rename_liftRen_elim0, substitute_outsideFragmentBodyType] using
      afterSignature
  have afterJudgment := Presentation.HasType.appElim
    afterSignatureNormalized judgmentTyping
  have afterJudgmentNormalized :
      IntrinsicHasType context
        (.app (.app (.const outsideFragmentName) signature) judgment)
        (arrow (.app (signatureBoundary signature) judgment)
          (outcomeApp signature judgment)) := by
    simpa only [constructorAtSignatureType, inst0_arrow,
      inst0_signatureBoundaryApplication_wk, inst0_familyApplication_wk,
      inst0_outcomeApplication_wk] using afterJudgment
  have afterWitness := Presentation.HasType.appElim afterJudgmentNormalized
    witnessTyping
  simpa only [outsideFragmentApp, arrow, inst0_rename_wk] using afterWitness

theorem incompleteApp_hasType {context : Tower.Ctx n}
    {signature judgment witness : Tower.Tm n}
    (signatureTyping : IntrinsicHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : IntrinsicHasType context judgment
      (signatureJudgment signature))
    (witnessTyping : IntrinsicHasType context witness
      (.app (signatureFrontier signature) judgment)) :
    IntrinsicHasType context (incompleteApp signature judgment witness)
      (outcomeApp signature judgment) := by
  have afterSignature := Presentation.HasType.appElim
    (incompleteConstant_hasType (context := context)) signatureTyping
  have afterSignatureNormalized :
      IntrinsicHasType context (.app (.const incompleteName) signature)
        (constructorAtSignatureType signature
          (signatureFrontier signature)) := by
    simpa only [incompleteType, liftClosed,
      inst0_rename_liftRen_elim0, substitute_incompleteBodyType] using
      afterSignature
  have afterJudgment := Presentation.HasType.appElim
    afterSignatureNormalized judgmentTyping
  have afterJudgmentNormalized :
      IntrinsicHasType context
        (.app (.app (.const incompleteName) signature) judgment)
        (arrow (.app (signatureFrontier signature) judgment)
          (outcomeApp signature judgment)) := by
    simpa only [constructorAtSignatureType, inst0_arrow,
      inst0_signatureFrontierApplication_wk, inst0_familyApplication_wk,
      inst0_outcomeApplication_wk] using afterJudgment
  have afterWitness := Presentation.HasType.appElim afterJudgmentNormalized
    witnessTyping
  simpa only [incompleteApp, arrow, inst0_rename_wk] using afterWitness

/-! ### Formation of the intrinsic family and constructors -/

/-- The already-proved formation judgment for the first-class signature
type embeds unchanged into the declaration-extended calculus. -/
theorem outcomeSignatureType_hasIntrinsicType :
    IntrinsicHasType (.nil : Tower.Ctx 0) outcomeSignatureType
      (sortTm signatureLevel) :=
  Presentation.Declaration.HasType.includeSignature Tower.rules
    rawOutcomeSignature
    outcomeSignatureType_hasType

def outcomeContextS : Tower.Ctx 1 :=
  .snoc .nil outcomeSignatureType

def outcomeContextSJ : Tower.Ctx 2 :=
  .snoc outcomeContextS (signatureJudgment (.var 0))

def outcomeContextSJW (payloadFamily : Tower.Tm 1) : Tower.Ctx 3 :=
  .snoc outcomeContextSJ
    (.app (Presentation.rename wk payloadFamily) (.var 0))

/-- Canonical context-comprehension variables.  These explicit lemmas avoid
re-normalizing the complete nested signature record at every use site. -/
theorem outcomeSignatureVar_hasType :
    IntrinsicHasType outcomeContextS (.var 0)
      (liftClosed outcomeSignatureType) := by
  have variableTyping :=
    (Presentation.HasType.var (R := outcomeRules)
      (Γ := outcomeContextS) (0 : Fin 1))
  have lookupEquality :
      Presentation.Ctx.lookup outcomeContextS (0 : Fin 1) =
        liftClosed outcomeSignatureType := by
    decide
  simpa only [lookupEquality] using variableTyping

theorem outcomeSignatureVarInSJ_hasType :
    IntrinsicHasType outcomeContextSJ (.var 1)
      (liftClosed outcomeSignatureType) := by
  have weakened := outcomeSignatureVar_hasType.weaken
    (extension := signatureJudgment (.var 0))
  simpa [outcomeContextSJ, Presentation.rename, rename_liftClosed, wk] using
    weakened

theorem outcomeJudgmentVar_hasType :
    IntrinsicHasType outcomeContextSJ (.var 0)
      (signatureJudgment (.var 1)) := by
  have variableTyping :=
    (Presentation.HasType.var (R := outcomeRules)
      (Γ := outcomeContextSJ) (0 : Fin 2))
  have lookupEquality :
      Presentation.Ctx.lookup outcomeContextSJ (0 : Fin 2) =
        signatureJudgment (.var 1) := by
    decide
  simpa only [lookupEquality] using variableTyping

theorem outcomeSignatureVarInSJW_hasType (payloadFamily : Tower.Tm 1) :
    IntrinsicHasType (outcomeContextSJW payloadFamily) (.var 2)
      (liftClosed outcomeSignatureType) := by
  have weakened := outcomeSignatureVarInSJ_hasType.weaken
    (extension := .app (Presentation.rename wk payloadFamily) (.var 0))
  simpa [outcomeContextSJW, Presentation.rename, rename_liftClosed, wk] using
    weakened

theorem outcomeJudgmentVarInSJW_hasType (payloadFamily : Tower.Tm 1) :
    IntrinsicHasType (outcomeContextSJW payloadFamily) (.var 1)
      (signatureJudgment (.var 2)) := by
  have weakened := outcomeJudgmentVar_hasType.weaken
    (extension := .app (Presentation.rename wk payloadFamily) (.var 0))
  simpa [outcomeContextSJW, Presentation.rename, wk] using weakened

def outcomeBodyLevel : LevelExpr :=
  .max judgmentLevel (.succ outcomeLevel)

def outcomeDeclarationLevel : LevelExpr :=
  .max signatureLevel outcomeBodyLevel

/-- `Outcome` is a genuine family former: after a first-class signature and
one judgment index it yields a type at the join of the four payload levels. -/
theorem outcomeType_hasType :
    IntrinsicHasType (.nil : Tower.Ctx 0) outcomeType
      (sortTm outcomeDeclarationLevel) := by
  unfold outcomeType outcomeDeclarationLevel outcomeBodyLevel
  apply Presentation.HasType.piForm
  · exact outcomeSignatureType_hasIntrinsicType
  · exact .sort signatureLevel
  · apply Presentation.HasType.piForm
    · apply signatureJudgment_hasType
      exact outcomeSignatureVar_hasType
    · exact .sort judgmentLevel
    · exact .headType (.sort outcomeLevel)
    · exact .sort (.succ outcomeLevel)
    · exact .sorts judgmentLevel (.succ outcomeLevel)
  · exact .sort outcomeBodyLevel
  · exact .sorts signatureLevel outcomeBodyLevel

def constructorWitnessLevel (payload : LevelExpr) : LevelExpr :=
  .max payload outcomeLevel

def constructorBodyLevel (payload : LevelExpr) : LevelExpr :=
  .max judgmentLevel (constructorWitnessLevel payload)

def constructorDeclarationLevel (payload : LevelExpr) : LevelExpr :=
  .max signatureLevel (constructorBodyLevel payload)

/-- Formation is uniform in the payload family.  This theorem is the
mathematical core shared by all four authority outcomes; the named
constructors below differ only in which projection they retain. -/
theorem constructorAtSignatureType_hasType (payload : LevelExpr)
    {payloadFamily : Tower.Tm 1}
    (payloadTyping : IntrinsicHasType outcomeContextS payloadFamily
      (familyType payload (signatureJudgment (.var 0)))) :
    IntrinsicHasType outcomeContextS
      (constructorAtSignatureType (.var 0) payloadFamily)
      (sortTm (constructorBodyLevel payload)) := by
  unfold constructorAtSignatureType constructorBodyLevel
    constructorWitnessLevel
  apply Presentation.HasType.piForm
  · apply signatureJudgment_hasType
    exact outcomeSignatureVar_hasType
  · exact .sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply familyApp_hasType
      · simpa only [rename_familyType, rename_signatureJudgment] using
          payloadTyping.weaken
      · exact outcomeJudgmentVar_hasType
    · exact .sort payload
    · apply outcomeApp_hasType
      · exact outcomeSignatureVarInSJW_hasType payloadFamily
      · exact outcomeJudgmentVarInSJW_hasType payloadFamily
    · exact .sort outcomeLevel
    · exact .sorts payload outcomeLevel
  · exact .sort (constructorWitnessLevel payload)
  · exact .sorts judgmentLevel (constructorWitnessLevel payload)

theorem establishedBodyType_asConstructor :
    establishedBodyType =
      constructorAtSignatureType (.var 0) (signatureEvidence (.var 0)) := by
  decide

theorem refutedBodyType_asConstructor :
    refutedBodyType =
      constructorAtSignatureType (.var 0) (signatureObstruction (.var 0)) := by
  decide

theorem outsideFragmentBodyType_asConstructor :
    outsideFragmentBodyType =
      constructorAtSignatureType (.var 0) (signatureBoundary (.var 0)) := by
  decide

theorem incompleteBodyType_asConstructor :
    incompleteBodyType =
      constructorAtSignatureType (.var 0) (signatureFrontier (.var 0)) := by
  decide

theorem establishedBodyType_hasType :
    IntrinsicHasType outcomeContextS establishedBodyType
      (sortTm (constructorBodyLevel evidenceLevel)) := by
  rw [establishedBodyType_asConstructor]
  apply constructorAtSignatureType_hasType evidenceLevel
  apply signatureEvidence_hasType
  exact outcomeSignatureVar_hasType

theorem refutedBodyType_hasType :
    IntrinsicHasType outcomeContextS refutedBodyType
      (sortTm (constructorBodyLevel obstructionLevel)) := by
  rw [refutedBodyType_asConstructor]
  apply constructorAtSignatureType_hasType obstructionLevel
  apply signatureObstruction_hasType
  exact outcomeSignatureVar_hasType

theorem outsideFragmentBodyType_hasType :
    IntrinsicHasType outcomeContextS outsideFragmentBodyType
      (sortTm (constructorBodyLevel boundaryLevel)) := by
  rw [outsideFragmentBodyType_asConstructor]
  apply constructorAtSignatureType_hasType boundaryLevel
  apply signatureBoundary_hasType
  exact outcomeSignatureVar_hasType

theorem incompleteBodyType_hasType :
    IntrinsicHasType outcomeContextS incompleteBodyType
      (sortTm (constructorBodyLevel frontierLevel)) := by
  rw [incompleteBodyType_asConstructor]
  apply constructorAtSignatureType_hasType frontierLevel
  apply signatureFrontier_hasType
  exact outcomeSignatureVar_hasType

theorem establishedType_hasType :
    IntrinsicHasType (.nil : Tower.Ctx 0) establishedType
      (sortTm (constructorDeclarationLevel evidenceLevel)) := by
  unfold establishedType constructorDeclarationLevel
  apply Presentation.HasType.piForm
  · exact outcomeSignatureType_hasIntrinsicType
  · exact .sort signatureLevel
  · exact establishedBodyType_hasType
  · exact .sort (constructorBodyLevel evidenceLevel)
  · exact .sorts signatureLevel (constructorBodyLevel evidenceLevel)

theorem refutedType_hasType :
    IntrinsicHasType (.nil : Tower.Ctx 0) refutedType
      (sortTm (constructorDeclarationLevel obstructionLevel)) := by
  unfold refutedType constructorDeclarationLevel
  apply Presentation.HasType.piForm
  · exact outcomeSignatureType_hasIntrinsicType
  · exact .sort signatureLevel
  · exact refutedBodyType_hasType
  · exact .sort (constructorBodyLevel obstructionLevel)
  · exact .sorts signatureLevel (constructorBodyLevel obstructionLevel)

theorem outsideFragmentType_hasType :
    IntrinsicHasType (.nil : Tower.Ctx 0) outsideFragmentType
      (sortTm (constructorDeclarationLevel boundaryLevel)) := by
  unfold outsideFragmentType constructorDeclarationLevel
  apply Presentation.HasType.piForm
  · exact outcomeSignatureType_hasIntrinsicType
  · exact .sort signatureLevel
  · exact outsideFragmentBodyType_hasType
  · exact .sort (constructorBodyLevel boundaryLevel)
  · exact .sorts signatureLevel (constructorBodyLevel boundaryLevel)

theorem incompleteType_hasType :
    IntrinsicHasType (.nil : Tower.Ctx 0) incompleteType
      (sortTm (constructorDeclarationLevel frontierLevel)) := by
  unfold incompleteType constructorDeclarationLevel
  apply Presentation.HasType.piForm
  · exact outcomeSignatureType_hasIntrinsicType
  · exact .sort signatureLevel
  · exact incompleteBodyType_hasType
  · exact .sort (constructorBodyLevel frontierLevel)
  · exact .sorts signatureLevel (constructorBodyLevel frontierLevel)

/-! ### Formation of the dependent eliminator -/

/-- The motive after its first-class signature has been selected. -/
def motiveAtSignatureType (signature : Tower.Tm n) : Tower.Tm n :=
  .pi (signatureJudgment signature)
    (.pi (outcomeApp (Presentation.rename wk signature) (.var 0))
      (sortTm motiveLevel))

theorem outcomeMotiveType_asAtSignature :
    outcomeMotiveType = motiveAtSignatureType (.var 0) := by
  decide

def outcomeContextSJO : Tower.Ctx 3 :=
  .snoc outcomeContextSJ (outcomeApp (.var 1) (.var 0))

def outcomeMotiveInnerLevel : LevelExpr :=
  .max outcomeLevel (.succ motiveLevel)

def outcomeMotiveTypeLevel : LevelExpr :=
  .max judgmentLevel outcomeMotiveInnerLevel

/-- A motive may depend on both the judgment and the exact constructor of
its outcome. -/
theorem outcomeMotiveType_hasType :
    IntrinsicHasType outcomeContextS outcomeMotiveType
      (sortTm outcomeMotiveTypeLevel) := by
  rw [outcomeMotiveType_asAtSignature]
  unfold motiveAtSignatureType outcomeMotiveTypeLevel
    outcomeMotiveInnerLevel
  apply Presentation.HasType.piForm
  · apply signatureJudgment_hasType
    exact outcomeSignatureVar_hasType
  · exact .sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply outcomeApp_hasType
      · exact outcomeSignatureVarInSJ_hasType
      · exact outcomeJudgmentVar_hasType
    · exact .sort outcomeLevel
    · exact .headType (.sort motiveLevel)
    · exact .sort (.succ motiveLevel)
    · exact .sorts outcomeLevel (.succ motiveLevel)
  · exact .sort outcomeMotiveInnerLevel
  · exact .sorts judgmentLevel outcomeMotiveInnerLevel

@[simp] theorem inst0_motiveAfterJudgment
    (judgment signature : Tower.Tm n) :
    Presentation.inst0 judgment
        (.pi (outcomeApp (Presentation.rename wk signature) (.var 0))
          (sortTm motiveLevel)) =
      .pi (outcomeApp signature judgment) (sortTm motiveLevel) := by
  change Presentation.Tm.pi
      (Presentation.inst0 judgment
        (outcomeApp (Presentation.rename wk signature) (.var 0)))
      (sortTm motiveLevel) =
    Presentation.Tm.pi (outcomeApp signature judgment) (sortTm motiveLevel)
  rw [inst0_outcomeApplication_wk]

/-- Applying a motive to a judgment and an outcome yields a type in the
motive universe. -/
theorem outcomeMotiveApp_hasType {context : Tower.Ctx n}
    {signature motive judgment outcome : Tower.Tm n}
    (motiveTyping : IntrinsicHasType context motive
      (motiveAtSignatureType signature))
    (judgmentTyping : IntrinsicHasType context judgment
      (signatureJudgment signature))
    (outcomeTyping : IntrinsicHasType context outcome
      (outcomeApp signature judgment)) :
    IntrinsicHasType context (.app (.app motive judgment) outcome)
      (sortTm motiveLevel) := by
  have afterJudgment := Presentation.HasType.appElim motiveTyping
    judgmentTyping
  have afterJudgmentNormalized :
      IntrinsicHasType context (.app motive judgment)
        (.pi (outcomeApp signature judgment) (sortTm motiveLevel)) := by
    simpa only [motiveAtSignatureType, inst0_motiveAfterJudgment] using
      afterJudgment
  have afterOutcome := Presentation.HasType.appElim afterJudgmentNormalized
    outcomeTyping
  simpa [sortTm, Presentation.inst0, Presentation.subst] using afterOutcome

def outcomeContextSM : Tower.Ctx 2 :=
  .snoc outcomeContextS outcomeMotiveType

def outcomeContextSMJ : Tower.Ctx 3 :=
  .snoc outcomeContextSM (signatureJudgment (.var 1))

def outcomeContextSMJW (payloadFamily : Tower.Tm 2) : Tower.Ctx 4 :=
  .snoc outcomeContextSMJ
    (.app (Presentation.rename wk payloadFamily) (.var 0))

theorem outcomeSignatureVarInSM_hasType :
    IntrinsicHasType outcomeContextSM (.var 1)
      (liftClosed outcomeSignatureType) := by
  have weakened := outcomeSignatureVar_hasType.weaken
    (extension := outcomeMotiveType)
  simpa [outcomeContextSM, Presentation.rename, rename_liftClosed, wk] using
    weakened

theorem outcomeMotiveVar_hasType :
    IntrinsicHasType outcomeContextSM (.var 0)
      (motiveAtSignatureType (.var 1)) := by
  have variableTyping :=
    (Presentation.HasType.var (R := outcomeRules)
      (Γ := outcomeContextSM) (0 : Fin 2))
  have lookupEquality :
      Presentation.Ctx.lookup outcomeContextSM (0 : Fin 2) =
        motiveAtSignatureType (.var 1) := by
    decide
  simpa only [lookupEquality] using variableTyping

theorem outcomeSignatureVarInSMJ_hasType :
    IntrinsicHasType outcomeContextSMJ (.var 2)
      (liftClosed outcomeSignatureType) := by
  have variableTyping :=
    (Presentation.HasType.var (R := outcomeRules)
      (Γ := outcomeContextSMJ) (2 : Fin 3))
  have lookupEquality :
      Presentation.Ctx.lookup outcomeContextSMJ (2 : Fin 3) =
        liftClosed outcomeSignatureType := by
    decide
  simpa only [lookupEquality] using variableTyping

theorem outcomeMotiveVarInSMJ_hasType :
    IntrinsicHasType outcomeContextSMJ (.var 1)
      (motiveAtSignatureType (.var 2)) := by
  have variableTyping :=
    (Presentation.HasType.var (R := outcomeRules)
      (Γ := outcomeContextSMJ) (1 : Fin 3))
  have lookupEquality :
      Presentation.Ctx.lookup outcomeContextSMJ (1 : Fin 3) =
        motiveAtSignatureType (.var 2) := by
    decide
  simpa only [lookupEquality] using variableTyping

theorem outcomeJudgmentVarInSMJ_hasType :
    IntrinsicHasType outcomeContextSMJ (.var 0)
      (signatureJudgment (.var 2)) := by
  have variableTyping :=
    (Presentation.HasType.var (R := outcomeRules)
      (Γ := outcomeContextSMJ) (0 : Fin 3))
  have lookupEquality :
      Presentation.Ctx.lookup outcomeContextSMJ (0 : Fin 3) =
        signatureJudgment (.var 2) := by
    decide
  simpa only [lookupEquality] using variableTyping

theorem outcomeSignatureVarInSMJW_hasType (payloadFamily : Tower.Tm 2) :
    IntrinsicHasType (outcomeContextSMJW payloadFamily) (.var 3)
      (liftClosed outcomeSignatureType) := by
  have weakened := outcomeSignatureVarInSMJ_hasType.weaken
    (extension := .app (Presentation.rename wk payloadFamily) (.var 0))
  simpa [outcomeContextSMJW, Presentation.rename, rename_liftClosed, wk] using
    weakened

theorem weaken_outcomeMotiveAtSMJ :
    Presentation.rename wk
        (motiveAtSignatureType (.var 2 : Tower.Tm 3)) =
      motiveAtSignatureType (.var 3 : Tower.Tm 4) := by
  decide

theorem outcomeMotiveVarInSMJW_hasType (payloadFamily : Tower.Tm 2) :
    IntrinsicHasType (outcomeContextSMJW payloadFamily) (.var 2)
      (motiveAtSignatureType (.var 3)) := by
  have weakened := outcomeMotiveVarInSMJ_hasType.weaken
    (extension := .app (Presentation.rename wk payloadFamily) (.var 0))
  unfold outcomeContextSMJW
  rw [weaken_outcomeMotiveAtSMJ] at weakened
  simpa [Presentation.rename, wk] using weakened

theorem outcomeJudgmentVarInSMJW_hasType (payloadFamily : Tower.Tm 2) :
    IntrinsicHasType (outcomeContextSMJW payloadFamily) (.var 1)
      (signatureJudgment (.var 3)) := by
  have weakened := outcomeJudgmentVarInSMJ_hasType.weaken
    (extension := .app (Presentation.rename wk payloadFamily) (.var 0))
  simpa [outcomeContextSMJW, Presentation.rename, wk] using weakened

theorem outcomeWitnessVarInSMJW_hasType (payloadFamily : Tower.Tm 2) :
    IntrinsicHasType (outcomeContextSMJW payloadFamily) (.var 0)
      (.app
        (Presentation.rename wk (Presentation.rename wk payloadFamily))
        (.var 1)) := by
  have variableTyping :=
    (Presentation.HasType.var (R := outcomeRules)
      (Γ := outcomeContextSMJW payloadFamily) (0 : Fin 4))
  simpa [outcomeContextSMJW, Presentation.rename, wk] using variableTyping

def outcomeConstructorApp (constructor : DeclName)
    (signature judgment witness : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.const constructor) signature) judgment) witness

def outcomeCaseAtSignatureType (constructor : DeclName)
    (payloadFamily : Tower.Tm 2) : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (.app (Presentation.rename wk payloadFamily) (.var 0))
      (.app
        (.app (.var 2) (.var 1))
        (outcomeConstructorApp constructor (.var 3) (.var 1) (.var 0))))

def outcomeCaseWitnessLevel (payload : LevelExpr) : LevelExpr :=
  .max payload motiveLevel

def outcomeCaseLevel (payload : LevelExpr) : LevelExpr :=
  .max judgmentLevel (outcomeCaseWitnessLevel payload)

/-- Every branch has one common dependent shape.  The payload projection and
constructor typing receipt are the only branch-specific inputs. -/
theorem outcomeCaseAtSignatureType_hasType (payload : LevelExpr)
    {constructor : DeclName} {payloadFamily : Tower.Tm 2}
    (payloadTyping : IntrinsicHasType outcomeContextSM payloadFamily
      (familyType payload (signatureJudgment (.var 1))))
    (constructorTyping :
      IntrinsicHasType (outcomeContextSMJW payloadFamily)
        (outcomeConstructorApp constructor (.var 3) (.var 1) (.var 0))
        (outcomeApp (.var 3) (.var 1))) :
    IntrinsicHasType outcomeContextSM
      (outcomeCaseAtSignatureType constructor payloadFamily)
      (sortTm (outcomeCaseLevel payload)) := by
  unfold outcomeCaseAtSignatureType outcomeCaseLevel
    outcomeCaseWitnessLevel
  apply Presentation.HasType.piForm
  · apply signatureJudgment_hasType
    exact outcomeSignatureVarInSM_hasType
  · exact .sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply familyApp_hasType
      · simpa only [rename_familyType, rename_signatureJudgment] using
          payloadTyping.weaken
      · exact outcomeJudgmentVarInSMJ_hasType
    · exact .sort payload
    · apply outcomeMotiveApp_hasType
      · exact outcomeMotiveVarInSMJW_hasType payloadFamily
      · exact outcomeJudgmentVarInSMJW_hasType payloadFamily
      · exact constructorTyping
    · exact .sort motiveLevel
    · exact .sorts payload motiveLevel
  · exact .sort (outcomeCaseWitnessLevel payload)
  · exact .sorts judgmentLevel (outcomeCaseWitnessLevel payload)

theorem establishedCaseType_asGeneric :
    establishedCaseType =
      outcomeCaseAtSignatureType establishedName
        (signatureEvidence (.var 1)) := by
  decide

theorem refutedCaseType_asGeneric :
    refutedCaseType =
      outcomeCaseAtSignatureType refutedName
        (signatureObstruction (.var 1)) := by
  decide

theorem outsideFragmentCaseType_asGeneric :
    outsideFragmentCaseType =
      outcomeCaseAtSignatureType outsideFragmentName
        (signatureBoundary (.var 1)) := by
  decide

theorem incompleteCaseType_asGeneric :
    incompleteCaseType =
      outcomeCaseAtSignatureType incompleteName
        (signatureFrontier (.var 1)) := by
  decide

theorem establishedCaseType_hasType :
    IntrinsicHasType outcomeContextSM establishedCaseType
      (sortTm (outcomeCaseLevel evidenceLevel)) := by
  rw [establishedCaseType_asGeneric]
  apply outcomeCaseAtSignatureType_hasType evidenceLevel
  · apply signatureEvidence_hasType
    exact outcomeSignatureVarInSM_hasType
  · have witnessTyping :
        IntrinsicHasType
          (outcomeContextSMJW (signatureEvidence (.var 1))) (.var 0)
          (.app (signatureEvidence (.var 3)) (.var 1)) := by
      simpa [Presentation.rename, wk] using
        outcomeWitnessVarInSMJW_hasType (signatureEvidence (.var 1))
    have constructorTyping := establishedApp_hasType
      (outcomeSignatureVarInSMJW_hasType (signatureEvidence (.var 1)))
      (outcomeJudgmentVarInSMJW_hasType (signatureEvidence (.var 1)))
      witnessTyping
    simpa [outcomeConstructorApp, establishedApp] using constructorTyping

theorem refutedCaseType_hasType :
    IntrinsicHasType outcomeContextSM refutedCaseType
      (sortTm (outcomeCaseLevel obstructionLevel)) := by
  rw [refutedCaseType_asGeneric]
  apply outcomeCaseAtSignatureType_hasType obstructionLevel
  · apply signatureObstruction_hasType
    exact outcomeSignatureVarInSM_hasType
  · have witnessTyping :
        IntrinsicHasType
          (outcomeContextSMJW (signatureObstruction (.var 1))) (.var 0)
          (.app (signatureObstruction (.var 3)) (.var 1)) := by
      simpa [Presentation.rename, wk] using
        outcomeWitnessVarInSMJW_hasType (signatureObstruction (.var 1))
    have constructorTyping := refutedApp_hasType
      (outcomeSignatureVarInSMJW_hasType (signatureObstruction (.var 1)))
      (outcomeJudgmentVarInSMJW_hasType (signatureObstruction (.var 1)))
      witnessTyping
    simpa [outcomeConstructorApp, refutedApp] using constructorTyping

theorem outsideFragmentCaseType_hasType :
    IntrinsicHasType outcomeContextSM outsideFragmentCaseType
      (sortTm (outcomeCaseLevel boundaryLevel)) := by
  rw [outsideFragmentCaseType_asGeneric]
  apply outcomeCaseAtSignatureType_hasType boundaryLevel
  · apply signatureBoundary_hasType
    exact outcomeSignatureVarInSM_hasType
  · have witnessTyping :
        IntrinsicHasType
          (outcomeContextSMJW (signatureBoundary (.var 1))) (.var 0)
          (.app (signatureBoundary (.var 3)) (.var 1)) := by
      simpa [Presentation.rename, wk] using
        outcomeWitnessVarInSMJW_hasType (signatureBoundary (.var 1))
    have constructorTyping := outsideFragmentApp_hasType
      (outcomeSignatureVarInSMJW_hasType (signatureBoundary (.var 1)))
      (outcomeJudgmentVarInSMJW_hasType (signatureBoundary (.var 1)))
      witnessTyping
    simpa [outcomeConstructorApp, outsideFragmentApp] using
      constructorTyping

theorem incompleteCaseType_hasType :
    IntrinsicHasType outcomeContextSM incompleteCaseType
      (sortTm (outcomeCaseLevel frontierLevel)) := by
  rw [incompleteCaseType_asGeneric]
  apply outcomeCaseAtSignatureType_hasType frontierLevel
  · apply signatureFrontier_hasType
    exact outcomeSignatureVarInSM_hasType
  · have witnessTyping :
        IntrinsicHasType
          (outcomeContextSMJW (signatureFrontier (.var 1))) (.var 0)
          (.app (signatureFrontier (.var 3)) (.var 1)) := by
      simpa [Presentation.rename, wk] using
        outcomeWitnessVarInSMJW_hasType (signatureFrontier (.var 1))
    have constructorTyping := incompleteApp_hasType
      (outcomeSignatureVarInSMJW_hasType (signatureFrontier (.var 1)))
      (outcomeJudgmentVarInSMJW_hasType (signatureFrontier (.var 1)))
      witnessTyping
    simpa [outcomeConstructorApp, incompleteApp] using constructorTyping

def outcomeContextSMJO : Tower.Ctx 4 :=
  .snoc outcomeContextSMJ (outcomeApp (.var 2) (.var 0))

theorem outcomeSignatureVarInSMJO_hasType :
    IntrinsicHasType outcomeContextSMJO (.var 3)
      (liftClosed outcomeSignatureType) := by
  have variableTyping :=
    (Presentation.HasType.var (R := outcomeRules)
      (Γ := outcomeContextSMJO) (3 : Fin 4))
  have lookupEquality :
      Presentation.Ctx.lookup outcomeContextSMJO (3 : Fin 4) =
        liftClosed outcomeSignatureType := by
    decide
  simpa only [lookupEquality] using variableTyping

theorem outcomeMotiveVarInSMJO_hasType :
    IntrinsicHasType outcomeContextSMJO (.var 2)
      (motiveAtSignatureType (.var 3)) := by
  have variableTyping :=
    (Presentation.HasType.var (R := outcomeRules)
      (Γ := outcomeContextSMJO) (2 : Fin 4))
  have lookupEquality :
      Presentation.Ctx.lookup outcomeContextSMJO (2 : Fin 4) =
        motiveAtSignatureType (.var 3) := by
    decide
  simpa only [lookupEquality] using variableTyping

theorem outcomeJudgmentVarInSMJO_hasType :
    IntrinsicHasType outcomeContextSMJO (.var 1)
      (signatureJudgment (.var 3)) := by
  have variableTyping :=
    (Presentation.HasType.var (R := outcomeRules)
      (Γ := outcomeContextSMJO) (1 : Fin 4))
  have lookupEquality :
      Presentation.Ctx.lookup outcomeContextSMJO (1 : Fin 4) =
        signatureJudgment (.var 3) := by
    decide
  simpa only [lookupEquality] using variableTyping

theorem outcomeVarInSMJO_hasType :
    IntrinsicHasType outcomeContextSMJO (.var 0)
      (outcomeApp (.var 3) (.var 1)) := by
  have variableTyping :=
    (Presentation.HasType.var (R := outcomeRules)
      (Γ := outcomeContextSMJO) (0 : Fin 4))
  have lookupEquality :
      Presentation.Ctx.lookup outcomeContextSMJO (0 : Fin 4) =
        outcomeApp (.var 3) (.var 1) := by
    decide
  simpa only [lookupEquality] using variableTyping

def outcomeEliminateInnerLevel : LevelExpr :=
  .max outcomeLevel motiveLevel

def outcomeEliminateResultLevel : LevelExpr :=
  .max judgmentLevel outcomeEliminateInnerLevel

/-- Once all four branches are available, elimination remains dependent on
the selected judgment and on the concrete outcome inhabiting its fibre. -/
theorem outcomeEliminateResultType_hasType :
    IntrinsicHasType outcomeContextSM outcomeEliminateResultType
      (sortTm outcomeEliminateResultLevel) := by
  unfold outcomeEliminateResultType outcomeEliminateResultLevel
    outcomeEliminateInnerLevel
  apply Presentation.HasType.piForm
  · apply signatureJudgment_hasType
    exact outcomeSignatureVarInSM_hasType
  · exact .sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply outcomeApp_hasType
      · exact outcomeSignatureVarInSMJ_hasType
      · exact outcomeJudgmentVarInSMJ_hasType
    · exact .sort outcomeLevel
    · apply outcomeMotiveApp_hasType
      · exact outcomeMotiveVarInSMJO_hasType
      · exact outcomeJudgmentVarInSMJO_hasType
      · exact outcomeVarInSMJO_hasType
    · exact .sort motiveLevel
    · exact .sorts outcomeLevel motiveLevel
  · exact .sort outcomeEliminateInnerLevel
  · exact .sorts judgmentLevel outcomeEliminateInnerLevel

def outcomeContextSME : Tower.Ctx 3 :=
  .snoc outcomeContextSM establishedCaseType

def outcomeContextSMER : Tower.Ctx 4 :=
  .snoc outcomeContextSME (Presentation.rename wk refutedCaseType)

def outcomeContextSMERO : Tower.Ctx 5 :=
  .snoc outcomeContextSMER
    (Presentation.rename wk (Presentation.rename wk outsideFragmentCaseType))

def outcomeContextSMEROI : Tower.Ctx 6 :=
  .snoc outcomeContextSMERO
    (Presentation.rename wk
      (Presentation.rename wk
        (Presentation.rename wk incompleteCaseType)))

theorem refutedCaseTypeInSME_hasType :
    IntrinsicHasType outcomeContextSME
      (Presentation.rename wk refutedCaseType)
      (sortTm (outcomeCaseLevel obstructionLevel)) := by
  simpa [outcomeContextSME, sortTm, Presentation.rename] using
    refutedCaseType_hasType.weaken (extension := establishedCaseType)

theorem outsideFragmentCaseTypeInSMER_hasType :
    IntrinsicHasType outcomeContextSMER
      (Presentation.rename wk
        (Presentation.rename wk outsideFragmentCaseType))
      (sortTm (outcomeCaseLevel boundaryLevel)) := by
  have first := outsideFragmentCaseType_hasType.weaken
    (extension := establishedCaseType)
  have second := first.weaken
    (extension := Presentation.rename wk refutedCaseType)
  simpa [outcomeContextSME, outcomeContextSMER, sortTm,
    Presentation.rename] using second

theorem incompleteCaseTypeInSMERO_hasType :
    IntrinsicHasType outcomeContextSMERO
      (Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk incompleteCaseType)))
      (sortTm (outcomeCaseLevel frontierLevel)) := by
  have first := incompleteCaseType_hasType.weaken
    (extension := establishedCaseType)
  have second := first.weaken
    (extension := Presentation.rename wk refutedCaseType)
  have third := second.weaken
    (extension := Presentation.rename wk
      (Presentation.rename wk outsideFragmentCaseType))
  simpa [outcomeContextSME, outcomeContextSMER, outcomeContextSMERO,
    sortTm, Presentation.rename] using third

theorem outcomeEliminateResultTypeInSMEROI_hasType :
    IntrinsicHasType outcomeContextSMEROI
      (Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk
            (Presentation.rename wk outcomeEliminateResultType))))
      (sortTm outcomeEliminateResultLevel) := by
  have first := outcomeEliminateResultType_hasType.weaken
    (extension := establishedCaseType)
  have second := first.weaken
    (extension := Presentation.rename wk refutedCaseType)
  have third := second.weaken
    (extension := Presentation.rename wk
      (Presentation.rename wk outsideFragmentCaseType))
  have fourth := third.weaken
    (extension := Presentation.rename wk
      (Presentation.rename wk
        (Presentation.rename wk incompleteCaseType)))
  simpa [outcomeContextSME, outcomeContextSMER, outcomeContextSMERO,
    outcomeContextSMEROI, sortTm, Presentation.rename] using fourth

def outcomeAfterIncompleteLevel : LevelExpr :=
  .max (outcomeCaseLevel frontierLevel) outcomeEliminateResultLevel

def outcomeAfterOutsideLevel : LevelExpr :=
  .max (outcomeCaseLevel boundaryLevel) outcomeAfterIncompleteLevel

def outcomeAfterRefutedLevel : LevelExpr :=
  .max (outcomeCaseLevel obstructionLevel) outcomeAfterOutsideLevel

def outcomeAfterEstablishedLevel : LevelExpr :=
  .max (outcomeCaseLevel evidenceLevel) outcomeAfterRefutedLevel

def outcomeEliminateBodyLevel : LevelExpr :=
  .max outcomeMotiveTypeLevel outcomeAfterEstablishedLevel

def outcomeEliminateDeclarationLevel : LevelExpr :=
  .max signatureLevel outcomeEliminateBodyLevel

theorem outcomeEliminateBodyType_hasType :
    IntrinsicHasType outcomeContextS outcomeEliminateBodyType
      (sortTm outcomeEliminateBodyLevel) := by
  unfold outcomeEliminateBodyType outcomeEliminateBodyLevel
    outcomeAfterEstablishedLevel outcomeAfterRefutedLevel
    outcomeAfterOutsideLevel outcomeAfterIncompleteLevel
  apply Presentation.HasType.piForm
  · exact outcomeMotiveType_hasType
  · exact .sort outcomeMotiveTypeLevel
  · apply Presentation.HasType.piForm
    · exact establishedCaseType_hasType
    · exact .sort (outcomeCaseLevel evidenceLevel)
    · apply Presentation.HasType.piForm
      · exact refutedCaseTypeInSME_hasType
      · exact .sort (outcomeCaseLevel obstructionLevel)
      · apply Presentation.HasType.piForm
        · exact outsideFragmentCaseTypeInSMER_hasType
        · exact .sort (outcomeCaseLevel boundaryLevel)
        · apply Presentation.HasType.piForm
          · exact incompleteCaseTypeInSMERO_hasType
          · exact .sort (outcomeCaseLevel frontierLevel)
          · exact outcomeEliminateResultTypeInSMEROI_hasType
          · exact .sort outcomeEliminateResultLevel
          · exact .sorts (outcomeCaseLevel frontierLevel)
              outcomeEliminateResultLevel
        · exact .sort outcomeAfterIncompleteLevel
        · exact .sorts (outcomeCaseLevel boundaryLevel)
            outcomeAfterIncompleteLevel
      · exact .sort outcomeAfterOutsideLevel
      · exact .sorts (outcomeCaseLevel obstructionLevel)
          outcomeAfterOutsideLevel
    · exact .sort outcomeAfterRefutedLevel
    · exact .sorts (outcomeCaseLevel evidenceLevel)
        outcomeAfterRefutedLevel
  · exact .sort outcomeAfterEstablishedLevel
  · exact .sorts outcomeMotiveTypeLevel outcomeAfterEstablishedLevel

/-- The complete intrinsic dependent eliminator is a formed closed
declaration. -/
theorem outcomeEliminateType_hasType :
    IntrinsicHasType (.nil : Tower.Ctx 0) outcomeEliminateType
      (sortTm outcomeEliminateDeclarationLevel) := by
  unfold outcomeEliminateType outcomeEliminateDeclarationLevel
  apply Presentation.HasType.piForm
  · exact outcomeSignatureType_hasIntrinsicType
  · exact .sort signatureLevel
  · exact outcomeEliminateBodyType_hasType
  · exact .sort outcomeEliminateBodyLevel
  · exact .sorts signatureLevel outcomeEliminateBodyLevel

/-! ### Formed declaration signature -/

@[simp] theorem rawOutcomeSignature_valueOf_none (name : DeclName) :
    rawOutcomeSignature.valueOf? name = none := by
  by_cases isOutcome : name = outcomeName
  · subst name
    simp [rawOutcomeSignature, outcomeDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty]
  by_cases isEstablished : name = establishedName
  · subst name
    simp [rawOutcomeSignature, outcomeDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isOutcome]
  by_cases isRefuted : name = refutedName
  · subst name
    simp [rawOutcomeSignature, outcomeDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isOutcome,
      isEstablished]
  by_cases isOutside : name = outsideFragmentName
  · subst name
    simp [rawOutcomeSignature, outcomeDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isOutcome,
      isEstablished, isRefuted]
  by_cases isIncomplete : name = incompleteName
  · subst name
    simp [rawOutcomeSignature, outcomeDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isOutcome,
      isEstablished, isRefuted, isOutside]
  by_cases isEliminate : name = outcomeEliminateName
  · subst name
    simp [rawOutcomeSignature, outcomeDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isOutcome,
      isEstablished, isRefuted, isOutside, isIncomplete]
  · simp [rawOutcomeSignature, outcomeDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isOutcome,
      isEstablished, isRefuted, isOutside, isIncomplete, isEliminate]

theorem rawOutcomeSignature_types_formed {name : DeclName}
    {type : Tower.Tm 0}
    (lookup : rawOutcomeSignature.typeOf? name = some type) :
    ∃ level : Tower.Head,
      Tower.rules.isUniverse level ∧
      IntrinsicHasType (.nil : Tower.Ctx 0) type (.head level) := by
  by_cases isOutcome : name = outcomeName
  · subst name
    have typeEquality : type = outcomeType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort outcomeDeclarationLevel, .sort outcomeDeclarationLevel,
      outcomeType_hasType⟩
  by_cases isEstablished : name = establishedName
  · subst name
    have typeEquality : type = establishedType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort (constructorDeclarationLevel evidenceLevel),
      .sort (constructorDeclarationLevel evidenceLevel),
      establishedType_hasType⟩
  by_cases isRefuted : name = refutedName
  · subst name
    have typeEquality : type = refutedType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort (constructorDeclarationLevel obstructionLevel),
      .sort (constructorDeclarationLevel obstructionLevel),
      refutedType_hasType⟩
  by_cases isOutside : name = outsideFragmentName
  · subst name
    have typeEquality : type = outsideFragmentType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort (constructorDeclarationLevel boundaryLevel),
      .sort (constructorDeclarationLevel boundaryLevel),
      outsideFragmentType_hasType⟩
  by_cases isIncomplete : name = incompleteName
  · subst name
    have typeEquality : type = incompleteType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort (constructorDeclarationLevel frontierLevel),
      .sort (constructorDeclarationLevel frontierLevel),
      incompleteType_hasType⟩
  by_cases isEliminate : name = outcomeEliminateName
  · subst name
    have typeEquality : type = outcomeEliminateType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort outcomeEliminateDeclarationLevel,
      .sort outcomeEliminateDeclarationLevel,
      outcomeEliminateType_hasType⟩
  · simp [rawOutcomeSignature, outcomeDeclarations, Signature.typeOf?,
      Signature.ofList, Signature.insert, Signature.empty, isOutcome,
      isEstablished, isRefuted, isOutside, isIncomplete, isEliminate] at lookup

theorem rawOutcomeSignature_fresh {name : DeclName}
    {entry : Entry Tower.Head}
    (_lookup : rawOutcomeSignature.entries name = some entry) :
    Tower.rules.constantType name = none :=
  rfl

/-- Formation, freshness, and the absence of hidden delta definitions are
proved independently of any choice of raw confluence discipline. -/
def rawOutcomeSignature_formed : rawOutcomeSignature.Formed Tower.rules where
  fresh := rawOutcomeSignature_fresh
  types := rawOutcomeSignature_types_formed
  values := by
    intro name type value _typeLookup valueLookup
    rw [rawOutcomeSignature_valueOf_none] at valueLookup
    cases valueLookup
  noSelfDelta := by
    intro name value valueLookup
    rw [rawOutcomeSignature_valueOf_none] at valueLookup
    cases valueLookup

/-! ### Strict positivity -/

def outcomeFamilyApplication (signature judgment : Tower.Tm n)
    (signatureFree : FreeOf outcomeName signature)
    (judgmentFree : FreeOf outcomeName judgment) :
    FamilyApplication outcomeName 2 (outcomeApp signature judgment) :=
  .intro [signature, judgment] rfl (by
    intro argument membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl
    · exact signatureFree
    · exact judgmentFree) rfl

/-- The first-class signature record is structural: it contains no declared
family constant at all.  Consequently it is free of every prospective
family name, not merely the intrinsic `Outcome` name. -/
def outcomeSignatureTypeFreeOf (family : DeclName) :
    FreeOf family outcomeSignatureType := by
  unfold outcomeSignatureType outcomeSignatureBody familyType sortTm
  exact .sigma (.head _)
    (.sigma
      (.pi (.var 0) (.head _))
      (.sigma
        (.pi (.var 1) (.head _))
        (.sigma
          (.pi (.var 2) (.head _))
          (.pi (.var 3) (.head _)))))

/-- Specialization used by the intrinsic Outcome declaration. -/
def outcomeSignatureTypeFree : FreeOf outcomeName outcomeSignatureType :=
  outcomeSignatureTypeFreeOf outcomeName

def establishedConstructorPositive :
    ConstructorType outcomeName 2 establishedType := by
  unfold establishedType establishedBodyType arrow outcomeApp
    signatureJudgment signatureEvidence
  exact .field (.free outcomeSignatureTypeFree)
    (.field (.free (.fst (.var 0)))
      (.field
        (.free (.app (.fst (.snd (.var 1))) (.var 0)))
        (.result (outcomeFamilyApplication (.var 2) (.var 1)
          (.var 2) (.var 1)))))

def refutedConstructorPositive :
    ConstructorType outcomeName 2 refutedType := by
  unfold refutedType refutedBodyType arrow outcomeApp
    signatureJudgment signatureObstruction
  exact .field (.free outcomeSignatureTypeFree)
    (.field (.free (.fst (.var 0)))
      (.field
        (.free (.app (.fst (.snd (.snd (.var 1)))) (.var 0)))
        (.result (outcomeFamilyApplication (.var 2) (.var 1)
          (.var 2) (.var 1)))))

def outsideFragmentConstructorPositive :
    ConstructorType outcomeName 2 outsideFragmentType := by
  unfold outsideFragmentType outsideFragmentBodyType arrow outcomeApp
    signatureJudgment signatureBoundary
  exact .field (.free outcomeSignatureTypeFree)
    (.field (.free (.fst (.var 0)))
      (.field
        (.free
          (.app
            (.fst (.snd (.snd (.snd (.var 1)))))
            (.var 0)))
        (.result (outcomeFamilyApplication (.var 2) (.var 1)
          (.var 2) (.var 1)))))

def incompleteConstructorPositive :
    ConstructorType outcomeName 2 incompleteType := by
  unfold incompleteType incompleteBodyType arrow outcomeApp
    signatureJudgment signatureFrontier
  exact .field (.free outcomeSignatureTypeFree)
    (.field (.free (.fst (.var 0)))
      (.field
        (.free
          (.app
            (.snd (.snd (.snd (.snd (.var 1)))))
            (.var 0)))
        (.result (outcomeFamilyApplication (.var 2) (.var 1)
          (.var 2) (.var 1)))))

def establishedConstructorSpec :
    ConstructorSpec rawOutcomeSignature outcomeName 2 where
  name := establishedName
  type := establishedType
  declared := typeOf_established
  positive := establishedConstructorPositive

def refutedConstructorSpec :
    ConstructorSpec rawOutcomeSignature outcomeName 2 where
  name := refutedName
  type := refutedType
  declared := typeOf_refuted
  positive := refutedConstructorPositive

def outsideFragmentConstructorSpec :
    ConstructorSpec rawOutcomeSignature outcomeName 2 where
  name := outsideFragmentName
  type := outsideFragmentType
  declared := typeOf_outsideFragment
  positive := outsideFragmentConstructorPositive

def incompleteConstructorSpec :
    ConstructorSpec rawOutcomeSignature outcomeName 2 where
  name := incompleteName
  type := incompleteType
  declared := typeOf_incomplete
  positive := incompleteConstructorPositive

def outcomeConstructors :
    List (ConstructorSpec rawOutcomeSignature outcomeName 2) :=
  [establishedConstructorSpec, refutedConstructorSpec,
    outsideFragmentConstructorSpec, incompleteConstructorSpec]

def outcomeEliminatorSpec : EliminatorSpec rawOutcomeSignature where
  name := outcomeEliminateName
  type := outcomeEliminateType
  declared := typeOf_outcomeEliminate

/-- Contravariant negative control: a recursive `Outcome S j` occurrence in
a function domain is rejected even though both indices are family-free. -/
theorem outcomeInFunctionDomain_not_strictlyPositive :
    StrictlyPositive outcomeName 2
      (.pi (outcomeApp (.var 1 : Tower.Tm 2) (.var 0)) (.var 0)) → False :=
  recursivePiDomain_not_strictlyPositive
    (outcomeFamilyApplication (.var 1) (.var 0) (.var 1) (.var 0)) (.var 0)

/-! ### Canonical typed ι schemas -/

/-- The eliminator after the signature, motive, and all four branches have
been supplied in the canonical declaration telescope. -/
def outcomeEliminateAtParameters : Tower.Tm 6 :=
  .app
    (.app
      (.app
        (.app
          (.app
            (.app (.const outcomeEliminateName) (.var 5))
            (.var 4))
          (.var 3))
        (.var 2))
      (.var 1))
    (.var 0)

def outcomeEliminateAtParametersType : Tower.Tm 6 :=
  .pi (signatureJudgment (.var 5))
    (.pi (outcomeApp (.var 6) (.var 0))
      (.app (.app (.var 6) (.var 1)) (.var 0)))

theorem outcomeEliminateAtParameters_hasType :
    IntrinsicHasType outcomeContextSMEROI outcomeEliminateAtParameters
      outcomeEliminateAtParametersType := by
  have afterSignature := Presentation.HasType.appElim
    (outcomeEliminateConstant_hasType (context := outcomeContextSMEROI))
    (Presentation.HasType.var 5)
  have afterMotive := Presentation.HasType.appElim afterSignature
    (Presentation.HasType.var 4)
  have afterEstablished := Presentation.HasType.appElim afterMotive
    (Presentation.HasType.var 3)
  have afterRefuted := Presentation.HasType.appElim afterEstablished
    (Presentation.HasType.var 2)
  have afterOutside := Presentation.HasType.appElim afterRefuted
    (Presentation.HasType.var 1)
  have afterIncomplete := Presentation.HasType.appElim afterOutside
    (Presentation.HasType.var 0)
  convert afterIncomplete using 1
  all_goals decide

def outcomeContextSMEROIJ : Tower.Ctx 7 :=
  .snoc outcomeContextSMEROI (signatureJudgment (.var 5))

def establishedIotaContext : Tower.Ctx 8 :=
  .snoc outcomeContextSMEROIJ
    (.app (signatureEvidence (.var 6)) (.var 0))

def refutedIotaContext : Tower.Ctx 8 :=
  .snoc outcomeContextSMEROIJ
    (.app (signatureObstruction (.var 6)) (.var 0))

def outsideFragmentIotaContext : Tower.Ctx 8 :=
  .snoc outcomeContextSMEROIJ
    (.app (signatureBoundary (.var 6)) (.var 0))

def incompleteIotaContext : Tower.Ctx 8 :=
  .snoc outcomeContextSMEROIJ
    (.app (signatureFrontier (.var 6)) (.var 0))

def establishedIotaOutcome : Tower.Tm 8 :=
  establishedApp (.var 7) (.var 1) (.var 0)

def refutedIotaOutcome : Tower.Tm 8 :=
  refutedApp (.var 7) (.var 1) (.var 0)

def outsideFragmentIotaOutcome : Tower.Tm 8 :=
  outsideFragmentApp (.var 7) (.var 1) (.var 0)

def incompleteIotaOutcome : Tower.Tm 8 :=
  incompleteApp (.var 7) (.var 1) (.var 0)

def establishedIotaLeft : Tower.Tm 8 :=
  .app
    (.app (Presentation.rename wk (Presentation.rename wk
      outcomeEliminateAtParameters)) (.var 1))
    establishedIotaOutcome

def establishedIotaRight : Tower.Tm 8 :=
  .app (.app (.var 5) (.var 1)) (.var 0)

def establishedIotaType : Tower.Tm 8 :=
  .app (.app (.var 6) (.var 1)) establishedIotaOutcome

def refutedIotaLeft : Tower.Tm 8 :=
  .app
    (.app (Presentation.rename wk (Presentation.rename wk
      outcomeEliminateAtParameters)) (.var 1))
    refutedIotaOutcome

def refutedIotaRight : Tower.Tm 8 :=
  .app (.app (.var 4) (.var 1)) (.var 0)

def refutedIotaType : Tower.Tm 8 :=
  .app (.app (.var 6) (.var 1)) refutedIotaOutcome

def outsideFragmentIotaLeft : Tower.Tm 8 :=
  .app
    (.app (Presentation.rename wk (Presentation.rename wk
      outcomeEliminateAtParameters)) (.var 1))
    outsideFragmentIotaOutcome

def outsideFragmentIotaRight : Tower.Tm 8 :=
  .app (.app (.var 3) (.var 1)) (.var 0)

def outsideFragmentIotaType : Tower.Tm 8 :=
  .app (.app (.var 6) (.var 1)) outsideFragmentIotaOutcome

def incompleteIotaLeft : Tower.Tm 8 :=
  .app
    (.app (Presentation.rename wk (Presentation.rename wk
      outcomeEliminateAtParameters)) (.var 1))
    incompleteIotaOutcome

def incompleteIotaRight : Tower.Tm 8 :=
  .app (.app (.var 2) (.var 1)) (.var 0)

def incompleteIotaType : Tower.Tm 8 :=
  .app (.app (.var 6) (.var 1)) incompleteIotaOutcome

abbrev OutcomeTypedIotaReceipt (context : Tower.Ctx n)
    (left right type : Tower.Tm n) : Type :=
  ProofRelevantStepReceipt Tower.rules rawOutcomeSignature
    proofRelevantOutcomeComputation context left right type

theorem establishedIotaLeft_asEliminate :
    establishedIotaLeft =
      outcomeEliminateApp (.var 7) (.var 6) (.var 5) (.var 4)
        (.var 3) (.var 2) (.var 1)
        (establishedApp (.var 7) (.var 1) (.var 0)) := by
  decide

theorem establishedIotaRight_asBranch :
    establishedIotaRight = .app (.app (.var 5) (.var 1)) (.var 0) :=
  rfl

def establishedIotaReceipt :
    OutcomeTypedIotaReceipt establishedIotaContext
      establishedIotaLeft establishedIotaRight establishedIotaType where
  sourceTyping := by
    unfold establishedIotaContext outcomeContextSMEROIJ
    have judgmentTyping :
        IntrinsicHasType establishedIotaContext (.var 1)
          (signatureJudgment (.var 7)) := by
      exact Presentation.HasType.var 1
    have witnessTyping :
        IntrinsicHasType establishedIotaContext (.var 0)
          (.app (signatureEvidence (.var 7)) (.var 1)) := by
      exact Presentation.HasType.var 0
    have outcomeTyping := establishedApp_hasType
      (context := establishedIotaContext)
      (signature := (.var 7)) (judgment := (.var 1))
      (witness := (.var 0)) (Presentation.HasType.var 7)
      judgmentTyping witnessTyping
    have afterJudgmentBinder := outcomeEliminateAtParameters_hasType.weaken
      (extension := signatureJudgment (.var 5))
    have weakened := afterJudgmentBinder.weaken
      (extension := .app (signatureEvidence (.var 6)) (.var 0))
    have afterJudgment := Presentation.HasType.appElim weakened judgmentTyping
    have source := Presentation.HasType.appElim afterJudgment outcomeTyping
    convert source using 1
    all_goals decide
  targetTyping := by
    unfold establishedIotaContext outcomeContextSMEROIJ
    have judgmentTyping :
        IntrinsicHasType establishedIotaContext (.var 1)
          (signatureJudgment (.var 7)) := by
      exact Presentation.HasType.var 1
    have witnessTyping :
        IntrinsicHasType establishedIotaContext (.var 0)
          (.app (signatureEvidence (.var 7)) (.var 1)) := by
      exact Presentation.HasType.var 0
    have afterJudgment := Presentation.HasType.appElim
      (Presentation.HasType.var (R := outcomeRules)
        (Γ := establishedIotaContext) (5 : Fin 8)) judgmentTyping
    have target := Presentation.HasType.appElim afterJudgment witnessTyping
    unfold establishedIotaContext outcomeContextSMEROIJ at target
    convert target using 1
    all_goals decide
  evidence := by
    change OutcomeIotaEvidence 8 establishedIotaLeft establishedIotaRight
    rw [establishedIotaLeft_asEliminate, establishedIotaRight_asBranch]
    exact OutcomeIotaEvidence.established
      (.var 7) (.var 6) (.var 5) (.var 4) (.var 3) (.var 2)
      (.var 1) (.var 0)

theorem refutedIotaLeft_asEliminate :
    refutedIotaLeft =
      outcomeEliminateApp (.var 7) (.var 6) (.var 5) (.var 4)
        (.var 3) (.var 2) (.var 1)
        (refutedApp (.var 7) (.var 1) (.var 0)) := by
  decide

theorem refutedIotaRight_asBranch :
    refutedIotaRight = .app (.app (.var 4) (.var 1)) (.var 0) :=
  rfl

def refutedIotaReceipt :
    OutcomeTypedIotaReceipt refutedIotaContext
      refutedIotaLeft refutedIotaRight refutedIotaType where
  sourceTyping := by
    unfold refutedIotaContext outcomeContextSMEROIJ
    have judgmentTyping :
        IntrinsicHasType refutedIotaContext (.var 1)
          (signatureJudgment (.var 7)) := by
      exact Presentation.HasType.var 1
    have witnessTyping :
        IntrinsicHasType refutedIotaContext (.var 0)
          (.app (signatureObstruction (.var 7)) (.var 1)) := by
      exact Presentation.HasType.var 0
    have outcomeTyping := refutedApp_hasType
      (context := refutedIotaContext)
      (signature := (.var 7)) (judgment := (.var 1))
      (witness := (.var 0)) (Presentation.HasType.var 7)
      judgmentTyping witnessTyping
    have afterJudgmentBinder := outcomeEliminateAtParameters_hasType.weaken
      (extension := signatureJudgment (.var 5))
    have weakened := afterJudgmentBinder.weaken
      (extension := .app (signatureObstruction (.var 6)) (.var 0))
    have afterJudgment := Presentation.HasType.appElim weakened judgmentTyping
    have source := Presentation.HasType.appElim afterJudgment outcomeTyping
    convert source using 1
    all_goals decide
  targetTyping := by
    unfold refutedIotaContext outcomeContextSMEROIJ
    have judgmentTyping :
        IntrinsicHasType refutedIotaContext (.var 1)
          (signatureJudgment (.var 7)) := by
      exact Presentation.HasType.var 1
    have witnessTyping :
        IntrinsicHasType refutedIotaContext (.var 0)
          (.app (signatureObstruction (.var 7)) (.var 1)) := by
      exact Presentation.HasType.var 0
    have afterJudgment := Presentation.HasType.appElim
      (Presentation.HasType.var (R := outcomeRules)
        (Γ := refutedIotaContext) (4 : Fin 8)) judgmentTyping
    have target := Presentation.HasType.appElim afterJudgment witnessTyping
    unfold refutedIotaContext outcomeContextSMEROIJ at target
    convert target using 1
    all_goals decide
  evidence := by
    change OutcomeIotaEvidence 8 refutedIotaLeft refutedIotaRight
    rw [refutedIotaLeft_asEliminate, refutedIotaRight_asBranch]
    exact OutcomeIotaEvidence.refuted
      (.var 7) (.var 6) (.var 5) (.var 4) (.var 3) (.var 2)
      (.var 1) (.var 0)

theorem outsideFragmentIotaLeft_asEliminate :
    outsideFragmentIotaLeft =
      outcomeEliminateApp (.var 7) (.var 6) (.var 5) (.var 4)
        (.var 3) (.var 2) (.var 1)
        (outsideFragmentApp (.var 7) (.var 1) (.var 0)) := by
  decide

theorem outsideFragmentIotaRight_asBranch :
    outsideFragmentIotaRight =
      .app (.app (.var 3) (.var 1)) (.var 0) :=
  rfl

def outsideFragmentIotaReceipt :
    OutcomeTypedIotaReceipt outsideFragmentIotaContext
      outsideFragmentIotaLeft outsideFragmentIotaRight
      outsideFragmentIotaType where
  sourceTyping := by
    unfold outsideFragmentIotaContext outcomeContextSMEROIJ
    have judgmentTyping :
        IntrinsicHasType outsideFragmentIotaContext (.var 1)
          (signatureJudgment (.var 7)) := by
      exact Presentation.HasType.var 1
    have witnessTyping :
        IntrinsicHasType outsideFragmentIotaContext (.var 0)
          (.app (signatureBoundary (.var 7)) (.var 1)) := by
      exact Presentation.HasType.var 0
    have outcomeTyping := outsideFragmentApp_hasType
      (context := outsideFragmentIotaContext)
      (signature := (.var 7)) (judgment := (.var 1))
      (witness := (.var 0)) (Presentation.HasType.var 7)
      judgmentTyping witnessTyping
    have afterJudgmentBinder := outcomeEliminateAtParameters_hasType.weaken
      (extension := signatureJudgment (.var 5))
    have weakened := afterJudgmentBinder.weaken
      (extension := .app (signatureBoundary (.var 6)) (.var 0))
    have afterJudgment := Presentation.HasType.appElim weakened judgmentTyping
    have source := Presentation.HasType.appElim afterJudgment outcomeTyping
    convert source using 1
    all_goals decide
  targetTyping := by
    unfold outsideFragmentIotaContext outcomeContextSMEROIJ
    have judgmentTyping :
        IntrinsicHasType outsideFragmentIotaContext (.var 1)
          (signatureJudgment (.var 7)) := by
      exact Presentation.HasType.var 1
    have witnessTyping :
        IntrinsicHasType outsideFragmentIotaContext (.var 0)
          (.app (signatureBoundary (.var 7)) (.var 1)) := by
      exact Presentation.HasType.var 0
    have afterJudgment := Presentation.HasType.appElim
      (Presentation.HasType.var (R := outcomeRules)
        (Γ := outsideFragmentIotaContext) (3 : Fin 8)) judgmentTyping
    have target := Presentation.HasType.appElim afterJudgment witnessTyping
    unfold outsideFragmentIotaContext outcomeContextSMEROIJ at target
    convert target using 1
    all_goals decide
  evidence := by
    change OutcomeIotaEvidence 8 outsideFragmentIotaLeft
      outsideFragmentIotaRight
    rw [outsideFragmentIotaLeft_asEliminate,
      outsideFragmentIotaRight_asBranch]
    exact OutcomeIotaEvidence.outsideFragment
      (.var 7) (.var 6) (.var 5) (.var 4) (.var 3) (.var 2)
      (.var 1) (.var 0)

theorem incompleteIotaLeft_asEliminate :
    incompleteIotaLeft =
      outcomeEliminateApp (.var 7) (.var 6) (.var 5) (.var 4)
        (.var 3) (.var 2) (.var 1)
        (incompleteApp (.var 7) (.var 1) (.var 0)) := by
  decide

theorem incompleteIotaRight_asBranch :
    incompleteIotaRight = .app (.app (.var 2) (.var 1)) (.var 0) :=
  rfl

def incompleteIotaReceipt :
    OutcomeTypedIotaReceipt incompleteIotaContext
      incompleteIotaLeft incompleteIotaRight incompleteIotaType where
  sourceTyping := by
    unfold incompleteIotaContext outcomeContextSMEROIJ
    have judgmentTyping :
        IntrinsicHasType incompleteIotaContext (.var 1)
          (signatureJudgment (.var 7)) := by
      exact Presentation.HasType.var 1
    have witnessTyping :
        IntrinsicHasType incompleteIotaContext (.var 0)
          (.app (signatureFrontier (.var 7)) (.var 1)) := by
      exact Presentation.HasType.var 0
    have outcomeTyping := incompleteApp_hasType
      (context := incompleteIotaContext)
      (signature := (.var 7)) (judgment := (.var 1))
      (witness := (.var 0)) (Presentation.HasType.var 7)
      judgmentTyping witnessTyping
    have afterJudgmentBinder := outcomeEliminateAtParameters_hasType.weaken
      (extension := signatureJudgment (.var 5))
    have weakened := afterJudgmentBinder.weaken
      (extension := .app (signatureFrontier (.var 6)) (.var 0))
    have afterJudgment := Presentation.HasType.appElim weakened judgmentTyping
    have source := Presentation.HasType.appElim afterJudgment outcomeTyping
    convert source using 1
    all_goals decide
  targetTyping := by
    unfold incompleteIotaContext outcomeContextSMEROIJ
    have judgmentTyping :
        IntrinsicHasType incompleteIotaContext (.var 1)
          (signatureJudgment (.var 7)) := by
      exact Presentation.HasType.var 1
    have witnessTyping :
        IntrinsicHasType incompleteIotaContext (.var 0)
          (.app (signatureFrontier (.var 7)) (.var 1)) := by
      exact Presentation.HasType.var 0
    have afterJudgment := Presentation.HasType.appElim
      (Presentation.HasType.var (R := outcomeRules)
        (Γ := incompleteIotaContext) (2 : Fin 8)) judgmentTyping
    have target := Presentation.HasType.appElim afterJudgment witnessTyping
    unfold incompleteIotaContext outcomeContextSMEROIJ at target
    convert target using 1
    all_goals decide
  evidence := by
    change OutcomeIotaEvidence 8 incompleteIotaLeft incompleteIotaRight
    rw [incompleteIotaLeft_asEliminate, incompleteIotaRight_asBranch]
    exact OutcomeIotaEvidence.incomplete
      (.var 7) (.var 6) (.var 5) (.var 4) (.var 3) (.var 2)
      (.var 1) (.var 0)

def establishedIotaSchema :
    IotaSchema Tower.rules rawOutcomeSignature
      proofRelevantOutcomeComputation 8 where
  context := establishedIotaContext
  left := establishedIotaLeft
  right := establishedIotaRight
  type := establishedIotaType
  receipt := establishedIotaReceipt

def refutedIotaSchema :
    IotaSchema Tower.rules rawOutcomeSignature
      proofRelevantOutcomeComputation 8 where
  context := refutedIotaContext
  left := refutedIotaLeft
  right := refutedIotaRight
  type := refutedIotaType
  receipt := refutedIotaReceipt

def outsideFragmentIotaSchema :
    IotaSchema Tower.rules rawOutcomeSignature
      proofRelevantOutcomeComputation 8 where
  context := outsideFragmentIotaContext
  left := outsideFragmentIotaLeft
  right := outsideFragmentIotaRight
  type := outsideFragmentIotaType
  receipt := outsideFragmentIotaReceipt

def incompleteIotaSchema :
    IotaSchema Tower.rules rawOutcomeSignature
      proofRelevantOutcomeComputation 8 where
  context := incompleteIotaContext
  left := incompleteIotaLeft
  right := incompleteIotaRight
  type := incompleteIotaType
  receipt := incompleteIotaReceipt

def outcomeEliminateAtParameters_applicationHead :
    ApplicationHead outcomeEliminateName outcomeEliminateAtParameters :=
  .app (.app (.app (.app (.app (.app .const)))))

noncomputable def outcomeEliminateAtIota_applicationHead :
    ApplicationHead outcomeEliminateName
      (Presentation.rename wk
        (Presentation.rename wk outcomeEliminateAtParameters)) :=
  (outcomeEliminateAtParameters_applicationHead.rename wk).rename wk

def establishedApp_constantOccurrence
    (signature judgment witness : Tower.Tm n) :
    ConstantOccurrence establishedName
      (establishedApp signature judgment witness) :=
  .appFunction (.appFunction (.appFunction .here))

def refutedApp_constantOccurrence
    (signature judgment witness : Tower.Tm n) :
    ConstantOccurrence refutedName
      (refutedApp signature judgment witness) :=
  .appFunction (.appFunction (.appFunction .here))

def outsideFragmentApp_constantOccurrence
    (signature judgment witness : Tower.Tm n) :
    ConstantOccurrence outsideFragmentName
      (outsideFragmentApp signature judgment witness) :=
  .appFunction (.appFunction (.appFunction .here))

def incompleteApp_constantOccurrence
    (signature judgment witness : Tower.Tm n) :
    ConstantOccurrence incompleteName
      (incompleteApp signature judgment witness) :=
  .appFunction (.appFunction (.appFunction .here))

noncomputable def establishedIotaClause :
    IotaClause Tower.rules rawOutcomeSignature
      proofRelevantOutcomeComputation
      (outcomeConstructors.map ConstructorSpec.name)
      outcomeEliminatorSpec.name where
  constructorName := establishedName
  constructorDeclared := by
    simp [outcomeConstructors, establishedConstructorSpec]
  arity := 8
  schema := establishedIotaSchema
  eliminatorHead := .app (.app outcomeEliminateAtIota_applicationHead)
  constructorOccurrence :=
    .appArgument
      (establishedApp_constantOccurrence (.var 7) (.var 1) (.var 0))

noncomputable def refutedIotaClause :
    IotaClause Tower.rules rawOutcomeSignature
      proofRelevantOutcomeComputation
      (outcomeConstructors.map ConstructorSpec.name)
      outcomeEliminatorSpec.name where
  constructorName := refutedName
  constructorDeclared := by
    simp [outcomeConstructors, establishedConstructorSpec,
      refutedConstructorSpec]
  arity := 8
  schema := refutedIotaSchema
  eliminatorHead := .app (.app outcomeEliminateAtIota_applicationHead)
  constructorOccurrence :=
    .appArgument
      (refutedApp_constantOccurrence (.var 7) (.var 1) (.var 0))

noncomputable def outsideFragmentIotaClause :
    IotaClause Tower.rules rawOutcomeSignature
      proofRelevantOutcomeComputation
      (outcomeConstructors.map ConstructorSpec.name)
      outcomeEliminatorSpec.name where
  constructorName := outsideFragmentName
  constructorDeclared := by
    simp [outcomeConstructors, establishedConstructorSpec,
      refutedConstructorSpec, outsideFragmentConstructorSpec]
  arity := 8
  schema := outsideFragmentIotaSchema
  eliminatorHead := .app (.app outcomeEliminateAtIota_applicationHead)
  constructorOccurrence :=
    .appArgument
      (outsideFragmentApp_constantOccurrence (.var 7) (.var 1) (.var 0))

noncomputable def incompleteIotaClause :
    IotaClause Tower.rules rawOutcomeSignature
      proofRelevantOutcomeComputation
      (outcomeConstructors.map ConstructorSpec.name)
      outcomeEliminatorSpec.name where
  constructorName := incompleteName
  constructorDeclared := by
    simp [outcomeConstructors, establishedConstructorSpec,
      refutedConstructorSpec, outsideFragmentConstructorSpec,
      incompleteConstructorSpec]
  arity := 8
  schema := incompleteIotaSchema
  eliminatorHead := .app (.app outcomeEliminateAtIota_applicationHead)
  constructorOccurrence :=
    .appArgument
      (incompleteApp_constantOccurrence (.var 7) (.var 1) (.var 0))

noncomputable def outcomeIotaClauses :
    List (IotaClause Tower.rules rawOutcomeSignature
      proofRelevantOutcomeComputation
      (outcomeConstructors.map ConstructorSpec.name)
      outcomeEliminatorSpec.name) :=
  [establishedIotaClause, refutedIotaClause,
    outsideFragmentIotaClause, incompleteIotaClause]

/-- A fully formed, strictly-positive intrinsic `Outcome` declaration with
four exact typed computation generators.  Raw preservation is deliberately
not asserted here: that later authority boundary depends on the selected
confluence discipline. -/
noncomputable def outcomeCandidate : Candidate Tower.rules where
  signature := rawOutcomeSignature
  formed := rawOutcomeSignature_formed
  computation := proofRelevantOutcomeComputation
  computationSupport := rfl
  familyName := outcomeName
  familyParameterCount := 1
  familyIndexCount := 1
  familyType := outcomeType
  familyDeclared := typeOf_outcome
  constructors := outcomeConstructors
  constructorNamesNodup := by
    change [establishedName, refutedName, outsideFragmentName,
      incompleteName].Nodup
    decide
  familyNotConstructor := by
    intro constructor membership
    simp only [outcomeConstructors, List.mem_cons, List.not_mem_nil,
      or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl <;> decide
  eliminator := outcomeEliminatorSpec
  eliminatorNotFamily := by decide
  eliminatorNotConstructor := by
    intro constructor membership
    simp only [outcomeConstructors, List.mem_cons, List.not_mem_nil,
      or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl <;> decide
  iotaClauses := outcomeIotaClauses
  constructorsComputed := by
    intro constructorName membership
    simp [outcomeConstructors, establishedConstructorSpec,
      refutedConstructorSpec, outsideFragmentConstructorSpec,
      incompleteConstructorSpec] at membership
    rcases membership with rfl | rfl | rfl | rfl <;>
      simp [outcomeIotaClauses, establishedIotaClause,
        refutedIotaClause, outsideFragmentIotaClause,
        incompleteIotaClause]


end Intrinsic

/-! ## Prime's exact authority as proof-relevant data -/

/-- The external proposition-valued exact authority, lifted without Boolean
erasure into a type-valued family. -/
def exactDataAuthority : DataAuthority ExactJudgment :=
  DataAuthority.ofProp exactAuthority

def exactOutcomeSignature : OutcomeFamily.Signature ExactJudgment :=
  OutcomeFamily.Signature.ofAuthority exactDataAuthority
    (fun _ => BoundaryReason) (fun _ => ResourceReceipt)

/-- The running Prime hypothesis for first-class authority outcomes.  It is
the fixed family of the generic strictly-positive four-constructor
polynomial, indexed by the exact judgment being observed. -/
abbrev InternalOutcome (judgment : ExactJudgment) : Type :=
  OutcomeFamily.Code exactOutcomeSignature judgment

abbrev DataOutcome (judgment : ExactJudgment) : Type 1 :=
  Outcome.{1, 1, 0, 0} (exactDataAuthority.Evidence judgment)
    (exactDataAuthority.Obstruction judgment) BoundaryReason ResourceReceipt

/-- Remove only the `PLift`/`ULift` used to make proposition-valued external
evidence available as ordinary data. -/
def liftedOutcomeEquivExact (judgment : ExactJudgment) :
    DataOutcome judgment ≃ ExactOutcome judgment where
  toFun
    | .established evidence => .established evidence.down.down
    | .refuted obstruction => .refuted obstruction.down.down
    | .outsideFragment reason => .outsideFragment reason
    | .incomplete frontier => .incomplete frontier
  invFun
    | .established evidence => .established ⟨⟨evidence⟩⟩
    | .refuted obstruction => .refuted ⟨⟨obstruction⟩⟩
    | .outsideFragment reason => .outsideFragment reason
    | .incomplete frontier => .incomplete frontier
  left_inv := by
    intro outcome
    cases outcome <;> rfl
  right_inv := by
    intro outcome
    cases outcome <;> rfl

/-- The existing Lean outcome contract interprets the internal polynomial
family exactly; neither constructor nor payload is lost. -/
def internalOutcomeModel (judgment : ExactJudgment) :
    InternalOutcome judgment ≃ ExactOutcome judgment :=
  (OutcomeFamily.representationEquiv exactOutcomeSignature judgment).trans
    (liftedOutcomeEquivExact judgment)

@[simp] theorem internalOutcomeModel_established
    {judgment : ExactJudgment}
    (evidence : exactDataAuthority.Evidence judgment) :
    internalOutcomeModel judgment (OutcomeFamily.established evidence) =
      .established evidence.down.down :=
  rfl

@[simp] theorem internalOutcomeModel_refuted
    {judgment : ExactJudgment}
    (obstruction : exactDataAuthority.Obstruction judgment) :
    internalOutcomeModel judgment (OutcomeFamily.refuted obstruction) =
      .refuted obstruction.down.down :=
  rfl

theorem internal_established_ne_refuted
    {judgment : ExactJudgment}
    (evidence : exactDataAuthority.Evidence judgment)
    (obstruction : exactDataAuthority.Obstruction judgment) :
    OutcomeFamily.established evidence ≠
      (OutcomeFamily.refuted obstruction : InternalOutcome judgment) := by
  intro equality
  have interpreted := congrArg (internalOutcomeModel judgment) equality
  cases interpreted

/-! ## Operational failure remains an outer indexed family -/

def exactRunSignature : RunFamily.Signature ExactJudgment where
  Failure := fun _ => FaultReason
  Result := InternalOutcome

abbrev InternalRun (judgment : ExactJudgment) : Type :=
  RunFamily.Code exactRunSignature judgment

/-- The semantic run model first interprets the polynomial outer sum, then
changes only its successful payload through `internalOutcomeModel`. -/
def internalRunModel (judgment : ExactJudgment) :
    InternalRun judgment ≃ ExactRun judgment :=
  (RunFamily.representationEquiv exactRunSignature judgment).trans
    (RunResult.mapResultEquiv (internalOutcomeModel judgment))

theorem internal_ok_ne_fault {judgment : ExactJudgment}
    (outcome : InternalOutcome judgment) (failure : FaultReason) :
    RunFamily.ok outcome ≠ (RunFamily.fault failure : InternalRun judgment) := by
  intro equality
  have interpreted := congrArg (internalRunModel judgment) equality
  cases interpreted

/-! ## Receipts as dependent records over internal runs -/

/-- A receipt inside the running Prime model.  Authority identity remains an
index, so a receipt cannot be replayed under a different key without an
explicit equality witness. -/
structure InternalReceipt (Budget Provenance : Type) (key : AuthorityKey)
    (requested : Budget) (judgment : ExactJudgment) where
  spent : Nat
  provenance : Provenance
  result : InternalRun judgment

/-- The generic external receipt is an exact model of the internal dependent
record once its run field is interpreted. -/
def internalReceiptModel (Budget Provenance : Type) (key : AuthorityKey)
    (requested : Budget)
    (judgment : ExactJudgment) :
    InternalReceipt Budget Provenance key requested judgment ≃
      Presentation.OutcomeContract.Receipt exactAuthority BoundaryReason
        ResourceReceipt FaultReason Budget Provenance key requested judgment where
  toFun receipt :=
    { spent := receipt.spent
      provenance := receipt.provenance
      result := internalRunModel judgment receipt.result }
  invFun receipt :=
    { spent := receipt.spent
      provenance := receipt.provenance
      result := (internalRunModel judgment).symm receipt.result }
  left_inv := by
    intro receipt
    cases receipt
    simp
  right_inv := by
    intro receipt
    cases receipt
    simp

/-! ## First-class refinement evidence -/

/-- Budget refinement inside Prime retains its constructor witness as a type,
while the old proposition is recovered as support through
`nonempty_budgetRefinementEvidence_iff`. -/
abbrev InternalBudgetRefinement {judgment : ExactJudgment}
    (before after : InternalOutcome judgment) : Type :=
  Outcome.BudgetRefinementEvidence
    (OutcomeFamily.interpret before) (OutcomeFamily.interpret after)

/-- Authority refinement is independently proof-relevant; it cannot be
confused with adding fuel to one fixed authority. -/
abbrev InternalAuthorityRefinement {judgment : ExactJudgment}
    (before after : InternalOutcome judgment) : Type :=
  Outcome.AuthorityRefinementEvidence
    (OutcomeFamily.interpret before) (OutcomeFamily.interpret after)

/-- The unified proof-relevant refinement family interpreted over Prime's
internal outcome polynomial.  Budget and authority are fibres, not unrelated
foundations. -/
abbrev InternalAxisRefinement (axis : Outcome.RefinementAxis)
    {judgment : ExactJudgment}
    (before after : InternalOutcome judgment) : Type :=
  Outcome.AxisRefinementEvidence axis
    (OutcomeFamily.interpret before) (OutcomeFamily.interpret after)

/-- The previously exposed budget witness is exactly the budget fibre of the
unified internal relation. -/
def internalBudgetAxisEquiv {judgment : ExactJudgment}
    {before after : InternalOutcome judgment} :
    InternalAxisRefinement .budget before after ≃
      InternalBudgetRefinement before after :=
  Outcome.AxisRefinementEvidence.budgetEquiv

/-- The previously exposed authority witness is exactly the authority fibre
of the unified internal relation. -/
def internalAuthorityAxisEquiv {judgment : ExactJudgment}
    {before after : InternalOutcome judgment} :
    InternalAxisRefinement .authority before after ≃
      InternalAuthorityRefinement before after :=
  Outcome.AxisRefinementEvidence.authorityEquiv

/-- Mixed refinement histories retain their intermediate internal outcomes
and the axis of every step. -/
abbrev InternalRefinementPath {judgment : ExactJudgment}
    (before after : InternalOutcome judgment) : Type 1 :=
  Outcome.RefinementPath
    (OutcomeFamily.interpret before) (OutcomeFamily.interpret after)

theorem liftedBudgetRefines_iff (judgment : ExactJudgment)
    (before after : DataOutcome judgment) :
    Outcome.BudgetRefines before after ↔
      Outcome.BudgetRefines (liftedOutcomeEquivExact judgment before)
        (liftedOutcomeEquivExact judgment after) := by
  constructor
  · intro refinement
    cases refinement <;> constructor
  · intro refinement
    cases before <;> cases after <;> cases refinement <;> constructor

theorem liftedAuthorityRefines_iff (judgment : ExactJudgment)
    (before after : DataOutcome judgment) :
    Outcome.AuthorityRefines before after ↔
      Outcome.AuthorityRefines (liftedOutcomeEquivExact judgment before)
        (liftedOutcomeEquivExact judgment after) := by
  constructor
  · intro refinement
    cases refinement <;> constructor
  · intro refinement
    cases before <;> cases after <;> cases refinement <;> constructor

theorem liftedAxisRefines_iff (axis : Outcome.RefinementAxis)
    (judgment : ExactJudgment) (before after : DataOutcome judgment) :
    Outcome.AxisRefines axis before after ↔
      Outcome.AxisRefines axis
        (liftedOutcomeEquivExact judgment before)
        (liftedOutcomeEquivExact judgment after) := by
  cases axis with
  | budget => exact liftedBudgetRefines_iff judgment before after
  | authority => exact liftedAuthorityRefines_iff judgment before after

theorem internalBudgetRefinement_support_iff
    {judgment : ExactJudgment} {before after : InternalOutcome judgment} :
    Nonempty (InternalBudgetRefinement before after) ↔
      Outcome.BudgetRefines (internalOutcomeModel judgment before)
        (internalOutcomeModel judgment after) := by
  rw [Outcome.nonempty_budgetRefinementEvidence_iff]
  exact liftedBudgetRefines_iff judgment
    (OutcomeFamily.interpret before) (OutcomeFamily.interpret after)

theorem internalAuthorityRefinement_support_iff
    {judgment : ExactJudgment} {before after : InternalOutcome judgment} :
    Nonempty (InternalAuthorityRefinement before after) ↔
      Outcome.AuthorityRefines (internalOutcomeModel judgment before)
        (internalOutcomeModel judgment after) := by
  rw [Outcome.nonempty_authorityRefinementEvidence_iff]
  exact liftedAuthorityRefines_iff judgment
    (OutcomeFamily.interpret before) (OutcomeFamily.interpret after)

/-- External support for either refinement policy is recovered uniformly
from nonemptiness of the corresponding internal fibre. -/
theorem internalAxisRefinement_support_iff
    {axis : Outcome.RefinementAxis}
    {judgment : ExactJudgment} {before after : InternalOutcome judgment} :
    Nonempty (InternalAxisRefinement axis before after) ↔
      Outcome.AxisRefines axis
        (internalOutcomeModel judgment before)
        (internalOutcomeModel judgment after) := by
  rw [Outcome.nonempty_axisRefinementEvidence_iff]
  exact liftedAxisRefines_iff axis judgment
    (OutcomeFamily.interpret before) (OutcomeFamily.interpret after)

/-- Positive mixed-history control: authority expansion may expose a resource
frontier, after which added budget may establish evidence. -/
def internalAuthorityThenBudgetEstablished
    {judgment : ExactJudgment}
    (boundary : BoundaryReason) (frontier : ResourceReceipt)
    (evidence : exactDataAuthority.Evidence judgment) :
    InternalRefinementPath
      (OutcomeFamily.outsideFragment boundary)
      (OutcomeFamily.established evidence) :=
  Outcome.RefinementPath.authorityThenBudgetEstablished
    boundary frontier evidence

@[simp] theorem internalAuthorityThenBudgetEstablished_axes
    {judgment : ExactJudgment}
    (boundary : BoundaryReason) (frontier : ResourceReceipt)
    (evidence : exactDataAuthority.Evidence judgment) :
    Outcome.RefinementPath.axes
      (internalAuthorityThenBudgetEstablished boundary frontier evidence) =
      [.authority, .budget] :=
  rfl

/-- Negative mixed-history control: no sequence of budget and authority
refinements can reverse a settled positive polarity. -/
theorem internalEstablishedToRefuted_forbidden
    {judgment : ExactJudgment}
    (evidence : exactDataAuthority.Evidence judgment)
    (obstruction : exactDataAuthority.Obstruction judgment)
    (path : InternalRefinementPath
      (OutcomeFamily.established evidence)
      (OutcomeFamily.refuted obstruction)) : False :=
  Outcome.RefinementPath.establishedToRefuted_forbidden path

/-! ## Honest object-language boundary

The constructions above certify the semantic polynomial and its external
model by equivalences and inhabitants.  Intrinsic declarations are certified
in the later modules that actually construct their formation, positivity,
elimination, and computation evidence.  No self-populated status list is used
as a substitute for those witnesses. -/

/-! ## Axiom audit -/

#print axioms internalOutcomeModel
#print axioms Intrinsic.outcomeSignatureType_hasType
#print axioms Intrinsic.parameterSignatureValue_hasType
#print axioms Intrinsic.rawOutcomeSignature_formed
#print axioms Intrinsic.establishedIotaReceipt
#print axioms Intrinsic.refutedIotaReceipt
#print axioms Intrinsic.outsideFragmentIotaReceipt
#print axioms Intrinsic.incompleteIotaReceipt
#print axioms Intrinsic.outcomeCandidate
#print axioms Intrinsic.outcomeInFunctionDomain_not_strictlyPositive
#print axioms internalRunModel
#print axioms internalReceiptModel
#print axioms internalBudgetRefinement_support_iff
#print axioms internalBudgetAxisEquiv
#print axioms internalAuthorityAxisEquiv
#print axioms internalAxisRefinement_support_iff
#print axioms internalAuthorityThenBudgetEstablished_axes
#print axioms internalEstablishedToRefuted_forbidden
#print axioms internal_established_ne_refuted

end InternalAuthorityMetatheory
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
