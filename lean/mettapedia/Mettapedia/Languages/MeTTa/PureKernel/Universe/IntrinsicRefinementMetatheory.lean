import Mettapedia.Languages.MeTTa.PureKernel.Universe.IntrinsicRefinementAxis

/-!
# Intrinsic authority refinement relations

Authority outcomes admit two different monotone evolutions.  Increasing the
budget of one fixed authority may resolve `Incomplete`, but it cannot change
an `OutsideFragment` boundary.  Replacing the authority may cross that
boundary, but that is a different relation with different evidence.

This module internalizes those orders as proof-relevant indexed families.
The endpoint outcomes remain indices, so illegal transitions have no
constructor rather than being rejected by a Boolean side condition.  The
construction is generic in an outcome signature and does not privilege a
guest language, checker, or runtime.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe
namespace InternalAuthorityMetatheory
namespace Intrinsic

open Presentation
open Presentation.SchemaElaboration
open Presentation.Declaration
open Presentation.Declaration.ComputationAuthority
open Presentation.Declaration.IndexedFamily

/-! ## Fixed-authority budget refinement -/

def budgetRefinementLevel : LevelExpr := outcomeLevel
def budgetRefinementMotiveLevel : LevelExpr := .param 16

def budgetRefinementName : DeclName :=
  `Prime.Authority.BudgetRefines
def budgetEstablishedName : DeclName :=
  `Prime.Authority.BudgetRefines.established
def budgetRefutedName : DeclName :=
  `Prime.Authority.BudgetRefines.refuted
def budgetOutsideFragmentName : DeclName :=
  `Prime.Authority.BudgetRefines.outsideFragment
def budgetIncompleteName : DeclName :=
  `Prime.Authority.BudgetRefines.incomplete
def budgetIncompleteEstablishedName : DeclName :=
  `Prime.Authority.BudgetRefines.incompleteEstablished
def budgetIncompleteRefutedName : DeclName :=
  `Prime.Authority.BudgetRefines.incompleteRefuted
def budgetRefinementEliminateName : DeclName :=
  `Prime.Authority.BudgetRefines.eliminate

def budgetRefinementApp
    (signature judgment before after : Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app
        (.app (.const budgetRefinementName) signature)
        judgment)
      before)
    after

def budgetEstablishedApp
    (signature judgment beforeEvidence afterEvidence : Tower.Tm n) :
    Tower.Tm n :=
  .app
    (.app
      (.app
        (.app (.const budgetEstablishedName) signature)
        judgment)
      beforeEvidence)
    afterEvidence

def budgetRefutedApp
    (signature judgment beforeObstruction afterObstruction : Tower.Tm n) :
    Tower.Tm n :=
  .app
    (.app
      (.app
        (.app (.const budgetRefutedName) signature)
        judgment)
      beforeObstruction)
    afterObstruction

def budgetOutsideFragmentApp
    (signature judgment reason : Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app (.const budgetOutsideFragmentName) signature)
      judgment)
    reason

def budgetIncompleteApp
    (signature judgment beforeFrontier afterFrontier : Tower.Tm n) :
    Tower.Tm n :=
  .app
    (.app
      (.app
        (.app (.const budgetIncompleteName) signature)
        judgment)
      beforeFrontier)
    afterFrontier

def budgetIncompleteEstablishedApp
    (signature judgment frontier evidence : Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app
        (.app (.const budgetIncompleteEstablishedName) signature)
        judgment)
      frontier)
    evidence

def budgetIncompleteRefutedApp
    (signature judgment frontier obstruction : Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app
        (.app (.const budgetIncompleteRefutedName) signature)
        judgment)
      frontier)
    obstruction

def budgetRefinementEliminateApp
    (signature motive establishedCase refutedCase outsideCase incompleteCase
      incompleteEstablishedCase incompleteRefutedCase judgment before after
      refinement : Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app
        (.app
          (.app
            (.app
              (.app
                (.app
                  (.app
                    (.app
                      (.app
                        (.app (.const budgetRefinementEliminateName) signature)
                        motive)
                      establishedCase)
                    refutedCase)
                  outsideCase)
                incompleteCase)
              incompleteEstablishedCase)
            incompleteRefutedCase)
          judgment)
        before)
      after)
    refinement

@[simp] theorem rename_budgetRefinementApp (renameMap : Ren n m)
    (signature judgment before after : Tower.Tm n) :
    Presentation.rename renameMap
        (budgetRefinementApp signature judgment before after) =
      budgetRefinementApp
        (Presentation.rename renameMap signature)
        (Presentation.rename renameMap judgment)
        (Presentation.rename renameMap before)
        (Presentation.rename renameMap after) :=
  rfl

@[simp] theorem subst_budgetRefinementApp
    (substitution : Sub Tower.Head n m)
    (signature judgment before after : Tower.Tm n) :
    Presentation.subst substitution
        (budgetRefinementApp signature judgment before after) =
      budgetRefinementApp
        (Presentation.subst substitution signature)
        (Presentation.subst substitution judgment)
        (Presentation.subst substitution before)
        (Presentation.subst substitution after) :=
  rfl

@[simp] theorem subst_establishedApp_local
    (substitution : Sub Tower.Head n m)
    (signature judgment witness : Tower.Tm n) :
    Presentation.subst substitution
        (establishedApp signature judgment witness) =
      establishedApp
        (Presentation.subst substitution signature)
        (Presentation.subst substitution judgment)
        (Presentation.subst substitution witness) :=
  rfl

@[simp] theorem subst_refutedApp_local
    (substitution : Sub Tower.Head n m)
    (signature judgment witness : Tower.Tm n) :
    Presentation.subst substitution
        (refutedApp signature judgment witness) =
      refutedApp
        (Presentation.subst substitution signature)
        (Presentation.subst substitution judgment)
        (Presentation.subst substitution witness) :=
  rfl

@[simp] theorem subst_outsideFragmentApp_local
    (substitution : Sub Tower.Head n m)
    (signature judgment witness : Tower.Tm n) :
    Presentation.subst substitution
        (outsideFragmentApp signature judgment witness) =
      outsideFragmentApp
        (Presentation.subst substitution signature)
        (Presentation.subst substitution judgment)
        (Presentation.subst substitution witness) :=
  rfl

@[simp] theorem subst_incompleteApp_local
    (substitution : Sub Tower.Head n m)
    (signature judgment witness : Tower.Tm n) :
    Presentation.subst substitution
        (incompleteApp signature judgment witness) =
      incompleteApp
        (Presentation.subst substitution signature)
        (Presentation.subst substitution judgment)
        (Presentation.subst substitution witness) :=
  rfl

/-! ### Family and constructor types -/

/-- `BudgetRefines : (S : OutcomeSignature) → (j : S.J) →
    Outcome S j → Outcome S j → U`. -/
def budgetRefinementBodyType : Tower.Tm 1 :=
  .pi (signatureJudgment (.var 0))
    (.pi (outcomeApp (.var 1) (.var 0))
      (.pi (outcomeApp (.var 2) (.var 1))
        (sortTm budgetRefinementLevel)))

def budgetRefinementType : Tower.Tm 0 :=
  .pi outcomeSignatureType budgetRefinementBodyType

def budgetEstablishedBodyType : Tower.Tm 1 :=
  .pi (signatureJudgment (.var 0))
    (.pi (.app (signatureEvidence (.var 1)) (.var 0))
      (.pi (.app (signatureEvidence (.var 2)) (.var 1))
        (budgetRefinementApp (.var 3) (.var 2)
          (establishedApp (.var 3) (.var 2) (.var 1))
          (establishedApp (.var 3) (.var 2) (.var 0)))))

def budgetEstablishedType : Tower.Tm 0 :=
  .pi outcomeSignatureType budgetEstablishedBodyType

def budgetRefutedBodyType : Tower.Tm 1 :=
  .pi (signatureJudgment (.var 0))
    (.pi (.app (signatureObstruction (.var 1)) (.var 0))
      (.pi (.app (signatureObstruction (.var 2)) (.var 1))
        (budgetRefinementApp (.var 3) (.var 2)
          (refutedApp (.var 3) (.var 2) (.var 1))
          (refutedApp (.var 3) (.var 2) (.var 0)))))

def budgetRefutedType : Tower.Tm 0 :=
  .pi outcomeSignatureType budgetRefutedBodyType

def budgetOutsideFragmentBodyType : Tower.Tm 1 :=
  .pi (signatureJudgment (.var 0))
    (.pi (.app (signatureBoundary (.var 1)) (.var 0))
      (budgetRefinementApp (.var 2) (.var 1)
        (outsideFragmentApp (.var 2) (.var 1) (.var 0))
        (outsideFragmentApp (.var 2) (.var 1) (.var 0))))

def budgetOutsideFragmentType : Tower.Tm 0 :=
  .pi outcomeSignatureType budgetOutsideFragmentBodyType

def budgetIncompleteBodyType : Tower.Tm 1 :=
  .pi (signatureJudgment (.var 0))
    (.pi (.app (signatureFrontier (.var 1)) (.var 0))
      (.pi (.app (signatureFrontier (.var 2)) (.var 1))
        (budgetRefinementApp (.var 3) (.var 2)
          (incompleteApp (.var 3) (.var 2) (.var 1))
          (incompleteApp (.var 3) (.var 2) (.var 0)))))

def budgetIncompleteType : Tower.Tm 0 :=
  .pi outcomeSignatureType budgetIncompleteBodyType

def budgetIncompleteEstablishedBodyType : Tower.Tm 1 :=
  .pi (signatureJudgment (.var 0))
    (.pi (.app (signatureFrontier (.var 1)) (.var 0))
      (.pi (.app (signatureEvidence (.var 2)) (.var 1))
        (budgetRefinementApp (.var 3) (.var 2)
          (incompleteApp (.var 3) (.var 2) (.var 1))
          (establishedApp (.var 3) (.var 2) (.var 0)))))

def budgetIncompleteEstablishedType : Tower.Tm 0 :=
  .pi outcomeSignatureType budgetIncompleteEstablishedBodyType

def budgetIncompleteRefutedBodyType : Tower.Tm 1 :=
  .pi (signatureJudgment (.var 0))
    (.pi (.app (signatureFrontier (.var 1)) (.var 0))
      (.pi (.app (signatureObstruction (.var 2)) (.var 1))
        (budgetRefinementApp (.var 3) (.var 2)
          (incompleteApp (.var 3) (.var 2) (.var 1))
          (refutedApp (.var 3) (.var 2) (.var 0)))))

def budgetIncompleteRefutedType : Tower.Tm 0 :=
  .pi outcomeSignatureType budgetIncompleteRefutedBodyType

/-! ### Dependent eliminator types -/

/-- In context `signature`, the motive observes both endpoint outcomes and
the exact refinement witness connecting them. -/
def budgetRefinementMotiveType : Tower.Tm 1 :=
  .pi (signatureJudgment (.var 0))
    (.pi (outcomeApp (.var 1) (.var 0))
      (.pi (outcomeApp (.var 2) (.var 1))
        (.pi
          (budgetRefinementApp (.var 3) (.var 2) (.var 1) (.var 0))
          (sortTm budgetRefinementMotiveLevel))))

def budgetEstablishedCaseType : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (.app (signatureEvidence (.var 2)) (.var 0))
      (.pi (.app (signatureEvidence (.var 3)) (.var 1))
        (.app
          (.app
            (.app
              (.app (.var 3) (.var 2))
              (establishedApp (.var 4) (.var 2) (.var 1)))
            (establishedApp (.var 4) (.var 2) (.var 0)))
          (budgetEstablishedApp (.var 4) (.var 2) (.var 1) (.var 0)))))

def budgetRefutedCaseType : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (.app (signatureObstruction (.var 2)) (.var 0))
      (.pi (.app (signatureObstruction (.var 3)) (.var 1))
        (.app
          (.app
            (.app
              (.app (.var 3) (.var 2))
              (refutedApp (.var 4) (.var 2) (.var 1)))
            (refutedApp (.var 4) (.var 2) (.var 0)))
          (budgetRefutedApp (.var 4) (.var 2) (.var 1) (.var 0)))))

def budgetOutsideFragmentCaseType : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (.app (signatureBoundary (.var 2)) (.var 0))
      (.app
        (.app
          (.app
            (.app (.var 2) (.var 1))
            (outsideFragmentApp (.var 3) (.var 1) (.var 0)))
          (outsideFragmentApp (.var 3) (.var 1) (.var 0)))
        (budgetOutsideFragmentApp (.var 3) (.var 1) (.var 0))))

def budgetIncompleteCaseType : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (.app (signatureFrontier (.var 2)) (.var 0))
      (.pi (.app (signatureFrontier (.var 3)) (.var 1))
        (.app
          (.app
            (.app
              (.app (.var 3) (.var 2))
              (incompleteApp (.var 4) (.var 2) (.var 1)))
            (incompleteApp (.var 4) (.var 2) (.var 0)))
          (budgetIncompleteApp (.var 4) (.var 2) (.var 1) (.var 0)))))

def budgetIncompleteEstablishedCaseType : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (.app (signatureFrontier (.var 2)) (.var 0))
      (.pi (.app (signatureEvidence (.var 3)) (.var 1))
        (.app
          (.app
            (.app
              (.app (.var 3) (.var 2))
              (incompleteApp (.var 4) (.var 2) (.var 1)))
            (establishedApp (.var 4) (.var 2) (.var 0)))
          (budgetIncompleteEstablishedApp
            (.var 4) (.var 2) (.var 1) (.var 0)))))

def budgetIncompleteRefutedCaseType : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (.app (signatureFrontier (.var 2)) (.var 0))
      (.pi (.app (signatureObstruction (.var 3)) (.var 1))
        (.app
          (.app
            (.app
              (.app (.var 3) (.var 2))
              (incompleteApp (.var 4) (.var 2) (.var 1)))
            (refutedApp (.var 4) (.var 2) (.var 0)))
          (budgetIncompleteRefutedApp
            (.var 4) (.var 2) (.var 1) (.var 0)))))

def budgetRefinementEliminateResultType : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (outcomeApp (.var 2) (.var 0))
      (.pi (outcomeApp (.var 3) (.var 1))
        (.pi
          (budgetRefinementApp (.var 4) (.var 2) (.var 1) (.var 0))
          (.app
            (.app
              (.app
                (.app (.var 4) (.var 3)) (.var 2))
              (.var 1))
            (.var 0)))))

def budgetRefutedCaseAfterEstablished : Tower.Tm 3 :=
  Presentation.rename wk budgetRefutedCaseType

def budgetOutsideCaseAfterTwo : Tower.Tm 4 :=
  Presentation.rename wk
    (Presentation.rename wk budgetOutsideFragmentCaseType)

def budgetIncompleteCaseAfterThree : Tower.Tm 5 :=
  Presentation.rename wk
    (Presentation.rename wk
      (Presentation.rename wk budgetIncompleteCaseType))

def budgetIncompleteEstablishedCaseAfterFour : Tower.Tm 6 :=
  Presentation.rename wk
    (Presentation.rename wk
      (Presentation.rename wk
        (Presentation.rename wk budgetIncompleteEstablishedCaseType)))

def budgetIncompleteRefutedCaseAfterFive : Tower.Tm 7 :=
  Presentation.rename wk
    (Presentation.rename wk
      (Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk budgetIncompleteRefutedCaseType))))

def budgetRefinementResultAfterSix : Tower.Tm 8 :=
  Presentation.rename wk
    (Presentation.rename wk
      (Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk
            (Presentation.rename wk
              budgetRefinementEliminateResultType)))))

def budgetRefinementEliminateBodyType : Tower.Tm 1 :=
  .pi budgetRefinementMotiveType
    (.pi budgetEstablishedCaseType
      (.pi budgetRefutedCaseAfterEstablished
        (.pi budgetOutsideCaseAfterTwo
          (.pi budgetIncompleteCaseAfterThree
            (.pi budgetIncompleteEstablishedCaseAfterFour
              (.pi budgetIncompleteRefutedCaseAfterFive
                budgetRefinementResultAfterSix))))))

def budgetRefinementEliminateType : Tower.Tm 0 :=
  .pi outcomeSignatureType budgetRefinementEliminateBodyType

/-! ### Proof-relevant computation carrier -/

inductive BudgetRefinementIotaEvidence (n : Nat) :
    Tower.Tm n → Tower.Tm n → Type where
  | established (signature motive establishedCase refutedCase outsideCase
      incompleteCase incompleteEstablishedCase incompleteRefutedCase
      judgment beforeEvidence afterEvidence : Tower.Tm n) :
      BudgetRefinementIotaEvidence n
        (budgetRefinementEliminateApp signature motive establishedCase
          refutedCase outsideCase incompleteCase incompleteEstablishedCase
          incompleteRefutedCase judgment
          (establishedApp signature judgment beforeEvidence)
          (establishedApp signature judgment afterEvidence)
          (budgetEstablishedApp signature judgment beforeEvidence
            afterEvidence))
        (.app (.app (.app establishedCase judgment) beforeEvidence)
          afterEvidence)
  | refuted (signature motive establishedCase refutedCase outsideCase
      incompleteCase incompleteEstablishedCase incompleteRefutedCase
      judgment beforeObstruction afterObstruction : Tower.Tm n) :
      BudgetRefinementIotaEvidence n
        (budgetRefinementEliminateApp signature motive establishedCase
          refutedCase outsideCase incompleteCase incompleteEstablishedCase
          incompleteRefutedCase judgment
          (refutedApp signature judgment beforeObstruction)
          (refutedApp signature judgment afterObstruction)
          (budgetRefutedApp signature judgment beforeObstruction
            afterObstruction))
        (.app (.app (.app refutedCase judgment) beforeObstruction)
          afterObstruction)
  | outsideFragment (signature motive establishedCase refutedCase outsideCase
      incompleteCase incompleteEstablishedCase incompleteRefutedCase
      judgment reason : Tower.Tm n) :
      BudgetRefinementIotaEvidence n
        (budgetRefinementEliminateApp signature motive establishedCase
          refutedCase outsideCase incompleteCase incompleteEstablishedCase
          incompleteRefutedCase judgment
          (outsideFragmentApp signature judgment reason)
          (outsideFragmentApp signature judgment reason)
          (budgetOutsideFragmentApp signature judgment reason))
        (.app (.app outsideCase judgment) reason)
  | incomplete (signature motive establishedCase refutedCase outsideCase
      incompleteCase incompleteEstablishedCase incompleteRefutedCase
      judgment beforeFrontier afterFrontier : Tower.Tm n) :
      BudgetRefinementIotaEvidence n
        (budgetRefinementEliminateApp signature motive establishedCase
          refutedCase outsideCase incompleteCase incompleteEstablishedCase
          incompleteRefutedCase judgment
          (incompleteApp signature judgment beforeFrontier)
          (incompleteApp signature judgment afterFrontier)
          (budgetIncompleteApp signature judgment beforeFrontier
            afterFrontier))
        (.app (.app (.app incompleteCase judgment) beforeFrontier)
          afterFrontier)
  | incompleteEstablished (signature motive establishedCase refutedCase
      outsideCase incompleteCase incompleteEstablishedCase
      incompleteRefutedCase judgment frontier evidence : Tower.Tm n) :
      BudgetRefinementIotaEvidence n
        (budgetRefinementEliminateApp signature motive establishedCase
          refutedCase outsideCase incompleteCase incompleteEstablishedCase
          incompleteRefutedCase judgment
          (incompleteApp signature judgment frontier)
          (establishedApp signature judgment evidence)
          (budgetIncompleteEstablishedApp signature judgment frontier
            evidence))
        (.app
          (.app (.app incompleteEstablishedCase judgment) frontier)
          evidence)
  | incompleteRefuted (signature motive establishedCase refutedCase
      outsideCase incompleteCase incompleteEstablishedCase
      incompleteRefutedCase judgment frontier obstruction : Tower.Tm n) :
      BudgetRefinementIotaEvidence n
        (budgetRefinementEliminateApp signature motive establishedCase
          refutedCase outsideCase incompleteCase incompleteEstablishedCase
          incompleteRefutedCase judgment
          (incompleteApp signature judgment frontier)
          (refutedApp signature judgment obstruction)
          (budgetIncompleteRefutedApp signature judgment frontier
            obstruction))
        (.app (.app (.app incompleteRefutedCase judgment) frontier)
          obstruction)

def BudgetRefinementIotaEvidence.rename {left right : Tower.Tm n}
    (evidence : BudgetRefinementIotaEvidence n left right)
    (renameMap : Ren n m) :
    BudgetRefinementIotaEvidence m
      (Presentation.rename renameMap left)
      (Presentation.rename renameMap right) := by
  cases evidence with
  | established => exact .established _ _ _ _ _ _ _ _ _ _ _
  | refuted => exact .refuted _ _ _ _ _ _ _ _ _ _ _
  | outsideFragment => exact .outsideFragment _ _ _ _ _ _ _ _ _ _
  | incomplete => exact .incomplete _ _ _ _ _ _ _ _ _ _ _
  | incompleteEstablished =>
      exact .incompleteEstablished _ _ _ _ _ _ _ _ _ _ _
  | incompleteRefuted => exact .incompleteRefuted _ _ _ _ _ _ _ _ _ _ _

def BudgetRefinementIotaEvidence.substitute {left right : Tower.Tm n}
    (evidence : BudgetRefinementIotaEvidence n left right)
    (substitution : Sub Tower.Head n m) :
    BudgetRefinementIotaEvidence m
      (Presentation.subst substitution left)
      (Presentation.subst substitution right) := by
  cases evidence with
  | established => exact .established _ _ _ _ _ _ _ _ _ _ _
  | refuted => exact .refuted _ _ _ _ _ _ _ _ _ _ _
  | outsideFragment => exact .outsideFragment _ _ _ _ _ _ _ _ _ _
  | incomplete => exact .incomplete _ _ _ _ _ _ _ _ _ _ _
  | incompleteEstablished =>
      exact .incompleteEstablished _ _ _ _ _ _ _ _ _ _ _
  | incompleteRefuted => exact .incompleteRefuted _ _ _ _ _ _ _ _ _ _ _

/-- Proof-relevant root computation generated by the six exact refinement
rules.  Its support relation is only the proposition-valued readout. -/
def proofRelevantBudgetRefinementComputation :
    ProofRelevantRootComputation Tower.Head where
  Evidence := BudgetRefinementIotaEvidence _
  rename := by
    intro n m renameMap left right evidence
    exact evidence.rename renameMap
  substitute := by
    intro n m substitution left right evidence
    exact evidence.substitute substitution

def budgetRefinementComputation : RootComputation Tower.Head :=
  proofRelevantBudgetRefinementComputation.support

/-! ### Declaration signature -/

def budgetRefinementDeclarations :
    List (DeclName × Entry Tower.Head) :=
  [(budgetRefinementName, { type := budgetRefinementType }),
   (budgetEstablishedName, { type := budgetEstablishedType }),
   (budgetRefutedName, { type := budgetRefutedType }),
   (budgetOutsideFragmentName, { type := budgetOutsideFragmentType }),
   (budgetIncompleteName, { type := budgetIncompleteType }),
   (budgetIncompleteEstablishedName,
      { type := budgetIncompleteEstablishedType }),
   (budgetIncompleteRefutedName, { type := budgetIncompleteRefutedType }),
   (budgetRefinementEliminateName,
      { type := budgetRefinementEliminateType })]

def rawBudgetRefinementSignature : Signature Tower.Head where
  entries :=
    (Signature.ofList budgetRefinementDeclarations).entries
  computation := budgetRefinementComputation

abbrev budgetRefinementRules : Rules Tower.Head :=
  extendRules emptyRules rawBudgetRefinementSignature

@[simp] theorem typeOf_budgetRefinement :
    rawBudgetRefinementSignature.typeOf? budgetRefinementName =
      some budgetRefinementType := by
  simp [rawBudgetRefinementSignature,
    budgetRefinementDeclarations, budgetRefinementName,
    budgetEstablishedName, budgetRefutedName,
    budgetOutsideFragmentName, budgetIncompleteName,
    budgetIncompleteEstablishedName, budgetIncompleteRefutedName,
    Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_budgetEstablished :
    rawBudgetRefinementSignature.typeOf? budgetEstablishedName =
      some budgetEstablishedType := by
  simp [rawBudgetRefinementSignature,
    budgetRefinementDeclarations, budgetRefinementName,
    budgetEstablishedName, budgetRefutedName,
    budgetOutsideFragmentName, budgetIncompleteName,
    budgetIncompleteEstablishedName, budgetIncompleteRefutedName,
    Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_budgetRefuted :
    rawBudgetRefinementSignature.typeOf? budgetRefutedName =
      some budgetRefutedType := by
  simp [rawBudgetRefinementSignature,
    budgetRefinementDeclarations, budgetRefinementName,
    budgetEstablishedName, budgetRefutedName,
    budgetOutsideFragmentName, budgetIncompleteName,
    budgetIncompleteEstablishedName, budgetIncompleteRefutedName,
    Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_budgetOutsideFragment :
    rawBudgetRefinementSignature.typeOf? budgetOutsideFragmentName =
      some budgetOutsideFragmentType := by
  simp [rawBudgetRefinementSignature,
    budgetRefinementDeclarations, budgetRefinementName,
    budgetEstablishedName, budgetRefutedName,
    budgetOutsideFragmentName, budgetIncompleteName,
    budgetIncompleteEstablishedName, budgetIncompleteRefutedName,
    Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_budgetIncomplete :
    rawBudgetRefinementSignature.typeOf? budgetIncompleteName =
      some budgetIncompleteType := by
  simp [rawBudgetRefinementSignature,
    budgetRefinementDeclarations, budgetRefinementName,
    budgetEstablishedName, budgetRefutedName,
    budgetOutsideFragmentName, budgetIncompleteName,
    budgetIncompleteEstablishedName, budgetIncompleteRefutedName,
    Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_budgetIncompleteEstablished :
    rawBudgetRefinementSignature.typeOf?
        budgetIncompleteEstablishedName =
      some budgetIncompleteEstablishedType := by
  simp [rawBudgetRefinementSignature,
    budgetRefinementDeclarations, budgetRefinementName,
    budgetEstablishedName, budgetRefutedName,
    budgetOutsideFragmentName, budgetIncompleteName,
    budgetIncompleteEstablishedName, budgetIncompleteRefutedName,
    Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_budgetIncompleteRefuted :
    rawBudgetRefinementSignature.typeOf?
        budgetIncompleteRefutedName =
      some budgetIncompleteRefutedType := by
  simp [rawBudgetRefinementSignature,
    budgetRefinementDeclarations, budgetRefinementName,
    budgetEstablishedName, budgetRefutedName,
    budgetOutsideFragmentName, budgetIncompleteName,
    budgetIncompleteEstablishedName, budgetIncompleteRefutedName,
    Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_budgetRefinementEliminate :
    rawBudgetRefinementSignature.typeOf?
        budgetRefinementEliminateName =
      some budgetRefinementEliminateType := by
  simp [rawBudgetRefinementSignature,
    budgetRefinementDeclarations, budgetRefinementName,
    budgetEstablishedName, budgetRefutedName,
    budgetOutsideFragmentName, budgetIncompleteName,
    budgetIncompleteEstablishedName, budgetIncompleteRefutedName,
    budgetRefinementEliminateName, Signature.ofList, Signature.insert,
    Signature.typeOf?]

abbrev BudgetRefinementHasType {n : Nat} :=
  @Presentation.HasType Tower.Head budgetRefinementRules n

def includeEmptyInBudgetRefinement {context : Tower.Ctx n}
    {term type : Tower.Tm n}
    (typing : EmptyHasType context term type) :
    BudgetRefinementHasType context term type :=
  Presentation.Declaration.HasType.includeSignature emptyRules
    rawBudgetRefinementSignature typing

def includeOutcomeInBudgetRefinement {context : Tower.Ctx n}
    {term type : Tower.Tm n}
    (typing : IntrinsicHasType context term type) :
    BudgetRefinementHasType context term type :=
  includeEmptyInBudgetRefinement
    (includeReceiptTyping (includeRunTyping (includeOutcomeTyping typing)))

private theorem budgetRefinementName_fresh :
    emptyRules.constantType budgetRefinementName = none := by
  decide

private theorem budgetEstablishedName_fresh :
    emptyRules.constantType budgetEstablishedName = none := by
  decide

private theorem budgetRefutedName_fresh :
    emptyRules.constantType budgetRefutedName = none := by
  decide

private theorem budgetOutsideFragmentName_fresh :
    emptyRules.constantType budgetOutsideFragmentName = none := by
  decide

private theorem budgetIncompleteName_fresh :
    emptyRules.constantType budgetIncompleteName = none := by
  decide

private theorem budgetIncompleteEstablishedName_fresh :
    emptyRules.constantType budgetIncompleteEstablishedName = none := by
  decide

private theorem budgetIncompleteRefutedName_fresh :
    emptyRules.constantType budgetIncompleteRefutedName = none := by
  decide

private theorem budgetRefinementEliminateName_fresh :
    emptyRules.constantType budgetRefinementEliminateName = none := by
  decide

private theorem declaredBudgetRefinementConstant_hasType
    {name : DeclName} {type : Tower.Tm 0}
    (lookup : rawBudgetRefinementSignature.typeOf? name = some type)
    (fresh : emptyRules.constantType name = none)
    {context : Tower.Ctx n} :
    BudgetRefinementHasType context (.const name)
      (liftClosed type) := by
  apply Presentation.HasType.const
  change combinedType emptyRules rawBudgetRefinementSignature name =
    some type
  exact combinedType_of_signature emptyRules
    rawBudgetRefinementSignature fresh lookup

theorem budgetRefinementConstant_hasType {context : Tower.Ctx n} :
    BudgetRefinementHasType context (.const budgetRefinementName)
      (liftClosed budgetRefinementType) :=
  declaredBudgetRefinementConstant_hasType typeOf_budgetRefinement
    budgetRefinementName_fresh

theorem budgetEstablishedConstant_hasType {context : Tower.Ctx n} :
    BudgetRefinementHasType context (.const budgetEstablishedName)
      (liftClosed budgetEstablishedType) :=
  declaredBudgetRefinementConstant_hasType typeOf_budgetEstablished
    budgetEstablishedName_fresh

theorem budgetRefutedConstant_hasType {context : Tower.Ctx n} :
    BudgetRefinementHasType context (.const budgetRefutedName)
      (liftClosed budgetRefutedType) :=
  declaredBudgetRefinementConstant_hasType typeOf_budgetRefuted
    budgetRefutedName_fresh

theorem budgetOutsideFragmentConstant_hasType {context : Tower.Ctx n} :
    BudgetRefinementHasType context
      (.const budgetOutsideFragmentName)
      (liftClosed budgetOutsideFragmentType) :=
  declaredBudgetRefinementConstant_hasType typeOf_budgetOutsideFragment
    budgetOutsideFragmentName_fresh

theorem budgetIncompleteConstant_hasType {context : Tower.Ctx n} :
    BudgetRefinementHasType context (.const budgetIncompleteName)
      (liftClosed budgetIncompleteType) :=
  declaredBudgetRefinementConstant_hasType typeOf_budgetIncomplete
    budgetIncompleteName_fresh

theorem budgetIncompleteEstablishedConstant_hasType
    {context : Tower.Ctx n} :
    BudgetRefinementHasType context
      (.const budgetIncompleteEstablishedName)
      (liftClosed budgetIncompleteEstablishedType) :=
  declaredBudgetRefinementConstant_hasType
    typeOf_budgetIncompleteEstablished
    budgetIncompleteEstablishedName_fresh

theorem budgetIncompleteRefutedConstant_hasType
    {context : Tower.Ctx n} :
    BudgetRefinementHasType context
      (.const budgetIncompleteRefutedName)
      (liftClosed budgetIncompleteRefutedType) :=
  declaredBudgetRefinementConstant_hasType typeOf_budgetIncompleteRefuted
    budgetIncompleteRefutedName_fresh

theorem budgetRefinementEliminateConstant_hasType
    {context : Tower.Ctx n} :
    BudgetRefinementHasType context
      (.const budgetRefinementEliminateName)
      (liftClosed budgetRefinementEliminateType) :=
  declaredBudgetRefinementConstant_hasType
    typeOf_budgetRefinementEliminate
    budgetRefinementEliminateName_fresh

def budgetRefinementAtSignatureType (signature : Tower.Tm n) :
    Tower.Tm n :=
  .pi (signatureJudgment signature)
    (.pi (outcomeApp (Presentation.rename wk signature) (.var 0))
      (.pi
        (outcomeApp
          (Presentation.rename wk (Presentation.rename wk signature))
          (.var 1))
        (sortTm budgetRefinementLevel)))

@[simp] theorem substitute_budgetRefinementBodyType
    (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature)
        budgetRefinementBodyType =
      budgetRefinementAtSignatureType signature := by
  simp [budgetRefinementBodyType, budgetRefinementAtSignatureType,
    Presentation.subst]

@[simp] theorem open_under_one_after_two_weakenings
    (argument term : Tower.Tm n) :
    Presentation.subst (Presentation.liftSub
        (Presentation.subst0 argument))
        (Presentation.rename (fun i => wk (wk i)) term) =
      Presentation.rename wk term := by
  rw [← Presentation.rename_comp wk wk term]
  rw [Presentation.subst_liftSub_wk]
  exact congrArg (Presentation.rename wk)
    (Presentation.inst0_rename_wk argument term)

@[simp] theorem open_under_two_after_three_weakenings
    (argument term : Tower.Tm n) :
    Presentation.subst
        (Presentation.liftSub
          (Presentation.liftSub (Presentation.subst0 argument)))
        (Presentation.rename (fun i => wk (wk (wk i))) term) =
      Presentation.rename (fun i => wk (wk i)) term := by
  rw [← Presentation.rename_comp wk (fun i => wk (wk i)) term]
  rw [← Presentation.rename_comp wk wk term]
  rw [open_weakened_under_two]

@[simp] theorem liftSub_three_singleParameter_two
    (term : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub
          (Presentation.liftSub (fun _ : Fin 1 => term)))
        (2 : Fin 4) = (.var 2 : Tower.Tm (n + 3)) := by
  rfl

theorem budgetRefinementApp_hasType {context : Tower.Ctx n}
    {signature judgment before after : Tower.Tm n}
    (signatureTyping : BudgetRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : BudgetRefinementHasType context judgment
      (signatureJudgment signature))
    (beforeTyping : BudgetRefinementHasType context before
      (outcomeApp signature judgment))
    (afterTyping : BudgetRefinementHasType context after
      (outcomeApp signature judgment)) :
    BudgetRefinementHasType context
      (budgetRefinementApp signature judgment before after)
      (sortTm budgetRefinementLevel) := by
  have afterSignature := Presentation.HasType.appElim
    (budgetRefinementConstant_hasType (context := context)) signatureTyping
  have afterSignatureNormalized :
      BudgetRefinementHasType context
        (.app (.const budgetRefinementName) signature)
        (budgetRefinementAtSignatureType signature) := by
    simpa only [budgetRefinementType, liftClosed,
      inst0_rename_liftRen_elim0,
      substitute_budgetRefinementBodyType] using afterSignature
  have afterJudgment := Presentation.HasType.appElim
    afterSignatureNormalized judgmentTyping
  have afterJudgmentNormalized :
      BudgetRefinementHasType context
        (.app (.app (.const budgetRefinementName) signature) judgment)
        (.pi (outcomeApp signature judgment)
          (.pi
            (outcomeApp (Presentation.rename wk signature)
              (Presentation.rename wk judgment))
            (sortTm budgetRefinementLevel))) := by
    convert afterJudgment using 1
    all_goals simp [Presentation.inst0, Presentation.subst]
  have afterBefore := Presentation.HasType.appElim afterJudgmentNormalized
    beforeTyping
  have afterBeforeNormalized :
      BudgetRefinementHasType context
        (.app
          (.app (.app (.const budgetRefinementName) signature) judgment)
          before)
        (.pi (outcomeApp signature judgment)
          (sortTm budgetRefinementLevel)) := by
    convert afterBefore using 1
    all_goals simp [Presentation.inst0, Presentation.subst]
  have afterAfter := Presentation.HasType.appElim afterBeforeNormalized
    afterTyping
  convert afterAfter using 1
  all_goals rfl

theorem establishedConstant_hasBudgetRefinementType
    {context : Tower.Ctx n} :
    BudgetRefinementHasType context (.const establishedName)
      (liftClosed establishedType) :=
  includeOutcomeInBudgetRefinement establishedConstant_hasType

theorem refutedConstant_hasBudgetRefinementType
    {context : Tower.Ctx n} :
    BudgetRefinementHasType context (.const refutedName)
      (liftClosed refutedType) :=
  includeOutcomeInBudgetRefinement refutedConstant_hasType

theorem outsideFragmentConstant_hasBudgetRefinementType
    {context : Tower.Ctx n} :
    BudgetRefinementHasType context (.const outsideFragmentName)
      (liftClosed outsideFragmentType) :=
  includeOutcomeInBudgetRefinement outsideFragmentConstant_hasType

theorem incompleteConstant_hasBudgetRefinementType
    {context : Tower.Ctx n} :
    BudgetRefinementHasType context (.const incompleteName)
      (liftClosed incompleteType) :=
  includeOutcomeInBudgetRefinement incompleteConstant_hasType

private theorem outcomeConstructorApp_hasBudgetRefinementType
    {context : Tower.Ctx n}
    {constructor : DeclName} {constructorType : Tower.Tm 0}
    {bodyType : Tower.Tm 1}
    {payloadFamily signature judgment witness : Tower.Tm n}
    (constantTyping : BudgetRefinementHasType context
      (.const constructor) (liftClosed constructorType))
    (constructorTypeEquation :
      constructorType = .pi outcomeSignatureType bodyType)
    (openedBody : Presentation.subst (fun _ : Fin 1 => signature) bodyType =
      constructorAtSignatureType signature payloadFamily)
    (signatureTyping : BudgetRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : BudgetRefinementHasType context judgment
      (signatureJudgment signature))
    (witnessTyping : BudgetRefinementHasType context witness
      (.app payloadFamily judgment)) :
    BudgetRefinementHasType context
      (.app (.app (.app (.const constructor) signature) judgment) witness)
      (outcomeApp signature judgment) := by
  subst constructorType
  have afterSignature := Presentation.HasType.appElim constantTyping
    signatureTyping
  have afterSignatureNormalized :
      BudgetRefinementHasType context
        (.app (.const constructor) signature)
        (constructorAtSignatureType signature payloadFamily) := by
    simpa only [liftClosed, inst0_rename_liftRen_elim0,
      openedBody] using afterSignature
  have afterJudgment := Presentation.HasType.appElim
    afterSignatureNormalized judgmentTyping
  have afterJudgmentNormalized :
      BudgetRefinementHasType context
        (.app (.app (.const constructor) signature) judgment)
        (arrow (.app payloadFamily judgment)
          (outcomeApp signature judgment)) := by
    simpa only [constructorAtSignatureType, inst0_arrow,
      inst0_familyApplication_wk, inst0_outcomeApplication_wk] using
      afterJudgment
  have afterWitness := Presentation.HasType.appElim
    afterJudgmentNormalized witnessTyping
  simpa only [arrow, inst0_rename_wk] using afterWitness

theorem establishedApp_hasBudgetRefinementType
    {context : Tower.Ctx n} {signature judgment witness : Tower.Tm n}
    (signatureTyping : BudgetRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : BudgetRefinementHasType context judgment
      (signatureJudgment signature))
    (witnessTyping : BudgetRefinementHasType context witness
      (.app (signatureEvidence signature) judgment)) :
    BudgetRefinementHasType context
      (establishedApp signature judgment witness)
      (outcomeApp signature judgment) := by
  apply outcomeConstructorApp_hasBudgetRefinementType
      establishedConstant_hasBudgetRefinementType rfl
      (substitute_establishedBodyType signature)
      signatureTyping judgmentTyping witnessTyping

theorem refutedApp_hasBudgetRefinementType
    {context : Tower.Ctx n} {signature judgment witness : Tower.Tm n}
    (signatureTyping : BudgetRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : BudgetRefinementHasType context judgment
      (signatureJudgment signature))
    (witnessTyping : BudgetRefinementHasType context witness
      (.app (signatureObstruction signature) judgment)) :
    BudgetRefinementHasType context
      (refutedApp signature judgment witness)
      (outcomeApp signature judgment) := by
  apply outcomeConstructorApp_hasBudgetRefinementType
      refutedConstant_hasBudgetRefinementType rfl
      (substitute_refutedBodyType signature)
      signatureTyping judgmentTyping witnessTyping

theorem outsideFragmentApp_hasBudgetRefinementType
    {context : Tower.Ctx n} {signature judgment witness : Tower.Tm n}
    (signatureTyping : BudgetRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : BudgetRefinementHasType context judgment
      (signatureJudgment signature))
    (witnessTyping : BudgetRefinementHasType context witness
      (.app (signatureBoundary signature) judgment)) :
    BudgetRefinementHasType context
      (outsideFragmentApp signature judgment witness)
      (outcomeApp signature judgment) := by
  apply outcomeConstructorApp_hasBudgetRefinementType
      outsideFragmentConstant_hasBudgetRefinementType rfl
      (substitute_outsideFragmentBodyType signature)
      signatureTyping judgmentTyping witnessTyping

theorem incompleteApp_hasBudgetRefinementType
    {context : Tower.Ctx n} {signature judgment witness : Tower.Tm n}
    (signatureTyping : BudgetRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : BudgetRefinementHasType context judgment
      (signatureJudgment signature))
    (witnessTyping : BudgetRefinementHasType context witness
      (.app (signatureFrontier signature) judgment)) :
    BudgetRefinementHasType context
      (incompleteApp signature judgment witness)
      (outcomeApp signature judgment) := by
  apply outcomeConstructorApp_hasBudgetRefinementType
      incompleteConstant_hasBudgetRefinementType rfl
      (substitute_incompleteBodyType signature)
      signatureTyping judgmentTyping witnessTyping

def namedOutcomeConstructorApp (constructor : DeclName)
    (signature judgment witness : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.const constructor) signature) judgment) witness

def namedBudgetBinaryConstructorApp (constructor : DeclName)
    (signature judgment beforeWitness afterWitness : Tower.Tm n) :
    Tower.Tm n :=
  .app
    (.app
      (.app
        (.app (.const constructor) signature)
        judgment)
      beforeWitness)
    afterWitness

def budgetBinaryAtSignatureType (beforeConstructor afterConstructor :
    DeclName) (signature beforeFamily afterFamily :
    Tower.Tm n) : Tower.Tm n :=
  .pi (signatureJudgment signature)
    (.pi (.app (Presentation.rename wk beforeFamily) (.var 0))
      (.pi
        (.app
          (Presentation.rename wk (Presentation.rename wk afterFamily))
          (.var 1))
        (budgetRefinementApp
          (Presentation.rename wk
            (Presentation.rename wk (Presentation.rename wk signature)))
          (.var 2)
          (namedOutcomeConstructorApp beforeConstructor
            (Presentation.rename wk
              (Presentation.rename wk (Presentation.rename wk signature)))
            (.var 2) (.var 1))
          (namedOutcomeConstructorApp afterConstructor
            (Presentation.rename wk
              (Presentation.rename wk (Presentation.rename wk signature)))
            (.var 2) (.var 0)))))

def budgetBinaryAfterJudgmentType (beforeConstructor afterConstructor :
    DeclName) (signature judgment beforeFamily
    afterFamily : Tower.Tm n) : Tower.Tm n :=
  .pi (.app beforeFamily judgment)
    (.pi
      (.app (Presentation.rename wk afterFamily)
        (Presentation.rename wk judgment))
      (budgetRefinementApp
        (Presentation.rename wk (Presentation.rename wk signature))
        (Presentation.rename wk (Presentation.rename wk judgment))
        (namedOutcomeConstructorApp beforeConstructor
          (Presentation.rename wk (Presentation.rename wk signature))
          (Presentation.rename wk (Presentation.rename wk judgment))
          (.var 1))
        (namedOutcomeConstructorApp afterConstructor
          (Presentation.rename wk (Presentation.rename wk signature))
          (Presentation.rename wk (Presentation.rename wk judgment))
          (.var 0))))

def budgetBinaryAfterBeforeType (beforeConstructor afterConstructor :
    DeclName) (signature judgment beforeWitness
    afterFamily : Tower.Tm n) : Tower.Tm n :=
  .pi (.app afterFamily judgment)
    (budgetRefinementApp
      (Presentation.rename wk signature)
      (Presentation.rename wk judgment)
      (namedOutcomeConstructorApp beforeConstructor
        (Presentation.rename wk signature)
        (Presentation.rename wk judgment)
        (Presentation.rename wk beforeWitness))
      (namedOutcomeConstructorApp afterConstructor
        (Presentation.rename wk signature)
        (Presentation.rename wk judgment)
        (.var 0)))

private theorem budgetBinaryConstructorApp_hasType
    {context : Tower.Ctx n}
    {relationConstructor beforeConstructor afterConstructor : DeclName}
    {relationType : Tower.Tm 0} {bodyType : Tower.Tm 1}
    {signature judgment beforeWitness afterWitness beforeFamily
      afterFamily : Tower.Tm n}
    (constantTyping : BudgetRefinementHasType context
      (.const relationConstructor) (liftClosed relationType))
    (relationTypeEquation :
      relationType = .pi outcomeSignatureType bodyType)
    (openedBody : Presentation.subst (fun _ : Fin 1 => signature) bodyType =
      budgetBinaryAtSignatureType beforeConstructor afterConstructor
        signature beforeFamily afterFamily)
    (signatureTyping : BudgetRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : BudgetRefinementHasType context judgment
      (signatureJudgment signature))
    (beforeTyping : BudgetRefinementHasType context beforeWitness
      (.app beforeFamily judgment))
    (afterTyping : BudgetRefinementHasType context afterWitness
      (.app afterFamily judgment)) :
    BudgetRefinementHasType context
      (namedBudgetBinaryConstructorApp relationConstructor signature judgment
        beforeWitness afterWitness)
      (budgetRefinementApp signature judgment
        (namedOutcomeConstructorApp beforeConstructor signature judgment
          beforeWitness)
        (namedOutcomeConstructorApp afterConstructor signature judgment
          afterWitness)) := by
  subst relationType
  have afterSignature := Presentation.HasType.appElim constantTyping
    signatureTyping
  have afterSignatureNormalized :
      BudgetRefinementHasType context
        (.app (.const relationConstructor) signature)
        (budgetBinaryAtSignatureType beforeConstructor afterConstructor
          signature beforeFamily afterFamily) := by
    simpa only [liftClosed, inst0_rename_liftRen_elim0,
      openedBody] using afterSignature
  have afterJudgment := Presentation.HasType.appElim
    afterSignatureNormalized judgmentTyping
  have afterJudgmentNormalized :
      BudgetRefinementHasType context
        (.app (.app (.const relationConstructor) signature) judgment)
        (budgetBinaryAfterJudgmentType beforeConstructor afterConstructor
          signature judgment beforeFamily afterFamily) := by
    convert afterJudgment using 1
    all_goals simp [budgetBinaryAfterJudgmentType,
      namedOutcomeConstructorApp, budgetRefinementApp,
      Presentation.inst0, Presentation.subst]
  have afterBefore := Presentation.HasType.appElim afterJudgmentNormalized
    beforeTyping
  have afterBeforeNormalized :
      BudgetRefinementHasType context
        (.app
          (.app (.app (.const relationConstructor) signature) judgment)
          beforeWitness)
        (budgetBinaryAfterBeforeType beforeConstructor afterConstructor
          signature judgment beforeWitness afterFamily) := by
    convert afterBefore using 1
    all_goals simp [budgetBinaryAfterBeforeType,
      namedOutcomeConstructorApp, budgetRefinementApp,
      Presentation.inst0, Presentation.subst]
  have afterAfter := Presentation.HasType.appElim afterBeforeNormalized
    afterTyping
  convert afterAfter using 1
  all_goals simp [namedBudgetBinaryConstructorApp,
    namedOutcomeConstructorApp, budgetRefinementApp,
    Presentation.inst0, Presentation.subst]

@[simp] theorem substitute_budgetEstablishedBodyType
    (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature)
        budgetEstablishedBodyType =
      budgetBinaryAtSignatureType establishedName establishedName signature
        (signatureEvidence signature)
        (signatureEvidence signature) := by
  simp [budgetEstablishedBodyType, budgetBinaryAtSignatureType,
    namedOutcomeConstructorApp, budgetRefinementApp, establishedApp,
    Presentation.subst]

theorem budgetEstablishedApp_hasType {context : Tower.Ctx n}
    {signature judgment beforeEvidence afterEvidence : Tower.Tm n}
    (signatureTyping : BudgetRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : BudgetRefinementHasType context judgment
      (signatureJudgment signature))
    (beforeTyping : BudgetRefinementHasType context beforeEvidence
      (.app (signatureEvidence signature) judgment))
    (afterTyping : BudgetRefinementHasType context afterEvidence
      (.app (signatureEvidence signature) judgment)) :
    BudgetRefinementHasType context
      (budgetEstablishedApp signature judgment beforeEvidence afterEvidence)
      (budgetRefinementApp signature judgment
        (establishedApp signature judgment beforeEvidence)
        (establishedApp signature judgment afterEvidence)) := by
  have generic := budgetBinaryConstructorApp_hasType
    (context := context)
    (relationConstructor := budgetEstablishedName)
    (beforeConstructor := establishedName)
    (afterConstructor := establishedName)
    (bodyType := budgetEstablishedBodyType)
    (beforeFamily := signatureEvidence signature)
    (afterFamily := signatureEvidence signature)
    budgetEstablishedConstant_hasType rfl
    (substitute_budgetEstablishedBodyType signature)
    signatureTyping judgmentTyping beforeTyping afterTyping
  simpa [namedBudgetBinaryConstructorApp, namedOutcomeConstructorApp,
    budgetEstablishedApp, establishedApp] using generic

@[simp] theorem substitute_budgetRefutedBodyType
    (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature)
        budgetRefutedBodyType =
      budgetBinaryAtSignatureType refutedName refutedName signature
        (signatureObstruction signature)
        (signatureObstruction signature) := by
  simp [budgetRefutedBodyType, budgetBinaryAtSignatureType,
    namedOutcomeConstructorApp, budgetRefinementApp, refutedApp,
    Presentation.subst]

theorem budgetRefutedApp_hasType {context : Tower.Ctx n}
    {signature judgment beforeObstruction afterObstruction : Tower.Tm n}
    (signatureTyping : BudgetRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : BudgetRefinementHasType context judgment
      (signatureJudgment signature))
    (beforeTyping : BudgetRefinementHasType context beforeObstruction
      (.app (signatureObstruction signature) judgment))
    (afterTyping : BudgetRefinementHasType context afterObstruction
      (.app (signatureObstruction signature) judgment)) :
    BudgetRefinementHasType context
      (budgetRefutedApp signature judgment beforeObstruction
        afterObstruction)
      (budgetRefinementApp signature judgment
        (refutedApp signature judgment beforeObstruction)
        (refutedApp signature judgment afterObstruction)) := by
  have generic := budgetBinaryConstructorApp_hasType
    (context := context)
    (relationConstructor := budgetRefutedName)
    (beforeConstructor := refutedName)
    (afterConstructor := refutedName)
    (bodyType := budgetRefutedBodyType)
    (beforeFamily := signatureObstruction signature)
    (afterFamily := signatureObstruction signature)
    budgetRefutedConstant_hasType rfl
    (substitute_budgetRefutedBodyType signature)
    signatureTyping judgmentTyping beforeTyping afterTyping
  simpa [namedBudgetBinaryConstructorApp, namedOutcomeConstructorApp,
    budgetRefutedApp, refutedApp] using generic

@[simp] theorem substitute_budgetIncompleteBodyType
    (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature)
        budgetIncompleteBodyType =
      budgetBinaryAtSignatureType incompleteName incompleteName signature
        (signatureFrontier signature) (signatureFrontier signature) := by
  simp [budgetIncompleteBodyType, budgetBinaryAtSignatureType,
    namedOutcomeConstructorApp, budgetRefinementApp, incompleteApp,
    Presentation.subst]

theorem budgetIncompleteApp_hasType {context : Tower.Ctx n}
    {signature judgment beforeFrontier afterFrontier : Tower.Tm n}
    (signatureTyping : BudgetRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : BudgetRefinementHasType context judgment
      (signatureJudgment signature))
    (beforeTyping : BudgetRefinementHasType context beforeFrontier
      (.app (signatureFrontier signature) judgment))
    (afterTyping : BudgetRefinementHasType context afterFrontier
      (.app (signatureFrontier signature) judgment)) :
    BudgetRefinementHasType context
      (budgetIncompleteApp signature judgment beforeFrontier afterFrontier)
      (budgetRefinementApp signature judgment
        (incompleteApp signature judgment beforeFrontier)
        (incompleteApp signature judgment afterFrontier)) := by
  have generic := budgetBinaryConstructorApp_hasType
    (context := context)
    (relationConstructor := budgetIncompleteName)
    (beforeConstructor := incompleteName)
    (afterConstructor := incompleteName)
    (bodyType := budgetIncompleteBodyType)
    (beforeFamily := signatureFrontier signature)
    (afterFamily := signatureFrontier signature)
    budgetIncompleteConstant_hasType rfl
    (substitute_budgetIncompleteBodyType signature)
    signatureTyping judgmentTyping beforeTyping afterTyping
  simpa [namedBudgetBinaryConstructorApp, namedOutcomeConstructorApp,
    budgetIncompleteApp, incompleteApp] using generic

@[simp] theorem substitute_budgetIncompleteEstablishedBodyType
    (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature)
        budgetIncompleteEstablishedBodyType =
      budgetBinaryAtSignatureType incompleteName establishedName signature
        (signatureFrontier signature) (signatureEvidence signature) := by
  simp [budgetIncompleteEstablishedBodyType, budgetBinaryAtSignatureType,
    namedOutcomeConstructorApp, budgetRefinementApp, incompleteApp,
    establishedApp, Presentation.subst]

theorem budgetIncompleteEstablishedApp_hasType
    {context : Tower.Ctx n}
    {signature judgment frontier evidence : Tower.Tm n}
    (signatureTyping : BudgetRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : BudgetRefinementHasType context judgment
      (signatureJudgment signature))
    (frontierTyping : BudgetRefinementHasType context frontier
      (.app (signatureFrontier signature) judgment))
    (evidenceTyping : BudgetRefinementHasType context evidence
      (.app (signatureEvidence signature) judgment)) :
    BudgetRefinementHasType context
      (budgetIncompleteEstablishedApp signature judgment frontier evidence)
      (budgetRefinementApp signature judgment
        (incompleteApp signature judgment frontier)
        (establishedApp signature judgment evidence)) := by
  have generic := budgetBinaryConstructorApp_hasType
    (context := context)
    (relationConstructor := budgetIncompleteEstablishedName)
    (beforeConstructor := incompleteName)
    (afterConstructor := establishedName)
    (bodyType := budgetIncompleteEstablishedBodyType)
    (beforeFamily := signatureFrontier signature)
    (afterFamily := signatureEvidence signature)
    budgetIncompleteEstablishedConstant_hasType rfl
    (substitute_budgetIncompleteEstablishedBodyType signature)
    signatureTyping judgmentTyping frontierTyping evidenceTyping
  simpa [namedBudgetBinaryConstructorApp, namedOutcomeConstructorApp,
    budgetIncompleteEstablishedApp, incompleteApp, establishedApp] using
    generic

@[simp] theorem substitute_budgetIncompleteRefutedBodyType
    (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature)
        budgetIncompleteRefutedBodyType =
      budgetBinaryAtSignatureType incompleteName refutedName signature
        (signatureFrontier signature) (signatureObstruction signature) := by
  simp [budgetIncompleteRefutedBodyType, budgetBinaryAtSignatureType,
    namedOutcomeConstructorApp, budgetRefinementApp, incompleteApp,
    refutedApp, Presentation.subst]

theorem budgetIncompleteRefutedApp_hasType
    {context : Tower.Ctx n}
    {signature judgment frontier obstruction : Tower.Tm n}
    (signatureTyping : BudgetRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : BudgetRefinementHasType context judgment
      (signatureJudgment signature))
    (frontierTyping : BudgetRefinementHasType context frontier
      (.app (signatureFrontier signature) judgment))
    (obstructionTyping : BudgetRefinementHasType context obstruction
      (.app (signatureObstruction signature) judgment)) :
    BudgetRefinementHasType context
      (budgetIncompleteRefutedApp signature judgment frontier obstruction)
      (budgetRefinementApp signature judgment
        (incompleteApp signature judgment frontier)
        (refutedApp signature judgment obstruction)) := by
  have generic := budgetBinaryConstructorApp_hasType
    (context := context)
    (relationConstructor := budgetIncompleteRefutedName)
    (beforeConstructor := incompleteName)
    (afterConstructor := refutedName)
    (bodyType := budgetIncompleteRefutedBodyType)
    (beforeFamily := signatureFrontier signature)
    (afterFamily := signatureObstruction signature)
    budgetIncompleteRefutedConstant_hasType rfl
    (substitute_budgetIncompleteRefutedBodyType signature)
    signatureTyping judgmentTyping frontierTyping obstructionTyping
  simpa [namedBudgetBinaryConstructorApp, namedOutcomeConstructorApp,
    budgetIncompleteRefutedApp, incompleteApp, refutedApp] using generic

def namedBudgetUnaryConstructorApp (constructor : DeclName)
    (signature judgment witness : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.const constructor) signature) judgment) witness

def budgetUnaryAtSignatureType (outcomeConstructor : DeclName)
    (signature payloadFamily : Tower.Tm n) : Tower.Tm n :=
  .pi (signatureJudgment signature)
    (.pi (.app (Presentation.rename wk payloadFamily) (.var 0))
      (budgetRefinementApp
        (Presentation.rename wk (Presentation.rename wk signature))
        (.var 1)
        (namedOutcomeConstructorApp outcomeConstructor
          (Presentation.rename wk (Presentation.rename wk signature))
          (.var 1) (.var 0))
        (namedOutcomeConstructorApp outcomeConstructor
          (Presentation.rename wk (Presentation.rename wk signature))
          (.var 1) (.var 0))))

def budgetUnaryAfterJudgmentType (outcomeConstructor : DeclName)
    (signature judgment payloadFamily : Tower.Tm n) : Tower.Tm n :=
  .pi (.app payloadFamily judgment)
    (budgetRefinementApp
      (Presentation.rename wk signature)
      (Presentation.rename wk judgment)
      (namedOutcomeConstructorApp outcomeConstructor
        (Presentation.rename wk signature)
        (Presentation.rename wk judgment) (.var 0))
      (namedOutcomeConstructorApp outcomeConstructor
        (Presentation.rename wk signature)
        (Presentation.rename wk judgment) (.var 0)))

private theorem budgetUnaryConstructorApp_hasType
    {context : Tower.Ctx n}
    {relationConstructor outcomeConstructor : DeclName}
    {relationType : Tower.Tm 0} {bodyType : Tower.Tm 1}
    {signature judgment witness payloadFamily : Tower.Tm n}
    (constantTyping : BudgetRefinementHasType context
      (.const relationConstructor) (liftClosed relationType))
    (relationTypeEquation :
      relationType = .pi outcomeSignatureType bodyType)
    (openedBody : Presentation.subst (fun _ : Fin 1 => signature) bodyType =
      budgetUnaryAtSignatureType outcomeConstructor signature payloadFamily)
    (signatureTyping : BudgetRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : BudgetRefinementHasType context judgment
      (signatureJudgment signature))
    (witnessTyping : BudgetRefinementHasType context witness
      (.app payloadFamily judgment)) :
    BudgetRefinementHasType context
      (namedBudgetUnaryConstructorApp relationConstructor signature judgment
        witness)
      (budgetRefinementApp signature judgment
        (namedOutcomeConstructorApp outcomeConstructor signature judgment
          witness)
        (namedOutcomeConstructorApp outcomeConstructor signature judgment
          witness)) := by
  subst relationType
  have afterSignature := Presentation.HasType.appElim constantTyping
    signatureTyping
  have afterSignatureNormalized :
      BudgetRefinementHasType context
        (.app (.const relationConstructor) signature)
        (budgetUnaryAtSignatureType outcomeConstructor signature
          payloadFamily) := by
    simpa only [liftClosed, inst0_rename_liftRen_elim0,
      openedBody] using afterSignature
  have afterJudgment := Presentation.HasType.appElim
    afterSignatureNormalized judgmentTyping
  have afterJudgmentNormalized :
      BudgetRefinementHasType context
        (.app (.app (.const relationConstructor) signature) judgment)
        (budgetUnaryAfterJudgmentType outcomeConstructor signature judgment
          payloadFamily) := by
    convert afterJudgment using 1
    all_goals simp [budgetUnaryAfterJudgmentType,
      namedOutcomeConstructorApp, budgetRefinementApp,
      Presentation.inst0, Presentation.subst]
  have afterWitness := Presentation.HasType.appElim
    afterJudgmentNormalized witnessTyping
  convert afterWitness using 1
  all_goals simp [namedBudgetUnaryConstructorApp,
    namedOutcomeConstructorApp, budgetRefinementApp,
    Presentation.inst0, Presentation.subst]

@[simp] theorem substitute_budgetOutsideFragmentBodyType
    (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature)
        budgetOutsideFragmentBodyType =
      budgetUnaryAtSignatureType outsideFragmentName signature
        (signatureBoundary signature) := by
  simp [budgetOutsideFragmentBodyType, budgetUnaryAtSignatureType,
    namedOutcomeConstructorApp, budgetRefinementApp, outsideFragmentApp,
    Presentation.subst]

theorem budgetOutsideFragmentApp_hasType {context : Tower.Ctx n}
    {signature judgment reason : Tower.Tm n}
    (signatureTyping : BudgetRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : BudgetRefinementHasType context judgment
      (signatureJudgment signature))
    (reasonTyping : BudgetRefinementHasType context reason
      (.app (signatureBoundary signature) judgment)) :
    BudgetRefinementHasType context
      (budgetOutsideFragmentApp signature judgment reason)
      (budgetRefinementApp signature judgment
        (outsideFragmentApp signature judgment reason)
        (outsideFragmentApp signature judgment reason)) := by
  have generic := budgetUnaryConstructorApp_hasType
    (context := context)
    (relationConstructor := budgetOutsideFragmentName)
    (outcomeConstructor := outsideFragmentName)
    (bodyType := budgetOutsideFragmentBodyType)
    (payloadFamily := signatureBoundary signature)
    budgetOutsideFragmentConstant_hasType rfl
    (substitute_budgetOutsideFragmentBodyType signature)
    signatureTyping judgmentTyping reasonTyping
  simpa [namedBudgetUnaryConstructorApp, namedOutcomeConstructorApp,
    budgetOutsideFragmentApp, outsideFragmentApp] using generic

theorem outcomeSignatureType_hasBudgetRefinementType :
    BudgetRefinementHasType (.nil : Tower.Ctx 0)
      outcomeSignatureType (sortTm signatureLevel) :=
  includeEmptyInBudgetRefinement outcomeSignatureType_hasEmptyType

def budgetContextS : Tower.Ctx 1 :=
  .snoc .nil outcomeSignatureType

def budgetContextSJ : Tower.Ctx 2 :=
  .snoc budgetContextS (signatureJudgment (.var 0))

def budgetContextSJB : Tower.Ctx 3 :=
  .snoc budgetContextSJ (outcomeApp (.var 1) (.var 0))

def budgetContextSJBA : Tower.Ctx 4 :=
  .snoc budgetContextSJB (outcomeApp (.var 2) (.var 1))

theorem budgetSignatureVar_hasType :
    BudgetRefinementHasType budgetContextS (.var 0)
      (liftClosed outcomeSignatureType) := by
  have variableTyping :=
    (Presentation.HasType.var (R := budgetRefinementRules)
      (Γ := budgetContextS) (0 : Fin 1))
  have lookupEquality :
      Presentation.Ctx.lookup budgetContextS (0 : Fin 1) =
        liftClosed outcomeSignatureType := by
    decide
  simpa only [lookupEquality] using variableTyping

theorem budgetJudgmentVar_hasType :
    BudgetRefinementHasType budgetContextSJ (.var 0)
      (signatureJudgment (.var 1)) := by
  exact Presentation.HasType.var 0

theorem budgetOutcomeBeforeVar_hasType :
    BudgetRefinementHasType budgetContextSJB (.var 0)
      (outcomeApp (.var 2) (.var 1)) := by
  exact Presentation.HasType.var 0

theorem budgetOutcomeAfterVar_hasType :
    BudgetRefinementHasType budgetContextSJBA (.var 0)
      (outcomeApp (.var 3) (.var 2)) := by
  exact Presentation.HasType.var 0

theorem budgetRefinementBodyType_hasType :
    BudgetRefinementHasType budgetContextS
      budgetRefinementBodyType
      (sortTm
        (.max judgmentLevel
          (.max outcomeLevel
            (.max outcomeLevel (.succ budgetRefinementLevel))))) := by
  unfold budgetRefinementBodyType budgetContextS
  apply Presentation.HasType.piForm
  · exact signatureJudgment_hasType budgetSignatureVar_hasType
  · exact Tower.IsUniverse.sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply outcomeApp_hasTypeWith
      · exact includeOutcomeInBudgetRefinement outcomeConstant_hasType
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0
    · exact Tower.IsUniverse.sort outcomeLevel
    · apply Presentation.HasType.piForm
      · apply outcomeApp_hasTypeWith
        · exact includeOutcomeInBudgetRefinement outcomeConstant_hasType
        · exact Presentation.HasType.var 2
        · exact Presentation.HasType.var 1
      · exact Tower.IsUniverse.sort outcomeLevel
      · exact Presentation.HasType.headType
          (Tower.HeadTyping.sort budgetRefinementLevel)
      · exact Tower.IsUniverse.sort (.succ budgetRefinementLevel)
      · exact Tower.Join.sorts outcomeLevel
          (.succ budgetRefinementLevel)
    · exact Tower.IsUniverse.sort
        (.max outcomeLevel (.succ budgetRefinementLevel))
    · exact Tower.Join.sorts outcomeLevel
        (.max outcomeLevel (.succ budgetRefinementLevel))
  · exact Tower.IsUniverse.sort
      (.max outcomeLevel
        (.max outcomeLevel (.succ budgetRefinementLevel)))
  · exact Tower.Join.sorts judgmentLevel
      (.max outcomeLevel
        (.max outcomeLevel (.succ budgetRefinementLevel)))

def budgetRefinementDeclarationLevel : LevelExpr :=
  .max signatureLevel
    (.max judgmentLevel
      (.max outcomeLevel
        (.max outcomeLevel (.succ budgetRefinementLevel))))

theorem budgetRefinementType_hasType :
    BudgetRefinementHasType (.nil : Tower.Ctx 0)
      budgetRefinementType (sortTm budgetRefinementDeclarationLevel) := by
  unfold budgetRefinementType budgetRefinementDeclarationLevel
  apply Presentation.HasType.piForm
      outcomeSignatureType_hasBudgetRefinementType
      (Tower.IsUniverse.sort signatureLevel)
  · exact budgetRefinementBodyType_hasType
  · exact Tower.IsUniverse.sort
      (.max judgmentLevel
        (.max outcomeLevel
          (.max outcomeLevel (.succ budgetRefinementLevel))))
  · exact Tower.Join.sorts signatureLevel
      (.max judgmentLevel
        (.max outcomeLevel
          (.max outcomeLevel (.succ budgetRefinementLevel))))

/-! ### Formation of binary refinement constructors -/

def budgetBinaryContextSJW (beforeFamily : Tower.Tm 1) : Tower.Ctx 3 :=
  .snoc budgetContextSJ
    (.app (Presentation.rename wk beforeFamily) (.var 0))

def budgetBinaryContextSJWW (beforeFamily afterFamily : Tower.Tm 1) :
    Tower.Ctx 4 :=
  .snoc (budgetBinaryContextSJW beforeFamily)
    (.app
      (Presentation.rename wk (Presentation.rename wk afterFamily))
      (.var 1))

def budgetBinaryAfterLevel (afterLevel : LevelExpr) : LevelExpr :=
  .max afterLevel budgetRefinementLevel

def budgetBinaryBeforeLevel (beforeLevel afterLevel : LevelExpr) :
    LevelExpr :=
  .max beforeLevel (budgetBinaryAfterLevel afterLevel)

def budgetBinaryBodyLevel (beforeLevel afterLevel : LevelExpr) :
    LevelExpr :=
  .max judgmentLevel (budgetBinaryBeforeLevel beforeLevel afterLevel)

@[simp] theorem budget_wk_wk_zero :
    wk (wk (0 : Fin 1)) = (2 : Fin 3) := by
  decide

@[simp] theorem budget_wk_wk_wk_zero :
    wk (wk (wk (0 : Fin 1))) = (3 : Fin 4) := by
  decide

@[simp] theorem budget_wk_two :
    wk (2 : Fin 3) = (3 : Fin 4) := by
  decide

theorem budgetBinaryAtSignatureType_hasType
    (beforeLevel afterLevel : LevelExpr)
    {beforeConstructor afterConstructor : DeclName}
    {beforeFamily afterFamily : Tower.Tm 1}
    (beforeFamilyTyping : BudgetRefinementHasType budgetContextS
      beforeFamily
      (familyType beforeLevel (signatureJudgment (.var 0))))
    (afterFamilyTyping : BudgetRefinementHasType budgetContextS
      afterFamily
      (familyType afterLevel (signatureJudgment (.var 0))))
    (resultTyping : BudgetRefinementHasType
      (budgetBinaryContextSJWW beforeFamily afterFamily)
      (budgetRefinementApp (.var 3) (.var 2)
        (namedOutcomeConstructorApp beforeConstructor
          (.var 3) (.var 2) (.var 1))
        (namedOutcomeConstructorApp afterConstructor
          (.var 3) (.var 2) (.var 0)))
      (sortTm budgetRefinementLevel)) :
    BudgetRefinementHasType budgetContextS
      (budgetBinaryAtSignatureType beforeConstructor afterConstructor
        (.var 0) beforeFamily afterFamily)
      (sortTm (budgetBinaryBodyLevel beforeLevel afterLevel)) := by
  unfold budgetBinaryAtSignatureType budgetBinaryBodyLevel
    budgetBinaryBeforeLevel budgetBinaryAfterLevel
  apply Presentation.HasType.piForm
  · exact signatureJudgment_hasType budgetSignatureVar_hasType
  · exact .sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply familyApp_hasType
      · have weakened := beforeFamilyTyping.weaken
          (extension := signatureJudgment (.var 0))
        simpa [budgetContextSJ, familyType, sortTm,
          Presentation.rename] using
          weakened
      · exact Presentation.HasType.var 0
    · exact .sort beforeLevel
    · apply Presentation.HasType.piForm
      · apply familyApp_hasType
        · have first := afterFamilyTyping.weaken
            (extension := signatureJudgment (.var 0))
          have second := first.weaken
            (extension :=
              .app (Presentation.rename wk beforeFamily) (.var 0))
          simpa [budgetBinaryContextSJW, budgetContextSJ, familyType,
            sortTm, Presentation.rename] using second
        · exact Presentation.HasType.var 1
      · exact .sort afterLevel
      · simpa [budgetBinaryContextSJWW, budgetBinaryContextSJW,
          budgetContextSJ, namedOutcomeConstructorApp,
          sortTm, Presentation.rename] using resultTyping
      · exact .sort budgetRefinementLevel
      · exact .sorts afterLevel budgetRefinementLevel
    · exact .sort (budgetBinaryAfterLevel afterLevel)
    · exact .sorts beforeLevel (budgetBinaryAfterLevel afterLevel)
  · exact .sort (budgetBinaryBeforeLevel beforeLevel afterLevel)
  · exact .sorts judgmentLevel
      (budgetBinaryBeforeLevel beforeLevel afterLevel)

theorem budgetEstablishedBodyType_asBinary :
    budgetEstablishedBodyType =
      budgetBinaryAtSignatureType establishedName establishedName
        (.var 0) (signatureEvidence (.var 0))
        (signatureEvidence (.var 0)) := by
  decide

theorem budgetEstablishedBodyType_hasType :
    BudgetRefinementHasType budgetContextS budgetEstablishedBodyType
      (sortTm (budgetBinaryBodyLevel evidenceLevel evidenceLevel)) := by
  rw [budgetEstablishedBodyType_asBinary]
  apply budgetBinaryAtSignatureType_hasType evidenceLevel evidenceLevel
  · exact signatureEvidence_hasType budgetSignatureVar_hasType
  · exact signatureEvidence_hasType budgetSignatureVar_hasType
  · apply budgetRefinementApp_hasType
    · exact Presentation.HasType.var 3
    · exact Presentation.HasType.var 2
    · apply establishedApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply establishedApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0

def budgetEstablishedDeclarationLevel : LevelExpr :=
  .max signatureLevel
    (budgetBinaryBodyLevel evidenceLevel evidenceLevel)

theorem budgetEstablishedType_hasType :
    BudgetRefinementHasType (.nil : Tower.Ctx 0)
      budgetEstablishedType
      (sortTm budgetEstablishedDeclarationLevel) := by
  unfold budgetEstablishedType budgetEstablishedDeclarationLevel
  apply Presentation.HasType.piForm
  · exact outcomeSignatureType_hasBudgetRefinementType
  · exact .sort signatureLevel
  · exact budgetEstablishedBodyType_hasType
  · exact .sort (budgetBinaryBodyLevel evidenceLevel evidenceLevel)
  · exact .sorts signatureLevel
      (budgetBinaryBodyLevel evidenceLevel evidenceLevel)

theorem budgetRefutedBodyType_asBinary :
    budgetRefutedBodyType =
      budgetBinaryAtSignatureType refutedName refutedName
        (.var 0) (signatureObstruction (.var 0))
        (signatureObstruction (.var 0)) := by
  decide

theorem budgetRefutedBodyType_hasType :
    BudgetRefinementHasType budgetContextS budgetRefutedBodyType
      (sortTm (budgetBinaryBodyLevel obstructionLevel obstructionLevel)) := by
  rw [budgetRefutedBodyType_asBinary]
  apply budgetBinaryAtSignatureType_hasType obstructionLevel obstructionLevel
  · exact signatureObstruction_hasType budgetSignatureVar_hasType
  · exact signatureObstruction_hasType budgetSignatureVar_hasType
  · apply budgetRefinementApp_hasType
    · exact Presentation.HasType.var 3
    · exact Presentation.HasType.var 2
    · apply refutedApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply refutedApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0

def budgetRefutedDeclarationLevel : LevelExpr :=
  .max signatureLevel
    (budgetBinaryBodyLevel obstructionLevel obstructionLevel)

theorem budgetRefutedType_hasType :
    BudgetRefinementHasType (.nil : Tower.Ctx 0)
      budgetRefutedType (sortTm budgetRefutedDeclarationLevel) := by
  unfold budgetRefutedType budgetRefutedDeclarationLevel
  apply Presentation.HasType.piForm
  · exact outcomeSignatureType_hasBudgetRefinementType
  · exact .sort signatureLevel
  · exact budgetRefutedBodyType_hasType
  · exact .sort (budgetBinaryBodyLevel obstructionLevel obstructionLevel)
  · exact .sorts signatureLevel
      (budgetBinaryBodyLevel obstructionLevel obstructionLevel)

theorem budgetIncompleteBodyType_asBinary :
    budgetIncompleteBodyType =
      budgetBinaryAtSignatureType incompleteName incompleteName
        (.var 0) (signatureFrontier (.var 0))
        (signatureFrontier (.var 0)) := by
  decide

theorem budgetIncompleteBodyType_hasType :
    BudgetRefinementHasType budgetContextS budgetIncompleteBodyType
      (sortTm (budgetBinaryBodyLevel frontierLevel frontierLevel)) := by
  rw [budgetIncompleteBodyType_asBinary]
  apply budgetBinaryAtSignatureType_hasType frontierLevel frontierLevel
  · exact signatureFrontier_hasType budgetSignatureVar_hasType
  · exact signatureFrontier_hasType budgetSignatureVar_hasType
  · apply budgetRefinementApp_hasType
    · exact Presentation.HasType.var 3
    · exact Presentation.HasType.var 2
    · apply incompleteApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply incompleteApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0

def budgetIncompleteDeclarationLevel : LevelExpr :=
  .max signatureLevel
    (budgetBinaryBodyLevel frontierLevel frontierLevel)

theorem budgetIncompleteType_hasType :
    BudgetRefinementHasType (.nil : Tower.Ctx 0)
      budgetIncompleteType (sortTm budgetIncompleteDeclarationLevel) := by
  unfold budgetIncompleteType budgetIncompleteDeclarationLevel
  apply Presentation.HasType.piForm
  · exact outcomeSignatureType_hasBudgetRefinementType
  · exact .sort signatureLevel
  · exact budgetIncompleteBodyType_hasType
  · exact .sort (budgetBinaryBodyLevel frontierLevel frontierLevel)
  · exact .sorts signatureLevel
      (budgetBinaryBodyLevel frontierLevel frontierLevel)

theorem budgetIncompleteEstablishedBodyType_asBinary :
    budgetIncompleteEstablishedBodyType =
      budgetBinaryAtSignatureType incompleteName establishedName
        (.var 0) (signatureFrontier (.var 0))
        (signatureEvidence (.var 0)) := by
  decide

theorem budgetIncompleteEstablishedBodyType_hasType :
    BudgetRefinementHasType budgetContextS
      budgetIncompleteEstablishedBodyType
      (sortTm (budgetBinaryBodyLevel frontierLevel evidenceLevel)) := by
  rw [budgetIncompleteEstablishedBodyType_asBinary]
  apply budgetBinaryAtSignatureType_hasType frontierLevel evidenceLevel
  · exact signatureFrontier_hasType budgetSignatureVar_hasType
  · exact signatureEvidence_hasType budgetSignatureVar_hasType
  · apply budgetRefinementApp_hasType
    · exact Presentation.HasType.var 3
    · exact Presentation.HasType.var 2
    · apply incompleteApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply establishedApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0

def budgetIncompleteEstablishedDeclarationLevel : LevelExpr :=
  .max signatureLevel
    (budgetBinaryBodyLevel frontierLevel evidenceLevel)

theorem budgetIncompleteEstablishedType_hasType :
    BudgetRefinementHasType (.nil : Tower.Ctx 0)
      budgetIncompleteEstablishedType
      (sortTm budgetIncompleteEstablishedDeclarationLevel) := by
  unfold budgetIncompleteEstablishedType
    budgetIncompleteEstablishedDeclarationLevel
  apply Presentation.HasType.piForm
  · exact outcomeSignatureType_hasBudgetRefinementType
  · exact .sort signatureLevel
  · exact budgetIncompleteEstablishedBodyType_hasType
  · exact .sort (budgetBinaryBodyLevel frontierLevel evidenceLevel)
  · exact .sorts signatureLevel
      (budgetBinaryBodyLevel frontierLevel evidenceLevel)

theorem budgetIncompleteRefutedBodyType_asBinary :
    budgetIncompleteRefutedBodyType =
      budgetBinaryAtSignatureType incompleteName refutedName
        (.var 0) (signatureFrontier (.var 0))
        (signatureObstruction (.var 0)) := by
  decide

theorem budgetIncompleteRefutedBodyType_hasType :
    BudgetRefinementHasType budgetContextS
      budgetIncompleteRefutedBodyType
      (sortTm (budgetBinaryBodyLevel frontierLevel obstructionLevel)) := by
  rw [budgetIncompleteRefutedBodyType_asBinary]
  apply budgetBinaryAtSignatureType_hasType frontierLevel obstructionLevel
  · exact signatureFrontier_hasType budgetSignatureVar_hasType
  · exact signatureObstruction_hasType budgetSignatureVar_hasType
  · apply budgetRefinementApp_hasType
    · exact Presentation.HasType.var 3
    · exact Presentation.HasType.var 2
    · apply incompleteApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply refutedApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0

def budgetIncompleteRefutedDeclarationLevel : LevelExpr :=
  .max signatureLevel
    (budgetBinaryBodyLevel frontierLevel obstructionLevel)

theorem budgetIncompleteRefutedType_hasType :
    BudgetRefinementHasType (.nil : Tower.Ctx 0)
      budgetIncompleteRefutedType
      (sortTm budgetIncompleteRefutedDeclarationLevel) := by
  unfold budgetIncompleteRefutedType
    budgetIncompleteRefutedDeclarationLevel
  apply Presentation.HasType.piForm
  · exact outcomeSignatureType_hasBudgetRefinementType
  · exact .sort signatureLevel
  · exact budgetIncompleteRefutedBodyType_hasType
  · exact .sort (budgetBinaryBodyLevel frontierLevel obstructionLevel)
  · exact .sorts signatureLevel
      (budgetBinaryBodyLevel frontierLevel obstructionLevel)

/-! ### Formation of the unary boundary-preservation constructor -/

def budgetUnaryContextSJW (payloadFamily : Tower.Tm 1) : Tower.Ctx 3 :=
  .snoc budgetContextSJ
    (.app (Presentation.rename wk payloadFamily) (.var 0))

def budgetUnaryWitnessLevel (payloadLevel : LevelExpr) : LevelExpr :=
  .max payloadLevel budgetRefinementLevel

def budgetUnaryBodyLevel (payloadLevel : LevelExpr) : LevelExpr :=
  .max judgmentLevel (budgetUnaryWitnessLevel payloadLevel)

theorem budgetUnaryAtSignatureType_hasType (payloadLevel : LevelExpr)
    {outcomeConstructor : DeclName} {payloadFamily : Tower.Tm 1}
    (payloadFamilyTyping : BudgetRefinementHasType budgetContextS
      payloadFamily
      (familyType payloadLevel (signatureJudgment (.var 0))))
    (resultTyping : BudgetRefinementHasType
      (budgetUnaryContextSJW payloadFamily)
      (budgetRefinementApp (.var 2) (.var 1)
        (namedOutcomeConstructorApp outcomeConstructor
          (.var 2) (.var 1) (.var 0))
        (namedOutcomeConstructorApp outcomeConstructor
          (.var 2) (.var 1) (.var 0)))
      (sortTm budgetRefinementLevel)) :
    BudgetRefinementHasType budgetContextS
      (budgetUnaryAtSignatureType outcomeConstructor (.var 0) payloadFamily)
      (sortTm (budgetUnaryBodyLevel payloadLevel)) := by
  unfold budgetUnaryAtSignatureType budgetUnaryBodyLevel
    budgetUnaryWitnessLevel
  apply Presentation.HasType.piForm
  · exact signatureJudgment_hasType budgetSignatureVar_hasType
  · exact .sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply familyApp_hasType
      · have weakened := payloadFamilyTyping.weaken
          (extension := signatureJudgment (.var 0))
        simpa [budgetContextSJ, familyType, sortTm,
          Presentation.rename] using weakened
      · exact Presentation.HasType.var 0
    · exact .sort payloadLevel
    · simpa [budgetUnaryContextSJW, budgetContextSJ,
        namedOutcomeConstructorApp, sortTm, Presentation.rename] using
        resultTyping
    · exact .sort budgetRefinementLevel
    · exact .sorts payloadLevel budgetRefinementLevel
  · exact .sort (budgetUnaryWitnessLevel payloadLevel)
  · exact .sorts judgmentLevel (budgetUnaryWitnessLevel payloadLevel)

theorem budgetOutsideFragmentBodyType_asUnary :
    budgetOutsideFragmentBodyType =
      budgetUnaryAtSignatureType outsideFragmentName (.var 0)
        (signatureBoundary (.var 0)) := by
  decide

theorem budgetOutsideFragmentBodyType_hasType :
    BudgetRefinementHasType budgetContextS
      budgetOutsideFragmentBodyType
      (sortTm (budgetUnaryBodyLevel boundaryLevel)) := by
  rw [budgetOutsideFragmentBodyType_asUnary]
  apply budgetUnaryAtSignatureType_hasType boundaryLevel
  · exact signatureBoundary_hasType budgetSignatureVar_hasType
  · apply budgetRefinementApp_hasType
    · exact Presentation.HasType.var 2
    · exact Presentation.HasType.var 1
    · apply outsideFragmentApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0
    · apply outsideFragmentApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0

def budgetOutsideFragmentDeclarationLevel : LevelExpr :=
  .max signatureLevel (budgetUnaryBodyLevel boundaryLevel)

theorem budgetOutsideFragmentType_hasType :
    BudgetRefinementHasType (.nil : Tower.Ctx 0)
      budgetOutsideFragmentType
      (sortTm budgetOutsideFragmentDeclarationLevel) := by
  unfold budgetOutsideFragmentType
    budgetOutsideFragmentDeclarationLevel
  apply Presentation.HasType.piForm
  · exact outcomeSignatureType_hasBudgetRefinementType
  · exact .sort signatureLevel
  · exact budgetOutsideFragmentBodyType_hasType
  · exact .sort (budgetUnaryBodyLevel boundaryLevel)
  · exact .sorts signatureLevel (budgetUnaryBodyLevel boundaryLevel)

/-! ### Formation of the dependent motive -/

def budgetRefinementMotiveAtSignatureType (signature : Tower.Tm n) :
    Tower.Tm n :=
  .pi (signatureJudgment signature)
    (.pi (outcomeApp (Presentation.rename wk signature) (.var 0))
      (.pi
        (outcomeApp
          (Presentation.rename wk (Presentation.rename wk signature))
          (.var 1))
        (.pi
          (budgetRefinementApp
            (Presentation.rename wk
              (Presentation.rename wk (Presentation.rename wk signature)))
            (.var 2) (.var 1) (.var 0))
          (sortTm budgetRefinementMotiveLevel))))

theorem budgetRefinementMotiveType_asAtSignature :
    budgetRefinementMotiveType =
      budgetRefinementMotiveAtSignatureType (.var 0) := by
  decide

def budgetRefinementMotiveRelationLevel : LevelExpr :=
  .max budgetRefinementLevel (.succ budgetRefinementMotiveLevel)

def budgetRefinementMotiveAfterLevel : LevelExpr :=
  .max outcomeLevel budgetRefinementMotiveRelationLevel

def budgetRefinementMotiveBeforeLevel : LevelExpr :=
  .max outcomeLevel budgetRefinementMotiveAfterLevel

def budgetRefinementMotiveTypeLevel : LevelExpr :=
  .max judgmentLevel budgetRefinementMotiveBeforeLevel

theorem budgetRefinementMotiveType_hasType :
    BudgetRefinementHasType budgetContextS budgetRefinementMotiveType
      (sortTm budgetRefinementMotiveTypeLevel) := by
  rw [budgetRefinementMotiveType_asAtSignature]
  unfold budgetRefinementMotiveAtSignatureType
    budgetRefinementMotiveTypeLevel budgetRefinementMotiveBeforeLevel
    budgetRefinementMotiveAfterLevel budgetRefinementMotiveRelationLevel
  apply Presentation.HasType.piForm
  · exact signatureJudgment_hasType budgetSignatureVar_hasType
  · exact .sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply outcomeApp_hasTypeWith
      · exact includeOutcomeInBudgetRefinement outcomeConstant_hasType
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0
    · exact .sort outcomeLevel
    · apply Presentation.HasType.piForm
      · apply outcomeApp_hasTypeWith
        · exact includeOutcomeInBudgetRefinement outcomeConstant_hasType
        · exact Presentation.HasType.var 2
        · exact Presentation.HasType.var 1
      · exact .sort outcomeLevel
      · apply Presentation.HasType.piForm
        · apply budgetRefinementApp_hasType
          · exact Presentation.HasType.var 3
          · exact Presentation.HasType.var 2
          · exact Presentation.HasType.var 1
          · exact Presentation.HasType.var 0
        · exact .sort budgetRefinementLevel
        · exact .headType (.sort budgetRefinementMotiveLevel)
        · exact .sort (.succ budgetRefinementMotiveLevel)
        · exact .sorts budgetRefinementLevel
            (.succ budgetRefinementMotiveLevel)
      · exact .sort budgetRefinementMotiveRelationLevel
      · exact .sorts outcomeLevel budgetRefinementMotiveRelationLevel
    · exact .sort budgetRefinementMotiveAfterLevel
    · exact .sorts outcomeLevel budgetRefinementMotiveAfterLevel
  · exact .sort budgetRefinementMotiveBeforeLevel
  · exact .sorts judgmentLevel budgetRefinementMotiveBeforeLevel

def budgetRefinementMotiveAfterJudgmentType
    (signature judgment : Tower.Tm n) : Tower.Tm n :=
  .pi (outcomeApp signature judgment)
    (.pi
      (outcomeApp (Presentation.rename wk signature)
        (Presentation.rename wk judgment))
      (.pi
        (budgetRefinementApp
          (Presentation.rename wk (Presentation.rename wk signature))
          (Presentation.rename wk (Presentation.rename wk judgment))
          (.var 1) (.var 0))
        (sortTm budgetRefinementMotiveLevel)))

def budgetRefinementMotiveAfterBeforeType
    (signature judgment before : Tower.Tm n) : Tower.Tm n :=
  .pi (outcomeApp signature judgment)
    (.pi
      (budgetRefinementApp (Presentation.rename wk signature)
        (Presentation.rename wk judgment)
        (Presentation.rename wk before) (.var 0))
      (sortTm budgetRefinementMotiveLevel))

def budgetRefinementMotiveAfterAfterType
    (signature judgment before after : Tower.Tm n) : Tower.Tm n :=
  .pi (budgetRefinementApp signature judgment before after)
    (sortTm budgetRefinementMotiveLevel)

theorem budgetRefinementMotiveApp_hasType {context : Tower.Ctx n}
    {signature motive judgment before after refinement : Tower.Tm n}
    (motiveTyping : BudgetRefinementHasType context motive
      (budgetRefinementMotiveAtSignatureType signature))
    (judgmentTyping : BudgetRefinementHasType context judgment
      (signatureJudgment signature))
    (beforeTyping : BudgetRefinementHasType context before
      (outcomeApp signature judgment))
    (afterTyping : BudgetRefinementHasType context after
      (outcomeApp signature judgment))
    (refinementTyping : BudgetRefinementHasType context refinement
      (budgetRefinementApp signature judgment before after)) :
    BudgetRefinementHasType context
      (.app (.app (.app (.app motive judgment) before) after) refinement)
      (sortTm budgetRefinementMotiveLevel) := by
  have afterJudgment := Presentation.HasType.appElim motiveTyping
    judgmentTyping
  have afterJudgmentNormalized :
      BudgetRefinementHasType context (.app motive judgment)
        (budgetRefinementMotiveAfterJudgmentType signature judgment) := by
    convert afterJudgment using 1
    all_goals simp [budgetRefinementMotiveAfterJudgmentType,
      budgetRefinementApp,
      Presentation.inst0, Presentation.subst]
  have afterBefore := Presentation.HasType.appElim afterJudgmentNormalized
    beforeTyping
  have afterBeforeNormalized :
      BudgetRefinementHasType context
        (.app (.app motive judgment) before)
        (budgetRefinementMotiveAfterBeforeType signature judgment before) := by
    convert afterBefore using 1
    all_goals simp [budgetRefinementMotiveAfterBeforeType,
      budgetRefinementApp,
      Presentation.inst0, Presentation.subst]
  have afterAfter := Presentation.HasType.appElim afterBeforeNormalized
    afterTyping
  have afterAfterNormalized :
      BudgetRefinementHasType context
        (.app (.app (.app motive judgment) before) after)
        (budgetRefinementMotiveAfterAfterType signature judgment before
          after) := by
    convert afterAfter using 1
    all_goals simp [budgetRefinementMotiveAfterAfterType,
      budgetRefinementApp,
      Presentation.inst0, Presentation.subst]
  have result := Presentation.HasType.appElim afterAfterNormalized
    refinementTyping
  simpa [budgetRefinementMotiveAfterAfterType, sortTm,
    Presentation.inst0, Presentation.subst] using result

/-! ### Formation of the dependent branches -/

def budgetContextSM : Tower.Ctx 2 :=
  .snoc budgetContextS budgetRefinementMotiveType

def budgetContextSMJ : Tower.Ctx 3 :=
  .snoc budgetContextSM (signatureJudgment (.var 1))

def budgetBinaryCaseContextSMJW (beforeFamily : Tower.Tm 2) :
    Tower.Ctx 4 :=
  .snoc budgetContextSMJ
    (.app (Presentation.rename wk beforeFamily) (.var 0))

def budgetBinaryCaseContextSMJWW
    (beforeFamily afterFamily : Tower.Tm 2) : Tower.Ctx 5 :=
  .snoc (budgetBinaryCaseContextSMJW beforeFamily)
    (.app
      (Presentation.rename wk (Presentation.rename wk afterFamily))
      (.var 1))

theorem budgetSignatureVarInSM_hasType :
    BudgetRefinementHasType budgetContextSM (.var 1)
      (liftClosed outcomeSignatureType) := by
  have variableTyping :=
    (Presentation.HasType.var (R := budgetRefinementRules)
      (Γ := budgetContextSM) (1 : Fin 2))
  have lookupEquality :
      Presentation.Ctx.lookup budgetContextSM (1 : Fin 2) =
        liftClosed outcomeSignatureType := by
    decide
  simpa only [lookupEquality] using variableTyping

theorem budgetMotiveVarInSM_hasType :
    BudgetRefinementHasType budgetContextSM (.var 0)
      (budgetRefinementMotiveAtSignatureType (.var 1)) := by
  have variableTyping :=
    (Presentation.HasType.var (R := budgetRefinementRules)
      (Γ := budgetContextSM) (0 : Fin 2))
  have lookupEquality :
      Presentation.Ctx.lookup budgetContextSM (0 : Fin 2) =
        budgetRefinementMotiveAtSignatureType (.var 1) := by
    decide
  simpa only [lookupEquality] using variableTyping

def budgetBinaryCaseAtSignatureType
    (relationConstructor beforeConstructor afterConstructor : DeclName)
    (beforeFamily afterFamily : Tower.Tm 2) : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (.app (Presentation.rename wk beforeFamily) (.var 0))
      (.pi
        (.app
          (Presentation.rename wk (Presentation.rename wk afterFamily))
          (.var 1))
        (.app
          (.app
            (.app
              (.app (.var 3) (.var 2))
              (namedOutcomeConstructorApp beforeConstructor
                (.var 4) (.var 2) (.var 1)))
            (namedOutcomeConstructorApp afterConstructor
              (.var 4) (.var 2) (.var 0)))
          (namedBudgetBinaryConstructorApp relationConstructor
            (.var 4) (.var 2) (.var 1) (.var 0)))))

def budgetBinaryCaseAfterLevel (afterLevel : LevelExpr) : LevelExpr :=
  .max afterLevel budgetRefinementMotiveLevel

def budgetBinaryCaseBeforeLevel
    (beforeLevel afterLevel : LevelExpr) : LevelExpr :=
  .max beforeLevel (budgetBinaryCaseAfterLevel afterLevel)

def budgetBinaryCaseLevel
    (beforeLevel afterLevel : LevelExpr) : LevelExpr :=
  .max judgmentLevel (budgetBinaryCaseBeforeLevel beforeLevel afterLevel)

theorem budgetBinaryCaseAtSignatureType_hasType
    (beforeLevel afterLevel : LevelExpr)
    {relationConstructor beforeConstructor afterConstructor : DeclName}
    {beforeFamily afterFamily : Tower.Tm 2}
    (beforeFamilyTyping : BudgetRefinementHasType budgetContextSM
      beforeFamily
      (familyType beforeLevel (signatureJudgment (.var 1))))
    (afterFamilyTyping : BudgetRefinementHasType budgetContextSM
      afterFamily
      (familyType afterLevel (signatureJudgment (.var 1))))
    (resultTyping : BudgetRefinementHasType
      (budgetBinaryCaseContextSMJWW beforeFamily afterFamily)
      (.app
        (.app
          (.app
            (.app (.var 3) (.var 2))
            (namedOutcomeConstructorApp beforeConstructor
              (.var 4) (.var 2) (.var 1)))
          (namedOutcomeConstructorApp afterConstructor
            (.var 4) (.var 2) (.var 0)))
        (namedBudgetBinaryConstructorApp relationConstructor
          (.var 4) (.var 2) (.var 1) (.var 0)))
      (sortTm budgetRefinementMotiveLevel)) :
    BudgetRefinementHasType budgetContextSM
      (budgetBinaryCaseAtSignatureType relationConstructor beforeConstructor
        afterConstructor beforeFamily afterFamily)
      (sortTm (budgetBinaryCaseLevel beforeLevel afterLevel)) := by
  unfold budgetBinaryCaseAtSignatureType budgetBinaryCaseLevel
    budgetBinaryCaseBeforeLevel budgetBinaryCaseAfterLevel
  apply Presentation.HasType.piForm
  · exact signatureJudgment_hasType budgetSignatureVarInSM_hasType
  · exact .sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply familyApp_hasType
      · have weakened := beforeFamilyTyping.weaken
          (extension := signatureJudgment (.var 1))
        simpa [budgetContextSMJ, familyType, sortTm,
          Presentation.rename] using weakened
      · exact Presentation.HasType.var 0
    · exact .sort beforeLevel
    · apply Presentation.HasType.piForm
      · apply familyApp_hasType
        · have first := afterFamilyTyping.weaken
            (extension := signatureJudgment (.var 1))
          have second := first.weaken
            (extension :=
              .app (Presentation.rename wk beforeFamily) (.var 0))
          simpa [budgetBinaryCaseContextSMJW, budgetContextSMJ,
            familyType, sortTm, Presentation.rename] using second
        · exact Presentation.HasType.var 1
      · exact .sort afterLevel
      · simpa [budgetBinaryCaseContextSMJWW,
          budgetBinaryCaseContextSMJW, budgetContextSMJ, sortTm,
          Presentation.rename] using resultTyping
      · exact .sort budgetRefinementMotiveLevel
      · exact .sorts afterLevel budgetRefinementMotiveLevel
    · exact .sort (budgetBinaryCaseAfterLevel afterLevel)
    · exact .sorts beforeLevel (budgetBinaryCaseAfterLevel afterLevel)
  · exact .sort (budgetBinaryCaseBeforeLevel beforeLevel afterLevel)
  · exact .sorts judgmentLevel
      (budgetBinaryCaseBeforeLevel beforeLevel afterLevel)

theorem budgetRefinementMotiveAtSignature_afterThreeWeakenings :
    Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk
            (budgetRefinementMotiveAtSignatureType
              (.var 1 : Tower.Tm 2)))) =
      budgetRefinementMotiveAtSignatureType (.var 4 : Tower.Tm 5) := by
  decide

theorem budgetMotiveVarInBinaryCase_hasType
    (beforeFamily afterFamily : Tower.Tm 2) :
    BudgetRefinementHasType
      (budgetBinaryCaseContextSMJWW beforeFamily afterFamily) (.var 3)
      (budgetRefinementMotiveAtSignatureType (.var 4)) := by
  have afterJudgment := budgetMotiveVarInSM_hasType.weaken
    (extension := signatureJudgment (.var 1))
  have afterBefore := afterJudgment.weaken
    (extension := .app (Presentation.rename wk beforeFamily) (.var 0))
  have afterAfter := afterBefore.weaken
    (extension :=
      .app (Presentation.rename wk (Presentation.rename wk afterFamily))
        (.var 1))
  rw [budgetRefinementMotiveAtSignature_afterThreeWeakenings] at afterAfter
  simpa [budgetBinaryCaseContextSMJWW,
    budgetBinaryCaseContextSMJW, budgetContextSMJ,
    Presentation.rename, wk] using afterAfter

theorem budgetEstablishedCaseType_asGeneric :
    budgetEstablishedCaseType =
      budgetBinaryCaseAtSignatureType budgetEstablishedName
        establishedName establishedName
        (signatureEvidence (.var 1)) (signatureEvidence (.var 1)) := by
  decide

theorem budgetEstablishedCaseType_hasType :
    BudgetRefinementHasType budgetContextSM budgetEstablishedCaseType
      (sortTm (budgetBinaryCaseLevel evidenceLevel evidenceLevel)) := by
  rw [budgetEstablishedCaseType_asGeneric]
  apply budgetBinaryCaseAtSignatureType_hasType evidenceLevel evidenceLevel
  · exact signatureEvidence_hasType budgetSignatureVarInSM_hasType
  · exact signatureEvidence_hasType budgetSignatureVarInSM_hasType
  · apply budgetRefinementMotiveApp_hasType
      (signature := (.var 4)) (motive := (.var 3))
      (judgment := (.var 2))
    · exact budgetMotiveVarInBinaryCase_hasType _ _
    · exact Presentation.HasType.var 2
    · apply establishedApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply establishedApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0
    · apply budgetEstablishedApp_hasType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0

theorem budgetRefutedCaseType_asGeneric :
    budgetRefutedCaseType =
      budgetBinaryCaseAtSignatureType budgetRefutedName
        refutedName refutedName
        (signatureObstruction (.var 1))
        (signatureObstruction (.var 1)) := by
  decide

theorem budgetRefutedCaseType_hasType :
    BudgetRefinementHasType budgetContextSM budgetRefutedCaseType
      (sortTm
        (budgetBinaryCaseLevel obstructionLevel obstructionLevel)) := by
  rw [budgetRefutedCaseType_asGeneric]
  apply budgetBinaryCaseAtSignatureType_hasType obstructionLevel
    obstructionLevel
  · exact signatureObstruction_hasType budgetSignatureVarInSM_hasType
  · exact signatureObstruction_hasType budgetSignatureVarInSM_hasType
  · apply budgetRefinementMotiveApp_hasType
      (signature := (.var 4)) (motive := (.var 3))
      (judgment := (.var 2))
    · exact budgetMotiveVarInBinaryCase_hasType _ _
    · exact Presentation.HasType.var 2
    · apply refutedApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply refutedApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0
    · apply budgetRefutedApp_hasType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0

theorem budgetIncompleteCaseType_asGeneric :
    budgetIncompleteCaseType =
      budgetBinaryCaseAtSignatureType budgetIncompleteName
        incompleteName incompleteName
        (signatureFrontier (.var 1))
        (signatureFrontier (.var 1)) := by
  decide

theorem budgetIncompleteCaseType_hasType :
    BudgetRefinementHasType budgetContextSM budgetIncompleteCaseType
      (sortTm (budgetBinaryCaseLevel frontierLevel frontierLevel)) := by
  rw [budgetIncompleteCaseType_asGeneric]
  apply budgetBinaryCaseAtSignatureType_hasType frontierLevel frontierLevel
  · exact signatureFrontier_hasType budgetSignatureVarInSM_hasType
  · exact signatureFrontier_hasType budgetSignatureVarInSM_hasType
  · apply budgetRefinementMotiveApp_hasType
      (signature := (.var 4)) (motive := (.var 3))
      (judgment := (.var 2))
    · exact budgetMotiveVarInBinaryCase_hasType _ _
    · exact Presentation.HasType.var 2
    · apply incompleteApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply incompleteApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0
    · apply budgetIncompleteApp_hasType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0

theorem budgetIncompleteEstablishedCaseType_asGeneric :
    budgetIncompleteEstablishedCaseType =
      budgetBinaryCaseAtSignatureType budgetIncompleteEstablishedName
        incompleteName establishedName
        (signatureFrontier (.var 1))
        (signatureEvidence (.var 1)) := by
  decide

theorem budgetIncompleteEstablishedCaseType_hasType :
    BudgetRefinementHasType budgetContextSM
      budgetIncompleteEstablishedCaseType
      (sortTm (budgetBinaryCaseLevel frontierLevel evidenceLevel)) := by
  rw [budgetIncompleteEstablishedCaseType_asGeneric]
  apply budgetBinaryCaseAtSignatureType_hasType frontierLevel evidenceLevel
  · exact signatureFrontier_hasType budgetSignatureVarInSM_hasType
  · exact signatureEvidence_hasType budgetSignatureVarInSM_hasType
  · apply budgetRefinementMotiveApp_hasType
      (signature := (.var 4)) (motive := (.var 3))
      (judgment := (.var 2))
    · exact budgetMotiveVarInBinaryCase_hasType _ _
    · exact Presentation.HasType.var 2
    · apply incompleteApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply establishedApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0
    · apply budgetIncompleteEstablishedApp_hasType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0

theorem budgetIncompleteRefutedCaseType_asGeneric :
    budgetIncompleteRefutedCaseType =
      budgetBinaryCaseAtSignatureType budgetIncompleteRefutedName
        incompleteName refutedName
        (signatureFrontier (.var 1))
        (signatureObstruction (.var 1)) := by
  decide

theorem budgetIncompleteRefutedCaseType_hasType :
    BudgetRefinementHasType budgetContextSM
      budgetIncompleteRefutedCaseType
      (sortTm (budgetBinaryCaseLevel frontierLevel obstructionLevel)) := by
  rw [budgetIncompleteRefutedCaseType_asGeneric]
  apply budgetBinaryCaseAtSignatureType_hasType frontierLevel
    obstructionLevel
  · exact signatureFrontier_hasType budgetSignatureVarInSM_hasType
  · exact signatureObstruction_hasType budgetSignatureVarInSM_hasType
  · apply budgetRefinementMotiveApp_hasType
      (signature := (.var 4)) (motive := (.var 3))
      (judgment := (.var 2))
    · exact budgetMotiveVarInBinaryCase_hasType _ _
    · exact Presentation.HasType.var 2
    · apply incompleteApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply refutedApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0
    · apply budgetIncompleteRefutedApp_hasType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0

def budgetUnaryCaseContextSMJW (payloadFamily : Tower.Tm 2) :
    Tower.Ctx 4 :=
  .snoc budgetContextSMJ
    (.app (Presentation.rename wk payloadFamily) (.var 0))

def budgetUnaryCaseAtSignatureType
    (relationConstructor outcomeConstructor : DeclName)
    (payloadFamily : Tower.Tm 2) : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (.app (Presentation.rename wk payloadFamily) (.var 0))
      (.app
        (.app
          (.app
            (.app (.var 2) (.var 1))
            (namedOutcomeConstructorApp outcomeConstructor
              (.var 3) (.var 1) (.var 0)))
          (namedOutcomeConstructorApp outcomeConstructor
            (.var 3) (.var 1) (.var 0)))
        (namedBudgetUnaryConstructorApp relationConstructor
          (.var 3) (.var 1) (.var 0))))

def budgetUnaryCaseWitnessLevel (payloadLevel : LevelExpr) : LevelExpr :=
  .max payloadLevel budgetRefinementMotiveLevel

def budgetUnaryCaseLevel (payloadLevel : LevelExpr) : LevelExpr :=
  .max judgmentLevel (budgetUnaryCaseWitnessLevel payloadLevel)

theorem budgetUnaryCaseAtSignatureType_hasType (payloadLevel : LevelExpr)
    {relationConstructor outcomeConstructor : DeclName}
    {payloadFamily : Tower.Tm 2}
    (payloadFamilyTyping : BudgetRefinementHasType budgetContextSM
      payloadFamily
      (familyType payloadLevel (signatureJudgment (.var 1))))
    (resultTyping : BudgetRefinementHasType
      (budgetUnaryCaseContextSMJW payloadFamily)
      (.app
        (.app
          (.app
            (.app (.var 2) (.var 1))
            (namedOutcomeConstructorApp outcomeConstructor
              (.var 3) (.var 1) (.var 0)))
          (namedOutcomeConstructorApp outcomeConstructor
            (.var 3) (.var 1) (.var 0)))
        (namedBudgetUnaryConstructorApp relationConstructor
          (.var 3) (.var 1) (.var 0)))
      (sortTm budgetRefinementMotiveLevel)) :
    BudgetRefinementHasType budgetContextSM
      (budgetUnaryCaseAtSignatureType relationConstructor
        outcomeConstructor payloadFamily)
      (sortTm (budgetUnaryCaseLevel payloadLevel)) := by
  unfold budgetUnaryCaseAtSignatureType budgetUnaryCaseLevel
    budgetUnaryCaseWitnessLevel
  apply Presentation.HasType.piForm
  · exact signatureJudgment_hasType budgetSignatureVarInSM_hasType
  · exact .sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply familyApp_hasType
      · have weakened := payloadFamilyTyping.weaken
          (extension := signatureJudgment (.var 1))
        simpa [budgetContextSMJ, familyType, sortTm,
          Presentation.rename] using weakened
      · exact Presentation.HasType.var 0
    · exact .sort payloadLevel
    · simpa [budgetUnaryCaseContextSMJW, budgetContextSMJ, sortTm,
        Presentation.rename] using resultTyping
    · exact .sort budgetRefinementMotiveLevel
    · exact .sorts payloadLevel budgetRefinementMotiveLevel
  · exact .sort (budgetUnaryCaseWitnessLevel payloadLevel)
  · exact .sorts judgmentLevel
      (budgetUnaryCaseWitnessLevel payloadLevel)

theorem budgetRefinementMotiveAtSignature_afterTwoWeakenings :
    Presentation.rename wk
        (Presentation.rename wk
          (budgetRefinementMotiveAtSignatureType
            (.var 1 : Tower.Tm 2))) =
      budgetRefinementMotiveAtSignatureType (.var 3 : Tower.Tm 4) := by
  decide

theorem budgetMotiveVarInUnaryCase_hasType (payloadFamily : Tower.Tm 2) :
    BudgetRefinementHasType
      (budgetUnaryCaseContextSMJW payloadFamily) (.var 2)
      (budgetRefinementMotiveAtSignatureType (.var 3)) := by
  have afterJudgment := budgetMotiveVarInSM_hasType.weaken
    (extension := signatureJudgment (.var 1))
  have afterWitness := afterJudgment.weaken
    (extension := .app (Presentation.rename wk payloadFamily) (.var 0))
  rw [budgetRefinementMotiveAtSignature_afterTwoWeakenings] at afterWitness
  simpa [budgetUnaryCaseContextSMJW, budgetContextSMJ,
    Presentation.rename, wk] using afterWitness

theorem budgetOutsideFragmentCaseType_asGeneric :
    budgetOutsideFragmentCaseType =
      budgetUnaryCaseAtSignatureType budgetOutsideFragmentName
        outsideFragmentName (signatureBoundary (.var 1)) := by
  decide

theorem budgetOutsideFragmentCaseType_hasType :
    BudgetRefinementHasType budgetContextSM
      budgetOutsideFragmentCaseType
      (sortTm (budgetUnaryCaseLevel boundaryLevel)) := by
  rw [budgetOutsideFragmentCaseType_asGeneric]
  apply budgetUnaryCaseAtSignatureType_hasType boundaryLevel
  · exact signatureBoundary_hasType budgetSignatureVarInSM_hasType
  · apply budgetRefinementMotiveApp_hasType
      (signature := (.var 3)) (motive := (.var 2))
      (judgment := (.var 1))
    · exact budgetMotiveVarInUnaryCase_hasType _
    · exact Presentation.HasType.var 1
    · apply outsideFragmentApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0
    · apply outsideFragmentApp_hasBudgetRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0
    · apply budgetOutsideFragmentApp_hasType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0

/-! ### Formation of the eliminator result -/

def budgetContextSMJB : Tower.Ctx 4 :=
  .snoc budgetContextSMJ (outcomeApp (.var 2) (.var 0))

def budgetContextSMJBA : Tower.Ctx 5 :=
  .snoc budgetContextSMJB (outcomeApp (.var 3) (.var 1))

def budgetContextSMJBAR : Tower.Ctx 6 :=
  .snoc budgetContextSMJBA
    (budgetRefinementApp (.var 4) (.var 2) (.var 1) (.var 0))

def budgetRefinementEliminateRelationLevel : LevelExpr :=
  .max budgetRefinementLevel budgetRefinementMotiveLevel

def budgetRefinementEliminateAfterLevel : LevelExpr :=
  .max outcomeLevel budgetRefinementEliminateRelationLevel

def budgetRefinementEliminateBeforeLevel : LevelExpr :=
  .max outcomeLevel budgetRefinementEliminateAfterLevel

def budgetRefinementEliminateResultLevel : LevelExpr :=
  .max judgmentLevel budgetRefinementEliminateBeforeLevel

theorem budgetRefinementMotiveAtSignature_afterFourWeakenings :
    Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk
            (Presentation.rename wk
              (budgetRefinementMotiveAtSignatureType
                (.var 1 : Tower.Tm 2))))) =
      budgetRefinementMotiveAtSignatureType (.var 5 : Tower.Tm 6) := by
  decide

theorem budgetMotiveVarInEliminateResult_hasType :
    BudgetRefinementHasType budgetContextSMJBAR (.var 4)
      (budgetRefinementMotiveAtSignatureType (.var 5)) := by
  have afterJudgment := budgetMotiveVarInSM_hasType.weaken
    (extension := signatureJudgment (.var 1))
  have afterBefore := afterJudgment.weaken
    (extension := outcomeApp (.var 2) (.var 0))
  have afterAfter := afterBefore.weaken
    (extension := outcomeApp (.var 3) (.var 1))
  have afterRefinement := afterAfter.weaken
    (extension := budgetRefinementApp (.var 4) (.var 2) (.var 1) (.var 0))
  rw [budgetRefinementMotiveAtSignature_afterFourWeakenings] at afterRefinement
  simpa [budgetContextSMJBAR, budgetContextSMJBA, budgetContextSMJB,
    budgetContextSMJ, Presentation.rename, wk] using afterRefinement

theorem budgetRefinementEliminateResultType_hasType :
    BudgetRefinementHasType budgetContextSM
      budgetRefinementEliminateResultType
      (sortTm budgetRefinementEliminateResultLevel) := by
  unfold budgetRefinementEliminateResultType
    budgetRefinementEliminateResultLevel
    budgetRefinementEliminateBeforeLevel
    budgetRefinementEliminateAfterLevel
    budgetRefinementEliminateRelationLevel
  apply Presentation.HasType.piForm
  · exact signatureJudgment_hasType budgetSignatureVarInSM_hasType
  · exact .sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply outcomeApp_hasTypeWith
      · exact includeOutcomeInBudgetRefinement outcomeConstant_hasType
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0
    · exact .sort outcomeLevel
    · apply Presentation.HasType.piForm
      · apply outcomeApp_hasTypeWith
        · exact includeOutcomeInBudgetRefinement outcomeConstant_hasType
        · exact Presentation.HasType.var 3
        · exact Presentation.HasType.var 1
      · exact .sort outcomeLevel
      · apply Presentation.HasType.piForm
        · apply budgetRefinementApp_hasType
          · exact Presentation.HasType.var 4
          · exact Presentation.HasType.var 2
          · exact Presentation.HasType.var 1
          · exact Presentation.HasType.var 0
        · exact .sort budgetRefinementLevel
        · apply budgetRefinementMotiveApp_hasType
            (signature := (.var 5)) (motive := (.var 4))
            (judgment := (.var 3)) (before := (.var 2))
            (after := (.var 1)) (refinement := (.var 0))
          · exact budgetMotiveVarInEliminateResult_hasType
          · exact Presentation.HasType.var 3
          · exact Presentation.HasType.var 2
          · exact Presentation.HasType.var 1
          · exact Presentation.HasType.var 0
        · exact .sort budgetRefinementMotiveLevel
        · exact .sorts budgetRefinementLevel
            budgetRefinementMotiveLevel
      · exact .sort budgetRefinementEliminateRelationLevel
      · exact .sorts outcomeLevel
          budgetRefinementEliminateRelationLevel
    · exact .sort budgetRefinementEliminateAfterLevel
    · exact .sorts outcomeLevel budgetRefinementEliminateAfterLevel
  · exact .sort budgetRefinementEliminateBeforeLevel
  · exact .sorts judgmentLevel budgetRefinementEliminateBeforeLevel

/-! ### Formation of the complete eliminator declaration -/

def budgetEliminatorContextEstablished : Tower.Ctx 3 :=
  .snoc budgetContextSM budgetEstablishedCaseType

def budgetEliminatorContextRefuted : Tower.Ctx 4 :=
  .snoc budgetEliminatorContextEstablished
    budgetRefutedCaseAfterEstablished

def budgetEliminatorContextOutside : Tower.Ctx 5 :=
  .snoc budgetEliminatorContextRefuted budgetOutsideCaseAfterTwo

def budgetEliminatorContextIncomplete : Tower.Ctx 6 :=
  .snoc budgetEliminatorContextOutside budgetIncompleteCaseAfterThree

def budgetEliminatorContextIncompleteEstablished : Tower.Ctx 7 :=
  .snoc budgetEliminatorContextIncomplete
    budgetIncompleteEstablishedCaseAfterFour

def budgetEliminatorContextIncompleteRefuted : Tower.Ctx 8 :=
  .snoc budgetEliminatorContextIncompleteEstablished
    budgetIncompleteRefutedCaseAfterFive

theorem budgetRefutedCaseAfterEstablished_hasType :
    BudgetRefinementHasType budgetEliminatorContextEstablished
      budgetRefutedCaseAfterEstablished
      (sortTm
        (budgetBinaryCaseLevel obstructionLevel obstructionLevel)) := by
  simpa [budgetEliminatorContextEstablished,
    budgetRefutedCaseAfterEstablished, sortTm, Presentation.rename] using
    budgetRefutedCaseType_hasType.weaken
      (extension := budgetEstablishedCaseType)

theorem budgetOutsideCaseAfterTwo_hasType :
    BudgetRefinementHasType budgetEliminatorContextRefuted
      budgetOutsideCaseAfterTwo
      (sortTm (budgetUnaryCaseLevel boundaryLevel)) := by
  have first := budgetOutsideFragmentCaseType_hasType.weaken
    (extension := budgetEstablishedCaseType)
  have second := first.weaken
    (extension := budgetRefutedCaseAfterEstablished)
  simpa [budgetEliminatorContextEstablished,
    budgetEliminatorContextRefuted, budgetOutsideCaseAfterTwo,
    sortTm, Presentation.rename] using second

theorem budgetIncompleteCaseAfterThree_hasType :
    BudgetRefinementHasType budgetEliminatorContextOutside
      budgetIncompleteCaseAfterThree
      (sortTm (budgetBinaryCaseLevel frontierLevel frontierLevel)) := by
  have first := budgetIncompleteCaseType_hasType.weaken
    (extension := budgetEstablishedCaseType)
  have second := first.weaken
    (extension := budgetRefutedCaseAfterEstablished)
  have third := second.weaken
    (extension := budgetOutsideCaseAfterTwo)
  simpa [budgetEliminatorContextEstablished,
    budgetEliminatorContextRefuted, budgetEliminatorContextOutside,
    budgetIncompleteCaseAfterThree, sortTm, Presentation.rename] using third

theorem budgetIncompleteEstablishedCaseAfterFour_hasType :
    BudgetRefinementHasType budgetEliminatorContextIncomplete
      budgetIncompleteEstablishedCaseAfterFour
      (sortTm (budgetBinaryCaseLevel frontierLevel evidenceLevel)) := by
  have first := budgetIncompleteEstablishedCaseType_hasType.weaken
    (extension := budgetEstablishedCaseType)
  have second := first.weaken
    (extension := budgetRefutedCaseAfterEstablished)
  have third := second.weaken
    (extension := budgetOutsideCaseAfterTwo)
  have fourth := third.weaken
    (extension := budgetIncompleteCaseAfterThree)
  simpa [budgetEliminatorContextEstablished,
    budgetEliminatorContextRefuted, budgetEliminatorContextOutside,
    budgetEliminatorContextIncomplete,
    budgetIncompleteEstablishedCaseAfterFour, sortTm,
    Presentation.rename] using fourth

theorem budgetIncompleteRefutedCaseAfterFive_hasType :
    BudgetRefinementHasType
      budgetEliminatorContextIncompleteEstablished
      budgetIncompleteRefutedCaseAfterFive
      (sortTm
        (budgetBinaryCaseLevel frontierLevel obstructionLevel)) := by
  have first := budgetIncompleteRefutedCaseType_hasType.weaken
    (extension := budgetEstablishedCaseType)
  have second := first.weaken
    (extension := budgetRefutedCaseAfterEstablished)
  have third := second.weaken
    (extension := budgetOutsideCaseAfterTwo)
  have fourth := third.weaken
    (extension := budgetIncompleteCaseAfterThree)
  have fifth := fourth.weaken
    (extension := budgetIncompleteEstablishedCaseAfterFour)
  simpa [budgetEliminatorContextEstablished,
    budgetEliminatorContextRefuted, budgetEliminatorContextOutside,
    budgetEliminatorContextIncomplete,
    budgetEliminatorContextIncompleteEstablished,
    budgetIncompleteRefutedCaseAfterFive, sortTm,
    Presentation.rename] using fifth

theorem budgetRefinementResultAfterSix_hasType :
    BudgetRefinementHasType
      budgetEliminatorContextIncompleteRefuted
      budgetRefinementResultAfterSix
      (sortTm budgetRefinementEliminateResultLevel) := by
  have first := budgetRefinementEliminateResultType_hasType.weaken
    (extension := budgetEstablishedCaseType)
  have second := first.weaken
    (extension := budgetRefutedCaseAfterEstablished)
  have third := second.weaken
    (extension := budgetOutsideCaseAfterTwo)
  have fourth := third.weaken
    (extension := budgetIncompleteCaseAfterThree)
  have fifth := fourth.weaken
    (extension := budgetIncompleteEstablishedCaseAfterFour)
  have sixth := fifth.weaken
    (extension := budgetIncompleteRefutedCaseAfterFive)
  simpa [budgetEliminatorContextEstablished,
    budgetEliminatorContextRefuted, budgetEliminatorContextOutside,
    budgetEliminatorContextIncomplete,
    budgetEliminatorContextIncompleteEstablished,
    budgetEliminatorContextIncompleteRefuted,
    budgetRefinementResultAfterSix, sortTm,
    Presentation.rename] using sixth

def budgetAfterIncompleteRefutedLevel : LevelExpr :=
  .max (budgetBinaryCaseLevel frontierLevel obstructionLevel)
    budgetRefinementEliminateResultLevel

def budgetAfterIncompleteEstablishedLevel : LevelExpr :=
  .max (budgetBinaryCaseLevel frontierLevel evidenceLevel)
    budgetAfterIncompleteRefutedLevel

def budgetAfterIncompleteLevel : LevelExpr :=
  .max (budgetBinaryCaseLevel frontierLevel frontierLevel)
    budgetAfterIncompleteEstablishedLevel

def budgetAfterOutsideLevel : LevelExpr :=
  .max (budgetUnaryCaseLevel boundaryLevel) budgetAfterIncompleteLevel

def budgetAfterRefutedLevel : LevelExpr :=
  .max (budgetBinaryCaseLevel obstructionLevel obstructionLevel)
    budgetAfterOutsideLevel

def budgetAfterEstablishedLevel : LevelExpr :=
  .max (budgetBinaryCaseLevel evidenceLevel evidenceLevel)
    budgetAfterRefutedLevel

def budgetRefinementEliminateBodyLevel : LevelExpr :=
  .max budgetRefinementMotiveTypeLevel budgetAfterEstablishedLevel

def budgetRefinementEliminateDeclarationLevel : LevelExpr :=
  .max signatureLevel budgetRefinementEliminateBodyLevel

theorem budgetRefinementEliminateBodyType_hasType :
    BudgetRefinementHasType budgetContextS
      budgetRefinementEliminateBodyType
      (sortTm budgetRefinementEliminateBodyLevel) := by
  unfold budgetRefinementEliminateBodyType
    budgetRefinementEliminateBodyLevel budgetAfterEstablishedLevel
    budgetAfterRefutedLevel budgetAfterOutsideLevel
    budgetAfterIncompleteLevel budgetAfterIncompleteEstablishedLevel
    budgetAfterIncompleteRefutedLevel
  apply Presentation.HasType.piForm
  · exact budgetRefinementMotiveType_hasType
  · exact .sort budgetRefinementMotiveTypeLevel
  · apply Presentation.HasType.piForm
    · exact budgetEstablishedCaseType_hasType
    · exact .sort (budgetBinaryCaseLevel evidenceLevel evidenceLevel)
    · apply Presentation.HasType.piForm
      · exact budgetRefutedCaseAfterEstablished_hasType
      · exact .sort
          (budgetBinaryCaseLevel obstructionLevel obstructionLevel)
      · apply Presentation.HasType.piForm
        · exact budgetOutsideCaseAfterTwo_hasType
        · exact .sort (budgetUnaryCaseLevel boundaryLevel)
        · apply Presentation.HasType.piForm
          · exact budgetIncompleteCaseAfterThree_hasType
          · exact .sort
              (budgetBinaryCaseLevel frontierLevel frontierLevel)
          · apply Presentation.HasType.piForm
            · exact budgetIncompleteEstablishedCaseAfterFour_hasType
            · exact .sort
                (budgetBinaryCaseLevel frontierLevel evidenceLevel)
            · apply Presentation.HasType.piForm
              · exact budgetIncompleteRefutedCaseAfterFive_hasType
              · exact .sort
                  (budgetBinaryCaseLevel frontierLevel obstructionLevel)
              · exact budgetRefinementResultAfterSix_hasType
              · exact .sort budgetRefinementEliminateResultLevel
              · exact .sorts
                  (budgetBinaryCaseLevel frontierLevel obstructionLevel)
                  budgetRefinementEliminateResultLevel
            · exact .sort budgetAfterIncompleteRefutedLevel
            · exact .sorts
                (budgetBinaryCaseLevel frontierLevel evidenceLevel)
                budgetAfterIncompleteRefutedLevel
          · exact .sort budgetAfterIncompleteEstablishedLevel
          · exact .sorts
              (budgetBinaryCaseLevel frontierLevel frontierLevel)
              budgetAfterIncompleteEstablishedLevel
        · exact .sort budgetAfterIncompleteLevel
        · exact .sorts (budgetUnaryCaseLevel boundaryLevel)
            budgetAfterIncompleteLevel
      · exact .sort budgetAfterOutsideLevel
      · exact .sorts
          (budgetBinaryCaseLevel obstructionLevel obstructionLevel)
          budgetAfterOutsideLevel
    · exact .sort budgetAfterRefutedLevel
    · exact .sorts
        (budgetBinaryCaseLevel evidenceLevel evidenceLevel)
        budgetAfterRefutedLevel
  · exact .sort budgetAfterEstablishedLevel
  · exact .sorts budgetRefinementMotiveTypeLevel
      budgetAfterEstablishedLevel

theorem budgetRefinementEliminateType_hasType :
    BudgetRefinementHasType (.nil : Tower.Ctx 0)
      budgetRefinementEliminateType
      (sortTm budgetRefinementEliminateDeclarationLevel) := by
  unfold budgetRefinementEliminateType
    budgetRefinementEliminateDeclarationLevel
  apply Presentation.HasType.piForm
  · exact outcomeSignatureType_hasBudgetRefinementType
  · exact .sort signatureLevel
  · exact budgetRefinementEliminateBodyType_hasType
  · exact .sort budgetRefinementEliminateBodyLevel
  · exact .sorts signatureLevel budgetRefinementEliminateBodyLevel

/-! ### Formed declaration signature -/

@[simp] theorem rawBudgetRefinementSignature_valueOf_none
    (name : DeclName) :
    rawBudgetRefinementSignature.valueOf? name = none := by
  by_cases isFamily : name = budgetRefinementName
  · subst name
    simp [rawBudgetRefinementSignature,
      budgetRefinementDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty]
  by_cases isEstablished : name = budgetEstablishedName
  · subst name
    simp [rawBudgetRefinementSignature,
      budgetRefinementDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isFamily]
  by_cases isRefuted : name = budgetRefutedName
  · subst name
    simp [rawBudgetRefinementSignature,
      budgetRefinementDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isFamily,
      isEstablished]
  by_cases isOutside : name = budgetOutsideFragmentName
  · subst name
    simp [rawBudgetRefinementSignature,
      budgetRefinementDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isFamily,
      isEstablished, isRefuted]
  by_cases isIncomplete : name = budgetIncompleteName
  · subst name
    simp [rawBudgetRefinementSignature,
      budgetRefinementDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isFamily,
      isEstablished, isRefuted, isOutside]
  by_cases isIncompleteEstablished :
      name = budgetIncompleteEstablishedName
  · subst name
    simp [rawBudgetRefinementSignature,
      budgetRefinementDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isFamily,
      isEstablished, isRefuted, isOutside, isIncomplete]
  by_cases isIncompleteRefuted : name = budgetIncompleteRefutedName
  · subst name
    simp [rawBudgetRefinementSignature,
      budgetRefinementDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isFamily,
      isEstablished, isRefuted, isOutside, isIncomplete,
      isIncompleteEstablished]
  by_cases isEliminate : name = budgetRefinementEliminateName
  · subst name
    simp [rawBudgetRefinementSignature,
      budgetRefinementDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isFamily,
      isEstablished, isRefuted, isOutside, isIncomplete,
      isIncompleteEstablished, isIncompleteRefuted]
  · simp [rawBudgetRefinementSignature,
      budgetRefinementDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isFamily,
      isEstablished, isRefuted, isOutside, isIncomplete,
      isIncompleteEstablished, isIncompleteRefuted, isEliminate]

theorem rawBudgetRefinementSignature_types_formed
    {name : DeclName} {type : Tower.Tm 0}
    (lookup :
      rawBudgetRefinementSignature.typeOf? name = some type) :
    ∃ level : Tower.Head,
      Tower.rules.isUniverse level ∧
      BudgetRefinementHasType (.nil : Tower.Ctx 0) type
        (.head level) := by
  by_cases isFamily : name = budgetRefinementName
  · subst name
    have typeEquality : type = budgetRefinementType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort budgetRefinementDeclarationLevel,
      .sort budgetRefinementDeclarationLevel,
      budgetRefinementType_hasType⟩
  by_cases isEstablished : name = budgetEstablishedName
  · subst name
    have typeEquality : type = budgetEstablishedType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort budgetEstablishedDeclarationLevel,
      .sort budgetEstablishedDeclarationLevel,
      budgetEstablishedType_hasType⟩
  by_cases isRefuted : name = budgetRefutedName
  · subst name
    have typeEquality : type = budgetRefutedType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort budgetRefutedDeclarationLevel,
      .sort budgetRefutedDeclarationLevel, budgetRefutedType_hasType⟩
  by_cases isOutside : name = budgetOutsideFragmentName
  · subst name
    have typeEquality : type = budgetOutsideFragmentType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort budgetOutsideFragmentDeclarationLevel,
      .sort budgetOutsideFragmentDeclarationLevel,
      budgetOutsideFragmentType_hasType⟩
  by_cases isIncomplete : name = budgetIncompleteName
  · subst name
    have typeEquality : type = budgetIncompleteType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort budgetIncompleteDeclarationLevel,
      .sort budgetIncompleteDeclarationLevel,
      budgetIncompleteType_hasType⟩
  by_cases isIncompleteEstablished :
      name = budgetIncompleteEstablishedName
  · subst name
    have typeEquality : type = budgetIncompleteEstablishedType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort budgetIncompleteEstablishedDeclarationLevel,
      .sort budgetIncompleteEstablishedDeclarationLevel,
      budgetIncompleteEstablishedType_hasType⟩
  by_cases isIncompleteRefuted : name = budgetIncompleteRefutedName
  · subst name
    have typeEquality : type = budgetIncompleteRefutedType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort budgetIncompleteRefutedDeclarationLevel,
      .sort budgetIncompleteRefutedDeclarationLevel,
      budgetIncompleteRefutedType_hasType⟩
  by_cases isEliminate : name = budgetRefinementEliminateName
  · subst name
    have typeEquality : type = budgetRefinementEliminateType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort budgetRefinementEliminateDeclarationLevel,
      .sort budgetRefinementEliminateDeclarationLevel,
      budgetRefinementEliminateType_hasType⟩
  · simp [rawBudgetRefinementSignature,
      budgetRefinementDeclarations, Signature.typeOf?,
      Signature.ofList, Signature.insert, Signature.empty, isFamily,
      isEstablished, isRefuted, isOutside, isIncomplete,
      isIncompleteEstablished, isIncompleteRefuted, isEliminate] at lookup

theorem rawBudgetRefinementSignature_fresh {name : DeclName}
    {entry : Entry Tower.Head}
    (lookup : rawBudgetRefinementSignature.entries name = some entry) :
    emptyRules.constantType name = none := by
  by_cases isFamily : name = budgetRefinementName
  · subst name
    exact budgetRefinementName_fresh
  by_cases isEstablished : name = budgetEstablishedName
  · subst name
    exact budgetEstablishedName_fresh
  by_cases isRefuted : name = budgetRefutedName
  · subst name
    exact budgetRefutedName_fresh
  by_cases isOutside : name = budgetOutsideFragmentName
  · subst name
    exact budgetOutsideFragmentName_fresh
  by_cases isIncomplete : name = budgetIncompleteName
  · subst name
    exact budgetIncompleteName_fresh
  by_cases isIncompleteEstablished :
      name = budgetIncompleteEstablishedName
  · subst name
    exact budgetIncompleteEstablishedName_fresh
  by_cases isIncompleteRefuted : name = budgetIncompleteRefutedName
  · subst name
    exact budgetIncompleteRefutedName_fresh
  by_cases isEliminate : name = budgetRefinementEliminateName
  · subst name
    exact budgetRefinementEliminateName_fresh
  · simp [rawBudgetRefinementSignature,
      budgetRefinementDeclarations, Signature.ofList,
      Signature.insert, Signature.empty, isFamily, isEstablished,
      isRefuted, isOutside, isIncomplete, isIncompleteEstablished,
      isIncompleteRefuted, isEliminate] at lookup

def rawBudgetRefinementSignature_formed :
    rawBudgetRefinementSignature.Formed emptyRules where
  fresh := rawBudgetRefinementSignature_fresh
  types := rawBudgetRefinementSignature_types_formed
  values := by
    intro name type value _typeLookup valueLookup
    rw [rawBudgetRefinementSignature_valueOf_none] at valueLookup
    cases valueLookup
  noSelfDelta := by
    intro name value valueLookup
    rw [rawBudgetRefinementSignature_valueOf_none] at valueLookup
    cases valueLookup

/-! ### Strict positivity -/

def budgetRefinementFamilyApplication
    (signature judgment before after : Tower.Tm n)
    (signatureFree : FreeOf budgetRefinementName signature)
    (judgmentFree : FreeOf budgetRefinementName judgment)
    (beforeFree : FreeOf budgetRefinementName before)
    (afterFree : FreeOf budgetRefinementName after) :
    FamilyApplication budgetRefinementName 4
      (budgetRefinementApp signature judgment before after) :=
  .intro [signature, judgment, before, after] rfl (by
    intro argument membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl
    · exact signatureFree
    · exact judgmentFree
    · exact beforeFree
    · exact afterFree) rfl

def budgetSignatureTypeFree :
    FreeOf budgetRefinementName outcomeSignatureType :=
  outcomeSignatureTypeFreeOf budgetRefinementName

def budgetSignatureJudgmentFree
    {signature : Tower.Tm n}
    (signatureFree : FreeOf budgetRefinementName signature) :
    FreeOf budgetRefinementName (signatureJudgment signature) := by
  unfold signatureJudgment
  exact .fst signatureFree

def budgetSignatureEvidenceFree
    {signature : Tower.Tm n}
    (signatureFree : FreeOf budgetRefinementName signature) :
    FreeOf budgetRefinementName (signatureEvidence signature) := by
  unfold signatureEvidence
  exact .fst (.snd signatureFree)

def budgetSignatureObstructionFree
    {signature : Tower.Tm n}
    (signatureFree : FreeOf budgetRefinementName signature) :
    FreeOf budgetRefinementName (signatureObstruction signature) := by
  unfold signatureObstruction
  exact .fst (.snd (.snd signatureFree))

def budgetSignatureBoundaryFree
    {signature : Tower.Tm n}
    (signatureFree : FreeOf budgetRefinementName signature) :
    FreeOf budgetRefinementName (signatureBoundary signature) := by
  unfold signatureBoundary
  exact .fst (.snd (.snd (.snd signatureFree)))

def budgetSignatureFrontierFree
    {signature : Tower.Tm n}
    (signatureFree : FreeOf budgetRefinementName signature) :
    FreeOf budgetRefinementName (signatureFrontier signature) := by
  unfold signatureFrontier
  exact .snd (.snd (.snd (.snd signatureFree)))

def budgetOutcomeConstructorFree (constructor : DeclName)
    (different : constructor ≠ budgetRefinementName)
    {signature judgment witness : Tower.Tm n}
    (signatureFree : FreeOf budgetRefinementName signature)
    (judgmentFree : FreeOf budgetRefinementName judgment)
    (witnessFree : FreeOf budgetRefinementName witness) :
    FreeOf budgetRefinementName
      (namedOutcomeConstructorApp constructor signature judgment witness) :=
  .app (.app (.app (.const different) signatureFree) judgmentFree)
    witnessFree

def budgetEstablishedConstructorPositive :
    ConstructorType budgetRefinementName 4 budgetEstablishedType := by
  unfold budgetEstablishedType budgetEstablishedBodyType
  exact .field (.free budgetSignatureTypeFree)
    (.field (.free (budgetSignatureJudgmentFree (.var 0)))
      (.field
        (.free
          (.app (budgetSignatureEvidenceFree (.var 1)) (.var 0)))
        (.field
          (.free
            (.app (budgetSignatureEvidenceFree (.var 2)) (.var 1)))
          (.result
            (budgetRefinementFamilyApplication (.var 3) (.var 2)
              (establishedApp (.var 3) (.var 2) (.var 1))
              (establishedApp (.var 3) (.var 2) (.var 0))
              (.var 3) (.var 2)
              (by
                simpa [establishedApp, namedOutcomeConstructorApp] using
                  budgetOutcomeConstructorFree establishedName (by decide)
                    (.var 3) (.var 2) (.var 1))
              (by
                simpa [establishedApp, namedOutcomeConstructorApp] using
                  budgetOutcomeConstructorFree establishedName (by decide)
                    (.var 3) (.var 2) (.var 0)))))))

def budgetRefutedConstructorPositive :
    ConstructorType budgetRefinementName 4 budgetRefutedType := by
  unfold budgetRefutedType budgetRefutedBodyType
  exact .field (.free budgetSignatureTypeFree)
    (.field (.free (budgetSignatureJudgmentFree (.var 0)))
      (.field
        (.free
          (.app (budgetSignatureObstructionFree (.var 1)) (.var 0)))
        (.field
          (.free
            (.app (budgetSignatureObstructionFree (.var 2)) (.var 1)))
          (.result
            (budgetRefinementFamilyApplication (.var 3) (.var 2)
              (refutedApp (.var 3) (.var 2) (.var 1))
              (refutedApp (.var 3) (.var 2) (.var 0))
              (.var 3) (.var 2)
              (by
                simpa [refutedApp, namedOutcomeConstructorApp] using
                  budgetOutcomeConstructorFree refutedName (by decide)
                    (.var 3) (.var 2) (.var 1))
              (by
                simpa [refutedApp, namedOutcomeConstructorApp] using
                  budgetOutcomeConstructorFree refutedName (by decide)
                    (.var 3) (.var 2) (.var 0)))))))

def budgetOutsideFragmentConstructorPositive :
    ConstructorType budgetRefinementName 4
      budgetOutsideFragmentType := by
  unfold budgetOutsideFragmentType budgetOutsideFragmentBodyType
  exact .field (.free budgetSignatureTypeFree)
    (.field (.free (budgetSignatureJudgmentFree (.var 0)))
      (.field
        (.free
          (.app (budgetSignatureBoundaryFree (.var 1)) (.var 0)))
        (.result
          (budgetRefinementFamilyApplication (.var 2) (.var 1)
            (outsideFragmentApp (.var 2) (.var 1) (.var 0))
            (outsideFragmentApp (.var 2) (.var 1) (.var 0))
            (.var 2) (.var 1)
            (by
              simpa [outsideFragmentApp, namedOutcomeConstructorApp] using
                budgetOutcomeConstructorFree outsideFragmentName (by decide)
                  (.var 2) (.var 1) (.var 0))
            (by
              simpa [outsideFragmentApp, namedOutcomeConstructorApp] using
                budgetOutcomeConstructorFree outsideFragmentName (by decide)
                  (.var 2) (.var 1) (.var 0))))))

def budgetIncompleteConstructorPositive :
    ConstructorType budgetRefinementName 4 budgetIncompleteType := by
  unfold budgetIncompleteType budgetIncompleteBodyType
  exact .field (.free budgetSignatureTypeFree)
    (.field (.free (budgetSignatureJudgmentFree (.var 0)))
      (.field
        (.free (.app (budgetSignatureFrontierFree (.var 1)) (.var 0)))
        (.field
          (.free (.app (budgetSignatureFrontierFree (.var 2)) (.var 1)))
          (.result
            (budgetRefinementFamilyApplication (.var 3) (.var 2)
              (incompleteApp (.var 3) (.var 2) (.var 1))
              (incompleteApp (.var 3) (.var 2) (.var 0))
              (.var 3) (.var 2)
              (by
                simpa [incompleteApp, namedOutcomeConstructorApp] using
                  budgetOutcomeConstructorFree incompleteName (by decide)
                    (.var 3) (.var 2) (.var 1))
              (by
                simpa [incompleteApp, namedOutcomeConstructorApp] using
                  budgetOutcomeConstructorFree incompleteName (by decide)
                    (.var 3) (.var 2) (.var 0)))))))

def budgetIncompleteEstablishedConstructorPositive :
    ConstructorType budgetRefinementName 4
      budgetIncompleteEstablishedType := by
  unfold budgetIncompleteEstablishedType
    budgetIncompleteEstablishedBodyType
  exact .field (.free budgetSignatureTypeFree)
    (.field (.free (budgetSignatureJudgmentFree (.var 0)))
      (.field
        (.free (.app (budgetSignatureFrontierFree (.var 1)) (.var 0)))
        (.field
          (.free (.app (budgetSignatureEvidenceFree (.var 2)) (.var 1)))
          (.result
            (budgetRefinementFamilyApplication (.var 3) (.var 2)
              (incompleteApp (.var 3) (.var 2) (.var 1))
              (establishedApp (.var 3) (.var 2) (.var 0))
              (.var 3) (.var 2)
              (by
                simpa [incompleteApp, namedOutcomeConstructorApp] using
                  budgetOutcomeConstructorFree incompleteName (by decide)
                    (.var 3) (.var 2) (.var 1))
              (by
                simpa [establishedApp, namedOutcomeConstructorApp] using
                  budgetOutcomeConstructorFree establishedName (by decide)
                    (.var 3) (.var 2) (.var 0)))))))

def budgetIncompleteRefutedConstructorPositive :
    ConstructorType budgetRefinementName 4 budgetIncompleteRefutedType := by
  unfold budgetIncompleteRefutedType budgetIncompleteRefutedBodyType
  exact .field (.free budgetSignatureTypeFree)
    (.field (.free (budgetSignatureJudgmentFree (.var 0)))
      (.field
        (.free (.app (budgetSignatureFrontierFree (.var 1)) (.var 0)))
        (.field
          (.free
            (.app (budgetSignatureObstructionFree (.var 2)) (.var 1)))
          (.result
            (budgetRefinementFamilyApplication (.var 3) (.var 2)
              (incompleteApp (.var 3) (.var 2) (.var 1))
              (refutedApp (.var 3) (.var 2) (.var 0))
              (.var 3) (.var 2)
              (by
                simpa [incompleteApp, namedOutcomeConstructorApp] using
                  budgetOutcomeConstructorFree incompleteName (by decide)
                    (.var 3) (.var 2) (.var 1))
              (by
                simpa [refutedApp, namedOutcomeConstructorApp] using
                  budgetOutcomeConstructorFree refutedName (by decide)
                    (.var 3) (.var 2) (.var 0)))))))

def budgetEstablishedConstructorSpec :
    ConstructorSpec rawBudgetRefinementSignature
      budgetRefinementName 4 where
  name := budgetEstablishedName
  type := budgetEstablishedType
  declared := typeOf_budgetEstablished
  positive := budgetEstablishedConstructorPositive

def budgetRefutedConstructorSpec :
    ConstructorSpec rawBudgetRefinementSignature
      budgetRefinementName 4 where
  name := budgetRefutedName
  type := budgetRefutedType
  declared := typeOf_budgetRefuted
  positive := budgetRefutedConstructorPositive

def budgetOutsideFragmentConstructorSpec :
    ConstructorSpec rawBudgetRefinementSignature
      budgetRefinementName 4 where
  name := budgetOutsideFragmentName
  type := budgetOutsideFragmentType
  declared := typeOf_budgetOutsideFragment
  positive := budgetOutsideFragmentConstructorPositive

def budgetIncompleteConstructorSpec :
    ConstructorSpec rawBudgetRefinementSignature
      budgetRefinementName 4 where
  name := budgetIncompleteName
  type := budgetIncompleteType
  declared := typeOf_budgetIncomplete
  positive := budgetIncompleteConstructorPositive

def budgetIncompleteEstablishedConstructorSpec :
    ConstructorSpec rawBudgetRefinementSignature
      budgetRefinementName 4 where
  name := budgetIncompleteEstablishedName
  type := budgetIncompleteEstablishedType
  declared := typeOf_budgetIncompleteEstablished
  positive := budgetIncompleteEstablishedConstructorPositive

def budgetIncompleteRefutedConstructorSpec :
    ConstructorSpec rawBudgetRefinementSignature
      budgetRefinementName 4 where
  name := budgetIncompleteRefutedName
  type := budgetIncompleteRefutedType
  declared := typeOf_budgetIncompleteRefuted
  positive := budgetIncompleteRefutedConstructorPositive

def budgetRefinementConstructors :
    List (ConstructorSpec rawBudgetRefinementSignature
      budgetRefinementName 4) :=
  [budgetEstablishedConstructorSpec, budgetRefutedConstructorSpec,
    budgetOutsideFragmentConstructorSpec, budgetIncompleteConstructorSpec,
    budgetIncompleteEstablishedConstructorSpec,
    budgetIncompleteRefutedConstructorSpec]

def budgetRefinementEliminatorSpec :
    EliminatorSpec rawBudgetRefinementSignature where
  name := budgetRefinementEliminateName
  type := budgetRefinementEliminateType
  declared := typeOf_budgetRefinementEliminate

/-- A budget-refinement witness in a function domain is rejected as a
negative recursive occurrence, even when all four family arguments are
free. -/
theorem budgetRefinementInFunctionDomain_not_strictlyPositive :
    StrictlyPositive budgetRefinementName 4
      (.pi
        (budgetRefinementApp (.var 3 : Tower.Tm 4) (.var 2) (.var 1)
          (.var 0))
        (.var 0)) → False :=
  recursivePiDomain_not_strictlyPositive
    (budgetRefinementFamilyApplication (.var 3) (.var 2) (.var 1)
      (.var 0) (.var 3) (.var 2) (.var 1) (.var 0)) (.var 0)

/-! ### Canonical typed iota schemas -/

/-- The eliminator after its signature, motive, and all six branches have
been supplied in the canonical declaration telescope. -/
def budgetRefinementEliminateAtParameters : Tower.Tm 8 :=
  .app
    (.app
      (.app
        (.app
          (.app
            (.app
              (.app
                (.app (.const budgetRefinementEliminateName) (.var 7))
                (.var 6))
              (.var 5))
            (.var 4))
          (.var 3))
        (.var 2))
      (.var 1))
    (.var 0)

def budgetRefinementEliminateAtParametersType : Tower.Tm 8 :=
  .pi (signatureJudgment (.var 7))
    (.pi (outcomeApp (.var 8) (.var 0))
      (.pi (outcomeApp (.var 9) (.var 1))
        (.pi
          (budgetRefinementApp (.var 10) (.var 2) (.var 1) (.var 0))
          (.app
            (.app
              (.app
                (.app (.var 10) (.var 3)) (.var 2))
              (.var 1))
            (.var 0)))))

theorem budgetRefinementEliminateAtParameters_hasType :
    BudgetRefinementHasType
      budgetEliminatorContextIncompleteRefuted
      budgetRefinementEliminateAtParameters
      budgetRefinementEliminateAtParametersType := by
  have afterSignature := Presentation.HasType.appElim
    (budgetRefinementEliminateConstant_hasType
      (context := budgetEliminatorContextIncompleteRefuted))
    (Presentation.HasType.var 7)
  have afterMotive := Presentation.HasType.appElim afterSignature
    (Presentation.HasType.var 6)
  have afterEstablished := Presentation.HasType.appElim afterMotive
    (Presentation.HasType.var 5)
  have afterRefuted := Presentation.HasType.appElim afterEstablished
    (Presentation.HasType.var 4)
  have afterOutside := Presentation.HasType.appElim afterRefuted
    (Presentation.HasType.var 3)
  have afterIncomplete := Presentation.HasType.appElim afterOutside
    (Presentation.HasType.var 2)
  have afterIncompleteEstablished := Presentation.HasType.appElim
    afterIncomplete (Presentation.HasType.var 1)
  have afterIncompleteRefuted := Presentation.HasType.appElim
    afterIncompleteEstablished (Presentation.HasType.var 0)
  convert afterIncompleteRefuted using 1
  all_goals decide

def budgetRefinementIotaContextJ : Tower.Ctx 9 :=
  .snoc budgetEliminatorContextIncompleteRefuted
    (signatureJudgment (.var 7))

def budgetEstablishedIotaContextBefore : Tower.Ctx 10 :=
  .snoc budgetRefinementIotaContextJ
    (.app (signatureEvidence (.var 8)) (.var 0))

def budgetEstablishedIotaContext : Tower.Ctx 11 :=
  .snoc budgetEstablishedIotaContextBefore
    (.app (signatureEvidence (.var 9)) (.var 1))

def budgetEstablishedIotaBefore : Tower.Tm 11 :=
  establishedApp (.var 10) (.var 2) (.var 1)

def budgetEstablishedIotaAfter : Tower.Tm 11 :=
  establishedApp (.var 10) (.var 2) (.var 0)

def budgetEstablishedIotaRefinement : Tower.Tm 11 :=
  budgetEstablishedApp (.var 10) (.var 2) (.var 1) (.var 0)

def budgetEstablishedIotaLeft : Tower.Tm 11 :=
  budgetRefinementEliminateApp (.var 10) (.var 9) (.var 8) (.var 7)
    (.var 6) (.var 5) (.var 4) (.var 3) (.var 2)
    budgetEstablishedIotaBefore budgetEstablishedIotaAfter
    budgetEstablishedIotaRefinement

def budgetEstablishedIotaRight : Tower.Tm 11 :=
  .app (.app (.app (.var 8) (.var 2)) (.var 1)) (.var 0)

def budgetEstablishedIotaType : Tower.Tm 11 :=
  .app
    (.app
      (.app
        (.app (.var 9) (.var 2)) budgetEstablishedIotaBefore)
      budgetEstablishedIotaAfter)
    budgetEstablishedIotaRefinement

abbrev BudgetRefinementTypedIotaReceipt (context : Tower.Ctx n)
    (left right type : Tower.Tm n) : Type :=
  ProofRelevantStepReceipt emptyRules rawBudgetRefinementSignature
    proofRelevantBudgetRefinementComputation context left right type

def budgetEstablishedIotaReceipt :
    BudgetRefinementTypedIotaReceipt budgetEstablishedIotaContext
      budgetEstablishedIotaLeft budgetEstablishedIotaRight
      budgetEstablishedIotaType where
  sourceTyping := by
    unfold budgetEstablishedIotaContext budgetEstablishedIotaContextBefore
      budgetRefinementIotaContextJ
    have judgmentTyping :
        BudgetRefinementHasType budgetEstablishedIotaContext (.var 2)
          (signatureJudgment (.var 10)) := by
      exact Presentation.HasType.var 2
    have beforeEvidenceTyping :
        BudgetRefinementHasType budgetEstablishedIotaContext (.var 1)
          (.app (signatureEvidence (.var 10)) (.var 2)) := by
      exact Presentation.HasType.var 1
    have afterEvidenceTyping :
        BudgetRefinementHasType budgetEstablishedIotaContext (.var 0)
          (.app (signatureEvidence (.var 10)) (.var 2)) := by
      exact Presentation.HasType.var 0
    have beforeTyping := establishedApp_hasBudgetRefinementType
      (context := budgetEstablishedIotaContext)
      (signature := (.var 10)) (judgment := (.var 2))
      (witness := (.var 1)) (Presentation.HasType.var 10)
      judgmentTyping beforeEvidenceTyping
    have afterTyping := establishedApp_hasBudgetRefinementType
      (context := budgetEstablishedIotaContext)
      (signature := (.var 10)) (judgment := (.var 2))
      (witness := (.var 0)) (Presentation.HasType.var 10)
      judgmentTyping afterEvidenceTyping
    have refinementTyping := budgetEstablishedApp_hasType
      (context := budgetEstablishedIotaContext)
      (signature := (.var 10)) (judgment := (.var 2))
      (beforeEvidence := (.var 1)) (afterEvidence := (.var 0))
      (Presentation.HasType.var 10) judgmentTyping
      beforeEvidenceTyping afterEvidenceTyping
    have afterJudgmentBinder :=
      budgetRefinementEliminateAtParameters_hasType.weaken
        (extension := signatureJudgment (.var 7))
    have afterBeforeBinder := afterJudgmentBinder.weaken
      (extension := .app (signatureEvidence (.var 8)) (.var 0))
    have weakened := afterBeforeBinder.weaken
      (extension := .app (signatureEvidence (.var 9)) (.var 1))
    have afterJudgment := Presentation.HasType.appElim weakened
      judgmentTyping
    have afterBefore := Presentation.HasType.appElim afterJudgment
      beforeTyping
    have afterAfter := Presentation.HasType.appElim afterBefore afterTyping
    have source := Presentation.HasType.appElim afterAfter refinementTyping
    convert source using 1
    all_goals decide
  targetTyping := by
    have judgmentTyping :
        BudgetRefinementHasType budgetEstablishedIotaContext (.var 2)
          (signatureJudgment (.var 10)) := by
      exact Presentation.HasType.var 2
    have beforeEvidenceTyping :
        BudgetRefinementHasType budgetEstablishedIotaContext (.var 1)
          (.app (signatureEvidence (.var 10)) (.var 2)) := by
      exact Presentation.HasType.var 1
    have afterEvidenceTyping :
        BudgetRefinementHasType budgetEstablishedIotaContext (.var 0)
          (.app (signatureEvidence (.var 10)) (.var 2)) := by
      exact Presentation.HasType.var 0
    have afterJudgment := Presentation.HasType.appElim
      (Presentation.HasType.var (R := budgetRefinementRules)
        (Γ := budgetEstablishedIotaContext) (8 : Fin 11))
      judgmentTyping
    have afterBefore := Presentation.HasType.appElim afterJudgment
      beforeEvidenceTyping
    have target := Presentation.HasType.appElim afterBefore
      afterEvidenceTyping
    convert target using 1
    all_goals decide
  evidence := by
    change BudgetRefinementIotaEvidence 11 budgetEstablishedIotaLeft
      budgetEstablishedIotaRight
    unfold budgetEstablishedIotaLeft budgetEstablishedIotaRight
      budgetEstablishedIotaBefore budgetEstablishedIotaAfter
      budgetEstablishedIotaRefinement
    exact BudgetRefinementIotaEvidence.established
      (.var 10) (.var 9) (.var 8) (.var 7) (.var 6) (.var 5)
      (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

def budgetEstablishedIotaSchema :
    IotaSchema emptyRules rawBudgetRefinementSignature
      proofRelevantBudgetRefinementComputation 11 where
  context := budgetEstablishedIotaContext
  left := budgetEstablishedIotaLeft
  right := budgetEstablishedIotaRight
  type := budgetEstablishedIotaType
  receipt := budgetEstablishedIotaReceipt

def budgetRefutedIotaContextBefore : Tower.Ctx 10 :=
  .snoc budgetRefinementIotaContextJ
    (.app (signatureObstruction (.var 8)) (.var 0))

def budgetRefutedIotaContext : Tower.Ctx 11 :=
  .snoc budgetRefutedIotaContextBefore
    (.app (signatureObstruction (.var 9)) (.var 1))

def budgetRefutedIotaBefore : Tower.Tm 11 :=
  refutedApp (.var 10) (.var 2) (.var 1)

def budgetRefutedIotaAfter : Tower.Tm 11 :=
  refutedApp (.var 10) (.var 2) (.var 0)

def budgetRefutedIotaRefinement : Tower.Tm 11 :=
  budgetRefutedApp (.var 10) (.var 2) (.var 1) (.var 0)

def budgetRefutedIotaLeft : Tower.Tm 11 :=
  budgetRefinementEliminateApp (.var 10) (.var 9) (.var 8) (.var 7)
    (.var 6) (.var 5) (.var 4) (.var 3) (.var 2)
    budgetRefutedIotaBefore budgetRefutedIotaAfter
    budgetRefutedIotaRefinement

def budgetRefutedIotaRight : Tower.Tm 11 :=
  .app (.app (.app (.var 7) (.var 2)) (.var 1)) (.var 0)

def budgetRefutedIotaType : Tower.Tm 11 :=
  .app
    (.app
      (.app
        (.app (.var 9) (.var 2)) budgetRefutedIotaBefore)
      budgetRefutedIotaAfter)
    budgetRefutedIotaRefinement

def budgetRefutedIotaReceipt :
    BudgetRefinementTypedIotaReceipt budgetRefutedIotaContext
      budgetRefutedIotaLeft budgetRefutedIotaRight
      budgetRefutedIotaType where
  sourceTyping := by
    unfold budgetRefutedIotaContext budgetRefutedIotaContextBefore
      budgetRefinementIotaContextJ
    have judgmentTyping :
        BudgetRefinementHasType budgetRefutedIotaContext (.var 2)
          (signatureJudgment (.var 10)) := by
      exact Presentation.HasType.var 2
    have beforeObstructionTyping :
        BudgetRefinementHasType budgetRefutedIotaContext (.var 1)
          (.app (signatureObstruction (.var 10)) (.var 2)) := by
      exact Presentation.HasType.var 1
    have afterObstructionTyping :
        BudgetRefinementHasType budgetRefutedIotaContext (.var 0)
          (.app (signatureObstruction (.var 10)) (.var 2)) := by
      exact Presentation.HasType.var 0
    have beforeTyping := refutedApp_hasBudgetRefinementType
      (context := budgetRefutedIotaContext)
      (signature := (.var 10)) (judgment := (.var 2))
      (witness := (.var 1)) (Presentation.HasType.var 10)
      judgmentTyping beforeObstructionTyping
    have afterTyping := refutedApp_hasBudgetRefinementType
      (context := budgetRefutedIotaContext)
      (signature := (.var 10)) (judgment := (.var 2))
      (witness := (.var 0)) (Presentation.HasType.var 10)
      judgmentTyping afterObstructionTyping
    have refinementTyping := budgetRefutedApp_hasType
      (context := budgetRefutedIotaContext)
      (signature := (.var 10)) (judgment := (.var 2))
      (beforeObstruction := (.var 1)) (afterObstruction := (.var 0))
      (Presentation.HasType.var 10) judgmentTyping
      beforeObstructionTyping afterObstructionTyping
    have afterJudgmentBinder :=
      budgetRefinementEliminateAtParameters_hasType.weaken
        (extension := signatureJudgment (.var 7))
    have afterBeforeBinder := afterJudgmentBinder.weaken
      (extension := .app (signatureObstruction (.var 8)) (.var 0))
    have weakened := afterBeforeBinder.weaken
      (extension := .app (signatureObstruction (.var 9)) (.var 1))
    have afterJudgment := Presentation.HasType.appElim weakened
      judgmentTyping
    have afterBefore := Presentation.HasType.appElim afterJudgment
      beforeTyping
    have afterAfter := Presentation.HasType.appElim afterBefore afterTyping
    have source := Presentation.HasType.appElim afterAfter refinementTyping
    convert source using 1
    all_goals decide
  targetTyping := by
    have judgmentTyping :
        BudgetRefinementHasType budgetRefutedIotaContext (.var 2)
          (signatureJudgment (.var 10)) := by
      exact Presentation.HasType.var 2
    have beforeObstructionTyping :
        BudgetRefinementHasType budgetRefutedIotaContext (.var 1)
          (.app (signatureObstruction (.var 10)) (.var 2)) := by
      exact Presentation.HasType.var 1
    have afterObstructionTyping :
        BudgetRefinementHasType budgetRefutedIotaContext (.var 0)
          (.app (signatureObstruction (.var 10)) (.var 2)) := by
      exact Presentation.HasType.var 0
    have afterJudgment := Presentation.HasType.appElim
      (Presentation.HasType.var (R := budgetRefinementRules)
        (Γ := budgetRefutedIotaContext) (7 : Fin 11))
      judgmentTyping
    have afterBefore := Presentation.HasType.appElim afterJudgment
      beforeObstructionTyping
    have target := Presentation.HasType.appElim afterBefore
      afterObstructionTyping
    convert target using 1
    all_goals decide
  evidence := by
    change BudgetRefinementIotaEvidence 11 budgetRefutedIotaLeft
      budgetRefutedIotaRight
    unfold budgetRefutedIotaLeft budgetRefutedIotaRight
      budgetRefutedIotaBefore budgetRefutedIotaAfter
      budgetRefutedIotaRefinement
    exact BudgetRefinementIotaEvidence.refuted
      (.var 10) (.var 9) (.var 8) (.var 7) (.var 6) (.var 5)
      (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

def budgetRefutedIotaSchema :
    IotaSchema emptyRules rawBudgetRefinementSignature
      proofRelevantBudgetRefinementComputation 11 where
  context := budgetRefutedIotaContext
  left := budgetRefutedIotaLeft
  right := budgetRefutedIotaRight
  type := budgetRefutedIotaType
  receipt := budgetRefutedIotaReceipt

def budgetOutsideFragmentIotaContext : Tower.Ctx 10 :=
  .snoc budgetRefinementIotaContextJ
    (.app (signatureBoundary (.var 8)) (.var 0))

def budgetOutsideFragmentIotaOutcome : Tower.Tm 10 :=
  outsideFragmentApp (.var 9) (.var 1) (.var 0)

def budgetOutsideFragmentIotaRefinement : Tower.Tm 10 :=
  budgetOutsideFragmentApp (.var 9) (.var 1) (.var 0)

def budgetOutsideFragmentIotaLeft : Tower.Tm 10 :=
  budgetRefinementEliminateApp (.var 9) (.var 8) (.var 7) (.var 6)
    (.var 5) (.var 4) (.var 3) (.var 2) (.var 1)
    budgetOutsideFragmentIotaOutcome budgetOutsideFragmentIotaOutcome
    budgetOutsideFragmentIotaRefinement

def budgetOutsideFragmentIotaRight : Tower.Tm 10 :=
  .app (.app (.var 5) (.var 1)) (.var 0)

def budgetOutsideFragmentIotaType : Tower.Tm 10 :=
  .app
    (.app
      (.app
        (.app (.var 8) (.var 1)) budgetOutsideFragmentIotaOutcome)
      budgetOutsideFragmentIotaOutcome)
    budgetOutsideFragmentIotaRefinement

def budgetOutsideFragmentIotaReceipt :
    BudgetRefinementTypedIotaReceipt budgetOutsideFragmentIotaContext
      budgetOutsideFragmentIotaLeft budgetOutsideFragmentIotaRight
      budgetOutsideFragmentIotaType where
  sourceTyping := by
    unfold budgetOutsideFragmentIotaContext budgetRefinementIotaContextJ
    have judgmentTyping :
        BudgetRefinementHasType budgetOutsideFragmentIotaContext
          (.var 1) (signatureJudgment (.var 9)) := by
      exact Presentation.HasType.var 1
    have reasonTyping :
        BudgetRefinementHasType budgetOutsideFragmentIotaContext
          (.var 0) (.app (signatureBoundary (.var 9)) (.var 1)) := by
      exact Presentation.HasType.var 0
    have outcomeTyping := outsideFragmentApp_hasBudgetRefinementType
      (context := budgetOutsideFragmentIotaContext)
      (signature := (.var 9)) (judgment := (.var 1))
      (witness := (.var 0)) (Presentation.HasType.var 9)
      judgmentTyping reasonTyping
    have refinementTyping := budgetOutsideFragmentApp_hasType
      (context := budgetOutsideFragmentIotaContext)
      (signature := (.var 9)) (judgment := (.var 1))
      (reason := (.var 0)) (Presentation.HasType.var 9)
      judgmentTyping reasonTyping
    have afterJudgmentBinder :=
      budgetRefinementEliminateAtParameters_hasType.weaken
        (extension := signatureJudgment (.var 7))
    have weakened := afterJudgmentBinder.weaken
      (extension := .app (signatureBoundary (.var 8)) (.var 0))
    have afterJudgment := Presentation.HasType.appElim weakened
      judgmentTyping
    have afterBefore := Presentation.HasType.appElim afterJudgment
      outcomeTyping
    have afterAfter := Presentation.HasType.appElim afterBefore outcomeTyping
    have source := Presentation.HasType.appElim afterAfter refinementTyping
    convert source using 1
    all_goals decide
  targetTyping := by
    have judgmentTyping :
        BudgetRefinementHasType budgetOutsideFragmentIotaContext
          (.var 1) (signatureJudgment (.var 9)) := by
      exact Presentation.HasType.var 1
    have reasonTyping :
        BudgetRefinementHasType budgetOutsideFragmentIotaContext
          (.var 0) (.app (signatureBoundary (.var 9)) (.var 1)) := by
      exact Presentation.HasType.var 0
    have afterJudgment := Presentation.HasType.appElim
      (Presentation.HasType.var (R := budgetRefinementRules)
        (Γ := budgetOutsideFragmentIotaContext) (5 : Fin 10))
      judgmentTyping
    have target := Presentation.HasType.appElim afterJudgment reasonTyping
    convert target using 1
    all_goals decide
  evidence := by
    change BudgetRefinementIotaEvidence 10 budgetOutsideFragmentIotaLeft
      budgetOutsideFragmentIotaRight
    unfold budgetOutsideFragmentIotaLeft budgetOutsideFragmentIotaRight
      budgetOutsideFragmentIotaOutcome
      budgetOutsideFragmentIotaRefinement
    exact BudgetRefinementIotaEvidence.outsideFragment
      (.var 9) (.var 8) (.var 7) (.var 6) (.var 5) (.var 4)
      (.var 3) (.var 2) (.var 1) (.var 0)

def budgetOutsideFragmentIotaSchema :
    IotaSchema emptyRules rawBudgetRefinementSignature
      proofRelevantBudgetRefinementComputation 10 where
  context := budgetOutsideFragmentIotaContext
  left := budgetOutsideFragmentIotaLeft
  right := budgetOutsideFragmentIotaRight
  type := budgetOutsideFragmentIotaType
  receipt := budgetOutsideFragmentIotaReceipt

def budgetIncompleteIotaContextBefore : Tower.Ctx 10 :=
  .snoc budgetRefinementIotaContextJ
    (.app (signatureFrontier (.var 8)) (.var 0))

def budgetIncompleteIotaContext : Tower.Ctx 11 :=
  .snoc budgetIncompleteIotaContextBefore
    (.app (signatureFrontier (.var 9)) (.var 1))

def budgetIncompleteIotaBefore : Tower.Tm 11 :=
  incompleteApp (.var 10) (.var 2) (.var 1)

def budgetIncompleteIotaAfter : Tower.Tm 11 :=
  incompleteApp (.var 10) (.var 2) (.var 0)

def budgetIncompleteIotaRefinement : Tower.Tm 11 :=
  budgetIncompleteApp (.var 10) (.var 2) (.var 1) (.var 0)

def budgetIncompleteIotaLeft : Tower.Tm 11 :=
  budgetRefinementEliminateApp (.var 10) (.var 9) (.var 8) (.var 7)
    (.var 6) (.var 5) (.var 4) (.var 3) (.var 2)
    budgetIncompleteIotaBefore budgetIncompleteIotaAfter
    budgetIncompleteIotaRefinement

def budgetIncompleteIotaRight : Tower.Tm 11 :=
  .app (.app (.app (.var 5) (.var 2)) (.var 1)) (.var 0)

def budgetIncompleteIotaType : Tower.Tm 11 :=
  .app
    (.app
      (.app
        (.app (.var 9) (.var 2)) budgetIncompleteIotaBefore)
      budgetIncompleteIotaAfter)
    budgetIncompleteIotaRefinement

def budgetIncompleteIotaReceipt :
    BudgetRefinementTypedIotaReceipt budgetIncompleteIotaContext
      budgetIncompleteIotaLeft budgetIncompleteIotaRight
      budgetIncompleteIotaType where
  sourceTyping := by
    unfold budgetIncompleteIotaContext budgetIncompleteIotaContextBefore
      budgetRefinementIotaContextJ
    have judgmentTyping :
        BudgetRefinementHasType budgetIncompleteIotaContext (.var 2)
          (signatureJudgment (.var 10)) := by
      exact Presentation.HasType.var 2
    have beforeFrontierTyping :
        BudgetRefinementHasType budgetIncompleteIotaContext (.var 1)
          (.app (signatureFrontier (.var 10)) (.var 2)) := by
      exact Presentation.HasType.var 1
    have afterFrontierTyping :
        BudgetRefinementHasType budgetIncompleteIotaContext (.var 0)
          (.app (signatureFrontier (.var 10)) (.var 2)) := by
      exact Presentation.HasType.var 0
    have beforeTyping := incompleteApp_hasBudgetRefinementType
      (context := budgetIncompleteIotaContext)
      (signature := (.var 10)) (judgment := (.var 2))
      (witness := (.var 1)) (Presentation.HasType.var 10)
      judgmentTyping beforeFrontierTyping
    have afterTyping := incompleteApp_hasBudgetRefinementType
      (context := budgetIncompleteIotaContext)
      (signature := (.var 10)) (judgment := (.var 2))
      (witness := (.var 0)) (Presentation.HasType.var 10)
      judgmentTyping afterFrontierTyping
    have refinementTyping := budgetIncompleteApp_hasType
      (context := budgetIncompleteIotaContext)
      (signature := (.var 10)) (judgment := (.var 2))
      (beforeFrontier := (.var 1)) (afterFrontier := (.var 0))
      (Presentation.HasType.var 10) judgmentTyping
      beforeFrontierTyping afterFrontierTyping
    have afterJudgmentBinder :=
      budgetRefinementEliminateAtParameters_hasType.weaken
        (extension := signatureJudgment (.var 7))
    have afterBeforeBinder := afterJudgmentBinder.weaken
      (extension := .app (signatureFrontier (.var 8)) (.var 0))
    have weakened := afterBeforeBinder.weaken
      (extension := .app (signatureFrontier (.var 9)) (.var 1))
    have afterJudgment := Presentation.HasType.appElim weakened
      judgmentTyping
    have afterBefore := Presentation.HasType.appElim afterJudgment
      beforeTyping
    have afterAfter := Presentation.HasType.appElim afterBefore afterTyping
    have source := Presentation.HasType.appElim afterAfter refinementTyping
    convert source using 1
    all_goals decide
  targetTyping := by
    have judgmentTyping :
        BudgetRefinementHasType budgetIncompleteIotaContext (.var 2)
          (signatureJudgment (.var 10)) := by
      exact Presentation.HasType.var 2
    have beforeFrontierTyping :
        BudgetRefinementHasType budgetIncompleteIotaContext (.var 1)
          (.app (signatureFrontier (.var 10)) (.var 2)) := by
      exact Presentation.HasType.var 1
    have afterFrontierTyping :
        BudgetRefinementHasType budgetIncompleteIotaContext (.var 0)
          (.app (signatureFrontier (.var 10)) (.var 2)) := by
      exact Presentation.HasType.var 0
    have afterJudgment := Presentation.HasType.appElim
      (Presentation.HasType.var (R := budgetRefinementRules)
        (Γ := budgetIncompleteIotaContext) (5 : Fin 11))
      judgmentTyping
    have afterBefore := Presentation.HasType.appElim afterJudgment
      beforeFrontierTyping
    have target := Presentation.HasType.appElim afterBefore
      afterFrontierTyping
    convert target using 1
    all_goals decide
  evidence := by
    change BudgetRefinementIotaEvidence 11 budgetIncompleteIotaLeft
      budgetIncompleteIotaRight
    unfold budgetIncompleteIotaLeft budgetIncompleteIotaRight
      budgetIncompleteIotaBefore budgetIncompleteIotaAfter
      budgetIncompleteIotaRefinement
    exact BudgetRefinementIotaEvidence.incomplete
      (.var 10) (.var 9) (.var 8) (.var 7) (.var 6) (.var 5)
      (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

def budgetIncompleteIotaSchema :
    IotaSchema emptyRules rawBudgetRefinementSignature
      proofRelevantBudgetRefinementComputation 11 where
  context := budgetIncompleteIotaContext
  left := budgetIncompleteIotaLeft
  right := budgetIncompleteIotaRight
  type := budgetIncompleteIotaType
  receipt := budgetIncompleteIotaReceipt

def budgetIncompleteEstablishedIotaContextBefore : Tower.Ctx 10 :=
  .snoc budgetRefinementIotaContextJ
    (.app (signatureFrontier (.var 8)) (.var 0))

def budgetIncompleteEstablishedIotaContext : Tower.Ctx 11 :=
  .snoc budgetIncompleteEstablishedIotaContextBefore
    (.app (signatureEvidence (.var 9)) (.var 1))

def budgetIncompleteEstablishedIotaBefore : Tower.Tm 11 :=
  incompleteApp (.var 10) (.var 2) (.var 1)

def budgetIncompleteEstablishedIotaAfter : Tower.Tm 11 :=
  establishedApp (.var 10) (.var 2) (.var 0)

def budgetIncompleteEstablishedIotaRefinement : Tower.Tm 11 :=
  budgetIncompleteEstablishedApp (.var 10) (.var 2) (.var 1) (.var 0)

def budgetIncompleteEstablishedIotaLeft : Tower.Tm 11 :=
  budgetRefinementEliminateApp (.var 10) (.var 9) (.var 8) (.var 7)
    (.var 6) (.var 5) (.var 4) (.var 3) (.var 2)
    budgetIncompleteEstablishedIotaBefore
    budgetIncompleteEstablishedIotaAfter
    budgetIncompleteEstablishedIotaRefinement

def budgetIncompleteEstablishedIotaRight : Tower.Tm 11 :=
  .app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 0)

def budgetIncompleteEstablishedIotaType : Tower.Tm 11 :=
  .app
    (.app
      (.app
        (.app (.var 9) (.var 2))
          budgetIncompleteEstablishedIotaBefore)
      budgetIncompleteEstablishedIotaAfter)
    budgetIncompleteEstablishedIotaRefinement

def budgetIncompleteEstablishedIotaReceipt :
    BudgetRefinementTypedIotaReceipt budgetIncompleteEstablishedIotaContext
      budgetIncompleteEstablishedIotaLeft
      budgetIncompleteEstablishedIotaRight
      budgetIncompleteEstablishedIotaType where
  sourceTyping := by
    unfold budgetIncompleteEstablishedIotaContext
      budgetIncompleteEstablishedIotaContextBefore
      budgetRefinementIotaContextJ
    have judgmentTyping :
        BudgetRefinementHasType budgetIncompleteEstablishedIotaContext
          (.var 2) (signatureJudgment (.var 10)) := by
      exact Presentation.HasType.var 2
    have frontierTyping :
        BudgetRefinementHasType budgetIncompleteEstablishedIotaContext
          (.var 1) (.app (signatureFrontier (.var 10)) (.var 2)) := by
      exact Presentation.HasType.var 1
    have evidenceTyping :
        BudgetRefinementHasType budgetIncompleteEstablishedIotaContext
          (.var 0) (.app (signatureEvidence (.var 10)) (.var 2)) := by
      exact Presentation.HasType.var 0
    have beforeTyping := incompleteApp_hasBudgetRefinementType
      (context := budgetIncompleteEstablishedIotaContext)
      (signature := (.var 10)) (judgment := (.var 2))
      (witness := (.var 1)) (Presentation.HasType.var 10)
      judgmentTyping frontierTyping
    have afterTyping := establishedApp_hasBudgetRefinementType
      (context := budgetIncompleteEstablishedIotaContext)
      (signature := (.var 10)) (judgment := (.var 2))
      (witness := (.var 0)) (Presentation.HasType.var 10)
      judgmentTyping evidenceTyping
    have refinementTyping := budgetIncompleteEstablishedApp_hasType
      (context := budgetIncompleteEstablishedIotaContext)
      (signature := (.var 10)) (judgment := (.var 2))
      (frontier := (.var 1)) (evidence := (.var 0))
      (Presentation.HasType.var 10) judgmentTyping frontierTyping
      evidenceTyping
    have afterJudgmentBinder :=
      budgetRefinementEliminateAtParameters_hasType.weaken
        (extension := signatureJudgment (.var 7))
    have afterFrontierBinder := afterJudgmentBinder.weaken
      (extension := .app (signatureFrontier (.var 8)) (.var 0))
    have weakened := afterFrontierBinder.weaken
      (extension := .app (signatureEvidence (.var 9)) (.var 1))
    have afterJudgment := Presentation.HasType.appElim weakened
      judgmentTyping
    have afterBefore := Presentation.HasType.appElim afterJudgment
      beforeTyping
    have afterAfter := Presentation.HasType.appElim afterBefore afterTyping
    have source := Presentation.HasType.appElim afterAfter refinementTyping
    convert source using 1
    all_goals decide
  targetTyping := by
    have judgmentTyping :
        BudgetRefinementHasType budgetIncompleteEstablishedIotaContext
          (.var 2) (signatureJudgment (.var 10)) := by
      exact Presentation.HasType.var 2
    have frontierTyping :
        BudgetRefinementHasType budgetIncompleteEstablishedIotaContext
          (.var 1) (.app (signatureFrontier (.var 10)) (.var 2)) := by
      exact Presentation.HasType.var 1
    have evidenceTyping :
        BudgetRefinementHasType budgetIncompleteEstablishedIotaContext
          (.var 0) (.app (signatureEvidence (.var 10)) (.var 2)) := by
      exact Presentation.HasType.var 0
    have afterJudgment := Presentation.HasType.appElim
      (Presentation.HasType.var (R := budgetRefinementRules)
        (Γ := budgetIncompleteEstablishedIotaContext) (4 : Fin 11))
      judgmentTyping
    have afterFrontier := Presentation.HasType.appElim afterJudgment
      frontierTyping
    have target := Presentation.HasType.appElim afterFrontier evidenceTyping
    convert target using 1
    all_goals decide
  evidence := by
    change BudgetRefinementIotaEvidence 11
      budgetIncompleteEstablishedIotaLeft
      budgetIncompleteEstablishedIotaRight
    unfold budgetIncompleteEstablishedIotaLeft
      budgetIncompleteEstablishedIotaRight
      budgetIncompleteEstablishedIotaBefore
      budgetIncompleteEstablishedIotaAfter
      budgetIncompleteEstablishedIotaRefinement
    exact BudgetRefinementIotaEvidence.incompleteEstablished
      (.var 10) (.var 9) (.var 8) (.var 7) (.var 6) (.var 5)
      (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

def budgetIncompleteEstablishedIotaSchema :
    IotaSchema emptyRules rawBudgetRefinementSignature
      proofRelevantBudgetRefinementComputation 11 where
  context := budgetIncompleteEstablishedIotaContext
  left := budgetIncompleteEstablishedIotaLeft
  right := budgetIncompleteEstablishedIotaRight
  type := budgetIncompleteEstablishedIotaType
  receipt := budgetIncompleteEstablishedIotaReceipt

def budgetIncompleteRefutedIotaContextBefore : Tower.Ctx 10 :=
  .snoc budgetRefinementIotaContextJ
    (.app (signatureFrontier (.var 8)) (.var 0))

def budgetIncompleteRefutedIotaContext : Tower.Ctx 11 :=
  .snoc budgetIncompleteRefutedIotaContextBefore
    (.app (signatureObstruction (.var 9)) (.var 1))

def budgetIncompleteRefutedIotaBefore : Tower.Tm 11 :=
  incompleteApp (.var 10) (.var 2) (.var 1)

def budgetIncompleteRefutedIotaAfter : Tower.Tm 11 :=
  refutedApp (.var 10) (.var 2) (.var 0)

def budgetIncompleteRefutedIotaRefinement : Tower.Tm 11 :=
  budgetIncompleteRefutedApp (.var 10) (.var 2) (.var 1) (.var 0)

def budgetIncompleteRefutedIotaLeft : Tower.Tm 11 :=
  budgetRefinementEliminateApp (.var 10) (.var 9) (.var 8) (.var 7)
    (.var 6) (.var 5) (.var 4) (.var 3) (.var 2)
    budgetIncompleteRefutedIotaBefore budgetIncompleteRefutedIotaAfter
    budgetIncompleteRefutedIotaRefinement

def budgetIncompleteRefutedIotaRight : Tower.Tm 11 :=
  .app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)

def budgetIncompleteRefutedIotaType : Tower.Tm 11 :=
  .app
    (.app
      (.app
        (.app (.var 9) (.var 2)) budgetIncompleteRefutedIotaBefore)
      budgetIncompleteRefutedIotaAfter)
    budgetIncompleteRefutedIotaRefinement

def budgetIncompleteRefutedIotaReceipt :
    BudgetRefinementTypedIotaReceipt budgetIncompleteRefutedIotaContext
      budgetIncompleteRefutedIotaLeft budgetIncompleteRefutedIotaRight
      budgetIncompleteRefutedIotaType where
  sourceTyping := by
    unfold budgetIncompleteRefutedIotaContext
      budgetIncompleteRefutedIotaContextBefore budgetRefinementIotaContextJ
    have judgmentTyping :
        BudgetRefinementHasType budgetIncompleteRefutedIotaContext
          (.var 2) (signatureJudgment (.var 10)) := by
      exact Presentation.HasType.var 2
    have frontierTyping :
        BudgetRefinementHasType budgetIncompleteRefutedIotaContext
          (.var 1) (.app (signatureFrontier (.var 10)) (.var 2)) := by
      exact Presentation.HasType.var 1
    have obstructionTyping :
        BudgetRefinementHasType budgetIncompleteRefutedIotaContext
          (.var 0) (.app (signatureObstruction (.var 10)) (.var 2)) := by
      exact Presentation.HasType.var 0
    have beforeTyping := incompleteApp_hasBudgetRefinementType
      (context := budgetIncompleteRefutedIotaContext)
      (signature := (.var 10)) (judgment := (.var 2))
      (witness := (.var 1)) (Presentation.HasType.var 10)
      judgmentTyping frontierTyping
    have afterTyping := refutedApp_hasBudgetRefinementType
      (context := budgetIncompleteRefutedIotaContext)
      (signature := (.var 10)) (judgment := (.var 2))
      (witness := (.var 0)) (Presentation.HasType.var 10)
      judgmentTyping obstructionTyping
    have refinementTyping := budgetIncompleteRefutedApp_hasType
      (context := budgetIncompleteRefutedIotaContext)
      (signature := (.var 10)) (judgment := (.var 2))
      (frontier := (.var 1)) (obstruction := (.var 0))
      (Presentation.HasType.var 10) judgmentTyping frontierTyping
      obstructionTyping
    have afterJudgmentBinder :=
      budgetRefinementEliminateAtParameters_hasType.weaken
        (extension := signatureJudgment (.var 7))
    have afterFrontierBinder := afterJudgmentBinder.weaken
      (extension := .app (signatureFrontier (.var 8)) (.var 0))
    have weakened := afterFrontierBinder.weaken
      (extension := .app (signatureObstruction (.var 9)) (.var 1))
    have afterJudgment := Presentation.HasType.appElim weakened
      judgmentTyping
    have afterBefore := Presentation.HasType.appElim afterJudgment
      beforeTyping
    have afterAfter := Presentation.HasType.appElim afterBefore afterTyping
    have source := Presentation.HasType.appElim afterAfter refinementTyping
    convert source using 1
    all_goals decide
  targetTyping := by
    have judgmentTyping :
        BudgetRefinementHasType budgetIncompleteRefutedIotaContext
          (.var 2) (signatureJudgment (.var 10)) := by
      exact Presentation.HasType.var 2
    have frontierTyping :
        BudgetRefinementHasType budgetIncompleteRefutedIotaContext
          (.var 1) (.app (signatureFrontier (.var 10)) (.var 2)) := by
      exact Presentation.HasType.var 1
    have obstructionTyping :
        BudgetRefinementHasType budgetIncompleteRefutedIotaContext
          (.var 0) (.app (signatureObstruction (.var 10)) (.var 2)) := by
      exact Presentation.HasType.var 0
    have afterJudgment := Presentation.HasType.appElim
      (Presentation.HasType.var (R := budgetRefinementRules)
        (Γ := budgetIncompleteRefutedIotaContext) (3 : Fin 11))
      judgmentTyping
    have afterFrontier := Presentation.HasType.appElim afterJudgment
      frontierTyping
    have target := Presentation.HasType.appElim afterFrontier
      obstructionTyping
    convert target using 1
    all_goals decide
  evidence := by
    change BudgetRefinementIotaEvidence 11 budgetIncompleteRefutedIotaLeft
      budgetIncompleteRefutedIotaRight
    unfold budgetIncompleteRefutedIotaLeft
      budgetIncompleteRefutedIotaRight budgetIncompleteRefutedIotaBefore
      budgetIncompleteRefutedIotaAfter
      budgetIncompleteRefutedIotaRefinement
    exact BudgetRefinementIotaEvidence.incompleteRefuted
      (.var 10) (.var 9) (.var 8) (.var 7) (.var 6) (.var 5)
      (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

def budgetIncompleteRefutedIotaSchema :
    IotaSchema emptyRules rawBudgetRefinementSignature
      proofRelevantBudgetRefinementComputation 11 where
  context := budgetIncompleteRefutedIotaContext
  left := budgetIncompleteRefutedIotaLeft
  right := budgetIncompleteRefutedIotaRight
  type := budgetIncompleteRefutedIotaType
  receipt := budgetIncompleteRefutedIotaReceipt

def budgetRefinementEliminateAtParameters_applicationHead :
    ApplicationHead budgetRefinementEliminateName
      budgetRefinementEliminateAtParameters :=
  .app (.app (.app (.app (.app (.app (.app (.app .const)))))))

noncomputable def budgetRefinementEliminateAtBinaryIota_applicationHead :
    ApplicationHead budgetRefinementEliminateName
      (Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk
            budgetRefinementEliminateAtParameters))) :=
  ((budgetRefinementEliminateAtParameters_applicationHead.rename wk).rename
    wk).rename wk

noncomputable def budgetRefinementEliminateAtUnaryIota_applicationHead :
    ApplicationHead budgetRefinementEliminateName
      (Presentation.rename wk
        (Presentation.rename wk budgetRefinementEliminateAtParameters)) :=
  (budgetRefinementEliminateAtParameters_applicationHead.rename wk).rename wk

def budgetEstablishedApp_constantOccurrence
    (signature judgment beforeEvidence afterEvidence : Tower.Tm n) :
    ConstantOccurrence budgetEstablishedName
      (budgetEstablishedApp signature judgment beforeEvidence
        afterEvidence) :=
  .appFunction (.appFunction (.appFunction (.appFunction .here)))

def budgetRefutedApp_constantOccurrence
    (signature judgment beforeObstruction afterObstruction : Tower.Tm n) :
    ConstantOccurrence budgetRefutedName
      (budgetRefutedApp signature judgment beforeObstruction
        afterObstruction) :=
  .appFunction (.appFunction (.appFunction (.appFunction .here)))

def budgetOutsideFragmentApp_constantOccurrence
    (signature judgment reason : Tower.Tm n) :
    ConstantOccurrence budgetOutsideFragmentName
      (budgetOutsideFragmentApp signature judgment reason) :=
  .appFunction (.appFunction (.appFunction .here))

def budgetIncompleteApp_constantOccurrence
    (signature judgment beforeFrontier afterFrontier : Tower.Tm n) :
    ConstantOccurrence budgetIncompleteName
      (budgetIncompleteApp signature judgment beforeFrontier
        afterFrontier) :=
  .appFunction (.appFunction (.appFunction (.appFunction .here)))

def budgetIncompleteEstablishedApp_constantOccurrence
    (signature judgment frontier evidence : Tower.Tm n) :
    ConstantOccurrence budgetIncompleteEstablishedName
      (budgetIncompleteEstablishedApp signature judgment frontier
        evidence) :=
  .appFunction (.appFunction (.appFunction (.appFunction .here)))

def budgetIncompleteRefutedApp_constantOccurrence
    (signature judgment frontier obstruction : Tower.Tm n) :
    ConstantOccurrence budgetIncompleteRefutedName
      (budgetIncompleteRefutedApp signature judgment frontier
        obstruction) :=
  .appFunction (.appFunction (.appFunction (.appFunction .here)))

noncomputable def budgetEstablishedIotaClause :
    IotaClause emptyRules rawBudgetRefinementSignature
      proofRelevantBudgetRefinementComputation
      (budgetRefinementConstructors.map ConstructorSpec.name)
      budgetRefinementEliminatorSpec.name where
  constructorName := budgetEstablishedName
  constructorDeclared := by
    simp [budgetRefinementConstructors, budgetEstablishedConstructorSpec,
      budgetRefutedConstructorSpec, budgetOutsideFragmentConstructorSpec,
      budgetIncompleteConstructorSpec,
      budgetIncompleteEstablishedConstructorSpec,
      budgetIncompleteRefutedConstructorSpec]
  arity := 11
  schema := budgetEstablishedIotaSchema
  eliminatorHead :=
    .app (.app (.app (.app
      budgetRefinementEliminateAtBinaryIota_applicationHead)))
  constructorOccurrence :=
    .appArgument
      (budgetEstablishedApp_constantOccurrence
        (.var 10) (.var 2) (.var 1) (.var 0))

noncomputable def budgetRefutedIotaClause :
    IotaClause emptyRules rawBudgetRefinementSignature
      proofRelevantBudgetRefinementComputation
      (budgetRefinementConstructors.map ConstructorSpec.name)
      budgetRefinementEliminatorSpec.name where
  constructorName := budgetRefutedName
  constructorDeclared := by
    simp [budgetRefinementConstructors, budgetEstablishedConstructorSpec,
      budgetRefutedConstructorSpec, budgetOutsideFragmentConstructorSpec,
      budgetIncompleteConstructorSpec,
      budgetIncompleteEstablishedConstructorSpec,
      budgetIncompleteRefutedConstructorSpec]
  arity := 11
  schema := budgetRefutedIotaSchema
  eliminatorHead :=
    .app (.app (.app (.app
      budgetRefinementEliminateAtBinaryIota_applicationHead)))
  constructorOccurrence :=
    .appArgument
      (budgetRefutedApp_constantOccurrence
        (.var 10) (.var 2) (.var 1) (.var 0))

noncomputable def budgetOutsideFragmentIotaClause :
    IotaClause emptyRules rawBudgetRefinementSignature
      proofRelevantBudgetRefinementComputation
      (budgetRefinementConstructors.map ConstructorSpec.name)
      budgetRefinementEliminatorSpec.name where
  constructorName := budgetOutsideFragmentName
  constructorDeclared := by
    simp [budgetRefinementConstructors, budgetEstablishedConstructorSpec,
      budgetRefutedConstructorSpec, budgetOutsideFragmentConstructorSpec,
      budgetIncompleteConstructorSpec,
      budgetIncompleteEstablishedConstructorSpec,
      budgetIncompleteRefutedConstructorSpec]
  arity := 10
  schema := budgetOutsideFragmentIotaSchema
  eliminatorHead :=
    .app (.app (.app (.app
      budgetRefinementEliminateAtUnaryIota_applicationHead)))
  constructorOccurrence :=
    .appArgument
      (budgetOutsideFragmentApp_constantOccurrence
        (.var 9) (.var 1) (.var 0))

noncomputable def budgetIncompleteIotaClause :
    IotaClause emptyRules rawBudgetRefinementSignature
      proofRelevantBudgetRefinementComputation
      (budgetRefinementConstructors.map ConstructorSpec.name)
      budgetRefinementEliminatorSpec.name where
  constructorName := budgetIncompleteName
  constructorDeclared := by
    simp [budgetRefinementConstructors, budgetEstablishedConstructorSpec,
      budgetRefutedConstructorSpec, budgetOutsideFragmentConstructorSpec,
      budgetIncompleteConstructorSpec,
      budgetIncompleteEstablishedConstructorSpec,
      budgetIncompleteRefutedConstructorSpec]
  arity := 11
  schema := budgetIncompleteIotaSchema
  eliminatorHead :=
    .app (.app (.app (.app
      budgetRefinementEliminateAtBinaryIota_applicationHead)))
  constructorOccurrence :=
    .appArgument
      (budgetIncompleteApp_constantOccurrence
        (.var 10) (.var 2) (.var 1) (.var 0))

noncomputable def budgetIncompleteEstablishedIotaClause :
    IotaClause emptyRules rawBudgetRefinementSignature
      proofRelevantBudgetRefinementComputation
      (budgetRefinementConstructors.map ConstructorSpec.name)
      budgetRefinementEliminatorSpec.name where
  constructorName := budgetIncompleteEstablishedName
  constructorDeclared := by
    simp [budgetRefinementConstructors, budgetEstablishedConstructorSpec,
      budgetRefutedConstructorSpec, budgetOutsideFragmentConstructorSpec,
      budgetIncompleteConstructorSpec,
      budgetIncompleteEstablishedConstructorSpec,
      budgetIncompleteRefutedConstructorSpec]
  arity := 11
  schema := budgetIncompleteEstablishedIotaSchema
  eliminatorHead :=
    .app (.app (.app (.app
      budgetRefinementEliminateAtBinaryIota_applicationHead)))
  constructorOccurrence :=
    .appArgument
      (budgetIncompleteEstablishedApp_constantOccurrence
        (.var 10) (.var 2) (.var 1) (.var 0))

noncomputable def budgetIncompleteRefutedIotaClause :
    IotaClause emptyRules rawBudgetRefinementSignature
      proofRelevantBudgetRefinementComputation
      (budgetRefinementConstructors.map ConstructorSpec.name)
      budgetRefinementEliminatorSpec.name where
  constructorName := budgetIncompleteRefutedName
  constructorDeclared := by
    simp [budgetRefinementConstructors, budgetEstablishedConstructorSpec,
      budgetRefutedConstructorSpec, budgetOutsideFragmentConstructorSpec,
      budgetIncompleteConstructorSpec,
      budgetIncompleteEstablishedConstructorSpec,
      budgetIncompleteRefutedConstructorSpec]
  arity := 11
  schema := budgetIncompleteRefutedIotaSchema
  eliminatorHead :=
    .app (.app (.app (.app
      budgetRefinementEliminateAtBinaryIota_applicationHead)))
  constructorOccurrence :=
    .appArgument
      (budgetIncompleteRefutedApp_constantOccurrence
        (.var 10) (.var 2) (.var 1) (.var 0))

noncomputable def budgetRefinementIotaClauses :
    List (IotaClause emptyRules rawBudgetRefinementSignature
      proofRelevantBudgetRefinementComputation
      (budgetRefinementConstructors.map ConstructorSpec.name)
      budgetRefinementEliminatorSpec.name) :=
  [budgetEstablishedIotaClause, budgetRefutedIotaClause,
    budgetOutsideFragmentIotaClause, budgetIncompleteIotaClause,
    budgetIncompleteEstablishedIotaClause,
    budgetIncompleteRefutedIotaClause]

/-- A formed, strictly-positive, proof-relevant declaration of the
fixed-authority budget order.  Its six computation schemas preserve the
transition witness; raw preservation remains separate from candidacy. -/
noncomputable def budgetRefinementCandidate : Candidate emptyRules where
  signature := rawBudgetRefinementSignature
  formed := rawBudgetRefinementSignature_formed
  computation := proofRelevantBudgetRefinementComputation
  computationSupport := rfl
  familyName := budgetRefinementName
  familyParameterCount := 1
  familyIndexCount := 3
  familyType := budgetRefinementType
  familyDeclared := typeOf_budgetRefinement
  constructors := budgetRefinementConstructors
  constructorNamesNodup := by
    change [budgetEstablishedName, budgetRefutedName,
      budgetOutsideFragmentName, budgetIncompleteName,
      budgetIncompleteEstablishedName,
      budgetIncompleteRefutedName].Nodup
    decide
  familyNotConstructor := by
    intro constructor membership
    simp only [budgetRefinementConstructors, List.mem_cons,
      List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  eliminator := budgetRefinementEliminatorSpec
  eliminatorNotFamily := by decide
  eliminatorNotConstructor := by
    intro constructor membership
    simp only [budgetRefinementConstructors, List.mem_cons,
      List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  iotaClauses := budgetRefinementIotaClauses
  constructorsComputed := by
    intro constructorName membership
    simp [budgetRefinementConstructors, budgetEstablishedConstructorSpec,
      budgetRefutedConstructorSpec, budgetOutsideFragmentConstructorSpec,
      budgetIncompleteConstructorSpec,
      budgetIncompleteEstablishedConstructorSpec,
      budgetIncompleteRefutedConstructorSpec] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [budgetRefinementIotaClauses, budgetEstablishedIotaClause,
        budgetRefutedIotaClause, budgetOutsideFragmentIotaClause,
        budgetIncompleteIotaClause,
        budgetIncompleteEstablishedIotaClause,
        budgetIncompleteRefutedIotaClause]

/-! ### Semantic positive and negative controls -/

universe u v w x

/-- More budget may turn a resource frontier into positive evidence. -/
def budgetIncompleteResolvesEstablished
    {Established : Type u} {Refuted : Type v}
    {Boundary : Type w} {Incomplete : Type x}
    (frontier : Incomplete) (evidence : Established) :
    Mettapedia.TypeTheory.AuthorityTheory.Outcome.BudgetRefinementEvidence
      (Refuted := Refuted) (Boundary := Boundary)
      (.incomplete frontier) (.established evidence) :=
  .incompleteEstablished frontier evidence

/-- More budget may instead expose a checked obstruction. -/
def budgetIncompleteResolvesRefuted
    {Established : Type u} {Refuted : Type v}
    {Boundary : Type w} {Incomplete : Type x}
    (frontier : Incomplete) (obstruction : Refuted) :
    Mettapedia.TypeTheory.AuthorityTheory.Outcome.BudgetRefinementEvidence
      (Established := Established) (Boundary := Boundary)
      (.incomplete frontier) (.refuted obstruction) :=
  .incompleteRefuted frontier obstruction

/-- Fixed-authority budget growth cannot cross an authority boundary. -/
theorem budgetOutsideToEstablished_forbidden
    {Established : Type u} {Refuted : Type v}
    {Boundary : Type w} {Incomplete : Type x}
    (reason : Boundary) (evidence : Established) :
    Mettapedia.TypeTheory.AuthorityTheory.Outcome.BudgetRefinementEvidence
      (Refuted := Refuted) (Incomplete := Incomplete)
      (.outsideFragment reason) (.established evidence) → False := by
  intro refinement
  cases refinement

/-- A settled positive result cannot become a refutation merely by adding
budget to the same authority. -/
theorem budgetEstablishedToRefuted_forbidden
    {Established : Type u} {Refuted : Type v}
    {Boundary : Type w} {Incomplete : Type x}
    (evidence : Established) (obstruction : Refuted) :
    Mettapedia.TypeTheory.AuthorityTheory.Outcome.BudgetRefinementEvidence
      (Boundary := Boundary) (Incomplete := Incomplete)
      (.established evidence) (.refuted obstruction) → False := by
  intro refinement
  cases refinement

/-- Even boundary preservation retains the exact reason rather than only
its status tag. -/
theorem budgetOutsideReason_cannot_change
    {Established : Type u} {Refuted : Type v}
    {Boundary : Type w} {Incomplete : Type x}
    {before after : Boundary} (different : before ≠ after) :
    Mettapedia.TypeTheory.AuthorityTheory.Outcome.BudgetRefinementEvidence
      (Established := Established) (Refuted := Refuted)
      (Incomplete := Incomplete)
      (.outsideFragment before) (.outsideFragment after) → False := by
  intro refinement
  cases refinement
  exact different rfl

end Intrinsic

#print axioms Intrinsic.rawBudgetRefinementSignature_formed
#print axioms Intrinsic.budgetEstablishedIotaReceipt
#print axioms Intrinsic.budgetRefutedIotaReceipt
#print axioms Intrinsic.budgetOutsideFragmentIotaReceipt
#print axioms Intrinsic.budgetIncompleteIotaReceipt
#print axioms Intrinsic.budgetIncompleteEstablishedIotaReceipt
#print axioms Intrinsic.budgetIncompleteRefutedIotaReceipt
#print axioms Intrinsic.budgetRefinementCandidate
#print axioms Intrinsic.budgetRefinementInFunctionDomain_not_strictlyPositive
#print axioms Intrinsic.budgetOutsideToEstablished_forbidden
#print axioms Intrinsic.budgetEstablishedToRefuted_forbidden
#print axioms Intrinsic.budgetOutsideReason_cannot_change

end InternalAuthorityMetatheory
end Mettapedia.Languages.MeTTa.PureKernel.Universe
