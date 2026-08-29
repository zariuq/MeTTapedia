import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.IntrinsicRefinementAxis

/-!
# Intrinsic axis-indexed refinement evidence

This module internalizes budget growth and authority growth as fibres of one
proof-relevant indexed family.  The outcome signature is a uniform parameter;
the refinement axis, judgment, and endpoint outcomes are indices.  Illegal
transitions therefore have no constructor, while legal transitions retain
their evidence.

The construction is independent of any checker, guest language, or runtime.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace InternalAuthorityMetatheory
namespace Intrinsic

open Presentation
open Presentation.SchemaElaboration
open Presentation.Declaration
open Presentation.Declaration.ComputationAuthority
open Presentation.Declaration.IndexedFamily

def axisRefinementLevel : LevelExpr := outcomeLevel
def axisRefinementMotiveLevel : LevelExpr := .param 18

def axisRefinementName : DeclName := `Prime.Authority.Refines
def axisEstablishedName : DeclName :=
  `Prime.Authority.Refines.established
def axisRefutedName : DeclName := `Prime.Authority.Refines.refuted
def axisIncompleteName : DeclName := `Prime.Authority.Refines.incomplete
def budgetOutsideRefinementName : DeclName :=
  `Prime.Authority.Refines.budgetOutsideFragment
def budgetIncompleteEstablishedRefinementName : DeclName :=
  `Prime.Authority.Refines.budgetIncompleteEstablished
def budgetIncompleteRefutedRefinementName : DeclName :=
  `Prime.Authority.Refines.budgetIncompleteRefuted
def authorityOutsideRefinementName : DeclName :=
  `Prime.Authority.Refines.authorityOutsideFragment
def authorityOutsideEstablishedRefinementName : DeclName :=
  `Prime.Authority.Refines.authorityOutsideEstablished
def authorityOutsideRefutedRefinementName : DeclName :=
  `Prime.Authority.Refines.authorityOutsideRefuted
def authorityOutsideIncompleteRefinementName : DeclName :=
  `Prime.Authority.Refines.authorityOutsideIncomplete
def axisRefinementEliminateName : DeclName :=
  `Prime.Authority.Refines.eliminate

/-! ## Applications -/

def axisRefinementApp
    (signature axis judgment before after : Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app
        (.app
          (.app (.const axisRefinementName) signature)
          axis)
        judgment)
      before)
    after

def axisEstablishedApp
    (signature axis judgment beforeEvidence afterEvidence : Tower.Tm n) :
    Tower.Tm n :=
  .app
    (.app
      (.app
        (.app
          (.app (.const axisEstablishedName) signature)
          axis)
        judgment)
      beforeEvidence)
    afterEvidence

def axisRefutedApp
    (signature axis judgment beforeObstruction afterObstruction : Tower.Tm n) :
    Tower.Tm n :=
  .app
    (.app
      (.app
        (.app
          (.app (.const axisRefutedName) signature)
          axis)
        judgment)
      beforeObstruction)
    afterObstruction

def axisIncompleteApp
    (signature axis judgment beforeFrontier afterFrontier : Tower.Tm n) :
    Tower.Tm n :=
  .app
    (.app
      (.app
        (.app
          (.app (.const axisIncompleteName) signature)
          axis)
        judgment)
      beforeFrontier)
    afterFrontier

def budgetOutsideRefinementApp
    (signature judgment reason : Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app (.const budgetOutsideRefinementName) signature)
      judgment)
    reason

def budgetIncompleteEstablishedRefinementApp
    (signature judgment frontier evidence : Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app
        (.app (.const budgetIncompleteEstablishedRefinementName) signature)
        judgment)
      frontier)
    evidence

def budgetIncompleteRefutedRefinementApp
    (signature judgment frontier obstruction : Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app
        (.app (.const budgetIncompleteRefutedRefinementName) signature)
        judgment)
      frontier)
    obstruction

def authorityOutsideRefinementApp
    (signature judgment beforeReason afterReason : Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app
        (.app (.const authorityOutsideRefinementName) signature)
        judgment)
      beforeReason)
    afterReason

def authorityOutsideEstablishedRefinementApp
    (signature judgment reason evidence : Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app
        (.app (.const authorityOutsideEstablishedRefinementName) signature)
        judgment)
      reason)
    evidence

def authorityOutsideRefutedRefinementApp
    (signature judgment reason obstruction : Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app
        (.app (.const authorityOutsideRefutedRefinementName) signature)
        judgment)
      reason)
    obstruction

def authorityOutsideIncompleteRefinementApp
    (signature judgment reason frontier : Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app
        (.app (.const authorityOutsideIncompleteRefinementName) signature)
        judgment)
      reason)
    frontier

@[simp] theorem rename_axisRefinementApp (renameMap : Ren n m)
    (signature axis judgment before after : Tower.Tm n) :
    Presentation.rename renameMap
        (axisRefinementApp signature axis judgment before after) =
      axisRefinementApp
        (Presentation.rename renameMap signature)
        (Presentation.rename renameMap axis)
        (Presentation.rename renameMap judgment)
        (Presentation.rename renameMap before)
        (Presentation.rename renameMap after) :=
  rfl

@[simp] theorem subst_axisRefinementApp
    (substitution : Sub Tower.Head n m)
    (signature axis judgment before after : Tower.Tm n) :
    Presentation.subst substitution
        (axisRefinementApp signature axis judgment before after) =
      axisRefinementApp
        (Presentation.subst substitution signature)
        (Presentation.subst substitution axis)
        (Presentation.subst substitution judgment)
        (Presentation.subst substitution before)
        (Presentation.subst substitution after) :=
  rfl

/-! ## Family and constructor types -/

/-- `Refines : (S : OutcomeSignature) → RefinementAxis → (j : S.J) →
    Outcome S j → Outcome S j → U`. -/
def axisRefinementBodyType : Tower.Tm 1 :=
  .pi refinementAxisTm
    (.pi (signatureJudgment (.var 1))
      (.pi (outcomeApp (.var 2) (.var 0))
        (.pi (outcomeApp (.var 3) (.var 1))
          (sortTm axisRefinementLevel))))

def axisRefinementType : Tower.Tm 0 :=
  .pi outcomeSignatureType axisRefinementBodyType

/-- Common settled-positive transition, polymorphic in the refinement axis. -/
def axisEstablishedBodyType : Tower.Tm 1 :=
  .pi refinementAxisTm
    (.pi (signatureJudgment (.var 1))
      (.pi (.app (signatureEvidence (.var 2)) (.var 0))
        (.pi (.app (signatureEvidence (.var 3)) (.var 1))
          (axisRefinementApp (.var 4) (.var 3) (.var 2)
            (establishedApp (.var 4) (.var 2) (.var 1))
            (establishedApp (.var 4) (.var 2) (.var 0))))))

def axisEstablishedType : Tower.Tm 0 :=
  .pi outcomeSignatureType axisEstablishedBodyType

/-- Common settled-negative transition, polymorphic in the refinement axis. -/
def axisRefutedBodyType : Tower.Tm 1 :=
  .pi refinementAxisTm
    (.pi (signatureJudgment (.var 1))
      (.pi (.app (signatureObstruction (.var 2)) (.var 0))
        (.pi (.app (signatureObstruction (.var 3)) (.var 1))
          (axisRefinementApp (.var 4) (.var 3) (.var 2)
            (refutedApp (.var 4) (.var 2) (.var 1))
            (refutedApp (.var 4) (.var 2) (.var 0))))))

def axisRefutedType : Tower.Tm 0 :=
  .pi outcomeSignatureType axisRefutedBodyType

/-- Common resource-frontier transition, polymorphic in the refinement axis. -/
def axisIncompleteBodyType : Tower.Tm 1 :=
  .pi refinementAxisTm
    (.pi (signatureJudgment (.var 1))
      (.pi (.app (signatureFrontier (.var 2)) (.var 0))
        (.pi (.app (signatureFrontier (.var 3)) (.var 1))
          (axisRefinementApp (.var 4) (.var 3) (.var 2)
            (incompleteApp (.var 4) (.var 2) (.var 1))
            (incompleteApp (.var 4) (.var 2) (.var 0))))))

def axisIncompleteType : Tower.Tm 0 :=
  .pi outcomeSignatureType axisIncompleteBodyType

/-- Budget growth preserves the recognized-fragment boundary and its reason. -/
def budgetOutsideRefinementBodyType : Tower.Tm 1 :=
  .pi (signatureJudgment (.var 0))
    (.pi (.app (signatureBoundary (.var 1)) (.var 0))
      (axisRefinementApp (.var 2) refinementAxisBudgetTm (.var 1)
        (outsideFragmentApp (.var 2) (.var 1) (.var 0))
        (outsideFragmentApp (.var 2) (.var 1) (.var 0))))

def budgetOutsideRefinementType : Tower.Tm 0 :=
  .pi outcomeSignatureType budgetOutsideRefinementBodyType

def budgetIncompleteEstablishedRefinementBodyType : Tower.Tm 1 :=
  .pi (signatureJudgment (.var 0))
    (.pi (.app (signatureFrontier (.var 1)) (.var 0))
      (.pi (.app (signatureEvidence (.var 2)) (.var 1))
        (axisRefinementApp (.var 3) refinementAxisBudgetTm (.var 2)
          (incompleteApp (.var 3) (.var 2) (.var 1))
          (establishedApp (.var 3) (.var 2) (.var 0)))))

def budgetIncompleteEstablishedRefinementType : Tower.Tm 0 :=
  .pi outcomeSignatureType budgetIncompleteEstablishedRefinementBodyType

def budgetIncompleteRefutedRefinementBodyType : Tower.Tm 1 :=
  .pi (signatureJudgment (.var 0))
    (.pi (.app (signatureFrontier (.var 1)) (.var 0))
      (.pi (.app (signatureObstruction (.var 2)) (.var 1))
        (axisRefinementApp (.var 3) refinementAxisBudgetTm (.var 2)
          (incompleteApp (.var 3) (.var 2) (.var 1))
          (refutedApp (.var 3) (.var 2) (.var 0)))))

def budgetIncompleteRefutedRefinementType : Tower.Tm 0 :=
  .pi outcomeSignatureType budgetIncompleteRefutedRefinementBodyType

/-- Authority growth may change one recognized-fragment boundary reason into
another while remaining outside the currently implemented fragment. -/
def authorityOutsideRefinementBodyType : Tower.Tm 1 :=
  .pi (signatureJudgment (.var 0))
    (.pi (.app (signatureBoundary (.var 1)) (.var 0))
      (.pi (.app (signatureBoundary (.var 2)) (.var 1))
        (axisRefinementApp (.var 3) refinementAxisAuthorityTm (.var 2)
          (outsideFragmentApp (.var 3) (.var 2) (.var 1))
          (outsideFragmentApp (.var 3) (.var 2) (.var 0)))))

def authorityOutsideRefinementType : Tower.Tm 0 :=
  .pi outcomeSignatureType authorityOutsideRefinementBodyType

def authorityOutsideEstablishedRefinementBodyType : Tower.Tm 1 :=
  .pi (signatureJudgment (.var 0))
    (.pi (.app (signatureBoundary (.var 1)) (.var 0))
      (.pi (.app (signatureEvidence (.var 2)) (.var 1))
        (axisRefinementApp (.var 3) refinementAxisAuthorityTm (.var 2)
          (outsideFragmentApp (.var 3) (.var 2) (.var 1))
          (establishedApp (.var 3) (.var 2) (.var 0)))))

def authorityOutsideEstablishedRefinementType : Tower.Tm 0 :=
  .pi outcomeSignatureType authorityOutsideEstablishedRefinementBodyType

def authorityOutsideRefutedRefinementBodyType : Tower.Tm 1 :=
  .pi (signatureJudgment (.var 0))
    (.pi (.app (signatureBoundary (.var 1)) (.var 0))
      (.pi (.app (signatureObstruction (.var 2)) (.var 1))
        (axisRefinementApp (.var 3) refinementAxisAuthorityTm (.var 2)
          (outsideFragmentApp (.var 3) (.var 2) (.var 1))
          (refutedApp (.var 3) (.var 2) (.var 0)))))

def authorityOutsideRefutedRefinementType : Tower.Tm 0 :=
  .pi outcomeSignatureType authorityOutsideRefutedRefinementBodyType

def authorityOutsideIncompleteRefinementBodyType : Tower.Tm 1 :=
  .pi (signatureJudgment (.var 0))
    (.pi (.app (signatureBoundary (.var 1)) (.var 0))
      (.pi (.app (signatureFrontier (.var 2)) (.var 1))
        (axisRefinementApp (.var 3) refinementAxisAuthorityTm (.var 2)
          (outsideFragmentApp (.var 3) (.var 2) (.var 1))
          (incompleteApp (.var 3) (.var 2) (.var 0)))))

def authorityOutsideIncompleteRefinementType : Tower.Tm 0 :=
  .pi outcomeSignatureType authorityOutsideIncompleteRefinementBodyType

/-! ## Dependent eliminator type -/

def axisRefinementMotiveApp
    (motive axis judgment before after refinement : Tower.Tm n) :
    Tower.Tm n :=
  .app
    (.app
      (.app
        (.app
          (.app motive axis)
          judgment)
        before)
      after)
    refinement

def axisRefinementMotiveType : Tower.Tm 1 :=
  .pi refinementAxisTm
    (.pi (signatureJudgment (.var 1))
      (.pi (outcomeApp (.var 2) (.var 0))
        (.pi (outcomeApp (.var 3) (.var 1))
          (.pi
            (axisRefinementApp (.var 4) (.var 3) (.var 2)
              (.var 1) (.var 0))
            (sortTm axisRefinementMotiveLevel)))))

def axisEstablishedCaseType : Tower.Tm 2 :=
  .pi refinementAxisTm
    (.pi (signatureJudgment (.var 2))
      (.pi (.app (signatureEvidence (.var 3)) (.var 0))
        (.pi (.app (signatureEvidence (.var 4)) (.var 1))
          (axisRefinementMotiveApp (.var 4) (.var 3) (.var 2)
            (establishedApp (.var 5) (.var 2) (.var 1))
            (establishedApp (.var 5) (.var 2) (.var 0))
            (axisEstablishedApp (.var 5) (.var 3) (.var 2)
              (.var 1) (.var 0))))))

def axisRefutedCaseType : Tower.Tm 2 :=
  .pi refinementAxisTm
    (.pi (signatureJudgment (.var 2))
      (.pi (.app (signatureObstruction (.var 3)) (.var 0))
        (.pi (.app (signatureObstruction (.var 4)) (.var 1))
          (axisRefinementMotiveApp (.var 4) (.var 3) (.var 2)
            (refutedApp (.var 5) (.var 2) (.var 1))
            (refutedApp (.var 5) (.var 2) (.var 0))
            (axisRefutedApp (.var 5) (.var 3) (.var 2)
              (.var 1) (.var 0))))))

def axisIncompleteCaseType : Tower.Tm 2 :=
  .pi refinementAxisTm
    (.pi (signatureJudgment (.var 2))
      (.pi (.app (signatureFrontier (.var 3)) (.var 0))
        (.pi (.app (signatureFrontier (.var 4)) (.var 1))
          (axisRefinementMotiveApp (.var 4) (.var 3) (.var 2)
            (incompleteApp (.var 5) (.var 2) (.var 1))
            (incompleteApp (.var 5) (.var 2) (.var 0))
            (axisIncompleteApp (.var 5) (.var 3) (.var 2)
              (.var 1) (.var 0))))))

def budgetOutsideRefinementCaseType : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (.app (signatureBoundary (.var 2)) (.var 0))
      (axisRefinementMotiveApp (.var 2) refinementAxisBudgetTm (.var 1)
        (outsideFragmentApp (.var 3) (.var 1) (.var 0))
        (outsideFragmentApp (.var 3) (.var 1) (.var 0))
        (budgetOutsideRefinementApp (.var 3) (.var 1) (.var 0))))

def budgetIncompleteEstablishedRefinementCaseType : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (.app (signatureFrontier (.var 2)) (.var 0))
      (.pi (.app (signatureEvidence (.var 3)) (.var 1))
        (axisRefinementMotiveApp (.var 3) refinementAxisBudgetTm (.var 2)
          (incompleteApp (.var 4) (.var 2) (.var 1))
          (establishedApp (.var 4) (.var 2) (.var 0))
          (budgetIncompleteEstablishedRefinementApp
            (.var 4) (.var 2) (.var 1) (.var 0)))))

def budgetIncompleteRefutedRefinementCaseType : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (.app (signatureFrontier (.var 2)) (.var 0))
      (.pi (.app (signatureObstruction (.var 3)) (.var 1))
        (axisRefinementMotiveApp (.var 3) refinementAxisBudgetTm (.var 2)
          (incompleteApp (.var 4) (.var 2) (.var 1))
          (refutedApp (.var 4) (.var 2) (.var 0))
          (budgetIncompleteRefutedRefinementApp
            (.var 4) (.var 2) (.var 1) (.var 0)))))

def authorityOutsideRefinementCaseType : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (.app (signatureBoundary (.var 2)) (.var 0))
      (.pi (.app (signatureBoundary (.var 3)) (.var 1))
        (axisRefinementMotiveApp (.var 3) refinementAxisAuthorityTm (.var 2)
          (outsideFragmentApp (.var 4) (.var 2) (.var 1))
          (outsideFragmentApp (.var 4) (.var 2) (.var 0))
          (authorityOutsideRefinementApp
            (.var 4) (.var 2) (.var 1) (.var 0)))))

def authorityOutsideEstablishedRefinementCaseType : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (.app (signatureBoundary (.var 2)) (.var 0))
      (.pi (.app (signatureEvidence (.var 3)) (.var 1))
        (axisRefinementMotiveApp (.var 3) refinementAxisAuthorityTm (.var 2)
          (outsideFragmentApp (.var 4) (.var 2) (.var 1))
          (establishedApp (.var 4) (.var 2) (.var 0))
          (authorityOutsideEstablishedRefinementApp
            (.var 4) (.var 2) (.var 1) (.var 0)))))

def authorityOutsideRefutedRefinementCaseType : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (.app (signatureBoundary (.var 2)) (.var 0))
      (.pi (.app (signatureObstruction (.var 3)) (.var 1))
        (axisRefinementMotiveApp (.var 3) refinementAxisAuthorityTm (.var 2)
          (outsideFragmentApp (.var 4) (.var 2) (.var 1))
          (refutedApp (.var 4) (.var 2) (.var 0))
          (authorityOutsideRefutedRefinementApp
            (.var 4) (.var 2) (.var 1) (.var 0)))))

def authorityOutsideIncompleteRefinementCaseType : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (.app (signatureBoundary (.var 2)) (.var 0))
      (.pi (.app (signatureFrontier (.var 3)) (.var 1))
        (axisRefinementMotiveApp (.var 3) refinementAxisAuthorityTm (.var 2)
          (outsideFragmentApp (.var 4) (.var 2) (.var 1))
          (incompleteApp (.var 4) (.var 2) (.var 0))
          (authorityOutsideIncompleteRefinementApp
            (.var 4) (.var 2) (.var 1) (.var 0)))))

def axisRefutedCaseAfterEstablished : Tower.Tm 3 :=
  Presentation.rename wk axisRefutedCaseType

def axisIncompleteCaseAfterTwo : Tower.Tm 4 :=
  Presentation.rename wk (Presentation.rename wk axisIncompleteCaseType)

def budgetOutsideCaseAfterThree : Tower.Tm 5 :=
  Presentation.rename wk
    (Presentation.rename wk
      (Presentation.rename wk budgetOutsideRefinementCaseType))

def budgetIncompleteEstablishedCaseAfterFour : Tower.Tm 6 :=
  Presentation.rename wk
    (Presentation.rename wk
      (Presentation.rename wk
        (Presentation.rename wk
          budgetIncompleteEstablishedRefinementCaseType)))

def budgetIncompleteRefutedCaseAfterFive : Tower.Tm 7 :=
  Presentation.rename wk
    (Presentation.rename wk
      (Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk
            budgetIncompleteRefutedRefinementCaseType))))

def authorityOutsideCaseAfterSix : Tower.Tm 8 :=
  Presentation.rename wk
    (Presentation.rename wk
      (Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk
            (Presentation.rename wk authorityOutsideRefinementCaseType)))))

def authorityOutsideEstablishedCaseAfterSeven : Tower.Tm 9 :=
  Presentation.rename wk
    (Presentation.rename wk
      (Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk
            (Presentation.rename wk
              (Presentation.rename wk
                authorityOutsideEstablishedRefinementCaseType))))))

def authorityOutsideRefutedCaseAfterEight : Tower.Tm 10 :=
  Presentation.rename wk
    (Presentation.rename wk
      (Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk
            (Presentation.rename wk
              (Presentation.rename wk
                (Presentation.rename wk
                  authorityOutsideRefutedRefinementCaseType)))))))

def authorityOutsideIncompleteCaseAfterNine : Tower.Tm 11 :=
  Presentation.rename wk
    (Presentation.rename wk
      (Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk
            (Presentation.rename wk
              (Presentation.rename wk
                (Presentation.rename wk
                  (Presentation.rename wk
                    authorityOutsideIncompleteRefinementCaseType))))))))

/-- In context `S, motive, ten cases`, eliminate every indexed witness. -/
def axisRefinementEliminateResultType : Tower.Tm 12 :=
  .pi refinementAxisTm
    (.pi (signatureJudgment (.var 12))
      (.pi (outcomeApp (.var 13) (.var 0))
        (.pi (outcomeApp (.var 14) (.var 1))
          (.pi
            (axisRefinementApp (.var 15) (.var 3) (.var 2)
              (.var 1) (.var 0))
            (axisRefinementMotiveApp (.var 15) (.var 4) (.var 3)
              (.var 2) (.var 1) (.var 0))))))

def axisRefinementEliminateBodyType : Tower.Tm 1 :=
  .pi axisRefinementMotiveType
    (.pi axisEstablishedCaseType
      (.pi axisRefutedCaseAfterEstablished
        (.pi axisIncompleteCaseAfterTwo
          (.pi budgetOutsideCaseAfterThree
            (.pi budgetIncompleteEstablishedCaseAfterFour
              (.pi budgetIncompleteRefutedCaseAfterFive
                (.pi authorityOutsideCaseAfterSix
                  (.pi authorityOutsideEstablishedCaseAfterSeven
                    (.pi authorityOutsideRefutedCaseAfterEight
                      (.pi authorityOutsideIncompleteCaseAfterNine
                        axisRefinementEliminateResultType))))))))))

def axisRefinementEliminateType : Tower.Tm 0 :=
  .pi outcomeSignatureType axisRefinementEliminateBodyType

/-! ## Proof-relevant computation carrier -/

/-- The ten branches are bundled only in the Lean presentation API.  The
object term remains the ordinary curried eliminator application. -/
structure AxisRefinementBranches (n : Nat) where
  established : Tower.Tm n
  refuted : Tower.Tm n
  incomplete : Tower.Tm n
  budgetOutside : Tower.Tm n
  budgetIncompleteEstablished : Tower.Tm n
  budgetIncompleteRefuted : Tower.Tm n
  authorityOutside : Tower.Tm n
  authorityOutsideEstablished : Tower.Tm n
  authorityOutsideRefuted : Tower.Tm n
  authorityOutsideIncomplete : Tower.Tm n

def AxisRefinementBranches.rename (branches : AxisRefinementBranches n)
    (renameMap : Ren n m) : AxisRefinementBranches m where
  established := Presentation.rename renameMap branches.established
  refuted := Presentation.rename renameMap branches.refuted
  incomplete := Presentation.rename renameMap branches.incomplete
  budgetOutside := Presentation.rename renameMap branches.budgetOutside
  budgetIncompleteEstablished :=
    Presentation.rename renameMap branches.budgetIncompleteEstablished
  budgetIncompleteRefuted :=
    Presentation.rename renameMap branches.budgetIncompleteRefuted
  authorityOutside :=
    Presentation.rename renameMap branches.authorityOutside
  authorityOutsideEstablished :=
    Presentation.rename renameMap branches.authorityOutsideEstablished
  authorityOutsideRefuted :=
    Presentation.rename renameMap branches.authorityOutsideRefuted
  authorityOutsideIncomplete :=
    Presentation.rename renameMap branches.authorityOutsideIncomplete

def AxisRefinementBranches.substitute
    (branches : AxisRefinementBranches n)
    (substitution : Sub Tower.Head n m) : AxisRefinementBranches m where
  established := Presentation.subst substitution branches.established
  refuted := Presentation.subst substitution branches.refuted
  incomplete := Presentation.subst substitution branches.incomplete
  budgetOutside := Presentation.subst substitution branches.budgetOutside
  budgetIncompleteEstablished :=
    Presentation.subst substitution branches.budgetIncompleteEstablished
  budgetIncompleteRefuted :=
    Presentation.subst substitution branches.budgetIncompleteRefuted
  authorityOutside :=
    Presentation.subst substitution branches.authorityOutside
  authorityOutsideEstablished :=
    Presentation.subst substitution branches.authorityOutsideEstablished
  authorityOutsideRefuted :=
    Presentation.subst substitution branches.authorityOutsideRefuted
  authorityOutsideIncomplete :=
    Presentation.subst substitution branches.authorityOutsideIncomplete

def axisRefinementEliminateAtBranches
    (signature motive : Tower.Tm n)
    (branches : AxisRefinementBranches n) : Tower.Tm n :=
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
                        (.app (.const axisRefinementEliminateName) signature)
                        motive)
                      branches.established)
                    branches.refuted)
                  branches.incomplete)
                branches.budgetOutside)
              branches.budgetIncompleteEstablished)
            branches.budgetIncompleteRefuted)
          branches.authorityOutside)
        branches.authorityOutsideEstablished)
      branches.authorityOutsideRefuted)
    branches.authorityOutsideIncomplete

def axisRefinementEliminateApp
    (signature motive : Tower.Tm n)
    (branches : AxisRefinementBranches n)
    (axis judgment before after refinement : Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app
        (.app
          (.app (axisRefinementEliminateAtBranches signature motive branches)
            axis)
          judgment)
        before)
      after)
    refinement

@[simp] theorem rename_axisRefinementEliminateAtBranches
    (renameMap : Ren n m) (signature motive : Tower.Tm n)
    (branches : AxisRefinementBranches n) :
    Presentation.rename renameMap
        (axisRefinementEliminateAtBranches signature motive branches) =
      axisRefinementEliminateAtBranches
        (Presentation.rename renameMap signature)
        (Presentation.rename renameMap motive)
        (branches.rename renameMap) :=
  rfl

@[simp] theorem subst_axisRefinementEliminateAtBranches
    (substitution : Sub Tower.Head n m) (signature motive : Tower.Tm n)
    (branches : AxisRefinementBranches n) :
    Presentation.subst substitution
        (axisRefinementEliminateAtBranches signature motive branches) =
      axisRefinementEliminateAtBranches
        (Presentation.subst substitution signature)
        (Presentation.subst substitution motive)
        (branches.substitute substitution) :=
  rfl

@[simp] theorem rename_axisRefinementEliminateApp
    (renameMap : Ren n m) (signature motive : Tower.Tm n)
    (branches : AxisRefinementBranches n)
    (axis judgment before after refinement : Tower.Tm n) :
    Presentation.rename renameMap
        (axisRefinementEliminateApp signature motive branches axis judgment
          before after refinement) =
      axisRefinementEliminateApp
        (Presentation.rename renameMap signature)
        (Presentation.rename renameMap motive)
        (branches.rename renameMap)
        (Presentation.rename renameMap axis)
        (Presentation.rename renameMap judgment)
        (Presentation.rename renameMap before)
        (Presentation.rename renameMap after)
        (Presentation.rename renameMap refinement) :=
  rfl

@[simp] theorem subst_axisRefinementEliminateApp
    (substitution : Sub Tower.Head n m) (signature motive : Tower.Tm n)
    (branches : AxisRefinementBranches n)
    (axis judgment before after refinement : Tower.Tm n) :
    Presentation.subst substitution
        (axisRefinementEliminateApp signature motive branches axis judgment
          before after refinement) =
      axisRefinementEliminateApp
        (Presentation.subst substitution signature)
        (Presentation.subst substitution motive)
        (branches.substitute substitution)
        (Presentation.subst substitution axis)
        (Presentation.subst substitution judgment)
        (Presentation.subst substitution before)
        (Presentation.subst substitution after)
        (Presentation.subst substitution refinement) :=
  rfl

inductive AxisRefinementIotaEvidence (n : Nat) :
    Tower.Tm n → Tower.Tm n → Type where
  | established (signature motive : Tower.Tm n)
      (branches : AxisRefinementBranches n)
      (axis judgment beforeEvidence afterEvidence : Tower.Tm n) :
      AxisRefinementIotaEvidence n
        (axisRefinementEliminateApp signature motive branches axis judgment
          (establishedApp signature judgment beforeEvidence)
          (establishedApp signature judgment afterEvidence)
          (axisEstablishedApp signature axis judgment beforeEvidence
            afterEvidence))
        (applyArgs branches.established
          [axis, judgment, beforeEvidence, afterEvidence])
  | refuted (signature motive : Tower.Tm n)
      (branches : AxisRefinementBranches n)
      (axis judgment beforeObstruction afterObstruction : Tower.Tm n) :
      AxisRefinementIotaEvidence n
        (axisRefinementEliminateApp signature motive branches axis judgment
          (refutedApp signature judgment beforeObstruction)
          (refutedApp signature judgment afterObstruction)
          (axisRefutedApp signature axis judgment beforeObstruction
            afterObstruction))
        (applyArgs branches.refuted
          [axis, judgment, beforeObstruction, afterObstruction])
  | incomplete (signature motive : Tower.Tm n)
      (branches : AxisRefinementBranches n)
      (axis judgment beforeFrontier afterFrontier : Tower.Tm n) :
      AxisRefinementIotaEvidence n
        (axisRefinementEliminateApp signature motive branches axis judgment
          (incompleteApp signature judgment beforeFrontier)
          (incompleteApp signature judgment afterFrontier)
          (axisIncompleteApp signature axis judgment beforeFrontier
            afterFrontier))
        (applyArgs branches.incomplete
          [axis, judgment, beforeFrontier, afterFrontier])
  | budgetOutside (signature motive : Tower.Tm n)
      (branches : AxisRefinementBranches n)
      (judgment reason : Tower.Tm n) :
      AxisRefinementIotaEvidence n
        (axisRefinementEliminateApp signature motive branches
          refinementAxisBudgetTm judgment
          (outsideFragmentApp signature judgment reason)
          (outsideFragmentApp signature judgment reason)
          (budgetOutsideRefinementApp signature judgment reason))
        (applyArgs branches.budgetOutside [judgment, reason])
  | budgetIncompleteEstablished (signature motive : Tower.Tm n)
      (branches : AxisRefinementBranches n)
      (judgment frontier evidence : Tower.Tm n) :
      AxisRefinementIotaEvidence n
        (axisRefinementEliminateApp signature motive branches
          refinementAxisBudgetTm judgment
          (incompleteApp signature judgment frontier)
          (establishedApp signature judgment evidence)
          (budgetIncompleteEstablishedRefinementApp signature judgment
            frontier evidence))
        (applyArgs branches.budgetIncompleteEstablished
          [judgment, frontier, evidence])
  | budgetIncompleteRefuted (signature motive : Tower.Tm n)
      (branches : AxisRefinementBranches n)
      (judgment frontier obstruction : Tower.Tm n) :
      AxisRefinementIotaEvidence n
        (axisRefinementEliminateApp signature motive branches
          refinementAxisBudgetTm judgment
          (incompleteApp signature judgment frontier)
          (refutedApp signature judgment obstruction)
          (budgetIncompleteRefutedRefinementApp signature judgment
            frontier obstruction))
        (applyArgs branches.budgetIncompleteRefuted
          [judgment, frontier, obstruction])
  | authorityOutside (signature motive : Tower.Tm n)
      (branches : AxisRefinementBranches n)
      (judgment beforeReason afterReason : Tower.Tm n) :
      AxisRefinementIotaEvidence n
        (axisRefinementEliminateApp signature motive branches
          refinementAxisAuthorityTm judgment
          (outsideFragmentApp signature judgment beforeReason)
          (outsideFragmentApp signature judgment afterReason)
          (authorityOutsideRefinementApp signature judgment beforeReason
            afterReason))
        (applyArgs branches.authorityOutside
          [judgment, beforeReason, afterReason])
  | authorityOutsideEstablished (signature motive : Tower.Tm n)
      (branches : AxisRefinementBranches n)
      (judgment reason evidence : Tower.Tm n) :
      AxisRefinementIotaEvidence n
        (axisRefinementEliminateApp signature motive branches
          refinementAxisAuthorityTm judgment
          (outsideFragmentApp signature judgment reason)
          (establishedApp signature judgment evidence)
          (authorityOutsideEstablishedRefinementApp signature judgment
            reason evidence))
        (applyArgs branches.authorityOutsideEstablished
          [judgment, reason, evidence])
  | authorityOutsideRefuted (signature motive : Tower.Tm n)
      (branches : AxisRefinementBranches n)
      (judgment reason obstruction : Tower.Tm n) :
      AxisRefinementIotaEvidence n
        (axisRefinementEliminateApp signature motive branches
          refinementAxisAuthorityTm judgment
          (outsideFragmentApp signature judgment reason)
          (refutedApp signature judgment obstruction)
          (authorityOutsideRefutedRefinementApp signature judgment
            reason obstruction))
        (applyArgs branches.authorityOutsideRefuted
          [judgment, reason, obstruction])
  | authorityOutsideIncomplete (signature motive : Tower.Tm n)
      (branches : AxisRefinementBranches n)
      (judgment reason frontier : Tower.Tm n) :
      AxisRefinementIotaEvidence n
        (axisRefinementEliminateApp signature motive branches
          refinementAxisAuthorityTm judgment
          (outsideFragmentApp signature judgment reason)
          (incompleteApp signature judgment frontier)
          (authorityOutsideIncompleteRefinementApp signature judgment
            reason frontier))
        (applyArgs branches.authorityOutsideIncomplete
          [judgment, reason, frontier])

def AxisRefinementIotaEvidence.rename {left right : Tower.Tm n}
    (step : AxisRefinementIotaEvidence n left right)
    (renameMap : Ren n m) :
    AxisRefinementIotaEvidence m
      (Presentation.rename renameMap left)
      (Presentation.rename renameMap right) := by
  cases step with
  | established signature motive branches axis judgment before after =>
      simpa [Presentation.rename, AxisRefinementBranches.rename, axisEstablishedApp,
        establishedApp] using
        (AxisRefinementIotaEvidence.established
          (Presentation.rename renameMap signature)
          (Presentation.rename renameMap motive)
          (branches.rename renameMap)
          (Presentation.rename renameMap axis)
          (Presentation.rename renameMap judgment)
          (Presentation.rename renameMap before)
          (Presentation.rename renameMap after))
  | refuted signature motive branches axis judgment before after =>
      simpa [Presentation.rename, AxisRefinementBranches.rename, axisRefutedApp, refutedApp] using
        (AxisRefinementIotaEvidence.refuted
          (Presentation.rename renameMap signature)
          (Presentation.rename renameMap motive)
          (branches.rename renameMap)
          (Presentation.rename renameMap axis)
          (Presentation.rename renameMap judgment)
          (Presentation.rename renameMap before)
          (Presentation.rename renameMap after))
  | incomplete signature motive branches axis judgment before after =>
      simpa [Presentation.rename, AxisRefinementBranches.rename, axisIncompleteApp,
        incompleteApp] using
        (AxisRefinementIotaEvidence.incomplete
          (Presentation.rename renameMap signature)
          (Presentation.rename renameMap motive)
          (branches.rename renameMap)
          (Presentation.rename renameMap axis)
          (Presentation.rename renameMap judgment)
          (Presentation.rename renameMap before)
          (Presentation.rename renameMap after))
  | budgetOutside signature motive branches judgment reason =>
      simpa [Presentation.rename, AxisRefinementBranches.rename,
        budgetOutsideRefinementApp, outsideFragmentApp] using
        (AxisRefinementIotaEvidence.budgetOutside
          (Presentation.rename renameMap signature)
          (Presentation.rename renameMap motive)
          (branches.rename renameMap)
          (Presentation.rename renameMap judgment)
          (Presentation.rename renameMap reason))
  | budgetIncompleteEstablished signature motive branches judgment frontier
      evidence =>
      simpa [Presentation.rename, AxisRefinementBranches.rename,
        budgetIncompleteEstablishedRefinementApp, incompleteApp,
        establishedApp] using
        (AxisRefinementIotaEvidence.budgetIncompleteEstablished
          (Presentation.rename renameMap signature)
          (Presentation.rename renameMap motive)
          (branches.rename renameMap)
          (Presentation.rename renameMap judgment)
          (Presentation.rename renameMap frontier)
          (Presentation.rename renameMap evidence))
  | budgetIncompleteRefuted signature motive branches judgment frontier
      obstruction =>
      simpa [Presentation.rename, AxisRefinementBranches.rename,
        budgetIncompleteRefutedRefinementApp, incompleteApp,
        refutedApp] using
        (AxisRefinementIotaEvidence.budgetIncompleteRefuted
          (Presentation.rename renameMap signature)
          (Presentation.rename renameMap motive)
          (branches.rename renameMap)
          (Presentation.rename renameMap judgment)
          (Presentation.rename renameMap frontier)
          (Presentation.rename renameMap obstruction))
  | authorityOutside signature motive branches judgment before after =>
      simpa [Presentation.rename, AxisRefinementBranches.rename,
        authorityOutsideRefinementApp, outsideFragmentApp] using
        (AxisRefinementIotaEvidence.authorityOutside
          (Presentation.rename renameMap signature)
          (Presentation.rename renameMap motive)
          (branches.rename renameMap)
          (Presentation.rename renameMap judgment)
          (Presentation.rename renameMap before)
          (Presentation.rename renameMap after))
  | authorityOutsideEstablished signature motive branches judgment reason
      evidence =>
      simpa [Presentation.rename, AxisRefinementBranches.rename,
        authorityOutsideEstablishedRefinementApp, outsideFragmentApp,
        establishedApp] using
        (AxisRefinementIotaEvidence.authorityOutsideEstablished
          (Presentation.rename renameMap signature)
          (Presentation.rename renameMap motive)
          (branches.rename renameMap)
          (Presentation.rename renameMap judgment)
          (Presentation.rename renameMap reason)
          (Presentation.rename renameMap evidence))
  | authorityOutsideRefuted signature motive branches judgment reason
      obstruction =>
      simpa [Presentation.rename, AxisRefinementBranches.rename,
        authorityOutsideRefutedRefinementApp, outsideFragmentApp,
        refutedApp] using
        (AxisRefinementIotaEvidence.authorityOutsideRefuted
          (Presentation.rename renameMap signature)
          (Presentation.rename renameMap motive)
          (branches.rename renameMap)
          (Presentation.rename renameMap judgment)
          (Presentation.rename renameMap reason)
          (Presentation.rename renameMap obstruction))
  | authorityOutsideIncomplete signature motive branches judgment reason
      frontier =>
      simpa [Presentation.rename, AxisRefinementBranches.rename,
        authorityOutsideIncompleteRefinementApp, outsideFragmentApp,
        incompleteApp] using
        (AxisRefinementIotaEvidence.authorityOutsideIncomplete
          (Presentation.rename renameMap signature)
          (Presentation.rename renameMap motive)
          (branches.rename renameMap)
          (Presentation.rename renameMap judgment)
          (Presentation.rename renameMap reason)
          (Presentation.rename renameMap frontier))

def AxisRefinementIotaEvidence.substitute {left right : Tower.Tm n}
    (step : AxisRefinementIotaEvidence n left right)
    (substitution : Sub Tower.Head n m) :
    AxisRefinementIotaEvidence m
      (Presentation.subst substitution left)
      (Presentation.subst substitution right) := by
  cases step with
  | established signature motive branches axis judgment before after =>
      simpa [Presentation.subst, AxisRefinementBranches.substitute, axisEstablishedApp,
        establishedApp] using
        (AxisRefinementIotaEvidence.established
          (Presentation.subst substitution signature)
          (Presentation.subst substitution motive)
          (branches.substitute substitution)
          (Presentation.subst substitution axis)
          (Presentation.subst substitution judgment)
          (Presentation.subst substitution before)
          (Presentation.subst substitution after))
  | refuted signature motive branches axis judgment before after =>
      simpa [Presentation.subst, AxisRefinementBranches.substitute, axisRefutedApp,
        refutedApp] using
        (AxisRefinementIotaEvidence.refuted
          (Presentation.subst substitution signature)
          (Presentation.subst substitution motive)
          (branches.substitute substitution)
          (Presentation.subst substitution axis)
          (Presentation.subst substitution judgment)
          (Presentation.subst substitution before)
          (Presentation.subst substitution after))
  | incomplete signature motive branches axis judgment before after =>
      simpa [Presentation.subst, AxisRefinementBranches.substitute, axisIncompleteApp,
        incompleteApp] using
        (AxisRefinementIotaEvidence.incomplete
          (Presentation.subst substitution signature)
          (Presentation.subst substitution motive)
          (branches.substitute substitution)
          (Presentation.subst substitution axis)
          (Presentation.subst substitution judgment)
          (Presentation.subst substitution before)
          (Presentation.subst substitution after))
  | budgetOutside signature motive branches judgment reason =>
      simpa [Presentation.subst, AxisRefinementBranches.substitute,
        budgetOutsideRefinementApp, outsideFragmentApp] using
        (AxisRefinementIotaEvidence.budgetOutside
          (Presentation.subst substitution signature)
          (Presentation.subst substitution motive)
          (branches.substitute substitution)
          (Presentation.subst substitution judgment)
          (Presentation.subst substitution reason))
  | budgetIncompleteEstablished signature motive branches judgment frontier
      evidence =>
      simpa [Presentation.subst, AxisRefinementBranches.substitute,
        budgetIncompleteEstablishedRefinementApp, incompleteApp,
        establishedApp] using
        (AxisRefinementIotaEvidence.budgetIncompleteEstablished
          (Presentation.subst substitution signature)
          (Presentation.subst substitution motive)
          (branches.substitute substitution)
          (Presentation.subst substitution judgment)
          (Presentation.subst substitution frontier)
          (Presentation.subst substitution evidence))
  | budgetIncompleteRefuted signature motive branches judgment frontier
      obstruction =>
      simpa [Presentation.subst, AxisRefinementBranches.substitute,
        budgetIncompleteRefutedRefinementApp, incompleteApp,
        refutedApp] using
        (AxisRefinementIotaEvidence.budgetIncompleteRefuted
          (Presentation.subst substitution signature)
          (Presentation.subst substitution motive)
          (branches.substitute substitution)
          (Presentation.subst substitution judgment)
          (Presentation.subst substitution frontier)
          (Presentation.subst substitution obstruction))
  | authorityOutside signature motive branches judgment before after =>
      simpa [Presentation.subst, AxisRefinementBranches.substitute,
        authorityOutsideRefinementApp, outsideFragmentApp] using
        (AxisRefinementIotaEvidence.authorityOutside
          (Presentation.subst substitution signature)
          (Presentation.subst substitution motive)
          (branches.substitute substitution)
          (Presentation.subst substitution judgment)
          (Presentation.subst substitution before)
          (Presentation.subst substitution after))
  | authorityOutsideEstablished signature motive branches judgment reason
      evidence =>
      simpa [Presentation.subst, AxisRefinementBranches.substitute,
        authorityOutsideEstablishedRefinementApp, outsideFragmentApp,
        establishedApp] using
        (AxisRefinementIotaEvidence.authorityOutsideEstablished
          (Presentation.subst substitution signature)
          (Presentation.subst substitution motive)
          (branches.substitute substitution)
          (Presentation.subst substitution judgment)
          (Presentation.subst substitution reason)
          (Presentation.subst substitution evidence))
  | authorityOutsideRefuted signature motive branches judgment reason
      obstruction =>
      simpa [Presentation.subst, AxisRefinementBranches.substitute,
        authorityOutsideRefutedRefinementApp, outsideFragmentApp,
        refutedApp] using
        (AxisRefinementIotaEvidence.authorityOutsideRefuted
          (Presentation.subst substitution signature)
          (Presentation.subst substitution motive)
          (branches.substitute substitution)
          (Presentation.subst substitution judgment)
          (Presentation.subst substitution reason)
          (Presentation.subst substitution obstruction))
  | authorityOutsideIncomplete signature motive branches judgment reason
      frontier =>
      simpa [Presentation.subst, AxisRefinementBranches.substitute,
        authorityOutsideIncompleteRefinementApp, outsideFragmentApp,
        incompleteApp] using
        (AxisRefinementIotaEvidence.authorityOutsideIncomplete
          (Presentation.subst substitution signature)
          (Presentation.subst substitution motive)
          (branches.substitute substitution)
          (Presentation.subst substitution judgment)
          (Presentation.subst substitution reason)
          (Presentation.subst substitution frontier))

def proofRelevantAxisRefinementComputation :
    ProofRelevantRootComputation Tower.Head where
  Evidence := AxisRefinementIotaEvidence _
  rename := by
    intro n m renameMap left right step
    exact step.rename renameMap
  substitute := by
    intro n m substitution left right step
    exact step.substitute substitution

def axisRefinementComputation : RootComputation Tower.Head :=
  proofRelevantAxisRefinementComputation.support

/-! ## Declaration signature -/

def axisRefinementDeclarations : List (DeclName × Entry Tower.Head) :=
  [(axisRefinementName, { type := axisRefinementType }),
   (axisEstablishedName, { type := axisEstablishedType }),
   (axisRefutedName, { type := axisRefutedType }),
   (axisIncompleteName, { type := axisIncompleteType }),
   (budgetOutsideRefinementName,
      { type := budgetOutsideRefinementType }),
   (budgetIncompleteEstablishedRefinementName,
      { type := budgetIncompleteEstablishedRefinementType }),
   (budgetIncompleteRefutedRefinementName,
      { type := budgetIncompleteRefutedRefinementType }),
   (authorityOutsideRefinementName,
      { type := authorityOutsideRefinementType }),
   (authorityOutsideEstablishedRefinementName,
      { type := authorityOutsideEstablishedRefinementType }),
   (authorityOutsideRefutedRefinementName,
      { type := authorityOutsideRefutedRefinementType }),
   (authorityOutsideIncompleteRefinementName,
      { type := authorityOutsideIncompleteRefinementType }),
   (axisRefinementEliminateName,
      { type := axisRefinementEliminateType })]

def rawAxisRefinementSignature : Signature Tower.Head where
  entries := (Signature.ofList axisRefinementDeclarations).entries
  computation := axisRefinementComputation

abbrev axisRefinementRules : Rules Tower.Head :=
  extendRules refinementAxisRules rawAxisRefinementSignature

@[simp] theorem typeOf_axisRefinement :
    rawAxisRefinementSignature.typeOf? axisRefinementName =
      some axisRefinementType := by
  simp [rawAxisRefinementSignature, axisRefinementDeclarations,
    axisRefinementName, axisEstablishedName, axisRefutedName,
    axisIncompleteName, budgetOutsideRefinementName,
    budgetIncompleteEstablishedRefinementName,
    budgetIncompleteRefutedRefinementName,
    authorityOutsideRefinementName,
    authorityOutsideEstablishedRefinementName,
    authorityOutsideRefutedRefinementName,
    authorityOutsideIncompleteRefinementName,
    axisRefinementEliminateName, Signature.ofList, Signature.insert,
    Signature.typeOf?]

@[simp] theorem typeOf_axisEstablished :
    rawAxisRefinementSignature.typeOf? axisEstablishedName =
      some axisEstablishedType := by
  simp [rawAxisRefinementSignature, axisRefinementDeclarations,
    axisRefinementName, axisEstablishedName, axisRefutedName,
    axisIncompleteName, budgetOutsideRefinementName,
    budgetIncompleteEstablishedRefinementName,
    budgetIncompleteRefutedRefinementName,
    authorityOutsideRefinementName,
    authorityOutsideEstablishedRefinementName,
    authorityOutsideRefutedRefinementName,
    authorityOutsideIncompleteRefinementName,
    axisRefinementEliminateName, Signature.ofList, Signature.insert,
    Signature.typeOf?]

@[simp] theorem typeOf_axisRefuted :
    rawAxisRefinementSignature.typeOf? axisRefutedName =
      some axisRefutedType := by
  simp [rawAxisRefinementSignature, axisRefinementDeclarations,
    axisRefinementName, axisEstablishedName, axisRefutedName,
    axisIncompleteName, budgetOutsideRefinementName,
    budgetIncompleteEstablishedRefinementName,
    budgetIncompleteRefutedRefinementName,
    authorityOutsideRefinementName,
    authorityOutsideEstablishedRefinementName,
    authorityOutsideRefutedRefinementName,
    authorityOutsideIncompleteRefinementName,
    axisRefinementEliminateName, Signature.ofList, Signature.insert,
    Signature.typeOf?]

@[simp] theorem typeOf_axisIncomplete :
    rawAxisRefinementSignature.typeOf? axisIncompleteName =
      some axisIncompleteType := by
  simp [rawAxisRefinementSignature, axisRefinementDeclarations,
    axisRefinementName, axisEstablishedName, axisRefutedName,
    axisIncompleteName, budgetOutsideRefinementName,
    budgetIncompleteEstablishedRefinementName,
    budgetIncompleteRefutedRefinementName,
    authorityOutsideRefinementName,
    authorityOutsideEstablishedRefinementName,
    authorityOutsideRefutedRefinementName,
    authorityOutsideIncompleteRefinementName,
    axisRefinementEliminateName, Signature.ofList, Signature.insert,
    Signature.typeOf?]

@[simp] theorem typeOf_budgetOutsideRefinement :
    rawAxisRefinementSignature.typeOf? budgetOutsideRefinementName =
      some budgetOutsideRefinementType := by
  simp [rawAxisRefinementSignature, axisRefinementDeclarations,
    axisRefinementName, axisEstablishedName, axisRefutedName,
    axisIncompleteName, budgetOutsideRefinementName,
    budgetIncompleteEstablishedRefinementName,
    budgetIncompleteRefutedRefinementName,
    authorityOutsideRefinementName,
    authorityOutsideEstablishedRefinementName,
    authorityOutsideRefutedRefinementName,
    authorityOutsideIncompleteRefinementName,
    axisRefinementEliminateName, Signature.ofList, Signature.insert,
    Signature.typeOf?]

@[simp] theorem typeOf_budgetIncompleteEstablishedRefinement :
    rawAxisRefinementSignature.typeOf?
        budgetIncompleteEstablishedRefinementName =
      some budgetIncompleteEstablishedRefinementType := by
  simp [rawAxisRefinementSignature, axisRefinementDeclarations,
    axisRefinementName, axisEstablishedName, axisRefutedName,
    axisIncompleteName, budgetOutsideRefinementName,
    budgetIncompleteEstablishedRefinementName,
    budgetIncompleteRefutedRefinementName,
    authorityOutsideRefinementName,
    authorityOutsideEstablishedRefinementName,
    authorityOutsideRefutedRefinementName,
    authorityOutsideIncompleteRefinementName,
    axisRefinementEliminateName, Signature.ofList, Signature.insert,
    Signature.typeOf?]

@[simp] theorem typeOf_budgetIncompleteRefutedRefinement :
    rawAxisRefinementSignature.typeOf?
        budgetIncompleteRefutedRefinementName =
      some budgetIncompleteRefutedRefinementType := by
  simp [rawAxisRefinementSignature, axisRefinementDeclarations,
    axisRefinementName, axisEstablishedName, axisRefutedName,
    axisIncompleteName, budgetOutsideRefinementName,
    budgetIncompleteEstablishedRefinementName,
    budgetIncompleteRefutedRefinementName,
    authorityOutsideRefinementName,
    authorityOutsideEstablishedRefinementName,
    authorityOutsideRefutedRefinementName,
    authorityOutsideIncompleteRefinementName,
    axisRefinementEliminateName, Signature.ofList, Signature.insert,
    Signature.typeOf?]

@[simp] theorem typeOf_authorityOutsideRefinement :
    rawAxisRefinementSignature.typeOf? authorityOutsideRefinementName =
      some authorityOutsideRefinementType := by
  simp [rawAxisRefinementSignature, axisRefinementDeclarations,
    axisRefinementName, axisEstablishedName, axisRefutedName,
    axisIncompleteName, budgetOutsideRefinementName,
    budgetIncompleteEstablishedRefinementName,
    budgetIncompleteRefutedRefinementName,
    authorityOutsideRefinementName,
    authorityOutsideEstablishedRefinementName,
    authorityOutsideRefutedRefinementName,
    authorityOutsideIncompleteRefinementName,
    axisRefinementEliminateName, Signature.ofList, Signature.insert,
    Signature.typeOf?]

@[simp] theorem typeOf_authorityOutsideEstablishedRefinement :
    rawAxisRefinementSignature.typeOf?
        authorityOutsideEstablishedRefinementName =
      some authorityOutsideEstablishedRefinementType := by
  simp [rawAxisRefinementSignature, axisRefinementDeclarations,
    axisRefinementName, axisEstablishedName, axisRefutedName,
    axisIncompleteName, budgetOutsideRefinementName,
    budgetIncompleteEstablishedRefinementName,
    budgetIncompleteRefutedRefinementName,
    authorityOutsideRefinementName,
    authorityOutsideEstablishedRefinementName,
    authorityOutsideRefutedRefinementName,
    authorityOutsideIncompleteRefinementName,
    axisRefinementEliminateName, Signature.ofList, Signature.insert,
    Signature.typeOf?]

@[simp] theorem typeOf_authorityOutsideRefutedRefinement :
    rawAxisRefinementSignature.typeOf?
        authorityOutsideRefutedRefinementName =
      some authorityOutsideRefutedRefinementType := by
  simp [rawAxisRefinementSignature, axisRefinementDeclarations,
    axisRefinementName, axisEstablishedName, axisRefutedName,
    axisIncompleteName, budgetOutsideRefinementName,
    budgetIncompleteEstablishedRefinementName,
    budgetIncompleteRefutedRefinementName,
    authorityOutsideRefinementName,
    authorityOutsideEstablishedRefinementName,
    authorityOutsideRefutedRefinementName,
    authorityOutsideIncompleteRefinementName,
    axisRefinementEliminateName, Signature.ofList, Signature.insert,
    Signature.typeOf?]

@[simp] theorem typeOf_authorityOutsideIncompleteRefinement :
    rawAxisRefinementSignature.typeOf?
        authorityOutsideIncompleteRefinementName =
      some authorityOutsideIncompleteRefinementType := by
  simp [rawAxisRefinementSignature, axisRefinementDeclarations,
    axisRefinementName, axisEstablishedName, axisRefutedName,
    axisIncompleteName, budgetOutsideRefinementName,
    budgetIncompleteEstablishedRefinementName,
    budgetIncompleteRefutedRefinementName,
    authorityOutsideRefinementName,
    authorityOutsideEstablishedRefinementName,
    authorityOutsideRefutedRefinementName,
    authorityOutsideIncompleteRefinementName,
    axisRefinementEliminateName, Signature.ofList, Signature.insert,
    Signature.typeOf?]

@[simp] theorem typeOf_axisRefinementEliminate :
    rawAxisRefinementSignature.typeOf? axisRefinementEliminateName =
      some axisRefinementEliminateType := by
  simp [rawAxisRefinementSignature, axisRefinementDeclarations,
    axisRefinementName, axisEstablishedName, axisRefutedName,
    axisIncompleteName, budgetOutsideRefinementName,
    budgetIncompleteEstablishedRefinementName,
    budgetIncompleteRefutedRefinementName,
    authorityOutsideRefinementName,
    authorityOutsideEstablishedRefinementName,
    authorityOutsideRefutedRefinementName,
    authorityOutsideIncompleteRefinementName,
    axisRefinementEliminateName, Signature.ofList, Signature.insert,
    Signature.typeOf?]

abbrev AxisRefinementHasType {n : Nat} :=
  @Presentation.HasType Tower.Head axisRefinementRules n

def includeRefinementAxisInAxisRefinement {context : Tower.Ctx n}
    {term type : Tower.Tm n}
    (typing : RefinementAxisHasType context term type) :
    AxisRefinementHasType context term type :=
  Presentation.Declaration.HasType.includeSignature refinementAxisRules
    rawAxisRefinementSignature typing

def includeEmptyInAxisRefinement {context : Tower.Ctx n}
    {term type : Tower.Tm n}
    (typing : EmptyHasType context term type) :
    AxisRefinementHasType context term type :=
  includeRefinementAxisInAxisRefinement
    (includeEmptyInRefinementAxis typing)

def includeOutcomeInAxisRefinement {context : Tower.Ctx n}
    {term type : Tower.Tm n}
    (typing : IntrinsicHasType context term type) :
    AxisRefinementHasType context term type :=
  includeEmptyInAxisRefinement
    (includeReceiptTyping (includeRunTyping (includeOutcomeTyping typing)))

private theorem axisRefinementName_fresh :
    refinementAxisRules.constantType axisRefinementName = none := by
  decide

private theorem axisEstablishedName_fresh :
    refinementAxisRules.constantType axisEstablishedName = none := by
  decide

private theorem axisRefutedName_fresh :
    refinementAxisRules.constantType axisRefutedName = none := by
  decide

private theorem axisIncompleteName_fresh :
    refinementAxisRules.constantType axisIncompleteName = none := by
  decide

private theorem budgetOutsideRefinementName_fresh :
    refinementAxisRules.constantType budgetOutsideRefinementName = none := by
  decide

private theorem budgetIncompleteEstablishedRefinementName_fresh :
    refinementAxisRules.constantType
      budgetIncompleteEstablishedRefinementName = none := by
  decide

private theorem budgetIncompleteRefutedRefinementName_fresh :
    refinementAxisRules.constantType
      budgetIncompleteRefutedRefinementName = none := by
  decide

private theorem authorityOutsideRefinementName_fresh :
    refinementAxisRules.constantType authorityOutsideRefinementName = none := by
  decide

private theorem authorityOutsideEstablishedRefinementName_fresh :
    refinementAxisRules.constantType
      authorityOutsideEstablishedRefinementName = none := by
  decide

private theorem authorityOutsideRefutedRefinementName_fresh :
    refinementAxisRules.constantType
      authorityOutsideRefutedRefinementName = none := by
  decide

private theorem authorityOutsideIncompleteRefinementName_fresh :
    refinementAxisRules.constantType
      authorityOutsideIncompleteRefinementName = none := by
  decide

private theorem axisRefinementEliminateName_fresh :
    refinementAxisRules.constantType axisRefinementEliminateName = none := by
  decide

private theorem declaredAxisRefinementConstant_hasType
    {name : DeclName} {type : Tower.Tm 0}
    (lookup : rawAxisRefinementSignature.typeOf? name = some type)
    (fresh : refinementAxisRules.constantType name = none)
    {context : Tower.Ctx n} :
    AxisRefinementHasType context (.const name) (liftClosed type) := by
  apply Presentation.HasType.const
  change combinedType refinementAxisRules rawAxisRefinementSignature name =
    some type
  exact combinedType_of_signature refinementAxisRules
    rawAxisRefinementSignature fresh lookup

theorem axisRefinementConstant_hasType {context : Tower.Ctx n} :
    AxisRefinementHasType context (.const axisRefinementName)
      (liftClosed axisRefinementType) :=
  declaredAxisRefinementConstant_hasType typeOf_axisRefinement
    axisRefinementName_fresh

theorem axisEstablishedConstant_hasType {context : Tower.Ctx n} :
    AxisRefinementHasType context (.const axisEstablishedName)
      (liftClosed axisEstablishedType) :=
  declaredAxisRefinementConstant_hasType typeOf_axisEstablished
    axisEstablishedName_fresh

theorem axisRefutedConstant_hasType {context : Tower.Ctx n} :
    AxisRefinementHasType context (.const axisRefutedName)
      (liftClosed axisRefutedType) :=
  declaredAxisRefinementConstant_hasType typeOf_axisRefuted
    axisRefutedName_fresh

theorem axisIncompleteConstant_hasType {context : Tower.Ctx n} :
    AxisRefinementHasType context (.const axisIncompleteName)
      (liftClosed axisIncompleteType) :=
  declaredAxisRefinementConstant_hasType typeOf_axisIncomplete
    axisIncompleteName_fresh

theorem budgetOutsideRefinementConstant_hasType
    {context : Tower.Ctx n} :
    AxisRefinementHasType context (.const budgetOutsideRefinementName)
      (liftClosed budgetOutsideRefinementType) :=
  declaredAxisRefinementConstant_hasType typeOf_budgetOutsideRefinement
    budgetOutsideRefinementName_fresh

theorem budgetIncompleteEstablishedRefinementConstant_hasType
    {context : Tower.Ctx n} :
    AxisRefinementHasType context
      (.const budgetIncompleteEstablishedRefinementName)
      (liftClosed budgetIncompleteEstablishedRefinementType) :=
  declaredAxisRefinementConstant_hasType
    typeOf_budgetIncompleteEstablishedRefinement
    budgetIncompleteEstablishedRefinementName_fresh

theorem budgetIncompleteRefutedRefinementConstant_hasType
    {context : Tower.Ctx n} :
    AxisRefinementHasType context
      (.const budgetIncompleteRefutedRefinementName)
      (liftClosed budgetIncompleteRefutedRefinementType) :=
  declaredAxisRefinementConstant_hasType
    typeOf_budgetIncompleteRefutedRefinement
    budgetIncompleteRefutedRefinementName_fresh

theorem authorityOutsideRefinementConstant_hasType
    {context : Tower.Ctx n} :
    AxisRefinementHasType context (.const authorityOutsideRefinementName)
      (liftClosed authorityOutsideRefinementType) :=
  declaredAxisRefinementConstant_hasType typeOf_authorityOutsideRefinement
    authorityOutsideRefinementName_fresh

theorem authorityOutsideEstablishedRefinementConstant_hasType
    {context : Tower.Ctx n} :
    AxisRefinementHasType context
      (.const authorityOutsideEstablishedRefinementName)
      (liftClosed authorityOutsideEstablishedRefinementType) :=
  declaredAxisRefinementConstant_hasType
    typeOf_authorityOutsideEstablishedRefinement
    authorityOutsideEstablishedRefinementName_fresh

theorem authorityOutsideRefutedRefinementConstant_hasType
    {context : Tower.Ctx n} :
    AxisRefinementHasType context
      (.const authorityOutsideRefutedRefinementName)
      (liftClosed authorityOutsideRefutedRefinementType) :=
  declaredAxisRefinementConstant_hasType
    typeOf_authorityOutsideRefutedRefinement
    authorityOutsideRefutedRefinementName_fresh

theorem authorityOutsideIncompleteRefinementConstant_hasType
    {context : Tower.Ctx n} :
    AxisRefinementHasType context
      (.const authorityOutsideIncompleteRefinementName)
      (liftClosed authorityOutsideIncompleteRefinementType) :=
  declaredAxisRefinementConstant_hasType
    typeOf_authorityOutsideIncompleteRefinement
    authorityOutsideIncompleteRefinementName_fresh

theorem axisRefinementEliminateConstant_hasType
    {context : Tower.Ctx n} :
    AxisRefinementHasType context (.const axisRefinementEliminateName)
      (liftClosed axisRefinementEliminateType) :=
  declaredAxisRefinementConstant_hasType typeOf_axisRefinementEliminate
    axisRefinementEliminateName_fresh

def axisRefinementAtSignatureType (signature : Tower.Tm n) :
    Tower.Tm n :=
  .pi refinementAxisTm
    (.pi (signatureJudgment (Presentation.rename wk signature))
      (.pi
        (outcomeApp
          (Presentation.rename wk (Presentation.rename wk signature))
          (.var 0))
        (.pi
          (outcomeApp
            (Presentation.rename wk
              (Presentation.rename wk
                (Presentation.rename wk signature)))
            (.var 1))
          (sortTm axisRefinementLevel))))

@[simp] theorem substitute_axisRefinementBodyType
    (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature)
        axisRefinementBodyType =
      axisRefinementAtSignatureType signature := by
  simp [axisRefinementBodyType, axisRefinementAtSignatureType,
    Presentation.subst]

@[simp] theorem axis_open_under_one_after_two_weakenings
    (argument term : Tower.Tm n) :
    Presentation.subst
        (Presentation.liftSub (Presentation.subst0 argument))
        (Presentation.rename (fun i => wk (wk i)) term) =
      Presentation.rename wk term := by
  rw [← Presentation.rename_comp wk wk term]
  rw [Presentation.subst_liftSub_wk]
  exact congrArg (Presentation.rename wk)
    (Presentation.inst0_rename_wk argument term)

@[simp] theorem axis_open_under_two_after_three_weakenings
    (argument term : Tower.Tm n) :
    Presentation.subst
        (Presentation.liftSub
          (Presentation.liftSub (Presentation.subst0 argument)))
        (Presentation.rename (fun i => wk (wk (wk i))) term) =
      Presentation.rename (fun i => wk (wk i)) term := by
  rw [← Presentation.rename_comp wk (fun i => wk (wk i)) term]
  rw [← Presentation.rename_comp wk wk term]
  rw [open_weakened_under_two]

@[simp] theorem axis_open_under_three_after_four_weakenings
    (argument term : Tower.Tm n) :
    Presentation.subst
        (Presentation.liftSub
          (Presentation.liftSub
            (Presentation.liftSub (Presentation.subst0 argument))))
        (Presentation.rename
          (fun i => wk (wk (wk (wk i)))) term) =
      Presentation.rename (fun i => wk (wk (wk i))) term := by
  rw [← Presentation.rename_comp wk (fun i => wk (wk (wk i))) term]
  rw [← Presentation.rename_comp wk (fun i => wk (wk i)) term]
  rw [← Presentation.rename_comp wk wk term]
  rw [open_weakened_under_three]

@[simp] theorem axis_liftSub_three_singleParameter_two
    (term : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub
          (Presentation.liftSub (fun _ : Fin 1 => term)))
        (2 : Fin 4) = (.var 2 : Tower.Tm (n + 3)) := by
  rfl

@[simp] theorem axis_liftSub_four_singleParameter_three
    (term : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub
          (Presentation.liftSub
            (Presentation.liftSub (fun _ : Fin 1 => term))))
        (3 : Fin 5) = (.var 3 : Tower.Tm (n + 4)) := by
  rfl

@[simp] theorem axis_liftSub_four_singleParameter_two
    (term : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub
          (Presentation.liftSub
            (Presentation.liftSub (fun _ : Fin 1 => term))))
        (2 : Fin 5) = (.var 2 : Tower.Tm (n + 4)) := by
  rfl

theorem axisRefinementApp_hasType {context : Tower.Ctx n}
    {signature axis judgment before after : Tower.Tm n}
    (signatureTyping : AxisRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (axisTyping : AxisRefinementHasType context axis refinementAxisTm)
    (judgmentTyping : AxisRefinementHasType context judgment
      (signatureJudgment signature))
    (beforeTyping : AxisRefinementHasType context before
      (outcomeApp signature judgment))
    (afterTyping : AxisRefinementHasType context after
      (outcomeApp signature judgment)) :
    AxisRefinementHasType context
      (axisRefinementApp signature axis judgment before after)
      (sortTm axisRefinementLevel) := by
  have afterSignature := Presentation.HasType.appElim
    (axisRefinementConstant_hasType (context := context)) signatureTyping
  have afterSignatureNormalized :
      AxisRefinementHasType context
        (.app (.const axisRefinementName) signature)
        (axisRefinementAtSignatureType signature) := by
    simpa only [axisRefinementType, liftClosed,
      inst0_rename_liftRen_elim0,
      substitute_axisRefinementBodyType] using afterSignature
  have afterAxis := Presentation.HasType.appElim
    afterSignatureNormalized axisTyping
  have afterAxisNormalized :
      AxisRefinementHasType context
        (.app (.app (.const axisRefinementName) signature) axis)
        (.pi (signatureJudgment signature)
          (.pi
            (outcomeApp (Presentation.rename wk signature) (.var 0))
            (.pi
              (outcomeApp
                (Presentation.rename wk (Presentation.rename wk signature))
                (.var 1))
              (sortTm axisRefinementLevel)))) := by
    convert afterAxis using 1
    all_goals simp [Presentation.inst0, Presentation.subst]
  have afterJudgment := Presentation.HasType.appElim afterAxisNormalized
    judgmentTyping
  have afterJudgmentNormalized :
      AxisRefinementHasType context
        (.app
          (.app (.app (.const axisRefinementName) signature) axis)
          judgment)
        (.pi (outcomeApp signature judgment)
          (.pi
            (outcomeApp (Presentation.rename wk signature)
              (Presentation.rename wk judgment))
            (sortTm axisRefinementLevel))) := by
    convert afterJudgment using 1
    all_goals simp [Presentation.inst0, Presentation.subst]
  have afterBefore := Presentation.HasType.appElim
    afterJudgmentNormalized beforeTyping
  have afterBeforeNormalized :
      AxisRefinementHasType context
        (.app
          (.app
            (.app (.app (.const axisRefinementName) signature) axis)
            judgment)
          before)
        (.pi (outcomeApp signature judgment)
          (sortTm axisRefinementLevel)) := by
    convert afterBefore using 1
    all_goals simp [Presentation.inst0, Presentation.subst]
  have afterAfter := Presentation.HasType.appElim afterBeforeNormalized
    afterTyping
  convert afterAfter using 1
  all_goals rfl

theorem refinementAxisTm_hasAxisRefinementType
    {context : Tower.Ctx n} :
    AxisRefinementHasType context refinementAxisTm
      (sortTm refinementAxisLevel) :=
  includeRefinementAxisInAxisRefinement refinementAxisTm_hasType

theorem refinementAxisBudgetTm_hasAxisRefinementType
    {context : Tower.Ctx n} :
    AxisRefinementHasType context refinementAxisBudgetTm refinementAxisTm :=
  includeRefinementAxisInAxisRefinement refinementAxisBudgetTm_hasType

theorem refinementAxisAuthorityTm_hasAxisRefinementType
    {context : Tower.Ctx n} :
    AxisRefinementHasType context refinementAxisAuthorityTm refinementAxisTm :=
  includeRefinementAxisInAxisRefinement refinementAxisAuthorityTm_hasType

theorem establishedConstant_hasAxisRefinementType
    {context : Tower.Ctx n} :
    AxisRefinementHasType context (.const establishedName)
      (liftClosed establishedType) :=
  includeOutcomeInAxisRefinement establishedConstant_hasType

theorem refutedConstant_hasAxisRefinementType
    {context : Tower.Ctx n} :
    AxisRefinementHasType context (.const refutedName)
      (liftClosed refutedType) :=
  includeOutcomeInAxisRefinement refutedConstant_hasType

theorem outsideFragmentConstant_hasAxisRefinementType
    {context : Tower.Ctx n} :
    AxisRefinementHasType context (.const outsideFragmentName)
      (liftClosed outsideFragmentType) :=
  includeOutcomeInAxisRefinement outsideFragmentConstant_hasType

theorem incompleteConstant_hasAxisRefinementType
    {context : Tower.Ctx n} :
    AxisRefinementHasType context (.const incompleteName)
      (liftClosed incompleteType) :=
  includeOutcomeInAxisRefinement incompleteConstant_hasType

private theorem outcomeConstructorApp_hasAxisRefinementType
    {context : Tower.Ctx n}
    {constructor : DeclName} {constructorType : Tower.Tm 0}
    {bodyType : Tower.Tm 1}
    {payloadFamily signature judgment witness : Tower.Tm n}
    (constantTyping : AxisRefinementHasType context
      (.const constructor) (liftClosed constructorType))
    (constructorTypeEquation :
      constructorType = .pi outcomeSignatureType bodyType)
    (openedBody : Presentation.subst (fun _ : Fin 1 => signature) bodyType =
      constructorAtSignatureType signature payloadFamily)
    (signatureTyping : AxisRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : AxisRefinementHasType context judgment
      (signatureJudgment signature))
    (witnessTyping : AxisRefinementHasType context witness
      (.app payloadFamily judgment)) :
    AxisRefinementHasType context
      (.app (.app (.app (.const constructor) signature) judgment) witness)
      (outcomeApp signature judgment) := by
  subst constructorType
  have afterSignature := Presentation.HasType.appElim constantTyping
    signatureTyping
  have afterSignatureNormalized :
      AxisRefinementHasType context
        (.app (.const constructor) signature)
        (constructorAtSignatureType signature payloadFamily) := by
    simpa only [liftClosed, inst0_rename_liftRen_elim0,
      openedBody] using afterSignature
  have afterJudgment := Presentation.HasType.appElim
    afterSignatureNormalized judgmentTyping
  have afterJudgmentNormalized :
      AxisRefinementHasType context
        (.app (.app (.const constructor) signature) judgment)
        (arrow (.app payloadFamily judgment)
          (outcomeApp signature judgment)) := by
    simpa only [constructorAtSignatureType, inst0_arrow,
      inst0_familyApplication_wk, inst0_outcomeApplication_wk] using
      afterJudgment
  have afterWitness := Presentation.HasType.appElim
    afterJudgmentNormalized witnessTyping
  simpa only [arrow, inst0_rename_wk] using afterWitness

theorem establishedApp_hasAxisRefinementType {context : Tower.Ctx n}
    {signature judgment witness : Tower.Tm n}
    (signatureTyping : AxisRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : AxisRefinementHasType context judgment
      (signatureJudgment signature))
    (witnessTyping : AxisRefinementHasType context witness
      (.app (signatureEvidence signature) judgment)) :
    AxisRefinementHasType context
      (establishedApp signature judgment witness)
      (outcomeApp signature judgment) := by
  exact outcomeConstructorApp_hasAxisRefinementType
    establishedConstant_hasAxisRefinementType rfl
    (substitute_establishedBodyType signature)
    signatureTyping judgmentTyping witnessTyping

theorem refutedApp_hasAxisRefinementType {context : Tower.Ctx n}
    {signature judgment witness : Tower.Tm n}
    (signatureTyping : AxisRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : AxisRefinementHasType context judgment
      (signatureJudgment signature))
    (witnessTyping : AxisRefinementHasType context witness
      (.app (signatureObstruction signature) judgment)) :
    AxisRefinementHasType context
      (refutedApp signature judgment witness)
      (outcomeApp signature judgment) := by
  exact outcomeConstructorApp_hasAxisRefinementType
    refutedConstant_hasAxisRefinementType rfl
    (substitute_refutedBodyType signature)
    signatureTyping judgmentTyping witnessTyping

theorem outsideFragmentApp_hasAxisRefinementType {context : Tower.Ctx n}
    {signature judgment witness : Tower.Tm n}
    (signatureTyping : AxisRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : AxisRefinementHasType context judgment
      (signatureJudgment signature))
    (witnessTyping : AxisRefinementHasType context witness
      (.app (signatureBoundary signature) judgment)) :
    AxisRefinementHasType context
      (outsideFragmentApp signature judgment witness)
      (outcomeApp signature judgment) := by
  exact outcomeConstructorApp_hasAxisRefinementType
    outsideFragmentConstant_hasAxisRefinementType rfl
    (substitute_outsideFragmentBodyType signature)
    signatureTyping judgmentTyping witnessTyping

theorem incompleteApp_hasAxisRefinementType {context : Tower.Ctx n}
    {signature judgment witness : Tower.Tm n}
    (signatureTyping : AxisRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : AxisRefinementHasType context judgment
      (signatureJudgment signature))
    (witnessTyping : AxisRefinementHasType context witness
      (.app (signatureFrontier signature) judgment)) :
    AxisRefinementHasType context
      (incompleteApp signature judgment witness)
      (outcomeApp signature judgment) := by
  exact outcomeConstructorApp_hasAxisRefinementType
    incompleteConstant_hasAxisRefinementType rfl
    (substitute_incompleteBodyType signature)
    signatureTyping judgmentTyping witnessTyping

/-! ## Formation of the family declaration -/

theorem outcomeSignatureType_hasAxisRefinementType :
    AxisRefinementHasType (.nil : Tower.Ctx 0)
      outcomeSignatureType (sortTm signatureLevel) :=
  includeEmptyInAxisRefinement outcomeSignatureType_hasEmptyType

def axisRefinementContextS : Tower.Ctx 1 :=
  .snoc .nil outcomeSignatureType

def axisRefinementContextSA : Tower.Ctx 2 :=
  .snoc axisRefinementContextS refinementAxisTm

def axisRefinementContextSAJ : Tower.Ctx 3 :=
  .snoc axisRefinementContextSA (signatureJudgment (.var 1))

def axisRefinementContextSAJB : Tower.Ctx 4 :=
  .snoc axisRefinementContextSAJ
    (outcomeApp (.var 2) (.var 0))

def axisRefinementContextSAJBA : Tower.Ctx 5 :=
  .snoc axisRefinementContextSAJB
    (outcomeApp (.var 3) (.var 1))

theorem axisRefinementSignatureVar_hasType :
    AxisRefinementHasType axisRefinementContextS (.var 0)
      (liftClosed outcomeSignatureType) := by
  have variableTyping :=
    (Presentation.HasType.var (R := axisRefinementRules)
      (Γ := axisRefinementContextS) (0 : Fin 1))
  have lookupEquality :
      Presentation.Ctx.lookup axisRefinementContextS (0 : Fin 1) =
        liftClosed outcomeSignatureType := by
    decide
  simpa only [lookupEquality] using variableTyping

theorem axisRefinementSignatureVarInSA_hasType :
    AxisRefinementHasType axisRefinementContextSA (.var 1)
      (liftClosed outcomeSignatureType) := by
  have variableTyping :=
    (Presentation.HasType.var (R := axisRefinementRules)
      (Γ := axisRefinementContextSA) (1 : Fin 2))
  have lookupEquality :
      Presentation.Ctx.lookup axisRefinementContextSA (1 : Fin 2) =
        liftClosed outcomeSignatureType := by
    decide
  simpa only [lookupEquality] using variableTyping

theorem axisRefinementAxisVar_hasType :
    AxisRefinementHasType axisRefinementContextSA (.var 0)
      refinementAxisTm := by
  exact Presentation.HasType.var 0

theorem axisRefinementJudgmentVar_hasType :
    AxisRefinementHasType axisRefinementContextSAJ (.var 0)
      (signatureJudgment (.var 2)) := by
  exact Presentation.HasType.var 0

theorem axisRefinementBeforeVar_hasType :
    AxisRefinementHasType axisRefinementContextSAJB (.var 0)
      (outcomeApp (.var 3) (.var 1)) := by
  exact Presentation.HasType.var 0

theorem axisRefinementAfterVar_hasType :
    AxisRefinementHasType axisRefinementContextSAJBA (.var 0)
      (outcomeApp (.var 4) (.var 2)) := by
  exact Presentation.HasType.var 0

def axisRefinementBodyLevel : LevelExpr :=
  .max refinementAxisLevel
    (.max judgmentLevel
      (.max outcomeLevel
        (.max outcomeLevel (.succ axisRefinementLevel))))

theorem axisRefinementBodyType_hasType :
    AxisRefinementHasType axisRefinementContextS
      axisRefinementBodyType (sortTm axisRefinementBodyLevel) := by
  unfold axisRefinementBodyType axisRefinementBodyLevel
    axisRefinementContextS
  apply Presentation.HasType.piForm
  · exact refinementAxisTm_hasAxisRefinementType
  · exact Tower.IsUniverse.sort refinementAxisLevel
  · apply Presentation.HasType.piForm
    · exact signatureJudgment_hasType
        axisRefinementSignatureVarInSA_hasType
    · exact Tower.IsUniverse.sort judgmentLevel
    · apply Presentation.HasType.piForm
      · apply outcomeApp_hasTypeWith
        · exact includeOutcomeInAxisRefinement outcomeConstant_hasType
        · exact Presentation.HasType.var 2
        · exact Presentation.HasType.var 0
      · exact Tower.IsUniverse.sort outcomeLevel
      · apply Presentation.HasType.piForm
        · apply outcomeApp_hasTypeWith
          · exact includeOutcomeInAxisRefinement outcomeConstant_hasType
          · exact Presentation.HasType.var 3
          · exact Presentation.HasType.var 1
        · exact Tower.IsUniverse.sort outcomeLevel
        · exact Presentation.HasType.headType
            (Tower.HeadTyping.sort axisRefinementLevel)
        · exact Tower.IsUniverse.sort (.succ axisRefinementLevel)
        · exact Tower.Join.sorts outcomeLevel
            (.succ axisRefinementLevel)
      · exact Tower.IsUniverse.sort
          (.max outcomeLevel (.succ axisRefinementLevel))
      · exact Tower.Join.sorts outcomeLevel
          (.max outcomeLevel (.succ axisRefinementLevel))
    · exact Tower.IsUniverse.sort
        (.max outcomeLevel
          (.max outcomeLevel (.succ axisRefinementLevel)))
    · exact Tower.Join.sorts judgmentLevel
        (.max outcomeLevel
          (.max outcomeLevel (.succ axisRefinementLevel)))
  · exact Tower.IsUniverse.sort
      (.max judgmentLevel
        (.max outcomeLevel
          (.max outcomeLevel (.succ axisRefinementLevel))))
  · exact Tower.Join.sorts refinementAxisLevel
      (.max judgmentLevel
        (.max outcomeLevel
          (.max outcomeLevel (.succ axisRefinementLevel))))

def axisRefinementDeclarationLevel : LevelExpr :=
  .max signatureLevel axisRefinementBodyLevel

theorem axisRefinementType_hasType :
    AxisRefinementHasType (.nil : Tower.Ctx 0)
      axisRefinementType (sortTm axisRefinementDeclarationLevel) := by
  unfold axisRefinementType axisRefinementDeclarationLevel
  apply Presentation.HasType.piForm
      outcomeSignatureType_hasAxisRefinementType
      (Tower.IsUniverse.sort signatureLevel)
  · exact axisRefinementBodyType_hasType
  · exact Tower.IsUniverse.sort axisRefinementBodyLevel
  · exact Tower.Join.sorts signatureLevel axisRefinementBodyLevel

/-! ### Formation of fixed-axis constructors -/

def axisNamedOutcomeConstructorApp (constructor : DeclName)
    (signature judgment witness : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.const constructor) signature) judgment) witness

def fixedAxisBinaryAtSignatureType
    (axis : Tower.Tm n) (beforeConstructor afterConstructor : DeclName)
    (signature beforeFamily afterFamily : Tower.Tm n) : Tower.Tm n :=
  .pi (signatureJudgment signature)
    (.pi (.app (Presentation.rename wk beforeFamily) (.var 0))
      (.pi
        (.app
          (Presentation.rename wk (Presentation.rename wk afterFamily))
          (.var 1))
        (axisRefinementApp
          (Presentation.rename wk
            (Presentation.rename wk (Presentation.rename wk signature)))
          (Presentation.rename wk
            (Presentation.rename wk (Presentation.rename wk axis)))
          (.var 2)
          (axisNamedOutcomeConstructorApp beforeConstructor
            (Presentation.rename wk
              (Presentation.rename wk (Presentation.rename wk signature)))
            (.var 2) (.var 1))
          (axisNamedOutcomeConstructorApp afterConstructor
            (Presentation.rename wk
              (Presentation.rename wk (Presentation.rename wk signature)))
            (.var 2) (.var 0)))))

def axisNamedFixedBinaryConstructorApp (constructor : DeclName)
    (signature judgment beforeWitness afterWitness : Tower.Tm n) :
    Tower.Tm n :=
  .app
    (.app
      (.app
        (.app (.const constructor) signature)
        judgment)
      beforeWitness)
    afterWitness

def fixedAxisBinaryAfterJudgmentType
    (axis : Tower.Tm n) (beforeConstructor afterConstructor : DeclName)
    (signature judgment beforeFamily afterFamily : Tower.Tm n) :
    Tower.Tm n :=
  .pi (.app beforeFamily judgment)
    (.pi
      (.app (Presentation.rename wk afterFamily)
        (Presentation.rename wk judgment))
      (axisRefinementApp
        (Presentation.rename wk (Presentation.rename wk signature))
        (Presentation.rename wk (Presentation.rename wk axis))
        (Presentation.rename wk (Presentation.rename wk judgment))
        (axisNamedOutcomeConstructorApp beforeConstructor
          (Presentation.rename wk (Presentation.rename wk signature))
          (Presentation.rename wk (Presentation.rename wk judgment))
          (.var 1))
        (axisNamedOutcomeConstructorApp afterConstructor
          (Presentation.rename wk (Presentation.rename wk signature))
          (Presentation.rename wk (Presentation.rename wk judgment))
          (.var 0))))

def fixedAxisBinaryAfterBeforeType
    (axis : Tower.Tm n) (beforeConstructor afterConstructor : DeclName)
    (signature judgment beforeWitness afterFamily : Tower.Tm n) :
    Tower.Tm n :=
  .pi (.app afterFamily judgment)
    (axisRefinementApp
      (Presentation.rename wk signature)
      (Presentation.rename wk axis)
      (Presentation.rename wk judgment)
      (axisNamedOutcomeConstructorApp beforeConstructor
        (Presentation.rename wk signature)
        (Presentation.rename wk judgment)
        (Presentation.rename wk beforeWitness))
      (axisNamedOutcomeConstructorApp afterConstructor
        (Presentation.rename wk signature)
        (Presentation.rename wk judgment) (.var 0)))

private theorem fixedAxisBinaryConstructorApp_hasType
    {context : Tower.Ctx n}
    {relationConstructor beforeConstructor afterConstructor : DeclName}
    {relationType : Tower.Tm 0} {bodyType : Tower.Tm 1}
    {axis signature judgment beforeWitness afterWitness beforeFamily
      afterFamily : Tower.Tm n}
    (constantTyping : AxisRefinementHasType context
      (.const relationConstructor) (liftClosed relationType))
    (relationTypeEquation :
      relationType = .pi outcomeSignatureType bodyType)
    (openedBody : Presentation.subst (fun _ : Fin 1 => signature) bodyType =
      fixedAxisBinaryAtSignatureType axis beforeConstructor
        afterConstructor signature beforeFamily afterFamily)
    (signatureTyping : AxisRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : AxisRefinementHasType context judgment
      (signatureJudgment signature))
    (beforeTyping : AxisRefinementHasType context beforeWitness
      (.app beforeFamily judgment))
    (afterTyping : AxisRefinementHasType context afterWitness
      (.app afterFamily judgment)) :
    AxisRefinementHasType context
      (axisNamedFixedBinaryConstructorApp relationConstructor signature
        judgment beforeWitness afterWitness)
      (axisRefinementApp signature axis judgment
        (axisNamedOutcomeConstructorApp beforeConstructor signature
          judgment beforeWitness)
        (axisNamedOutcomeConstructorApp afterConstructor signature
          judgment afterWitness)) := by
  subst relationType
  have afterSignature := Presentation.HasType.appElim constantTyping
    signatureTyping
  have afterSignatureNormalized :
      AxisRefinementHasType context
        (.app (.const relationConstructor) signature)
        (fixedAxisBinaryAtSignatureType axis beforeConstructor
          afterConstructor signature beforeFamily afterFamily) := by
    simpa only [liftClosed, inst0_rename_liftRen_elim0,
      openedBody] using afterSignature
  have afterJudgment := Presentation.HasType.appElim
    afterSignatureNormalized judgmentTyping
  have afterJudgmentNormalized :
      AxisRefinementHasType context
        (.app (.app (.const relationConstructor) signature) judgment)
        (fixedAxisBinaryAfterJudgmentType axis beforeConstructor
          afterConstructor signature judgment beforeFamily afterFamily) := by
    convert afterJudgment using 1
    all_goals simp [fixedAxisBinaryAfterJudgmentType,
      axisNamedOutcomeConstructorApp, axisRefinementApp,
      Presentation.inst0, Presentation.subst]
  have afterBefore := Presentation.HasType.appElim afterJudgmentNormalized
    beforeTyping
  have afterBeforeNormalized :
      AxisRefinementHasType context
        (.app
          (.app (.app (.const relationConstructor) signature) judgment)
          beforeWitness)
        (fixedAxisBinaryAfterBeforeType axis beforeConstructor
          afterConstructor signature judgment beforeWitness afterFamily) := by
    convert afterBefore using 1
    all_goals simp [fixedAxisBinaryAfterBeforeType,
      axisNamedOutcomeConstructorApp,
      axisRefinementApp, Presentation.inst0, Presentation.subst]
  have afterAfter := Presentation.HasType.appElim afterBeforeNormalized
    afterTyping
  convert afterAfter using 1
  all_goals simp [axisNamedFixedBinaryConstructorApp,
    axisNamedOutcomeConstructorApp,
    axisRefinementApp, Presentation.inst0, Presentation.subst]

def fixedAxisBinaryContextSJW (beforeFamily : Tower.Tm 1) :
    Tower.Ctx 3 :=
  .snoc
    (.snoc axisRefinementContextS (signatureJudgment (.var 0)))
    (.app (Presentation.rename wk beforeFamily) (.var 0))

def fixedAxisBinaryContextSJWW
    (beforeFamily afterFamily : Tower.Tm 1) : Tower.Ctx 4 :=
  .snoc (fixedAxisBinaryContextSJW beforeFamily)
    (.app
      (Presentation.rename wk (Presentation.rename wk afterFamily))
      (.var 1))

def fixedAxisBinaryAfterLevel (afterLevel : LevelExpr) : LevelExpr :=
  .max afterLevel axisRefinementLevel

def fixedAxisBinaryBeforeLevel
    (beforeLevel afterLevel : LevelExpr) : LevelExpr :=
  .max beforeLevel (fixedAxisBinaryAfterLevel afterLevel)

def fixedAxisBinaryBodyLevel
    (beforeLevel afterLevel : LevelExpr) : LevelExpr :=
  .max judgmentLevel (fixedAxisBinaryBeforeLevel beforeLevel afterLevel)

@[simp] theorem fixedAxis_wk_wk_wk_zero :
    wk (wk (wk (0 : Fin 1))) = (3 : Fin 4) := by
  decide

@[simp] theorem fixedAxis_wk_wk_zero :
    wk (wk (0 : Fin 1)) = (2 : Fin 3) := by
  decide

@[simp] theorem fixedAxis_wk_two :
    wk (2 : Fin 3) = (3 : Fin 4) := by
  decide

theorem fixedAxisBinaryAtSignatureType_hasType
    (beforeLevel afterLevel : LevelExpr)
    {axis : Tower.Tm 1}
    {beforeConstructor afterConstructor : DeclName}
    {beforeFamily afterFamily : Tower.Tm 1}
    (beforeFamilyTyping : AxisRefinementHasType axisRefinementContextS
      beforeFamily
      (familyType beforeLevel (signatureJudgment (.var 0))))
    (afterFamilyTyping : AxisRefinementHasType axisRefinementContextS
      afterFamily
      (familyType afterLevel (signatureJudgment (.var 0))))
    (resultTyping : AxisRefinementHasType
      (fixedAxisBinaryContextSJWW beforeFamily afterFamily)
      (axisRefinementApp (.var 3)
        (Presentation.rename wk
          (Presentation.rename wk (Presentation.rename wk axis)))
        (.var 2)
        (axisNamedOutcomeConstructorApp beforeConstructor
          (.var 3) (.var 2) (.var 1))
        (axisNamedOutcomeConstructorApp afterConstructor
          (.var 3) (.var 2) (.var 0)))
      (sortTm axisRefinementLevel)) :
    AxisRefinementHasType axisRefinementContextS
      (fixedAxisBinaryAtSignatureType axis beforeConstructor
        afterConstructor (.var 0) beforeFamily afterFamily)
      (sortTm (fixedAxisBinaryBodyLevel beforeLevel afterLevel)) := by
  unfold fixedAxisBinaryAtSignatureType fixedAxisBinaryBodyLevel
    fixedAxisBinaryBeforeLevel fixedAxisBinaryAfterLevel
  apply Presentation.HasType.piForm
  · exact signatureJudgment_hasType axisRefinementSignatureVar_hasType
  · exact .sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply familyApp_hasType
      · have weakened := beforeFamilyTyping.weaken
          (extension := signatureJudgment (.var 0))
        simpa [axisRefinementContextS, familyType, sortTm,
          Presentation.rename] using weakened
      · exact Presentation.HasType.var 0
    · exact .sort beforeLevel
    · apply Presentation.HasType.piForm
      · apply familyApp_hasType
        · have first := afterFamilyTyping.weaken
            (extension := signatureJudgment (.var 0))
          have second := first.weaken
            (extension :=
              .app (Presentation.rename wk beforeFamily) (.var 0))
          simpa [fixedAxisBinaryContextSJW, axisRefinementContextS,
            familyType, sortTm, Presentation.rename] using second
        · exact Presentation.HasType.var 1
      · exact .sort afterLevel
      · simpa [fixedAxisBinaryContextSJWW,
          fixedAxisBinaryContextSJW, axisRefinementContextS,
          axisNamedOutcomeConstructorApp, sortTm,
          Presentation.rename] using resultTyping
      · exact .sort axisRefinementLevel
      · exact .sorts afterLevel axisRefinementLevel
    · exact .sort (fixedAxisBinaryAfterLevel afterLevel)
    · exact .sorts beforeLevel (fixedAxisBinaryAfterLevel afterLevel)
  · exact .sort (fixedAxisBinaryBeforeLevel beforeLevel afterLevel)
  · exact .sorts judgmentLevel
      (fixedAxisBinaryBeforeLevel beforeLevel afterLevel)

def fixedAxisUnaryAtSignatureType
    (axis : Tower.Tm n) (outcomeConstructor : DeclName)
    (signature payloadFamily : Tower.Tm n) : Tower.Tm n :=
  .pi (signatureJudgment signature)
    (.pi (.app (Presentation.rename wk payloadFamily) (.var 0))
      (axisRefinementApp
        (Presentation.rename wk (Presentation.rename wk signature))
        (Presentation.rename wk (Presentation.rename wk axis))
        (.var 1)
        (axisNamedOutcomeConstructorApp outcomeConstructor
          (Presentation.rename wk (Presentation.rename wk signature))
          (.var 1) (.var 0))
        (axisNamedOutcomeConstructorApp outcomeConstructor
          (Presentation.rename wk (Presentation.rename wk signature))
          (.var 1) (.var 0))))

def axisNamedFixedUnaryConstructorApp (constructor : DeclName)
    (signature judgment witness : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.const constructor) signature) judgment) witness

def fixedAxisUnaryAfterJudgmentType
    (axis : Tower.Tm n) (outcomeConstructor : DeclName)
    (signature judgment payloadFamily : Tower.Tm n) : Tower.Tm n :=
  .pi (.app payloadFamily judgment)
    (axisRefinementApp
      (Presentation.rename wk signature)
      (Presentation.rename wk axis)
      (Presentation.rename wk judgment)
      (axisNamedOutcomeConstructorApp outcomeConstructor
        (Presentation.rename wk signature)
        (Presentation.rename wk judgment) (.var 0))
      (axisNamedOutcomeConstructorApp outcomeConstructor
        (Presentation.rename wk signature)
        (Presentation.rename wk judgment) (.var 0)))

private theorem fixedAxisUnaryConstructorApp_hasType
    {context : Tower.Ctx n}
    {relationConstructor outcomeConstructor : DeclName}
    {relationType : Tower.Tm 0} {bodyType : Tower.Tm 1}
    {axis signature judgment witness payloadFamily : Tower.Tm n}
    (constantTyping : AxisRefinementHasType context
      (.const relationConstructor) (liftClosed relationType))
    (relationTypeEquation :
      relationType = .pi outcomeSignatureType bodyType)
    (openedBody : Presentation.subst (fun _ : Fin 1 => signature) bodyType =
      fixedAxisUnaryAtSignatureType axis outcomeConstructor signature
        payloadFamily)
    (signatureTyping : AxisRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : AxisRefinementHasType context judgment
      (signatureJudgment signature))
    (witnessTyping : AxisRefinementHasType context witness
      (.app payloadFamily judgment)) :
    AxisRefinementHasType context
      (axisNamedFixedUnaryConstructorApp relationConstructor signature
        judgment witness)
      (axisRefinementApp signature axis judgment
        (axisNamedOutcomeConstructorApp outcomeConstructor signature
          judgment witness)
        (axisNamedOutcomeConstructorApp outcomeConstructor signature
          judgment witness)) := by
  subst relationType
  have afterSignature := Presentation.HasType.appElim constantTyping
    signatureTyping
  have afterSignatureNormalized :
      AxisRefinementHasType context
        (.app (.const relationConstructor) signature)
        (fixedAxisUnaryAtSignatureType axis outcomeConstructor signature
          payloadFamily) := by
    simpa only [liftClosed, inst0_rename_liftRen_elim0,
      openedBody] using afterSignature
  have afterJudgment := Presentation.HasType.appElim
    afterSignatureNormalized judgmentTyping
  have afterJudgmentNormalized :
      AxisRefinementHasType context
        (.app (.app (.const relationConstructor) signature) judgment)
        (fixedAxisUnaryAfterJudgmentType axis outcomeConstructor signature
          judgment payloadFamily) := by
    convert afterJudgment using 1
    all_goals simp [fixedAxisUnaryAfterJudgmentType,
      axisNamedOutcomeConstructorApp, axisRefinementApp,
      Presentation.inst0, Presentation.subst]
  have afterWitness := Presentation.HasType.appElim
    afterJudgmentNormalized witnessTyping
  convert afterWitness using 1
  all_goals simp [axisNamedFixedUnaryConstructorApp,
    axisNamedOutcomeConstructorApp,
    axisRefinementApp, Presentation.inst0, Presentation.subst]

def fixedAxisUnaryContextSJW (payloadFamily : Tower.Tm 1) :
    Tower.Ctx 3 :=
  .snoc
    (.snoc axisRefinementContextS (signatureJudgment (.var 0)))
    (.app (Presentation.rename wk payloadFamily) (.var 0))

def fixedAxisUnaryWitnessLevel (payloadLevel : LevelExpr) : LevelExpr :=
  .max payloadLevel axisRefinementLevel

def fixedAxisUnaryBodyLevel (payloadLevel : LevelExpr) : LevelExpr :=
  .max judgmentLevel (fixedAxisUnaryWitnessLevel payloadLevel)

theorem fixedAxisUnaryAtSignatureType_hasType
    (payloadLevel : LevelExpr)
    {axis : Tower.Tm 1} {outcomeConstructor : DeclName}
    {payloadFamily : Tower.Tm 1}
    (payloadFamilyTyping : AxisRefinementHasType axisRefinementContextS
      payloadFamily
      (familyType payloadLevel (signatureJudgment (.var 0))))
    (resultTyping : AxisRefinementHasType
      (fixedAxisUnaryContextSJW payloadFamily)
      (axisRefinementApp (.var 2)
        (Presentation.rename wk (Presentation.rename wk axis))
        (.var 1)
        (axisNamedOutcomeConstructorApp outcomeConstructor
          (.var 2) (.var 1) (.var 0))
        (axisNamedOutcomeConstructorApp outcomeConstructor
          (.var 2) (.var 1) (.var 0)))
      (sortTm axisRefinementLevel)) :
    AxisRefinementHasType axisRefinementContextS
      (fixedAxisUnaryAtSignatureType axis outcomeConstructor
        (.var 0) payloadFamily)
      (sortTm (fixedAxisUnaryBodyLevel payloadLevel)) := by
  unfold fixedAxisUnaryAtSignatureType fixedAxisUnaryBodyLevel
    fixedAxisUnaryWitnessLevel
  apply Presentation.HasType.piForm
  · exact signatureJudgment_hasType axisRefinementSignatureVar_hasType
  · exact .sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply familyApp_hasType
      · have weakened := payloadFamilyTyping.weaken
          (extension := signatureJudgment (.var 0))
        simpa [axisRefinementContextS, familyType, sortTm,
          Presentation.rename] using weakened
      · exact Presentation.HasType.var 0
    · exact .sort payloadLevel
    · simpa [fixedAxisUnaryContextSJW, axisRefinementContextS,
        axisNamedOutcomeConstructorApp, sortTm,
        Presentation.rename] using resultTyping
    · exact .sort axisRefinementLevel
    · exact .sorts payloadLevel axisRefinementLevel
  · exact .sort (fixedAxisUnaryWitnessLevel payloadLevel)
  · exact .sorts judgmentLevel (fixedAxisUnaryWitnessLevel payloadLevel)

theorem closeAxisRefinementBody_hasType
    {body : Tower.Tm 1} {bodyLevel : LevelExpr}
    (bodyTyping : AxisRefinementHasType axisRefinementContextS body
      (sortTm bodyLevel)) :
    AxisRefinementHasType (.nil : Tower.Ctx 0)
      (.pi outcomeSignatureType body)
      (sortTm (.max signatureLevel bodyLevel)) := by
  apply Presentation.HasType.piForm
  · exact outcomeSignatureType_hasAxisRefinementType
  · exact .sort signatureLevel
  · simpa [axisRefinementContextS, sortTm] using bodyTyping
  · exact .sort bodyLevel
  · exact .sorts signatureLevel bodyLevel

theorem budgetOutsideRefinementBodyType_asUnary :
    budgetOutsideRefinementBodyType =
      fixedAxisUnaryAtSignatureType refinementAxisBudgetTm
        outsideFragmentName (.var 0) (signatureBoundary (.var 0)) := by
  decide

@[simp] theorem substitute_budgetOutsideRefinementBodyType
    (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature)
        budgetOutsideRefinementBodyType =
      fixedAxisUnaryAtSignatureType refinementAxisBudgetTm
        outsideFragmentName signature (signatureBoundary signature) := by
  simp [budgetOutsideRefinementBodyType, fixedAxisUnaryAtSignatureType,
    axisNamedOutcomeConstructorApp, axisRefinementApp,
    outsideFragmentApp, Presentation.subst]

theorem budgetOutsideRefinementApp_hasType {context : Tower.Ctx n}
    {signature judgment reason : Tower.Tm n}
    (signatureTyping : AxisRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : AxisRefinementHasType context judgment
      (signatureJudgment signature))
    (reasonTyping : AxisRefinementHasType context reason
      (.app (signatureBoundary signature) judgment)) :
    AxisRefinementHasType context
      (budgetOutsideRefinementApp signature judgment reason)
      (axisRefinementApp signature refinementAxisBudgetTm judgment
        (outsideFragmentApp signature judgment reason)
        (outsideFragmentApp signature judgment reason)) := by
  have generic := fixedAxisUnaryConstructorApp_hasType
    (context := context)
    (relationConstructor := budgetOutsideRefinementName)
    (outcomeConstructor := outsideFragmentName)
    (bodyType := budgetOutsideRefinementBodyType)
    (axis := refinementAxisBudgetTm)
    (payloadFamily := signatureBoundary signature)
    budgetOutsideRefinementConstant_hasType rfl
    (substitute_budgetOutsideRefinementBodyType signature)
    signatureTyping judgmentTyping reasonTyping
  simpa [axisNamedFixedUnaryConstructorApp,
    axisNamedOutcomeConstructorApp, budgetOutsideRefinementApp,
    outsideFragmentApp] using generic

theorem budgetOutsideRefinementBodyType_hasType :
    AxisRefinementHasType axisRefinementContextS
      budgetOutsideRefinementBodyType
      (sortTm (fixedAxisUnaryBodyLevel boundaryLevel)) := by
  rw [budgetOutsideRefinementBodyType_asUnary]
  apply fixedAxisUnaryAtSignatureType_hasType boundaryLevel
  · exact signatureBoundary_hasType axisRefinementSignatureVar_hasType
  · apply axisRefinementApp_hasType
    · exact Presentation.HasType.var 2
    · exact refinementAxisBudgetTm_hasAxisRefinementType
    · exact Presentation.HasType.var 1
    · apply outsideFragmentApp_hasAxisRefinementType
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0
    · apply outsideFragmentApp_hasAxisRefinementType
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0

def budgetOutsideRefinementDeclarationLevel : LevelExpr :=
  .max signatureLevel (fixedAxisUnaryBodyLevel boundaryLevel)

theorem budgetOutsideRefinementType_hasType :
    AxisRefinementHasType (.nil : Tower.Ctx 0)
      budgetOutsideRefinementType
      (sortTm budgetOutsideRefinementDeclarationLevel) := by
  simpa [budgetOutsideRefinementType,
    budgetOutsideRefinementDeclarationLevel] using
    (closeAxisRefinementBody_hasType
      budgetOutsideRefinementBodyType_hasType)

theorem budgetIncompleteEstablishedRefinementBodyType_asBinary :
    budgetIncompleteEstablishedRefinementBodyType =
      fixedAxisBinaryAtSignatureType refinementAxisBudgetTm
        incompleteName establishedName (.var 0)
        (signatureFrontier (.var 0)) (signatureEvidence (.var 0)) := by
  decide

@[simp] theorem substitute_budgetIncompleteEstablishedRefinementBodyType
    (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature)
        budgetIncompleteEstablishedRefinementBodyType =
      fixedAxisBinaryAtSignatureType refinementAxisBudgetTm
        incompleteName establishedName signature
        (signatureFrontier signature) (signatureEvidence signature) := by
  simp [budgetIncompleteEstablishedRefinementBodyType,
    fixedAxisBinaryAtSignatureType, axisNamedOutcomeConstructorApp,
    axisRefinementApp, incompleteApp, establishedApp,
    Presentation.subst]

theorem budgetIncompleteEstablishedRefinementApp_hasType
    {context : Tower.Ctx n}
    {signature judgment frontier evidence : Tower.Tm n}
    (signatureTyping : AxisRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : AxisRefinementHasType context judgment
      (signatureJudgment signature))
    (frontierTyping : AxisRefinementHasType context frontier
      (.app (signatureFrontier signature) judgment))
    (evidenceTyping : AxisRefinementHasType context evidence
      (.app (signatureEvidence signature) judgment)) :
    AxisRefinementHasType context
      (budgetIncompleteEstablishedRefinementApp signature judgment
        frontier evidence)
      (axisRefinementApp signature refinementAxisBudgetTm judgment
        (incompleteApp signature judgment frontier)
        (establishedApp signature judgment evidence)) := by
  have generic := fixedAxisBinaryConstructorApp_hasType
    (context := context)
    (relationConstructor := budgetIncompleteEstablishedRefinementName)
    (beforeConstructor := incompleteName)
    (afterConstructor := establishedName)
    (bodyType := budgetIncompleteEstablishedRefinementBodyType)
    (axis := refinementAxisBudgetTm)
    (beforeFamily := signatureFrontier signature)
    (afterFamily := signatureEvidence signature)
    budgetIncompleteEstablishedRefinementConstant_hasType rfl
    (substitute_budgetIncompleteEstablishedRefinementBodyType signature)
    signatureTyping judgmentTyping frontierTyping evidenceTyping
  simpa [axisNamedFixedBinaryConstructorApp,
    axisNamedOutcomeConstructorApp,
    budgetIncompleteEstablishedRefinementApp, incompleteApp,
    establishedApp] using generic

theorem budgetIncompleteEstablishedRefinementBodyType_hasType :
    AxisRefinementHasType axisRefinementContextS
      budgetIncompleteEstablishedRefinementBodyType
      (sortTm (fixedAxisBinaryBodyLevel frontierLevel evidenceLevel)) := by
  rw [budgetIncompleteEstablishedRefinementBodyType_asBinary]
  apply fixedAxisBinaryAtSignatureType_hasType frontierLevel evidenceLevel
  · exact signatureFrontier_hasType axisRefinementSignatureVar_hasType
  · exact signatureEvidence_hasType axisRefinementSignatureVar_hasType
  · apply axisRefinementApp_hasType
    · exact Presentation.HasType.var 3
    · exact refinementAxisBudgetTm_hasAxisRefinementType
    · exact Presentation.HasType.var 2
    · apply incompleteApp_hasAxisRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply establishedApp_hasAxisRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0

def budgetIncompleteEstablishedRefinementDeclarationLevel : LevelExpr :=
  .max signatureLevel
    (fixedAxisBinaryBodyLevel frontierLevel evidenceLevel)

theorem budgetIncompleteEstablishedRefinementType_hasType :
    AxisRefinementHasType (.nil : Tower.Ctx 0)
      budgetIncompleteEstablishedRefinementType
      (sortTm budgetIncompleteEstablishedRefinementDeclarationLevel) := by
  simpa [budgetIncompleteEstablishedRefinementType,
    budgetIncompleteEstablishedRefinementDeclarationLevel] using
    (closeAxisRefinementBody_hasType
      budgetIncompleteEstablishedRefinementBodyType_hasType)

theorem budgetIncompleteRefutedRefinementBodyType_asBinary :
    budgetIncompleteRefutedRefinementBodyType =
      fixedAxisBinaryAtSignatureType refinementAxisBudgetTm
        incompleteName refutedName (.var 0)
        (signatureFrontier (.var 0)) (signatureObstruction (.var 0)) := by
  decide

@[simp] theorem substitute_budgetIncompleteRefutedRefinementBodyType
    (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature)
        budgetIncompleteRefutedRefinementBodyType =
      fixedAxisBinaryAtSignatureType refinementAxisBudgetTm
        incompleteName refutedName signature
        (signatureFrontier signature) (signatureObstruction signature) := by
  simp [budgetIncompleteRefutedRefinementBodyType,
    fixedAxisBinaryAtSignatureType, axisNamedOutcomeConstructorApp,
    axisRefinementApp, incompleteApp, refutedApp, Presentation.subst]

theorem budgetIncompleteRefutedRefinementApp_hasType
    {context : Tower.Ctx n}
    {signature judgment frontier obstruction : Tower.Tm n}
    (signatureTyping : AxisRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : AxisRefinementHasType context judgment
      (signatureJudgment signature))
    (frontierTyping : AxisRefinementHasType context frontier
      (.app (signatureFrontier signature) judgment))
    (obstructionTyping : AxisRefinementHasType context obstruction
      (.app (signatureObstruction signature) judgment)) :
    AxisRefinementHasType context
      (budgetIncompleteRefutedRefinementApp signature judgment
        frontier obstruction)
      (axisRefinementApp signature refinementAxisBudgetTm judgment
        (incompleteApp signature judgment frontier)
        (refutedApp signature judgment obstruction)) := by
  have generic := fixedAxisBinaryConstructorApp_hasType
    (context := context)
    (relationConstructor := budgetIncompleteRefutedRefinementName)
    (beforeConstructor := incompleteName)
    (afterConstructor := refutedName)
    (bodyType := budgetIncompleteRefutedRefinementBodyType)
    (axis := refinementAxisBudgetTm)
    (beforeFamily := signatureFrontier signature)
    (afterFamily := signatureObstruction signature)
    budgetIncompleteRefutedRefinementConstant_hasType rfl
    (substitute_budgetIncompleteRefutedRefinementBodyType signature)
    signatureTyping judgmentTyping frontierTyping obstructionTyping
  simpa [axisNamedFixedBinaryConstructorApp,
    axisNamedOutcomeConstructorApp,
    budgetIncompleteRefutedRefinementApp, incompleteApp, refutedApp] using
    generic

theorem budgetIncompleteRefutedRefinementBodyType_hasType :
    AxisRefinementHasType axisRefinementContextS
      budgetIncompleteRefutedRefinementBodyType
      (sortTm (fixedAxisBinaryBodyLevel frontierLevel obstructionLevel)) := by
  rw [budgetIncompleteRefutedRefinementBodyType_asBinary]
  apply fixedAxisBinaryAtSignatureType_hasType frontierLevel obstructionLevel
  · exact signatureFrontier_hasType axisRefinementSignatureVar_hasType
  · exact signatureObstruction_hasType axisRefinementSignatureVar_hasType
  · apply axisRefinementApp_hasType
    · exact Presentation.HasType.var 3
    · exact refinementAxisBudgetTm_hasAxisRefinementType
    · exact Presentation.HasType.var 2
    · apply incompleteApp_hasAxisRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply refutedApp_hasAxisRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0

def budgetIncompleteRefutedRefinementDeclarationLevel : LevelExpr :=
  .max signatureLevel
    (fixedAxisBinaryBodyLevel frontierLevel obstructionLevel)

theorem budgetIncompleteRefutedRefinementType_hasType :
    AxisRefinementHasType (.nil : Tower.Ctx 0)
      budgetIncompleteRefutedRefinementType
      (sortTm budgetIncompleteRefutedRefinementDeclarationLevel) := by
  simpa [budgetIncompleteRefutedRefinementType,
    budgetIncompleteRefutedRefinementDeclarationLevel] using
    (closeAxisRefinementBody_hasType
      budgetIncompleteRefutedRefinementBodyType_hasType)

theorem authorityOutsideRefinementBodyType_asBinary :
    authorityOutsideRefinementBodyType =
      fixedAxisBinaryAtSignatureType refinementAxisAuthorityTm
        outsideFragmentName outsideFragmentName (.var 0)
        (signatureBoundary (.var 0)) (signatureBoundary (.var 0)) := by
  decide

@[simp] theorem substitute_authorityOutsideRefinementBodyType
    (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature)
        authorityOutsideRefinementBodyType =
      fixedAxisBinaryAtSignatureType refinementAxisAuthorityTm
        outsideFragmentName outsideFragmentName signature
        (signatureBoundary signature) (signatureBoundary signature) := by
  simp [authorityOutsideRefinementBodyType,
    fixedAxisBinaryAtSignatureType, axisNamedOutcomeConstructorApp,
    axisRefinementApp, outsideFragmentApp, Presentation.subst]

theorem authorityOutsideRefinementApp_hasType {context : Tower.Ctx n}
    {signature judgment before after : Tower.Tm n}
    (signatureTyping : AxisRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : AxisRefinementHasType context judgment
      (signatureJudgment signature))
    (beforeTyping : AxisRefinementHasType context before
      (.app (signatureBoundary signature) judgment))
    (afterTyping : AxisRefinementHasType context after
      (.app (signatureBoundary signature) judgment)) :
    AxisRefinementHasType context
      (authorityOutsideRefinementApp signature judgment before after)
      (axisRefinementApp signature refinementAxisAuthorityTm judgment
        (outsideFragmentApp signature judgment before)
        (outsideFragmentApp signature judgment after)) := by
  have generic := fixedAxisBinaryConstructorApp_hasType
    (context := context)
    (relationConstructor := authorityOutsideRefinementName)
    (beforeConstructor := outsideFragmentName)
    (afterConstructor := outsideFragmentName)
    (bodyType := authorityOutsideRefinementBodyType)
    (axis := refinementAxisAuthorityTm)
    (beforeFamily := signatureBoundary signature)
    (afterFamily := signatureBoundary signature)
    authorityOutsideRefinementConstant_hasType rfl
    (substitute_authorityOutsideRefinementBodyType signature)
    signatureTyping judgmentTyping beforeTyping afterTyping
  simpa [axisNamedFixedBinaryConstructorApp,
    axisNamedOutcomeConstructorApp, authorityOutsideRefinementApp,
    outsideFragmentApp] using generic

theorem authorityOutsideRefinementBodyType_hasType :
    AxisRefinementHasType axisRefinementContextS
      authorityOutsideRefinementBodyType
      (sortTm (fixedAxisBinaryBodyLevel boundaryLevel boundaryLevel)) := by
  rw [authorityOutsideRefinementBodyType_asBinary]
  apply fixedAxisBinaryAtSignatureType_hasType boundaryLevel boundaryLevel
  · exact signatureBoundary_hasType axisRefinementSignatureVar_hasType
  · exact signatureBoundary_hasType axisRefinementSignatureVar_hasType
  · apply axisRefinementApp_hasType
    · exact Presentation.HasType.var 3
    · exact refinementAxisAuthorityTm_hasAxisRefinementType
    · exact Presentation.HasType.var 2
    · apply outsideFragmentApp_hasAxisRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply outsideFragmentApp_hasAxisRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0

def authorityOutsideRefinementDeclarationLevel : LevelExpr :=
  .max signatureLevel
    (fixedAxisBinaryBodyLevel boundaryLevel boundaryLevel)

theorem authorityOutsideRefinementType_hasType :
    AxisRefinementHasType (.nil : Tower.Ctx 0)
      authorityOutsideRefinementType
      (sortTm authorityOutsideRefinementDeclarationLevel) := by
  simpa [authorityOutsideRefinementType,
    authorityOutsideRefinementDeclarationLevel] using
    (closeAxisRefinementBody_hasType
      authorityOutsideRefinementBodyType_hasType)

theorem authorityOutsideEstablishedRefinementBodyType_asBinary :
    authorityOutsideEstablishedRefinementBodyType =
      fixedAxisBinaryAtSignatureType refinementAxisAuthorityTm
        outsideFragmentName establishedName (.var 0)
        (signatureBoundary (.var 0)) (signatureEvidence (.var 0)) := by
  decide

@[simp] theorem substitute_authorityOutsideEstablishedRefinementBodyType
    (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature)
        authorityOutsideEstablishedRefinementBodyType =
      fixedAxisBinaryAtSignatureType refinementAxisAuthorityTm
        outsideFragmentName establishedName signature
        (signatureBoundary signature) (signatureEvidence signature) := by
  simp [authorityOutsideEstablishedRefinementBodyType,
    fixedAxisBinaryAtSignatureType, axisNamedOutcomeConstructorApp,
    axisRefinementApp, outsideFragmentApp, establishedApp,
    Presentation.subst]

theorem authorityOutsideEstablishedRefinementApp_hasType
    {context : Tower.Ctx n}
    {signature judgment reason evidence : Tower.Tm n}
    (signatureTyping : AxisRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : AxisRefinementHasType context judgment
      (signatureJudgment signature))
    (reasonTyping : AxisRefinementHasType context reason
      (.app (signatureBoundary signature) judgment))
    (evidenceTyping : AxisRefinementHasType context evidence
      (.app (signatureEvidence signature) judgment)) :
    AxisRefinementHasType context
      (authorityOutsideEstablishedRefinementApp signature judgment
        reason evidence)
      (axisRefinementApp signature refinementAxisAuthorityTm judgment
        (outsideFragmentApp signature judgment reason)
        (establishedApp signature judgment evidence)) := by
  have generic := fixedAxisBinaryConstructorApp_hasType
    (context := context)
    (relationConstructor := authorityOutsideEstablishedRefinementName)
    (beforeConstructor := outsideFragmentName)
    (afterConstructor := establishedName)
    (bodyType := authorityOutsideEstablishedRefinementBodyType)
    (axis := refinementAxisAuthorityTm)
    (beforeFamily := signatureBoundary signature)
    (afterFamily := signatureEvidence signature)
    authorityOutsideEstablishedRefinementConstant_hasType rfl
    (substitute_authorityOutsideEstablishedRefinementBodyType signature)
    signatureTyping judgmentTyping reasonTyping evidenceTyping
  simpa [axisNamedFixedBinaryConstructorApp,
    axisNamedOutcomeConstructorApp,
    authorityOutsideEstablishedRefinementApp, outsideFragmentApp,
    establishedApp] using generic

theorem authorityOutsideEstablishedRefinementBodyType_hasType :
    AxisRefinementHasType axisRefinementContextS
      authorityOutsideEstablishedRefinementBodyType
      (sortTm (fixedAxisBinaryBodyLevel boundaryLevel evidenceLevel)) := by
  rw [authorityOutsideEstablishedRefinementBodyType_asBinary]
  apply fixedAxisBinaryAtSignatureType_hasType boundaryLevel evidenceLevel
  · exact signatureBoundary_hasType axisRefinementSignatureVar_hasType
  · exact signatureEvidence_hasType axisRefinementSignatureVar_hasType
  · apply axisRefinementApp_hasType
    · exact Presentation.HasType.var 3
    · exact refinementAxisAuthorityTm_hasAxisRefinementType
    · exact Presentation.HasType.var 2
    · apply outsideFragmentApp_hasAxisRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply establishedApp_hasAxisRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0

def authorityOutsideEstablishedRefinementDeclarationLevel : LevelExpr :=
  .max signatureLevel
    (fixedAxisBinaryBodyLevel boundaryLevel evidenceLevel)

theorem authorityOutsideEstablishedRefinementType_hasType :
    AxisRefinementHasType (.nil : Tower.Ctx 0)
      authorityOutsideEstablishedRefinementType
      (sortTm authorityOutsideEstablishedRefinementDeclarationLevel) := by
  simpa [authorityOutsideEstablishedRefinementType,
    authorityOutsideEstablishedRefinementDeclarationLevel] using
    (closeAxisRefinementBody_hasType
      authorityOutsideEstablishedRefinementBodyType_hasType)

theorem authorityOutsideRefutedRefinementBodyType_asBinary :
    authorityOutsideRefutedRefinementBodyType =
      fixedAxisBinaryAtSignatureType refinementAxisAuthorityTm
        outsideFragmentName refutedName (.var 0)
        (signatureBoundary (.var 0)) (signatureObstruction (.var 0)) := by
  decide

@[simp] theorem substitute_authorityOutsideRefutedRefinementBodyType
    (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature)
        authorityOutsideRefutedRefinementBodyType =
      fixedAxisBinaryAtSignatureType refinementAxisAuthorityTm
        outsideFragmentName refutedName signature
        (signatureBoundary signature) (signatureObstruction signature) := by
  simp [authorityOutsideRefutedRefinementBodyType,
    fixedAxisBinaryAtSignatureType, axisNamedOutcomeConstructorApp,
    axisRefinementApp, outsideFragmentApp, refutedApp,
    Presentation.subst]

theorem authorityOutsideRefutedRefinementApp_hasType
    {context : Tower.Ctx n}
    {signature judgment reason obstruction : Tower.Tm n}
    (signatureTyping : AxisRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : AxisRefinementHasType context judgment
      (signatureJudgment signature))
    (reasonTyping : AxisRefinementHasType context reason
      (.app (signatureBoundary signature) judgment))
    (obstructionTyping : AxisRefinementHasType context obstruction
      (.app (signatureObstruction signature) judgment)) :
    AxisRefinementHasType context
      (authorityOutsideRefutedRefinementApp signature judgment
        reason obstruction)
      (axisRefinementApp signature refinementAxisAuthorityTm judgment
        (outsideFragmentApp signature judgment reason)
        (refutedApp signature judgment obstruction)) := by
  have generic := fixedAxisBinaryConstructorApp_hasType
    (context := context)
    (relationConstructor := authorityOutsideRefutedRefinementName)
    (beforeConstructor := outsideFragmentName)
    (afterConstructor := refutedName)
    (bodyType := authorityOutsideRefutedRefinementBodyType)
    (axis := refinementAxisAuthorityTm)
    (beforeFamily := signatureBoundary signature)
    (afterFamily := signatureObstruction signature)
    authorityOutsideRefutedRefinementConstant_hasType rfl
    (substitute_authorityOutsideRefutedRefinementBodyType signature)
    signatureTyping judgmentTyping reasonTyping obstructionTyping
  simpa [axisNamedFixedBinaryConstructorApp,
    axisNamedOutcomeConstructorApp,
    authorityOutsideRefutedRefinementApp, outsideFragmentApp, refutedApp]
    using generic

theorem authorityOutsideRefutedRefinementBodyType_hasType :
    AxisRefinementHasType axisRefinementContextS
      authorityOutsideRefutedRefinementBodyType
      (sortTm (fixedAxisBinaryBodyLevel boundaryLevel obstructionLevel)) := by
  rw [authorityOutsideRefutedRefinementBodyType_asBinary]
  apply fixedAxisBinaryAtSignatureType_hasType boundaryLevel obstructionLevel
  · exact signatureBoundary_hasType axisRefinementSignatureVar_hasType
  · exact signatureObstruction_hasType axisRefinementSignatureVar_hasType
  · apply axisRefinementApp_hasType
    · exact Presentation.HasType.var 3
    · exact refinementAxisAuthorityTm_hasAxisRefinementType
    · exact Presentation.HasType.var 2
    · apply outsideFragmentApp_hasAxisRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply refutedApp_hasAxisRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0

def authorityOutsideRefutedRefinementDeclarationLevel : LevelExpr :=
  .max signatureLevel
    (fixedAxisBinaryBodyLevel boundaryLevel obstructionLevel)

theorem authorityOutsideRefutedRefinementType_hasType :
    AxisRefinementHasType (.nil : Tower.Ctx 0)
      authorityOutsideRefutedRefinementType
      (sortTm authorityOutsideRefutedRefinementDeclarationLevel) := by
  simpa [authorityOutsideRefutedRefinementType,
    authorityOutsideRefutedRefinementDeclarationLevel] using
    (closeAxisRefinementBody_hasType
      authorityOutsideRefutedRefinementBodyType_hasType)

theorem authorityOutsideIncompleteRefinementBodyType_asBinary :
    authorityOutsideIncompleteRefinementBodyType =
      fixedAxisBinaryAtSignatureType refinementAxisAuthorityTm
        outsideFragmentName incompleteName (.var 0)
        (signatureBoundary (.var 0)) (signatureFrontier (.var 0)) := by
  decide

@[simp] theorem substitute_authorityOutsideIncompleteRefinementBodyType
    (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature)
        authorityOutsideIncompleteRefinementBodyType =
      fixedAxisBinaryAtSignatureType refinementAxisAuthorityTm
        outsideFragmentName incompleteName signature
        (signatureBoundary signature) (signatureFrontier signature) := by
  simp [authorityOutsideIncompleteRefinementBodyType,
    fixedAxisBinaryAtSignatureType, axisNamedOutcomeConstructorApp,
    axisRefinementApp, outsideFragmentApp, incompleteApp,
    Presentation.subst]

theorem authorityOutsideIncompleteRefinementApp_hasType
    {context : Tower.Ctx n}
    {signature judgment reason frontier : Tower.Tm n}
    (signatureTyping : AxisRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (judgmentTyping : AxisRefinementHasType context judgment
      (signatureJudgment signature))
    (reasonTyping : AxisRefinementHasType context reason
      (.app (signatureBoundary signature) judgment))
    (frontierTyping : AxisRefinementHasType context frontier
      (.app (signatureFrontier signature) judgment)) :
    AxisRefinementHasType context
      (authorityOutsideIncompleteRefinementApp signature judgment
        reason frontier)
      (axisRefinementApp signature refinementAxisAuthorityTm judgment
        (outsideFragmentApp signature judgment reason)
        (incompleteApp signature judgment frontier)) := by
  have generic := fixedAxisBinaryConstructorApp_hasType
    (context := context)
    (relationConstructor := authorityOutsideIncompleteRefinementName)
    (beforeConstructor := outsideFragmentName)
    (afterConstructor := incompleteName)
    (bodyType := authorityOutsideIncompleteRefinementBodyType)
    (axis := refinementAxisAuthorityTm)
    (beforeFamily := signatureBoundary signature)
    (afterFamily := signatureFrontier signature)
    authorityOutsideIncompleteRefinementConstant_hasType rfl
    (substitute_authorityOutsideIncompleteRefinementBodyType signature)
    signatureTyping judgmentTyping reasonTyping frontierTyping
  simpa [axisNamedFixedBinaryConstructorApp,
    axisNamedOutcomeConstructorApp,
    authorityOutsideIncompleteRefinementApp, outsideFragmentApp,
    incompleteApp] using generic

theorem authorityOutsideIncompleteRefinementBodyType_hasType :
    AxisRefinementHasType axisRefinementContextS
      authorityOutsideIncompleteRefinementBodyType
      (sortTm (fixedAxisBinaryBodyLevel boundaryLevel frontierLevel)) := by
  rw [authorityOutsideIncompleteRefinementBodyType_asBinary]
  apply fixedAxisBinaryAtSignatureType_hasType boundaryLevel frontierLevel
  · exact signatureBoundary_hasType axisRefinementSignatureVar_hasType
  · exact signatureFrontier_hasType axisRefinementSignatureVar_hasType
  · apply axisRefinementApp_hasType
    · exact Presentation.HasType.var 3
    · exact refinementAxisAuthorityTm_hasAxisRefinementType
    · exact Presentation.HasType.var 2
    · apply outsideFragmentApp_hasAxisRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply incompleteApp_hasAxisRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0

def authorityOutsideIncompleteRefinementDeclarationLevel : LevelExpr :=
  .max signatureLevel
    (fixedAxisBinaryBodyLevel boundaryLevel frontierLevel)

theorem authorityOutsideIncompleteRefinementType_hasType :
    AxisRefinementHasType (.nil : Tower.Ctx 0)
      authorityOutsideIncompleteRefinementType
      (sortTm authorityOutsideIncompleteRefinementDeclarationLevel) := by
  simpa [authorityOutsideIncompleteRefinementType,
    authorityOutsideIncompleteRefinementDeclarationLevel] using
    (closeAxisRefinementBody_hasType
      authorityOutsideIncompleteRefinementBodyType_hasType)

/-! ### Formation of axis-polymorphic constructors -/

def axisBinaryAtSignatureType
    (beforeConstructor afterConstructor : DeclName)
    (signature beforeFamily afterFamily : Tower.Tm n) : Tower.Tm n :=
  .pi refinementAxisTm
    (.pi (signatureJudgment (Presentation.rename wk signature))
      (.pi
        (.app
          (Presentation.rename wk (Presentation.rename wk beforeFamily))
          (.var 0))
        (.pi
          (.app
            (Presentation.rename wk
              (Presentation.rename wk
                (Presentation.rename wk afterFamily)))
            (.var 1))
          (axisRefinementApp
            (Presentation.rename wk
              (Presentation.rename wk
                (Presentation.rename wk
                  (Presentation.rename wk signature))))
            (.var 3) (.var 2)
            (axisNamedOutcomeConstructorApp beforeConstructor
              (Presentation.rename wk
                (Presentation.rename wk
                  (Presentation.rename wk
                    (Presentation.rename wk signature))))
              (.var 2) (.var 1))
            (axisNamedOutcomeConstructorApp afterConstructor
              (Presentation.rename wk
                (Presentation.rename wk
                  (Presentation.rename wk
                    (Presentation.rename wk signature))))
              (.var 2) (.var 0))))))

def axisNamedBinaryConstructorApp (constructor : DeclName)
    (signature axis judgment beforeWitness afterWitness : Tower.Tm n) :
    Tower.Tm n :=
  .app
    (.app
      (.app
        (.app
          (.app (.const constructor) signature)
          axis)
        judgment)
      beforeWitness)
    afterWitness

def axisBinaryAfterAxisType
    (beforeConstructor afterConstructor : DeclName)
    (signature axis beforeFamily afterFamily : Tower.Tm n) : Tower.Tm n :=
  .pi (signatureJudgment signature)
    (.pi (.app (Presentation.rename wk beforeFamily) (.var 0))
      (.pi
        (.app
          (Presentation.rename wk (Presentation.rename wk afterFamily))
          (.var 1))
        (axisRefinementApp
          (Presentation.rename wk
            (Presentation.rename wk (Presentation.rename wk signature)))
          (Presentation.rename wk
            (Presentation.rename wk (Presentation.rename wk axis)))
          (.var 2)
          (axisNamedOutcomeConstructorApp beforeConstructor
            (Presentation.rename wk
              (Presentation.rename wk (Presentation.rename wk signature)))
            (.var 2) (.var 1))
          (axisNamedOutcomeConstructorApp afterConstructor
            (Presentation.rename wk
              (Presentation.rename wk (Presentation.rename wk signature)))
            (.var 2) (.var 0)))))

def axisBinaryAfterJudgmentType
    (beforeConstructor afterConstructor : DeclName)
    (signature axis judgment beforeFamily afterFamily : Tower.Tm n) :
    Tower.Tm n :=
  .pi (.app beforeFamily judgment)
    (.pi
      (.app (Presentation.rename wk afterFamily)
        (Presentation.rename wk judgment))
      (axisRefinementApp
        (Presentation.rename wk (Presentation.rename wk signature))
        (Presentation.rename wk (Presentation.rename wk axis))
        (Presentation.rename wk (Presentation.rename wk judgment))
        (axisNamedOutcomeConstructorApp beforeConstructor
          (Presentation.rename wk (Presentation.rename wk signature))
          (Presentation.rename wk (Presentation.rename wk judgment))
          (.var 1))
        (axisNamedOutcomeConstructorApp afterConstructor
          (Presentation.rename wk (Presentation.rename wk signature))
          (Presentation.rename wk (Presentation.rename wk judgment))
          (.var 0))))

def axisBinaryAfterBeforeType
    (beforeConstructor afterConstructor : DeclName)
    (signature axis judgment beforeWitness afterFamily : Tower.Tm n) :
    Tower.Tm n :=
  .pi (.app afterFamily judgment)
    (axisRefinementApp
      (Presentation.rename wk signature)
      (Presentation.rename wk axis)
      (Presentation.rename wk judgment)
      (axisNamedOutcomeConstructorApp beforeConstructor
        (Presentation.rename wk signature)
        (Presentation.rename wk judgment)
        (Presentation.rename wk beforeWitness))
      (axisNamedOutcomeConstructorApp afterConstructor
        (Presentation.rename wk signature)
        (Presentation.rename wk judgment) (.var 0)))

private theorem axisBinaryConstructorApp_hasType
    {context : Tower.Ctx n}
    {relationConstructor beforeConstructor afterConstructor : DeclName}
    {relationType : Tower.Tm 0} {bodyType : Tower.Tm 1}
    {signature axis judgment beforeWitness afterWitness beforeFamily
      afterFamily : Tower.Tm n}
    (constantTyping : AxisRefinementHasType context
      (.const relationConstructor) (liftClosed relationType))
    (relationTypeEquation :
      relationType = .pi outcomeSignatureType bodyType)
    (openedBody : Presentation.subst (fun _ : Fin 1 => signature) bodyType =
      axisBinaryAtSignatureType beforeConstructor afterConstructor
        signature beforeFamily afterFamily)
    (signatureTyping : AxisRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (axisTyping : AxisRefinementHasType context axis refinementAxisTm)
    (judgmentTyping : AxisRefinementHasType context judgment
      (signatureJudgment signature))
    (beforeTyping : AxisRefinementHasType context beforeWitness
      (.app beforeFamily judgment))
    (afterTyping : AxisRefinementHasType context afterWitness
      (.app afterFamily judgment)) :
    AxisRefinementHasType context
      (axisNamedBinaryConstructorApp relationConstructor signature axis
        judgment beforeWitness afterWitness)
      (axisRefinementApp signature axis judgment
        (axisNamedOutcomeConstructorApp beforeConstructor signature
          judgment beforeWitness)
        (axisNamedOutcomeConstructorApp afterConstructor signature
          judgment afterWitness)) := by
  subst relationType
  have afterSignature := Presentation.HasType.appElim constantTyping
    signatureTyping
  have afterSignatureNormalized :
      AxisRefinementHasType context
        (.app (.const relationConstructor) signature)
        (axisBinaryAtSignatureType beforeConstructor afterConstructor
          signature beforeFamily afterFamily) := by
    simpa only [liftClosed, inst0_rename_liftRen_elim0,
      openedBody] using afterSignature
  have afterAxis := Presentation.HasType.appElim afterSignatureNormalized
    axisTyping
  have afterAxisNormalized :
      AxisRefinementHasType context
        (.app (.app (.const relationConstructor) signature) axis)
        (axisBinaryAfterAxisType beforeConstructor afterConstructor
          signature axis beforeFamily afterFamily) := by
    convert afterAxis using 1
    all_goals simp [axisBinaryAfterAxisType,
      axisNamedOutcomeConstructorApp, axisRefinementApp,
      Presentation.inst0, Presentation.subst]
  have afterJudgment := Presentation.HasType.appElim afterAxisNormalized
    judgmentTyping
  have afterJudgmentNormalized :
      AxisRefinementHasType context
        (.app
          (.app (.app (.const relationConstructor) signature) axis)
          judgment)
        (axisBinaryAfterJudgmentType beforeConstructor afterConstructor
          signature axis judgment beforeFamily afterFamily) := by
    convert afterJudgment using 1
    all_goals simp [axisBinaryAfterJudgmentType,
      axisNamedOutcomeConstructorApp, axisRefinementApp,
      Presentation.inst0, Presentation.subst]
  have afterBefore := Presentation.HasType.appElim afterJudgmentNormalized
    beforeTyping
  have afterBeforeNormalized :
      AxisRefinementHasType context
        (.app
          (.app
            (.app (.app (.const relationConstructor) signature) axis)
            judgment)
          beforeWitness)
        (axisBinaryAfterBeforeType beforeConstructor afterConstructor
          signature axis judgment beforeWitness afterFamily) := by
    convert afterBefore using 1
    all_goals simp [axisBinaryAfterBeforeType,
      axisNamedOutcomeConstructorApp, axisRefinementApp,
      Presentation.inst0, Presentation.subst]
  have afterAfter := Presentation.HasType.appElim afterBeforeNormalized
    afterTyping
  convert afterAfter using 1
  all_goals simp [axisNamedBinaryConstructorApp,
    axisNamedOutcomeConstructorApp, axisRefinementApp,
    Presentation.inst0, Presentation.subst]

def axisBinaryContextSAJW (beforeFamily : Tower.Tm 1) : Tower.Ctx 4 :=
  .snoc axisRefinementContextSAJ
    (.app
      (Presentation.rename wk (Presentation.rename wk beforeFamily))
      (.var 0))

def axisBinaryContextSAJWW
    (beforeFamily afterFamily : Tower.Tm 1) : Tower.Ctx 5 :=
  .snoc (axisBinaryContextSAJW beforeFamily)
    (.app
      (Presentation.rename wk
        (Presentation.rename wk (Presentation.rename wk afterFamily)))
      (.var 1))

def axisBinaryAfterLevel (afterLevel : LevelExpr) : LevelExpr :=
  .max afterLevel axisRefinementLevel

def axisBinaryBeforeLevel
    (beforeLevel afterLevel : LevelExpr) : LevelExpr :=
  .max beforeLevel (axisBinaryAfterLevel afterLevel)

def axisBinaryJudgmentLevel
    (beforeLevel afterLevel : LevelExpr) : LevelExpr :=
  .max judgmentLevel (axisBinaryBeforeLevel beforeLevel afterLevel)

def axisBinaryBodyLevel
    (beforeLevel afterLevel : LevelExpr) : LevelExpr :=
  .max refinementAxisLevel
    (axisBinaryJudgmentLevel beforeLevel afterLevel)

@[simp] theorem axisBinary_wk_wk_wk_wk_zero :
    wk (wk (wk (wk (0 : Fin 1)))) = (4 : Fin 5) := by
  decide

@[simp] theorem axisBinary_wk_zero :
    wk (0 : Fin 1) = (1 : Fin 2) := by
  decide

@[simp] theorem axisBinary_wk_three :
    wk (3 : Fin 4) = (4 : Fin 5) := by
  decide

@[simp] theorem axisBinary_wk_wk_wk_one :
    wk (wk (wk (1 : Fin 2))) = (4 : Fin 5) := by
  decide

theorem axisBinaryAtSignatureType_hasType
    (beforeLevel afterLevel : LevelExpr)
    {beforeConstructor afterConstructor : DeclName}
    {beforeFamily afterFamily : Tower.Tm 1}
    (beforeFamilyTyping : AxisRefinementHasType axisRefinementContextS
      beforeFamily
      (familyType beforeLevel (signatureJudgment (.var 0))))
    (afterFamilyTyping : AxisRefinementHasType axisRefinementContextS
      afterFamily
      (familyType afterLevel (signatureJudgment (.var 0))))
    (resultTyping : AxisRefinementHasType
      (axisBinaryContextSAJWW beforeFamily afterFamily)
      (axisRefinementApp (.var 4) (.var 3) (.var 2)
        (axisNamedOutcomeConstructorApp beforeConstructor
          (.var 4) (.var 2) (.var 1))
        (axisNamedOutcomeConstructorApp afterConstructor
          (.var 4) (.var 2) (.var 0)))
      (sortTm axisRefinementLevel)) :
    AxisRefinementHasType axisRefinementContextS
      (axisBinaryAtSignatureType beforeConstructor afterConstructor
        (.var 0) beforeFamily afterFamily)
      (sortTm (axisBinaryBodyLevel beforeLevel afterLevel)) := by
  unfold axisBinaryAtSignatureType axisBinaryBodyLevel
    axisBinaryJudgmentLevel axisBinaryBeforeLevel axisBinaryAfterLevel
  apply Presentation.HasType.piForm
  · exact refinementAxisTm_hasAxisRefinementType
  · exact .sort refinementAxisLevel
  · apply Presentation.HasType.piForm
    · exact signatureJudgment_hasType
        axisRefinementSignatureVarInSA_hasType
    · exact .sort judgmentLevel
    · apply Presentation.HasType.piForm
      · apply familyApp_hasType
        · have first := beforeFamilyTyping.weaken
            (extension := refinementAxisTm)
          have second := first.weaken
            (extension := signatureJudgment (.var 1))
          simpa [axisRefinementContextSAJ, axisRefinementContextSA,
            axisRefinementContextS, familyType, sortTm,
            Presentation.rename] using second
        · exact Presentation.HasType.var 0
      · exact .sort beforeLevel
      · apply Presentation.HasType.piForm
        · apply familyApp_hasType
          · have first := afterFamilyTyping.weaken
              (extension := refinementAxisTm)
            have second := first.weaken
              (extension := signatureJudgment (.var 1))
            have third := second.weaken
              (extension :=
                .app
                  (Presentation.rename wk
                    (Presentation.rename wk beforeFamily))
                  (.var 0))
            simpa [axisBinaryContextSAJW, axisRefinementContextSAJ,
              axisRefinementContextSA, axisRefinementContextS,
              familyType, sortTm, Presentation.rename] using third
          · exact Presentation.HasType.var 1
        · exact .sort afterLevel
        · simpa [axisBinaryContextSAJWW, axisBinaryContextSAJW,
            axisRefinementContextSAJ, axisRefinementContextSA,
            axisRefinementContextS, axisNamedOutcomeConstructorApp,
            sortTm, Presentation.rename] using resultTyping
        · exact .sort axisRefinementLevel
        · exact .sorts afterLevel axisRefinementLevel
      · exact .sort (axisBinaryAfterLevel afterLevel)
      · exact .sorts beforeLevel (axisBinaryAfterLevel afterLevel)
    · exact .sort (axisBinaryBeforeLevel beforeLevel afterLevel)
    · exact .sorts judgmentLevel
        (axisBinaryBeforeLevel beforeLevel afterLevel)
  · exact .sort (axisBinaryJudgmentLevel beforeLevel afterLevel)
  · exact .sorts refinementAxisLevel
      (axisBinaryJudgmentLevel beforeLevel afterLevel)

theorem axisEstablishedBodyType_asBinary :
    axisEstablishedBodyType =
      axisBinaryAtSignatureType establishedName establishedName (.var 0)
        (signatureEvidence (.var 0)) (signatureEvidence (.var 0)) := by
  decide

@[simp] theorem substitute_axisEstablishedBodyType
    (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature)
        axisEstablishedBodyType =
      axisBinaryAtSignatureType establishedName establishedName signature
        (signatureEvidence signature) (signatureEvidence signature) := by
  simp [axisEstablishedBodyType, axisBinaryAtSignatureType,
    axisNamedOutcomeConstructorApp, axisRefinementApp, establishedApp,
    Presentation.subst]

theorem axisEstablishedApp_hasType {context : Tower.Ctx n}
    {signature axis judgment beforeEvidence afterEvidence : Tower.Tm n}
    (signatureTyping : AxisRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (axisTyping : AxisRefinementHasType context axis refinementAxisTm)
    (judgmentTyping : AxisRefinementHasType context judgment
      (signatureJudgment signature))
    (beforeTyping : AxisRefinementHasType context beforeEvidence
      (.app (signatureEvidence signature) judgment))
    (afterTyping : AxisRefinementHasType context afterEvidence
      (.app (signatureEvidence signature) judgment)) :
    AxisRefinementHasType context
      (axisEstablishedApp signature axis judgment beforeEvidence
        afterEvidence)
      (axisRefinementApp signature axis judgment
        (establishedApp signature judgment beforeEvidence)
        (establishedApp signature judgment afterEvidence)) := by
  have generic := axisBinaryConstructorApp_hasType
    (context := context)
    (relationConstructor := axisEstablishedName)
    (beforeConstructor := establishedName)
    (afterConstructor := establishedName)
    (bodyType := axisEstablishedBodyType)
    (beforeFamily := signatureEvidence signature)
    (afterFamily := signatureEvidence signature)
    axisEstablishedConstant_hasType rfl
    (substitute_axisEstablishedBodyType signature)
    signatureTyping axisTyping judgmentTyping beforeTyping afterTyping
  simpa [axisNamedBinaryConstructorApp,
    axisNamedOutcomeConstructorApp, axisEstablishedApp, establishedApp]
    using generic

theorem axisEstablishedBodyType_hasType :
    AxisRefinementHasType axisRefinementContextS axisEstablishedBodyType
      (sortTm (axisBinaryBodyLevel evidenceLevel evidenceLevel)) := by
  rw [axisEstablishedBodyType_asBinary]
  apply axisBinaryAtSignatureType_hasType evidenceLevel evidenceLevel
  · exact signatureEvidence_hasType axisRefinementSignatureVar_hasType
  · exact signatureEvidence_hasType axisRefinementSignatureVar_hasType
  · apply axisRefinementApp_hasType
    · exact Presentation.HasType.var 4
    · exact Presentation.HasType.var 3
    · exact Presentation.HasType.var 2
    · apply establishedApp_hasAxisRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply establishedApp_hasAxisRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0

def axisEstablishedDeclarationLevel : LevelExpr :=
  .max signatureLevel (axisBinaryBodyLevel evidenceLevel evidenceLevel)

theorem axisEstablishedType_hasType :
    AxisRefinementHasType (.nil : Tower.Ctx 0)
      axisEstablishedType (sortTm axisEstablishedDeclarationLevel) := by
  simpa [axisEstablishedType, axisEstablishedDeclarationLevel] using
    (closeAxisRefinementBody_hasType axisEstablishedBodyType_hasType)

theorem axisRefutedBodyType_asBinary :
    axisRefutedBodyType =
      axisBinaryAtSignatureType refutedName refutedName (.var 0)
        (signatureObstruction (.var 0))
        (signatureObstruction (.var 0)) := by
  decide

@[simp] theorem substitute_axisRefutedBodyType
    (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature)
        axisRefutedBodyType =
      axisBinaryAtSignatureType refutedName refutedName signature
        (signatureObstruction signature)
        (signatureObstruction signature) := by
  simp [axisRefutedBodyType, axisBinaryAtSignatureType,
    axisNamedOutcomeConstructorApp, axisRefinementApp, refutedApp,
    Presentation.subst]

theorem axisRefutedApp_hasType {context : Tower.Ctx n}
    {signature axis judgment beforeObstruction afterObstruction :
      Tower.Tm n}
    (signatureTyping : AxisRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (axisTyping : AxisRefinementHasType context axis refinementAxisTm)
    (judgmentTyping : AxisRefinementHasType context judgment
      (signatureJudgment signature))
    (beforeTyping : AxisRefinementHasType context beforeObstruction
      (.app (signatureObstruction signature) judgment))
    (afterTyping : AxisRefinementHasType context afterObstruction
      (.app (signatureObstruction signature) judgment)) :
    AxisRefinementHasType context
      (axisRefutedApp signature axis judgment beforeObstruction
        afterObstruction)
      (axisRefinementApp signature axis judgment
        (refutedApp signature judgment beforeObstruction)
        (refutedApp signature judgment afterObstruction)) := by
  have generic := axisBinaryConstructorApp_hasType
    (context := context)
    (relationConstructor := axisRefutedName)
    (beforeConstructor := refutedName)
    (afterConstructor := refutedName)
    (bodyType := axisRefutedBodyType)
    (beforeFamily := signatureObstruction signature)
    (afterFamily := signatureObstruction signature)
    axisRefutedConstant_hasType rfl
    (substitute_axisRefutedBodyType signature)
    signatureTyping axisTyping judgmentTyping beforeTyping afterTyping
  simpa [axisNamedBinaryConstructorApp,
    axisNamedOutcomeConstructorApp, axisRefutedApp, refutedApp] using generic

theorem axisRefutedBodyType_hasType :
    AxisRefinementHasType axisRefinementContextS axisRefutedBodyType
      (sortTm (axisBinaryBodyLevel obstructionLevel obstructionLevel)) := by
  rw [axisRefutedBodyType_asBinary]
  apply axisBinaryAtSignatureType_hasType obstructionLevel obstructionLevel
  · exact signatureObstruction_hasType axisRefinementSignatureVar_hasType
  · exact signatureObstruction_hasType axisRefinementSignatureVar_hasType
  · apply axisRefinementApp_hasType
    · exact Presentation.HasType.var 4
    · exact Presentation.HasType.var 3
    · exact Presentation.HasType.var 2
    · apply refutedApp_hasAxisRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply refutedApp_hasAxisRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0

def axisRefutedDeclarationLevel : LevelExpr :=
  .max signatureLevel
    (axisBinaryBodyLevel obstructionLevel obstructionLevel)

theorem axisRefutedType_hasType :
    AxisRefinementHasType (.nil : Tower.Ctx 0)
      axisRefutedType (sortTm axisRefutedDeclarationLevel) := by
  simpa [axisRefutedType, axisRefutedDeclarationLevel] using
    (closeAxisRefinementBody_hasType axisRefutedBodyType_hasType)

theorem axisIncompleteBodyType_asBinary :
    axisIncompleteBodyType =
      axisBinaryAtSignatureType incompleteName incompleteName (.var 0)
        (signatureFrontier (.var 0)) (signatureFrontier (.var 0)) := by
  decide

@[simp] theorem substitute_axisIncompleteBodyType
    (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature)
        axisIncompleteBodyType =
      axisBinaryAtSignatureType incompleteName incompleteName signature
        (signatureFrontier signature) (signatureFrontier signature) := by
  simp [axisIncompleteBodyType, axisBinaryAtSignatureType,
    axisNamedOutcomeConstructorApp, axisRefinementApp, incompleteApp,
    Presentation.subst]

theorem axisIncompleteApp_hasType {context : Tower.Ctx n}
    {signature axis judgment beforeFrontier afterFrontier : Tower.Tm n}
    (signatureTyping : AxisRefinementHasType context signature
      (liftClosed outcomeSignatureType))
    (axisTyping : AxisRefinementHasType context axis refinementAxisTm)
    (judgmentTyping : AxisRefinementHasType context judgment
      (signatureJudgment signature))
    (beforeTyping : AxisRefinementHasType context beforeFrontier
      (.app (signatureFrontier signature) judgment))
    (afterTyping : AxisRefinementHasType context afterFrontier
      (.app (signatureFrontier signature) judgment)) :
    AxisRefinementHasType context
      (axisIncompleteApp signature axis judgment beforeFrontier
        afterFrontier)
      (axisRefinementApp signature axis judgment
        (incompleteApp signature judgment beforeFrontier)
        (incompleteApp signature judgment afterFrontier)) := by
  have generic := axisBinaryConstructorApp_hasType
    (context := context)
    (relationConstructor := axisIncompleteName)
    (beforeConstructor := incompleteName)
    (afterConstructor := incompleteName)
    (bodyType := axisIncompleteBodyType)
    (beforeFamily := signatureFrontier signature)
    (afterFamily := signatureFrontier signature)
    axisIncompleteConstant_hasType rfl
    (substitute_axisIncompleteBodyType signature)
    signatureTyping axisTyping judgmentTyping beforeTyping afterTyping
  simpa [axisNamedBinaryConstructorApp,
    axisNamedOutcomeConstructorApp, axisIncompleteApp, incompleteApp]
    using generic

theorem axisIncompleteBodyType_hasType :
    AxisRefinementHasType axisRefinementContextS axisIncompleteBodyType
      (sortTm (axisBinaryBodyLevel frontierLevel frontierLevel)) := by
  rw [axisIncompleteBodyType_asBinary]
  apply axisBinaryAtSignatureType_hasType frontierLevel frontierLevel
  · exact signatureFrontier_hasType axisRefinementSignatureVar_hasType
  · exact signatureFrontier_hasType axisRefinementSignatureVar_hasType
  · apply axisRefinementApp_hasType
    · exact Presentation.HasType.var 4
    · exact Presentation.HasType.var 3
    · exact Presentation.HasType.var 2
    · apply incompleteApp_hasAxisRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply incompleteApp_hasAxisRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0

def axisIncompleteDeclarationLevel : LevelExpr :=
  .max signatureLevel (axisBinaryBodyLevel frontierLevel frontierLevel)

theorem axisIncompleteType_hasType :
    AxisRefinementHasType (.nil : Tower.Ctx 0)
      axisIncompleteType (sortTm axisIncompleteDeclarationLevel) := by
  simpa [axisIncompleteType, axisIncompleteDeclarationLevel] using
    (closeAxisRefinementBody_hasType axisIncompleteBodyType_hasType)

/-! ### Formation and use of the dependent motive -/

def axisRefinementMotiveAtSignatureType (signature : Tower.Tm n) :
    Tower.Tm n :=
  .pi refinementAxisTm
    (.pi (signatureJudgment (Presentation.rename wk signature))
      (.pi
        (outcomeApp
          (Presentation.rename wk (Presentation.rename wk signature))
          (.var 0))
        (.pi
          (outcomeApp
            (Presentation.rename wk
              (Presentation.rename wk
                (Presentation.rename wk signature)))
            (.var 1))
          (.pi
            (axisRefinementApp
              (Presentation.rename wk
                (Presentation.rename wk
                  (Presentation.rename wk
                    (Presentation.rename wk signature))))
              (.var 3) (.var 2) (.var 1) (.var 0))
            (sortTm axisRefinementMotiveLevel)))))

theorem axisRefinementMotiveType_asAtSignature :
    axisRefinementMotiveType =
      axisRefinementMotiveAtSignatureType (.var 0) := by
  decide

def axisRefinementMotiveRelationLevel : LevelExpr :=
  .max axisRefinementLevel (.succ axisRefinementMotiveLevel)

def axisRefinementMotiveAfterLevel : LevelExpr :=
  .max outcomeLevel axisRefinementMotiveRelationLevel

def axisRefinementMotiveBeforeLevel : LevelExpr :=
  .max outcomeLevel axisRefinementMotiveAfterLevel

def axisRefinementMotiveJudgmentLevel : LevelExpr :=
  .max judgmentLevel axisRefinementMotiveBeforeLevel

def axisRefinementMotiveTypeLevel : LevelExpr :=
  .max refinementAxisLevel axisRefinementMotiveJudgmentLevel

theorem axisRefinementMotiveType_hasType :
    AxisRefinementHasType axisRefinementContextS
      axisRefinementMotiveType
      (sortTm axisRefinementMotiveTypeLevel) := by
  rw [axisRefinementMotiveType_asAtSignature]
  unfold axisRefinementMotiveAtSignatureType
    axisRefinementMotiveTypeLevel axisRefinementMotiveJudgmentLevel
    axisRefinementMotiveBeforeLevel axisRefinementMotiveAfterLevel
    axisRefinementMotiveRelationLevel
  apply Presentation.HasType.piForm
  · exact refinementAxisTm_hasAxisRefinementType
  · exact .sort refinementAxisLevel
  · apply Presentation.HasType.piForm
    · exact signatureJudgment_hasType
        axisRefinementSignatureVarInSA_hasType
    · exact .sort judgmentLevel
    · apply Presentation.HasType.piForm
      · apply outcomeApp_hasTypeWith
        · exact includeOutcomeInAxisRefinement outcomeConstant_hasType
        · exact Presentation.HasType.var 2
        · exact Presentation.HasType.var 0
      · exact .sort outcomeLevel
      · apply Presentation.HasType.piForm
        · apply outcomeApp_hasTypeWith
          · exact includeOutcomeInAxisRefinement outcomeConstant_hasType
          · exact Presentation.HasType.var 3
          · exact Presentation.HasType.var 1
        · exact .sort outcomeLevel
        · apply Presentation.HasType.piForm
          · apply axisRefinementApp_hasType
            · exact Presentation.HasType.var 4
            · exact Presentation.HasType.var 3
            · exact Presentation.HasType.var 2
            · exact Presentation.HasType.var 1
            · exact Presentation.HasType.var 0
          · exact .sort axisRefinementLevel
          · exact .headType (.sort axisRefinementMotiveLevel)
          · exact .sort (.succ axisRefinementMotiveLevel)
          · exact .sorts axisRefinementLevel
              (.succ axisRefinementMotiveLevel)
        · exact .sort axisRefinementMotiveRelationLevel
        · exact .sorts outcomeLevel axisRefinementMotiveRelationLevel
      · exact .sort axisRefinementMotiveAfterLevel
      · exact .sorts outcomeLevel axisRefinementMotiveAfterLevel
    · exact .sort axisRefinementMotiveBeforeLevel
    · exact .sorts judgmentLevel axisRefinementMotiveBeforeLevel
  · exact .sort axisRefinementMotiveJudgmentLevel
  · exact .sorts refinementAxisLevel axisRefinementMotiveJudgmentLevel

def axisRefinementMotiveAfterAxisType
    (signature axis : Tower.Tm n) : Tower.Tm n :=
  .pi (signatureJudgment signature)
    (.pi (outcomeApp (Presentation.rename wk signature) (.var 0))
      (.pi
        (outcomeApp
          (Presentation.rename wk (Presentation.rename wk signature))
          (.var 1))
        (.pi
          (axisRefinementApp
            (Presentation.rename wk
              (Presentation.rename wk (Presentation.rename wk signature)))
            (Presentation.rename wk
              (Presentation.rename wk (Presentation.rename wk axis)))
            (.var 2) (.var 1) (.var 0))
          (sortTm axisRefinementMotiveLevel))))

def axisRefinementMotiveAfterJudgmentType
    (signature axis judgment : Tower.Tm n) : Tower.Tm n :=
  .pi (outcomeApp signature judgment)
    (.pi
      (outcomeApp (Presentation.rename wk signature)
        (Presentation.rename wk judgment))
      (.pi
        (axisRefinementApp
          (Presentation.rename wk (Presentation.rename wk signature))
          (Presentation.rename wk (Presentation.rename wk axis))
          (Presentation.rename wk (Presentation.rename wk judgment))
          (.var 1) (.var 0))
        (sortTm axisRefinementMotiveLevel)))

def axisRefinementMotiveAfterBeforeType
    (signature axis judgment before : Tower.Tm n) : Tower.Tm n :=
  .pi (outcomeApp signature judgment)
    (.pi
      (axisRefinementApp (Presentation.rename wk signature)
        (Presentation.rename wk axis)
        (Presentation.rename wk judgment)
        (Presentation.rename wk before) (.var 0))
      (sortTm axisRefinementMotiveLevel))

def axisRefinementMotiveAfterAfterType
    (signature axis judgment before after : Tower.Tm n) : Tower.Tm n :=
  .pi (axisRefinementApp signature axis judgment before after)
    (sortTm axisRefinementMotiveLevel)

theorem axisRefinementMotiveApp_hasType {context : Tower.Ctx n}
    {signature motive axis judgment before after refinement : Tower.Tm n}
    (motiveTyping : AxisRefinementHasType context motive
      (axisRefinementMotiveAtSignatureType signature))
    (axisTyping : AxisRefinementHasType context axis refinementAxisTm)
    (judgmentTyping : AxisRefinementHasType context judgment
      (signatureJudgment signature))
    (beforeTyping : AxisRefinementHasType context before
      (outcomeApp signature judgment))
    (afterTyping : AxisRefinementHasType context after
      (outcomeApp signature judgment))
    (refinementTyping : AxisRefinementHasType context refinement
      (axisRefinementApp signature axis judgment before after)) :
    AxisRefinementHasType context
      (axisRefinementMotiveApp motive axis judgment before after refinement)
      (sortTm axisRefinementMotiveLevel) := by
  have afterAxis := Presentation.HasType.appElim motiveTyping axisTyping
  have afterAxisNormalized :
      AxisRefinementHasType context (.app motive axis)
        (axisRefinementMotiveAfterAxisType signature axis) := by
    convert afterAxis using 1
    all_goals simp [axisRefinementMotiveAfterAxisType,
      axisRefinementApp, Presentation.inst0, Presentation.subst]
  have afterJudgment := Presentation.HasType.appElim afterAxisNormalized
    judgmentTyping
  have afterJudgmentNormalized :
      AxisRefinementHasType context (.app (.app motive axis) judgment)
        (axisRefinementMotiveAfterJudgmentType signature axis judgment) := by
    convert afterJudgment using 1
    all_goals simp [axisRefinementMotiveAfterJudgmentType, axisRefinementApp,
      Presentation.inst0, Presentation.subst]
  have afterBefore := Presentation.HasType.appElim afterJudgmentNormalized
    beforeTyping
  have afterBeforeNormalized :
      AxisRefinementHasType context
        (.app (.app (.app motive axis) judgment) before)
        (axisRefinementMotiveAfterBeforeType signature axis judgment
          before) := by
    convert afterBefore using 1
    all_goals simp [axisRefinementMotiveAfterBeforeType, axisRefinementApp,
      Presentation.inst0, Presentation.subst]
  have afterAfter := Presentation.HasType.appElim afterBeforeNormalized
    afterTyping
  have afterAfterNormalized :
      AxisRefinementHasType context
        (.app (.app (.app (.app motive axis) judgment) before) after)
        (axisRefinementMotiveAfterAfterType signature axis judgment
          before after) := by
    convert afterAfter using 1
    all_goals simp [axisRefinementMotiveAfterAfterType, axisRefinementApp,
      Presentation.inst0, Presentation.subst]
  have result := Presentation.HasType.appElim afterAfterNormalized
    refinementTyping
  simpa [axisRefinementMotiveApp, axisRefinementMotiveAfterAfterType,
    sortTm, Presentation.inst0, Presentation.subst] using result

/-! ### Formation of the ten dependent branches -/

def axisRefinementContextSM : Tower.Ctx 2 :=
  .snoc axisRefinementContextS axisRefinementMotiveType

theorem axisRefinementSignatureVarInSM_hasType :
    AxisRefinementHasType axisRefinementContextSM (.var 1)
      (liftClosed outcomeSignatureType) := by
  have variableTyping :=
    (Presentation.HasType.var (R := axisRefinementRules)
      (Γ := axisRefinementContextSM) (1 : Fin 2))
  have lookupEquality :
      Presentation.Ctx.lookup axisRefinementContextSM (1 : Fin 2) =
        liftClosed outcomeSignatureType := by
    decide
  simpa only [lookupEquality] using variableTyping

theorem axisRefinementMotiveVarInSM_hasType :
    AxisRefinementHasType axisRefinementContextSM (.var 0)
      (axisRefinementMotiveAtSignatureType (.var 1)) := by
  have variableTyping :=
    (Presentation.HasType.var (R := axisRefinementRules)
      (Γ := axisRefinementContextSM) (0 : Fin 2))
  have lookupEquality :
      Presentation.Ctx.lookup axisRefinementContextSM (0 : Fin 2) =
        axisRefinementMotiveAtSignatureType (.var 1) := by
    decide
  simpa only [lookupEquality] using variableTyping

def axisBinaryCaseContextSMAJ : Tower.Ctx 4 :=
  .snoc
    (.snoc axisRefinementContextSM refinementAxisTm)
    (signatureJudgment (.var 2))

def axisBinaryCaseContextSMAJW (beforeFamily : Tower.Tm 2) :
    Tower.Ctx 5 :=
  .snoc axisBinaryCaseContextSMAJ
    (.app
      (Presentation.rename wk (Presentation.rename wk beforeFamily))
      (.var 0))

def axisBinaryCaseContextSMAJWW
    (beforeFamily afterFamily : Tower.Tm 2) : Tower.Ctx 6 :=
  .snoc (axisBinaryCaseContextSMAJW beforeFamily)
    (.app
      (Presentation.rename wk
        (Presentation.rename wk (Presentation.rename wk afterFamily)))
      (.var 1))

def axisBinaryCaseAtSignatureType
    (relationConstructor beforeConstructor afterConstructor : DeclName)
    (beforeFamily afterFamily : Tower.Tm 2) : Tower.Tm 2 :=
  .pi refinementAxisTm
    (.pi (signatureJudgment (.var 2))
      (.pi
        (.app
          (Presentation.rename wk (Presentation.rename wk beforeFamily))
          (.var 0))
        (.pi
          (.app
            (Presentation.rename wk
              (Presentation.rename wk
                (Presentation.rename wk afterFamily)))
            (.var 1))
          (axisRefinementMotiveApp (.var 4) (.var 3) (.var 2)
            (axisNamedOutcomeConstructorApp beforeConstructor
              (.var 5) (.var 2) (.var 1))
            (axisNamedOutcomeConstructorApp afterConstructor
              (.var 5) (.var 2) (.var 0))
            (axisNamedBinaryConstructorApp relationConstructor
              (.var 5) (.var 3) (.var 2) (.var 1) (.var 0))))))

def axisBinaryCaseAfterLevel (afterLevel : LevelExpr) : LevelExpr :=
  .max afterLevel axisRefinementMotiveLevel

def axisBinaryCaseBeforeLevel
    (beforeLevel afterLevel : LevelExpr) : LevelExpr :=
  .max beforeLevel (axisBinaryCaseAfterLevel afterLevel)

def axisBinaryCaseJudgmentLevel
    (beforeLevel afterLevel : LevelExpr) : LevelExpr :=
  .max judgmentLevel (axisBinaryCaseBeforeLevel beforeLevel afterLevel)

def axisBinaryCaseLevel
    (beforeLevel afterLevel : LevelExpr) : LevelExpr :=
  .max refinementAxisLevel
    (axisBinaryCaseJudgmentLevel beforeLevel afterLevel)

theorem axisBinaryCaseAtSignatureType_hasType
    (beforeLevel afterLevel : LevelExpr)
    {relationConstructor beforeConstructor afterConstructor : DeclName}
    {beforeFamily afterFamily : Tower.Tm 2}
    (beforeFamilyTyping : AxisRefinementHasType axisRefinementContextSM
      beforeFamily
      (familyType beforeLevel (signatureJudgment (.var 1))))
    (afterFamilyTyping : AxisRefinementHasType axisRefinementContextSM
      afterFamily
      (familyType afterLevel (signatureJudgment (.var 1))))
    (resultTyping : AxisRefinementHasType
      (axisBinaryCaseContextSMAJWW beforeFamily afterFamily)
      (axisRefinementMotiveApp (.var 4) (.var 3) (.var 2)
        (axisNamedOutcomeConstructorApp beforeConstructor
          (.var 5) (.var 2) (.var 1))
        (axisNamedOutcomeConstructorApp afterConstructor
          (.var 5) (.var 2) (.var 0))
        (axisNamedBinaryConstructorApp relationConstructor
          (.var 5) (.var 3) (.var 2) (.var 1) (.var 0)))
      (sortTm axisRefinementMotiveLevel)) :
    AxisRefinementHasType axisRefinementContextSM
      (axisBinaryCaseAtSignatureType relationConstructor
        beforeConstructor afterConstructor beforeFamily afterFamily)
      (sortTm (axisBinaryCaseLevel beforeLevel afterLevel)) := by
  unfold axisBinaryCaseAtSignatureType axisBinaryCaseLevel
    axisBinaryCaseJudgmentLevel axisBinaryCaseBeforeLevel
    axisBinaryCaseAfterLevel
  apply Presentation.HasType.piForm
  · exact refinementAxisTm_hasAxisRefinementType
  · exact .sort refinementAxisLevel
  · apply Presentation.HasType.piForm
    · exact signatureJudgment_hasType
        (axisRefinementSignatureVarInSM_hasType.weaken
          (extension := refinementAxisTm))
    · exact .sort judgmentLevel
    · apply Presentation.HasType.piForm
      · apply familyApp_hasType
        · have first := beforeFamilyTyping.weaken
            (extension := refinementAxisTm)
          have second := first.weaken
            (extension := signatureJudgment (.var 2))
          simpa [axisBinaryCaseContextSMAJ, axisRefinementContextSM,
            axisRefinementContextS, familyType, sortTm,
            Presentation.rename] using second
        · exact Presentation.HasType.var 0
      · exact .sort beforeLevel
      · apply Presentation.HasType.piForm
        · apply familyApp_hasType
          · have first := afterFamilyTyping.weaken
              (extension := refinementAxisTm)
            have second := first.weaken
              (extension := signatureJudgment (.var 2))
            have third := second.weaken
              (extension :=
                .app
                  (Presentation.rename wk
                    (Presentation.rename wk beforeFamily))
                  (.var 0))
            simpa [axisBinaryCaseContextSMAJW,
              axisBinaryCaseContextSMAJ, axisRefinementContextSM,
              axisRefinementContextS, familyType, sortTm,
              Presentation.rename] using third
          · exact Presentation.HasType.var 1
        · exact .sort afterLevel
        · simpa [axisBinaryCaseContextSMAJWW,
            axisBinaryCaseContextSMAJW, axisBinaryCaseContextSMAJ,
            axisRefinementContextSM, axisRefinementContextS, sortTm,
            Presentation.rename] using resultTyping
        · exact .sort axisRefinementMotiveLevel
        · exact .sorts afterLevel axisRefinementMotiveLevel
      · exact .sort (axisBinaryCaseAfterLevel afterLevel)
      · exact .sorts beforeLevel (axisBinaryCaseAfterLevel afterLevel)
    · exact .sort (axisBinaryCaseBeforeLevel beforeLevel afterLevel)
    · exact .sorts judgmentLevel
        (axisBinaryCaseBeforeLevel beforeLevel afterLevel)
  · exact .sort (axisBinaryCaseJudgmentLevel beforeLevel afterLevel)
  · exact .sorts refinementAxisLevel
      (axisBinaryCaseJudgmentLevel beforeLevel afterLevel)

def fixedAxisBinaryCaseContextSMJ : Tower.Ctx 3 :=
  .snoc axisRefinementContextSM (signatureJudgment (.var 1))

def fixedAxisBinaryCaseContextSMJW (beforeFamily : Tower.Tm 2) :
    Tower.Ctx 4 :=
  .snoc fixedAxisBinaryCaseContextSMJ
    (.app (Presentation.rename wk beforeFamily) (.var 0))

def fixedAxisBinaryCaseContextSMJWW
    (beforeFamily afterFamily : Tower.Tm 2) : Tower.Ctx 5 :=
  .snoc (fixedAxisBinaryCaseContextSMJW beforeFamily)
    (.app
      (Presentation.rename wk (Presentation.rename wk afterFamily))
      (.var 1))

def fixedAxisBinaryCaseAtSignatureType
    (axis : Tower.Tm 2)
    (relationConstructor beforeConstructor afterConstructor : DeclName)
    (beforeFamily afterFamily : Tower.Tm 2) : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (.app (Presentation.rename wk beforeFamily) (.var 0))
      (.pi
        (.app
          (Presentation.rename wk (Presentation.rename wk afterFamily))
          (.var 1))
        (axisRefinementMotiveApp (.var 3)
          (Presentation.rename wk
            (Presentation.rename wk (Presentation.rename wk axis)))
          (.var 2)
          (axisNamedOutcomeConstructorApp beforeConstructor
            (.var 4) (.var 2) (.var 1))
          (axisNamedOutcomeConstructorApp afterConstructor
            (.var 4) (.var 2) (.var 0))
          (axisNamedFixedBinaryConstructorApp relationConstructor
            (.var 4) (.var 2) (.var 1) (.var 0)))))

def fixedAxisBinaryCaseAfterLevel (afterLevel : LevelExpr) : LevelExpr :=
  .max afterLevel axisRefinementMotiveLevel

def fixedAxisBinaryCaseBeforeLevel
    (beforeLevel afterLevel : LevelExpr) : LevelExpr :=
  .max beforeLevel (fixedAxisBinaryCaseAfterLevel afterLevel)

def fixedAxisBinaryCaseLevel
    (beforeLevel afterLevel : LevelExpr) : LevelExpr :=
  .max judgmentLevel
    (fixedAxisBinaryCaseBeforeLevel beforeLevel afterLevel)

theorem fixedAxisBinaryCaseAtSignatureType_hasType
    (beforeLevel afterLevel : LevelExpr)
    {axis : Tower.Tm 2}
    {relationConstructor beforeConstructor afterConstructor : DeclName}
    {beforeFamily afterFamily : Tower.Tm 2}
    (beforeFamilyTyping : AxisRefinementHasType axisRefinementContextSM
      beforeFamily
      (familyType beforeLevel (signatureJudgment (.var 1))))
    (afterFamilyTyping : AxisRefinementHasType axisRefinementContextSM
      afterFamily
      (familyType afterLevel (signatureJudgment (.var 1))))
    (resultTyping : AxisRefinementHasType
      (fixedAxisBinaryCaseContextSMJWW beforeFamily afterFamily)
      (axisRefinementMotiveApp (.var 3)
        (Presentation.rename wk
          (Presentation.rename wk (Presentation.rename wk axis)))
        (.var 2)
        (axisNamedOutcomeConstructorApp beforeConstructor
          (.var 4) (.var 2) (.var 1))
        (axisNamedOutcomeConstructorApp afterConstructor
          (.var 4) (.var 2) (.var 0))
        (axisNamedFixedBinaryConstructorApp relationConstructor
          (.var 4) (.var 2) (.var 1) (.var 0)))
      (sortTm axisRefinementMotiveLevel)) :
    AxisRefinementHasType axisRefinementContextSM
      (fixedAxisBinaryCaseAtSignatureType axis relationConstructor
        beforeConstructor afterConstructor beforeFamily afterFamily)
      (sortTm (fixedAxisBinaryCaseLevel beforeLevel afterLevel)) := by
  unfold fixedAxisBinaryCaseAtSignatureType fixedAxisBinaryCaseLevel
    fixedAxisBinaryCaseBeforeLevel fixedAxisBinaryCaseAfterLevel
  apply Presentation.HasType.piForm
  · exact signatureJudgment_hasType axisRefinementSignatureVarInSM_hasType
  · exact .sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply familyApp_hasType
      · have weakened := beforeFamilyTyping.weaken
          (extension := signatureJudgment (.var 1))
        simpa [fixedAxisBinaryCaseContextSMJ,
          axisRefinementContextSM, axisRefinementContextS,
          familyType, sortTm, Presentation.rename] using weakened
      · exact Presentation.HasType.var 0
    · exact .sort beforeLevel
    · apply Presentation.HasType.piForm
      · apply familyApp_hasType
        · have first := afterFamilyTyping.weaken
            (extension := signatureJudgment (.var 1))
          have second := first.weaken
            (extension := .app (Presentation.rename wk beforeFamily)
              (.var 0))
          simpa [fixedAxisBinaryCaseContextSMJW,
            fixedAxisBinaryCaseContextSMJ, axisRefinementContextSM,
            axisRefinementContextS, familyType, sortTm,
            Presentation.rename] using second
        · exact Presentation.HasType.var 1
      · exact .sort afterLevel
      · simpa [fixedAxisBinaryCaseContextSMJWW,
          fixedAxisBinaryCaseContextSMJW,
          fixedAxisBinaryCaseContextSMJ, axisRefinementContextSM,
          axisRefinementContextS, sortTm, Presentation.rename] using
          resultTyping
      · exact .sort axisRefinementMotiveLevel
      · exact .sorts afterLevel axisRefinementMotiveLevel
    · exact .sort (fixedAxisBinaryCaseAfterLevel afterLevel)
    · exact .sorts beforeLevel
        (fixedAxisBinaryCaseAfterLevel afterLevel)
  · exact .sort (fixedAxisBinaryCaseBeforeLevel beforeLevel afterLevel)
  · exact .sorts judgmentLevel
      (fixedAxisBinaryCaseBeforeLevel beforeLevel afterLevel)

def fixedAxisUnaryCaseContextSMJW (payloadFamily : Tower.Tm 2) :
    Tower.Ctx 4 :=
  .snoc fixedAxisBinaryCaseContextSMJ
    (.app (Presentation.rename wk payloadFamily) (.var 0))

def fixedAxisUnaryCaseAtSignatureType
    (axis : Tower.Tm 2) (relationConstructor outcomeConstructor : DeclName)
    (payloadFamily : Tower.Tm 2) : Tower.Tm 2 :=
  .pi (signatureJudgment (.var 1))
    (.pi (.app (Presentation.rename wk payloadFamily) (.var 0))
      (axisRefinementMotiveApp (.var 2)
        (Presentation.rename wk (Presentation.rename wk axis))
        (.var 1)
        (axisNamedOutcomeConstructorApp outcomeConstructor
          (.var 3) (.var 1) (.var 0))
        (axisNamedOutcomeConstructorApp outcomeConstructor
          (.var 3) (.var 1) (.var 0))
        (axisNamedFixedUnaryConstructorApp relationConstructor
          (.var 3) (.var 1) (.var 0))))

def fixedAxisUnaryCaseWitnessLevel (payloadLevel : LevelExpr) : LevelExpr :=
  .max payloadLevel axisRefinementMotiveLevel

def fixedAxisUnaryCaseLevel (payloadLevel : LevelExpr) : LevelExpr :=
  .max judgmentLevel (fixedAxisUnaryCaseWitnessLevel payloadLevel)

theorem fixedAxisUnaryCaseAtSignatureType_hasType
    (payloadLevel : LevelExpr)
    {axis : Tower.Tm 2}
    {relationConstructor outcomeConstructor : DeclName}
    {payloadFamily : Tower.Tm 2}
    (payloadFamilyTyping : AxisRefinementHasType axisRefinementContextSM
      payloadFamily
      (familyType payloadLevel (signatureJudgment (.var 1))))
    (resultTyping : AxisRefinementHasType
      (fixedAxisUnaryCaseContextSMJW payloadFamily)
      (axisRefinementMotiveApp (.var 2)
        (Presentation.rename wk (Presentation.rename wk axis))
        (.var 1)
        (axisNamedOutcomeConstructorApp outcomeConstructor
          (.var 3) (.var 1) (.var 0))
        (axisNamedOutcomeConstructorApp outcomeConstructor
          (.var 3) (.var 1) (.var 0))
        (axisNamedFixedUnaryConstructorApp relationConstructor
          (.var 3) (.var 1) (.var 0)))
      (sortTm axisRefinementMotiveLevel)) :
    AxisRefinementHasType axisRefinementContextSM
      (fixedAxisUnaryCaseAtSignatureType axis relationConstructor
        outcomeConstructor payloadFamily)
      (sortTm (fixedAxisUnaryCaseLevel payloadLevel)) := by
  unfold fixedAxisUnaryCaseAtSignatureType fixedAxisUnaryCaseLevel
    fixedAxisUnaryCaseWitnessLevel
  apply Presentation.HasType.piForm
  · exact signatureJudgment_hasType axisRefinementSignatureVarInSM_hasType
  · exact .sort judgmentLevel
  · apply Presentation.HasType.piForm
    · apply familyApp_hasType
      · have weakened := payloadFamilyTyping.weaken
          (extension := signatureJudgment (.var 1))
        simpa [fixedAxisBinaryCaseContextSMJ,
          axisRefinementContextSM, axisRefinementContextS,
          familyType, sortTm, Presentation.rename] using weakened
      · exact Presentation.HasType.var 0
    · exact .sort payloadLevel
    · simpa [fixedAxisUnaryCaseContextSMJW,
        fixedAxisBinaryCaseContextSMJ, axisRefinementContextSM,
        axisRefinementContextS, sortTm, Presentation.rename] using
        resultTyping
    · exact .sort axisRefinementMotiveLevel
    · exact .sorts payloadLevel axisRefinementMotiveLevel
  · exact .sort (fixedAxisUnaryCaseWitnessLevel payloadLevel)
  · exact .sorts judgmentLevel
      (fixedAxisUnaryCaseWitnessLevel payloadLevel)

theorem axisRefinementMotiveAtSignature_afterFourWeakenings :
    Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk
            (Presentation.rename wk
              (axisRefinementMotiveAtSignatureType
                (.var 1 : Tower.Tm 2))))) =
      axisRefinementMotiveAtSignatureType (.var 5 : Tower.Tm 6) := by
  decide

theorem axisRefinementMotiveVarInAxisBinaryCase_hasType
    (beforeFamily afterFamily : Tower.Tm 2) :
    AxisRefinementHasType
      (axisBinaryCaseContextSMAJWW beforeFamily afterFamily) (.var 4)
      (axisRefinementMotiveAtSignatureType (.var 5)) := by
  have first := axisRefinementMotiveVarInSM_hasType.weaken
    (extension := refinementAxisTm)
  have second := first.weaken
    (extension := signatureJudgment (.var 2))
  have third := second.weaken
    (extension :=
      .app (Presentation.rename wk (Presentation.rename wk beforeFamily))
        (.var 0))
  have fourth := third.weaken
    (extension :=
      .app
        (Presentation.rename wk
          (Presentation.rename wk (Presentation.rename wk afterFamily)))
        (.var 1))
  rw [axisRefinementMotiveAtSignature_afterFourWeakenings] at fourth
  simpa [axisBinaryCaseContextSMAJWW, axisBinaryCaseContextSMAJW,
    axisBinaryCaseContextSMAJ, axisRefinementContextSM,
    Presentation.rename, wk] using fourth

theorem axisRefinementMotiveAtSignature_afterThreeWeakenings :
    Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk
            (axisRefinementMotiveAtSignatureType
              (.var 1 : Tower.Tm 2)))) =
      axisRefinementMotiveAtSignatureType (.var 4 : Tower.Tm 5) := by
  decide

theorem axisRefinementMotiveVarInFixedBinaryCase_hasType
    (beforeFamily afterFamily : Tower.Tm 2) :
    AxisRefinementHasType
      (fixedAxisBinaryCaseContextSMJWW beforeFamily afterFamily) (.var 3)
      (axisRefinementMotiveAtSignatureType (.var 4)) := by
  have first := axisRefinementMotiveVarInSM_hasType.weaken
    (extension := signatureJudgment (.var 1))
  have second := first.weaken
    (extension := .app (Presentation.rename wk beforeFamily) (.var 0))
  have third := second.weaken
    (extension :=
      .app (Presentation.rename wk (Presentation.rename wk afterFamily))
        (.var 1))
  rw [axisRefinementMotiveAtSignature_afterThreeWeakenings] at third
  simpa [fixedAxisBinaryCaseContextSMJWW,
    fixedAxisBinaryCaseContextSMJW, fixedAxisBinaryCaseContextSMJ,
    axisRefinementContextSM, Presentation.rename, wk] using third

theorem axisRefinementMotiveAtSignature_afterTwoWeakenings :
    Presentation.rename wk
        (Presentation.rename wk
          (axisRefinementMotiveAtSignatureType
            (.var 1 : Tower.Tm 2))) =
      axisRefinementMotiveAtSignatureType (.var 3 : Tower.Tm 4) := by
  decide

theorem axisRefinementMotiveVarInFixedUnaryCase_hasType
    (payloadFamily : Tower.Tm 2) :
    AxisRefinementHasType
      (fixedAxisUnaryCaseContextSMJW payloadFamily) (.var 2)
      (axisRefinementMotiveAtSignatureType (.var 3)) := by
  have first := axisRefinementMotiveVarInSM_hasType.weaken
    (extension := signatureJudgment (.var 1))
  have second := first.weaken
    (extension := .app (Presentation.rename wk payloadFamily) (.var 0))
  rw [axisRefinementMotiveAtSignature_afterTwoWeakenings] at second
  simpa [fixedAxisUnaryCaseContextSMJW,
    fixedAxisBinaryCaseContextSMJ, axisRefinementContextSM,
    Presentation.rename, wk] using second

theorem axisEstablishedCaseType_asGeneric :
    axisEstablishedCaseType =
      axisBinaryCaseAtSignatureType axisEstablishedName establishedName
        establishedName (signatureEvidence (.var 1))
        (signatureEvidence (.var 1)) := by
  decide

theorem axisEstablishedCaseType_hasType :
    AxisRefinementHasType axisRefinementContextSM axisEstablishedCaseType
      (sortTm (axisBinaryCaseLevel evidenceLevel evidenceLevel)) := by
  rw [axisEstablishedCaseType_asGeneric]
  apply axisBinaryCaseAtSignatureType_hasType evidenceLevel evidenceLevel
  · exact signatureEvidence_hasType axisRefinementSignatureVarInSM_hasType
  · exact signatureEvidence_hasType axisRefinementSignatureVarInSM_hasType
  · apply axisRefinementMotiveApp_hasType
    · exact axisRefinementMotiveVarInAxisBinaryCase_hasType _ _
    · exact Presentation.HasType.var 3
    · exact Presentation.HasType.var 2
    · apply establishedApp_hasAxisRefinementType
      · exact Presentation.HasType.var 5
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply establishedApp_hasAxisRefinementType
      · exact Presentation.HasType.var 5
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0
    · apply axisEstablishedApp_hasType
      · exact Presentation.HasType.var 5
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0

theorem axisRefutedCaseType_asGeneric :
    axisRefutedCaseType =
      axisBinaryCaseAtSignatureType axisRefutedName refutedName
        refutedName (signatureObstruction (.var 1))
        (signatureObstruction (.var 1)) := by
  decide

theorem axisRefutedCaseType_hasType :
    AxisRefinementHasType axisRefinementContextSM axisRefutedCaseType
      (sortTm (axisBinaryCaseLevel obstructionLevel obstructionLevel)) := by
  rw [axisRefutedCaseType_asGeneric]
  apply axisBinaryCaseAtSignatureType_hasType obstructionLevel
    obstructionLevel
  · exact signatureObstruction_hasType
      axisRefinementSignatureVarInSM_hasType
  · exact signatureObstruction_hasType
      axisRefinementSignatureVarInSM_hasType
  · apply axisRefinementMotiveApp_hasType
    · exact axisRefinementMotiveVarInAxisBinaryCase_hasType _ _
    · exact Presentation.HasType.var 3
    · exact Presentation.HasType.var 2
    · apply refutedApp_hasAxisRefinementType
      · exact Presentation.HasType.var 5
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply refutedApp_hasAxisRefinementType
      · exact Presentation.HasType.var 5
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0
    · apply axisRefutedApp_hasType
      · exact Presentation.HasType.var 5
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0

theorem axisIncompleteCaseType_asGeneric :
    axisIncompleteCaseType =
      axisBinaryCaseAtSignatureType axisIncompleteName incompleteName
        incompleteName (signatureFrontier (.var 1))
        (signatureFrontier (.var 1)) := by
  decide

theorem axisIncompleteCaseType_hasType :
    AxisRefinementHasType axisRefinementContextSM axisIncompleteCaseType
      (sortTm (axisBinaryCaseLevel frontierLevel frontierLevel)) := by
  rw [axisIncompleteCaseType_asGeneric]
  apply axisBinaryCaseAtSignatureType_hasType frontierLevel frontierLevel
  · exact signatureFrontier_hasType axisRefinementSignatureVarInSM_hasType
  · exact signatureFrontier_hasType axisRefinementSignatureVarInSM_hasType
  · apply axisRefinementMotiveApp_hasType
    · exact axisRefinementMotiveVarInAxisBinaryCase_hasType _ _
    · exact Presentation.HasType.var 3
    · exact Presentation.HasType.var 2
    · apply incompleteApp_hasAxisRefinementType
      · exact Presentation.HasType.var 5
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply incompleteApp_hasAxisRefinementType
      · exact Presentation.HasType.var 5
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0
    · apply axisIncompleteApp_hasType
      · exact Presentation.HasType.var 5
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0

theorem budgetOutsideRefinementCaseType_asGeneric :
    budgetOutsideRefinementCaseType =
      fixedAxisUnaryCaseAtSignatureType refinementAxisBudgetTm
        budgetOutsideRefinementName outsideFragmentName
        (signatureBoundary (.var 1)) := by
  decide

theorem budgetOutsideRefinementCaseType_hasType :
    AxisRefinementHasType axisRefinementContextSM
      budgetOutsideRefinementCaseType
      (sortTm (fixedAxisUnaryCaseLevel boundaryLevel)) := by
  rw [budgetOutsideRefinementCaseType_asGeneric]
  apply fixedAxisUnaryCaseAtSignatureType_hasType boundaryLevel
  · exact signatureBoundary_hasType axisRefinementSignatureVarInSM_hasType
  · apply axisRefinementMotiveApp_hasType
    · exact axisRefinementMotiveVarInFixedUnaryCase_hasType _
    · exact refinementAxisBudgetTm_hasAxisRefinementType
    · exact Presentation.HasType.var 1
    · apply outsideFragmentApp_hasAxisRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0
    · apply outsideFragmentApp_hasAxisRefinementType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0
    · apply budgetOutsideRefinementApp_hasType
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0

theorem budgetIncompleteEstablishedRefinementCaseType_asGeneric :
    budgetIncompleteEstablishedRefinementCaseType =
      fixedAxisBinaryCaseAtSignatureType refinementAxisBudgetTm
        budgetIncompleteEstablishedRefinementName incompleteName
        establishedName (signatureFrontier (.var 1))
        (signatureEvidence (.var 1)) := by
  decide

theorem budgetIncompleteEstablishedRefinementCaseType_hasType :
    AxisRefinementHasType axisRefinementContextSM
      budgetIncompleteEstablishedRefinementCaseType
      (sortTm
        (fixedAxisBinaryCaseLevel frontierLevel evidenceLevel)) := by
  rw [budgetIncompleteEstablishedRefinementCaseType_asGeneric]
  apply fixedAxisBinaryCaseAtSignatureType_hasType frontierLevel evidenceLevel
  · exact signatureFrontier_hasType axisRefinementSignatureVarInSM_hasType
  · exact signatureEvidence_hasType axisRefinementSignatureVarInSM_hasType
  · apply axisRefinementMotiveApp_hasType
    · exact axisRefinementMotiveVarInFixedBinaryCase_hasType _ _
    · exact refinementAxisBudgetTm_hasAxisRefinementType
    · exact Presentation.HasType.var 2
    · apply incompleteApp_hasAxisRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply establishedApp_hasAxisRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0
    · apply budgetIncompleteEstablishedRefinementApp_hasType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0

theorem budgetIncompleteRefutedRefinementCaseType_asGeneric :
    budgetIncompleteRefutedRefinementCaseType =
      fixedAxisBinaryCaseAtSignatureType refinementAxisBudgetTm
        budgetIncompleteRefutedRefinementName incompleteName refutedName
        (signatureFrontier (.var 1))
        (signatureObstruction (.var 1)) := by
  decide

theorem budgetIncompleteRefutedRefinementCaseType_hasType :
    AxisRefinementHasType axisRefinementContextSM
      budgetIncompleteRefutedRefinementCaseType
      (sortTm
        (fixedAxisBinaryCaseLevel frontierLevel obstructionLevel)) := by
  rw [budgetIncompleteRefutedRefinementCaseType_asGeneric]
  apply fixedAxisBinaryCaseAtSignatureType_hasType frontierLevel
    obstructionLevel
  · exact signatureFrontier_hasType axisRefinementSignatureVarInSM_hasType
  · exact signatureObstruction_hasType
      axisRefinementSignatureVarInSM_hasType
  · apply axisRefinementMotiveApp_hasType
    · exact axisRefinementMotiveVarInFixedBinaryCase_hasType _ _
    · exact refinementAxisBudgetTm_hasAxisRefinementType
    · exact Presentation.HasType.var 2
    · apply incompleteApp_hasAxisRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply refutedApp_hasAxisRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0
    · apply budgetIncompleteRefutedRefinementApp_hasType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0

theorem authorityOutsideRefinementCaseType_asGeneric :
    authorityOutsideRefinementCaseType =
      fixedAxisBinaryCaseAtSignatureType refinementAxisAuthorityTm
        authorityOutsideRefinementName outsideFragmentName
        outsideFragmentName (signatureBoundary (.var 1))
        (signatureBoundary (.var 1)) := by
  decide

theorem authorityOutsideRefinementCaseType_hasType :
    AxisRefinementHasType axisRefinementContextSM
      authorityOutsideRefinementCaseType
      (sortTm
        (fixedAxisBinaryCaseLevel boundaryLevel boundaryLevel)) := by
  rw [authorityOutsideRefinementCaseType_asGeneric]
  apply fixedAxisBinaryCaseAtSignatureType_hasType boundaryLevel boundaryLevel
  · exact signatureBoundary_hasType axisRefinementSignatureVarInSM_hasType
  · exact signatureBoundary_hasType axisRefinementSignatureVarInSM_hasType
  · apply axisRefinementMotiveApp_hasType
    · exact axisRefinementMotiveVarInFixedBinaryCase_hasType _ _
    · exact refinementAxisAuthorityTm_hasAxisRefinementType
    · exact Presentation.HasType.var 2
    · apply outsideFragmentApp_hasAxisRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply outsideFragmentApp_hasAxisRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0
    · apply authorityOutsideRefinementApp_hasType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0

theorem authorityOutsideEstablishedRefinementCaseType_asGeneric :
    authorityOutsideEstablishedRefinementCaseType =
      fixedAxisBinaryCaseAtSignatureType refinementAxisAuthorityTm
        authorityOutsideEstablishedRefinementName outsideFragmentName
        establishedName (signatureBoundary (.var 1))
        (signatureEvidence (.var 1)) := by
  decide

theorem authorityOutsideEstablishedRefinementCaseType_hasType :
    AxisRefinementHasType axisRefinementContextSM
      authorityOutsideEstablishedRefinementCaseType
      (sortTm
        (fixedAxisBinaryCaseLevel boundaryLevel evidenceLevel)) := by
  rw [authorityOutsideEstablishedRefinementCaseType_asGeneric]
  apply fixedAxisBinaryCaseAtSignatureType_hasType boundaryLevel evidenceLevel
  · exact signatureBoundary_hasType axisRefinementSignatureVarInSM_hasType
  · exact signatureEvidence_hasType axisRefinementSignatureVarInSM_hasType
  · apply axisRefinementMotiveApp_hasType
    · exact axisRefinementMotiveVarInFixedBinaryCase_hasType _ _
    · exact refinementAxisAuthorityTm_hasAxisRefinementType
    · exact Presentation.HasType.var 2
    · apply outsideFragmentApp_hasAxisRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply establishedApp_hasAxisRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0
    · apply authorityOutsideEstablishedRefinementApp_hasType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0

theorem authorityOutsideRefutedRefinementCaseType_asGeneric :
    authorityOutsideRefutedRefinementCaseType =
      fixedAxisBinaryCaseAtSignatureType refinementAxisAuthorityTm
        authorityOutsideRefutedRefinementName outsideFragmentName
        refutedName (signatureBoundary (.var 1))
        (signatureObstruction (.var 1)) := by
  decide

theorem authorityOutsideRefutedRefinementCaseType_hasType :
    AxisRefinementHasType axisRefinementContextSM
      authorityOutsideRefutedRefinementCaseType
      (sortTm
        (fixedAxisBinaryCaseLevel boundaryLevel obstructionLevel)) := by
  rw [authorityOutsideRefutedRefinementCaseType_asGeneric]
  apply fixedAxisBinaryCaseAtSignatureType_hasType boundaryLevel
    obstructionLevel
  · exact signatureBoundary_hasType axisRefinementSignatureVarInSM_hasType
  · exact signatureObstruction_hasType
      axisRefinementSignatureVarInSM_hasType
  · apply axisRefinementMotiveApp_hasType
    · exact axisRefinementMotiveVarInFixedBinaryCase_hasType _ _
    · exact refinementAxisAuthorityTm_hasAxisRefinementType
    · exact Presentation.HasType.var 2
    · apply outsideFragmentApp_hasAxisRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply refutedApp_hasAxisRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0
    · apply authorityOutsideRefutedRefinementApp_hasType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0

theorem authorityOutsideIncompleteRefinementCaseType_asGeneric :
    authorityOutsideIncompleteRefinementCaseType =
      fixedAxisBinaryCaseAtSignatureType refinementAxisAuthorityTm
        authorityOutsideIncompleteRefinementName outsideFragmentName
        incompleteName (signatureBoundary (.var 1))
        (signatureFrontier (.var 1)) := by
  decide

theorem authorityOutsideIncompleteRefinementCaseType_hasType :
    AxisRefinementHasType axisRefinementContextSM
      authorityOutsideIncompleteRefinementCaseType
      (sortTm
        (fixedAxisBinaryCaseLevel boundaryLevel frontierLevel)) := by
  rw [authorityOutsideIncompleteRefinementCaseType_asGeneric]
  apply fixedAxisBinaryCaseAtSignatureType_hasType boundaryLevel frontierLevel
  · exact signatureBoundary_hasType axisRefinementSignatureVarInSM_hasType
  · exact signatureFrontier_hasType axisRefinementSignatureVarInSM_hasType
  · apply axisRefinementMotiveApp_hasType
    · exact axisRefinementMotiveVarInFixedBinaryCase_hasType _ _
    · exact refinementAxisAuthorityTm_hasAxisRefinementType
    · exact Presentation.HasType.var 2
    · apply outsideFragmentApp_hasAxisRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
    · apply incompleteApp_hasAxisRefinementType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 0
    · apply authorityOutsideIncompleteRefinementApp_hasType
      · exact Presentation.HasType.var 4
      · exact Presentation.HasType.var 2
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0

/-! ### Formation of the complete eliminator -/

def axisEliminatorContextEstablished : Tower.Ctx 3 :=
  .snoc axisRefinementContextSM axisEstablishedCaseType

def axisEliminatorContextRefuted : Tower.Ctx 4 :=
  .snoc axisEliminatorContextEstablished axisRefutedCaseAfterEstablished

def axisEliminatorContextIncomplete : Tower.Ctx 5 :=
  .snoc axisEliminatorContextRefuted axisIncompleteCaseAfterTwo

def axisEliminatorContextBudgetOutside : Tower.Ctx 6 :=
  .snoc axisEliminatorContextIncomplete budgetOutsideCaseAfterThree

def axisEliminatorContextBudgetIncompleteEstablished : Tower.Ctx 7 :=
  .snoc axisEliminatorContextBudgetOutside
    budgetIncompleteEstablishedCaseAfterFour

def axisEliminatorContextBudgetIncompleteRefuted : Tower.Ctx 8 :=
  .snoc axisEliminatorContextBudgetIncompleteEstablished
    budgetIncompleteRefutedCaseAfterFive

def axisEliminatorContextAuthorityOutside : Tower.Ctx 9 :=
  .snoc axisEliminatorContextBudgetIncompleteRefuted
    authorityOutsideCaseAfterSix

def axisEliminatorContextAuthorityOutsideEstablished : Tower.Ctx 10 :=
  .snoc axisEliminatorContextAuthorityOutside
    authorityOutsideEstablishedCaseAfterSeven

def axisEliminatorContextAuthorityOutsideRefuted : Tower.Ctx 11 :=
  .snoc axisEliminatorContextAuthorityOutsideEstablished
    authorityOutsideRefutedCaseAfterEight

def axisEliminatorContextAuthorityOutsideIncomplete : Tower.Ctx 12 :=
  .snoc axisEliminatorContextAuthorityOutsideRefuted
    authorityOutsideIncompleteCaseAfterNine

theorem axisRefutedCaseAfterEstablished_hasType :
    AxisRefinementHasType axisEliminatorContextEstablished
      axisRefutedCaseAfterEstablished
      (sortTm
        (axisBinaryCaseLevel obstructionLevel obstructionLevel)) := by
  simpa [axisEliminatorContextEstablished,
    axisRefutedCaseAfterEstablished, sortTm, Presentation.rename] using
    axisRefutedCaseType_hasType.weaken
      (extension := axisEstablishedCaseType)

theorem axisIncompleteCaseAfterTwo_hasType :
    AxisRefinementHasType axisEliminatorContextRefuted
      axisIncompleteCaseAfterTwo
      (sortTm (axisBinaryCaseLevel frontierLevel frontierLevel)) := by
  have first := axisIncompleteCaseType_hasType.weaken
    (extension := axisEstablishedCaseType)
  have second := first.weaken
    (extension := axisRefutedCaseAfterEstablished)
  simpa [axisEliminatorContextEstablished, axisEliminatorContextRefuted,
    axisIncompleteCaseAfterTwo, sortTm, Presentation.rename] using second

theorem budgetOutsideCaseAfterThree_hasType :
    AxisRefinementHasType axisEliminatorContextIncomplete
      budgetOutsideCaseAfterThree
      (sortTm (fixedAxisUnaryCaseLevel boundaryLevel)) := by
  have first := budgetOutsideRefinementCaseType_hasType.weaken
    (extension := axisEstablishedCaseType)
  have second := first.weaken
    (extension := axisRefutedCaseAfterEstablished)
  have third := second.weaken
    (extension := axisIncompleteCaseAfterTwo)
  simpa [axisEliminatorContextEstablished, axisEliminatorContextRefuted,
    axisEliminatorContextIncomplete, budgetOutsideCaseAfterThree,
    sortTm, Presentation.rename] using third

theorem budgetIncompleteEstablishedCaseAfterFour_hasType :
    AxisRefinementHasType axisEliminatorContextBudgetOutside
      budgetIncompleteEstablishedCaseAfterFour
      (sortTm
        (fixedAxisBinaryCaseLevel frontierLevel evidenceLevel)) := by
  have first :=
    budgetIncompleteEstablishedRefinementCaseType_hasType.weaken
      (extension := axisEstablishedCaseType)
  have second := first.weaken
    (extension := axisRefutedCaseAfterEstablished)
  have third := second.weaken
    (extension := axisIncompleteCaseAfterTwo)
  have fourth := third.weaken
    (extension := budgetOutsideCaseAfterThree)
  simpa [axisEliminatorContextEstablished, axisEliminatorContextRefuted,
    axisEliminatorContextIncomplete, axisEliminatorContextBudgetOutside,
    budgetIncompleteEstablishedCaseAfterFour, sortTm,
    Presentation.rename] using fourth

theorem budgetIncompleteRefutedCaseAfterFive_hasType :
    AxisRefinementHasType axisEliminatorContextBudgetIncompleteEstablished
      budgetIncompleteRefutedCaseAfterFive
      (sortTm
        (fixedAxisBinaryCaseLevel frontierLevel obstructionLevel)) := by
  have first := budgetIncompleteRefutedRefinementCaseType_hasType.weaken
    (extension := axisEstablishedCaseType)
  have second := first.weaken
    (extension := axisRefutedCaseAfterEstablished)
  have third := second.weaken
    (extension := axisIncompleteCaseAfterTwo)
  have fourth := third.weaken
    (extension := budgetOutsideCaseAfterThree)
  have fifth := fourth.weaken
    (extension := budgetIncompleteEstablishedCaseAfterFour)
  simpa [axisEliminatorContextEstablished, axisEliminatorContextRefuted,
    axisEliminatorContextIncomplete, axisEliminatorContextBudgetOutside,
    axisEliminatorContextBudgetIncompleteEstablished,
    budgetIncompleteRefutedCaseAfterFive, sortTm,
    Presentation.rename] using fifth

theorem authorityOutsideCaseAfterSix_hasType :
    AxisRefinementHasType axisEliminatorContextBudgetIncompleteRefuted
      authorityOutsideCaseAfterSix
      (sortTm
        (fixedAxisBinaryCaseLevel boundaryLevel boundaryLevel)) := by
  have first := authorityOutsideRefinementCaseType_hasType.weaken
    (extension := axisEstablishedCaseType)
  have second := first.weaken
    (extension := axisRefutedCaseAfterEstablished)
  have third := second.weaken
    (extension := axisIncompleteCaseAfterTwo)
  have fourth := third.weaken
    (extension := budgetOutsideCaseAfterThree)
  have fifth := fourth.weaken
    (extension := budgetIncompleteEstablishedCaseAfterFour)
  have sixth := fifth.weaken
    (extension := budgetIncompleteRefutedCaseAfterFive)
  simpa [axisEliminatorContextEstablished, axisEliminatorContextRefuted,
    axisEliminatorContextIncomplete, axisEliminatorContextBudgetOutside,
    axisEliminatorContextBudgetIncompleteEstablished,
    axisEliminatorContextBudgetIncompleteRefuted,
    authorityOutsideCaseAfterSix, sortTm, Presentation.rename] using sixth

theorem authorityOutsideEstablishedCaseAfterSeven_hasType :
    AxisRefinementHasType axisEliminatorContextAuthorityOutside
      authorityOutsideEstablishedCaseAfterSeven
      (sortTm
        (fixedAxisBinaryCaseLevel boundaryLevel evidenceLevel)) := by
  have first :=
    authorityOutsideEstablishedRefinementCaseType_hasType.weaken
      (extension := axisEstablishedCaseType)
  have second := first.weaken
    (extension := axisRefutedCaseAfterEstablished)
  have third := second.weaken
    (extension := axisIncompleteCaseAfterTwo)
  have fourth := third.weaken
    (extension := budgetOutsideCaseAfterThree)
  have fifth := fourth.weaken
    (extension := budgetIncompleteEstablishedCaseAfterFour)
  have sixth := fifth.weaken
    (extension := budgetIncompleteRefutedCaseAfterFive)
  have seventh := sixth.weaken
    (extension := authorityOutsideCaseAfterSix)
  simpa [axisEliminatorContextEstablished, axisEliminatorContextRefuted,
    axisEliminatorContextIncomplete, axisEliminatorContextBudgetOutside,
    axisEliminatorContextBudgetIncompleteEstablished,
    axisEliminatorContextBudgetIncompleteRefuted,
    axisEliminatorContextAuthorityOutside,
    authorityOutsideEstablishedCaseAfterSeven, sortTm,
    Presentation.rename] using seventh

theorem authorityOutsideRefutedCaseAfterEight_hasType :
    AxisRefinementHasType axisEliminatorContextAuthorityOutsideEstablished
      authorityOutsideRefutedCaseAfterEight
      (sortTm
        (fixedAxisBinaryCaseLevel boundaryLevel obstructionLevel)) := by
  have first := authorityOutsideRefutedRefinementCaseType_hasType.weaken
    (extension := axisEstablishedCaseType)
  have second := first.weaken
    (extension := axisRefutedCaseAfterEstablished)
  have third := second.weaken
    (extension := axisIncompleteCaseAfterTwo)
  have fourth := third.weaken
    (extension := budgetOutsideCaseAfterThree)
  have fifth := fourth.weaken
    (extension := budgetIncompleteEstablishedCaseAfterFour)
  have sixth := fifth.weaken
    (extension := budgetIncompleteRefutedCaseAfterFive)
  have seventh := sixth.weaken
    (extension := authorityOutsideCaseAfterSix)
  have eighth := seventh.weaken
    (extension := authorityOutsideEstablishedCaseAfterSeven)
  simpa [axisEliminatorContextEstablished, axisEliminatorContextRefuted,
    axisEliminatorContextIncomplete, axisEliminatorContextBudgetOutside,
    axisEliminatorContextBudgetIncompleteEstablished,
    axisEliminatorContextBudgetIncompleteRefuted,
    axisEliminatorContextAuthorityOutside,
    axisEliminatorContextAuthorityOutsideEstablished,
    authorityOutsideRefutedCaseAfterEight, sortTm,
    Presentation.rename] using eighth

theorem authorityOutsideIncompleteCaseAfterNine_hasType :
    AxisRefinementHasType axisEliminatorContextAuthorityOutsideRefuted
      authorityOutsideIncompleteCaseAfterNine
      (sortTm
        (fixedAxisBinaryCaseLevel boundaryLevel frontierLevel)) := by
  have first := authorityOutsideIncompleteRefinementCaseType_hasType.weaken
    (extension := axisEstablishedCaseType)
  have second := first.weaken
    (extension := axisRefutedCaseAfterEstablished)
  have third := second.weaken
    (extension := axisIncompleteCaseAfterTwo)
  have fourth := third.weaken
    (extension := budgetOutsideCaseAfterThree)
  have fifth := fourth.weaken
    (extension := budgetIncompleteEstablishedCaseAfterFour)
  have sixth := fifth.weaken
    (extension := budgetIncompleteRefutedCaseAfterFive)
  have seventh := sixth.weaken
    (extension := authorityOutsideCaseAfterSix)
  have eighth := seventh.weaken
    (extension := authorityOutsideEstablishedCaseAfterSeven)
  have ninth := eighth.weaken
    (extension := authorityOutsideRefutedCaseAfterEight)
  simpa [axisEliminatorContextEstablished, axisEliminatorContextRefuted,
    axisEliminatorContextIncomplete, axisEliminatorContextBudgetOutside,
    axisEliminatorContextBudgetIncompleteEstablished,
    axisEliminatorContextBudgetIncompleteRefuted,
    axisEliminatorContextAuthorityOutside,
    axisEliminatorContextAuthorityOutsideEstablished,
    axisEliminatorContextAuthorityOutsideRefuted,
    authorityOutsideIncompleteCaseAfterNine, sortTm,
    Presentation.rename] using ninth

def axisEliminatorResultContextA : Tower.Ctx 13 :=
  .snoc axisEliminatorContextAuthorityOutsideIncomplete refinementAxisTm

def axisEliminatorResultContextAJ : Tower.Ctx 14 :=
  .snoc axisEliminatorResultContextA (signatureJudgment (.var 12))

def axisEliminatorResultContextAJB : Tower.Ctx 15 :=
  .snoc axisEliminatorResultContextAJ
    (outcomeApp (.var 13) (.var 0))

def axisEliminatorResultContextAJBA : Tower.Ctx 16 :=
  .snoc axisEliminatorResultContextAJB
    (outcomeApp (.var 14) (.var 1))

def axisEliminatorResultContextAJBAR : Tower.Ctx 17 :=
  .snoc axisEliminatorResultContextAJBA
    (axisRefinementApp (.var 15) (.var 3) (.var 2)
      (.var 1) (.var 0))

def axisRefinementEliminateRelationLevel : LevelExpr :=
  .max axisRefinementLevel axisRefinementMotiveLevel

def axisRefinementEliminateAfterLevel : LevelExpr :=
  .max outcomeLevel axisRefinementEliminateRelationLevel

def axisRefinementEliminateBeforeLevel : LevelExpr :=
  .max outcomeLevel axisRefinementEliminateAfterLevel

def axisRefinementEliminateJudgmentLevel : LevelExpr :=
  .max judgmentLevel axisRefinementEliminateBeforeLevel

def axisRefinementEliminateResultLevel : LevelExpr :=
  .max refinementAxisLevel axisRefinementEliminateJudgmentLevel

theorem axisRefinementMotiveVarInEliminateResult_hasType :
    AxisRefinementHasType axisEliminatorResultContextAJBAR (.var 15)
      (axisRefinementMotiveAtSignatureType (.var 16)) := by
  have variableTyping :=
    (Presentation.HasType.var (R := axisRefinementRules)
      (Γ := axisEliminatorResultContextAJBAR) (15 : Fin 17))
  have lookupEquality :
      Presentation.Ctx.lookup axisEliminatorResultContextAJBAR
          (15 : Fin 17) =
        axisRefinementMotiveAtSignatureType (.var 16) := by
    decide
  simpa only [lookupEquality] using variableTyping

theorem axisRefinementEliminateResultType_hasType :
    AxisRefinementHasType
      axisEliminatorContextAuthorityOutsideIncomplete
      axisRefinementEliminateResultType
      (sortTm axisRefinementEliminateResultLevel) := by
  unfold axisRefinementEliminateResultType
    axisRefinementEliminateResultLevel
    axisRefinementEliminateJudgmentLevel
    axisRefinementEliminateBeforeLevel
    axisRefinementEliminateAfterLevel
    axisRefinementEliminateRelationLevel
  apply Presentation.HasType.piForm
  · exact refinementAxisTm_hasAxisRefinementType
  · exact .sort refinementAxisLevel
  · apply Presentation.HasType.piForm
    · apply signatureJudgment_hasType
      exact Presentation.HasType.var 12
    · exact .sort judgmentLevel
    · apply Presentation.HasType.piForm
      · apply outcomeApp_hasTypeWith
        · exact includeOutcomeInAxisRefinement outcomeConstant_hasType
        · exact Presentation.HasType.var 13
        · exact Presentation.HasType.var 0
      · exact .sort outcomeLevel
      · apply Presentation.HasType.piForm
        · apply outcomeApp_hasTypeWith
          · exact includeOutcomeInAxisRefinement outcomeConstant_hasType
          · exact Presentation.HasType.var 14
          · exact Presentation.HasType.var 1
        · exact .sort outcomeLevel
        · apply Presentation.HasType.piForm
          · apply axisRefinementApp_hasType
            · exact Presentation.HasType.var 15
            · exact Presentation.HasType.var 3
            · exact Presentation.HasType.var 2
            · exact Presentation.HasType.var 1
            · exact Presentation.HasType.var 0
          · exact .sort axisRefinementLevel
          · apply axisRefinementMotiveApp_hasType
            · exact axisRefinementMotiveVarInEliminateResult_hasType
            · exact Presentation.HasType.var 4
            · exact Presentation.HasType.var 3
            · exact Presentation.HasType.var 2
            · exact Presentation.HasType.var 1
            · exact Presentation.HasType.var 0
          · exact .sort axisRefinementMotiveLevel
          · exact .sorts axisRefinementLevel axisRefinementMotiveLevel
        · exact .sort axisRefinementEliminateRelationLevel
        · exact .sorts outcomeLevel
            axisRefinementEliminateRelationLevel
      · exact .sort axisRefinementEliminateAfterLevel
      · exact .sorts outcomeLevel axisRefinementEliminateAfterLevel
    · exact .sort axisRefinementEliminateBeforeLevel
    · exact .sorts judgmentLevel axisRefinementEliminateBeforeLevel
  · exact .sort axisRefinementEliminateJudgmentLevel
  · exact .sorts refinementAxisLevel
      axisRefinementEliminateJudgmentLevel

def afterAuthorityOutsideIncompleteLevel : LevelExpr :=
  .max (fixedAxisBinaryCaseLevel boundaryLevel frontierLevel)
    axisRefinementEliminateResultLevel

def afterAuthorityOutsideRefutedLevel : LevelExpr :=
  .max (fixedAxisBinaryCaseLevel boundaryLevel obstructionLevel)
    afterAuthorityOutsideIncompleteLevel

def afterAuthorityOutsideEstablishedLevel : LevelExpr :=
  .max (fixedAxisBinaryCaseLevel boundaryLevel evidenceLevel)
    afterAuthorityOutsideRefutedLevel

def afterAuthorityOutsideLevel : LevelExpr :=
  .max (fixedAxisBinaryCaseLevel boundaryLevel boundaryLevel)
    afterAuthorityOutsideEstablishedLevel

def afterBudgetIncompleteRefutedLevel : LevelExpr :=
  .max (fixedAxisBinaryCaseLevel frontierLevel obstructionLevel)
    afterAuthorityOutsideLevel

def afterBudgetIncompleteEstablishedLevel : LevelExpr :=
  .max (fixedAxisBinaryCaseLevel frontierLevel evidenceLevel)
    afterBudgetIncompleteRefutedLevel

def afterBudgetOutsideLevel : LevelExpr :=
  .max (fixedAxisUnaryCaseLevel boundaryLevel)
    afterBudgetIncompleteEstablishedLevel

def afterAxisIncompleteLevel : LevelExpr :=
  .max (axisBinaryCaseLevel frontierLevel frontierLevel)
    afterBudgetOutsideLevel

def afterAxisRefutedLevel : LevelExpr :=
  .max (axisBinaryCaseLevel obstructionLevel obstructionLevel)
    afterAxisIncompleteLevel

def afterAxisEstablishedLevel : LevelExpr :=
  .max (axisBinaryCaseLevel evidenceLevel evidenceLevel)
    afterAxisRefutedLevel

def axisRefinementEliminateBodyLevel : LevelExpr :=
  .max axisRefinementMotiveTypeLevel afterAxisEstablishedLevel

def axisRefinementEliminateDeclarationLevel : LevelExpr :=
  .max signatureLevel axisRefinementEliminateBodyLevel

theorem axisRefinementEliminateBodyType_hasType :
    AxisRefinementHasType axisRefinementContextS
      axisRefinementEliminateBodyType
      (sortTm axisRefinementEliminateBodyLevel) := by
  unfold axisRefinementEliminateBodyType
    axisRefinementEliminateBodyLevel afterAxisEstablishedLevel
    afterAxisRefutedLevel afterAxisIncompleteLevel afterBudgetOutsideLevel
    afterBudgetIncompleteEstablishedLevel
    afterBudgetIncompleteRefutedLevel afterAuthorityOutsideLevel
    afterAuthorityOutsideEstablishedLevel
    afterAuthorityOutsideRefutedLevel
    afterAuthorityOutsideIncompleteLevel
  apply Presentation.HasType.piForm
  · exact axisRefinementMotiveType_hasType
  · exact .sort axisRefinementMotiveTypeLevel
  · apply Presentation.HasType.piForm
    · exact axisEstablishedCaseType_hasType
    · exact .sort (axisBinaryCaseLevel evidenceLevel evidenceLevel)
    · apply Presentation.HasType.piForm
      · exact axisRefutedCaseAfterEstablished_hasType
      · exact .sort
          (axisBinaryCaseLevel obstructionLevel obstructionLevel)
      · apply Presentation.HasType.piForm
        · exact axisIncompleteCaseAfterTwo_hasType
        · exact .sort
            (axisBinaryCaseLevel frontierLevel frontierLevel)
        · apply Presentation.HasType.piForm
          · exact budgetOutsideCaseAfterThree_hasType
          · exact .sort (fixedAxisUnaryCaseLevel boundaryLevel)
          · apply Presentation.HasType.piForm
            · exact budgetIncompleteEstablishedCaseAfterFour_hasType
            · exact .sort
                (fixedAxisBinaryCaseLevel frontierLevel evidenceLevel)
            · apply Presentation.HasType.piForm
              · exact budgetIncompleteRefutedCaseAfterFive_hasType
              · exact .sort
                  (fixedAxisBinaryCaseLevel frontierLevel obstructionLevel)
              · apply Presentation.HasType.piForm
                · exact authorityOutsideCaseAfterSix_hasType
                · exact .sort
                    (fixedAxisBinaryCaseLevel boundaryLevel boundaryLevel)
                · apply Presentation.HasType.piForm
                  · exact
                      authorityOutsideEstablishedCaseAfterSeven_hasType
                  · exact .sort
                      (fixedAxisBinaryCaseLevel boundaryLevel evidenceLevel)
                  · apply Presentation.HasType.piForm
                    · exact authorityOutsideRefutedCaseAfterEight_hasType
                    · exact .sort
                        (fixedAxisBinaryCaseLevel boundaryLevel
                          obstructionLevel)
                    · apply Presentation.HasType.piForm
                      · exact
                          authorityOutsideIncompleteCaseAfterNine_hasType
                      · exact .sort
                          (fixedAxisBinaryCaseLevel boundaryLevel
                            frontierLevel)
                      · exact axisRefinementEliminateResultType_hasType
                      · exact .sort axisRefinementEliminateResultLevel
                      · exact .sorts
                          (fixedAxisBinaryCaseLevel boundaryLevel
                            frontierLevel)
                          axisRefinementEliminateResultLevel
                    · exact .sort afterAuthorityOutsideIncompleteLevel
                    · exact .sorts
                        (fixedAxisBinaryCaseLevel boundaryLevel
                          obstructionLevel)
                        afterAuthorityOutsideIncompleteLevel
                  · exact .sort afterAuthorityOutsideRefutedLevel
                  · exact .sorts
                      (fixedAxisBinaryCaseLevel boundaryLevel evidenceLevel)
                      afterAuthorityOutsideRefutedLevel
                · exact .sort afterAuthorityOutsideEstablishedLevel
                · exact .sorts
                    (fixedAxisBinaryCaseLevel boundaryLevel boundaryLevel)
                    afterAuthorityOutsideEstablishedLevel
              · exact .sort afterAuthorityOutsideLevel
              · exact .sorts
                  (fixedAxisBinaryCaseLevel frontierLevel obstructionLevel)
                  afterAuthorityOutsideLevel
            · exact .sort afterBudgetIncompleteRefutedLevel
            · exact .sorts
                (fixedAxisBinaryCaseLevel frontierLevel evidenceLevel)
                afterBudgetIncompleteRefutedLevel
          · exact .sort afterBudgetIncompleteEstablishedLevel
          · exact .sorts (fixedAxisUnaryCaseLevel boundaryLevel)
              afterBudgetIncompleteEstablishedLevel
        · exact .sort afterBudgetOutsideLevel
        · exact .sorts
            (axisBinaryCaseLevel frontierLevel frontierLevel)
            afterBudgetOutsideLevel
      · exact .sort afterAxisIncompleteLevel
      · exact .sorts
          (axisBinaryCaseLevel obstructionLevel obstructionLevel)
          afterAxisIncompleteLevel
    · exact .sort afterAxisRefutedLevel
    · exact .sorts (axisBinaryCaseLevel evidenceLevel evidenceLevel)
        afterAxisRefutedLevel
  · exact .sort afterAxisEstablishedLevel
  · exact .sorts axisRefinementMotiveTypeLevel
      afterAxisEstablishedLevel

theorem axisRefinementEliminateType_hasType :
    AxisRefinementHasType (.nil : Tower.Ctx 0)
      axisRefinementEliminateType
      (sortTm axisRefinementEliminateDeclarationLevel) := by
  unfold axisRefinementEliminateType
    axisRefinementEliminateDeclarationLevel
  apply Presentation.HasType.piForm
  · exact outcomeSignatureType_hasAxisRefinementType
  · exact .sort signatureLevel
  · exact axisRefinementEliminateBodyType_hasType
  · exact .sort axisRefinementEliminateBodyLevel
  · exact .sorts signatureLevel axisRefinementEliminateBodyLevel

/-! ### Formed declaration signature -/

@[simp] theorem rawAxisRefinementSignature_valueOf_none
    (name : DeclName) :
    rawAxisRefinementSignature.valueOf? name = none := by
  by_cases h0 : name = axisRefinementName
  · subst name
    simp [rawAxisRefinementSignature, axisRefinementDeclarations,
      Signature.valueOf?, Signature.ofList, Signature.insert,
      Signature.empty]
  by_cases h1 : name = axisEstablishedName
  · subst name
    simp [rawAxisRefinementSignature, axisRefinementDeclarations,
      Signature.valueOf?, Signature.ofList, Signature.insert,
      Signature.empty, h0]
  by_cases h2 : name = axisRefutedName
  · subst name
    simp [rawAxisRefinementSignature, axisRefinementDeclarations,
      Signature.valueOf?, Signature.ofList, Signature.insert,
      Signature.empty, h0, h1]
  by_cases h3 : name = axisIncompleteName
  · subst name
    simp [rawAxisRefinementSignature, axisRefinementDeclarations,
      Signature.valueOf?, Signature.ofList, Signature.insert,
      Signature.empty, h0, h1, h2]
  by_cases h4 : name = budgetOutsideRefinementName
  · subst name
    simp [rawAxisRefinementSignature, axisRefinementDeclarations,
      Signature.valueOf?, Signature.ofList, Signature.insert,
      Signature.empty, h0, h1, h2, h3]
  by_cases h5 : name = budgetIncompleteEstablishedRefinementName
  · subst name
    simp [rawAxisRefinementSignature, axisRefinementDeclarations,
      Signature.valueOf?, Signature.ofList, Signature.insert,
      Signature.empty, h0, h1, h2, h3, h4]
  by_cases h6 : name = budgetIncompleteRefutedRefinementName
  · subst name
    simp [rawAxisRefinementSignature, axisRefinementDeclarations,
      Signature.valueOf?, Signature.ofList, Signature.insert,
      Signature.empty, h0, h1, h2, h3, h4, h5]
  by_cases h7 : name = authorityOutsideRefinementName
  · subst name
    simp [rawAxisRefinementSignature, axisRefinementDeclarations,
      Signature.valueOf?, Signature.ofList, Signature.insert,
      Signature.empty, h0, h1, h2, h3, h4, h5, h6]
  by_cases h8 : name = authorityOutsideEstablishedRefinementName
  · subst name
    simp [rawAxisRefinementSignature, axisRefinementDeclarations,
      Signature.valueOf?, Signature.ofList, Signature.insert,
      Signature.empty, h0, h1, h2, h3, h4, h5, h6, h7]
  by_cases h9 : name = authorityOutsideRefutedRefinementName
  · subst name
    simp [rawAxisRefinementSignature, axisRefinementDeclarations,
      Signature.valueOf?, Signature.ofList, Signature.insert,
      Signature.empty, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  by_cases h10 : name = authorityOutsideIncompleteRefinementName
  · subst name
    simp [rawAxisRefinementSignature, axisRefinementDeclarations,
      Signature.valueOf?, Signature.ofList, Signature.insert,
      Signature.empty, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  by_cases h11 : name = axisRefinementEliminateName
  · subst name
    simp [rawAxisRefinementSignature, axisRefinementDeclarations,
      Signature.valueOf?, Signature.ofList, Signature.insert,
      Signature.empty, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · simp [rawAxisRefinementSignature, axisRefinementDeclarations,
      Signature.valueOf?, Signature.ofList, Signature.insert,
      Signature.empty, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
      h11]

theorem rawAxisRefinementSignature_types_formed
    {name : DeclName} {type : Tower.Tm 0}
    (lookup : rawAxisRefinementSignature.typeOf? name = some type) :
    ∃ level : Tower.Head,
      refinementAxisRules.isUniverse level ∧
      AxisRefinementHasType (.nil : Tower.Ctx 0) type (.head level) := by
  by_cases h0 : name = axisRefinementName
  · subst name
    have typeEquality : type = axisRefinementType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort axisRefinementDeclarationLevel,
      .sort axisRefinementDeclarationLevel, axisRefinementType_hasType⟩
  by_cases h1 : name = axisEstablishedName
  · subst name
    have typeEquality : type = axisEstablishedType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort axisEstablishedDeclarationLevel,
      .sort axisEstablishedDeclarationLevel, axisEstablishedType_hasType⟩
  by_cases h2 : name = axisRefutedName
  · subst name
    have typeEquality : type = axisRefutedType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort axisRefutedDeclarationLevel,
      .sort axisRefutedDeclarationLevel, axisRefutedType_hasType⟩
  by_cases h3 : name = axisIncompleteName
  · subst name
    have typeEquality : type = axisIncompleteType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort axisIncompleteDeclarationLevel,
      .sort axisIncompleteDeclarationLevel, axisIncompleteType_hasType⟩
  by_cases h4 : name = budgetOutsideRefinementName
  · subst name
    have typeEquality : type = budgetOutsideRefinementType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort budgetOutsideRefinementDeclarationLevel,
      .sort budgetOutsideRefinementDeclarationLevel,
      budgetOutsideRefinementType_hasType⟩
  by_cases h5 : name = budgetIncompleteEstablishedRefinementName
  · subst name
    have typeEquality :
        type = budgetIncompleteEstablishedRefinementType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort budgetIncompleteEstablishedRefinementDeclarationLevel,
      .sort budgetIncompleteEstablishedRefinementDeclarationLevel,
      budgetIncompleteEstablishedRefinementType_hasType⟩
  by_cases h6 : name = budgetIncompleteRefutedRefinementName
  · subst name
    have typeEquality : type = budgetIncompleteRefutedRefinementType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort budgetIncompleteRefutedRefinementDeclarationLevel,
      .sort budgetIncompleteRefutedRefinementDeclarationLevel,
      budgetIncompleteRefutedRefinementType_hasType⟩
  by_cases h7 : name = authorityOutsideRefinementName
  · subst name
    have typeEquality : type = authorityOutsideRefinementType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort authorityOutsideRefinementDeclarationLevel,
      .sort authorityOutsideRefinementDeclarationLevel,
      authorityOutsideRefinementType_hasType⟩
  by_cases h8 : name = authorityOutsideEstablishedRefinementName
  · subst name
    have typeEquality :
        type = authorityOutsideEstablishedRefinementType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort authorityOutsideEstablishedRefinementDeclarationLevel,
      .sort authorityOutsideEstablishedRefinementDeclarationLevel,
      authorityOutsideEstablishedRefinementType_hasType⟩
  by_cases h9 : name = authorityOutsideRefutedRefinementName
  · subst name
    have typeEquality : type = authorityOutsideRefutedRefinementType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort authorityOutsideRefutedRefinementDeclarationLevel,
      .sort authorityOutsideRefutedRefinementDeclarationLevel,
      authorityOutsideRefutedRefinementType_hasType⟩
  by_cases h10 : name = authorityOutsideIncompleteRefinementName
  · subst name
    have typeEquality :
        type = authorityOutsideIncompleteRefinementType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort authorityOutsideIncompleteRefinementDeclarationLevel,
      .sort authorityOutsideIncompleteRefinementDeclarationLevel,
      authorityOutsideIncompleteRefinementType_hasType⟩
  by_cases h11 : name = axisRefinementEliminateName
  · subst name
    have typeEquality : type = axisRefinementEliminateType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort axisRefinementEliminateDeclarationLevel,
      .sort axisRefinementEliminateDeclarationLevel,
      axisRefinementEliminateType_hasType⟩
  · simp [rawAxisRefinementSignature, axisRefinementDeclarations,
      Signature.typeOf?, Signature.ofList, Signature.insert,
      Signature.empty, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
      h11] at lookup

theorem rawAxisRefinementSignature_fresh
    {name : DeclName} {entry : Entry Tower.Head}
    (lookup : rawAxisRefinementSignature.entries name = some entry) :
    refinementAxisRules.constantType name = none := by
  by_cases h0 : name = axisRefinementName
  · subst name
    exact axisRefinementName_fresh
  by_cases h1 : name = axisEstablishedName
  · subst name
    exact axisEstablishedName_fresh
  by_cases h2 : name = axisRefutedName
  · subst name
    exact axisRefutedName_fresh
  by_cases h3 : name = axisIncompleteName
  · subst name
    exact axisIncompleteName_fresh
  by_cases h4 : name = budgetOutsideRefinementName
  · subst name
    exact budgetOutsideRefinementName_fresh
  by_cases h5 : name = budgetIncompleteEstablishedRefinementName
  · subst name
    exact budgetIncompleteEstablishedRefinementName_fresh
  by_cases h6 : name = budgetIncompleteRefutedRefinementName
  · subst name
    exact budgetIncompleteRefutedRefinementName_fresh
  by_cases h7 : name = authorityOutsideRefinementName
  · subst name
    exact authorityOutsideRefinementName_fresh
  by_cases h8 : name = authorityOutsideEstablishedRefinementName
  · subst name
    exact authorityOutsideEstablishedRefinementName_fresh
  by_cases h9 : name = authorityOutsideRefutedRefinementName
  · subst name
    exact authorityOutsideRefutedRefinementName_fresh
  by_cases h10 : name = authorityOutsideIncompleteRefinementName
  · subst name
    exact authorityOutsideIncompleteRefinementName_fresh
  by_cases h11 : name = axisRefinementEliminateName
  · subst name
    exact axisRefinementEliminateName_fresh
  · simp [rawAxisRefinementSignature, axisRefinementDeclarations,
      Signature.ofList, Signature.insert, Signature.empty,
      h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11] at lookup

def rawAxisRefinementSignature_formed :
    rawAxisRefinementSignature.Formed refinementAxisRules where
  fresh := rawAxisRefinementSignature_fresh
  types := rawAxisRefinementSignature_types_formed
  values := by
    intro name type value _typeLookup valueLookup
    rw [rawAxisRefinementSignature_valueOf_none] at valueLookup
    cases valueLookup
  noSelfDelta := by
    intro name value valueLookup
    rw [rawAxisRefinementSignature_valueOf_none] at valueLookup
    cases valueLookup

/-! ### Strict positivity -/

def axisRefinementFamilyApplication
    (signature axis judgment before after : Tower.Tm n)
    (signatureFree : FreeOf axisRefinementName signature)
    (axisFree : FreeOf axisRefinementName axis)
    (judgmentFree : FreeOf axisRefinementName judgment)
    (beforeFree : FreeOf axisRefinementName before)
    (afterFree : FreeOf axisRefinementName after) :
    FamilyApplication axisRefinementName 5
      (axisRefinementApp signature axis judgment before after) :=
  .intro [signature, axis, judgment, before, after] rfl (by
    intro argument membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl
    · exact signatureFree
    · exact axisFree
    · exact judgmentFree
    · exact beforeFree
    · exact afterFree) rfl

def axisSignatureTypeFree :
    FreeOf axisRefinementName outcomeSignatureType :=
  outcomeSignatureTypeFreeOf axisRefinementName

def refinementAxisTypeFree {n : Nat} :
    FreeOf axisRefinementName (refinementAxisTm : Tower.Tm n) :=
  .const (by decide)

def axisSignatureJudgmentFree
    {signature : Tower.Tm n}
    (signatureFree : FreeOf axisRefinementName signature) :
    FreeOf axisRefinementName (signatureJudgment signature) := by
  unfold signatureJudgment
  exact .fst signatureFree

def axisSignatureEvidenceFree
    {signature : Tower.Tm n}
    (signatureFree : FreeOf axisRefinementName signature) :
    FreeOf axisRefinementName (signatureEvidence signature) := by
  unfold signatureEvidence
  exact .fst (.snd signatureFree)

def axisSignatureObstructionFree
    {signature : Tower.Tm n}
    (signatureFree : FreeOf axisRefinementName signature) :
    FreeOf axisRefinementName (signatureObstruction signature) := by
  unfold signatureObstruction
  exact .fst (.snd (.snd signatureFree))

def axisSignatureBoundaryFree
    {signature : Tower.Tm n}
    (signatureFree : FreeOf axisRefinementName signature) :
    FreeOf axisRefinementName (signatureBoundary signature) := by
  unfold signatureBoundary
  exact .fst (.snd (.snd (.snd signatureFree)))

def axisSignatureFrontierFree
    {signature : Tower.Tm n}
    (signatureFree : FreeOf axisRefinementName signature) :
    FreeOf axisRefinementName (signatureFrontier signature) := by
  unfold signatureFrontier
  exact .snd (.snd (.snd (.snd signatureFree)))

def axisOutcomeConstructorFree (constructor : DeclName)
    (different : constructor ≠ axisRefinementName)
    {signature judgment witness : Tower.Tm n}
    (signatureFree : FreeOf axisRefinementName signature)
    (judgmentFree : FreeOf axisRefinementName judgment)
    (witnessFree : FreeOf axisRefinementName witness) :
    FreeOf axisRefinementName
      (axisNamedOutcomeConstructorApp constructor signature judgment
        witness) :=
  .app (.app (.app (.const different) signatureFree) judgmentFree)
    witnessFree

def axisEstablishedConstructorPositive :
    ConstructorType axisRefinementName 5 axisEstablishedType := by
  unfold axisEstablishedType axisEstablishedBodyType
  exact .field (.free axisSignatureTypeFree)
    (.field (.free refinementAxisTypeFree)
      (.field (.free (axisSignatureJudgmentFree (.var 1)))
        (.field
          (.free (.app (axisSignatureEvidenceFree (.var 2)) (.var 0)))
          (.field
            (.free (.app (axisSignatureEvidenceFree (.var 3)) (.var 1)))
            (.result
              (axisRefinementFamilyApplication (.var 4) (.var 3) (.var 2)
                (establishedApp (.var 4) (.var 2) (.var 1))
                (establishedApp (.var 4) (.var 2) (.var 0))
                (.var 4) (.var 3) (.var 2)
                (by
                  simpa [establishedApp,
                    axisNamedOutcomeConstructorApp] using
                    axisOutcomeConstructorFree establishedName (by decide)
                      (.var 4) (.var 2) (.var 1))
                (by
                  simpa [establishedApp,
                    axisNamedOutcomeConstructorApp] using
                    axisOutcomeConstructorFree establishedName (by decide)
                      (.var 4) (.var 2) (.var 0))))))))

def axisRefutedConstructorPositive :
    ConstructorType axisRefinementName 5 axisRefutedType := by
  unfold axisRefutedType axisRefutedBodyType
  exact .field (.free axisSignatureTypeFree)
    (.field (.free refinementAxisTypeFree)
      (.field (.free (axisSignatureJudgmentFree (.var 1)))
        (.field
          (.free
            (.app (axisSignatureObstructionFree (.var 2)) (.var 0)))
          (.field
            (.free
              (.app (axisSignatureObstructionFree (.var 3)) (.var 1)))
            (.result
              (axisRefinementFamilyApplication (.var 4) (.var 3) (.var 2)
                (refutedApp (.var 4) (.var 2) (.var 1))
                (refutedApp (.var 4) (.var 2) (.var 0))
                (.var 4) (.var 3) (.var 2)
                (by
                  simpa [refutedApp, axisNamedOutcomeConstructorApp] using
                    axisOutcomeConstructorFree refutedName (by decide)
                      (.var 4) (.var 2) (.var 1))
                (by
                  simpa [refutedApp, axisNamedOutcomeConstructorApp] using
                    axisOutcomeConstructorFree refutedName (by decide)
                      (.var 4) (.var 2) (.var 0))))))))

def axisIncompleteConstructorPositive :
    ConstructorType axisRefinementName 5 axisIncompleteType := by
  unfold axisIncompleteType axisIncompleteBodyType
  exact .field (.free axisSignatureTypeFree)
    (.field (.free refinementAxisTypeFree)
      (.field (.free (axisSignatureJudgmentFree (.var 1)))
        (.field
          (.free (.app (axisSignatureFrontierFree (.var 2)) (.var 0)))
          (.field
            (.free (.app (axisSignatureFrontierFree (.var 3)) (.var 1)))
            (.result
              (axisRefinementFamilyApplication (.var 4) (.var 3) (.var 2)
                (incompleteApp (.var 4) (.var 2) (.var 1))
                (incompleteApp (.var 4) (.var 2) (.var 0))
                (.var 4) (.var 3) (.var 2)
                (by
                  simpa [incompleteApp,
                    axisNamedOutcomeConstructorApp] using
                    axisOutcomeConstructorFree incompleteName (by decide)
                      (.var 4) (.var 2) (.var 1))
                (by
                  simpa [incompleteApp,
                    axisNamedOutcomeConstructorApp] using
                    axisOutcomeConstructorFree incompleteName (by decide)
                      (.var 4) (.var 2) (.var 0))))))))

def refinementAxisBudgetFree {n : Nat} :
    FreeOf axisRefinementName (refinementAxisBudgetTm : Tower.Tm n) :=
  .const (by decide)

def refinementAxisAuthorityFree {n : Nat} :
    FreeOf axisRefinementName (refinementAxisAuthorityTm : Tower.Tm n) :=
  .const (by decide)

def budgetOutsideRefinementConstructorPositive :
    ConstructorType axisRefinementName 5
      budgetOutsideRefinementType := by
  unfold budgetOutsideRefinementType budgetOutsideRefinementBodyType
  exact .field (.free axisSignatureTypeFree)
    (.field (.free (axisSignatureJudgmentFree (.var 0)))
      (.field
        (.free (.app (axisSignatureBoundaryFree (.var 1)) (.var 0)))
        (.result
          (axisRefinementFamilyApplication (.var 2)
            refinementAxisBudgetTm (.var 1)
            (outsideFragmentApp (.var 2) (.var 1) (.var 0))
            (outsideFragmentApp (.var 2) (.var 1) (.var 0))
            (.var 2) refinementAxisBudgetFree (.var 1)
            (by
              simpa [outsideFragmentApp,
                axisNamedOutcomeConstructorApp] using
                axisOutcomeConstructorFree outsideFragmentName (by decide)
                  (.var 2) (.var 1) (.var 0))
            (by
              simpa [outsideFragmentApp,
                axisNamedOutcomeConstructorApp] using
                axisOutcomeConstructorFree outsideFragmentName (by decide)
                  (.var 2) (.var 1) (.var 0))))))

def budgetIncompleteEstablishedRefinementConstructorPositive :
    ConstructorType axisRefinementName 5
      budgetIncompleteEstablishedRefinementType := by
  unfold budgetIncompleteEstablishedRefinementType
    budgetIncompleteEstablishedRefinementBodyType
  exact .field (.free axisSignatureTypeFree)
    (.field (.free (axisSignatureJudgmentFree (.var 0)))
      (.field
        (.free (.app (axisSignatureFrontierFree (.var 1)) (.var 0)))
        (.field
          (.free (.app (axisSignatureEvidenceFree (.var 2)) (.var 1)))
          (.result
            (axisRefinementFamilyApplication (.var 3)
              refinementAxisBudgetTm (.var 2)
              (incompleteApp (.var 3) (.var 2) (.var 1))
              (establishedApp (.var 3) (.var 2) (.var 0))
              (.var 3) refinementAxisBudgetFree (.var 2)
              (by
                simpa [incompleteApp,
                  axisNamedOutcomeConstructorApp] using
                  axisOutcomeConstructorFree incompleteName (by decide)
                    (.var 3) (.var 2) (.var 1))
              (by
                simpa [establishedApp,
                  axisNamedOutcomeConstructorApp] using
                  axisOutcomeConstructorFree establishedName (by decide)
                    (.var 3) (.var 2) (.var 0)))))))

def budgetIncompleteRefutedRefinementConstructorPositive :
    ConstructorType axisRefinementName 5
      budgetIncompleteRefutedRefinementType := by
  unfold budgetIncompleteRefutedRefinementType
    budgetIncompleteRefutedRefinementBodyType
  exact .field (.free axisSignatureTypeFree)
    (.field (.free (axisSignatureJudgmentFree (.var 0)))
      (.field
        (.free (.app (axisSignatureFrontierFree (.var 1)) (.var 0)))
        (.field
          (.free
            (.app (axisSignatureObstructionFree (.var 2)) (.var 1)))
          (.result
            (axisRefinementFamilyApplication (.var 3)
              refinementAxisBudgetTm (.var 2)
              (incompleteApp (.var 3) (.var 2) (.var 1))
              (refutedApp (.var 3) (.var 2) (.var 0))
              (.var 3) refinementAxisBudgetFree (.var 2)
              (by
                simpa [incompleteApp,
                  axisNamedOutcomeConstructorApp] using
                  axisOutcomeConstructorFree incompleteName (by decide)
                    (.var 3) (.var 2) (.var 1))
              (by
                simpa [refutedApp,
                  axisNamedOutcomeConstructorApp] using
                  axisOutcomeConstructorFree refutedName (by decide)
                    (.var 3) (.var 2) (.var 0)))))))

def authorityOutsideRefinementConstructorPositive :
    ConstructorType axisRefinementName 5
      authorityOutsideRefinementType := by
  unfold authorityOutsideRefinementType authorityOutsideRefinementBodyType
  exact .field (.free axisSignatureTypeFree)
    (.field (.free (axisSignatureJudgmentFree (.var 0)))
      (.field
        (.free (.app (axisSignatureBoundaryFree (.var 1)) (.var 0)))
        (.field
          (.free (.app (axisSignatureBoundaryFree (.var 2)) (.var 1)))
          (.result
            (axisRefinementFamilyApplication (.var 3)
              refinementAxisAuthorityTm (.var 2)
              (outsideFragmentApp (.var 3) (.var 2) (.var 1))
              (outsideFragmentApp (.var 3) (.var 2) (.var 0))
              (.var 3) refinementAxisAuthorityFree (.var 2)
              (by
                simpa [outsideFragmentApp,
                  axisNamedOutcomeConstructorApp] using
                  axisOutcomeConstructorFree outsideFragmentName (by decide)
                    (.var 3) (.var 2) (.var 1))
              (by
                simpa [outsideFragmentApp,
                  axisNamedOutcomeConstructorApp] using
                  axisOutcomeConstructorFree outsideFragmentName (by decide)
                    (.var 3) (.var 2) (.var 0)))))))

def authorityOutsideEstablishedRefinementConstructorPositive :
    ConstructorType axisRefinementName 5
      authorityOutsideEstablishedRefinementType := by
  unfold authorityOutsideEstablishedRefinementType
    authorityOutsideEstablishedRefinementBodyType
  exact .field (.free axisSignatureTypeFree)
    (.field (.free (axisSignatureJudgmentFree (.var 0)))
      (.field
        (.free (.app (axisSignatureBoundaryFree (.var 1)) (.var 0)))
        (.field
          (.free (.app (axisSignatureEvidenceFree (.var 2)) (.var 1)))
          (.result
            (axisRefinementFamilyApplication (.var 3)
              refinementAxisAuthorityTm (.var 2)
              (outsideFragmentApp (.var 3) (.var 2) (.var 1))
              (establishedApp (.var 3) (.var 2) (.var 0))
              (.var 3) refinementAxisAuthorityFree (.var 2)
              (by
                simpa [outsideFragmentApp,
                  axisNamedOutcomeConstructorApp] using
                  axisOutcomeConstructorFree outsideFragmentName (by decide)
                    (.var 3) (.var 2) (.var 1))
              (by
                simpa [establishedApp,
                  axisNamedOutcomeConstructorApp] using
                  axisOutcomeConstructorFree establishedName (by decide)
                    (.var 3) (.var 2) (.var 0)))))))

def authorityOutsideRefutedRefinementConstructorPositive :
    ConstructorType axisRefinementName 5
      authorityOutsideRefutedRefinementType := by
  unfold authorityOutsideRefutedRefinementType
    authorityOutsideRefutedRefinementBodyType
  exact .field (.free axisSignatureTypeFree)
    (.field (.free (axisSignatureJudgmentFree (.var 0)))
      (.field
        (.free (.app (axisSignatureBoundaryFree (.var 1)) (.var 0)))
        (.field
          (.free
            (.app (axisSignatureObstructionFree (.var 2)) (.var 1)))
          (.result
            (axisRefinementFamilyApplication (.var 3)
              refinementAxisAuthorityTm (.var 2)
              (outsideFragmentApp (.var 3) (.var 2) (.var 1))
              (refutedApp (.var 3) (.var 2) (.var 0))
              (.var 3) refinementAxisAuthorityFree (.var 2)
              (by
                simpa [outsideFragmentApp,
                  axisNamedOutcomeConstructorApp] using
                  axisOutcomeConstructorFree outsideFragmentName (by decide)
                    (.var 3) (.var 2) (.var 1))
              (by
                simpa [refutedApp,
                  axisNamedOutcomeConstructorApp] using
                  axisOutcomeConstructorFree refutedName (by decide)
                    (.var 3) (.var 2) (.var 0)))))))

def authorityOutsideIncompleteRefinementConstructorPositive :
    ConstructorType axisRefinementName 5
      authorityOutsideIncompleteRefinementType := by
  unfold authorityOutsideIncompleteRefinementType
    authorityOutsideIncompleteRefinementBodyType
  exact .field (.free axisSignatureTypeFree)
    (.field (.free (axisSignatureJudgmentFree (.var 0)))
      (.field
        (.free (.app (axisSignatureBoundaryFree (.var 1)) (.var 0)))
        (.field
          (.free (.app (axisSignatureFrontierFree (.var 2)) (.var 1)))
          (.result
            (axisRefinementFamilyApplication (.var 3)
              refinementAxisAuthorityTm (.var 2)
              (outsideFragmentApp (.var 3) (.var 2) (.var 1))
              (incompleteApp (.var 3) (.var 2) (.var 0))
              (.var 3) refinementAxisAuthorityFree (.var 2)
              (by
                simpa [outsideFragmentApp,
                  axisNamedOutcomeConstructorApp] using
                  axisOutcomeConstructorFree outsideFragmentName (by decide)
                    (.var 3) (.var 2) (.var 1))
              (by
                simpa [incompleteApp,
                  axisNamedOutcomeConstructorApp] using
                    axisOutcomeConstructorFree incompleteName (by decide)
                      (.var 3) (.var 2) (.var 0)))))))

def axisEstablishedConstructorSpec :
    ConstructorSpec rawAxisRefinementSignature axisRefinementName 5 where
  name := axisEstablishedName
  type := axisEstablishedType
  declared := typeOf_axisEstablished
  positive := axisEstablishedConstructorPositive

def axisRefutedConstructorSpec :
    ConstructorSpec rawAxisRefinementSignature axisRefinementName 5 where
  name := axisRefutedName
  type := axisRefutedType
  declared := typeOf_axisRefuted
  positive := axisRefutedConstructorPositive

def axisIncompleteConstructorSpec :
    ConstructorSpec rawAxisRefinementSignature axisRefinementName 5 where
  name := axisIncompleteName
  type := axisIncompleteType
  declared := typeOf_axisIncomplete
  positive := axisIncompleteConstructorPositive

def budgetOutsideRefinementConstructorSpec :
    ConstructorSpec rawAxisRefinementSignature axisRefinementName 5 where
  name := budgetOutsideRefinementName
  type := budgetOutsideRefinementType
  declared := typeOf_budgetOutsideRefinement
  positive := budgetOutsideRefinementConstructorPositive

def budgetIncompleteEstablishedRefinementConstructorSpec :
    ConstructorSpec rawAxisRefinementSignature axisRefinementName 5 where
  name := budgetIncompleteEstablishedRefinementName
  type := budgetIncompleteEstablishedRefinementType
  declared := typeOf_budgetIncompleteEstablishedRefinement
  positive := budgetIncompleteEstablishedRefinementConstructorPositive

def budgetIncompleteRefutedRefinementConstructorSpec :
    ConstructorSpec rawAxisRefinementSignature axisRefinementName 5 where
  name := budgetIncompleteRefutedRefinementName
  type := budgetIncompleteRefutedRefinementType
  declared := typeOf_budgetIncompleteRefutedRefinement
  positive := budgetIncompleteRefutedRefinementConstructorPositive

def authorityOutsideRefinementConstructorSpec :
    ConstructorSpec rawAxisRefinementSignature axisRefinementName 5 where
  name := authorityOutsideRefinementName
  type := authorityOutsideRefinementType
  declared := typeOf_authorityOutsideRefinement
  positive := authorityOutsideRefinementConstructorPositive

def authorityOutsideEstablishedRefinementConstructorSpec :
    ConstructorSpec rawAxisRefinementSignature axisRefinementName 5 where
  name := authorityOutsideEstablishedRefinementName
  type := authorityOutsideEstablishedRefinementType
  declared := typeOf_authorityOutsideEstablishedRefinement
  positive := authorityOutsideEstablishedRefinementConstructorPositive

def authorityOutsideRefutedRefinementConstructorSpec :
    ConstructorSpec rawAxisRefinementSignature axisRefinementName 5 where
  name := authorityOutsideRefutedRefinementName
  type := authorityOutsideRefutedRefinementType
  declared := typeOf_authorityOutsideRefutedRefinement
  positive := authorityOutsideRefutedRefinementConstructorPositive

def authorityOutsideIncompleteRefinementConstructorSpec :
    ConstructorSpec rawAxisRefinementSignature axisRefinementName 5 where
  name := authorityOutsideIncompleteRefinementName
  type := authorityOutsideIncompleteRefinementType
  declared := typeOf_authorityOutsideIncompleteRefinement
  positive := authorityOutsideIncompleteRefinementConstructorPositive

def axisRefinementConstructors :
    List (ConstructorSpec rawAxisRefinementSignature
      axisRefinementName 5) :=
  [axisEstablishedConstructorSpec, axisRefutedConstructorSpec,
    axisIncompleteConstructorSpec, budgetOutsideRefinementConstructorSpec,
    budgetIncompleteEstablishedRefinementConstructorSpec,
    budgetIncompleteRefutedRefinementConstructorSpec,
    authorityOutsideRefinementConstructorSpec,
    authorityOutsideEstablishedRefinementConstructorSpec,
    authorityOutsideRefutedRefinementConstructorSpec,
    authorityOutsideIncompleteRefinementConstructorSpec]

def axisRefinementEliminatorSpec :
    EliminatorSpec rawAxisRefinementSignature where
  name := axisRefinementEliminateName
  type := axisRefinementEliminateType
  declared := typeOf_axisRefinementEliminate

/-- An axis-indexed refinement witness in a function domain is rejected as a
negative recursive occurrence. -/
theorem axisRefinementInFunctionDomain_not_strictlyPositive :
    StrictlyPositive axisRefinementName 5
      (.pi
        (axisRefinementApp (.var 4 : Tower.Tm 5) (.var 3) (.var 2)
          (.var 1) (.var 0))
        (.var 0)) → False :=
  recursivePiDomain_not_strictlyPositive
    (axisRefinementFamilyApplication (.var 4) (.var 3) (.var 2)
      (.var 1) (.var 0) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))
    (.var 0)

/-! ### Canonical typed computation schemas -/

abbrev AxisRefinementTypedIotaReceipt (context : Tower.Ctx n)
    (left right type : Tower.Tm n) : Type :=
  ProofRelevantStepReceipt refinementAxisRules rawAxisRefinementSignature
    proofRelevantAxisRefinementComputation context left right type

def axisRefinementParameterBranches : AxisRefinementBranches 12 where
  established := .var 9
  refuted := .var 8
  incomplete := .var 7
  budgetOutside := .var 6
  budgetIncompleteEstablished := .var 5
  budgetIncompleteRefuted := .var 4
  authorityOutside := .var 3
  authorityOutsideEstablished := .var 2
  authorityOutsideRefuted := .var 1
  authorityOutsideIncomplete := .var 0

def axisRefinementEliminateAtParameters : Tower.Tm 12 :=
  axisRefinementEliminateAtBranches (.var 11) (.var 10)
    axisRefinementParameterBranches

set_option maxHeartbeats 1000000 in
theorem axisRefinementEliminateAtParameters_hasType :
    AxisRefinementHasType
      axisEliminatorContextAuthorityOutsideIncomplete
      axisRefinementEliminateAtParameters
      axisRefinementEliminateResultType := by
  have afterSignature := Presentation.HasType.appElim
    (axisRefinementEliminateConstant_hasType
      (context := axisEliminatorContextAuthorityOutsideIncomplete))
    (Presentation.HasType.var 11)
  have afterMotive := Presentation.HasType.appElim afterSignature
    (Presentation.HasType.var 10)
  have afterEstablished := Presentation.HasType.appElim afterMotive
    (Presentation.HasType.var 9)
  have afterRefuted := Presentation.HasType.appElim afterEstablished
    (Presentation.HasType.var 8)
  have afterIncomplete := Presentation.HasType.appElim afterRefuted
    (Presentation.HasType.var 7)
  have afterBudgetOutside := Presentation.HasType.appElim afterIncomplete
    (Presentation.HasType.var 6)
  have afterBudgetIncompleteEstablished := Presentation.HasType.appElim
    afterBudgetOutside (Presentation.HasType.var 5)
  have afterBudgetIncompleteRefuted := Presentation.HasType.appElim
    afterBudgetIncompleteEstablished (Presentation.HasType.var 4)
  have afterAuthorityOutside := Presentation.HasType.appElim
    afterBudgetIncompleteRefuted (Presentation.HasType.var 3)
  have afterAuthorityOutsideEstablished := Presentation.HasType.appElim
    afterAuthorityOutside (Presentation.HasType.var 2)
  have afterAuthorityOutsideRefuted := Presentation.HasType.appElim
    afterAuthorityOutsideEstablished (Presentation.HasType.var 1)
  have afterAuthorityOutsideIncomplete := Presentation.HasType.appElim
    afterAuthorityOutsideRefuted (Presentation.HasType.var 0)
  convert afterAuthorityOutsideIncomplete using 1
  all_goals rfl

def axisRefinementBranchesAfterFour : AxisRefinementBranches 16 where
  established := .var 13
  refuted := .var 12
  incomplete := .var 11
  budgetOutside := .var 10
  budgetIncompleteEstablished := .var 9
  budgetIncompleteRefuted := .var 8
  authorityOutside := .var 7
  authorityOutsideEstablished := .var 6
  authorityOutsideRefuted := .var 5
  authorityOutsideIncomplete := .var 4

def axisIotaContextA : Tower.Ctx 13 :=
  .snoc axisEliminatorContextAuthorityOutsideIncomplete refinementAxisTm

def axisIotaContextAJ : Tower.Ctx 14 :=
  .snoc axisIotaContextA (signatureJudgment (.var 12))

def axisEstablishedIotaContextBefore : Tower.Ctx 15 :=
  .snoc axisIotaContextAJ
    (.app (signatureEvidence (.var 13)) (.var 0))

def axisEstablishedIotaContext : Tower.Ctx 16 :=
  .snoc axisEstablishedIotaContextBefore
    (.app (signatureEvidence (.var 14)) (.var 1))

def axisEstablishedIotaBefore : Tower.Tm 16 :=
  establishedApp (.var 15) (.var 2) (.var 1)

def axisEstablishedIotaAfter : Tower.Tm 16 :=
  establishedApp (.var 15) (.var 2) (.var 0)

def axisEstablishedIotaRefinement : Tower.Tm 16 :=
  axisEstablishedApp (.var 15) (.var 3) (.var 2) (.var 1) (.var 0)

def axisEstablishedIotaLeft : Tower.Tm 16 :=
  axisRefinementEliminateApp (.var 15) (.var 14)
    axisRefinementBranchesAfterFour (.var 3) (.var 2)
    axisEstablishedIotaBefore axisEstablishedIotaAfter
    axisEstablishedIotaRefinement

def axisEstablishedIotaRight : Tower.Tm 16 :=
  applyArgs (.var 13) [(.var 3), (.var 2), (.var 1), (.var 0)]

def axisEstablishedIotaType : Tower.Tm 16 :=
  axisRefinementMotiveApp (.var 14) (.var 3) (.var 2)
    axisEstablishedIotaBefore axisEstablishedIotaAfter
    axisEstablishedIotaRefinement

set_option maxHeartbeats 1000000 in
def axisEstablishedIotaReceipt :
    AxisRefinementTypedIotaReceipt axisEstablishedIotaContext
      axisEstablishedIotaLeft axisEstablishedIotaRight
      axisEstablishedIotaType where
  sourceTyping := by
    have afterAxisBinder := axisRefinementEliminateAtParameters_hasType.weaken
      (extension := refinementAxisTm)
    have afterJudgmentBinder := afterAxisBinder.weaken
      (extension := signatureJudgment (.var 12))
    have afterBeforeBinder := afterJudgmentBinder.weaken
      (extension := .app (signatureEvidence (.var 13)) (.var 0))
    have weakened := afterBeforeBinder.weaken
      (extension := .app (signatureEvidence (.var 14)) (.var 1))
    have judgmentTyping :
        AxisRefinementHasType axisEstablishedIotaContext (.var 2)
          (signatureJudgment (.var 15)) := by
      exact Presentation.HasType.var 2
    have beforeEvidenceTyping :
        AxisRefinementHasType axisEstablishedIotaContext (.var 1)
          (.app (signatureEvidence (.var 15)) (.var 2)) := by
      exact Presentation.HasType.var 1
    have afterEvidenceTyping :
        AxisRefinementHasType axisEstablishedIotaContext (.var 0)
          (.app (signatureEvidence (.var 15)) (.var 2)) := by
      exact Presentation.HasType.var 0
    have beforeTyping := establishedApp_hasAxisRefinementType
      (Presentation.HasType.var 15) judgmentTyping beforeEvidenceTyping
    have afterTyping := establishedApp_hasAxisRefinementType
      (Presentation.HasType.var 15) judgmentTyping afterEvidenceTyping
    have refinementTyping := axisEstablishedApp_hasType
      (Presentation.HasType.var 15) (Presentation.HasType.var 3)
      judgmentTyping beforeEvidenceTyping afterEvidenceTyping
    have afterAxis := Presentation.HasType.appElim weakened
      (Presentation.HasType.var 3)
    have afterJudgment := Presentation.HasType.appElim afterAxis
      judgmentTyping
    have afterBefore := Presentation.HasType.appElim afterJudgment
      beforeTyping
    have afterAfter := Presentation.HasType.appElim afterBefore afterTyping
    have source := Presentation.HasType.appElim afterAfter refinementTyping
    convert source using 1
    all_goals rfl
  targetTyping := by
    have afterAxis := Presentation.HasType.appElim
      (Presentation.HasType.var (R := axisRefinementRules)
        (Γ := axisEstablishedIotaContext) (13 : Fin 16))
      (Presentation.HasType.var 3)
    have afterJudgment := Presentation.HasType.appElim afterAxis
      (Presentation.HasType.var 2)
    have afterBefore := Presentation.HasType.appElim afterJudgment
      (Presentation.HasType.var 1)
    have target := Presentation.HasType.appElim afterBefore
      (Presentation.HasType.var 0)
    convert target using 1
    all_goals rfl
  evidence := by
    change AxisRefinementIotaEvidence 16 axisEstablishedIotaLeft
      axisEstablishedIotaRight
    unfold axisEstablishedIotaLeft axisEstablishedIotaRight
      axisEstablishedIotaBefore axisEstablishedIotaAfter
      axisEstablishedIotaRefinement
    exact AxisRefinementIotaEvidence.established
      (.var 15) (.var 14) axisRefinementBranchesAfterFour
      (.var 3) (.var 2) (.var 1) (.var 0)

def axisEstablishedIotaSchema :
    IotaSchema refinementAxisRules rawAxisRefinementSignature
      proofRelevantAxisRefinementComputation 16 where
  context := axisEstablishedIotaContext
  left := axisEstablishedIotaLeft
  right := axisEstablishedIotaRight
  type := axisEstablishedIotaType
  receipt := axisEstablishedIotaReceipt

def axisRefutedIotaContextBefore : Tower.Ctx 15 :=
  .snoc axisIotaContextAJ
    (.app (signatureObstruction (.var 13)) (.var 0))

def axisRefutedIotaContext : Tower.Ctx 16 :=
  .snoc axisRefutedIotaContextBefore
    (.app (signatureObstruction (.var 14)) (.var 1))

def axisRefutedIotaBefore : Tower.Tm 16 :=
  refutedApp (.var 15) (.var 2) (.var 1)

def axisRefutedIotaAfter : Tower.Tm 16 :=
  refutedApp (.var 15) (.var 2) (.var 0)

def axisRefutedIotaRefinement : Tower.Tm 16 :=
  axisRefutedApp (.var 15) (.var 3) (.var 2) (.var 1) (.var 0)

def axisRefutedIotaLeft : Tower.Tm 16 :=
  axisRefinementEliminateApp (.var 15) (.var 14)
    axisRefinementBranchesAfterFour (.var 3) (.var 2)
    axisRefutedIotaBefore axisRefutedIotaAfter axisRefutedIotaRefinement

def axisRefutedIotaRight : Tower.Tm 16 :=
  applyArgs (.var 12) [(.var 3), (.var 2), (.var 1), (.var 0)]

def axisRefutedIotaType : Tower.Tm 16 :=
  axisRefinementMotiveApp (.var 14) (.var 3) (.var 2)
    axisRefutedIotaBefore axisRefutedIotaAfter axisRefutedIotaRefinement

set_option maxHeartbeats 1000000 in
def axisRefutedIotaReceipt :
    AxisRefinementTypedIotaReceipt axisRefutedIotaContext
      axisRefutedIotaLeft axisRefutedIotaRight axisRefutedIotaType where
  sourceTyping := by
    have afterAxisBinder := axisRefinementEliminateAtParameters_hasType.weaken
      (extension := refinementAxisTm)
    have afterJudgmentBinder := afterAxisBinder.weaken
      (extension := signatureJudgment (.var 12))
    have afterBeforeBinder := afterJudgmentBinder.weaken
      (extension := .app (signatureObstruction (.var 13)) (.var 0))
    have weakened := afterBeforeBinder.weaken
      (extension := .app (signatureObstruction (.var 14)) (.var 1))
    have judgmentTyping :
        AxisRefinementHasType axisRefutedIotaContext (.var 2)
          (signatureJudgment (.var 15)) := by
      exact Presentation.HasType.var 2
    have beforeObstructionTyping :
        AxisRefinementHasType axisRefutedIotaContext (.var 1)
          (.app (signatureObstruction (.var 15)) (.var 2)) := by
      exact Presentation.HasType.var 1
    have afterObstructionTyping :
        AxisRefinementHasType axisRefutedIotaContext (.var 0)
          (.app (signatureObstruction (.var 15)) (.var 2)) := by
      exact Presentation.HasType.var 0
    have beforeTyping := refutedApp_hasAxisRefinementType
      (Presentation.HasType.var 15) judgmentTyping beforeObstructionTyping
    have afterTyping := refutedApp_hasAxisRefinementType
      (Presentation.HasType.var 15) judgmentTyping afterObstructionTyping
    have refinementTyping := axisRefutedApp_hasType
      (Presentation.HasType.var 15) (Presentation.HasType.var 3)
      judgmentTyping beforeObstructionTyping afterObstructionTyping
    have afterAxis := Presentation.HasType.appElim weakened
      (Presentation.HasType.var 3)
    have afterJudgment := Presentation.HasType.appElim afterAxis
      judgmentTyping
    have afterBefore := Presentation.HasType.appElim afterJudgment
      beforeTyping
    have afterAfter := Presentation.HasType.appElim afterBefore afterTyping
    have source := Presentation.HasType.appElim afterAfter refinementTyping
    convert source using 1
    all_goals rfl
  targetTyping := by
    have afterAxis := Presentation.HasType.appElim
      (Presentation.HasType.var (R := axisRefinementRules)
        (Γ := axisRefutedIotaContext) (12 : Fin 16))
      (Presentation.HasType.var 3)
    have afterJudgment := Presentation.HasType.appElim afterAxis
      (Presentation.HasType.var 2)
    have afterBefore := Presentation.HasType.appElim afterJudgment
      (Presentation.HasType.var 1)
    have target := Presentation.HasType.appElim afterBefore
      (Presentation.HasType.var 0)
    convert target using 1
    all_goals rfl
  evidence := by
    change AxisRefinementIotaEvidence 16 axisRefutedIotaLeft
      axisRefutedIotaRight
    unfold axisRefutedIotaLeft axisRefutedIotaRight axisRefutedIotaBefore
      axisRefutedIotaAfter axisRefutedIotaRefinement
    exact AxisRefinementIotaEvidence.refuted
      (.var 15) (.var 14) axisRefinementBranchesAfterFour
      (.var 3) (.var 2) (.var 1) (.var 0)

def axisRefutedIotaSchema :
    IotaSchema refinementAxisRules rawAxisRefinementSignature
      proofRelevantAxisRefinementComputation 16 where
  context := axisRefutedIotaContext
  left := axisRefutedIotaLeft
  right := axisRefutedIotaRight
  type := axisRefutedIotaType
  receipt := axisRefutedIotaReceipt

def axisIncompleteIotaContextBefore : Tower.Ctx 15 :=
  .snoc axisIotaContextAJ
    (.app (signatureFrontier (.var 13)) (.var 0))

def axisIncompleteIotaContext : Tower.Ctx 16 :=
  .snoc axisIncompleteIotaContextBefore
    (.app (signatureFrontier (.var 14)) (.var 1))

def axisIncompleteIotaBefore : Tower.Tm 16 :=
  incompleteApp (.var 15) (.var 2) (.var 1)

def axisIncompleteIotaAfter : Tower.Tm 16 :=
  incompleteApp (.var 15) (.var 2) (.var 0)

def axisIncompleteIotaRefinement : Tower.Tm 16 :=
  axisIncompleteApp (.var 15) (.var 3) (.var 2) (.var 1) (.var 0)

def axisIncompleteIotaLeft : Tower.Tm 16 :=
  axisRefinementEliminateApp (.var 15) (.var 14)
    axisRefinementBranchesAfterFour (.var 3) (.var 2)
    axisIncompleteIotaBefore axisIncompleteIotaAfter
    axisIncompleteIotaRefinement

def axisIncompleteIotaRight : Tower.Tm 16 :=
  applyArgs (.var 11) [(.var 3), (.var 2), (.var 1), (.var 0)]

def axisIncompleteIotaType : Tower.Tm 16 :=
  axisRefinementMotiveApp (.var 14) (.var 3) (.var 2)
    axisIncompleteIotaBefore axisIncompleteIotaAfter
    axisIncompleteIotaRefinement

set_option maxHeartbeats 1000000 in
def axisIncompleteIotaReceipt :
    AxisRefinementTypedIotaReceipt axisIncompleteIotaContext
      axisIncompleteIotaLeft axisIncompleteIotaRight
      axisIncompleteIotaType where
  sourceTyping := by
    have afterAxisBinder := axisRefinementEliminateAtParameters_hasType.weaken
      (extension := refinementAxisTm)
    have afterJudgmentBinder := afterAxisBinder.weaken
      (extension := signatureJudgment (.var 12))
    have afterBeforeBinder := afterJudgmentBinder.weaken
      (extension := .app (signatureFrontier (.var 13)) (.var 0))
    have weakened := afterBeforeBinder.weaken
      (extension := .app (signatureFrontier (.var 14)) (.var 1))
    have judgmentTyping :
        AxisRefinementHasType axisIncompleteIotaContext (.var 2)
          (signatureJudgment (.var 15)) := by
      exact Presentation.HasType.var 2
    have beforeFrontierTyping :
        AxisRefinementHasType axisIncompleteIotaContext (.var 1)
          (.app (signatureFrontier (.var 15)) (.var 2)) := by
      exact Presentation.HasType.var 1
    have afterFrontierTyping :
        AxisRefinementHasType axisIncompleteIotaContext (.var 0)
          (.app (signatureFrontier (.var 15)) (.var 2)) := by
      exact Presentation.HasType.var 0
    have beforeTyping := incompleteApp_hasAxisRefinementType
      (Presentation.HasType.var 15) judgmentTyping beforeFrontierTyping
    have afterTyping := incompleteApp_hasAxisRefinementType
      (Presentation.HasType.var 15) judgmentTyping afterFrontierTyping
    have refinementTyping := axisIncompleteApp_hasType
      (Presentation.HasType.var 15) (Presentation.HasType.var 3)
      judgmentTyping beforeFrontierTyping afterFrontierTyping
    have afterAxis := Presentation.HasType.appElim weakened
      (Presentation.HasType.var 3)
    have afterJudgment := Presentation.HasType.appElim afterAxis
      judgmentTyping
    have afterBefore := Presentation.HasType.appElim afterJudgment
      beforeTyping
    have afterAfter := Presentation.HasType.appElim afterBefore afterTyping
    have source := Presentation.HasType.appElim afterAfter refinementTyping
    convert source using 1
    all_goals rfl
  targetTyping := by
    have afterAxis := Presentation.HasType.appElim
      (Presentation.HasType.var (R := axisRefinementRules)
        (Γ := axisIncompleteIotaContext) (11 : Fin 16))
      (Presentation.HasType.var 3)
    have afterJudgment := Presentation.HasType.appElim afterAxis
      (Presentation.HasType.var 2)
    have afterBefore := Presentation.HasType.appElim afterJudgment
      (Presentation.HasType.var 1)
    have target := Presentation.HasType.appElim afterBefore
      (Presentation.HasType.var 0)
    convert target using 1
    all_goals rfl
  evidence := by
    change AxisRefinementIotaEvidence 16 axisIncompleteIotaLeft
      axisIncompleteIotaRight
    unfold axisIncompleteIotaLeft axisIncompleteIotaRight
      axisIncompleteIotaBefore axisIncompleteIotaAfter
      axisIncompleteIotaRefinement
    exact AxisRefinementIotaEvidence.incomplete
      (.var 15) (.var 14) axisRefinementBranchesAfterFour
      (.var 3) (.var 2) (.var 1) (.var 0)

def axisIncompleteIotaSchema :
    IotaSchema refinementAxisRules rawAxisRefinementSignature
      proofRelevantAxisRefinementComputation 16 where
  context := axisIncompleteIotaContext
  left := axisIncompleteIotaLeft
  right := axisIncompleteIotaRight
  type := axisIncompleteIotaType
  receipt := axisIncompleteIotaReceipt

def axisRefinementBranchesAfterTwo : AxisRefinementBranches 14 where
  established := .var 11
  refuted := .var 10
  incomplete := .var 9
  budgetOutside := .var 8
  budgetIncompleteEstablished := .var 7
  budgetIncompleteRefuted := .var 6
  authorityOutside := .var 5
  authorityOutsideEstablished := .var 4
  authorityOutsideRefuted := .var 3
  authorityOutsideIncomplete := .var 2

def fixedAxisIotaContextJ : Tower.Ctx 13 :=
  .snoc axisEliminatorContextAuthorityOutsideIncomplete
    (signatureJudgment (.var 11))

def budgetOutsideIotaContext : Tower.Ctx 14 :=
  .snoc fixedAxisIotaContextJ
    (.app (signatureBoundary (.var 12)) (.var 0))

def budgetOutsideIotaBefore : Tower.Tm 14 :=
  outsideFragmentApp (.var 13) (.var 1) (.var 0)

def budgetOutsideIotaRefinement : Tower.Tm 14 :=
  budgetOutsideRefinementApp (.var 13) (.var 1) (.var 0)

def budgetOutsideIotaLeft : Tower.Tm 14 :=
  axisRefinementEliminateApp (.var 13) (.var 12)
    axisRefinementBranchesAfterTwo refinementAxisBudgetTm (.var 1)
    budgetOutsideIotaBefore budgetOutsideIotaBefore
    budgetOutsideIotaRefinement

def budgetOutsideIotaRight : Tower.Tm 14 :=
  applyArgs (.var 8) [(.var 1), (.var 0)]

def budgetOutsideIotaType : Tower.Tm 14 :=
  axisRefinementMotiveApp (.var 12) refinementAxisBudgetTm (.var 1)
    budgetOutsideIotaBefore budgetOutsideIotaBefore
    budgetOutsideIotaRefinement

set_option maxHeartbeats 1000000 in
def budgetOutsideIotaReceipt :
    AxisRefinementTypedIotaReceipt budgetOutsideIotaContext
      budgetOutsideIotaLeft budgetOutsideIotaRight budgetOutsideIotaType where
  sourceTyping := by
    have afterJudgmentBinder :=
      axisRefinementEliminateAtParameters_hasType.weaken
        (extension := signatureJudgment (.var 11))
    have weakened := afterJudgmentBinder.weaken
      (extension := .app (signatureBoundary (.var 12)) (.var 0))
    have judgmentTyping :
        AxisRefinementHasType budgetOutsideIotaContext (.var 1)
          (signatureJudgment (.var 13)) := by
      exact Presentation.HasType.var 1
    have reasonTyping :
        AxisRefinementHasType budgetOutsideIotaContext (.var 0)
          (.app (signatureBoundary (.var 13)) (.var 1)) := by
      exact Presentation.HasType.var 0
    have outcomeTyping := outsideFragmentApp_hasAxisRefinementType
      (Presentation.HasType.var 13) judgmentTyping reasonTyping
    have refinementTyping := budgetOutsideRefinementApp_hasType
      (Presentation.HasType.var 13) judgmentTyping reasonTyping
    have afterAxis := Presentation.HasType.appElim weakened
      refinementAxisBudgetTm_hasAxisRefinementType
    have afterJudgment := Presentation.HasType.appElim afterAxis
      judgmentTyping
    have afterBefore := Presentation.HasType.appElim afterJudgment
      outcomeTyping
    have afterAfter := Presentation.HasType.appElim afterBefore outcomeTyping
    have source := Presentation.HasType.appElim afterAfter refinementTyping
    convert source using 1
    all_goals rfl
  targetTyping := by
    have afterJudgment := Presentation.HasType.appElim
      (Presentation.HasType.var (R := axisRefinementRules)
        (Γ := budgetOutsideIotaContext) (8 : Fin 14))
      (Presentation.HasType.var 1)
    have target := Presentation.HasType.appElim afterJudgment
      (Presentation.HasType.var 0)
    convert target using 1
    all_goals rfl
  evidence := by
    change AxisRefinementIotaEvidence 14 budgetOutsideIotaLeft
      budgetOutsideIotaRight
    unfold budgetOutsideIotaLeft budgetOutsideIotaRight
      budgetOutsideIotaBefore budgetOutsideIotaRefinement
    exact AxisRefinementIotaEvidence.budgetOutside
      (.var 13) (.var 12) axisRefinementBranchesAfterTwo
      (.var 1) (.var 0)

def budgetOutsideIotaSchema :
    IotaSchema refinementAxisRules rawAxisRefinementSignature
      proofRelevantAxisRefinementComputation 14 where
  context := budgetOutsideIotaContext
  left := budgetOutsideIotaLeft
  right := budgetOutsideIotaRight
  type := budgetOutsideIotaType
  receipt := budgetOutsideIotaReceipt

def axisRefinementBranchesAfterThree : AxisRefinementBranches 15 where
  established := .var 12
  refuted := .var 11
  incomplete := .var 10
  budgetOutside := .var 9
  budgetIncompleteEstablished := .var 8
  budgetIncompleteRefuted := .var 7
  authorityOutside := .var 6
  authorityOutsideEstablished := .var 5
  authorityOutsideRefuted := .var 4
  authorityOutsideIncomplete := .var 3

def budgetIncompleteEstablishedIotaContextBefore : Tower.Ctx 14 :=
  .snoc fixedAxisIotaContextJ
    (.app (signatureFrontier (.var 12)) (.var 0))

def budgetIncompleteEstablishedIotaContext : Tower.Ctx 15 :=
  .snoc budgetIncompleteEstablishedIotaContextBefore
    (.app (signatureEvidence (.var 13)) (.var 1))

def budgetIncompleteEstablishedIotaBefore : Tower.Tm 15 :=
  incompleteApp (.var 14) (.var 2) (.var 1)

def budgetIncompleteEstablishedIotaAfter : Tower.Tm 15 :=
  establishedApp (.var 14) (.var 2) (.var 0)

def budgetIncompleteEstablishedIotaRefinement : Tower.Tm 15 :=
  budgetIncompleteEstablishedRefinementApp (.var 14) (.var 2)
    (.var 1) (.var 0)

def budgetIncompleteEstablishedIotaLeft : Tower.Tm 15 :=
  axisRefinementEliminateApp (.var 14) (.var 13)
    axisRefinementBranchesAfterThree refinementAxisBudgetTm (.var 2)
    budgetIncompleteEstablishedIotaBefore
    budgetIncompleteEstablishedIotaAfter
    budgetIncompleteEstablishedIotaRefinement

def budgetIncompleteEstablishedIotaRight : Tower.Tm 15 :=
  applyArgs (.var 8) [(.var 2), (.var 1), (.var 0)]

def budgetIncompleteEstablishedIotaType : Tower.Tm 15 :=
  axisRefinementMotiveApp (.var 13) refinementAxisBudgetTm (.var 2)
    budgetIncompleteEstablishedIotaBefore
    budgetIncompleteEstablishedIotaAfter
    budgetIncompleteEstablishedIotaRefinement

set_option maxHeartbeats 1000000 in
def budgetIncompleteEstablishedIotaReceipt :
    AxisRefinementTypedIotaReceipt
      budgetIncompleteEstablishedIotaContext
      budgetIncompleteEstablishedIotaLeft
      budgetIncompleteEstablishedIotaRight
      budgetIncompleteEstablishedIotaType where
  sourceTyping := by
    have afterJudgmentBinder :=
      axisRefinementEliminateAtParameters_hasType.weaken
        (extension := signatureJudgment (.var 11))
    have afterBeforeBinder := afterJudgmentBinder.weaken
      (extension := .app (signatureFrontier (.var 12)) (.var 0))
    have weakened := afterBeforeBinder.weaken
      (extension := .app (signatureEvidence (.var 13)) (.var 1))
    have judgmentTyping :
        AxisRefinementHasType budgetIncompleteEstablishedIotaContext
          (.var 2) (signatureJudgment (.var 14)) := by
      exact Presentation.HasType.var 2
    have frontierTyping :
        AxisRefinementHasType budgetIncompleteEstablishedIotaContext
          (.var 1) (.app (signatureFrontier (.var 14)) (.var 2)) := by
      exact Presentation.HasType.var 1
    have evidenceTyping :
        AxisRefinementHasType budgetIncompleteEstablishedIotaContext
          (.var 0) (.app (signatureEvidence (.var 14)) (.var 2)) := by
      exact Presentation.HasType.var 0
    have beforeTyping := incompleteApp_hasAxisRefinementType
      (Presentation.HasType.var 14) judgmentTyping frontierTyping
    have afterTyping := establishedApp_hasAxisRefinementType
      (Presentation.HasType.var 14) judgmentTyping evidenceTyping
    have refinementTyping :=
      budgetIncompleteEstablishedRefinementApp_hasType
        (Presentation.HasType.var 14) judgmentTyping frontierTyping
        evidenceTyping
    have afterAxis := Presentation.HasType.appElim weakened
      refinementAxisBudgetTm_hasAxisRefinementType
    have afterJudgment := Presentation.HasType.appElim afterAxis
      judgmentTyping
    have afterBefore := Presentation.HasType.appElim afterJudgment
      beforeTyping
    have afterAfter := Presentation.HasType.appElim afterBefore afterTyping
    have source := Presentation.HasType.appElim afterAfter refinementTyping
    convert source using 1
    all_goals rfl
  targetTyping := by
    have afterJudgment := Presentation.HasType.appElim
      (Presentation.HasType.var (R := axisRefinementRules)
        (Γ := budgetIncompleteEstablishedIotaContext) (8 : Fin 15))
      (Presentation.HasType.var 2)
    have afterFrontier := Presentation.HasType.appElim afterJudgment
      (Presentation.HasType.var 1)
    have target := Presentation.HasType.appElim afterFrontier
      (Presentation.HasType.var 0)
    convert target using 1
    all_goals rfl
  evidence := by
    change AxisRefinementIotaEvidence 15
      budgetIncompleteEstablishedIotaLeft
      budgetIncompleteEstablishedIotaRight
    unfold budgetIncompleteEstablishedIotaLeft
      budgetIncompleteEstablishedIotaRight
      budgetIncompleteEstablishedIotaBefore
      budgetIncompleteEstablishedIotaAfter
      budgetIncompleteEstablishedIotaRefinement
    exact AxisRefinementIotaEvidence.budgetIncompleteEstablished
      (.var 14) (.var 13) axisRefinementBranchesAfterThree
      (.var 2) (.var 1) (.var 0)

def budgetIncompleteEstablishedIotaSchema :
    IotaSchema refinementAxisRules rawAxisRefinementSignature
      proofRelevantAxisRefinementComputation 15 where
  context := budgetIncompleteEstablishedIotaContext
  left := budgetIncompleteEstablishedIotaLeft
  right := budgetIncompleteEstablishedIotaRight
  type := budgetIncompleteEstablishedIotaType
  receipt := budgetIncompleteEstablishedIotaReceipt

def budgetIncompleteRefutedIotaContextBefore : Tower.Ctx 14 :=
  .snoc fixedAxisIotaContextJ
    (.app (signatureFrontier (.var 12)) (.var 0))

def budgetIncompleteRefutedIotaContext : Tower.Ctx 15 :=
  .snoc budgetIncompleteRefutedIotaContextBefore
    (.app (signatureObstruction (.var 13)) (.var 1))

def budgetIncompleteRefutedIotaBefore : Tower.Tm 15 :=
  incompleteApp (.var 14) (.var 2) (.var 1)

def budgetIncompleteRefutedIotaAfter : Tower.Tm 15 :=
  refutedApp (.var 14) (.var 2) (.var 0)

def budgetIncompleteRefutedIotaRefinement : Tower.Tm 15 :=
  budgetIncompleteRefutedRefinementApp (.var 14) (.var 2)
    (.var 1) (.var 0)

def budgetIncompleteRefutedIotaLeft : Tower.Tm 15 :=
  axisRefinementEliminateApp (.var 14) (.var 13)
    axisRefinementBranchesAfterThree refinementAxisBudgetTm (.var 2)
    budgetIncompleteRefutedIotaBefore budgetIncompleteRefutedIotaAfter
    budgetIncompleteRefutedIotaRefinement

def budgetIncompleteRefutedIotaRight : Tower.Tm 15 :=
  applyArgs (.var 7) [(.var 2), (.var 1), (.var 0)]

def budgetIncompleteRefutedIotaType : Tower.Tm 15 :=
  axisRefinementMotiveApp (.var 13) refinementAxisBudgetTm (.var 2)
    budgetIncompleteRefutedIotaBefore budgetIncompleteRefutedIotaAfter
    budgetIncompleteRefutedIotaRefinement

set_option maxHeartbeats 1000000 in
def budgetIncompleteRefutedIotaReceipt :
    AxisRefinementTypedIotaReceipt budgetIncompleteRefutedIotaContext
      budgetIncompleteRefutedIotaLeft budgetIncompleteRefutedIotaRight
      budgetIncompleteRefutedIotaType where
  sourceTyping := by
    have afterJudgmentBinder :=
      axisRefinementEliminateAtParameters_hasType.weaken
        (extension := signatureJudgment (.var 11))
    have afterBeforeBinder := afterJudgmentBinder.weaken
      (extension := .app (signatureFrontier (.var 12)) (.var 0))
    have weakened := afterBeforeBinder.weaken
      (extension := .app (signatureObstruction (.var 13)) (.var 1))
    have judgmentTyping :
        AxisRefinementHasType budgetIncompleteRefutedIotaContext (.var 2)
          (signatureJudgment (.var 14)) := by
      exact Presentation.HasType.var 2
    have frontierTyping :
        AxisRefinementHasType budgetIncompleteRefutedIotaContext (.var 1)
          (.app (signatureFrontier (.var 14)) (.var 2)) := by
      exact Presentation.HasType.var 1
    have obstructionTyping :
        AxisRefinementHasType budgetIncompleteRefutedIotaContext (.var 0)
          (.app (signatureObstruction (.var 14)) (.var 2)) := by
      exact Presentation.HasType.var 0
    have beforeTyping := incompleteApp_hasAxisRefinementType
      (Presentation.HasType.var 14) judgmentTyping frontierTyping
    have afterTyping := refutedApp_hasAxisRefinementType
      (Presentation.HasType.var 14) judgmentTyping obstructionTyping
    have refinementTyping := budgetIncompleteRefutedRefinementApp_hasType
      (Presentation.HasType.var 14) judgmentTyping frontierTyping
      obstructionTyping
    have afterAxis := Presentation.HasType.appElim weakened
      refinementAxisBudgetTm_hasAxisRefinementType
    have afterJudgment := Presentation.HasType.appElim afterAxis
      judgmentTyping
    have afterBefore := Presentation.HasType.appElim afterJudgment
      beforeTyping
    have afterAfter := Presentation.HasType.appElim afterBefore afterTyping
    have source := Presentation.HasType.appElim afterAfter refinementTyping
    convert source using 1
    all_goals rfl
  targetTyping := by
    have afterJudgment := Presentation.HasType.appElim
      (Presentation.HasType.var (R := axisRefinementRules)
        (Γ := budgetIncompleteRefutedIotaContext) (7 : Fin 15))
      (Presentation.HasType.var 2)
    have afterFrontier := Presentation.HasType.appElim afterJudgment
      (Presentation.HasType.var 1)
    have target := Presentation.HasType.appElim afterFrontier
      (Presentation.HasType.var 0)
    convert target using 1
    all_goals rfl
  evidence := by
    change AxisRefinementIotaEvidence 15 budgetIncompleteRefutedIotaLeft
      budgetIncompleteRefutedIotaRight
    unfold budgetIncompleteRefutedIotaLeft
      budgetIncompleteRefutedIotaRight budgetIncompleteRefutedIotaBefore
      budgetIncompleteRefutedIotaAfter
      budgetIncompleteRefutedIotaRefinement
    exact AxisRefinementIotaEvidence.budgetIncompleteRefuted
      (.var 14) (.var 13) axisRefinementBranchesAfterThree
      (.var 2) (.var 1) (.var 0)

def budgetIncompleteRefutedIotaSchema :
    IotaSchema refinementAxisRules rawAxisRefinementSignature
      proofRelevantAxisRefinementComputation 15 where
  context := budgetIncompleteRefutedIotaContext
  left := budgetIncompleteRefutedIotaLeft
  right := budgetIncompleteRefutedIotaRight
  type := budgetIncompleteRefutedIotaType
  receipt := budgetIncompleteRefutedIotaReceipt

def authorityOutsideIotaContextBefore : Tower.Ctx 14 :=
  .snoc fixedAxisIotaContextJ
    (.app (signatureBoundary (.var 12)) (.var 0))

def authorityOutsideIotaContext : Tower.Ctx 15 :=
  .snoc authorityOutsideIotaContextBefore
    (.app (signatureBoundary (.var 13)) (.var 1))

def authorityOutsideIotaBefore : Tower.Tm 15 :=
  outsideFragmentApp (.var 14) (.var 2) (.var 1)

def authorityOutsideIotaAfter : Tower.Tm 15 :=
  outsideFragmentApp (.var 14) (.var 2) (.var 0)

def authorityOutsideIotaRefinement : Tower.Tm 15 :=
  authorityOutsideRefinementApp (.var 14) (.var 2) (.var 1) (.var 0)

def authorityOutsideIotaLeft : Tower.Tm 15 :=
  axisRefinementEliminateApp (.var 14) (.var 13)
    axisRefinementBranchesAfterThree refinementAxisAuthorityTm (.var 2)
    authorityOutsideIotaBefore authorityOutsideIotaAfter
    authorityOutsideIotaRefinement

def authorityOutsideIotaRight : Tower.Tm 15 :=
  applyArgs (.var 6) [(.var 2), (.var 1), (.var 0)]

def authorityOutsideIotaType : Tower.Tm 15 :=
  axisRefinementMotiveApp (.var 13) refinementAxisAuthorityTm (.var 2)
    authorityOutsideIotaBefore authorityOutsideIotaAfter
    authorityOutsideIotaRefinement

set_option maxHeartbeats 1000000 in
def authorityOutsideIotaReceipt :
    AxisRefinementTypedIotaReceipt authorityOutsideIotaContext
      authorityOutsideIotaLeft authorityOutsideIotaRight
      authorityOutsideIotaType where
  sourceTyping := by
    have afterJudgmentBinder :=
      axisRefinementEliminateAtParameters_hasType.weaken
        (extension := signatureJudgment (.var 11))
    have afterBeforeBinder := afterJudgmentBinder.weaken
      (extension := .app (signatureBoundary (.var 12)) (.var 0))
    have weakened := afterBeforeBinder.weaken
      (extension := .app (signatureBoundary (.var 13)) (.var 1))
    have judgmentTyping :
        AxisRefinementHasType authorityOutsideIotaContext (.var 2)
          (signatureJudgment (.var 14)) := by
      exact Presentation.HasType.var 2
    have beforeReasonTyping :
        AxisRefinementHasType authorityOutsideIotaContext (.var 1)
          (.app (signatureBoundary (.var 14)) (.var 2)) := by
      exact Presentation.HasType.var 1
    have afterReasonTyping :
        AxisRefinementHasType authorityOutsideIotaContext (.var 0)
          (.app (signatureBoundary (.var 14)) (.var 2)) := by
      exact Presentation.HasType.var 0
    have beforeTyping := outsideFragmentApp_hasAxisRefinementType
      (Presentation.HasType.var 14) judgmentTyping beforeReasonTyping
    have afterTyping := outsideFragmentApp_hasAxisRefinementType
      (Presentation.HasType.var 14) judgmentTyping afterReasonTyping
    have refinementTyping := authorityOutsideRefinementApp_hasType
      (Presentation.HasType.var 14) judgmentTyping beforeReasonTyping
      afterReasonTyping
    have afterAxis := Presentation.HasType.appElim weakened
      refinementAxisAuthorityTm_hasAxisRefinementType
    have afterJudgment := Presentation.HasType.appElim afterAxis
      judgmentTyping
    have afterBefore := Presentation.HasType.appElim afterJudgment
      beforeTyping
    have afterAfter := Presentation.HasType.appElim afterBefore afterTyping
    have source := Presentation.HasType.appElim afterAfter refinementTyping
    convert source using 1
    all_goals rfl
  targetTyping := by
    have afterJudgment := Presentation.HasType.appElim
      (Presentation.HasType.var (R := axisRefinementRules)
        (Γ := authorityOutsideIotaContext) (6 : Fin 15))
      (Presentation.HasType.var 2)
    have afterBefore := Presentation.HasType.appElim afterJudgment
      (Presentation.HasType.var 1)
    have target := Presentation.HasType.appElim afterBefore
      (Presentation.HasType.var 0)
    convert target using 1
    all_goals rfl
  evidence := by
    change AxisRefinementIotaEvidence 15 authorityOutsideIotaLeft
      authorityOutsideIotaRight
    unfold authorityOutsideIotaLeft authorityOutsideIotaRight
      authorityOutsideIotaBefore authorityOutsideIotaAfter
      authorityOutsideIotaRefinement
    exact AxisRefinementIotaEvidence.authorityOutside
      (.var 14) (.var 13) axisRefinementBranchesAfterThree
      (.var 2) (.var 1) (.var 0)

def authorityOutsideIotaSchema :
    IotaSchema refinementAxisRules rawAxisRefinementSignature
      proofRelevantAxisRefinementComputation 15 where
  context := authorityOutsideIotaContext
  left := authorityOutsideIotaLeft
  right := authorityOutsideIotaRight
  type := authorityOutsideIotaType
  receipt := authorityOutsideIotaReceipt

def authorityOutsideEstablishedIotaContextBefore : Tower.Ctx 14 :=
  .snoc fixedAxisIotaContextJ
    (.app (signatureBoundary (.var 12)) (.var 0))

def authorityOutsideEstablishedIotaContext : Tower.Ctx 15 :=
  .snoc authorityOutsideEstablishedIotaContextBefore
    (.app (signatureEvidence (.var 13)) (.var 1))

def authorityOutsideEstablishedIotaBefore : Tower.Tm 15 :=
  outsideFragmentApp (.var 14) (.var 2) (.var 1)

def authorityOutsideEstablishedIotaAfter : Tower.Tm 15 :=
  establishedApp (.var 14) (.var 2) (.var 0)

def authorityOutsideEstablishedIotaRefinement : Tower.Tm 15 :=
  authorityOutsideEstablishedRefinementApp (.var 14) (.var 2)
    (.var 1) (.var 0)

def authorityOutsideEstablishedIotaLeft : Tower.Tm 15 :=
  axisRefinementEliminateApp (.var 14) (.var 13)
    axisRefinementBranchesAfterThree refinementAxisAuthorityTm (.var 2)
    authorityOutsideEstablishedIotaBefore
    authorityOutsideEstablishedIotaAfter
    authorityOutsideEstablishedIotaRefinement

def authorityOutsideEstablishedIotaRight : Tower.Tm 15 :=
  applyArgs (.var 5) [(.var 2), (.var 1), (.var 0)]

def authorityOutsideEstablishedIotaType : Tower.Tm 15 :=
  axisRefinementMotiveApp (.var 13) refinementAxisAuthorityTm (.var 2)
    authorityOutsideEstablishedIotaBefore
    authorityOutsideEstablishedIotaAfter
    authorityOutsideEstablishedIotaRefinement

set_option maxHeartbeats 1000000 in
def authorityOutsideEstablishedIotaReceipt :
    AxisRefinementTypedIotaReceipt authorityOutsideEstablishedIotaContext
      authorityOutsideEstablishedIotaLeft
      authorityOutsideEstablishedIotaRight
      authorityOutsideEstablishedIotaType where
  sourceTyping := by
    have afterJudgmentBinder :=
      axisRefinementEliminateAtParameters_hasType.weaken
        (extension := signatureJudgment (.var 11))
    have afterBeforeBinder := afterJudgmentBinder.weaken
      (extension := .app (signatureBoundary (.var 12)) (.var 0))
    have weakened := afterBeforeBinder.weaken
      (extension := .app (signatureEvidence (.var 13)) (.var 1))
    have judgmentTyping :
        AxisRefinementHasType authorityOutsideEstablishedIotaContext
          (.var 2) (signatureJudgment (.var 14)) := by
      exact Presentation.HasType.var 2
    have reasonTyping :
        AxisRefinementHasType authorityOutsideEstablishedIotaContext
          (.var 1) (.app (signatureBoundary (.var 14)) (.var 2)) := by
      exact Presentation.HasType.var 1
    have evidenceTyping :
        AxisRefinementHasType authorityOutsideEstablishedIotaContext
          (.var 0) (.app (signatureEvidence (.var 14)) (.var 2)) := by
      exact Presentation.HasType.var 0
    have beforeTyping := outsideFragmentApp_hasAxisRefinementType
      (Presentation.HasType.var 14) judgmentTyping reasonTyping
    have afterTyping := establishedApp_hasAxisRefinementType
      (Presentation.HasType.var 14) judgmentTyping evidenceTyping
    have refinementTyping :=
      authorityOutsideEstablishedRefinementApp_hasType
        (Presentation.HasType.var 14) judgmentTyping reasonTyping
        evidenceTyping
    have afterAxis := Presentation.HasType.appElim weakened
      refinementAxisAuthorityTm_hasAxisRefinementType
    have afterJudgment := Presentation.HasType.appElim afterAxis
      judgmentTyping
    have afterBefore := Presentation.HasType.appElim afterJudgment
      beforeTyping
    have afterAfter := Presentation.HasType.appElim afterBefore afterTyping
    have source := Presentation.HasType.appElim afterAfter refinementTyping
    convert source using 1
    all_goals rfl
  targetTyping := by
    have afterJudgment := Presentation.HasType.appElim
      (Presentation.HasType.var (R := axisRefinementRules)
        (Γ := authorityOutsideEstablishedIotaContext) (5 : Fin 15))
      (Presentation.HasType.var 2)
    have afterReason := Presentation.HasType.appElim afterJudgment
      (Presentation.HasType.var 1)
    have target := Presentation.HasType.appElim afterReason
      (Presentation.HasType.var 0)
    convert target using 1
    all_goals rfl
  evidence := by
    change AxisRefinementIotaEvidence 15
      authorityOutsideEstablishedIotaLeft
      authorityOutsideEstablishedIotaRight
    unfold authorityOutsideEstablishedIotaLeft
      authorityOutsideEstablishedIotaRight
      authorityOutsideEstablishedIotaBefore
      authorityOutsideEstablishedIotaAfter
      authorityOutsideEstablishedIotaRefinement
    exact AxisRefinementIotaEvidence.authorityOutsideEstablished
      (.var 14) (.var 13) axisRefinementBranchesAfterThree
      (.var 2) (.var 1) (.var 0)

def authorityOutsideEstablishedIotaSchema :
    IotaSchema refinementAxisRules rawAxisRefinementSignature
      proofRelevantAxisRefinementComputation 15 where
  context := authorityOutsideEstablishedIotaContext
  left := authorityOutsideEstablishedIotaLeft
  right := authorityOutsideEstablishedIotaRight
  type := authorityOutsideEstablishedIotaType
  receipt := authorityOutsideEstablishedIotaReceipt

def authorityOutsideRefutedIotaContextBefore : Tower.Ctx 14 :=
  .snoc fixedAxisIotaContextJ
    (.app (signatureBoundary (.var 12)) (.var 0))

def authorityOutsideRefutedIotaContext : Tower.Ctx 15 :=
  .snoc authorityOutsideRefutedIotaContextBefore
    (.app (signatureObstruction (.var 13)) (.var 1))

def authorityOutsideRefutedIotaBefore : Tower.Tm 15 :=
  outsideFragmentApp (.var 14) (.var 2) (.var 1)

def authorityOutsideRefutedIotaAfter : Tower.Tm 15 :=
  refutedApp (.var 14) (.var 2) (.var 0)

def authorityOutsideRefutedIotaRefinement : Tower.Tm 15 :=
  authorityOutsideRefutedRefinementApp (.var 14) (.var 2)
    (.var 1) (.var 0)

def authorityOutsideRefutedIotaLeft : Tower.Tm 15 :=
  axisRefinementEliminateApp (.var 14) (.var 13)
    axisRefinementBranchesAfterThree refinementAxisAuthorityTm (.var 2)
    authorityOutsideRefutedIotaBefore authorityOutsideRefutedIotaAfter
    authorityOutsideRefutedIotaRefinement

def authorityOutsideRefutedIotaRight : Tower.Tm 15 :=
  applyArgs (.var 4) [(.var 2), (.var 1), (.var 0)]

def authorityOutsideRefutedIotaType : Tower.Tm 15 :=
  axisRefinementMotiveApp (.var 13) refinementAxisAuthorityTm (.var 2)
    authorityOutsideRefutedIotaBefore authorityOutsideRefutedIotaAfter
    authorityOutsideRefutedIotaRefinement

set_option maxHeartbeats 1000000 in
def authorityOutsideRefutedIotaReceipt :
    AxisRefinementTypedIotaReceipt authorityOutsideRefutedIotaContext
      authorityOutsideRefutedIotaLeft authorityOutsideRefutedIotaRight
      authorityOutsideRefutedIotaType where
  sourceTyping := by
    have afterJudgmentBinder :=
      axisRefinementEliminateAtParameters_hasType.weaken
        (extension := signatureJudgment (.var 11))
    have afterBeforeBinder := afterJudgmentBinder.weaken
      (extension := .app (signatureBoundary (.var 12)) (.var 0))
    have weakened := afterBeforeBinder.weaken
      (extension := .app (signatureObstruction (.var 13)) (.var 1))
    have judgmentTyping :
        AxisRefinementHasType authorityOutsideRefutedIotaContext (.var 2)
          (signatureJudgment (.var 14)) := by
      exact Presentation.HasType.var 2
    have reasonTyping :
        AxisRefinementHasType authorityOutsideRefutedIotaContext (.var 1)
          (.app (signatureBoundary (.var 14)) (.var 2)) := by
      exact Presentation.HasType.var 1
    have obstructionTyping :
        AxisRefinementHasType authorityOutsideRefutedIotaContext (.var 0)
          (.app (signatureObstruction (.var 14)) (.var 2)) := by
      exact Presentation.HasType.var 0
    have beforeTyping := outsideFragmentApp_hasAxisRefinementType
      (Presentation.HasType.var 14) judgmentTyping reasonTyping
    have afterTyping := refutedApp_hasAxisRefinementType
      (Presentation.HasType.var 14) judgmentTyping obstructionTyping
    have refinementTyping :=
      authorityOutsideRefutedRefinementApp_hasType
        (Presentation.HasType.var 14) judgmentTyping reasonTyping
        obstructionTyping
    have afterAxis := Presentation.HasType.appElim weakened
      refinementAxisAuthorityTm_hasAxisRefinementType
    have afterJudgment := Presentation.HasType.appElim afterAxis
      judgmentTyping
    have afterBefore := Presentation.HasType.appElim afterJudgment
      beforeTyping
    have afterAfter := Presentation.HasType.appElim afterBefore afterTyping
    have source := Presentation.HasType.appElim afterAfter refinementTyping
    convert source using 1
    all_goals rfl
  targetTyping := by
    have afterJudgment := Presentation.HasType.appElim
      (Presentation.HasType.var (R := axisRefinementRules)
        (Γ := authorityOutsideRefutedIotaContext) (4 : Fin 15))
      (Presentation.HasType.var 2)
    have afterReason := Presentation.HasType.appElim afterJudgment
      (Presentation.HasType.var 1)
    have target := Presentation.HasType.appElim afterReason
      (Presentation.HasType.var 0)
    convert target using 1
    all_goals rfl
  evidence := by
    change AxisRefinementIotaEvidence 15 authorityOutsideRefutedIotaLeft
      authorityOutsideRefutedIotaRight
    unfold authorityOutsideRefutedIotaLeft
      authorityOutsideRefutedIotaRight authorityOutsideRefutedIotaBefore
      authorityOutsideRefutedIotaAfter
      authorityOutsideRefutedIotaRefinement
    exact AxisRefinementIotaEvidence.authorityOutsideRefuted
      (.var 14) (.var 13) axisRefinementBranchesAfterThree
      (.var 2) (.var 1) (.var 0)

def authorityOutsideRefutedIotaSchema :
    IotaSchema refinementAxisRules rawAxisRefinementSignature
      proofRelevantAxisRefinementComputation 15 where
  context := authorityOutsideRefutedIotaContext
  left := authorityOutsideRefutedIotaLeft
  right := authorityOutsideRefutedIotaRight
  type := authorityOutsideRefutedIotaType
  receipt := authorityOutsideRefutedIotaReceipt

def authorityOutsideIncompleteIotaContextBefore : Tower.Ctx 14 :=
  .snoc fixedAxisIotaContextJ
    (.app (signatureBoundary (.var 12)) (.var 0))

def authorityOutsideIncompleteIotaContext : Tower.Ctx 15 :=
  .snoc authorityOutsideIncompleteIotaContextBefore
    (.app (signatureFrontier (.var 13)) (.var 1))

def authorityOutsideIncompleteIotaBefore : Tower.Tm 15 :=
  outsideFragmentApp (.var 14) (.var 2) (.var 1)

def authorityOutsideIncompleteIotaAfter : Tower.Tm 15 :=
  incompleteApp (.var 14) (.var 2) (.var 0)

def authorityOutsideIncompleteIotaRefinement : Tower.Tm 15 :=
  authorityOutsideIncompleteRefinementApp (.var 14) (.var 2)
    (.var 1) (.var 0)

def authorityOutsideIncompleteIotaLeft : Tower.Tm 15 :=
  axisRefinementEliminateApp (.var 14) (.var 13)
    axisRefinementBranchesAfterThree refinementAxisAuthorityTm (.var 2)
    authorityOutsideIncompleteIotaBefore
    authorityOutsideIncompleteIotaAfter
    authorityOutsideIncompleteIotaRefinement

def authorityOutsideIncompleteIotaRight : Tower.Tm 15 :=
  applyArgs (.var 3) [(.var 2), (.var 1), (.var 0)]

def authorityOutsideIncompleteIotaType : Tower.Tm 15 :=
  axisRefinementMotiveApp (.var 13) refinementAxisAuthorityTm (.var 2)
    authorityOutsideIncompleteIotaBefore
    authorityOutsideIncompleteIotaAfter
    authorityOutsideIncompleteIotaRefinement

set_option maxHeartbeats 1000000 in
def authorityOutsideIncompleteIotaReceipt :
    AxisRefinementTypedIotaReceipt authorityOutsideIncompleteIotaContext
      authorityOutsideIncompleteIotaLeft
      authorityOutsideIncompleteIotaRight
      authorityOutsideIncompleteIotaType where
  sourceTyping := by
    have afterJudgmentBinder :=
      axisRefinementEliminateAtParameters_hasType.weaken
        (extension := signatureJudgment (.var 11))
    have afterBeforeBinder := afterJudgmentBinder.weaken
      (extension := .app (signatureBoundary (.var 12)) (.var 0))
    have weakened := afterBeforeBinder.weaken
      (extension := .app (signatureFrontier (.var 13)) (.var 1))
    have judgmentTyping :
        AxisRefinementHasType authorityOutsideIncompleteIotaContext
          (.var 2) (signatureJudgment (.var 14)) := by
      exact Presentation.HasType.var 2
    have reasonTyping :
        AxisRefinementHasType authorityOutsideIncompleteIotaContext
          (.var 1) (.app (signatureBoundary (.var 14)) (.var 2)) := by
      exact Presentation.HasType.var 1
    have frontierTyping :
        AxisRefinementHasType authorityOutsideIncompleteIotaContext
          (.var 0) (.app (signatureFrontier (.var 14)) (.var 2)) := by
      exact Presentation.HasType.var 0
    have beforeTyping := outsideFragmentApp_hasAxisRefinementType
      (Presentation.HasType.var 14) judgmentTyping reasonTyping
    have afterTyping := incompleteApp_hasAxisRefinementType
      (Presentation.HasType.var 14) judgmentTyping frontierTyping
    have refinementTyping :=
      authorityOutsideIncompleteRefinementApp_hasType
        (Presentation.HasType.var 14) judgmentTyping reasonTyping
        frontierTyping
    have afterAxis := Presentation.HasType.appElim weakened
      refinementAxisAuthorityTm_hasAxisRefinementType
    have afterJudgment := Presentation.HasType.appElim afterAxis
      judgmentTyping
    have afterBefore := Presentation.HasType.appElim afterJudgment
      beforeTyping
    have afterAfter := Presentation.HasType.appElim afterBefore afterTyping
    have source := Presentation.HasType.appElim afterAfter refinementTyping
    convert source using 1
    all_goals rfl
  targetTyping := by
    have afterJudgment := Presentation.HasType.appElim
      (Presentation.HasType.var (R := axisRefinementRules)
        (Γ := authorityOutsideIncompleteIotaContext) (3 : Fin 15))
      (Presentation.HasType.var 2)
    have afterReason := Presentation.HasType.appElim afterJudgment
      (Presentation.HasType.var 1)
    have target := Presentation.HasType.appElim afterReason
      (Presentation.HasType.var 0)
    convert target using 1
    all_goals rfl
  evidence := by
    change AxisRefinementIotaEvidence 15
      authorityOutsideIncompleteIotaLeft
      authorityOutsideIncompleteIotaRight
    unfold authorityOutsideIncompleteIotaLeft
      authorityOutsideIncompleteIotaRight
      authorityOutsideIncompleteIotaBefore
      authorityOutsideIncompleteIotaAfter
      authorityOutsideIncompleteIotaRefinement
    exact AxisRefinementIotaEvidence.authorityOutsideIncomplete
      (.var 14) (.var 13) axisRefinementBranchesAfterThree
      (.var 2) (.var 1) (.var 0)

def authorityOutsideIncompleteIotaSchema :
    IotaSchema refinementAxisRules rawAxisRefinementSignature
      proofRelevantAxisRefinementComputation 15 where
  context := authorityOutsideIncompleteIotaContext
  left := authorityOutsideIncompleteIotaLeft
  right := authorityOutsideIncompleteIotaRight
  type := authorityOutsideIncompleteIotaType
  receipt := authorityOutsideIncompleteIotaReceipt

def axisRefinementEliminateAtParameters_applicationHead :
    ApplicationHead axisRefinementEliminateName
      axisRefinementEliminateAtParameters := by
  unfold axisRefinementEliminateAtParameters
    axisRefinementEliminateAtBranches
  repeat' apply ApplicationHead.app
  exact ApplicationHead.const

noncomputable def axisRefinementEliminateAfterFour_applicationHead :
    ApplicationHead axisRefinementEliminateName
      (Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk
            (Presentation.rename wk axisRefinementEliminateAtParameters)))) :=
  ((((axisRefinementEliminateAtParameters_applicationHead.rename wk).rename
    wk).rename wk).rename wk)

noncomputable def axisRefinementEliminateAfterThree_applicationHead :
    ApplicationHead axisRefinementEliminateName
      (Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk axisRefinementEliminateAtParameters))) :=
  (((axisRefinementEliminateAtParameters_applicationHead.rename wk).rename
    wk).rename wk)

noncomputable def axisRefinementEliminateAfterTwo_applicationHead :
    ApplicationHead axisRefinementEliminateName
      (Presentation.rename wk
        (Presentation.rename wk axisRefinementEliminateAtParameters)) :=
  ((axisRefinementEliminateAtParameters_applicationHead.rename wk).rename wk)

def axisNamedBinaryConstructorApp_constantOccurrence
    (constructor : DeclName)
    (signature axis judgment before after : Tower.Tm n) :
    ConstantOccurrence constructor
      (axisNamedBinaryConstructorApp constructor signature axis judgment
        before after) :=
  .appFunction
    (.appFunction
      (.appFunction (.appFunction (.appFunction .here))))

def axisNamedFixedBinaryConstructorApp_constantOccurrence
    (constructor : DeclName)
    (signature judgment before after : Tower.Tm n) :
    ConstantOccurrence constructor
      (axisNamedFixedBinaryConstructorApp constructor signature judgment
        before after) :=
  .appFunction (.appFunction (.appFunction (.appFunction .here)))

def axisNamedFixedUnaryConstructorApp_constantOccurrence
    (constructor : DeclName)
    (signature judgment witness : Tower.Tm n) :
    ConstantOccurrence constructor
      (axisNamedFixedUnaryConstructorApp constructor signature judgment
        witness) :=
  .appFunction (.appFunction (.appFunction .here))

noncomputable def axisEstablishedIotaClause :
    IotaClause refinementAxisRules rawAxisRefinementSignature
      proofRelevantAxisRefinementComputation
      (axisRefinementConstructors.map ConstructorSpec.name)
      axisRefinementEliminatorSpec.name where
  constructorName := axisEstablishedName
  constructorDeclared := by
    simp [axisRefinementConstructors, axisEstablishedConstructorSpec,
      axisRefutedConstructorSpec, axisIncompleteConstructorSpec,
      budgetOutsideRefinementConstructorSpec,
      budgetIncompleteEstablishedRefinementConstructorSpec,
      budgetIncompleteRefutedRefinementConstructorSpec,
      authorityOutsideRefinementConstructorSpec,
      authorityOutsideEstablishedRefinementConstructorSpec,
      authorityOutsideRefutedRefinementConstructorSpec,
      authorityOutsideIncompleteRefinementConstructorSpec]
  arity := 16
  schema := axisEstablishedIotaSchema
  eliminatorHead :=
    .app (.app (.app (.app (.app
      axisRefinementEliminateAfterFour_applicationHead))))
  constructorOccurrence := by
    apply ConstantOccurrence.appArgument
    simpa [axisEstablishedIotaRefinement, axisEstablishedApp,
      axisNamedBinaryConstructorApp] using
      axisNamedBinaryConstructorApp_constantOccurrence axisEstablishedName
        (.var 15) (.var 3) (.var 2) (.var 1) (.var 0)

noncomputable def axisRefutedIotaClause :
    IotaClause refinementAxisRules rawAxisRefinementSignature
      proofRelevantAxisRefinementComputation
      (axisRefinementConstructors.map ConstructorSpec.name)
      axisRefinementEliminatorSpec.name where
  constructorName := axisRefutedName
  constructorDeclared := by
    simp [axisRefinementConstructors, axisEstablishedConstructorSpec,
      axisRefutedConstructorSpec, axisIncompleteConstructorSpec,
      budgetOutsideRefinementConstructorSpec,
      budgetIncompleteEstablishedRefinementConstructorSpec,
      budgetIncompleteRefutedRefinementConstructorSpec,
      authorityOutsideRefinementConstructorSpec,
      authorityOutsideEstablishedRefinementConstructorSpec,
      authorityOutsideRefutedRefinementConstructorSpec,
      authorityOutsideIncompleteRefinementConstructorSpec]
  arity := 16
  schema := axisRefutedIotaSchema
  eliminatorHead :=
    .app (.app (.app (.app (.app
      axisRefinementEliminateAfterFour_applicationHead))))
  constructorOccurrence := by
    apply ConstantOccurrence.appArgument
    simpa [axisRefutedIotaRefinement, axisRefutedApp,
      axisNamedBinaryConstructorApp] using
      axisNamedBinaryConstructorApp_constantOccurrence axisRefutedName
        (.var 15) (.var 3) (.var 2) (.var 1) (.var 0)

noncomputable def axisIncompleteIotaClause :
    IotaClause refinementAxisRules rawAxisRefinementSignature
      proofRelevantAxisRefinementComputation
      (axisRefinementConstructors.map ConstructorSpec.name)
      axisRefinementEliminatorSpec.name where
  constructorName := axisIncompleteName
  constructorDeclared := by
    simp [axisRefinementConstructors, axisEstablishedConstructorSpec,
      axisRefutedConstructorSpec, axisIncompleteConstructorSpec,
      budgetOutsideRefinementConstructorSpec,
      budgetIncompleteEstablishedRefinementConstructorSpec,
      budgetIncompleteRefutedRefinementConstructorSpec,
      authorityOutsideRefinementConstructorSpec,
      authorityOutsideEstablishedRefinementConstructorSpec,
      authorityOutsideRefutedRefinementConstructorSpec,
      authorityOutsideIncompleteRefinementConstructorSpec]
  arity := 16
  schema := axisIncompleteIotaSchema
  eliminatorHead :=
    .app (.app (.app (.app (.app
      axisRefinementEliminateAfterFour_applicationHead))))
  constructorOccurrence := by
    apply ConstantOccurrence.appArgument
    simpa [axisIncompleteIotaRefinement, axisIncompleteApp,
      axisNamedBinaryConstructorApp] using
      axisNamedBinaryConstructorApp_constantOccurrence axisIncompleteName
        (.var 15) (.var 3) (.var 2) (.var 1) (.var 0)

noncomputable def budgetOutsideIotaClause :
    IotaClause refinementAxisRules rawAxisRefinementSignature
      proofRelevantAxisRefinementComputation
      (axisRefinementConstructors.map ConstructorSpec.name)
      axisRefinementEliminatorSpec.name where
  constructorName := budgetOutsideRefinementName
  constructorDeclared := by
    simp [axisRefinementConstructors, axisEstablishedConstructorSpec,
      axisRefutedConstructorSpec, axisIncompleteConstructorSpec,
      budgetOutsideRefinementConstructorSpec,
      budgetIncompleteEstablishedRefinementConstructorSpec,
      budgetIncompleteRefutedRefinementConstructorSpec,
      authorityOutsideRefinementConstructorSpec,
      authorityOutsideEstablishedRefinementConstructorSpec,
      authorityOutsideRefutedRefinementConstructorSpec,
      authorityOutsideIncompleteRefinementConstructorSpec]
  arity := 14
  schema := budgetOutsideIotaSchema
  eliminatorHead :=
    .app (.app (.app (.app (.app
      axisRefinementEliminateAfterTwo_applicationHead))))
  constructorOccurrence := by
    apply ConstantOccurrence.appArgument
    simpa [budgetOutsideIotaRefinement, budgetOutsideRefinementApp,
      axisNamedFixedUnaryConstructorApp] using
      axisNamedFixedUnaryConstructorApp_constantOccurrence
        budgetOutsideRefinementName (.var 13) (.var 1) (.var 0)

noncomputable def budgetIncompleteEstablishedIotaClause :
    IotaClause refinementAxisRules rawAxisRefinementSignature
      proofRelevantAxisRefinementComputation
      (axisRefinementConstructors.map ConstructorSpec.name)
      axisRefinementEliminatorSpec.name where
  constructorName := budgetIncompleteEstablishedRefinementName
  constructorDeclared := by
    simp [axisRefinementConstructors, axisEstablishedConstructorSpec,
      axisRefutedConstructorSpec, axisIncompleteConstructorSpec,
      budgetOutsideRefinementConstructorSpec,
      budgetIncompleteEstablishedRefinementConstructorSpec,
      budgetIncompleteRefutedRefinementConstructorSpec,
      authorityOutsideRefinementConstructorSpec,
      authorityOutsideEstablishedRefinementConstructorSpec,
      authorityOutsideRefutedRefinementConstructorSpec,
      authorityOutsideIncompleteRefinementConstructorSpec]
  arity := 15
  schema := budgetIncompleteEstablishedIotaSchema
  eliminatorHead :=
    .app (.app (.app (.app (.app
      axisRefinementEliminateAfterThree_applicationHead))))
  constructorOccurrence := by
    apply ConstantOccurrence.appArgument
    simpa [budgetIncompleteEstablishedIotaRefinement,
      budgetIncompleteEstablishedRefinementApp,
      axisNamedFixedBinaryConstructorApp] using
      axisNamedFixedBinaryConstructorApp_constantOccurrence
        budgetIncompleteEstablishedRefinementName
        (.var 14) (.var 2) (.var 1) (.var 0)

noncomputable def budgetIncompleteRefutedIotaClause :
    IotaClause refinementAxisRules rawAxisRefinementSignature
      proofRelevantAxisRefinementComputation
      (axisRefinementConstructors.map ConstructorSpec.name)
      axisRefinementEliminatorSpec.name where
  constructorName := budgetIncompleteRefutedRefinementName
  constructorDeclared := by
    simp [axisRefinementConstructors, axisEstablishedConstructorSpec,
      axisRefutedConstructorSpec, axisIncompleteConstructorSpec,
      budgetOutsideRefinementConstructorSpec,
      budgetIncompleteEstablishedRefinementConstructorSpec,
      budgetIncompleteRefutedRefinementConstructorSpec,
      authorityOutsideRefinementConstructorSpec,
      authorityOutsideEstablishedRefinementConstructorSpec,
      authorityOutsideRefutedRefinementConstructorSpec,
      authorityOutsideIncompleteRefinementConstructorSpec]
  arity := 15
  schema := budgetIncompleteRefutedIotaSchema
  eliminatorHead :=
    .app (.app (.app (.app (.app
      axisRefinementEliminateAfterThree_applicationHead))))
  constructorOccurrence := by
    apply ConstantOccurrence.appArgument
    simpa [budgetIncompleteRefutedIotaRefinement,
      budgetIncompleteRefutedRefinementApp,
      axisNamedFixedBinaryConstructorApp] using
      axisNamedFixedBinaryConstructorApp_constantOccurrence
        budgetIncompleteRefutedRefinementName
        (.var 14) (.var 2) (.var 1) (.var 0)

noncomputable def authorityOutsideIotaClause :
    IotaClause refinementAxisRules rawAxisRefinementSignature
      proofRelevantAxisRefinementComputation
      (axisRefinementConstructors.map ConstructorSpec.name)
      axisRefinementEliminatorSpec.name where
  constructorName := authorityOutsideRefinementName
  constructorDeclared := by
    simp [axisRefinementConstructors, axisEstablishedConstructorSpec,
      axisRefutedConstructorSpec, axisIncompleteConstructorSpec,
      budgetOutsideRefinementConstructorSpec,
      budgetIncompleteEstablishedRefinementConstructorSpec,
      budgetIncompleteRefutedRefinementConstructorSpec,
      authorityOutsideRefinementConstructorSpec,
      authorityOutsideEstablishedRefinementConstructorSpec,
      authorityOutsideRefutedRefinementConstructorSpec,
      authorityOutsideIncompleteRefinementConstructorSpec]
  arity := 15
  schema := authorityOutsideIotaSchema
  eliminatorHead :=
    .app (.app (.app (.app (.app
      axisRefinementEliminateAfterThree_applicationHead))))
  constructorOccurrence := by
    apply ConstantOccurrence.appArgument
    simpa [authorityOutsideIotaRefinement,
      authorityOutsideRefinementApp,
      axisNamedFixedBinaryConstructorApp] using
      axisNamedFixedBinaryConstructorApp_constantOccurrence
        authorityOutsideRefinementName
        (.var 14) (.var 2) (.var 1) (.var 0)

noncomputable def authorityOutsideEstablishedIotaClause :
    IotaClause refinementAxisRules rawAxisRefinementSignature
      proofRelevantAxisRefinementComputation
      (axisRefinementConstructors.map ConstructorSpec.name)
      axisRefinementEliminatorSpec.name where
  constructorName := authorityOutsideEstablishedRefinementName
  constructorDeclared := by
    simp [axisRefinementConstructors, axisEstablishedConstructorSpec,
      axisRefutedConstructorSpec, axisIncompleteConstructorSpec,
      budgetOutsideRefinementConstructorSpec,
      budgetIncompleteEstablishedRefinementConstructorSpec,
      budgetIncompleteRefutedRefinementConstructorSpec,
      authorityOutsideRefinementConstructorSpec,
      authorityOutsideEstablishedRefinementConstructorSpec,
      authorityOutsideRefutedRefinementConstructorSpec,
      authorityOutsideIncompleteRefinementConstructorSpec]
  arity := 15
  schema := authorityOutsideEstablishedIotaSchema
  eliminatorHead :=
    .app (.app (.app (.app (.app
      axisRefinementEliminateAfterThree_applicationHead))))
  constructorOccurrence := by
    apply ConstantOccurrence.appArgument
    simpa [authorityOutsideEstablishedIotaRefinement,
      authorityOutsideEstablishedRefinementApp,
      axisNamedFixedBinaryConstructorApp] using
      axisNamedFixedBinaryConstructorApp_constantOccurrence
        authorityOutsideEstablishedRefinementName
        (.var 14) (.var 2) (.var 1) (.var 0)

noncomputable def authorityOutsideRefutedIotaClause :
    IotaClause refinementAxisRules rawAxisRefinementSignature
      proofRelevantAxisRefinementComputation
      (axisRefinementConstructors.map ConstructorSpec.name)
      axisRefinementEliminatorSpec.name where
  constructorName := authorityOutsideRefutedRefinementName
  constructorDeclared := by
    simp [axisRefinementConstructors, axisEstablishedConstructorSpec,
      axisRefutedConstructorSpec, axisIncompleteConstructorSpec,
      budgetOutsideRefinementConstructorSpec,
      budgetIncompleteEstablishedRefinementConstructorSpec,
      budgetIncompleteRefutedRefinementConstructorSpec,
      authorityOutsideRefinementConstructorSpec,
      authorityOutsideEstablishedRefinementConstructorSpec,
      authorityOutsideRefutedRefinementConstructorSpec,
      authorityOutsideIncompleteRefinementConstructorSpec]
  arity := 15
  schema := authorityOutsideRefutedIotaSchema
  eliminatorHead :=
    .app (.app (.app (.app (.app
      axisRefinementEliminateAfterThree_applicationHead))))
  constructorOccurrence := by
    apply ConstantOccurrence.appArgument
    simpa [authorityOutsideRefutedIotaRefinement,
      authorityOutsideRefutedRefinementApp,
      axisNamedFixedBinaryConstructorApp] using
      axisNamedFixedBinaryConstructorApp_constantOccurrence
        authorityOutsideRefutedRefinementName
        (.var 14) (.var 2) (.var 1) (.var 0)

noncomputable def authorityOutsideIncompleteIotaClause :
    IotaClause refinementAxisRules rawAxisRefinementSignature
      proofRelevantAxisRefinementComputation
      (axisRefinementConstructors.map ConstructorSpec.name)
      axisRefinementEliminatorSpec.name where
  constructorName := authorityOutsideIncompleteRefinementName
  constructorDeclared := by
    simp [axisRefinementConstructors, axisEstablishedConstructorSpec,
      axisRefutedConstructorSpec, axisIncompleteConstructorSpec,
      budgetOutsideRefinementConstructorSpec,
      budgetIncompleteEstablishedRefinementConstructorSpec,
      budgetIncompleteRefutedRefinementConstructorSpec,
      authorityOutsideRefinementConstructorSpec,
      authorityOutsideEstablishedRefinementConstructorSpec,
      authorityOutsideRefutedRefinementConstructorSpec,
      authorityOutsideIncompleteRefinementConstructorSpec]
  arity := 15
  schema := authorityOutsideIncompleteIotaSchema
  eliminatorHead :=
    .app (.app (.app (.app (.app
      axisRefinementEliminateAfterThree_applicationHead))))
  constructorOccurrence := by
    apply ConstantOccurrence.appArgument
    simpa [authorityOutsideIncompleteIotaRefinement,
      authorityOutsideIncompleteRefinementApp,
      axisNamedFixedBinaryConstructorApp] using
      axisNamedFixedBinaryConstructorApp_constantOccurrence
        authorityOutsideIncompleteRefinementName
        (.var 14) (.var 2) (.var 1) (.var 0)

noncomputable def axisRefinementIotaClauses :
    List (IotaClause refinementAxisRules rawAxisRefinementSignature
      proofRelevantAxisRefinementComputation
      (axisRefinementConstructors.map ConstructorSpec.name)
      axisRefinementEliminatorSpec.name) :=
  [axisEstablishedIotaClause, axisRefutedIotaClause,
    axisIncompleteIotaClause, budgetOutsideIotaClause,
    budgetIncompleteEstablishedIotaClause,
    budgetIncompleteRefutedIotaClause, authorityOutsideIotaClause,
    authorityOutsideEstablishedIotaClause,
    authorityOutsideRefutedIotaClause,
    authorityOutsideIncompleteIotaClause]

/-- The proof-relevant refinement family has one uniform signature parameter
and four indices: axis, judgment, source outcome, and target outcome. -/
noncomputable def axisRefinementCandidate : Candidate refinementAxisRules where
  signature := rawAxisRefinementSignature
  formed := rawAxisRefinementSignature_formed
  computation := proofRelevantAxisRefinementComputation
  computationSupport := rfl
  familyName := axisRefinementName
  familyParameterCount := 1
  familyIndexCount := 4
  familyType := axisRefinementType
  familyDeclared := typeOf_axisRefinement
  constructors := axisRefinementConstructors
  constructorNamesNodup := by
    change [axisEstablishedName, axisRefutedName, axisIncompleteName,
      budgetOutsideRefinementName,
      budgetIncompleteEstablishedRefinementName,
      budgetIncompleteRefutedRefinementName,
      authorityOutsideRefinementName,
      authorityOutsideEstablishedRefinementName,
      authorityOutsideRefutedRefinementName,
      authorityOutsideIncompleteRefinementName].Nodup
    decide
  familyNotConstructor := by
    intro constructor membership
    simp only [axisRefinementConstructors, List.mem_cons,
      List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> decide
  eliminator := axisRefinementEliminatorSpec
  eliminatorNotFamily := by decide
  eliminatorNotConstructor := by
    intro constructor membership
    simp only [axisRefinementConstructors, List.mem_cons,
      List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> decide
  iotaClauses := axisRefinementIotaClauses
  constructorsComputed := by
    intro constructorName membership
    simp [axisRefinementConstructors, axisEstablishedConstructorSpec,
      axisRefutedConstructorSpec, axisIncompleteConstructorSpec,
      budgetOutsideRefinementConstructorSpec,
      budgetIncompleteEstablishedRefinementConstructorSpec,
      budgetIncompleteRefutedRefinementConstructorSpec,
      authorityOutsideRefinementConstructorSpec,
      authorityOutsideEstablishedRefinementConstructorSpec,
      authorityOutsideRefutedRefinementConstructorSpec,
      authorityOutsideIncompleteRefinementConstructorSpec] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;>
      simp [axisRefinementIotaClauses, axisEstablishedIotaClause,
        axisRefutedIotaClause, axisIncompleteIotaClause,
        budgetOutsideIotaClause,
        budgetIncompleteEstablishedIotaClause,
        budgetIncompleteRefutedIotaClause, authorityOutsideIotaClause,
        authorityOutsideEstablishedIotaClause,
        authorityOutsideRefutedIotaClause,
        authorityOutsideIncompleteIotaClause]

/-! ## Structural separation controls -/

theorem budgetOutside_and_authorityOutside_names_distinct :
    budgetOutsideRefinementName ≠ authorityOutsideRefinementName := by
  decide

theorem axisRefinement_and_axisCarrier_names_distinct :
    axisRefinementName ≠ refinementAxisName := by
  decide

/-! ## Exact canonical-constructor model

The declaration above gives the intrinsic syntax, typing, elimination, and
computation rules.  The independent family below gives the semantics of its
canonical constructor image.  It deliberately does not assert that every raw
term of `Refines` normalizes to a constructor; that stronger canonicity result
belongs to the later conversion development.
-/

open Mettapedia.TypeTheory.AuthorityTheory

universe u v w x

/-- Canonical evidence generated by the ten native `Refines` constructors.
Its indices expose exactly which transitions each constructor permits. -/
inductive CanonicalAxisRefinement
    {Established : Type u} {Refuted : Type v}
    {Boundary : Type w} {Incomplete : Type x} :
    Outcome.RefinementAxis →
      Outcome Established Refuted Boundary Incomplete →
      Outcome Established Refuted Boundary Incomplete →
      Type (max u v w x) where
  | established (axis : Outcome.RefinementAxis)
      (before after : Established) :
      CanonicalAxisRefinement axis
        (.established before) (.established after)
  | refuted (axis : Outcome.RefinementAxis)
      (before after : Refuted) :
      CanonicalAxisRefinement axis (.refuted before) (.refuted after)
  | incomplete (axis : Outcome.RefinementAxis)
      (before after : Incomplete) :
      CanonicalAxisRefinement axis (.incomplete before) (.incomplete after)
  | budgetOutsideFragment (reason : Boundary) :
      CanonicalAxisRefinement .budget
        (.outsideFragment reason) (.outsideFragment reason)
  | budgetIncompleteEstablished
      (before : Incomplete) (after : Established) :
      CanonicalAxisRefinement .budget
        (.incomplete before) (.established after)
  | budgetIncompleteRefuted
      (before : Incomplete) (after : Refuted) :
      CanonicalAxisRefinement .budget
        (.incomplete before) (.refuted after)
  | authorityOutsideFragment (before after : Boundary) :
      CanonicalAxisRefinement .authority
        (.outsideFragment before) (.outsideFragment after)
  | authorityOutsideEstablished
      (before : Boundary) (after : Established) :
      CanonicalAxisRefinement .authority
        (.outsideFragment before) (.established after)
  | authorityOutsideRefuted
      (before : Boundary) (after : Refuted) :
      CanonicalAxisRefinement .authority
        (.outsideFragment before) (.refuted after)
  | authorityOutsideIncomplete
      (before : Boundary) (after : Incomplete) :
      CanonicalAxisRefinement .authority
        (.outsideFragment before) (.incomplete after)

namespace CanonicalAxisRefinement

variable {Established : Type u} {Refuted : Type v}
variable {Boundary : Type w} {Incomplete : Type x}

/-- Interpret one canonical native constructor as abstract refinement
evidence. -/
def toEvidence {axis : Outcome.RefinementAxis}
    {before after : Outcome Established Refuted Boundary Incomplete} :
    CanonicalAxisRefinement axis before after →
      Outcome.AxisRefinementEvidence axis before after
  | .established axis before after =>
      .established axis before after
  | .refuted axis before after => .refuted axis before after
  | .incomplete axis before after => .incomplete axis before after
  | .budgetOutsideFragment reason => .budgetOutsideFragment reason
  | .budgetIncompleteEstablished before after =>
      .budgetIncompleteEstablished before after
  | .budgetIncompleteRefuted before after =>
      .budgetIncompleteRefuted before after
  | .authorityOutsideFragment before after =>
      .authorityOutsideFragment before after
  | .authorityOutsideEstablished before after =>
      .authorityOutsideEstablished before after
  | .authorityOutsideRefuted before after =>
      .authorityOutsideRefuted before after
  | .authorityOutsideIncomplete before after =>
      .authorityOutsideIncomplete before after

/-- Reify abstract refinement evidence by the corresponding native
constructor code. -/
def ofEvidence {axis : Outcome.RefinementAxis}
    {before after : Outcome Established Refuted Boundary Incomplete} :
    Outcome.AxisRefinementEvidence axis before after →
      CanonicalAxisRefinement axis before after
  | .established axis before after =>
      .established axis before after
  | .refuted axis before after => .refuted axis before after
  | .incomplete axis before after => .incomplete axis before after
  | .budgetOutsideFragment reason => .budgetOutsideFragment reason
  | .budgetIncompleteEstablished before after =>
      .budgetIncompleteEstablished before after
  | .budgetIncompleteRefuted before after =>
      .budgetIncompleteRefuted before after
  | .authorityOutsideFragment before after =>
      .authorityOutsideFragment before after
  | .authorityOutsideEstablished before after =>
      .authorityOutsideEstablished before after
  | .authorityOutsideRefuted before after =>
      .authorityOutsideRefuted before after
  | .authorityOutsideIncomplete before after =>
      .authorityOutsideIncomplete before after

@[simp] theorem toEvidence_ofEvidence
    {axis : Outcome.RefinementAxis}
    {before after : Outcome Established Refuted Boundary Incomplete}
    (evidence : Outcome.AxisRefinementEvidence axis before after) :
    toEvidence (ofEvidence evidence) = evidence := by
  cases evidence <;> rfl

@[simp] theorem ofEvidence_toEvidence
    {axis : Outcome.RefinementAxis}
    {before after : Outcome Established Refuted Boundary Incomplete}
    (code : CanonicalAxisRefinement axis before after) :
    ofEvidence (toEvidence code) = code := by
  cases code <;> rfl

/-- The canonical native constructor image and the abstract, proof-relevant
refinement algebra are equivalent without quotienting witnesses. -/
def evidenceEquiv {axis : Outcome.RefinementAxis}
    {before after : Outcome Established Refuted Boundary Incomplete} :
    CanonicalAxisRefinement axis before after ≃
      Outcome.AxisRefinementEvidence axis before after where
  toFun := toEvidence
  invFun := ofEvidence
  left_inv := ofEvidence_toEvidence
  right_inv := toEvidence_ofEvidence

/-- The declared constant used by a canonical witness. -/
def constructorName {axis : Outcome.RefinementAxis}
    {before after : Outcome Established Refuted Boundary Incomplete} :
    CanonicalAxisRefinement axis before after → DeclName
  | .established .. => axisEstablishedName
  | .refuted .. => axisRefutedName
  | .incomplete .. => axisIncompleteName
  | .budgetOutsideFragment .. => budgetOutsideRefinementName
  | .budgetIncompleteEstablished .. =>
      budgetIncompleteEstablishedRefinementName
  | .budgetIncompleteRefuted .. => budgetIncompleteRefutedRefinementName
  | .authorityOutsideFragment .. => authorityOutsideRefinementName
  | .authorityOutsideEstablished .. =>
      authorityOutsideEstablishedRefinementName
  | .authorityOutsideRefuted .. => authorityOutsideRefutedRefinementName
  | .authorityOutsideIncomplete .. =>
      authorityOutsideIncompleteRefinementName

/-- Every semantic constructor code names one of the constructors certified
by `axisRefinementCandidate`. -/
theorem constructorName_mem
    {axis : Outcome.RefinementAxis}
    {before after : Outcome Established Refuted Boundary Incomplete}
    (code : CanonicalAxisRefinement axis before after) :
    code.constructorName ∈
      axisRefinementConstructors.map ConstructorSpec.name := by
  cases code <;>
    simp [constructorName, axisRefinementConstructors,
      axisEstablishedConstructorSpec, axisRefutedConstructorSpec,
      axisIncompleteConstructorSpec,
      budgetOutsideRefinementConstructorSpec,
      budgetIncompleteEstablishedRefinementConstructorSpec,
      budgetIncompleteRefutedRefinementConstructorSpec,
      authorityOutsideRefinementConstructorSpec,
      authorityOutsideEstablishedRefinementConstructorSpec,
      authorityOutsideRefutedRefinementConstructorSpec,
      authorityOutsideIncompleteRefinementConstructorSpec]

/-- The old fixed-authority relation is exactly the budget fibre of the
canonical native family. -/
def budgetEquiv
    {before after : Outcome Established Refuted Boundary Incomplete} :
    CanonicalAxisRefinement .budget before after ≃
      Outcome.BudgetRefinementEvidence before after :=
  evidenceEquiv.trans Outcome.AxisRefinementEvidence.budgetEquiv

/-- The old expanding-authority relation is exactly the authority fibre of
the canonical native family. -/
def authorityEquiv
    {before after : Outcome Established Refuted Boundary Incomplete} :
    CanonicalAxisRefinement .authority before after ≃
      Outcome.AuthorityRefinementEvidence before after :=
  evidenceEquiv.trans Outcome.AxisRefinementEvidence.authorityEquiv

/-- Proposition-valued reachability is precisely the support of canonical
proof-relevant evidence; it is a readout, not the foundation. -/
theorem nonempty_iff_support {axis : Outcome.RefinementAxis}
    {before after : Outcome Established Refuted Boundary Incomplete} :
    Nonempty (CanonicalAxisRefinement axis before after) ↔
      Outcome.AxisRefines axis before after := by
  constructor
  · rintro ⟨code⟩
    exact code.toEvidence.support
  · intro support
    rcases Outcome.nonempty_axisRefinementEvidence_iff.mpr support with
      ⟨evidence⟩
    exact ⟨ofEvidence evidence⟩

/-- Budget growth cannot rewrite the reason why a judgment lies outside the
recognized fragment. -/
theorem budgetOutside_reason_preserved {before after : Boundary}
    (code : CanonicalAxisRefinement
      (Established := Established) (Refuted := Refuted)
      (Boundary := Boundary) (Incomplete := Incomplete) .budget
      (.outsideFragment before) (.outsideFragment after)) :
    before = after := by
  cases code
  rfl

/-- Increasing resources cannot discharge a boundary that requires a
stronger authority. -/
theorem budgetOutside_established_forbidden
    {reason : Boundary} {evidence : Established}
    (code : CanonicalAxisRefinement
      (Established := Established) (Refuted := Refuted)
      (Boundary := Boundary) (Incomplete := Incomplete) .budget
      (.outsideFragment reason) (.established evidence)) : False := by
  cases code

/-- Increasing authority is not evidence that a resource frontier has been
resolved. -/
theorem authorityIncomplete_established_forbidden
    {frontier : Incomplete} {evidence : Established}
    (code : CanonicalAxisRefinement
      (Established := Established) (Refuted := Refuted)
      (Boundary := Boundary) (Incomplete := Incomplete) .authority
      (.incomplete frontier) (.established evidence)) : False := by
  cases code

end CanonicalAxisRefinement

/-! ### Exact proof-relevant histories -/

/-- Free paths generated by canonical native refinement witnesses.  Both the
axis label and every intermediate outcome remain data. -/
inductive CanonicalRefinementPath
    {Established : Type u} {Refuted : Type v}
    {Boundary : Type w} {Incomplete : Type x} :
    Outcome Established Refuted Boundary Incomplete →
      Outcome Established Refuted Boundary Incomplete →
      Type (max (u + 1) (v + 1) w x) where
  | nil {outcome : Outcome Established Refuted Boundary Incomplete} :
      CanonicalRefinementPath outcome outcome
  | cons {axis : Outcome.RefinementAxis}
      {before middle after :
        Outcome Established Refuted Boundary Incomplete}
      (edge : CanonicalAxisRefinement axis before middle)
      (rest : CanonicalRefinementPath middle after) :
      CanonicalRefinementPath before after

namespace CanonicalRefinementPath

variable {Established : Type u} {Refuted : Type v}
variable {Boundary : Type w} {Incomplete : Type x}

/-- Interpret a canonical native history as an abstract refinement history. -/
def toExternal
    {before after : Outcome Established Refuted Boundary Incomplete} :
    CanonicalRefinementPath before after →
      Outcome.RefinementPath before after
  | .nil => .nil
  | .cons edge rest => .cons edge.toEvidence (toExternal rest)

/-- Reify an abstract refinement history edge by edge. -/
def ofExternal
    {before after : Outcome Established Refuted Boundary Incomplete} :
    Outcome.RefinementPath before after →
      CanonicalRefinementPath before after
  | .nil => .nil
  | .cons edge rest => .cons (.ofEvidence edge) (ofExternal rest)

@[simp] theorem toExternal_ofExternal
    {before after : Outcome Established Refuted Boundary Incomplete}
    (path : Outcome.RefinementPath before after) :
    toExternal (ofExternal path) = path := by
  induction path with
  | nil => rfl
  | cons edge rest ih => simp [ofExternal, toExternal, ih]

@[simp] theorem ofExternal_toExternal
    {before after : Outcome Established Refuted Boundary Incomplete}
    (path : CanonicalRefinementPath before after) :
    ofExternal (toExternal path) = path := by
  induction path with
  | nil => rfl
  | cons edge rest ih => simp [toExternal, ofExternal, ih]

/-- Native canonical histories and external histories are equivalent without
collapsing intermediate outcomes or edge witnesses. -/
def externalEquiv
    {before after : Outcome Established Refuted Boundary Incomplete} :
    CanonicalRefinementPath before after ≃
      Outcome.RefinementPath before after where
  toFun := toExternal
  invFun := ofExternal
  left_inv := ofExternal_toExternal
  right_inv := toExternal_ofExternal

/-- The axis trace is a derived observation of a proof-relevant history. -/
def axes
    {before after : Outcome Established Refuted Boundary Incomplete} :
    CanonicalRefinementPath before after → List Outcome.RefinementAxis
  | .nil => []
  | @cons _ _ _ _ axis _ _ _ _ rest => axis :: axes rest

@[simp] theorem axes_nil
    (outcome : Outcome Established Refuted Boundary Incomplete) :
    axes (.nil (outcome := outcome)) = [] :=
  rfl

@[simp] theorem axes_cons {axis : Outcome.RefinementAxis}
    {before middle after :
      Outcome Established Refuted Boundary Incomplete}
    (edge : CanonicalAxisRefinement axis before middle)
    (rest : CanonicalRefinementPath middle after) :
    axes (.cons edge rest) = axis :: axes rest :=
  rfl

/-- Positive mixed-history control: authority expansion may reveal a
resource frontier, after which a larger budget establishes evidence. -/
def authorityThenBudgetEstablished
    (boundary : Boundary) (frontier : Incomplete)
    (evidence : Established) :
    CanonicalRefinementPath
      ((.outsideFragment boundary) :
        Outcome Established Refuted Boundary Incomplete)
      (.established evidence) :=
  .cons (.authorityOutsideIncomplete boundary frontier)
    (.cons (.budgetIncompleteEstablished frontier evidence) .nil)

@[simp] theorem authorityThenBudgetEstablished_axes
    (boundary : Boundary) (frontier : Incomplete)
    (evidence : Established) :
    axes (authorityThenBudgetEstablished
      (Refuted := Refuted) boundary frontier evidence) =
      [.authority, .budget] :=
  rfl

/-- No mixed sequence of legal refinements can reverse an established
decision into a checked refutation. -/
theorem establishedToRefuted_forbidden
    {evidence : Established} {obstruction : Refuted}
    (path : CanonicalRefinementPath
      ((.established evidence) :
        Outcome Established Refuted Boundary Incomplete)
      (.refuted obstruction)) : False :=
  Outcome.RefinementPath.establishedToRefuted_forbidden path.toExternal

end CanonicalRefinementPath

/-! ## Axiom audit -/

#print axioms rawAxisRefinementSignature_formed
#print axioms axisEstablishedIotaReceipt
#print axioms axisRefutedIotaReceipt
#print axioms axisIncompleteIotaReceipt
#print axioms budgetOutsideIotaReceipt
#print axioms budgetIncompleteEstablishedIotaReceipt
#print axioms budgetIncompleteRefutedIotaReceipt
#print axioms authorityOutsideIotaReceipt
#print axioms authorityOutsideEstablishedIotaReceipt
#print axioms authorityOutsideRefutedIotaReceipt
#print axioms authorityOutsideIncompleteIotaReceipt
#print axioms axisRefinementCandidate
#print axioms CanonicalAxisRefinement.evidenceEquiv
#print axioms CanonicalAxisRefinement.budgetEquiv
#print axioms CanonicalAxisRefinement.authorityEquiv
#print axioms CanonicalAxisRefinement.nonempty_iff_support
#print axioms CanonicalRefinementPath.externalEquiv
#print axioms CanonicalRefinementPath.establishedToRefuted_forbidden

end Intrinsic
end InternalAuthorityMetatheory
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
