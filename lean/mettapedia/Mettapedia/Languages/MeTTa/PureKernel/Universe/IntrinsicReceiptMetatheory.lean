import Mettapedia.Languages.MeTTa.PureKernel.Universe.IntrinsicRunMetatheory

/-!
# Intrinsic authority receipts

This module adds provenance-bearing invocation receipts above the intrinsic
`Run` family.  A receipt signature bundles a run signature with independent
types of requested budgets, actual costs, provenance, and authority keys.
The receipt family is indexed by the exact authority key, requested budget,
and judgment.  Consequently, replay under a different authority or budget
requires explicit equality evidence; neither identity may be reconstructed
from a result or cost observation.

The construction is generic.  Prime supplies one later signature value, while
other languages may supply their own judgments, evidence, faults, resources,
and provenance.  Formation, strict positivity, and exact typed iota evidence
produce a declaration candidate.  Raw conversion authority remains a
separate obligation.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe
namespace InternalAuthorityMetatheory
namespace Intrinsic

open Presentation
open Presentation.SchemaElaboration
open Presentation.Declaration
open Presentation.Declaration.ComputationAuthority
open Presentation.Declaration.IndexedFamily

/-! ## First-class receipt signatures -/

/-- Requested budgets are independent of actual costs. -/
def receiptBudgetLevel : LevelExpr := .param 8

/-- Actual costs may inhabit a universe independent of budgets. -/
def receiptCostLevel : LevelExpr := .param 9

/-- Provenance is retained as data rather than reconstructed from outcomes. -/
def receiptProvenanceLevel : LevelExpr := .param 10

/-- Authority identities are first-class and need not be natural numbers. -/
def receiptKeyLevel : LevelExpr := .param 11

/-- Receipt elimination may target an independently selected universe. -/
def receiptMotiveLevel : LevelExpr := .param 12

def receiptKeyTailLevel : LevelExpr :=
  .max (.succ receiptProvenanceLevel) (.succ receiptKeyLevel)

def receiptCostTailLevel : LevelExpr :=
  .max (.succ receiptCostLevel) receiptKeyTailLevel

def receiptResourceBundleLevel : LevelExpr :=
  .max (.succ receiptBudgetLevel) receiptCostTailLevel

/-- In context `runSignature`, the remaining components are ordinary types:
budget, cost, provenance, and authority key. -/
def receiptSignatureBody : Tower.Tm 1 :=
  .sigma (sortTm receiptBudgetLevel)
    (.sigma (sortTm receiptCostLevel)
      (.sigma (sortTm receiptProvenanceLevel)
        (sortTm receiptKeyLevel)))

/-- `ReceiptSignature` retains the semantic and operational signature once,
then adds resource and identity types without privileging an implementation. -/
def receiptSignatureType : Tower.Tm 0 :=
  .sigma runSignatureType receiptSignatureBody

def receiptSignatureLevel : LevelExpr :=
  .max runSignatureLevel receiptResourceBundleLevel

theorem receiptSignatureBody_hasType :
    RunHasType runContextR receiptSignatureBody
      (sortTm receiptResourceBundleLevel) := by
  unfold receiptSignatureBody receiptResourceBundleLevel
    receiptCostTailLevel receiptKeyTailLevel
  apply Presentation.HasType.sigmaForm
      (Presentation.HasType.headType
        (Tower.HeadTyping.sort receiptBudgetLevel))
      (Tower.IsUniverse.sort (.succ receiptBudgetLevel))
  · apply Presentation.HasType.sigmaForm
        (Presentation.HasType.headType
          (Tower.HeadTyping.sort receiptCostLevel))
        (Tower.IsUniverse.sort (.succ receiptCostLevel))
    · apply Presentation.HasType.sigmaForm
          (Presentation.HasType.headType
            (Tower.HeadTyping.sort receiptProvenanceLevel))
          (Tower.IsUniverse.sort (.succ receiptProvenanceLevel))
      · exact Presentation.HasType.headType
          (Tower.HeadTyping.sort receiptKeyLevel)
      · exact Tower.IsUniverse.sort (.succ receiptKeyLevel)
      · exact Tower.Join.sorts (.succ receiptProvenanceLevel)
          (.succ receiptKeyLevel)
    · exact Tower.IsUniverse.sort receiptKeyTailLevel
    · exact Tower.Join.sorts (.succ receiptCostLevel) receiptKeyTailLevel
  · exact Tower.IsUniverse.sort receiptCostTailLevel
  · exact Tower.Join.sorts (.succ receiptBudgetLevel) receiptCostTailLevel

theorem receiptSignatureType_hasType :
    RunHasType (.nil : Tower.Ctx 0) receiptSignatureType
      (sortTm receiptSignatureLevel) := by
  unfold receiptSignatureType receiptSignatureLevel
  apply Presentation.HasType.sigmaForm
  · exact runSignatureType_hasRunType
  · exact .sort runSignatureLevel
  · exact receiptSignatureBody_hasType
  · exact .sort receiptResourceBundleLevel
  · exact .sorts runSignatureLevel receiptResourceBundleLevel

def receiptSignatureContextR : Tower.Ctx 1 :=
  .snoc .nil runSignatureType

def receiptSignatureContextRB : Tower.Ctx 2 :=
  .snoc receiptSignatureContextR (sortTm receiptBudgetLevel)

def receiptSignatureContextRBC : Tower.Ctx 3 :=
  .snoc receiptSignatureContextRB (sortTm receiptCostLevel)

def receiptSignatureContextRBCP : Tower.Ctx 4 :=
  .snoc receiptSignatureContextRBC (sortTm receiptProvenanceLevel)

def receiptSignatureContextRBCPK : Tower.Ctx 5 :=
  .snoc receiptSignatureContextRBCP (sortTm receiptKeyLevel)

/-- Positive control: independently typed components assemble into a
first-class receipt signature value. -/
def parameterReceiptSignatureValue : Tower.Tm 5 :=
  .pair (.var 4)
    (.pair (.var 3)
      (.pair (.var 2)
        (.pair (.var 1) (.var 0))))

theorem parameterReceiptSignatureValue_hasType :
    RunHasType receiptSignatureContextRBCPK parameterReceiptSignatureValue
      (liftClosed receiptSignatureType) := by
  unfold parameterReceiptSignatureValue receiptSignatureContextRBCPK
    receiptSignatureContextRBCP receiptSignatureContextRBC
    receiptSignatureContextRB receiptSignatureContextR
    receiptSignatureType receiptSignatureBody
  apply Presentation.HasType.pairIntro (Presentation.HasType.var 4)
  apply Presentation.HasType.pairIntro (Presentation.HasType.var 3)
  apply Presentation.HasType.pairIntro (Presentation.HasType.var 2)
  apply Presentation.HasType.pairIntro (Presentation.HasType.var 1)
  exact Presentation.HasType.var 0

/-- Projections preserve the run signature as one coherent component. -/
def receiptRunSignature (signature : Tower.Tm n) : Tower.Tm n :=
  .fst signature

def receiptBudget (signature : Tower.Tm n) : Tower.Tm n :=
  .fst (.snd signature)

def receiptCost (signature : Tower.Tm n) : Tower.Tm n :=
  .fst (.snd (.snd signature))

def receiptProvenance (signature : Tower.Tm n) : Tower.Tm n :=
  .fst (.snd (.snd (.snd signature)))

def receiptKey (signature : Tower.Tm n) : Tower.Tm n :=
  .snd (.snd (.snd (.snd signature)))

def receiptJudgment (signature : Tower.Tm n) : Tower.Tm n :=
  runJudgment (receiptRunSignature signature)

@[simp] theorem rename_receiptRunSignature (renameMap : Ren n m)
    (signature : Tower.Tm n) :
    Presentation.rename renameMap (receiptRunSignature signature) =
      receiptRunSignature (Presentation.rename renameMap signature) := rfl

@[simp] theorem rename_receiptBudget (renameMap : Ren n m)
    (signature : Tower.Tm n) :
    Presentation.rename renameMap (receiptBudget signature) =
      receiptBudget (Presentation.rename renameMap signature) := rfl

@[simp] theorem rename_receiptCost (renameMap : Ren n m)
    (signature : Tower.Tm n) :
    Presentation.rename renameMap (receiptCost signature) =
      receiptCost (Presentation.rename renameMap signature) := rfl

@[simp] theorem rename_receiptProvenance (renameMap : Ren n m)
    (signature : Tower.Tm n) :
    Presentation.rename renameMap (receiptProvenance signature) =
      receiptProvenance (Presentation.rename renameMap signature) := rfl

@[simp] theorem rename_receiptKey (renameMap : Ren n m)
    (signature : Tower.Tm n) :
    Presentation.rename renameMap (receiptKey signature) =
      receiptKey (Presentation.rename renameMap signature) := rfl

@[simp] theorem rename_receiptJudgment (renameMap : Ren n m)
    (signature : Tower.Tm n) :
    Presentation.rename renameMap (receiptJudgment signature) =
      receiptJudgment (Presentation.rename renameMap signature) := rfl

@[simp] theorem subst_receiptRunSignature
    (substitution : Sub Tower.Head n m) (signature : Tower.Tm n) :
    Presentation.subst substitution (receiptRunSignature signature) =
      receiptRunSignature (Presentation.subst substitution signature) := rfl

@[simp] theorem subst_receiptBudget
    (substitution : Sub Tower.Head n m) (signature : Tower.Tm n) :
    Presentation.subst substitution (receiptBudget signature) =
      receiptBudget (Presentation.subst substitution signature) := rfl

@[simp] theorem subst_receiptCost
    (substitution : Sub Tower.Head n m) (signature : Tower.Tm n) :
    Presentation.subst substitution (receiptCost signature) =
      receiptCost (Presentation.subst substitution signature) := rfl

@[simp] theorem subst_receiptProvenance
    (substitution : Sub Tower.Head n m) (signature : Tower.Tm n) :
    Presentation.subst substitution (receiptProvenance signature) =
      receiptProvenance (Presentation.subst substitution signature) := rfl

@[simp] theorem subst_receiptKey
    (substitution : Sub Tower.Head n m) (signature : Tower.Tm n) :
    Presentation.subst substitution (receiptKey signature) =
      receiptKey (Presentation.subst substitution signature) := rfl

@[simp] theorem subst_receiptJudgment
    (substitution : Sub Tower.Head n m) (signature : Tower.Tm n) :
    Presentation.subst substitution (receiptJudgment signature) =
      receiptJudgment (Presentation.subst substitution signature) := rfl

theorem receiptRunSignature_hasType {rules : Rules Tower.Head}
    {context : Tower.Ctx n} {signature : Tower.Tm n}
    (signatureTyping : Presentation.HasType rules context signature
      (liftClosed receiptSignatureType)) :
    Presentation.HasType rules context (receiptRunSignature signature)
      (liftClosed runSignatureType) := by
  have projection := Presentation.HasType.fstElim signatureTyping
  simpa [receiptRunSignature, receiptSignatureType, liftClosed,
    Presentation.rename] using projection

theorem receiptBudget_hasType {rules : Rules Tower.Head}
    {context : Tower.Ctx n} {signature : Tower.Tm n}
    (signatureTyping : Presentation.HasType rules context signature
      (liftClosed receiptSignatureType)) :
    Presentation.HasType rules context (receiptBudget signature)
      (sortTm receiptBudgetLevel) := by
  have tail := Presentation.HasType.sndElim signatureTyping
  have projection := Presentation.HasType.fstElim tail
  simpa [receiptBudget, receiptSignatureType, receiptSignatureBody,
    liftClosed, sortTm, Presentation.rename, Presentation.subst0,
    Presentation.inst0, Presentation.subst, Presentation.liftSub,
    Presentation.liftRen] using projection

theorem receiptCost_hasType {rules : Rules Tower.Head}
    {context : Tower.Ctx n} {signature : Tower.Tm n}
    (signatureTyping : Presentation.HasType rules context signature
      (liftClosed receiptSignatureType)) :
    Presentation.HasType rules context (receiptCost signature)
      (sortTm receiptCostLevel) := by
  have tail₁ := Presentation.HasType.sndElim signatureTyping
  have tail₂ := Presentation.HasType.sndElim tail₁
  have projection := Presentation.HasType.fstElim tail₂
  simpa [receiptCost, receiptSignatureType, receiptSignatureBody,
    liftClosed, sortTm, Presentation.rename, Presentation.subst0,
    Presentation.inst0, Presentation.subst, Presentation.liftSub,
    Presentation.liftRen] using projection

theorem receiptProvenance_hasType {rules : Rules Tower.Head}
    {context : Tower.Ctx n} {signature : Tower.Tm n}
    (signatureTyping : Presentation.HasType rules context signature
      (liftClosed receiptSignatureType)) :
    Presentation.HasType rules context (receiptProvenance signature)
      (sortTm receiptProvenanceLevel) := by
  have tail₁ := Presentation.HasType.sndElim signatureTyping
  have tail₂ := Presentation.HasType.sndElim tail₁
  have tail₃ := Presentation.HasType.sndElim tail₂
  have projection := Presentation.HasType.fstElim tail₃
  simpa [receiptProvenance, receiptSignatureType, receiptSignatureBody,
    liftClosed, sortTm, Presentation.rename, Presentation.subst0,
    Presentation.inst0, Presentation.subst, Presentation.liftSub,
    Presentation.liftRen] using projection

theorem receiptKey_hasType {rules : Rules Tower.Head}
    {context : Tower.Ctx n} {signature : Tower.Tm n}
    (signatureTyping : Presentation.HasType rules context signature
      (liftClosed receiptSignatureType)) :
    Presentation.HasType rules context (receiptKey signature)
      (sortTm receiptKeyLevel) := by
  have tail₁ := Presentation.HasType.sndElim signatureTyping
  have tail₂ := Presentation.HasType.sndElim tail₁
  have tail₃ := Presentation.HasType.sndElim tail₂
  have projection := Presentation.HasType.sndElim tail₃
  simpa [receiptKey, receiptSignatureType, receiptSignatureBody,
    liftClosed, sortTm, Presentation.rename, Presentation.subst0,
    Presentation.inst0, Presentation.subst, Presentation.liftSub,
    Presentation.liftRen] using projection

theorem receiptJudgment_hasType {rules : Rules Tower.Head}
    {context : Tower.Ctx n} {signature : Tower.Tm n}
    (signatureTyping : Presentation.HasType rules context signature
      (liftClosed receiptSignatureType)) :
    Presentation.HasType rules context (receiptJudgment signature)
      (sortTm judgmentLevel) :=
  runJudgment_hasType (receiptRunSignature_hasType signatureTyping)

/-! ## The intrinsic indexed receipt family -/

def receiptName : DeclName := `Prime.Authority.Receipt
def receiptMakeName : DeclName := `Prime.Authority.Receipt.make
def receiptEliminateName : DeclName := `Prime.Authority.Receipt.eliminate

def receiptLevel : LevelExpr :=
  .max judgmentLevel
    (.max runLevel
      (.max receiptBudgetLevel
        (.max receiptCostLevel
          (.max receiptProvenanceLevel receiptKeyLevel))))

def receiptApp (signature key budget judgment : Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app
        (.app (.const receiptName) signature)
        key)
      budget)
    judgment

def receiptMakeApp (signature key budget judgment spent provenance result :
    Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app
        (.app
          (.app
            (.app
              (.app (.const receiptMakeName) signature)
              key)
            budget)
          judgment)
        spent)
      provenance)
    result

def receiptMotiveApp (motive key budget judgment receipt : Tower.Tm n) :
    Tower.Tm n :=
  .app (.app (.app (.app motive key) budget) judgment) receipt

def receiptEliminateApp (signature motive makeCase key budget judgment receipt :
    Tower.Tm n) : Tower.Tm n :=
  .app
    (.app
      (.app
        (.app
          (.app
            (.app
              (.app (.const receiptEliminateName) signature)
              motive)
            makeCase)
          key)
        budget)
      judgment)
    receipt

@[simp] theorem rename_receiptApp (renameMap : Ren n m)
    (signature key budget judgment : Tower.Tm n) :
    Presentation.rename renameMap
        (receiptApp signature key budget judgment) =
      receiptApp (Presentation.rename renameMap signature)
        (Presentation.rename renameMap key)
        (Presentation.rename renameMap budget)
        (Presentation.rename renameMap judgment) := rfl

@[simp] theorem subst_receiptApp (substitution : Sub Tower.Head n m)
    (signature key budget judgment : Tower.Tm n) :
    Presentation.subst substitution
        (receiptApp signature key budget judgment) =
      receiptApp (Presentation.subst substitution signature)
        (Presentation.subst substitution key)
        (Presentation.subst substitution budget)
        (Presentation.subst substitution judgment) := rfl

@[simp] theorem rename_receiptMakeApp (renameMap : Ren n m)
    (signature key budget judgment spent provenance result : Tower.Tm n) :
    Presentation.rename renameMap
        (receiptMakeApp signature key budget judgment spent provenance result) =
      receiptMakeApp (Presentation.rename renameMap signature)
        (Presentation.rename renameMap key)
        (Presentation.rename renameMap budget)
        (Presentation.rename renameMap judgment)
        (Presentation.rename renameMap spent)
        (Presentation.rename renameMap provenance)
        (Presentation.rename renameMap result) := rfl

@[simp] theorem subst_receiptMakeApp (substitution : Sub Tower.Head n m)
    (signature key budget judgment spent provenance result : Tower.Tm n) :
    Presentation.subst substitution
        (receiptMakeApp signature key budget judgment spent provenance result) =
      receiptMakeApp (Presentation.subst substitution signature)
        (Presentation.subst substitution key)
        (Presentation.subst substitution budget)
        (Presentation.subst substitution judgment)
        (Presentation.subst substitution spent)
        (Presentation.subst substitution provenance)
        (Presentation.subst substitution result) := rfl

@[simp] theorem rename_receiptMotiveApp (renameMap : Ren n m)
    (motive key budget judgment receipt : Tower.Tm n) :
    Presentation.rename renameMap
        (receiptMotiveApp motive key budget judgment receipt) =
      receiptMotiveApp (Presentation.rename renameMap motive)
        (Presentation.rename renameMap key)
        (Presentation.rename renameMap budget)
        (Presentation.rename renameMap judgment)
        (Presentation.rename renameMap receipt) := rfl

@[simp] theorem subst_receiptMotiveApp (substitution : Sub Tower.Head n m)
    (motive key budget judgment receipt : Tower.Tm n) :
    Presentation.subst substitution
        (receiptMotiveApp motive key budget judgment receipt) =
      receiptMotiveApp (Presentation.subst substitution motive)
        (Presentation.subst substitution key)
        (Presentation.subst substitution budget)
        (Presentation.subst substitution judgment)
        (Presentation.subst substitution receipt) := rfl

@[simp] theorem rename_receiptEliminateApp (renameMap : Ren n m)
    (signature motive makeCase key budget judgment receipt : Tower.Tm n) :
    Presentation.rename renameMap
        (receiptEliminateApp signature motive makeCase key budget judgment
          receipt) =
      receiptEliminateApp (Presentation.rename renameMap signature)
        (Presentation.rename renameMap motive)
        (Presentation.rename renameMap makeCase)
        (Presentation.rename renameMap key)
        (Presentation.rename renameMap budget)
        (Presentation.rename renameMap judgment)
        (Presentation.rename renameMap receipt) := rfl

@[simp] theorem subst_receiptEliminateApp
    (substitution : Sub Tower.Head n m)
    (signature motive makeCase key budget judgment receipt : Tower.Tm n) :
    Presentation.subst substitution
        (receiptEliminateApp signature motive makeCase key budget judgment
          receipt) =
      receiptEliminateApp (Presentation.subst substitution signature)
        (Presentation.subst substitution motive)
        (Presentation.subst substitution makeCase)
        (Presentation.subst substitution key)
        (Presentation.subst substitution budget)
        (Presentation.subst substitution judgment)
        (Presentation.subst substitution receipt) := rfl

/-- Family telescope below its first-class signature parameter. -/
def receiptBodyType : Tower.Tm 1 :=
  .pi (receiptKey (.var 0))
    (.pi (receiptBudget (.var 1))
      (.pi (receiptJudgment (.var 2)) (sortTm receiptLevel)))

/-- `Receipt : (signature : ReceiptSignature) -> signature.Key ->
signature.Budget -> signature.Judgment -> U`. -/
def receiptType : Tower.Tm 0 :=
  .pi receiptSignatureType receiptBodyType

def receiptMakeBodyType : Tower.Tm 1 :=
  .pi (receiptKey (.var 0))
    (.pi (receiptBudget (.var 1))
      (.pi (receiptJudgment (.var 2))
        (.pi (receiptCost (.var 3))
          (.pi (receiptProvenance (.var 4))
            (.pi (runApp (receiptRunSignature (.var 5)) (.var 2))
              (receiptApp (.var 6) (.var 5) (.var 4) (.var 3)))))))

def receiptMakeType : Tower.Tm 0 :=
  .pi receiptSignatureType receiptMakeBodyType

def receiptAtSignatureType (signature : Tower.Tm n) : Tower.Tm n :=
  .pi (receiptKey signature)
    (.pi (receiptBudget (Presentation.rename wk signature))
      (.pi
        (receiptJudgment
          (Presentation.rename wk (Presentation.rename wk signature)))
        (sortTm receiptLevel)))

@[simp] theorem liftSub_singleParameter_two (term : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub (fun _ : Fin 1 => term))
        (2 : Fin 3) =
      Presentation.rename wk (Presentation.rename wk term) := by
  rfl

@[simp] theorem liftSub_singleParameter_three (term : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub
          (Presentation.liftSub (fun _ : Fin 1 => term)))
        (3 : Fin 4) =
      Presentation.rename wk
        (Presentation.rename wk (Presentation.rename wk term)) := by
  rfl

@[simp] theorem liftSub_singleParameter_four (term : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub
          (Presentation.liftSub
            (Presentation.liftSub (fun _ : Fin 1 => term))))
        (4 : Fin 5) =
      Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk (Presentation.rename wk term))) := by
  rfl

@[simp] theorem liftSub_singleParameter_five (term : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub
          (Presentation.liftSub
            (Presentation.liftSub
              (Presentation.liftSub (fun _ : Fin 1 => term)))))
        (5 : Fin 6) =
      Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk
            (Presentation.rename wk (Presentation.rename wk term)))) := by
  rfl

@[simp] theorem liftSub_singleParameter_six (term : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub
          (Presentation.liftSub
            (Presentation.liftSub
              (Presentation.liftSub
                (Presentation.liftSub (fun _ : Fin 1 => term))))))
        (6 : Fin 7) =
      Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk
            (Presentation.rename wk
              (Presentation.rename wk (Presentation.rename wk term))))) := by
  rfl

/-- A lifted one-parameter substitution fixes the binders introduced after
that parameter.  These low-variable equations are the other half of the
closed-parameter equations above: the signature is substituted, while the
constructor's locally bound data remain local variables. -/
@[simp] theorem liftSub_five_singleParameter_two (term : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub
          (Presentation.liftSub
            (Presentation.liftSub
              (Presentation.liftSub (fun _ : Fin 1 => term)))))
        (2 : Fin 6) = (.var 2 : Tower.Tm (n + 5)) := by
  rfl

@[simp] theorem liftSub_six_singleParameter_three (term : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub
          (Presentation.liftSub
            (Presentation.liftSub
              (Presentation.liftSub
                (Presentation.liftSub (fun _ : Fin 1 => term))))))
        (3 : Fin 7) = (.var 3 : Tower.Tm (n + 6)) := by
  rfl

@[simp] theorem liftSub_six_singleParameter_four (term : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub
          (Presentation.liftSub
            (Presentation.liftSub
              (Presentation.liftSub
                (Presentation.liftSub (fun _ : Fin 1 => term))))))
        (4 : Fin 7) = (.var 4 : Tower.Tm (n + 6)) := by
  rfl

@[simp] theorem liftSub_six_singleParameter_five (term : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub
          (Presentation.liftSub
            (Presentation.liftSub
              (Presentation.liftSub
                (Presentation.liftSub (fun _ : Fin 1 => term))))))
        (5 : Fin 7) = (.var 5 : Tower.Tm (n + 6)) := by
  rfl

/-! Opening below an existing local telescope cancels one weakening while
preserving all newer binders.  The fixed arities mirror the receipt
constructor's six fields and make its dependent indices auditable. -/

@[simp] theorem open_weakened_under_zero
    (argument term : Tower.Tm n) :
    Presentation.subst (Presentation.subst0 argument)
        (Presentation.rename wk term) = term := by
  exact inst0_rename_wk argument term

@[simp] theorem open_weakened_under_one
    (argument term : Tower.Tm n) :
    Presentation.subst
        (Presentation.liftSub (Presentation.subst0 argument))
        (Presentation.rename wk (Presentation.rename wk term)) =
      Presentation.rename wk term := by
  rw [Presentation.subst_liftSub_wk]
  change Presentation.rename wk
      (Presentation.inst0 argument (Presentation.rename wk term)) =
    Presentation.rename wk term
  rw [inst0_rename_wk]

@[simp] theorem open_weakened_under_two
    (argument term : Tower.Tm n) :
    Presentation.subst
        (Presentation.liftSub
          (Presentation.liftSub (Presentation.subst0 argument)))
        (Presentation.rename wk
          (Presentation.rename wk (Presentation.rename wk term))) =
      Presentation.rename wk (Presentation.rename wk term) := by
  rw [Presentation.subst_liftSub_wk, open_weakened_under_one]

@[simp] theorem open_weakened_under_three
    (argument term : Tower.Tm n) :
    Presentation.subst
        (Presentation.liftSub
          (Presentation.liftSub
            (Presentation.liftSub (Presentation.subst0 argument))))
        (Presentation.rename wk
          (Presentation.rename wk
            (Presentation.rename wk (Presentation.rename wk term)))) =
      Presentation.rename wk
        (Presentation.rename wk (Presentation.rename wk term)) := by
  rw [Presentation.subst_liftSub_wk, open_weakened_under_two]

@[simp] theorem open_weakened_under_four
    (argument term : Tower.Tm n) :
    Presentation.subst
        (Presentation.liftSub
          (Presentation.liftSub
            (Presentation.liftSub
              (Presentation.liftSub (Presentation.subst0 argument)))))
        (Presentation.rename wk
          (Presentation.rename wk
            (Presentation.rename wk
              (Presentation.rename wk (Presentation.rename wk term))))) =
      Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk (Presentation.rename wk term))) := by
  rw [Presentation.subst_liftSub_wk, open_weakened_under_three]

@[simp] theorem open_weakened_under_five
    (argument term : Tower.Tm n) :
    Presentation.subst
        (Presentation.liftSub
          (Presentation.liftSub
            (Presentation.liftSub
              (Presentation.liftSub
                (Presentation.liftSub
                  (Presentation.subst0 argument))))))
        (Presentation.rename wk
          (Presentation.rename wk
            (Presentation.rename wk
              (Presentation.rename wk
                (Presentation.rename wk
                  (Presentation.rename wk term)))))) =
      Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk
            (Presentation.rename wk (Presentation.rename wk term)))) := by
  rw [Presentation.subst_liftSub_wk, open_weakened_under_four]

@[simp] theorem liftSub_five_subst0_at_five (argument : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub
          (Presentation.liftSub
            (Presentation.liftSub
              (Presentation.liftSub (Presentation.subst0 argument)))))
        (5 : Fin (n + 6)) =
      Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk
            (Presentation.rename wk (Presentation.rename wk argument)))) := by
  rfl

@[simp] theorem liftSub_four_subst0_at_four (argument : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub
          (Presentation.liftSub
            (Presentation.liftSub (Presentation.subst0 argument))))
        (4 : Fin (n + 5)) =
      Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk (Presentation.rename wk argument))) := by
  rfl

@[simp] theorem liftSub_three_subst0_at_three (argument : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub
          (Presentation.liftSub (Presentation.subst0 argument)))
        (3 : Fin (n + 4)) =
      Presentation.rename wk
        (Presentation.rename wk (Presentation.rename wk argument)) := by
  rfl

@[simp] theorem liftSub_two_subst0_at_two (argument : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub (Presentation.subst0 argument))
        (2 : Fin (n + 3)) =
      Presentation.rename wk (Presentation.rename wk argument) := by
  rfl

@[simp] theorem liftSub_one_subst0_at_one (argument : Tower.Tm n) :
    Presentation.liftSub (Presentation.subst0 argument)
        (1 : Fin (n + 2)) =
      Presentation.rename wk argument := by
  rfl

@[simp] theorem liftSub_two_subst0_at_one (argument : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub (Presentation.subst0 argument))
        (1 : Fin (n + 3)) = (.var 1 : Tower.Tm (n + 2)) := by
  rfl

@[simp] theorem liftSub_one_subst0_at_zero (argument : Tower.Tm n) :
    Presentation.liftSub (Presentation.subst0 argument)
        (0 : Fin (n + 2)) = (.var 0 : Tower.Tm (n + 1)) := by
  rfl

@[simp] theorem liftSub_two_subst0_at_zero (argument : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub (Presentation.subst0 argument))
        (0 : Fin (n + 3)) = (.var 0 : Tower.Tm (n + 2)) := by
  rfl

@[simp] theorem subst_subst0_var_zero (argument : Tower.Tm n) :
    Presentation.subst (Presentation.subst0 argument)
        (.var 0 : Tower.Tm (n + 1)) = argument := by
  rfl

@[simp] theorem subst_sortTm (substitution : Sub Tower.Head n m)
    (level : LevelExpr) :
    Presentation.subst substitution (sortTm level) = sortTm level := by
  rfl

@[simp] theorem liftSub_five_subst0_at_four (argument : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub
          (Presentation.liftSub
            (Presentation.liftSub
              (Presentation.liftSub (Presentation.subst0 argument)))))
        (4 : Fin (n + 6)) = (.var 4 : Tower.Tm (n + 5)) := by
  rfl

@[simp] theorem liftSub_five_subst0_at_three (argument : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub
          (Presentation.liftSub
            (Presentation.liftSub
              (Presentation.liftSub (Presentation.subst0 argument)))))
        (3 : Fin (n + 6)) = (.var 3 : Tower.Tm (n + 5)) := by
  rfl

@[simp] theorem liftSub_five_subst0_at_two (argument : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub
          (Presentation.liftSub
            (Presentation.liftSub
              (Presentation.liftSub (Presentation.subst0 argument)))))
        (2 : Fin (n + 6)) = (.var 2 : Tower.Tm (n + 5)) := by
  rfl

@[simp] theorem liftSub_four_subst0_at_three (argument : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub
          (Presentation.liftSub
            (Presentation.liftSub (Presentation.subst0 argument))))
        (3 : Fin (n + 5)) = (.var 3 : Tower.Tm (n + 4)) := by
  rfl

@[simp] theorem liftSub_four_subst0_at_two (argument : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub
          (Presentation.liftSub
            (Presentation.liftSub (Presentation.subst0 argument))))
        (2 : Fin (n + 5)) = (.var 2 : Tower.Tm (n + 4)) := by
  rfl

@[simp] theorem liftSub_three_subst0_at_two (argument : Tower.Tm n) :
    Presentation.liftSub
        (Presentation.liftSub
          (Presentation.liftSub (Presentation.subst0 argument)))
        (2 : Fin (n + 4)) = (.var 2 : Tower.Tm (n + 3)) := by
  rfl

@[simp] theorem substitute_receiptBodyType (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature) receiptBodyType =
      receiptAtSignatureType signature := by
  simp [receiptBodyType, receiptAtSignatureType, Presentation.subst,
    sortTm]

def receiptMakeAtSignatureType (signature : Tower.Tm n) : Tower.Tm n :=
  .pi (receiptKey signature)
    (.pi (receiptBudget (Presentation.rename wk signature))
      (.pi
        (receiptJudgment
          (Presentation.rename wk (Presentation.rename wk signature)))
        (.pi
          (receiptCost
            (Presentation.rename wk
              (Presentation.rename wk
                (Presentation.rename wk signature))))
          (.pi
            (receiptProvenance
              (Presentation.rename wk
                (Presentation.rename wk
                  (Presentation.rename wk
                    (Presentation.rename wk signature)))))
            (.pi
              (runApp
                (receiptRunSignature
                  (Presentation.rename wk
                    (Presentation.rename wk
                      (Presentation.rename wk
                        (Presentation.rename wk
                          (Presentation.rename wk signature))))))
                (.var 2))
              (receiptApp
                (Presentation.rename wk
                  (Presentation.rename wk
                    (Presentation.rename wk
                      (Presentation.rename wk
                        (Presentation.rename wk
                          (Presentation.rename wk signature))))))
                (.var 5) (.var 4) (.var 3)))))))

@[simp] theorem substitute_receiptMakeBodyType (signature : Tower.Tm n) :
    Presentation.subst (fun _ : Fin 1 => signature) receiptMakeBodyType =
      receiptMakeAtSignatureType signature := by
  simp [receiptMakeBodyType, receiptMakeAtSignatureType,
    Presentation.subst]

@[simp] theorem inst0_receiptBudget_wk
    (argument signature : Tower.Tm n) :
    Presentation.inst0 argument
        (receiptBudget (Presentation.rename wk signature)) =
      receiptBudget signature := by
  change receiptBudget
      (Presentation.inst0 argument (Presentation.rename wk signature)) =
    receiptBudget signature
  rw [inst0_rename_wk]

@[simp] theorem inst0_receiptCost_wk
    (argument signature : Tower.Tm n) :
    Presentation.inst0 argument
        (receiptCost (Presentation.rename wk signature)) =
      receiptCost signature := by
  change receiptCost
      (Presentation.inst0 argument (Presentation.rename wk signature)) =
    receiptCost signature
  rw [inst0_rename_wk]

@[simp] theorem inst0_receiptProvenance_wk
    (argument signature : Tower.Tm n) :
    Presentation.inst0 argument
        (receiptProvenance (Presentation.rename wk signature)) =
      receiptProvenance signature := by
  change receiptProvenance
      (Presentation.inst0 argument (Presentation.rename wk signature)) =
    receiptProvenance signature
  rw [inst0_rename_wk]

@[simp] theorem inst0_receiptKey_wk
    (argument signature : Tower.Tm n) :
    Presentation.inst0 argument
        (receiptKey (Presentation.rename wk signature)) =
      receiptKey signature := by
  change receiptKey
      (Presentation.inst0 argument (Presentation.rename wk signature)) =
    receiptKey signature
  rw [inst0_rename_wk]

@[simp] theorem inst0_receiptJudgment_wk
    (argument signature : Tower.Tm n) :
    Presentation.inst0 argument
        (receiptJudgment (Presentation.rename wk signature)) =
      receiptJudgment signature := by
  change receiptJudgment
      (Presentation.inst0 argument (Presentation.rename wk signature)) =
    receiptJudgment signature
  rw [inst0_rename_wk]

/-! Opening the indexed family telescope one binder at a time keeps the
requested budget and judgment domains visibly tied to the same signature. -/

def receiptAfterKeyType (signature : Tower.Tm n) : Tower.Tm n :=
  .pi (receiptBudget signature)
    (.pi (receiptJudgment (Presentation.rename wk signature))
      (sortTm receiptLevel))

def receiptAfterBudgetType (signature : Tower.Tm n) : Tower.Tm n :=
  .pi (receiptJudgment signature) (sortTm receiptLevel)

/-- Constructor telescope after supplying its authority key.  The supplied
key is weakened beneath the five fields that remain; it is not erased from
the result index. -/
def receiptMakeAfterKeyType (signature key : Tower.Tm n) : Tower.Tm n :=
  .pi (receiptBudget signature)
    (.pi (receiptJudgment (Presentation.rename wk signature))
      (.pi
        (receiptCost
          (Presentation.rename wk (Presentation.rename wk signature)))
        (.pi
          (receiptProvenance
            (Presentation.rename wk
              (Presentation.rename wk
                (Presentation.rename wk signature))))
          (.pi
            (runApp
              (receiptRunSignature
                (Presentation.rename wk
                  (Presentation.rename wk
                    (Presentation.rename wk
                      (Presentation.rename wk signature)))))
              (.var 2))
            (receiptApp
              (Presentation.rename wk
                (Presentation.rename wk
                  (Presentation.rename wk
                    (Presentation.rename wk
                      (Presentation.rename wk signature)))))
              (Presentation.rename wk
                (Presentation.rename wk
                  (Presentation.rename wk
                    (Presentation.rename wk
                      (Presentation.rename wk key)))))
              (.var 4) (.var 3))))))

def receiptMakeAfterBudgetType
    (signature key budget : Tower.Tm n) : Tower.Tm n :=
  .pi (receiptJudgment signature)
    (.pi (receiptCost (Presentation.rename wk signature))
      (.pi
        (receiptProvenance
          (Presentation.rename wk (Presentation.rename wk signature)))
        (.pi
          (runApp
            (receiptRunSignature
              (Presentation.rename wk
                (Presentation.rename wk
                  (Presentation.rename wk signature))))
            (.var 2))
          (receiptApp
            (Presentation.rename wk
              (Presentation.rename wk
                (Presentation.rename wk
                  (Presentation.rename wk signature))))
            (Presentation.rename wk
              (Presentation.rename wk
                (Presentation.rename wk
                  (Presentation.rename wk key))))
            (Presentation.rename wk
              (Presentation.rename wk
                (Presentation.rename wk
                  (Presentation.rename wk budget))))
            (.var 3)))))

def receiptMakeAfterJudgmentType
    (signature key budget judgment : Tower.Tm n) : Tower.Tm n :=
  .pi (receiptCost signature)
    (.pi (receiptProvenance (Presentation.rename wk signature))
      (.pi
        (runApp
          (receiptRunSignature
            (Presentation.rename wk (Presentation.rename wk signature)))
          (Presentation.rename wk (Presentation.rename wk judgment)))
        (receiptApp
          (Presentation.rename wk
            (Presentation.rename wk (Presentation.rename wk signature)))
          (Presentation.rename wk
            (Presentation.rename wk (Presentation.rename wk key)))
          (Presentation.rename wk
            (Presentation.rename wk (Presentation.rename wk budget)))
          (Presentation.rename wk
            (Presentation.rename wk (Presentation.rename wk judgment))))))

def receiptMakeAfterSpentType
    (signature key budget judgment : Tower.Tm n) : Tower.Tm n :=
  .pi (receiptProvenance signature)
    (.pi
      (runApp
        (receiptRunSignature (Presentation.rename wk signature))
        (Presentation.rename wk judgment))
      (receiptApp
        (Presentation.rename wk (Presentation.rename wk signature))
        (Presentation.rename wk (Presentation.rename wk key))
        (Presentation.rename wk (Presentation.rename wk budget))
        (Presentation.rename wk (Presentation.rename wk judgment))))

def receiptMakeAfterProvenanceType
    (signature key budget judgment : Tower.Tm n) : Tower.Tm n :=
  .pi (runApp (receiptRunSignature signature) judgment)
    (receiptApp (Presentation.rename wk signature)
      (Presentation.rename wk key) (Presentation.rename wk budget)
      (Presentation.rename wk judgment))

@[simp] theorem inst0_receiptAfterKeyType
    (key signature : Tower.Tm n) :
    Presentation.inst0 key
        (.pi (receiptBudget (Presentation.rename wk signature))
          (.pi
            (receiptJudgment
              (Presentation.rename wk (Presentation.rename wk signature)))
            (sortTm receiptLevel))) =
      receiptAfterKeyType signature := by
  have openedSignature :
      Presentation.subst (Presentation.subst0 key)
          (Presentation.rename wk signature) = signature := by
    exact inst0_rename_wk key signature
  have openedWeakenedSignature :
      Presentation.subst
          (Presentation.liftSub (Presentation.subst0 key))
          (Presentation.rename wk (Presentation.rename wk signature)) =
        Presentation.rename wk signature := by
    rw [Presentation.subst_liftSub_wk, openedSignature]
  unfold Presentation.inst0 receiptAfterKeyType sortTm
  simp only [Presentation.subst]
  rw [subst_receiptBudget, openedSignature, subst_receiptJudgment,
    openedWeakenedSignature]

@[simp] theorem inst0_receiptAfterBudgetType
    (budget signature : Tower.Tm n) :
    Presentation.inst0 budget
        (.pi (receiptJudgment (Presentation.rename wk signature))
          (sortTm receiptLevel)) =
      receiptAfterBudgetType signature := by
  have openedSignature :
      Presentation.subst (Presentation.subst0 budget)
          (Presentation.rename wk signature) = signature := by
    exact inst0_rename_wk budget signature
  unfold Presentation.inst0 receiptAfterBudgetType sortTm
  simp only [Presentation.subst]
  rw [subst_receiptJudgment, openedSignature]

def receiptMotiveType : Tower.Tm 1 :=
  .pi (receiptKey (.var 0))
    (.pi (receiptBudget (.var 1))
      (.pi (receiptJudgment (.var 2))
        (.pi (receiptApp (.var 3) (.var 2) (.var 1) (.var 0))
          (sortTm receiptMotiveLevel))))

def receiptMakeCaseType : Tower.Tm 2 :=
  .pi (receiptKey (.var 1))
    (.pi (receiptBudget (.var 2))
      (.pi (receiptJudgment (.var 3))
        (.pi (receiptCost (.var 4))
          (.pi (receiptProvenance (.var 5))
            (.pi (runApp (receiptRunSignature (.var 6)) (.var 2))
              (receiptMotiveApp (.var 6) (.var 5) (.var 4) (.var 3)
                (receiptMakeApp (.var 7) (.var 5) (.var 4) (.var 3)
                  (.var 2) (.var 1) (.var 0))))))))

def receiptEliminateResultType : Tower.Tm 2 :=
  .pi (receiptKey (.var 1))
    (.pi (receiptBudget (.var 2))
      (.pi (receiptJudgment (.var 3))
        (.pi (receiptApp (.var 4) (.var 2) (.var 1) (.var 0))
          (receiptMotiveApp (.var 4) (.var 3) (.var 2) (.var 1)
            (.var 0)))))

def receiptEliminateBodyType : Tower.Tm 1 :=
  .pi receiptMotiveType
    (.pi receiptMakeCaseType
      (Presentation.rename wk receiptEliminateResultType))

def receiptEliminateType : Tower.Tm 0 :=
  .pi receiptSignatureType receiptEliminateBodyType

/-! ## Proof-relevant computation generators -/

inductive ReceiptIotaEvidence (n : Nat) :
    Tower.Tm n → Tower.Tm n → Type where
  | make (signature motive makeCase key budget judgment spent provenance result :
      Tower.Tm n) :
      ReceiptIotaEvidence n
        (receiptEliminateApp signature motive makeCase key budget judgment
          (receiptMakeApp signature key budget judgment spent provenance result))
        (.app
          (.app
            (.app
              (.app
                (.app
                  (.app makeCase key)
                  budget)
                judgment)
              spent)
            provenance)
          result)

def ReceiptIotaEvidence.rename {left right : Tower.Tm n}
    (step : ReceiptIotaEvidence n left right) (renameMap : Ren n m) :
    ReceiptIotaEvidence m (Presentation.rename renameMap left)
      (Presentation.rename renameMap right) := by
  cases step with
  | make => exact .make _ _ _ _ _ _ _ _ _

def ReceiptIotaEvidence.substitute {left right : Tower.Tm n}
    (step : ReceiptIotaEvidence n left right)
    (substitution : Sub Tower.Head n m) :
    ReceiptIotaEvidence m (Presentation.subst substitution left)
      (Presentation.subst substitution right) := by
  cases step with
  | make => exact .make _ _ _ _ _ _ _ _ _

def proofRelevantReceiptComputation :
    ProofRelevantRootComputation Tower.Head where
  Evidence := ReceiptIotaEvidence _
  rename := by
    intro n m renameMap left right step
    exact step.rename renameMap
  substitute := by
    intro n m substitution left right step
    exact step.substitute substitution

def receiptComputation : RootComputation Tower.Head :=
  proofRelevantReceiptComputation.support

/-! ## Declaration signature layered over intrinsic Run -/

def receiptDeclarations : List (DeclName × Entry Tower.Head) :=
  [(receiptName, { type := receiptType }),
   (receiptMakeName, { type := receiptMakeType }),
   (receiptEliminateName, { type := receiptEliminateType })]

def rawReceiptSignature : Signature Tower.Head where
  entries := (Signature.ofList receiptDeclarations).entries
  computation := receiptComputation

abbrev receiptRules : Rules Tower.Head :=
  extendRules runRules rawReceiptSignature

@[simp] theorem typeOf_receipt :
    rawReceiptSignature.typeOf? receiptName = some receiptType := by
  simp [rawReceiptSignature, receiptDeclarations, receiptName,
    receiptMakeName, receiptEliminateName, Signature.ofList,
    Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_receiptMake :
    rawReceiptSignature.typeOf? receiptMakeName = some receiptMakeType := by
  simp [rawReceiptSignature, receiptDeclarations, receiptName,
    receiptMakeName, receiptEliminateName, Signature.ofList,
    Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_receiptEliminate :
    rawReceiptSignature.typeOf? receiptEliminateName =
      some receiptEliminateType := by
  simp [rawReceiptSignature, receiptDeclarations, receiptName,
    receiptMakeName, receiptEliminateName, Signature.ofList,
    Signature.insert, Signature.typeOf?]

/-! ## Typing in the receipt-extended calculus -/

abbrev ReceiptHasType {n : Nat} :=
  @Presentation.HasType Tower.Head receiptRules n

def includeRunTyping {context : Tower.Ctx n}
    {term type : Tower.Tm n}
    (typing : RunHasType context term type) :
    ReceiptHasType context term type :=
  Presentation.Declaration.HasType.includeSignature runRules
    rawReceiptSignature typing

private theorem declaredReceiptConstant_hasType
    {name : DeclName} {type : Tower.Tm 0}
    (lookup : rawReceiptSignature.typeOf? name = some type)
    {context : Tower.Ctx n} :
    ReceiptHasType context (.const name) (liftClosed type) := by
  apply Presentation.HasType.const
  change combinedType runRules rawReceiptSignature name = some type
  apply combinedType_of_signature
  · by_cases isReceipt : name = receiptName
    · subst name
      simp [runRules, outcomeRules, extendRules, combinedType, Tower.rules,
        rawRunSignature, runDeclarations, rawOutcomeSignature,
        outcomeDeclarations, receiptName, runName, runOkName, runFaultName,
        runEliminateName, outcomeName, establishedName, refutedName,
        outsideFragmentName, incompleteName, outcomeEliminateName,
        Signature.typeOf?, Signature.ofList, Signature.insert,
        Signature.empty]
    by_cases isMake : name = receiptMakeName
    · subst name
      simp [runRules, outcomeRules, extendRules, combinedType, Tower.rules,
        rawRunSignature, runDeclarations, rawOutcomeSignature,
        outcomeDeclarations, receiptMakeName, runName, runOkName,
        runFaultName, runEliminateName, outcomeName, establishedName,
        refutedName, outsideFragmentName, incompleteName,
        outcomeEliminateName, Signature.typeOf?, Signature.ofList,
        Signature.insert, Signature.empty]
    by_cases isEliminate : name = receiptEliminateName
    · subst name
      simp [runRules, outcomeRules, extendRules, combinedType, Tower.rules,
        rawRunSignature, runDeclarations, rawOutcomeSignature,
        outcomeDeclarations, receiptEliminateName, runName, runOkName,
        runFaultName, runEliminateName, outcomeName, establishedName,
        refutedName, outsideFragmentName, incompleteName,
        outcomeEliminateName, Signature.typeOf?, Signature.ofList,
        Signature.insert, Signature.empty]
    · simp [rawReceiptSignature, receiptDeclarations, Signature.typeOf?,
        Signature.ofList, Signature.insert, Signature.empty, isReceipt,
        isMake, isEliminate] at lookup
  · exact lookup

theorem receiptConstant_hasType {context : Tower.Ctx n} :
    ReceiptHasType context (.const receiptName)
      (liftClosed receiptType) :=
  declaredReceiptConstant_hasType typeOf_receipt

theorem receiptMakeConstant_hasType {context : Tower.Ctx n} :
    ReceiptHasType context (.const receiptMakeName)
      (liftClosed receiptMakeType) :=
  declaredReceiptConstant_hasType typeOf_receiptMake

theorem receiptEliminateConstant_hasType {context : Tower.Ctx n} :
    ReceiptHasType context (.const receiptEliminateName)
      (liftClosed receiptEliminateType) :=
  declaredReceiptConstant_hasType typeOf_receiptEliminate

theorem runConstant_hasReceiptType {context : Tower.Ctx n} :
    ReceiptHasType context (.const runName) (liftClosed runType) :=
  includeRunTyping runConstant_hasType

theorem receiptSignatureType_hasReceiptType :
    ReceiptHasType (.nil : Tower.Ctx 0) receiptSignatureType
      (sortTm receiptSignatureLevel) :=
  includeRunTyping receiptSignatureType_hasType

theorem receiptApp_hasType {context : Tower.Ctx n}
    {signature key budget judgment : Tower.Tm n}
    (signatureTyping : ReceiptHasType context signature
      (liftClosed receiptSignatureType))
    (keyTyping : ReceiptHasType context key (receiptKey signature))
    (budgetTyping : ReceiptHasType context budget (receiptBudget signature))
    (judgmentTyping : ReceiptHasType context judgment
      (receiptJudgment signature)) :
    ReceiptHasType context (receiptApp signature key budget judgment)
      (sortTm receiptLevel) := by
  have afterSignature := Presentation.HasType.appElim
    (receiptConstant_hasType (context := context)) signatureTyping
  have afterSignatureNormalized :
      ReceiptHasType context (.app (.const receiptName) signature)
        (receiptAtSignatureType signature) := by
    simpa only [receiptType, liftClosed,
      inst0_rename_liftRen_elim0, substitute_receiptBodyType] using
      afterSignature
  have afterKey := Presentation.HasType.appElim afterSignatureNormalized
    keyTyping
  have afterKeyNormalized :
      ReceiptHasType context
        (.app (.app (.const receiptName) signature) key)
        (receiptAfterKeyType signature) := by
    simpa only [receiptAtSignatureType, inst0_receiptAfterKeyType] using
      afterKey
  have afterBudget := Presentation.HasType.appElim afterKeyNormalized
    budgetTyping
  have afterBudgetNormalized :
      ReceiptHasType context
        (.app (.app (.app (.const receiptName) signature) key) budget)
        (receiptAfterBudgetType signature) := by
    simpa only [receiptAfterKeyType, inst0_receiptAfterBudgetType] using
      afterBudget
  have afterJudgment := Presentation.HasType.appElim afterBudgetNormalized
    judgmentTyping
  simpa only [receiptApp, receiptAfterBudgetType,
    Presentation.inst0, Presentation.subst, sortTm] using afterJudgment

theorem receiptRunApp_hasType {context : Tower.Ctx n}
    {signature judgment : Tower.Tm n}
    (signatureTyping : ReceiptHasType context signature
      (liftClosed receiptSignatureType))
    (judgmentTyping : ReceiptHasType context judgment
      (receiptJudgment signature)) :
    ReceiptHasType context
      (runApp (receiptRunSignature signature) judgment)
      (sortTm runLevel) := by
  apply runApp_hasTypeWith runConstant_hasReceiptType
  · exact receiptRunSignature_hasType signatureTyping
  · simpa [receiptJudgment] using judgmentTyping

theorem receiptMakeApp_hasType {context : Tower.Ctx n}
    {signature key budget judgment spent provenance result : Tower.Tm n}
    (signatureTyping : ReceiptHasType context signature
      (liftClosed receiptSignatureType))
    (keyTyping : ReceiptHasType context key (receiptKey signature))
    (budgetTyping : ReceiptHasType context budget (receiptBudget signature))
    (judgmentTyping : ReceiptHasType context judgment
      (receiptJudgment signature))
    (spentTyping : ReceiptHasType context spent (receiptCost signature))
    (provenanceTyping : ReceiptHasType context provenance
      (receiptProvenance signature))
    (resultTyping : ReceiptHasType context result
      (runApp (receiptRunSignature signature) judgment)) :
    ReceiptHasType context
      (receiptMakeApp signature key budget judgment spent provenance result)
      (receiptApp signature key budget judgment) := by
  have afterSignature := Presentation.HasType.appElim
    (receiptMakeConstant_hasType (context := context)) signatureTyping
  have afterSignatureNormalized :
      ReceiptHasType context (.app (.const receiptMakeName) signature)
        (receiptMakeAtSignatureType signature) := by
    simpa only [receiptMakeType, liftClosed,
      inst0_rename_liftRen_elim0, substitute_receiptMakeBodyType] using
      afterSignature
  have afterKey := Presentation.HasType.appElim afterSignatureNormalized
    keyTyping
  have afterKeyNormalized :
      ReceiptHasType context
        (.app (.app (.const receiptMakeName) signature) key)
        (receiptMakeAfterKeyType signature key) := by
    have normalized := afterKey
    simp only [Presentation.inst0, Presentation.subst] at normalized
    simp only [subst_receiptBudget,
      subst_receiptJudgment, subst_receiptCost, subst_receiptProvenance,
      subst_receiptRunSignature, subst_runApp, subst_receiptApp,
      open_weakened_under_zero,
      open_weakened_under_one, open_weakened_under_two,
      open_weakened_under_three, open_weakened_under_four,
      open_weakened_under_five] at normalized
    simpa only [receiptMakeAfterKeyType, Presentation.subst,
      liftSub_five_subst0_at_five, liftSub_five_subst0_at_four,
      liftSub_five_subst0_at_three, liftSub_five_subst0_at_two,
      liftSub_four_subst0_at_two] using
      normalized
  have afterBudget := Presentation.HasType.appElim afterKeyNormalized
    budgetTyping
  have afterBudgetNormalized :
      ReceiptHasType context
        (.app (.app (.app (.const receiptMakeName) signature) key) budget)
        (receiptMakeAfterBudgetType signature key budget) := by
    have normalized := afterBudget
    simp only [Presentation.inst0, Presentation.subst] at normalized
    simp only [subst_receiptJudgment,
      subst_receiptCost, subst_receiptProvenance,
      subst_receiptRunSignature, subst_runApp, subst_receiptApp,
      open_weakened_under_zero,
      open_weakened_under_one, open_weakened_under_two,
      open_weakened_under_three, open_weakened_under_four] at normalized
    simpa only [receiptMakeAfterBudgetType, Presentation.subst,
      liftSub_four_subst0_at_four,
      liftSub_four_subst0_at_three, liftSub_four_subst0_at_two,
      liftSub_three_subst0_at_two] using
      normalized
  have afterJudgment := Presentation.HasType.appElim afterBudgetNormalized
    judgmentTyping
  have afterJudgmentNormalized :
      ReceiptHasType context
        (.app
          (.app (.app (.app (.const receiptMakeName) signature) key) budget)
          judgment)
        (receiptMakeAfterJudgmentType signature key budget judgment) := by
    have normalized := afterJudgment
    simp only [Presentation.inst0, Presentation.subst] at normalized
    simp only [subst_receiptCost,
      subst_receiptProvenance, subst_receiptRunSignature, subst_runApp,
      subst_receiptApp, open_weakened_under_zero,
      open_weakened_under_one,
      open_weakened_under_two, open_weakened_under_three] at normalized
    simpa only [receiptMakeAfterJudgmentType, Presentation.subst,
      liftSub_three_subst0_at_three,
      liftSub_three_subst0_at_two, liftSub_two_subst0_at_two] using
      normalized
  have afterSpent := Presentation.HasType.appElim afterJudgmentNormalized
    spentTyping
  have afterSpentNormalized :
      ReceiptHasType context
        (.app
          (.app
            (.app (.app (.app (.const receiptMakeName) signature) key)
              budget)
            judgment)
          spent)
        (receiptMakeAfterSpentType signature key budget judgment) := by
    have normalized := afterSpent
    simp only [Presentation.inst0, Presentation.subst] at normalized
    simp only [subst_receiptProvenance,
      subst_receiptRunSignature, subst_runApp, subst_receiptApp,
      open_weakened_under_zero,
      open_weakened_under_one, open_weakened_under_two] at normalized
    simpa only [receiptMakeAfterSpentType, Presentation.subst] using
      normalized
  have afterProvenance := Presentation.HasType.appElim afterSpentNormalized
    provenanceTyping
  have afterProvenanceNormalized :
      ReceiptHasType context
        (.app
          (.app
            (.app
              (.app (.app (.app (.const receiptMakeName) signature) key)
                budget)
              judgment)
            spent)
          provenance)
        (receiptMakeAfterProvenanceType signature key budget judgment) := by
    have normalized := afterProvenance
    simp only [Presentation.inst0, Presentation.subst] at normalized
    simp only [
      subst_receiptRunSignature, subst_runApp, subst_receiptApp,
      open_weakened_under_zero, open_weakened_under_one] at normalized
    simpa only [receiptMakeAfterProvenanceType, Presentation.subst] using
      normalized
  have afterResult := Presentation.HasType.appElim afterProvenanceNormalized
    resultTyping
  have normalized := afterResult
  simp only [Presentation.inst0] at normalized
  simp only [subst_receiptApp, open_weakened_under_zero] at normalized
  simpa only [receiptMakeApp] using
    normalized

/-! ## Formation of the intrinsic family and constructor -/

def receiptContextS : Tower.Ctx 1 :=
  .snoc .nil receiptSignatureType

def receiptContextSK : Tower.Ctx 2 :=
  .snoc receiptContextS (receiptKey (.var 0))

def receiptContextSKB : Tower.Ctx 3 :=
  .snoc receiptContextSK (receiptBudget (.var 1))

def receiptContextSKBJ : Tower.Ctx 4 :=
  .snoc receiptContextSKB (receiptJudgment (.var 2))

def receiptContextSKBJC : Tower.Ctx 5 :=
  .snoc receiptContextSKBJ (receiptCost (.var 3))

def receiptContextSKBJCP : Tower.Ctx 6 :=
  .snoc receiptContextSKBJC (receiptProvenance (.var 4))

def receiptContextSKBJCPR : Tower.Ctx 7 :=
  .snoc receiptContextSKBJCP
    (runApp (receiptRunSignature (.var 5)) (.var 2))

theorem receiptSignatureVar_hasType :
    ReceiptHasType receiptContextS (.var 0)
      (liftClosed receiptSignatureType) := by
  have variableTyping :=
    (Presentation.HasType.var (R := receiptRules)
      (Γ := receiptContextS) (0 : Fin 1))
  have lookupEquality :
      Presentation.Ctx.lookup receiptContextS (0 : Fin 1) =
        liftClosed receiptSignatureType := by
    decide
  simpa only [lookupEquality] using variableTyping

def receiptJudgmentTailLevel : LevelExpr :=
  .max judgmentLevel (.succ receiptLevel)

def receiptBudgetTailDeclarationLevel : LevelExpr :=
  .max receiptBudgetLevel receiptJudgmentTailLevel

def receiptKeyTailDeclarationLevel : LevelExpr :=
  .max receiptKeyLevel receiptBudgetTailDeclarationLevel

def receiptDeclarationLevel : LevelExpr :=
  .max receiptSignatureLevel receiptKeyTailDeclarationLevel

theorem receiptType_hasType :
    ReceiptHasType (.nil : Tower.Ctx 0) receiptType
      (sortTm receiptDeclarationLevel) := by
  unfold receiptType receiptBodyType receiptDeclarationLevel
    receiptKeyTailDeclarationLevel receiptBudgetTailDeclarationLevel
    receiptJudgmentTailLevel
  apply Presentation.HasType.piForm
  · exact receiptSignatureType_hasReceiptType
  · exact .sort receiptSignatureLevel
  · apply Presentation.HasType.piForm
    · apply receiptKey_hasType
      exact receiptSignatureVar_hasType
    · exact .sort receiptKeyLevel
    · apply Presentation.HasType.piForm
      · apply receiptBudget_hasType
        exact Presentation.HasType.var 1
      · exact .sort receiptBudgetLevel
      · apply Presentation.HasType.piForm
        · apply receiptJudgment_hasType
          exact Presentation.HasType.var 2
        · exact .sort judgmentLevel
        · exact .headType (.sort receiptLevel)
        · exact .sort (.succ receiptLevel)
        · exact .sorts judgmentLevel (.succ receiptLevel)
      · exact .sort receiptJudgmentTailLevel
      · exact .sorts receiptBudgetLevel receiptJudgmentTailLevel
    · exact .sort receiptBudgetTailDeclarationLevel
    · exact .sorts receiptKeyLevel receiptBudgetTailDeclarationLevel
  · exact .sort receiptKeyTailDeclarationLevel
  · exact .sorts receiptSignatureLevel receiptKeyTailDeclarationLevel

def receiptMakeResultLevel : LevelExpr :=
  .max runLevel receiptLevel

def receiptMakeProvenanceTailLevel : LevelExpr :=
  .max receiptProvenanceLevel receiptMakeResultLevel

def receiptMakeCostTailLevel : LevelExpr :=
  .max receiptCostLevel receiptMakeProvenanceTailLevel

def receiptMakeJudgmentTailLevel : LevelExpr :=
  .max judgmentLevel receiptMakeCostTailLevel

def receiptMakeBudgetTailLevel : LevelExpr :=
  .max receiptBudgetLevel receiptMakeJudgmentTailLevel

def receiptMakeKeyTailLevel : LevelExpr :=
  .max receiptKeyLevel receiptMakeBudgetTailLevel

def receiptMakeDeclarationLevel : LevelExpr :=
  .max receiptSignatureLevel receiptMakeKeyTailLevel

theorem receiptMakeBodyType_hasType :
    ReceiptHasType receiptContextS receiptMakeBodyType
      (sortTm receiptMakeKeyTailLevel) := by
  unfold receiptMakeBodyType receiptMakeKeyTailLevel
    receiptMakeBudgetTailLevel receiptMakeJudgmentTailLevel
    receiptMakeCostTailLevel receiptMakeProvenanceTailLevel
    receiptMakeResultLevel
  apply Presentation.HasType.piForm
  · apply receiptKey_hasType
    exact receiptSignatureVar_hasType
  · exact .sort receiptKeyLevel
  · apply Presentation.HasType.piForm
    · apply receiptBudget_hasType
      exact Presentation.HasType.var 1
    · exact .sort receiptBudgetLevel
    · apply Presentation.HasType.piForm
      · apply receiptJudgment_hasType
        exact Presentation.HasType.var 2
      · exact .sort judgmentLevel
      · apply Presentation.HasType.piForm
        · apply receiptCost_hasType
          exact Presentation.HasType.var 3
        · exact .sort receiptCostLevel
        · apply Presentation.HasType.piForm
          · apply receiptProvenance_hasType
            exact Presentation.HasType.var 4
          · exact .sort receiptProvenanceLevel
          · apply Presentation.HasType.piForm
            · apply receiptRunApp_hasType
              · exact Presentation.HasType.var 5
              · exact Presentation.HasType.var 2
            · exact .sort runLevel
            · apply receiptApp_hasType
              · exact Presentation.HasType.var 6
              · exact Presentation.HasType.var 5
              · exact Presentation.HasType.var 4
              · exact Presentation.HasType.var 3
            · exact .sort receiptLevel
            · exact .sorts runLevel receiptLevel
          · exact .sort receiptMakeResultLevel
          · exact .sorts receiptProvenanceLevel receiptMakeResultLevel
        · exact .sort receiptMakeProvenanceTailLevel
        · exact .sorts receiptCostLevel receiptMakeProvenanceTailLevel
      · exact .sort receiptMakeCostTailLevel
      · exact .sorts judgmentLevel receiptMakeCostTailLevel
    · exact .sort receiptMakeJudgmentTailLevel
    · exact .sorts receiptBudgetLevel receiptMakeJudgmentTailLevel
  · exact .sort receiptMakeBudgetTailLevel
  · exact .sorts receiptKeyLevel receiptMakeBudgetTailLevel

theorem receiptMakeType_hasType :
    ReceiptHasType (.nil : Tower.Ctx 0) receiptMakeType
      (sortTm receiptMakeDeclarationLevel) := by
  unfold receiptMakeType receiptMakeDeclarationLevel
  apply Presentation.HasType.piForm
  · exact receiptSignatureType_hasReceiptType
  · exact .sort receiptSignatureLevel
  · exact receiptMakeBodyType_hasType
  · exact .sort receiptMakeKeyTailLevel
  · exact .sorts receiptSignatureLevel receiptMakeKeyTailLevel

/-! ### Formation and application of the dependent motive -/

def receiptMotiveAtSignatureType (signature : Tower.Tm n) : Tower.Tm n :=
  .pi (receiptKey signature)
    (.pi (receiptBudget (Presentation.rename wk signature))
      (.pi
        (receiptJudgment
          (Presentation.rename wk (Presentation.rename wk signature)))
        (.pi
          (receiptApp
            (Presentation.rename wk
              (Presentation.rename wk (Presentation.rename wk signature)))
            (.var 2) (.var 1) (.var 0))
          (sortTm receiptMotiveLevel))))

theorem receiptMotiveType_asAtSignature :
    receiptMotiveType = receiptMotiveAtSignatureType (.var 0) := by
  decide

def receiptMotiveAfterKeyType
    (signature key : Tower.Tm n) : Tower.Tm n :=
  .pi (receiptBudget signature)
    (.pi (receiptJudgment (Presentation.rename wk signature))
      (.pi
        (receiptApp
          (Presentation.rename wk (Presentation.rename wk signature))
          (Presentation.rename wk (Presentation.rename wk key))
          (.var 1) (.var 0))
        (sortTm receiptMotiveLevel)))

def receiptMotiveAfterBudgetType
    (signature key budget : Tower.Tm n) : Tower.Tm n :=
  .pi (receiptJudgment signature)
    (.pi
      (receiptApp (Presentation.rename wk signature)
        (Presentation.rename wk key) (Presentation.rename wk budget)
        (.var 0))
      (sortTm receiptMotiveLevel))

def receiptMotiveAfterJudgmentType
    (signature key budget judgment : Tower.Tm n) : Tower.Tm n :=
  .pi (receiptApp signature key budget judgment)
    (sortTm receiptMotiveLevel)

def receiptContextSKBJR : Tower.Ctx 5 :=
  .snoc receiptContextSKBJ
    (receiptApp (.var 3) (.var 2) (.var 1) (.var 0))

def receiptMotiveInnerLevel : LevelExpr :=
  .max receiptLevel (.succ receiptMotiveLevel)

def receiptMotiveJudgmentTailLevel : LevelExpr :=
  .max judgmentLevel receiptMotiveInnerLevel

def receiptMotiveBudgetTailLevel : LevelExpr :=
  .max receiptBudgetLevel receiptMotiveJudgmentTailLevel

def receiptMotiveTypeLevel : LevelExpr :=
  .max receiptKeyLevel receiptMotiveBudgetTailLevel

theorem receiptMotiveType_hasType :
    ReceiptHasType receiptContextS receiptMotiveType
      (sortTm receiptMotiveTypeLevel) := by
  rw [receiptMotiveType_asAtSignature]
  unfold receiptMotiveAtSignatureType receiptMotiveTypeLevel
    receiptMotiveBudgetTailLevel receiptMotiveJudgmentTailLevel
    receiptMotiveInnerLevel
  apply Presentation.HasType.piForm
  · apply receiptKey_hasType
    exact receiptSignatureVar_hasType
  · exact .sort receiptKeyLevel
  · apply Presentation.HasType.piForm
    · apply receiptBudget_hasType
      exact Presentation.HasType.var 1
    · exact .sort receiptBudgetLevel
    · apply Presentation.HasType.piForm
      · apply receiptJudgment_hasType
        exact Presentation.HasType.var 2
      · exact .sort judgmentLevel
      · apply Presentation.HasType.piForm
        · apply receiptApp_hasType
          · exact Presentation.HasType.var 3
          · exact Presentation.HasType.var 2
          · exact Presentation.HasType.var 1
          · exact Presentation.HasType.var 0
        · exact .sort receiptLevel
        · exact .headType (.sort receiptMotiveLevel)
        · exact .sort (.succ receiptMotiveLevel)
        · exact .sorts receiptLevel (.succ receiptMotiveLevel)
      · exact .sort receiptMotiveInnerLevel
      · exact .sorts judgmentLevel receiptMotiveInnerLevel
    · exact .sort receiptMotiveJudgmentTailLevel
    · exact .sorts receiptBudgetLevel receiptMotiveJudgmentTailLevel
  · exact .sort receiptMotiveBudgetTailLevel
  · exact .sorts receiptKeyLevel receiptMotiveBudgetTailLevel

theorem receiptMotiveApp_hasType {context : Tower.Ctx n}
    {signature motive key budget judgment receipt : Tower.Tm n}
    (motiveTyping : ReceiptHasType context motive
      (receiptMotiveAtSignatureType signature))
    (keyTyping : ReceiptHasType context key (receiptKey signature))
    (budgetTyping : ReceiptHasType context budget (receiptBudget signature))
    (judgmentTyping : ReceiptHasType context judgment
      (receiptJudgment signature))
    (receiptTyping : ReceiptHasType context receipt
      (receiptApp signature key budget judgment)) :
    ReceiptHasType context
      (receiptMotiveApp motive key budget judgment receipt)
      (sortTm receiptMotiveLevel) := by
  have afterKey := Presentation.HasType.appElim motiveTyping keyTyping
  have afterKeyNormalized :
      ReceiptHasType context (.app motive key)
        (receiptMotiveAfterKeyType signature key) := by
    have normalized := afterKey
    simp only [Presentation.inst0, Presentation.subst] at normalized
    simp only [subst_receiptBudget, subst_receiptJudgment,
      subst_receiptApp, open_weakened_under_zero,
      open_weakened_under_one, open_weakened_under_two] at normalized
    simp only [Presentation.subst] at normalized
    simpa only [receiptMotiveAfterKeyType, subst_sortTm,
      liftSub_two_subst0_at_two, liftSub_two_subst0_at_one,
      liftSub_two_subst0_at_zero] using normalized
  have afterBudget := Presentation.HasType.appElim afterKeyNormalized
    budgetTyping
  have afterBudgetNormalized :
      ReceiptHasType context (.app (.app motive key) budget)
        (receiptMotiveAfterBudgetType signature key budget) := by
    have normalized := afterBudget
    simp only [Presentation.inst0, Presentation.subst] at normalized
    simp only [subst_receiptJudgment, subst_receiptApp,
      open_weakened_under_zero, open_weakened_under_one] at normalized
    simp only [Presentation.subst] at normalized
    simpa only [receiptMotiveAfterBudgetType, subst_sortTm,
      liftSub_one_subst0_at_one, liftSub_one_subst0_at_zero] using normalized
  have afterJudgment := Presentation.HasType.appElim afterBudgetNormalized
    judgmentTyping
  have afterJudgmentNormalized :
      ReceiptHasType context (.app (.app (.app motive key) budget) judgment)
        (receiptMotiveAfterJudgmentType signature key budget judgment) := by
    have normalized := afterJudgment
    simp only [Presentation.inst0, Presentation.subst] at normalized
    simp only [subst_receiptApp, open_weakened_under_zero] at normalized
    simpa only [receiptMotiveAfterJudgmentType, subst_subst0_var_zero,
      subst_sortTm] using normalized
  have afterReceipt := Presentation.HasType.appElim afterJudgmentNormalized
    receiptTyping
  simpa [receiptMotiveApp, receiptMotiveAfterJudgmentType, sortTm,
    Presentation.inst0, Presentation.subst] using afterReceipt

/-! ### Formation of the constructor case and eliminator result -/

def receiptContextSM : Tower.Ctx 2 :=
  .snoc receiptContextS receiptMotiveType

def receiptContextSMK : Tower.Ctx 3 :=
  .snoc receiptContextSM (receiptKey (.var 1))

def receiptContextSMKB : Tower.Ctx 4 :=
  .snoc receiptContextSMK (receiptBudget (.var 2))

def receiptContextSMKBJ : Tower.Ctx 5 :=
  .snoc receiptContextSMKB (receiptJudgment (.var 3))

def receiptContextSMKBJC : Tower.Ctx 6 :=
  .snoc receiptContextSMKBJ (receiptCost (.var 4))

def receiptContextSMKBJCP : Tower.Ctx 7 :=
  .snoc receiptContextSMKBJC (receiptProvenance (.var 5))

def receiptContextSMKBJCPR : Tower.Ctx 8 :=
  .snoc receiptContextSMKBJCP
    (runApp (receiptRunSignature (.var 6)) (.var 2))

theorem receiptSignatureVarInSM_hasType :
    ReceiptHasType receiptContextSM (.var 1)
      (liftClosed receiptSignatureType) := by
  have variableTyping :=
    (Presentation.HasType.var (R := receiptRules)
      (Γ := receiptContextSM) (1 : Fin 2))
  have lookupEquality :
      Presentation.Ctx.lookup receiptContextSM (1 : Fin 2) =
        liftClosed receiptSignatureType := by
    decide
  simpa only [lookupEquality] using variableTyping

theorem receiptMotiveVarInSM_hasType :
    ReceiptHasType receiptContextSM (.var 0)
      (receiptMotiveAtSignatureType (.var 1)) := by
  have variableTyping :=
    (Presentation.HasType.var (R := receiptRules)
      (Γ := receiptContextSM) (0 : Fin 2))
  have lookupEquality :
      Presentation.Ctx.lookup receiptContextSM (0 : Fin 2) =
        receiptMotiveAtSignatureType (.var 1) := by
    decide
  simpa only [lookupEquality] using variableTyping

def receiptMakeCaseResultLevel : LevelExpr :=
  .max runLevel receiptMotiveLevel

def receiptMakeCaseProvenanceTailLevel : LevelExpr :=
  .max receiptProvenanceLevel receiptMakeCaseResultLevel

def receiptMakeCaseCostTailLevel : LevelExpr :=
  .max receiptCostLevel receiptMakeCaseProvenanceTailLevel

def receiptMakeCaseJudgmentTailLevel : LevelExpr :=
  .max judgmentLevel receiptMakeCaseCostTailLevel

def receiptMakeCaseBudgetTailLevel : LevelExpr :=
  .max receiptBudgetLevel receiptMakeCaseJudgmentTailLevel

def receiptMakeCaseLevel : LevelExpr :=
  .max receiptKeyLevel receiptMakeCaseBudgetTailLevel

theorem receiptMakeCaseType_hasType :
    ReceiptHasType receiptContextSM receiptMakeCaseType
      (sortTm receiptMakeCaseLevel) := by
  unfold receiptMakeCaseType receiptMakeCaseLevel
    receiptMakeCaseBudgetTailLevel receiptMakeCaseJudgmentTailLevel
    receiptMakeCaseCostTailLevel receiptMakeCaseProvenanceTailLevel
    receiptMakeCaseResultLevel
  apply Presentation.HasType.piForm
  · apply receiptKey_hasType
    exact receiptSignatureVarInSM_hasType
  · exact .sort receiptKeyLevel
  · apply Presentation.HasType.piForm
    · apply receiptBudget_hasType
      exact Presentation.HasType.var 2
    · exact .sort receiptBudgetLevel
    · apply Presentation.HasType.piForm
      · apply receiptJudgment_hasType
        exact Presentation.HasType.var 3
      · exact .sort judgmentLevel
      · apply Presentation.HasType.piForm
        · apply receiptCost_hasType
          exact Presentation.HasType.var 4
        · exact .sort receiptCostLevel
        · apply Presentation.HasType.piForm
          · apply receiptProvenance_hasType
            exact Presentation.HasType.var 5
          · exact .sort receiptProvenanceLevel
          · apply Presentation.HasType.piForm
            · apply receiptRunApp_hasType
              · exact Presentation.HasType.var 6
              · exact Presentation.HasType.var 2
            · exact .sort runLevel
            · apply receiptMotiveApp_hasType
              · exact Presentation.HasType.var 6
              · exact Presentation.HasType.var 5
              · exact Presentation.HasType.var 4
              · exact Presentation.HasType.var 3
              · apply receiptMakeApp_hasType
                · exact Presentation.HasType.var 7
                · exact Presentation.HasType.var 5
                · exact Presentation.HasType.var 4
                · exact Presentation.HasType.var 3
                · exact Presentation.HasType.var 2
                · exact Presentation.HasType.var 1
                · exact Presentation.HasType.var 0
            · exact .sort receiptMotiveLevel
            · exact .sorts runLevel receiptMotiveLevel
          · exact .sort receiptMakeCaseResultLevel
          · exact .sorts receiptProvenanceLevel
              receiptMakeCaseResultLevel
        · exact .sort receiptMakeCaseProvenanceTailLevel
        · exact .sorts receiptCostLevel
            receiptMakeCaseProvenanceTailLevel
      · exact .sort receiptMakeCaseCostTailLevel
      · exact .sorts judgmentLevel receiptMakeCaseCostTailLevel
    · exact .sort receiptMakeCaseJudgmentTailLevel
    · exact .sorts receiptBudgetLevel receiptMakeCaseJudgmentTailLevel
  · exact .sort receiptMakeCaseBudgetTailLevel
  · exact .sorts receiptKeyLevel receiptMakeCaseBudgetTailLevel

def receiptEliminateInnerLevel : LevelExpr :=
  .max receiptLevel receiptMotiveLevel

def receiptEliminateJudgmentTailLevel : LevelExpr :=
  .max judgmentLevel receiptEliminateInnerLevel

def receiptEliminateBudgetTailLevel : LevelExpr :=
  .max receiptBudgetLevel receiptEliminateJudgmentTailLevel

def receiptEliminateResultLevel : LevelExpr :=
  .max receiptKeyLevel receiptEliminateBudgetTailLevel

theorem receiptEliminateResultType_hasType :
    ReceiptHasType receiptContextSM receiptEliminateResultType
      (sortTm receiptEliminateResultLevel) := by
  unfold receiptEliminateResultType receiptEliminateResultLevel
    receiptEliminateBudgetTailLevel receiptEliminateJudgmentTailLevel
    receiptEliminateInnerLevel
  apply Presentation.HasType.piForm
  · apply receiptKey_hasType
    exact receiptSignatureVarInSM_hasType
  · exact .sort receiptKeyLevel
  · apply Presentation.HasType.piForm
    · apply receiptBudget_hasType
      exact Presentation.HasType.var 2
    · exact .sort receiptBudgetLevel
    · apply Presentation.HasType.piForm
      · apply receiptJudgment_hasType
        exact Presentation.HasType.var 3
      · exact .sort judgmentLevel
      · apply Presentation.HasType.piForm
        · apply receiptApp_hasType
          · exact Presentation.HasType.var 4
          · exact Presentation.HasType.var 2
          · exact Presentation.HasType.var 1
          · exact Presentation.HasType.var 0
        · exact .sort receiptLevel
        · apply receiptMotiveApp_hasType
          · exact Presentation.HasType.var 4
          · exact Presentation.HasType.var 3
          · exact Presentation.HasType.var 2
          · exact Presentation.HasType.var 1
          · exact Presentation.HasType.var 0
        · exact .sort receiptMotiveLevel
        · exact .sorts receiptLevel receiptMotiveLevel
      · exact .sort receiptEliminateInnerLevel
      · exact .sorts judgmentLevel receiptEliminateInnerLevel
    · exact .sort receiptEliminateJudgmentTailLevel
    · exact .sorts receiptBudgetLevel receiptEliminateJudgmentTailLevel
  · exact .sort receiptEliminateBudgetTailLevel
  · exact .sorts receiptKeyLevel receiptEliminateBudgetTailLevel

def receiptContextSMC : Tower.Ctx 3 :=
  .snoc receiptContextSM receiptMakeCaseType

theorem receiptEliminateResultTypeInSMC_hasType :
    ReceiptHasType receiptContextSMC
      (Presentation.rename wk receiptEliminateResultType)
      (sortTm receiptEliminateResultLevel) := by
  simpa [receiptContextSMC, sortTm, Presentation.rename] using
    receiptEliminateResultType_hasType.weaken
      (extension := receiptMakeCaseType)

def receiptEliminateAfterCaseLevel : LevelExpr :=
  .max receiptMakeCaseLevel receiptEliminateResultLevel

def receiptEliminateBodyLevel : LevelExpr :=
  .max receiptMotiveTypeLevel receiptEliminateAfterCaseLevel

def receiptEliminateDeclarationLevel : LevelExpr :=
  .max receiptSignatureLevel receiptEliminateBodyLevel

theorem receiptEliminateBodyType_hasType :
    ReceiptHasType receiptContextS receiptEliminateBodyType
      (sortTm receiptEliminateBodyLevel) := by
  unfold receiptEliminateBodyType receiptEliminateBodyLevel
    receiptEliminateAfterCaseLevel
  apply Presentation.HasType.piForm
  · exact receiptMotiveType_hasType
  · exact .sort receiptMotiveTypeLevel
  · apply Presentation.HasType.piForm
    · exact receiptMakeCaseType_hasType
    · exact .sort receiptMakeCaseLevel
    · exact receiptEliminateResultTypeInSMC_hasType
    · exact .sort receiptEliminateResultLevel
    · exact .sorts receiptMakeCaseLevel receiptEliminateResultLevel
  · exact .sort receiptEliminateAfterCaseLevel
  · exact .sorts receiptMotiveTypeLevel receiptEliminateAfterCaseLevel

theorem receiptEliminateType_hasType :
    ReceiptHasType (.nil : Tower.Ctx 0) receiptEliminateType
      (sortTm receiptEliminateDeclarationLevel) := by
  unfold receiptEliminateType receiptEliminateDeclarationLevel
  apply Presentation.HasType.piForm
  · exact receiptSignatureType_hasReceiptType
  · exact .sort receiptSignatureLevel
  · exact receiptEliminateBodyType_hasType
  · exact .sort receiptEliminateBodyLevel
  · exact .sorts receiptSignatureLevel receiptEliminateBodyLevel

/-! ### Formed declaration signature -/

@[simp] theorem rawReceiptSignature_valueOf_none (name : DeclName) :
    rawReceiptSignature.valueOf? name = none := by
  by_cases isReceipt : name = receiptName
  · subst name
    simp [rawReceiptSignature, receiptDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty]
  by_cases isMake : name = receiptMakeName
  · subst name
    simp [rawReceiptSignature, receiptDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isReceipt]
  by_cases isEliminate : name = receiptEliminateName
  · subst name
    simp [rawReceiptSignature, receiptDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isReceipt,
      isMake]
  · simp [rawReceiptSignature, receiptDeclarations, Signature.valueOf?,
      Signature.ofList, Signature.insert, Signature.empty, isReceipt,
      isMake, isEliminate]

theorem rawReceiptSignature_types_formed {name : DeclName}
    {type : Tower.Tm 0}
    (lookup : rawReceiptSignature.typeOf? name = some type) :
    ∃ level : Tower.Head,
      runRules.isUniverse level ∧
      ReceiptHasType (.nil : Tower.Ctx 0) type (.head level) := by
  by_cases isReceipt : name = receiptName
  · subst name
    have typeEquality : type = receiptType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort receiptDeclarationLevel, .sort receiptDeclarationLevel,
      receiptType_hasType⟩
  by_cases isMake : name = receiptMakeName
  · subst name
    have typeEquality : type = receiptMakeType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort receiptMakeDeclarationLevel,
      .sort receiptMakeDeclarationLevel, receiptMakeType_hasType⟩
  by_cases isEliminate : name = receiptEliminateName
  · subst name
    have typeEquality : type = receiptEliminateType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort receiptEliminateDeclarationLevel,
      .sort receiptEliminateDeclarationLevel, receiptEliminateType_hasType⟩
  · simp [rawReceiptSignature, receiptDeclarations, Signature.typeOf?,
      Signature.ofList, Signature.insert, Signature.empty, isReceipt,
      isMake, isEliminate] at lookup

theorem rawReceiptSignature_fresh {name : DeclName}
    {entry : Entry Tower.Head}
    (lookup : rawReceiptSignature.entries name = some entry) :
    runRules.constantType name = none := by
  by_cases isReceipt : name = receiptName
  · subst name
    simp [runRules, outcomeRules, extendRules, combinedType, Tower.rules,
      rawRunSignature, runDeclarations, rawOutcomeSignature,
      outcomeDeclarations, receiptName, runName, runOkName, runFaultName,
      runEliminateName, outcomeName, establishedName, refutedName,
      outsideFragmentName, incompleteName, outcomeEliminateName,
      Signature.typeOf?, Signature.ofList, Signature.insert,
      Signature.empty]
  by_cases isMake : name = receiptMakeName
  · subst name
    simp [runRules, outcomeRules, extendRules, combinedType, Tower.rules,
      rawRunSignature, runDeclarations, rawOutcomeSignature,
      outcomeDeclarations, receiptMakeName, runName, runOkName,
      runFaultName, runEliminateName, outcomeName, establishedName,
      refutedName, outsideFragmentName, incompleteName,
      outcomeEliminateName, Signature.typeOf?, Signature.ofList,
      Signature.insert, Signature.empty]
  by_cases isEliminate : name = receiptEliminateName
  · subst name
    simp [runRules, outcomeRules, extendRules, combinedType, Tower.rules,
      rawRunSignature, runDeclarations, rawOutcomeSignature,
      outcomeDeclarations, receiptEliminateName, runName, runOkName,
      runFaultName, runEliminateName, outcomeName, establishedName,
      refutedName, outsideFragmentName, incompleteName,
      outcomeEliminateName, Signature.typeOf?, Signature.ofList,
      Signature.insert, Signature.empty]
  · simp [rawReceiptSignature, receiptDeclarations, Signature.ofList,
      Signature.insert, Signature.empty, isReceipt, isMake,
      isEliminate] at lookup

def rawReceiptSignature_formed : rawReceiptSignature.Formed runRules where
  fresh := rawReceiptSignature_fresh
  types := rawReceiptSignature_types_formed
  values := by
    intro name type value _typeLookup valueLookup
    rw [rawReceiptSignature_valueOf_none] at valueLookup
    cases valueLookup
  noSelfDelta := by
    intro name value valueLookup
    rw [rawReceiptSignature_valueOf_none] at valueLookup
    cases valueLookup

/-! ### Strict positivity -/

def receiptFamilyApplication
    (signature key budget judgment : Tower.Tm n)
    (signatureFree : FreeOf receiptName signature)
    (keyFree : FreeOf receiptName key)
    (budgetFree : FreeOf receiptName budget)
    (judgmentFree : FreeOf receiptName judgment) :
    FamilyApplication receiptName 4
      (receiptApp signature key budget judgment) :=
  .intro [signature, key, budget, judgment] rfl (by
    intro argument membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl
    · exact signatureFree
    · exact keyFree
    · exact budgetFree
    · exact judgmentFree) rfl

/-- Receipt signatures, like their Outcome and Run components, are
structural data and contain no occurrence of the receipt family constant. -/
def receiptSignatureTypeFree : FreeOf receiptName receiptSignatureType := by
  unfold receiptSignatureType receiptSignatureBody sortTm
  exact .sigma (runSignatureTypeFreeOf receiptName)
    (.sigma (.head _)
      (.sigma (.head _)
        (.sigma (.head _) (.head _))))

def receiptMakeConstructorPositive :
    ConstructorType receiptName 4 receiptMakeType := by
  unfold receiptMakeType receiptMakeBodyType receiptKey receiptBudget
    receiptJudgment receiptRunSignature receiptCost receiptProvenance
    runJudgment runOutcomeSignature signatureJudgment runApp receiptApp
  exact .field (.free receiptSignatureTypeFree)
    (.field
      (.free (.snd (.snd (.snd (.snd (.var 0))))))
      (.field
        (.free (.fst (.snd (.var 1))))
        (.field
          (.free (.fst (.fst (.fst (.var 2)))))
          (.field
            (.free (.fst (.snd (.snd (.var 3)))))
            (.field
              (.free (.fst (.snd (.snd (.snd (.var 4))))))
              (.field
                (.free
                  (.app
                    (.app
                      (.const (by decide : runName ≠ receiptName))
                      (.fst (.var 5)))
                    (.var 2)))
                (.result
                  (receiptFamilyApplication (.var 6) (.var 5) (.var 4)
                    (.var 3) (.var 6) (.var 5) (.var 4) (.var 3)))))))))

def receiptMakeConstructorSpec :
    ConstructorSpec rawReceiptSignature receiptName 4 where
  name := receiptMakeName
  type := receiptMakeType
  declared := typeOf_receiptMake
  positive := receiptMakeConstructorPositive

def receiptConstructors :
    List (ConstructorSpec rawReceiptSignature receiptName 4) :=
  [receiptMakeConstructorSpec]

def receiptEliminatorSpec : EliminatorSpec rawReceiptSignature where
  name := receiptEliminateName
  type := receiptEliminateType
  declared := typeOf_receiptEliminate

/-- A receipt in a function domain is rejected as a negative recursive
occurrence, even when every index is family-free. -/
theorem receiptInFunctionDomain_not_strictlyPositive :
    StrictlyPositive receiptName 4
      (.pi
        (receiptApp (.var 3 : Tower.Tm 4) (.var 2) (.var 1) (.var 0))
        (.var 0)) → False :=
  recursivePiDomain_not_strictlyPositive
    (receiptFamilyApplication (.var 3) (.var 2) (.var 1) (.var 0)
      (.var 3) (.var 2) (.var 1) (.var 0)) (.var 0)

/-! ### Canonical typed iota schema -/

/-- The receipt eliminator after its signature, motive, and constructor case
have been supplied. -/
def receiptEliminateAtParameters : Tower.Tm 3 :=
  .app
    (.app
      (.app (.const receiptEliminateName) (.var 2))
      (.var 1))
    (.var 0)

def receiptEliminateAtParametersType : Tower.Tm 3 :=
  .pi (receiptKey (.var 2))
    (.pi (receiptBudget (.var 3))
      (.pi (receiptJudgment (.var 4))
        (.pi (receiptApp (.var 5) (.var 2) (.var 1) (.var 0))
          (receiptMotiveApp (.var 5) (.var 3) (.var 2) (.var 1)
            (.var 0)))))

theorem receiptEliminateAtParameters_hasType :
    ReceiptHasType receiptContextSMC receiptEliminateAtParameters
      receiptEliminateAtParametersType := by
  have afterSignature := Presentation.HasType.appElim
    (receiptEliminateConstant_hasType (context := receiptContextSMC))
    (Presentation.HasType.var 2)
  have afterMotive := Presentation.HasType.appElim afterSignature
    (Presentation.HasType.var 1)
  have afterCase := Presentation.HasType.appElim afterMotive
    (Presentation.HasType.var 0)
  convert afterCase using 1
  all_goals decide

def receiptIotaContextK : Tower.Ctx 4 :=
  .snoc receiptContextSMC (receiptKey (.var 2))

def receiptIotaContextKB : Tower.Ctx 5 :=
  .snoc receiptIotaContextK (receiptBudget (.var 3))

def receiptIotaContextKBJ : Tower.Ctx 6 :=
  .snoc receiptIotaContextKB (receiptJudgment (.var 4))

def receiptIotaContextKBJC : Tower.Ctx 7 :=
  .snoc receiptIotaContextKBJ (receiptCost (.var 5))

def receiptIotaContextKBJCP : Tower.Ctx 8 :=
  .snoc receiptIotaContextKBJC (receiptProvenance (.var 6))

def receiptMakeIotaContext : Tower.Ctx 9 :=
  .snoc receiptIotaContextKBJCP
    (runApp (receiptRunSignature (.var 7)) (.var 2))

def receiptMakeIotaReceiptTerm : Tower.Tm 9 :=
  receiptMakeApp (.var 8) (.var 5) (.var 4) (.var 3)
    (.var 2) (.var 1) (.var 0)

/-- The fully parameterized eliminator weakened beneath the six fields of
the `make` constructor.  Naming this term keeps the typed computation schema
structurally visible: weakening changes the context, not the eliminator. -/
def receiptEliminateAtIotaParameters : Tower.Tm 9 :=
  Presentation.rename wk
    (Presentation.rename wk
      (Presentation.rename wk
        (Presentation.rename wk
          (Presentation.rename wk
            (Presentation.rename wk receiptEliminateAtParameters)))))

def receiptMakeIotaLeft : Tower.Tm 9 :=
  .app
    (.app
      (.app
        (.app
          receiptEliminateAtIotaParameters
          (.var 5))
        (.var 4))
      (.var 3))
    receiptMakeIotaReceiptTerm

def receiptMakeIotaRight : Tower.Tm 9 :=
  .app
    (.app
      (.app
        (.app
          (.app
            (.app (.var 6) (.var 5))
            (.var 4))
          (.var 3))
        (.var 2))
      (.var 1))
    (.var 0)

def receiptMakeIotaType : Tower.Tm 9 :=
  receiptMotiveApp (.var 7) (.var 5) (.var 4) (.var 3)
    receiptMakeIotaReceiptTerm

abbrev ReceiptTypedIotaReceipt (context : Tower.Ctx n)
    (left right type : Tower.Tm n) : Type :=
  ProofRelevantStepReceipt runRules rawReceiptSignature
    proofRelevantReceiptComputation context left right type

theorem receiptMakeIotaLeft_asEliminate :
    receiptMakeIotaLeft =
      receiptEliminateApp (.var 8) (.var 7) (.var 6)
        (.var 5) (.var 4) (.var 3)
        (receiptMakeApp (.var 8) (.var 5) (.var 4) (.var 3)
          (.var 2) (.var 1) (.var 0)) := by
  unfold receiptMakeIotaLeft receiptEliminateAtIotaParameters
    receiptEliminateAtParameters receiptEliminateApp
    receiptMakeIotaReceiptTerm
  rfl

theorem receiptMakeIotaRight_asBranch :
    receiptMakeIotaRight =
      .app
        (.app
          (.app
            (.app
              (.app
                (.app (.var 6) (.var 5))
                (.var 4))
              (.var 3))
            (.var 2))
          (.var 1))
        (.var 0) := rfl

def receiptMakeIotaReceipt :
    ReceiptTypedIotaReceipt receiptMakeIotaContext receiptMakeIotaLeft
      receiptMakeIotaRight receiptMakeIotaType where
  sourceTyping := by
    have constructedTyping := receiptMakeApp_hasType
      (context := receiptMakeIotaContext)
      (signature := (.var 8)) (key := (.var 5)) (budget := (.var 4))
      (judgment := (.var 3)) (spent := (.var 2))
      (provenance := (.var 1)) (result := (.var 0))
      (Presentation.HasType.var 8) (Presentation.HasType.var 5)
      (Presentation.HasType.var 4) (Presentation.HasType.var 3)
      (Presentation.HasType.var 2) (Presentation.HasType.var 1)
      (Presentation.HasType.var 0)
    have underKey := receiptEliminateAtParameters_hasType.weaken
      (extension := receiptKey (.var 2))
    have underBudget := underKey.weaken
      (extension := receiptBudget (.var 3))
    have underJudgment := underBudget.weaken
      (extension := receiptJudgment (.var 4))
    have underCost := underJudgment.weaken
      (extension := receiptCost (.var 5))
    have underProvenance := underCost.weaken
      (extension := receiptProvenance (.var 6))
    have weakened := underProvenance.weaken
      (extension := runApp (receiptRunSignature (.var 7)) (.var 2))
    have afterKey := Presentation.HasType.appElim weakened
      (Presentation.HasType.var 5)
    have afterBudget := Presentation.HasType.appElim afterKey
      (Presentation.HasType.var 4)
    have afterJudgment := Presentation.HasType.appElim afterBudget
      (Presentation.HasType.var 3)
    have source := Presentation.HasType.appElim afterJudgment
      constructedTyping
    unfold receiptMakeIotaLeft receiptEliminateAtIotaParameters
      receiptMakeIotaType receiptMakeIotaReceiptTerm
    convert source using 1
    all_goals rfl
  targetTyping := by
    have afterKey := Presentation.HasType.appElim
      (Presentation.HasType.var (R := receiptRules)
        (Γ := receiptMakeIotaContext) (6 : Fin 9))
      (Presentation.HasType.var 5)
    have afterBudget := Presentation.HasType.appElim afterKey
      (Presentation.HasType.var 4)
    have afterJudgment := Presentation.HasType.appElim afterBudget
      (Presentation.HasType.var 3)
    have afterSpent := Presentation.HasType.appElim afterJudgment
      (Presentation.HasType.var 2)
    have afterProvenance := Presentation.HasType.appElim afterSpent
      (Presentation.HasType.var 1)
    have target := Presentation.HasType.appElim afterProvenance
      (Presentation.HasType.var 0)
    unfold receiptMakeIotaRight receiptMakeIotaType
      receiptMakeIotaReceiptTerm
    convert target using 1
    all_goals rfl
  evidence := by
    change ReceiptIotaEvidence 9 receiptMakeIotaLeft receiptMakeIotaRight
    rw [receiptMakeIotaLeft_asEliminate, receiptMakeIotaRight_asBranch]
    exact ReceiptIotaEvidence.make
      (.var 8) (.var 7) (.var 6) (.var 5) (.var 4) (.var 3)
      (.var 2) (.var 1) (.var 0)

def receiptMakeIotaSchema :
    IotaSchema runRules rawReceiptSignature
      proofRelevantReceiptComputation 9 where
  context := receiptMakeIotaContext
  left := receiptMakeIotaLeft
  right := receiptMakeIotaRight
  type := receiptMakeIotaType
  receipt := receiptMakeIotaReceipt

def receiptEliminateAtParameters_applicationHead :
    ApplicationHead receiptEliminateName receiptEliminateAtParameters :=
  .app (.app (.app .const))

noncomputable def receiptEliminateAtIota_applicationHead :
    ApplicationHead receiptEliminateName
      receiptEliminateAtIotaParameters := by
  have underKey := receiptEliminateAtParameters_applicationHead.rename wk
  have underBudget := underKey.rename wk
  have underJudgment := underBudget.rename wk
  have underCost := underJudgment.rename wk
  have underProvenance := underCost.rename wk
  exact underProvenance.rename wk

def receiptMakeApp_constantOccurrence
    (signature key budget judgment spent provenance result : Tower.Tm n) :
    ConstantOccurrence receiptMakeName
      (receiptMakeApp signature key budget judgment spent provenance result) :=
  .appFunction
    (.appFunction
      (.appFunction
        (.appFunction
          (.appFunction
            (.appFunction
              (.appFunction .here))))))

noncomputable def receiptMakeIotaClause :
    IotaClause runRules rawReceiptSignature
      proofRelevantReceiptComputation
      (receiptConstructors.map ConstructorSpec.name)
      receiptEliminatorSpec.name where
  constructorName := receiptMakeName
  constructorDeclared := by
    simp [receiptConstructors, receiptMakeConstructorSpec]
  arity := 9
  schema := receiptMakeIotaSchema
  eliminatorHead :=
    .app (.app (.app (.app receiptEliminateAtIota_applicationHead)))
  constructorOccurrence :=
    .appArgument
      (receiptMakeApp_constantOccurrence
        (.var 8) (.var 5) (.var 4) (.var 3)
        (.var 2) (.var 1) (.var 0))

noncomputable def receiptIotaClauses :
    List (IotaClause runRules rawReceiptSignature
      proofRelevantReceiptComputation
      (receiptConstructors.map ConstructorSpec.name)
      receiptEliminatorSpec.name) :=
  [receiptMakeIotaClause]

/-- A formed, strictly-positive intrinsic receipt family whose key, requested
budget, and judgment remain visible as indices and whose constructor records
actual cost, provenance, and the proof-relevant run.  It is deliberately a
candidate rather than an `Authorized` family until the selected raw
conversion discipline supplies preservation. -/
noncomputable def receiptCandidate : Candidate runRules where
  signature := rawReceiptSignature
  formed := rawReceiptSignature_formed
  computation := proofRelevantReceiptComputation
  computationSupport := rfl
  familyName := receiptName
  familyParameterCount := 1
  familyIndexCount := 3
  familyType := receiptType
  familyDeclared := typeOf_receipt
  constructors := receiptConstructors
  constructorNamesNodup := by
    change [receiptMakeName].Nodup
    decide
  familyNotConstructor := by
    intro constructor membership
    simp only [receiptConstructors, List.mem_cons, List.not_mem_nil,
      or_false] at membership
    rcases membership with rfl
    decide
  eliminator := receiptEliminatorSpec
  eliminatorNotFamily := by decide
  eliminatorNotConstructor := by
    intro constructor membership
    simp only [receiptConstructors, List.mem_cons, List.not_mem_nil,
      or_false] at membership
    rcases membership with rfl
    decide
  iotaClauses := receiptIotaClauses
  constructorsComputed := by
    intro constructorName membership
    simp [receiptConstructors, receiptMakeConstructorSpec] at membership
    rcases membership with rfl
    simp [receiptIotaClauses, receiptMakeIotaClause]

/-! ## Axiom audit -/

#print axioms receiptSignatureType_hasType
#print axioms parameterReceiptSignatureValue_hasType
#print axioms rawReceiptSignature_formed
#print axioms receiptMakeIotaReceipt
#print axioms receiptCandidate
#print axioms receiptInFunctionDomain_not_strictlyPositive

end Intrinsic
end InternalAuthorityMetatheory
end Mettapedia.Languages.MeTTa.PureKernel.Universe
