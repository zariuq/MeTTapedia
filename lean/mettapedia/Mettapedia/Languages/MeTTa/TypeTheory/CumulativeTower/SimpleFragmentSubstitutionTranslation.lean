import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FourFaceBetaExperiment
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareErasureNaturality
import Mettapedia.GSLT.Core.ContextualLadderBaseCategory

/-!
# Substitution-natural translation of the simple fragment

The simple-function fragment used by the four-face comparison translates into the
cumulative tower on every typed term.  This module proves that the translation
also commutes with arbitrary typed renamings and simultaneous substitutions.
Consequently every intrinsic simple beta cell, not merely the original
identity example, becomes a typed cumulative-tower beta cell.

This is a fragment comparison theorem preserving typing and substitution.
It does not assert injectivity of raw term erasure: internal application types
are discarded. The separate set-family comparison at the end concerns the
families CwF, not the image of this syntactic translation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace SimpleFragmentSubstitutionTranslation

open Presentation
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.MeTTaIL.Syntax
open FourFaceBetaExperiment.IntrinsicSTT
open FourFaceBetaExperiment.TowerDTT
open DeclarationAwareSubstitutionCompiler
open DeclarationAwareSubstitutionLanguage

variable {sourceContext targetContext : List Ty}
variable {selectedType : Ty}

/-! ## Typed variables exactly cover de Bruijn positions -/

/-- The simple type selected by a de Bruijn position in a typed context. -/
def contextTypeAt : (context : List Ty) → Fin context.length → Ty
  | [], index => Fin.elim0 index
  | head :: tail, index =>
      Fin.cases head (fun prior => contextTypeAt tail prior) index

/-- Reconstruct the intrinsically typed variable at a de Bruijn position. -/
def typedVarAt : (context : List Ty) → (index : Fin context.length) →
    Var context (contextTypeAt context index)
  | [], index => Fin.elim0 index
  | _ :: tail, index =>
      Fin.cases .zero (fun prior => .succ (typedVarAt tail prior)) index

/-- Reconstructing a typed variable and then erasing it returns the original
de Bruijn position. -/
@[simp]
theorem eraseVar_typedVarAt (context : List Ty)
    (index : Fin context.length) :
    eraseVar (typedVarAt context index) = index := by
  induction context with
  | nil => exact Fin.elim0 index
  | cons head tail induction =>
      refine Fin.cases ?_ (fun prior => ?_) index
      · rfl
      · change
          Fin.succ (eraseVar (typedVarAt tail prior)) = Fin.succ prior
        exact congrArg Fin.succ (induction prior)

/-! ## Typed renamings become ordinary tower renamings -/

/-- Forget the type index of every component of a typed renaming. -/
def eraseRenaming : {sourceContext targetContext : List Ty} →
    Renaming sourceContext targetContext →
      Presentation.Ren sourceContext.length targetContext.length
  | [], _, _ => fun index => Fin.elim0 index
  | _ :: _, _, ρ =>
      Fin.cases (eraseVar (ρ .zero))
        (fun index =>
          eraseRenaming
            (fun {_type} typedVar => ρ (.succ typedVar)) index)

/-- Erasing a typed renaming at a typed variable is exactly erasing the
renamed variable. -/
@[simp]
theorem eraseRenaming_apply
    (ρ : Renaming sourceContext targetContext)
    (typedVar : Var sourceContext selectedType) :
    eraseRenaming ρ (eraseVar typedVar) =
      eraseVar (ρ typedVar) := by
  induction typedVar generalizing targetContext with
  | zero => rfl
  | succ prior induction =>
      exact induction
        (ρ := fun {_type} typedVar => ρ (.succ typedVar))

/-- Lifting a typed renaming under a binder becomes the ordinary lifted tower
renaming. -/
theorem eraseRenaming_lift
    {binderType : Ty}
    (ρ : Renaming sourceContext targetContext) :
    eraseRenaming (liftRenaming (B := binderType) ρ) =
      Presentation.liftRen (eraseRenaming ρ) := by
  funext index
  refine Fin.cases ?_ (fun prior => ?_) index
  · rfl
  · let typedVar := typedVarAt sourceContext prior
    calc
      eraseRenaming (liftRenaming (B := binderType) ρ) (Fin.succ prior) =
          eraseRenaming
            (fun {_type} typedVariable =>
              liftRenaming (B := binderType) ρ (.succ typedVariable)) prior := rfl
      _ = eraseRenaming
            (fun {_type} typedVariable =>
              liftRenaming (B := binderType) ρ (.succ typedVariable))
            (eraseVar typedVar) := by rw [eraseVar_typedVarAt]
      _ = eraseVar
            (liftRenaming (B := binderType) ρ (.succ typedVar)) :=
        eraseRenaming_apply _ typedVar
      _ = Fin.succ (eraseVar (ρ typedVar)) := rfl
      _ = Fin.succ (eraseRenaming ρ (eraseVar typedVar)) := by
        rw [eraseRenaming_apply]
      _ = Fin.succ (eraseRenaming ρ prior) := by
        rw [eraseVar_typedVarAt]
      _ = Presentation.liftRen (eraseRenaming ρ) (Fin.succ prior) := rfl

/-- Weakening a typed context erases to ordinary de Bruijn weakening. -/
theorem eraseRenaming_weakening
    {binderType : Ty} (context : List Ty) :
    eraseRenaming
        (sourceContext := context) (targetContext := binderType :: context)
        weakening = Presentation.wk := by
  funext index
  let typedVar := typedVarAt context index
  calc
    eraseRenaming weakening index =
        eraseRenaming weakening (eraseVar typedVar) := by
          rw [eraseVar_typedVarAt]
    _ = eraseVar (weakening typedVar) := eraseRenaming_apply weakening typedVar
    _ = Fin.succ (eraseVar typedVar) := rfl
    _ = Fin.succ index := by rw [eraseVar_typedVarAt]
    _ = Presentation.wk index := rfl

/-- Typed term renaming commutes with the simple-fragment translation. -/
@[simp]
theorem eraseTerm_rename
    (ρ : Renaming sourceContext targetContext)
    (term : Term sourceContext selectedType) :
    eraseTerm (term.rename ρ) =
      Presentation.rename (eraseRenaming ρ) (eraseTerm term) := by
  induction term generalizing targetContext with
  | var typedVar =>
      change
        Presentation.Tm.var (eraseVar (ρ typedVar)) =
          Presentation.Tm.var (eraseRenaming ρ (eraseVar typedVar))
      rw [eraseRenaming_apply]
  | @lam context domain codomain body induction =>
      simp only [Term.rename, eraseTerm, Presentation.rename]
      rw [induction, eraseRenaming_lift]
  | app function argument functionInduction argumentInduction =>
      simp only [Term.rename, eraseTerm, Presentation.rename]
      rw [functionInduction, argumentInduction]

/-! ## Typed substitutions become ordinary tower substitutions -/

/-- Forget the type index of every component of a typed simultaneous
substitution. -/
def eraseSubstitution : {sourceContext targetContext : List Ty} →
    Substitution sourceContext targetContext →
      Presentation.Sub Presentation.Tower.Head sourceContext.length
        targetContext.length
  | [], _, _ => fun index => Fin.elim0 index
  | _ :: _, _, σ =>
      Fin.cases (eraseTerm (σ .zero))
        (fun index =>
          eraseSubstitution
            (fun {_type} typedVar => σ (.succ typedVar)) index)

/-- Looking up a typed substitution before or after erasure agrees exactly. -/
@[simp]
theorem eraseSubstitution_apply
    (σ : Substitution sourceContext targetContext)
    (typedVar : Var sourceContext selectedType) :
    eraseSubstitution σ (eraseVar typedVar) =
      eraseTerm (σ typedVar) := by
  induction typedVar generalizing targetContext with
  | zero => rfl
  | succ prior induction =>
      exact induction
        (σ := fun {_type} typedVar => σ (.succ typedVar))

/-- Lifting a typed substitution under a binder becomes the ordinary lifted
tower substitution. -/
theorem eraseSubstitution_lift
    {binderType : Ty}
    (σ : Substitution sourceContext targetContext) :
    eraseSubstitution (liftSubstitution (B := binderType) σ) =
      Presentation.liftSub (eraseSubstitution σ) := by
  funext index
  refine Fin.cases ?_ (fun prior => ?_) index
  · rfl
  · let typedVar := typedVarAt sourceContext prior
    calc
      eraseSubstitution (liftSubstitution (B := binderType) σ)
          (Fin.succ prior) =
        eraseSubstitution
          (fun {_type} typedVariable =>
            liftSubstitution (B := binderType) σ (.succ typedVariable)) prior := rfl
      _ = eraseSubstitution
          (fun {_type} typedVariable =>
            liftSubstitution (B := binderType) σ (.succ typedVariable))
          (eraseVar typedVar) := by rw [eraseVar_typedVarAt]
      _ = eraseTerm
          (liftSubstitution (B := binderType) σ (.succ typedVar)) :=
        eraseSubstitution_apply _ typedVar
      _ = eraseTerm ((σ typedVar).rename weakening) := rfl
      _ = Presentation.rename (eraseRenaming weakening)
          (eraseTerm (σ typedVar)) := eraseTerm_rename weakening (σ typedVar)
      _ = Presentation.rename Presentation.wk
          (eraseTerm (σ typedVar)) := by rw [eraseRenaming_weakening]
      _ = Presentation.rename Presentation.wk
          (eraseSubstitution σ (eraseVar typedVar)) := by
        rw [eraseSubstitution_apply]
      _ = Presentation.rename Presentation.wk
          (eraseSubstitution σ prior) := by rw [eraseVar_typedVarAt]
      _ = Presentation.liftSub (eraseSubstitution σ)
          (Fin.succ prior) := rfl

/-- Simultaneous substitution commutes with the simple-fragment translation. -/
@[simp]
theorem eraseTerm_substitute
    (σ : Substitution sourceContext targetContext)
    (term : Term sourceContext selectedType) :
    eraseTerm (term.substitute σ) =
      Presentation.subst (eraseSubstitution σ) (eraseTerm term) := by
  induction term generalizing targetContext with
  | var typedVar =>
      simp [Term.substitute, eraseTerm]
  | @lam context domain codomain body induction =>
      simp only [Term.substitute, eraseTerm, Presentation.subst]
      rw [induction, eraseSubstitution_lift]
  | app function argument functionInduction argumentInduction =>
      simp only [Term.substitute, eraseTerm, Presentation.subst]
      rw [functionInduction, argumentInduction]

/-- The typed variable substitution erases to the tower's variable
substitution. -/
theorem eraseSubstitution_variables (context : List Ty) :
    eraseSubstitution
        (sourceContext := context) (targetContext := context)
        (fun {_type} typedVar => Term.var typedVar) =
      Presentation.ids := by
  funext index
  let typedVar := typedVarAt context index
  calc
    eraseSubstitution (fun {_type} typedVar => Term.var typedVar) index =
        eraseSubstitution (fun {_type} typedVar => Term.var typedVar)
          (eraseVar typedVar) := by rw [eraseVar_typedVarAt]
    _ = eraseTerm (Term.var typedVar) :=
      eraseSubstitution_apply
        (fun {_type} typedVar => Term.var typedVar) typedVar
    _ = Presentation.Tm.var (eraseVar typedVar) := rfl
    _ = Presentation.Tm.var index := by rw [eraseVar_typedVarAt]
    _ = Presentation.ids index := rfl

/-- The newest-variable substitution is sent to the tower's canonical
single-variable substitution. -/
theorem eraseSubstitution_newest
    (argument : Term targetContext selectedType) :
    eraseSubstitution (newestSubstitution argument) =
      Presentation.subst0 (eraseTerm argument) := by
  funext index
  refine Fin.cases ?_ (fun prior => ?_) index
  · rfl
  · exact congrFun (eraseSubstitution_variables targetContext) prior

/-- Opening the newest binder commutes exactly with the translation. -/
@[simp]
theorem eraseTerm_instantiateNewest
    {targetType : Ty}
    (body : Term (selectedType :: sourceContext) targetType)
    (argument : Term sourceContext selectedType) :
    eraseTerm (body.instantiateNewest argument) =
      Presentation.inst0 (eraseTerm argument) (eraseTerm body) := by
  unfold Term.instantiateNewest Presentation.inst0
  rw [eraseTerm_substitute, eraseSubstitution_newest]

/-! ## Every simple beta cell transports -/

variable {domain codomain : Ty}

/-- Every intrinsically typed simple beta claim maps to a cumulative-tower
beta step with both endpoints typed at the embedded result type. -/
theorem betaClaim_typed
    (claim : BetaClaim sourceContext domain codomain) :
    StepCore Presentation.Tower.rules.computation
        Presentation.Tower.rules.headEq
        (eraseTerm claim.source) (eraseTerm claim.target) ∧
      Presentation.Tower.HasType (eraseContext sourceContext)
        (eraseTerm claim.source)
        (eraseTypeAt sourceContext.length codomain) ∧
      Presentation.Tower.HasType (eraseContext sourceContext)
        (eraseTerm claim.target)
        (eraseTypeAt sourceContext.length codomain) := by
  have transported := Presentation.HasType.typedBeta
    (eraseTerm_hasType claim.body) (eraseTerm_hasType claim.argument)
  simpa [BetaClaim.source, BetaClaim.target, eraseTerm,
    eraseTerm_instantiateNewest, Presentation.inst0] using transported

/-! ## Every simple beta cell reaches the first-order checker -/

/-- First-order erasure of every intrinsic newest-variable opening is the
independently defined raw substitution function. -/
@[simp]
theorem rawErase_instantiateNewest
    {targetType : Ty}
    (body : Term (selectedType :: sourceContext) targetType)
    (argument : Term sourceContext selectedType) :
    FourFaceBetaExperiment.DeepGSLT.rawErase
        (body.instantiateNewest argument) =
      substituteRaw 0
        (FourFaceBetaExperiment.DeepGSLT.rawErase argument)
        (FourFaceBetaExperiment.DeepGSLT.rawErase body) := by
  calc
    FourFaceBetaExperiment.DeepGSLT.rawErase
        (body.instantiateNewest argument) =
      DeclarationAwareSubstitutionSemantics.erase
        (eraseTerm (body.instantiateNewest argument)) :=
      FourFaceBetaExperiment.DeepGSLT.rawErase_eq_eraseTower _
    _ = DeclarationAwareSubstitutionSemantics.erase
        (Presentation.inst0 (eraseTerm argument) (eraseTerm body)) := by
      rw [eraseTerm_instantiateNewest]
    _ = DeclarationAwareSubstitutionSemantics.substituteAt 0
        (DeclarationAwareSubstitutionSemantics.erase (eraseTerm argument))
        (DeclarationAwareSubstitutionSemantics.erase (eraseTerm body)) :=
      DeclarationAwareErasureNaturality.erase_inst0
        (eraseTerm argument) (eraseTerm body)
    _ = substituteRaw 0
        (FourFaceBetaExperiment.DeepGSLT.rawErase argument)
        (FourFaceBetaExperiment.DeepGSLT.rawErase body) := by
      rw [FourFaceBetaExperiment.DeepGSLT.rawErase_eq_eraseTower,
        FourFaceBetaExperiment.DeepGSLT.rawErase_eq_eraseTower]
      rfl

/-- The first-order target associated with an arbitrary intrinsic beta cell. -/
def rawTarget (claim : BetaClaim sourceContext domain codomain) : Pattern :=
  encodeRaw (FourFaceBetaExperiment.DeepGSLT.rawErase claim.target)

/-- The declaration-aware root-beta query generated from an arbitrary
intrinsic beta cell. -/
def rawGoal (claim : BetaClaim sourceContext domain codomain) : Pattern :=
  rootBeta
    (tmApp
      (tmLam (encodeRaw
        (FourFaceBetaExperiment.DeepGSLT.rawErase claim.body)))
      (encodeRaw
        (FourFaceBetaExperiment.DeepGSLT.rawErase claim.argument)))
    (rawTarget claim)

/-- The generic proof-producing checker accepts every intrinsic simple beta
cell after first-order erasure. -/
theorem betaClaim_deep_checked
    (claim : BetaClaim sourceContext domain codomain) :
    checkRaw DeclarationAwareSubstitutionLanguage.definition
      (rawGoal claim)
      (betaRawProof
        (FourFaceBetaExperiment.DeepGSLT.rawErase claim.body)
        (FourFaceBetaExperiment.DeepGSLT.rawErase claim.argument)) = true := by
  simp only [rawGoal, rawTarget, BetaClaim.target]
  rw [rawErase_instantiateNewest]
  exact betaRawProof_accepts
    (FourFaceBetaExperiment.DeepGSLT.rawErase claim.body)
    (FourFaceBetaExperiment.DeepGSLT.rawErase claim.argument)

/-- No accepted first-order certificate for the erased source can name a
different target. -/
theorem betaClaim_deep_no_invention
    (claim : BetaClaim sourceContext domain codomain)
    {target : Pattern} {proof : RawProof}
    (accepted :
      checkRaw DeclarationAwareSubstitutionLanguage.definition
        (rootBeta
          (tmApp
            (tmLam (encodeRaw
              (FourFaceBetaExperiment.DeepGSLT.rawErase claim.body)))
            (encodeRaw
              (FourFaceBetaExperiment.DeepGSLT.rawErase claim.argument)))
          target)
        proof = true) :
    target = rawTarget claim := by
  have reflected :=
    DeclarationAwareSubstitutionReflection.checkRaw_beta_reflects
      (FourFaceBetaExperiment.DeepGSLT.rawErase claim.body)
      (FourFaceBetaExperiment.DeepGSLT.rawErase claim.argument) accepted
  calc
    target = encodeRaw
        (substituteRaw 0
          (FourFaceBetaExperiment.DeepGSLT.rawErase claim.argument)
          (FourFaceBetaExperiment.DeepGSLT.rawErase claim.body)) := reflected
    _ = rawTarget claim := by
      simp only [rawTarget, BetaClaim.target]
      rw [rawErase_instantiateNewest]

/-! ## Positive and negative controls -/

/-- The original identity beta cell is now one instance of the generic
transport theorem. -/
theorem canonical_beta_is_generic :
    StepCore Presentation.Tower.rules.computation
        Presentation.Tower.rules.headEq
        (eraseTerm canonicalClaim.source) (eraseTerm canonicalClaim.target) :=
  (betaClaim_typed canonicalClaim).1

/-- In the separate set-family model, the varying Boolean family is outside
the constant-family image. This is not a claim about the tower's syntax. -/
theorem varying_set_family_outside_constant_image :
    ¬ Mettapedia.GSLT.Core.ContextualLadder.IsConstantFamily
      Mettapedia.GSLT.Core.ContextualLadder.varyingBoolFamily :=
  Mettapedia.GSLT.Core.ContextualLadder.varyingBoolFamily_not_constant

#print axioms eraseRenaming_apply
#print axioms eraseTerm_rename
#print axioms eraseSubstitution_apply
#print axioms eraseTerm_substitute
#print axioms eraseTerm_instantiateNewest
#print axioms betaClaim_typed
#print axioms rawErase_instantiateNewest
#print axioms betaClaim_deep_checked
#print axioms betaClaim_deep_no_invention
#print axioms varying_set_family_outside_constant_image

end SimpleFragmentSubstitutionTranslation
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
