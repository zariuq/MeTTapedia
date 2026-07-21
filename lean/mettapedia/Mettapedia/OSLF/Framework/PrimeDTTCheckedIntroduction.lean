import Mettapedia.GSLT.LanguageDef.LFTyping
import Mettapedia.Languages.MeTTa.Pure.Typing
import Mettapedia.Languages.MeTTa.Pure.SubjectReduction

/-!
# Prime checked dependent-introduction reference canaries

This file compares the Prime v0.69 executable calibration with two independent
Lean developments already present in MeTTapedia:

* the directly indexed LF checker, for de Bruijn lookup, substitution, beta,
  and lambda/Pi checking; and
* the locally nameless MeTTa-Pure typing relation, for canonical binders and a
  genuinely dependent polymorphic identity.

These are narrow agreement canaries, not a claim that either reference is a
complete semantics for the Prime package.
-/

namespace Mettapedia.OSLF.Framework.PrimeDTTCheckedIntroduction

open Mettapedia.OSLF.MeTTaIL.Syntax

namespace LFReference

open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping

def zero : Term := .con "zero"
def nat : Term := .con "nat"

theorem identity_checks :
    check 32 corpusSig [] idProof idProofTy = true :=
  corpus_id_check

theorem identity_is_typed :
    HasType corpusSig [] idProof idProofTy :=
  corpus_id_sound

theorem subst_var_zero : subst0 zero (.var 0) = zero := by
  rfl

theorem subst_crosses_inner_binder_without_capture :
    subst0 zero (.lam nat (.var 1)) = .lam nat zero := by
  rfl

theorem beta_identity :
    nfApp [] 2 (.lam nat (.var 0)) zero = zero := by
  rfl

end LFReference

namespace PureReference

open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.MeTTa.Pure.Core
open Mettapedia.Languages.MeTTa.Pure.BinderOps
open Mettapedia.Languages.MeTTa.Pure.Fragment
open Mettapedia.Languages.MeTTa.Pure.Typing
open Mettapedia.Languages.MeTTa.Pure.Reduction

def zero : Pattern := .apply "Zero" []

theorem instantiate_var_zero :
    instantiateBVarAt 0 zero (.bvar 0) = zero := by
  simp [instantiateBVarAt, zero, liftBVars]

theorem instantiate_crosses_inner_binder_without_capture :
    instantiateBVarAt 0 zero (mkLam (.bvar 1)) = mkLam zero := by
  simp [instantiateBVarAt, mkLam, zero, liftBVars]

theorem identity_is_typed :
    PureHasType [] (mkLam (.bvar 0)) (mkPi u0 u0) :=
  identity_type

theorem nested_projection_is_typed :
    PureHasType [] (mkLam (mkLam (.bvar 1)))
      (mkPi u0 (mkPi u0 u0)) :=
  fst_proj_type

def polymorphicIdentity : Pattern :=
  mkLam (mkLam (.bvar 0))

def polymorphicIdentityType : Pattern :=
  mkPi u0 (mkPi (.bvar 0) (.bvar 1))

theorem polymorphic_identity_is_typed :
    PureHasType [] polymorphicIdentity polymorphicIdentityType := by
  unfold polymorphicIdentity polymorphicIdentityType
  apply PureHasType.lam_intro [] ∅
      u0 (mkLam (.bvar 0)) (mkPi (.bvar 0) (.bvar 1)) u1
      (.u0_type [])
  intro typeName _
  simp only [openBVar_mkLam, openBVar_mkPi, openBVar]
  apply PureHasType.lam_intro
      [(typeName, u0)] ∅
      (.fvar typeName) (.bvar 0) (.fvar typeName) u0
  · exact .fvar [(typeName, u0)] typeName u0
      List.mem_cons_self PureTmPattern.u0 (by rfl)
  · intro valueName _
    simp only [openBVar]
    exact .fvar
      [(valueName, .fvar typeName), (typeName, u0)]
      valueName (.fvar typeName)
      List.mem_cons_self (PureTmPattern.fvar typeName)
      (by simp [lc_at])

/-! ### Calibrated structural metatheory canaries -/

def argumentName : String := "argument"
def binderName : String := "bound"
def argumentContext : PureCtx := [(argumentName, u0)]

theorem argument_is_typed :
    PureHasType argumentContext (.fvar argumentName) u0 := by
  exact .fvar argumentContext argumentName u0
    (by simp [argumentContext]) PureTmPattern.u0
    (by simp [lc_at, lc_at_list, u0])

/-- The closed identity remains typed after extending its context.  This is a
concrete use of the general weakening theorem, not a second typing rule. -/
theorem identity_survives_context_extension :
    PureHasType argumentContext (mkLam (.bvar 0)) (mkPi u0 u0) := by
  simpa [argumentContext, argumentName] using
    (Mettapedia.Languages.MeTTa.Pure.SubjectReduction.weakening
      (x := argumentName) (U := u0) identity_type)

/-- Substituting the typed argument for a genuinely free binder name preserves
typing in the calibrated one-variable context. -/
theorem calibrated_substitution :
    PureHasType argumentContext
      (Mettapedia.Languages.MeTTa.Pure.SubjectReduction.substFVar
        binderName (.fvar argumentName) (.fvar binderName))
      (Mettapedia.Languages.MeTTa.Pure.SubjectReduction.substFVar
        binderName (.fvar argumentName) u0) := by
  have hBound :
      PureHasType ((binderName, u0) :: argumentContext)
        (.fvar binderName) u0 := by
    exact .fvar _ binderName u0 List.mem_cons_self
      PureTmPattern.u0 (by simp [lc_at, lc_at_list, u0])
  have hSub :=
    Mettapedia.Languages.MeTTa.Pure.SubjectReduction.typing_subst
    (x := binderName) (A := u0) (u := .fvar argumentName)
    (Γ := argumentContext)
    argument_is_typed
    (by simp [lc_at])
    (by
      simp [Mettapedia.Languages.MeTTa.Pure.SubjectReduction.ctxNames,
        argumentContext, argumentName, binderName])
    (by simp [isFresh, freeVars, u0, binderName])
    (by
      simp [Mettapedia.Languages.MeTTa.Pure.SubjectReduction.ctxFresh,
        argumentContext, isFresh, freeVars, u0, binderName])
    hBound
    (Δ := [])
    rfl
    (by
      simp [Mettapedia.Languages.MeTTa.Pure.SubjectReduction.ctxNames,
        binderName])
  simpa [argumentContext] using hSub

def identityApplication : Pattern :=
  mkApp (mkLam (.bvar 0)) (.fvar argumentName)

theorem identity_application_is_typed :
    PureHasType argumentContext identityApplication u0 := by
  unfold identityApplication
  have hApp := PureHasType.app argumentContext ∅
      (mkLam (.bvar 0)) (.fvar argumentName) u0 u0 u1
      identity_survives_context_extension argument_is_typed (by
        intro freshName _
        simpa [openBVar, u0] using
          (PureHasType.u0_type ((freshName, u0) :: argumentContext)))
  simpa [openBVar, u0] using hApp

/-- The actual beta step for the calibrated identity application preserves its
type by the general MeTTa-Pure subject-reduction theorem. -/
theorem identity_beta_subject_reduction :
    PureHasType argumentContext (.fvar argumentName) u0 := by
  have hReduction :
      PureReduces identityApplication (.fvar argumentName) := by
    unfold identityApplication
    simpa [openBVar] using
      (PureReduces.betaPi (.bvar 0) (.fvar argumentName))
  exact
    Mettapedia.Languages.MeTTa.Pure.SubjectReduction.mettaPure_subject_reduction
      identity_application_is_typed hReduction

end PureReference

/-- Both independent substitution engines eliminate the innermost variable. -/
theorem substitution_agreement_canary :
    (Mettapedia.GSLT.LanguageDef.LFTyping.subst0
      LFReference.zero (.var 0) = LFReference.zero) ∧
    (Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt
      0 PureReference.zero (.bvar 0) = PureReference.zero) := by
  exact ⟨LFReference.subst_var_zero, PureReference.instantiate_var_zero⟩

#print axioms LFReference.identity_is_typed
#print axioms LFReference.beta_identity
#print axioms PureReference.polymorphic_identity_is_typed
#print axioms PureReference.identity_survives_context_extension
#print axioms PureReference.calibrated_substitution
#print axioms PureReference.identity_beta_subject_reduction
#print axioms substitution_agreement_canary

end Mettapedia.OSLF.Framework.PrimeDTTCheckedIntroduction
