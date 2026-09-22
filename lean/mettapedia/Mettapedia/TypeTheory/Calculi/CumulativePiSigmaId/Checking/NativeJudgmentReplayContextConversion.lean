import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplayFormation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayContextConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCodeCongruence

/-!
# Native certificate transport across convertible binders and indices

The native finite conversion encoding supplies every qualification of the
generic context and pointwise-substitution transformations. Both the original
and destination contexts are replayed; a conversion certificate alone cannot
introduce an unformed assumption. Syntax is unchanged by context conversion,
but the variable-use evidence is explicitly transported, not erased.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

open Presentation NativeIndexedFamilies

namespace NativeRelatorConversionChecking

def substitutePointwise {n m : Nat} (σ τ : Sub Tower.Head n m)
    (images : Fin n → Code m) (term : Tower.Tm n) : Code m :=
  StructuralConversionCode.Code.substitutePointwise rename σ τ images term

theorem check_substitutePointwise {n m : Nat} (σ τ : Sub Tower.Head n m)
    (images : Fin n → Code m) (term : Tower.Tm n)
    (accepted : ∀ index, check (images index) (σ index) (τ index) = true) :
    check (substitutePointwise σ τ images term) (subst σ term) (subst τ term) = true :=
  StructuralConversionCode.Code.substitutePointwise_checked Tower.HeadEq NativeRelatorRootConversionCode.decode
    rename check_rename term σ τ images accepted

def inst0Argument {n : Nat} (left right : Tower.Tm n) (code : Code n)
    (body : Tower.Tm (n + 1)) : Code n :=
  StructuralConversionCode.Code.inst0Argument rename left right code body

theorem check_inst0Argument {n : Nat} {left right : Tower.Tm n} {code : Code n}
    (accepted : check code left right = true) (body : Tower.Tm (n + 1)) :
    check (inst0Argument left right code body) (inst0 left body) (inst0 right body) = true :=
  StructuralConversionCode.Code.inst0Argument_checked Tower.HeadEq NativeRelatorRootConversionCode.decode
    rename check_rename accepted body

end NativeRelatorConversionChecking

namespace NativeJudgmentReplay

open StructuralTypingReplay

def convertNewest {n : Nat} (new : Tower.Tm n) (level : Tower.Head)
    (oldFormation : Code n) (forward : NativeRelatorConversionChecking.Code n)
    (subject type : Tower.Tm (n + 1)) (code : Code (n + 1)) : Code (n + 1) :=
  StructuralTypingReplay.Code.convertNewest NativeRelatorConversionChecking.rename
    NativeRelatorConversionChecking.substitute new level oldFormation (.symm forward) subject type code

/-- The complete accepted judgment changes ambient binder while retaining
the same raw subject and annotation. Both context certificates are concrete. -/
theorem check_convertNewest {n : Nat} {context : Tower.Ctx n} {old new : Tower.Tm n}
    {u v : Tower.Head} {contextCode : ContextCode n} {oldFormation newFormation : Code n}
    {subject type : Tower.Tm (n + 1)} {code : Code (n + 1)}
    {forward : NativeRelatorConversionChecking.Code n}
    (accepted : check (.snoc context old) subject type (.snoc contextCode u oldFormation) code = true)
    (newFormed : check context new (.head v) contextCode newFormation = true)
    (newUniverse : IntrinsicRelator.rules.isUniverse v)
    (converted : NativeRelatorConversionChecking.check forward old new = true) :
    check (.snoc context new) subject type (.snoc contextCode v newFormation)
      (convertNewest new u oldFormation forward subject type code) = true := by
  simp only [check, checkJudgment, checkContext, Bool.and_eq_true, decide_eq_true_eq] at accepted newFormed ⊢
  refine ⟨⟨⟨newFormed.1, newUniverse⟩, newFormed.2⟩, ?_⟩
  exact StructuralTypingReplay.Code.convertNewest_checked NativeRelatorConversionChecking.rename
    NativeRelatorConversionChecking.substitute IntrinsicRelator.rules NativeRelatorConversionChecking.check
    NativeRelatorConversionChecking.check_rename NativeRelatorConversionChecking.check_substitute
    accepted.1.2 accepted.1.1.2
    (StructuralConversionCode.Code.check_symm Tower.HeadEq NativeRelatorRootConversionCode.decode converted)
    accepted.2

namespace ContextConversionControls

open NativeRelatorConversionChecking.Examples (ground betaArgument identityExpansionCode)

def oldType : Tower.Tm 1 := .id ground (.var 0) (.var 0)
def newType : Tower.Tm 1 := .id ground (betaArgument (.var 0)) (betaArgument (.var 0))
def oldFormation : Code 1 := .idForm (.sort Tower.zero) .headType .var .var
def newFormation : Code 1 := Controls.targetFormation
def oldContext : Tower.Ctx 2 := .snoc Controls.context oldType
def newContext : Tower.Ctx 2 := .snoc Controls.context newType
def oldContextCode : ContextCode 2 := .snoc Controls.contextCode (.sort Tower.zero) oldFormation
def newContextCode : ContextCode 2 := .snoc Controls.contextCode (.sort Tower.zero) newFormation
def oldLookup : Tower.Tm 2 := Presentation.rename wk oldType

def convertedVariable : Code 2 :=
  convertNewest newType (.sort Tower.zero) oldFormation (identityExpansionCode (.var 0))
    (.var 0) oldLookup .var

theorem converted_variable_checked :
    check newContext (.var 0) oldLookup newContextCode convertedVariable = true :=
  check_convertNewest (by decide +kernel) (by decide +kernel) (.sort _)
    (NativeRelatorConversionChecking.Examples.identity_expansion_checked _)

theorem unchanged_variable_certificate_rejected :
    check newContext (.var 0) oldLookup newContextCode .var = false := by decide +kernel

def functionType : Tower.Tm 2 := .pi ground (Presentation.rename wk oldLookup)
def functionCode : Code 2 :=
  .lamIntro (.sort (.max Tower.zero Tower.zero))
    (.piForm (.sort Tower.zero) (.sort Tower.zero) .headType
      (.idForm (.sort Tower.zero) .headType .var .var)) .var

def convertedFunction : Code 2 :=
  convertNewest newType (.sort Tower.zero) oldFormation (identityExpansionCode (.var 0))
    (.lam (.var 1)) functionType functionCode

theorem conversion_beneath_further_binder_checked :
    check newContext (.lam (.var 1)) functionType newContextCode convertedFunction = true :=
  check_convertNewest (by decide +kernel) (by decide +kernel) (.sort _)
    (NativeRelatorConversionChecking.Examples.identity_expansion_checked _)

theorem captured_function_rejected :
    check newContext (.lam (.var 0)) functionType newContextCode convertedFunction = false := by
  decide +kernel

/-- Pointwise conversion of an index traverses a further binder and both
occurrences of the old variable, instead of converting just the outer head. -/
def nestedFamily : Tower.Tm 2 :=
  .pi ground (.id ground (.var 1) (.var 1))

def indexConversion : NativeRelatorConversionChecking.Code 1 :=
  .single (.betaPi (.var 0) (.var 0))

def nestedIndexConversion : NativeRelatorConversionChecking.Code 1 :=
  NativeRelatorConversionChecking.inst0Argument (betaArgument (.var 0)) (.var 0)
    indexConversion nestedFamily

theorem repeated_index_beneath_binder_checked :
    NativeRelatorConversionChecking.check nestedIndexConversion
      (.pi ground (.id ground (betaArgument (.var 1)) (betaArgument (.var 1))))
      (.pi ground (.id ground (.var 1) (.var 1))) = true :=
  NativeRelatorConversionChecking.check_inst0Argument (by decide +kernel) nestedFamily

theorem captured_index_conversion_rejected :
    NativeRelatorConversionChecking.check nestedIndexConversion
      (.pi ground (.id ground (betaArgument (.var 1)) (betaArgument (.var 1))))
      (.pi ground (.id ground (.var 0) (.var 0))) = false := by decide +kernel

def uncheckedBinder : Tower.Tm 1 :=
  .app (.lam (Presentation.rename wk oldType)) (.const `ContextConversion.undeclared)

def uncheckedBinderConversion : NativeRelatorConversionChecking.Code 1 :=
  .symm (.single (.betaPi (Presentation.rename wk oldType) (.const `ContextConversion.undeclared)))

def uncheckedBinderBody : Code 2 :=
  convertNewest uncheckedBinder (.sort Tower.zero) oldFormation uncheckedBinderConversion
    (.var 0) oldLookup .var

/-- An accepted raw conversion and even successful body replay do not
validate the destination context's independently supplied formation code. -/
theorem destination_formation_gate_retained :
    NativeRelatorConversionChecking.check uncheckedBinderConversion oldType uncheckedBinder = true ∧
      StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check
        (.snoc Controls.context uncheckedBinder) (.var 0) oldLookup uncheckedBinderBody = true ∧
      check (.snoc Controls.context uncheckedBinder) (.var 0) oldLookup
        (.snoc Controls.contextCode (.sort Tower.zero) .headType) uncheckedBinderBody = false := by
  decide +kernel

end ContextConversionControls

#print axioms check_convertNewest
#print axioms ContextConversionControls.converted_variable_checked
#print axioms ContextConversionControls.unchanged_variable_certificate_rejected
#print axioms ContextConversionControls.conversion_beneath_further_binder_checked
#print axioms ContextConversionControls.captured_function_rejected
#print axioms ContextConversionControls.repeated_index_beneath_binder_checked
#print axioms ContextConversionControls.captured_index_conversion_rejected
#print axioms ContextConversionControls.destination_formation_gate_retained

end NativeJudgmentReplay

#print axioms NativeRelatorConversionChecking.check_substitutePointwise
#print axioms NativeRelatorConversionChecking.check_inst0Argument

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
