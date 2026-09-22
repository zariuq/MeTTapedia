import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplay
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeJoins
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Conversion.NativeConversionSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplaySubstitution

/-!
# Transport of retained native judgment certificates

The actual replay tree, including conversion inside premises, is renamed or
instantiated with supplied argument certificates without proof search.
Closed declaration evidence remains closed. A target
telescope is independently checked: a compatible variable map alone is not
authority for its formation.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay

open Presentation StructuralTypingReplay NativeIndexedFamilies

def rename {n m : Nat} (ρ : Ren n m) (code : Code n) : Code m :=
  code.rename NativeRelatorConversionChecking.rename ρ

theorem rename_id {n : Nat} (code : Code n) : rename idRen code = code :=
  StructuralTypingReplay.Code.rename_id _ NativeRelatorConversionChecking.rename_id code

theorem rename_comp {n m k : Nat} (ρ : Ren m k) (ξ : Ren n m) (code : Code n) :
    rename ρ (rename ξ code) = rename (fun index => ρ (ξ index)) code :=
  StructuralTypingReplay.Code.rename_comp _ NativeRelatorConversionChecking.rename_comp ρ ξ code

/-- Successful complete judgment replay transports its particular term
certificate to an independently checked compatible target context. -/
theorem check_rename {n m : Nat} {source : Tower.Ctx n} {target : Tower.Ctx m}
    {subject type : Tower.Tm n} {sourceContextCode : ContextCode n} {termCode : Code n}
    (accepted : check source subject type sourceContextCode termCode = true)
    (targetContextCode : ContextCode m)
    (targetAccepted : checkContext IntrinsicRelator.rules NativeRelatorConversionChecking.check
      target targetContextCode = true)
    {ρ : Ren n m} (compatible : CtxRen source target ρ) :
    check target (Presentation.rename ρ subject) (Presentation.rename ρ type)
      targetContextCode (rename ρ termCode) = true := by
  simp only [check, checkJudgment, Bool.and_eq_true] at accepted ⊢
  exact ⟨targetAccepted, StructuralTypingReplay.check_rename
    NativeRelatorConversionChecking.rename IntrinsicRelator.rules
    NativeRelatorConversionChecking.check NativeRelatorConversionChecking.check_rename
    termCode accepted.2 compatible⟩

def substitute {n m : Nat} (σ : Sub Tower.Head n m) (imageCodes : Fin n → Code m)
    (subject type : Tower.Tm n) (code : Code n) : Code m :=
  code.substitute NativeRelatorConversionChecking.rename NativeRelatorConversionChecking.substitute
    σ imageCodes subject type

/-- The complete checker accepts the computed instantiated proof, using
the existing dependent argument fold and independently formed target. -/
theorem check_substitute {n m : Nat} {source : Tower.Ctx n} {target : Tower.Ctx m}
    {subject type : Tower.Tm n} {sourceContextCode : ContextCode n} {termCode : Code n}
    (accepted : check source subject type sourceContextCode termCode = true)
    (targetContextCode : ContextCode m)
    (targetAccepted : checkContext IntrinsicRelator.rules NativeRelatorConversionChecking.check
      target targetContextCode = true)
    (σ : Sub Tower.Head n m) (imageCodes : Fin n → Code m)
    (images : TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check target)
      source σ imageCodes = true) :
    check target (subst σ subject) (subst σ type) targetContextCode
      (substitute σ imageCodes subject type termCode) = true := by
  simp only [check, checkJudgment, Bool.and_eq_true] at accepted ⊢
  exact ⟨targetAccepted, check_substitute_of_checked_arguments
    NativeRelatorConversionChecking.rename NativeRelatorConversionChecking.substitute
    IntrinsicRelator.rules NativeRelatorConversionChecking.check
    NativeRelatorConversionChecking.check_rename NativeRelatorConversionChecking.check_substitute
    accepted.2 σ imageCodes images⟩

/-- Replay of the computed certificate constructs the actual formed
judgment, not only an agreement of observed normal forms. -/
theorem instantiated_judgment {n m : Nat} {source : Tower.Ctx n} {target : Tower.Ctx m}
    {subject type : Tower.Tm n} {sourceContextCode : ContextCode n} {termCode : Code n}
    (accepted : check source subject type sourceContextCode termCode = true)
    (targetContextCode : ContextCode m)
    (targetAccepted : checkContext IntrinsicRelator.rules NativeRelatorConversionChecking.check
      target targetContextCode = true)
    (σ : Sub Tower.Head n m) (imageCodes : Fin n → Code m)
    (images : TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check target)
      source σ imageCodes = true) :
    FormationSensitive.Judgment IntrinsicRelator.rules target (subst σ subject) (subst σ type) :=
  sound (check_substitute accepted targetContextCode targetAccepted σ imageCodes images)

open TelescopeAbstraction in
/-- Checked arguments simultaneously determine directed execution and the
retained certificate for its result. The application is the existing
telescope closure, not an abstract operational relation supplied as a premise. -/
theorem checked_execution {n m : Nat} {source : Tower.Ctx n} {target : Tower.Ctx m}
    {subject type : Tower.Tm n} {sourceContextCode : ContextCode n} {termCode : Code n}
    (accepted : check source subject type sourceContextCode termCode = true)
    (targetContextCode : ContextCode m)
    (targetAccepted : checkContext IntrinsicRelator.rules NativeRelatorConversionChecking.check
      target targetContextCode = true)
    (σ : Sub Tower.Head n m) (imageCodes : Fin n → Code m)
    (images : TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check target)
      source σ imageCodes = true) :
    check target (subst σ subject) (subst σ type) targetContextCode
        (substitute σ imageCodes subject type termCode) = true ∧
      FormationSensitive.Judgment IntrinsicRelator.rules target
        (applyClosed source σ (liftClosed (closeTerm source subject))) (subst σ type) ∧
      BetaSteps (applyClosed source σ (liftClosed (closeTerm source subject))) (subst σ subject) := by
  have targetFormed := checkContext_sound IntrinsicRelator.rules NativeRelatorConversionChecking.check
    NativeRelatorConversionChecking.check_sound targetContextCode targetAccepted
  obtain ⟨applicationTyped, _, steps⟩ := StructuralTypingReplay.checked_program
    IntrinsicRelator.rules NativeRelatorConversionChecking.check NativeRelatorConversionChecking.check_sound
    FormationSensitiveNativeRelatorElimination.universes FormationCheckedTelescopePrograms.tower_joins
    targetFormed (sound accepted) images
  exact ⟨check_substitute accepted targetContextCode targetAccepted σ imageCodes images,
    applicationTyped, steps⟩

namespace TransportControls

open NativeRelatorConversionChecking.Examples (ground betaArgument)

def extended : Tower.Ctx 2 := .snoc Controls.context ground
def extendedCode : ContextCode 2 := .snoc Controls.contextCode (.sort Tower.zero) .headType

theorem extended_context_checked :
    checkContext IntrinsicRelator.rules NativeRelatorConversionChecking.check
      extended extendedCode = true := by decide +kernel

/-- The retained conversion proof moves with the old variable, which is
now at position one rather than the newly introduced position zero. -/
theorem converted_proof_weakens :
    check extended (.refl (.var 1))
      (.id ground (betaArgument (.var 1)) (betaArgument (.var 1)))
      extendedCode (rename wk Controls.proofCode) = true :=
  check_rename Controls.dependent_conversion_checked extendedCode extended_context_checked (ρ := wk)
    (fun _ => rfl)

theorem captured_proof_rejected :
    check extended (.refl (.var 0))
      (.id ground (betaArgument (.var 1)) (betaArgument (.var 1)))
      extendedCode (rename wk Controls.proofCode) = false := by decide +kernel

/-- A closed converted lambda is moved into a nonempty checked context;
the conversion child is traversed under its retained binder. -/
theorem converted_function_weakens :
    check Controls.context (.lam (.refl (.var 0)))
      (.pi ground (.id ground (betaArgument (.var 0)) (betaArgument (.var 0))))
      Controls.contextCode (rename Fin.elim0 Controls.functionCode) = true := by
  decide +kernel

def nonVariable : Sub Tower.Head 1 1 := fun _ => betaArgument (.var 0)
def nonVariableCodes : Fin 1 → Code 1 := fun _ => Controls.betaArgumentCode

theorem nonvariable_arguments_checked :
    TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check
        Controls.context) Controls.context nonVariable nonVariableCodes = true := by
  decide +kernel

theorem nonvariable_certificate_checked :
    check Controls.context (.refl (betaArgument (.var 0)))
      (.id ground (betaArgument (betaArgument (.var 0))) (betaArgument (betaArgument (.var 0))))
      Controls.contextCode
      (substitute nonVariable nonVariableCodes (.refl (.var 0)) Controls.targetType Controls.proofCode) = true :=
  check_substitute Controls.dependent_conversion_checked Controls.contextCode (by decide +kernel)
    nonVariable nonVariableCodes nonvariable_arguments_checked

def openFunctionType : Tower.Tm 1 :=
  .pi ground (Presentation.rename wk Controls.targetType)

def openFunctionCode : Code 1 :=
  .lamIntro (.sort (.max Tower.zero Tower.zero))
    (.piForm (.sort Tower.zero) (.sort Tower.zero) .headType (rename wk Controls.targetFormation))
    (rename wk Controls.proofCode)

theorem open_function_checked :
    check Controls.context (.lam (.refl (.var 1))) openFunctionType
      Controls.contextCode openFunctionCode = true := by decide +kernel

/-- The substituted argument is itself an application containing a lambda.
It crosses the retained proof's binder without capturing the free variable. -/
theorem nonvariable_under_binder_checked :
    check Controls.context (.lam (.refl (betaArgument (.var 1))))
      (subst nonVariable openFunctionType) Controls.contextCode
      (substitute nonVariable nonVariableCodes (.lam (.refl (.var 1))) openFunctionType openFunctionCode) = true :=
  check_substitute open_function_checked Controls.contextCode (by decide +kernel)
    nonVariable nonVariableCodes nonvariable_arguments_checked

theorem captured_instantiation_rejected :
    check Controls.context (.lam (.refl (betaArgument (.var 0))))
      (subst nonVariable openFunctionType) Controls.contextCode
      (substitute nonVariable nonVariableCodes (.lam (.refl (.var 1))) openFunctionType openFunctionCode) = false := by
  decide +kernel

theorem unchecked_argument_rejected :
    TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check
        Controls.context) Controls.context nonVariable (fun _ => (.var : Code 1)) = false := by
  decide +kernel

end TransportControls

#print axioms rename_id
#print axioms rename_comp
#print axioms check_rename
#print axioms check_substitute
#print axioms instantiated_judgment
#print axioms checked_execution
#print axioms TransportControls.converted_proof_weakens
#print axioms TransportControls.captured_proof_rejected
#print axioms TransportControls.converted_function_weakens
#print axioms TransportControls.nonvariable_arguments_checked
#print axioms TransportControls.nonvariable_certificate_checked
#print axioms TransportControls.open_function_checked
#print axioms TransportControls.nonvariable_under_binder_checked
#print axioms TransportControls.captured_instantiation_rejected
#print axioms TransportControls.unchecked_argument_rejected

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay
