import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveReplaySemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeRelatorEliminationPreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeRelatorConversionChecking

/-!
# Finite judgment replay for the native List/identity/relator candidate

The shared formed replay is instantiated with the existing finite native
conversion codes and the actual cumulative head decisions. Every current
formed judgment of this rule package has a certificate, and every accepted
certificate reconstructs that judgment, including its ambient context.

Conversion may occur at any recursive premise. Its target formation and
source admission are checked independently. This is proof replay, not total
type inference, search completeness at a resource bound, or C refinement.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay

open Presentation FormationSensitive StructuralTypingReplay
open NativeIndexedFamilies

abbrev Code := StructuralTypingReplay.Code Tower.Head NativeRelatorConversionChecking.Code
abbrev ContextCode := StructuralTypingReplay.ContextCode Tower.Head NativeRelatorConversionChecking.Code

/-- Include the earlier structural-only certificate without introducing a
conversion step or changing any node or annotation. -/
def includeStructuralCode {n : Nat}
    (code : StructuralTypingReplay.Code Tower.Head NoConversion n) : Code n :=
  code.mapConversion (fun impossible => impossible.elim)

theorem structural_replay_unchanged {n : Nat}
    (code : StructuralTypingReplay.Code Tower.Head NoConversion n)
    (context : Tower.Ctx n) (subject type : Tower.Tm n) :
    StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check
        context subject type (includeStructuralCode code) =
      StructuralTypingReplay.check IntrinsicRelator.rules noConversionCheck context subject type code := by
  apply check_mapConversion
  intro scope impossible left right
  exact impossible.elim

def check {n : Nat} (context : Tower.Ctx n) (subject type : Tower.Tm n)
    (contextCode : ContextCode n) (termCode : Code n) : Bool :=
  checkJudgment IntrinsicRelator.rules NativeRelatorConversionChecking.check
    context subject type contextCode termCode

theorem sound {n : Nat} {context : Tower.Ctx n} {subject type : Tower.Tm n}
    {contextCode : ContextCode n} {termCode : Code n}
    (accepted : check context subject type contextCode termCode = true) :
    Judgment IntrinsicRelator.rules context subject type :=
  checkJudgment_sound IntrinsicRelator.rules NativeRelatorConversionChecking.check
    NativeRelatorConversionChecking.check_sound accepted

theorem judgment_iff_certificate {n : Nat} {context : Tower.Ctx n} {subject type : Tower.Tm n} :
    Judgment IntrinsicRelator.rules context subject type ↔
      ∃ contextCode termCode, check context subject type contextCode termCode = true :=
  judgment_iff_checked IntrinsicRelator.rules NativeRelatorConversionChecking.check
    (fun conversion => NativeRelatorConversionChecking.conversion_iff_checked.mp conversion)
    NativeRelatorConversionChecking.check_sound

open FormationSensitiveContextual _root_.CategoryTheory Mettapedia.TypeTheory in
/-- The actual native checker supplies a represented formed source term,
with its original subject/type and its value at every admitted substitution. -/
theorem accepted_representation {n : Nat} {context : Tower.Ctx n} {subject type : Tower.Tm n}
    {contextCode : ContextCode n} {termCode : Code n}
    (accepted : check context subject type contextCode termCode = true) :
    ∃ formed : ContextFormation IntrinsicRelator.rules context,
      ∃ actualType : TypeOver (⟨n, context, formed⟩ : Context IntrinsicRelator.rules),
        ∃ actualTerm : Term (⟨n, context, formed⟩ : Context IntrinsicRelator.rules) actualType,
          actualType.code = type ∧ actualTerm.code = subject ∧
            ∀ (target : Context IntrinsicRelator.rules) (σ : Hom target ⟨n, context, formed⟩),
              (CwfYoneda.decodeTerm (asCwf IntrinsicRelator.rules) actualType σ
                ((PresheafSemantics.termEquiv actualType actualTerm).val
                  ⟨Opposite.op (CwfYoneda.context (asCwf IntrinsicRelator.rules) target), σ⟩)).code =
                subst σ.substitution subject :=
  accepted_has_represented_term IntrinsicRelator.rules NativeRelatorConversionChecking.check
    NativeRelatorConversionChecking.check_sound FormationSensitiveNativeRelatorElimination.universes accepted

namespace Controls

open NativeRelatorConversionChecking.Examples (ground betaArgument identityExpansionCode)

private def zero : Tower.Head := .sort Tower.zero
private def pairLevel : Tower.Head := .sort (.max Tower.zero Tower.zero)

def context : Tower.Ctx 1 := .snoc .nil ground
def contextCode : ContextCode 1 := .snoc .nil zero .headType

def targetType : Tower.Tm 1 :=
  .id ground (betaArgument (.var 0)) (betaArgument (.var 0))

def betaArgumentCode : Code 1 :=
  .appElim ground ground
    (.lamIntro pairLevel (.piForm zero zero .headType .headType) .var) .var

def targetFormation : Code 1 :=
  .idForm zero .headType betaArgumentCode betaArgumentCode

def proofCode : Code 1 :=
  .convert (.id ground (.var 0) (.var 0)) zero
    (.reflIntro ground .var) targetFormation (identityExpansionCode (.var 0))

theorem dependent_conversion_checked :
    check context (.refl (.var 0)) targetType contextCode proofCode = true := by
  decide +kernel

/-- Both conversion and its formed target occur inside a lambda premise. -/
def functionCode : Code 0 :=
  .lamIntro pairLevel (.piForm zero zero .headType targetFormation) proofCode

theorem conversion_beneath_binder_checked :
    check .nil (.lam (.refl (.var 0))) (.pi ground targetType) .nil functionCode = true := by
  decide +kernel

theorem converted_function_admitted :
    Judgment IntrinsicRelator.rules .nil (.lam (.refl (.var 0))) (.pi ground targetType) :=
  sound conversion_beneath_binder_checked

/-- An accepted source and conversion do not excuse a malformed target
formation certificate. The endpoint judgment itself is still derivable. -/
theorem malformed_target_formation_rejected :
    check context (.refl (.var 0)) targetType contextCode
      (.convert (.id ground (.var 0) (.var 0)) zero
        (.reflIntro ground .var) .var (identityExpansionCode (.var 0))) = false := by
  decide +kernel

theorem mismatched_conversion_rejected :
    check context (.refl (.var 0)) targetType contextCode
      (.convert (.id ground (.var 0) (.var 0)) zero
        (.reflIntro ground .var) targetFormation (.refl (.id ground (.var 0) (.var 0)))) = false := by
  decide +kernel

def unformedContext : Tower.Ctx 1 := .snoc .nil (.const `NativeReplay.undeclared)

/-- A raw variable derivation does not establish formation of its ambient
assumption. The complete entry point checks and rejects that context. -/
theorem unchecked_assumption_rejected :
    StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check
        unformedContext (.var 0) (Ctx.lookup unformedContext 0) (.var : Code 1) = true ∧
      check unformedContext (.var 0) (Ctx.lookup unformedContext 0) contextCode .var = false := by
  decide +kernel

/-! Declaration-local replay also covers nontrivial conversion below a
binder. The decoder perturbation below tests dependency locality, not a new
selected logical profile. -/

def unusedDeclaration : Declaration.Signature Tower.Head :=
  Declaration.Signature.ofList [(`NativeReplay.laterProgram, ⟨.pi ground ground, some (.lam (.var 0))⟩)]

abbrev extendedRules := Declaration.extendRules IntrinsicRelator.rules unusedDeclaration

instance : ∀ h u, Decidable (extendedRules.headTyping h u) :=
  fun h u => inferInstanceAs (Decidable (IntrinsicRelator.rules.headTyping h u))
instance : ∀ h, Decidable (extendedRules.isUniverse h) :=
  fun h => inferInstanceAs (Decidable (IntrinsicRelator.rules.isUniverse h))
instance : ∀ u v w, Decidable (extendedRules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (IntrinsicRelator.rules.join u v w))
instance : ∀ u v, Decidable (extendedRules.cumulative u v) :=
  fun u v => inferInstanceAs (Decidable (IntrinsicRelator.rules.cumulative u v))

def noNativeRoots : {n : Nat} → NativeRelatorRootConversionCode.Code n →
    Option (Tower.Tm n × Tower.Tm n) := fun _ => none

theorem binder_dependency_comparison_accepts :
    judgmentDependencyCheck IntrinsicRelator.rules extendedRules
      NativeRelatorRootConversionCode.decode noNativeRoots
      .nil (.lam (.refl (.var 0))) (.pi ground targetType) .nil functionCode = true := by
  decide +kernel

/-- This whole judgment uses genuine beta conversion inside a dependent
lambda but none of the native iota roots. Removing those roots and adding an
unused defined constant therefore leaves its supplied certificate accepted. -/
theorem converted_binder_reuses_after_extension :
    checkJudgment extendedRules (StructuralConversionCode.Code.check Tower.HeadEq noNativeRoots)
      .nil (.lam (.refl (.var 0))) (.pi ground targetType) .nil functionCode = true := by
  rw [← checkJudgment_eq_of_dependencyCheck IntrinsicRelator.rules extendedRules
    Tower.HeadEq NativeRelatorRootConversionCode.decode noNativeRoots
    ⟨rfl, rfl, rfl, rfl⟩ _ _ _ _ _ binder_dependency_comparison_accepts]
  exact conversion_beneath_binder_checked

/-- The unused decoder change is observable elsewhere: an actual authored
relator root stops checking. The agreement above is genuinely local. -/
theorem removed_native_root_rejected :
    NativeRelatorConversionChecking.checkStep NativeRelatorConversionChecking.Examples.relConsStep
        IntrinsicRelator.consIotaLeft IntrinsicRelator.consIotaRight = true ∧
      StructuralConversionCode.StepCode.check Tower.HeadEq noNativeRoots
        NativeRelatorConversionChecking.Examples.relConsStep
        IntrinsicRelator.consIotaLeft IntrinsicRelator.consIotaRight = false := by
  decide +kernel

end Controls

#print axioms sound
#print axioms structural_replay_unchanged
#print axioms judgment_iff_certificate
#print axioms accepted_representation
#print axioms Controls.dependent_conversion_checked
#print axioms Controls.conversion_beneath_binder_checked
#print axioms Controls.converted_function_admitted
#print axioms Controls.malformed_target_formation_rejected
#print axioms Controls.mismatched_conversion_rejected
#print axioms Controls.unchecked_assumption_rejected
#print axioms Controls.binder_dependency_comparison_accepts
#print axioms Controls.converted_binder_reuses_after_extension
#print axioms Controls.removed_native_root_rejected

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay
