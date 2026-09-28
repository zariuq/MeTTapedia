import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplay
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCode

/-!
# Checked one-sided beta conversion in an identity family

The finite conversion code expands only the left endpoint of an identity
type. It uses the structural beta rule, so its construction is independent
of the selected declaration-specific root decoder. Admission of a proof at
the expanded type still requires both a checked source and an independently
checked target formation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralTypingReplay

variable {Head : Type} {RootCode : Nat → Type} {n : Nat}

/-- A scoped finite path from diagonal identity to one-sided beta expansion.
The underlying forward reduction contracts the expanded left endpoint;
symmetry is used only at the conversion boundary. -/
def betaIdentityLeftCode (carrier argument : Tm Head n) :
    StructuralConversionCode.Code Head RootCode n :=
  .symm (.single (.congIdLeft carrier (.betaPi (.var 0) argument) argument))

theorem betaIdentityLeftCode_checked [DecidableEq Head]
    (headEq : Head → Head → Prop) [DecidableRel headEq]
    (decodeRoot : {k : Nat} → RootCode k → Option (Tm Head k × Tm Head k))
    (carrier argument : Tm Head n) :
    (betaIdentityLeftCode (RootCode := RootCode) carrier argument).check
      headEq decodeRoot (.id carrier argument argument)
      (.id carrier (.app (.lam (.var 0)) argument) argument) = true := by
  simp [betaIdentityLeftCode, StructuralConversionCode.Code.check,
    StructuralConversionCode.Code.decode, StructuralConversionCode.StepCode.decode,
    StructuralConversionCode.mapEndpoints,
    StructuralConversionCode.reverseEndpoints, inst0, subst]

variable (R : Rules Head) [DecidableEq Head] [DecidableRel R.headEq]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]
variable (decoder : StructuralConversionCode.RootDecoder R.computation)

def betaConversionCheck {k : Nat}
    (code : StructuralConversionCode.Code Head decoder.Code k)
    (left right : Tm Head k) : Bool :=
  code.check R.headEq decoder.decode left right

/-- Build the actual finite typing evidence. The argument's certificate and
target formation are inputs; the conversion payload is constructed here. -/
def betaIdentityLeftProof
    (carrier argument : Tm Head n) (level : Head)
    (argumentCode targetFormation : Code Head
      (StructuralConversionCode.Code Head decoder.Code) n) :
    Code Head (StructuralConversionCode.Code Head decoder.Code) n :=
  .convert (.id carrier argument argument) level
    (.reflIntro carrier argumentCode) targetFormation
    (betaIdentityLeftCode (RootCode := decoder.Code) carrier argument)

/-- The cast checks only when its source argument and expanded target type
formation check. This is finite evidence replay, not proof search. -/
theorem betaIdentityLeftProof_checked
    (context : Ctx Head n) (carrier argument : Tm Head n) (level : Head)
    (argumentCode targetFormation : Code Head
      (StructuralConversionCode.Code Head decoder.Code) n)
    (isUniverse : R.isUniverse level)
    (argumentChecked : check R (betaConversionCheck R decoder) context
      argument carrier argumentCode = true)
    (targetChecked : check R (betaConversionCheck R decoder) context
      (.id carrier (.app (.lam (.var 0)) argument) argument)
      (.head level) targetFormation = true) :
    check R (betaConversionCheck R decoder) context (.refl argument)
      (.id carrier (.app (.lam (.var 0)) argument) argument)
      (betaIdentityLeftProof R decoder carrier argument level
        argumentCode targetFormation) = true := by
  simp [betaIdentityLeftProof, check, isUniverse, argumentChecked, targetChecked,
    betaConversionCheck, betaIdentityLeftCode_checked]

/-- Soundness is inherited from the selected decoder and the existing
replay-soundness theorem; neither is reconstructed from an erased term. -/
theorem betaIdentityLeftProof_typing
    (context : Ctx Head n) (carrier argument : Tm Head n) (level : Head)
    (argumentCode targetFormation : Code Head
      (StructuralConversionCode.Code Head decoder.Code) n)
    (isUniverse : R.isUniverse level)
    (argumentChecked : check R (betaConversionCheck R decoder) context
      argument carrier argumentCode = true)
    (targetChecked : check R (betaConversionCheck R decoder) context
      (.id carrier (.app (.lam (.var 0)) argument) argument)
      (.head level) targetFormation = true) :
    FormationSensitive.Typing R context (.refl argument)
      (.id carrier (.app (.lam (.var 0)) argument) argument) := by
  exact check_sound R (betaConversionCheck R decoder)
    (fun accepted => StructuralConversionCode.Code.check_sound decoder accepted)
    (betaIdentityLeftProof R decoder carrier argument level argumentCode targetFormation)
    (betaIdentityLeftProof_checked R decoder context carrier argument level
      argumentCode targetFormation isUniverse argumentChecked targetChecked)

#print axioms betaIdentityLeftCode_checked
#print axioms betaIdentityLeftProof_checked
#print axioms betaIdentityLeftProof_typing

end StructuralTypingReplay
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
