import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayBetaIdentityConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplaySubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSubstitution

/-!
# Substitution of checked beta-expanded identity evidence

The one-sided beta code is structural: substituting it never asks the root
decoder for a new conversion step. Substitution of the enclosing typing tree
therefore retains the original reflexivity proof, substituted argument proof,
substituted target formation, and the same beta constructor.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralTypingReplay

variable {Head : Type} {RootCode : Nat → Type}

/-- Structural beta evidence is natural under every scoped simultaneous
substitution, independently of the action chosen for declared root codes. -/
theorem betaIdentityLeftCode_substitute
    (substituteRoot : {n m : Nat} → Sub Head n m → RootCode n → RootCode m)
    {n m : Nat} (σ : Sub Head n m) (carrier argument : Tm Head n) :
    (betaIdentityLeftCode (RootCode := RootCode) carrier argument).substitute
      substituteRoot σ =
    betaIdentityLeftCode (RootCode := RootCode) (subst σ carrier) (subst σ argument) := by
  simp [betaIdentityLeftCode, StructuralConversionCode.Code.substitute,
    StructuralConversionCode.StepCode.substitute]

variable (R : Rules Head)
variable (decoder : StructuralConversionCode.RootDecoder R.computation)

/-- The *actual* typing-certificate substitution produces the same
beta-expanded identity proof as rebuilding the generic construction from
the substituted premise certificates. The target formation remains an
independent input, rather than being inferred from the source proof. -/
theorem betaIdentityLeftProof_substitute
    (renameConversion : {n m : Nat} → Ren n m →
      StructuralConversionCode.Code Head decoder.Code n →
      StructuralConversionCode.Code Head decoder.Code m)
    (substituteRoot : {n m : Nat} → Sub Head n m → decoder.Code n → decoder.Code m)
    {n m : Nat} (σ : Sub Head n m)
    (imageCodes : Fin n → Code Head (StructuralConversionCode.Code Head decoder.Code) m)
    (carrier argument : Tm Head n) (level : Head)
    (argumentCode targetFormation : Code Head
      (StructuralConversionCode.Code Head decoder.Code) n) :
    (betaIdentityLeftProof R decoder carrier argument level argumentCode targetFormation).substitute
      renameConversion (StructuralConversionCode.Code.substitute substituteRoot)
      σ imageCodes (.refl argument)
      (.id carrier (.app (.lam (.var 0)) argument) argument) =
    betaIdentityLeftProof R decoder (subst σ carrier) (subst σ argument) level
      (argumentCode.substitute renameConversion
        (StructuralConversionCode.Code.substitute substituteRoot)
        σ imageCodes argument carrier)
      (targetFormation.substitute renameConversion
        (StructuralConversionCode.Code.substitute substituteRoot)
        σ imageCodes (.id carrier (.app (.lam (.var 0)) argument) argument) (.head level)) := by
  simp [betaIdentityLeftProof, Code.substitute, betaIdentityLeftCode_substitute, subst]

#print axioms betaIdentityLeftCode_substitute
#print axioms betaIdentityLeftProof_substitute

end StructuralTypingReplay
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
