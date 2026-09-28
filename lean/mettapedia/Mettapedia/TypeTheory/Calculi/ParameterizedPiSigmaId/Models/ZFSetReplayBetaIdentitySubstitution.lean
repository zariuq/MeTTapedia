import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayBetaIdentitySubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplaySubstitution

/-!
# The checked beta-identity substitution square

The finite one-sided beta cast is stable under the actual replay-certificate
substitution, and its set value reindexes along the assembled substitution
images. Root-decoder naturality is needed for preservation of checking; the
beta path itself contains no root request. The image certificates and their
set meanings remain explicit evidence, not reconstructed erased terms.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay

universe u
variable {Head : Type}
variable (R : Rules Head) [DecidableEq Head] [DecidableRel R.headEq]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]
variable (decoder : StructuralConversionCode.RootDecoder R.computation)
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})

/-- Checked certificate substitution and semantic reindexing commute for
the beta-expanded identity proof at any checked, computed argument. The
substituted tree is definitionally the generic constructor applied to the
transformed premises, not merely some extensionally equal proof. -/
theorem betaIdentityLeftProof_substitution_square
    (renameConversion : {n m : Nat} → Ren n m →
      StructuralConversionCode.Code Head decoder.Code n →
      StructuralConversionCode.Code Head decoder.Code m)
    (substituteRoot : {n m : Nat} → Sub Head n m → decoder.Code n → decoder.Code m)
    (renamePreserves : ∀ {n m} (rho : Ren n m)
      (code : StructuralConversionCode.Code Head decoder.Code n)
      {left right : Tm Head n},
      betaConversionCheck R decoder code left right = true →
      betaConversionCheck R decoder (renameConversion rho code)
        (rename rho left) (rename rho right) = true)
    (rootNatural : ∀ {n m : Nat} (σ : Sub Head n m) (code : decoder.Code n),
      decoder.decode (substituteRoot σ code) =
        StructuralConversionCode.mapEndpoints (subst σ) (decoder.decode code))
    {n m : Nat} (sourceContext : Ctx Head n) (targetContext : Ctx Head m)
    (σ : Sub Head n m)
    (imageCodes : Fin n → Code Head (StructuralConversionCode.Code Head decoder.Code) m)
    (images : Fin n → Meaning.{u} m)
    (imagesChecked : ∀ index, check R (betaConversionCheck R decoder) targetContext
      (σ index) (subst σ (sourceContext.lookup index)) (imageCodes index) = true)
    (atImages : ∀ index, assemble heads constants (imageCodes index) (σ index)
      (subst σ (sourceContext.lookup index)) = some (images index))
    (carrier argument : Tm Head n) (level : Head)
    (argumentCode targetFormation : Code Head
      (StructuralConversionCode.Code Head decoder.Code) n)
    (sourceMeaning : Meaning.{u} n)
    (sourceChecked : check R (betaConversionCheck R decoder) sourceContext (.refl argument)
      (.id carrier (.app (.lam (.var 0)) argument) argument)
      (betaIdentityLeftProof R decoder carrier argument level argumentCode targetFormation) = true)
    (atSource : assemble heads constants
      (betaIdentityLeftProof R decoder carrier argument level argumentCode targetFormation)
      (.refl argument) (.id carrier (.app (.lam (.var 0)) argument) argument) =
      some sourceMeaning) :
    let substitutedArgumentCode := argumentCode.substitute renameConversion
      (StructuralConversionCode.Code.substitute substituteRoot)
      σ imageCodes argument carrier
    let substitutedFormation := targetFormation.substitute renameConversion
      (StructuralConversionCode.Code.substitute substituteRoot)
      σ imageCodes (.id carrier (.app (.lam (.var 0)) argument) argument) (.head level)
    let substitutedProof := betaIdentityLeftProof R decoder (subst σ carrier)
      (subst σ argument) level substitutedArgumentCode substitutedFormation
    check R (betaConversionCheck R decoder) targetContext (.refl (subst σ argument))
      (.id (subst σ carrier) (.app (.lam (.var 0)) (subst σ argument)) (subst σ argument))
      substitutedProof = true ∧
    ∃ result,
      assemble heads constants substitutedProof (.refl (subst σ argument))
        (.id (subst σ carrier) (.app (.lam (.var 0)) (subst σ argument)) (subst σ argument)) =
          some result ∧
      ∀ env, result.value env = sourceMeaning.value (imageEnvironment images env) := by
  dsimp only
  have conversionSubstitution : ∀ {n m : Nat} (τ : Sub Head n m)
      (code : StructuralConversionCode.Code Head decoder.Code n)
      {left right : Tm Head n},
      betaConversionCheck R decoder code left right = true →
      betaConversionCheck R decoder
        (StructuralConversionCode.Code.substitute substituteRoot τ code)
        (subst τ left) (subst τ right) = true := by
    intro k l τ code left right accepted
    exact StructuralConversionCode.Code.check_substitute substituteRoot R.headEq
      decoder.decode rootNatural τ code accepted
  have checked := StructuralTypingReplay.check_substitute renameConversion
    (StructuralConversionCode.Code.substitute substituteRoot) R
    (betaConversionCheck R decoder) renamePreserves conversionSubstitution
    (betaIdentityLeftProof R decoder carrier argument level argumentCode targetFormation)
    sourceChecked σ imageCodes imagesChecked
  obtain ⟨result, atResult, values, _⟩ :=
    assemble_substitute renameConversion
      (StructuralConversionCode.Code.substitute substituteRoot) heads constants R
      (betaConversionCheck R decoder)
      (betaIdentityLeftProof R decoder carrier argument level argumentCode targetFormation)
      sourceMeaning sourceChecked atSource σ imageCodes images atImages
  rw [betaIdentityLeftProof_substitute R decoder renameConversion substituteRoot σ imageCodes
    carrier argument level argumentCode targetFormation] at checked atResult
  refine ⟨?_, result, ?_, values⟩
  · simpa only [subst, liftSub_zero] using checked
  · simpa only [subst, liftSub_zero] using atResult

#print axioms betaIdentityLeftProof_substitution_square

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
