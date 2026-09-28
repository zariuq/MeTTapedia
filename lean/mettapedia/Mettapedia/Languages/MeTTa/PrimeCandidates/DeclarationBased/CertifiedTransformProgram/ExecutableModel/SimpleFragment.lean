import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TypedEqualityEmbedding
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueSound

/-!
# The simple fragment of the executable dependent package

The actual package's own head rules instantiate the generic fragment theorem.
Translated simple terms are native `Typed objectRules` terms and inherit the
package's normalization theorem. There is no separate simple-type authority.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC
open IntrinsicSTT TowerDTT TypedEqualityEmbedding SubstitutionTranslation
open CodeModel

theorem simpleHeadRules : HeadRules objectRules :=
  ⟨.legacyGround, fun _ => .sort _, fun _ _ => .sorts _ _⟩

theorem simple_typed {Γ : List Ty} {A : Ty} (t : Term Γ A) :
    Typed objectRules (eraseContext Γ) (eraseTerm t) (eraseTypeAt Γ.length A) :=
  term_typed simpleHeadRules t

theorem simple_beta {Γ : List Ty} {A B : Ty}
    (body : Term (A :: Γ) B) (argument : Term Γ A) :
    Equal objectRules (eraseContext Γ) (eraseTerm (.app (.lam body) argument))
      (eraseTerm (body.instantiateNewest argument)) (eraseTypeAt Γ.length B) :=
  beta_equal simpleHeadRules body argument

theorem simple_substitution {Γ Δ : List Ty} {A : Ty}
    (σ : Substitution Γ Δ) (t : Term Γ A) :
    eraseTerm (t.substitute σ) = subst (eraseSubstitution σ) (eraseTerm t) ∧
    Typed objectRules (eraseContext Δ) (subst (eraseSubstitution σ) (eraseTerm t))
      (eraseTypeAt Δ.length A) :=
  substitution_square simpleHeadRules σ t

theorem simple_sn {Γ : List Ty} {A : Ty} (t : Term Γ A) :
    StrongNormalization.SN objectRules (eraseTerm t) ∧
    StrongNormalization.SN objectRules (eraseTypeAt Γ.length A) :=
  objectRules_sn (context_formed simpleHeadRules Γ) (simple_typed t)

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
