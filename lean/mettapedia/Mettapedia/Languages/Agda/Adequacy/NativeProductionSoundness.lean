import Mettapedia.Languages.Agda.Native.Selection
import Mettapedia.Languages.Agda.Adequacy.AdministrativeReflection

/-!
# Independent source soundness of structural proof production

Only this adequacy consumer imports both the structural producer and the
independent source interpretation. A successful search supplies a native tree;
reflection of that tree supplies the source derivation. The producer does not
read the source specification or its metatheoretic proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Native.Production

open Mettapedia.Languages.Agda
open Mettapedia.OSLF.Binding.FiniteRuleSearch
open Structural.Statics
open StaticAdequacy

/-- Arbitrary supported raw syntax receives an actual successful source
observation, rather than only a structural typing flag. -/
theorem typing_sound {n : Nat} (Γ : RawContext n) (t : RawTm n) (A : RawTy n)
    (fuel : Nat) (positive : (run fuel (.core (typed Γ t A))).isEstablished = true) :
    Nonempty (Reflection.ReflectedTyping Γ t A) := by
  rcases (Verdict.established_iff _).mp positive with ⟨tree, _⟩
  exact ⟨AdministrativeReflection.reflectTyping tree⟩

/-- On an independently specified input, successful structural execution
returns a derivation of exactly that source typing judgment. -/
theorem embedded_typing_sound {n : Nat} (Γ : StaticSpecification.RawContext n)
    (t : StaticSpecification.Term n) (A : StaticSpecification.Ty n) (fuel : Nat)
    (positive : (run fuel (.core
      (typed (embedContext Γ) (embedTerm t) (embedTy A)))).isEstablished = true) :
    Nonempty (StaticSpecification.Typing Γ t A) := by
  rcases (Verdict.established_iff _).mp positive with ⟨tree, _⟩
  exact ⟨AdministrativeReflection.typingBack tree⟩

theorem embedded_formation_sound {n : Nat} (Γ : StaticSpecification.RawContext n)
    (A : StaticSpecification.Ty n) (fuel : Nat)
    (positive : (run fuel (.core
      (formed (embedContext Γ) (embedTy A)))).isEstablished = true) :
    Nonempty (StaticSpecification.FormTy Γ A) := by
  rcases (Verdict.established_iff _).mp positive with ⟨tree, _⟩
  exact ⟨AdministrativeReflection.formationBack tree⟩

theorem embedded_context_sound {n : Nat} (Γ : StaticSpecification.RawContext n)
    (fuel : Nat) (positive : (run fuel (.core
      (context (embedContext Γ)))).isEstablished = true) :
    Nonempty (StaticSpecification.FormCtx Γ) := by
  rcases (Verdict.established_iff _).mp positive with ⟨tree, _⟩
  exact ⟨AdministrativeReflection.contextBack tree⟩

#print axioms typing_sound
#print axioms embedded_typing_sound

end Mettapedia.Languages.Agda.Native.Production
