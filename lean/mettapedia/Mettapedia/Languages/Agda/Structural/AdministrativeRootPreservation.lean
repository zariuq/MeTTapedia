import Mettapedia.Languages.Agda.Structural.AdministrativeTypingGeneration
import Mettapedia.Languages.Agda.Structural.Reduction

/-!
# Native preservation of administrative root occurrences

Certificates retain the actual structural step and construct native typed
term equality or conditional spine equality from arbitrary source histories.
Typing preservation follows from the proved native endpoint operation.
No observation into another calculus is used.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Preservation

open Mettapedia.OSLF.Binding
open Statics (RawTm RawTy RawContext)

structure TermCertificate {n : Nat} (source target : RawTm n) where
  step : Step source target
  equality : ∀ (Γ : RawContext n) (A : RawTy n), CoreDerivation (Statics.typed Γ source A) →
    CoreDerivation (Statics.termEqual Γ source target A)

structure SpineCertificate {n : Nat} (source target : Spine (scope n)) where
  step : Step source target
  equality : ∀ (Γ : RawContext n) (A B : RawTy n), Action Γ A source B → SpineEq Γ A source target B

noncomputable def TermCertificate.typing {n : Nat} {source target : RawTm n}
    (certificate : TermCertificate source target) {Γ : RawContext n} {A : RawTy n}
    (tree : CoreDerivation (Statics.typed Γ source A)) : CoreDerivation (Statics.typed Γ target A) :=
  (certificate.equality Γ A tree).termEndpoints.right

noncomputable def SpineCertificate.action {n : Nat} {source target : Spine (scope n)}
    (certificate : SpineCertificate source target) {Γ : RawContext n} {A B : RawTy n}
    (tree : Action Γ A source B) (input : CoreDerivation (Statics.formed Γ A)) : Action Γ A target B :=
  (certificate.equality Γ A B tree).endpoints input |>.right

noncomputable def eliminateEmpty {n : Nat} (head : RawTm n) : TermCertificate (eliminate head nil) head where
  step := .root (.eliminateEmpty head)
  equality _ _ tree :=
    let parts := tree.eliminationParts
    Derivation.emptyElimination (parts.action.nilConversion.typing parts.headTyping)

noncomputable def eliminateAppend {n : Nat} (head : RawTm n) (first second : Spine (scope n)) :
    TermCertificate (eliminate (eliminate head first) second) (eliminate head (append first second)) where
  step := .root (.eliminateAppend head first second)
  equality _ _ tree :=
    let outer := tree.eliminationParts
    let inner := outer.headTyping.eliminationParts
    Derivation.nestedElimination inner.headTyping inner.action outer.action

def appendEmpty {n : Nat} (rest : Spine (scope n)) : SpineCertificate (append nil rest) rest where
  step := .root (.appendEmpty rest)
  equality _ _ _ tree := Derivation.appendEmpty tree

noncomputable def appendCons {n : Nat} (head : Elim (scope n)) (first second : Spine (scope n)) :
    SpineCertificate (append (cons head first) second) (cons head (append first second)) where
  step := .root (.appendCons head first second)
  equality Γ A B tree := by
    obtain ⟨u, same⟩ := tree.splitAppend.first.appliedHead
    cases same
    exact Derivation.appendCons tree

/-- Append contraction itself also acts without an input-formation premise. -/
noncomputable def appendEmptyAction {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    {es : Spine (scope n)} (tree : Action Γ A (append nil es) B) : Action Γ A es B := tree.dropEmptyAppend

noncomputable def appendConsAction {n : Nat} {Γ : RawContext n} {A B : RawTy n}
    {e : Elim (scope n)} {es fs : Spine (scope n)} (tree : Action Γ A (append (cons e es) fs) B) :
    Action Γ A (cons e (append es fs)) B := by
  obtain ⟨u, same⟩ := tree.splitAppend.first.appliedHead
  cases same
  exact tree.distributeAppend

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Preservation
