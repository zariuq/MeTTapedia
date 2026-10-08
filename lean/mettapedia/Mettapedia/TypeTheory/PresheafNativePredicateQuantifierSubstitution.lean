import Mettapedia.TypeTheory.PresheafNativeClosedSubstitution
import Mettapedia.GSLT.Topos.PresheafPredicateQuantifierBaseChange

/-!
# Quantifier substitution for the actual native context extension

Existential image and future-sensitive universal quantification are taken
along the actual native weakening map. Their substitution laws use the
actual native extension-substitution arrow, whose previously checked total
comparison proves this square is a pullback. Image types use the same
weakening and substitution square.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafNativePredicateQuantifierSubstitution

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder Mettapedia.GSLT.Topos
open DisplayedPresheafTransport DisplayedPresheafComprehension
open ContextualLocalUniverses NativeLocalTypeFormers NativeLocalTheoryTransformation
open PresheafNativeClosedSubstitution

universe u
variable {C : Type u} [Category.{u} C] {P Q : Cᵒᵖ ⥤ Type u}

def nativeExists (A : NativeType P) (predicate : Subfunctor (totalSpace A.decoded)) :
    Subfunctor P :=
  predicate.image ((nativeLocalModel C).toCwf.wk A)

def nativeForall (A : NativeType P) (predicate : Subfunctor (totalSpace A.decoded)) :
    Subfunctor P :=
  forallAlong ((nativeLocalModel C).toCwf.wk A) predicate

def nativeImage (A : NativeType P) : Subfunctor P :=
  Subfunctor.range ((nativeLocalModel C).toCwf.wk A)

set_option backward.isDefEq.respectTransparency false in
theorem native_extension_isPullback (substitution : Q ⟶ P) (A : NativeType P) :
    IsPullback
      (TypeOver.extensionSubstitution (C := (nativeLocalModel C).toCwf) substitution A)
      ((nativeLocalModel C).toCwf.wk (A.reindex substitution))
      ((nativeLocalModel C).toCwf.wk A) substitution := by
  rw [extensionSubstitution_as_total substitution (⟨A⟩ : TypeOver (nativeLocalModel C).toCwf P)]
  exact (totalReindexMap_isPullback substitution A.decoded).flip

theorem nativeForall_substitution (substitution : Q ⟶ P) (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) :
    (nativeForall A predicate).preimage substitution =
      nativeForall (A.reindex substitution)
        (predicate.preimage
          (TypeOver.extensionSubstitution (C := (nativeLocalModel C).toCwf) substitution A)) :=
  forallAlong_beckChevalley _ _ _ _ (native_extension_isPullback substitution A) predicate

theorem nativeExists_substitution (substitution : Q ⟶ P) (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) :
    (nativeExists A predicate).preimage substitution =
      nativeExists (A.reindex substitution)
        (predicate.preimage
          (TypeOver.extensionSubstitution (C := (nativeLocalModel C).toCwf) substitution A)) :=
  image_beckChevalley _ _ _ _ (native_extension_isPullback substitution A) predicate

set_option backward.isDefEq.respectTransparency false in
theorem nativeImage_substitution (substitution : Q ⟶ P) (A : NativeType P) :
    (nativeImage A).preimage substitution = nativeImage (A.reindex substitution) := by
  have existsComparison := nativeExists_substitution substitution A ⊤
  have topPullback : (⊤ : Subfunctor (totalSpace A.decoded)).preimage
      (TypeOver.extensionSubstitution (C := (nativeLocalModel C).toCwf) substitution A) =
      (⊤ : Subfunctor (totalSpace (A.reindex substitution).decoded)) := by
    ext world value
    rfl
  simpa only [nativeExists, nativeImage, topPullback, Subfunctor.image_top] using existsComparison

end Mettapedia.TypeTheory.PresheafNativePredicateQuantifierSubstitution
