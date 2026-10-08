import Mettapedia.TypeTheory.PresheafNativePredicateQuantifierSubstitution
import Mettapedia.TypeTheory.PresheafNativePredicateRefinementControls

/-!
# Native quantifiers under a nonidentity context substitution

The native fibre `Fin n` is empty at zero and inhabited at one. Advancing
the supplied context changes existential and universal readouts through the
actual weakening and extension-substitution maps. Omitting this map gives
the wrong proposition, rather than merely a different type presentation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafNativePredicateQuantifierControls

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open ContextualLocalUniverses NativeLocalTypeFormers
open NativeLocalTheoryTransformation
open PresheafNativePredicateRefinementControls
open PresheafNativePredicateQuantifierSubstitution

abbrev possiblyEmpty : DisplayedFamily programs where
  obj point := Fin point.2
  map arrow := TypeCat.ofHom fun value => Fin.cast arrow.property value
  map_id _ := by ext value; rfl
  map_comp _ _ := by ext value; rfl

abbrev argument : NativeType programs := LocalType.present possiblyEmpty

theorem universal_at_empty :
    0 ∈ (nativeForall argument ⊥).obj world := by
  intro future restriction receipt over
  change receipt.1 = 0 at over
  rcases receipt with ⟨n, evidence⟩
  change n = 0 at over
  cases over
  exact Fin.elim0 evidence

theorem universal_at_inhabited_false :
    1 ∉ (nativeForall argument ⊥).obj world := by
  intro holds
  exact holds world (𝟙 world) ⟨1, (⟨0, by decide⟩ : Fin 1)⟩ rfl

theorem actual_universal_substitution :
    (nativeForall argument ⊥).preimage advance =
      nativeForall (argument.reindex advance)
        ((⊥ : Subfunctor (totalSpace argument.decoded)).preimage
          (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
            (C := (nativeLocalModel World).toCwf) advance argument)) :=
  nativeForall_substitution advance argument ⊥

theorem omitted_universal_substitution_changes_truth :
    (nativeForall argument ⊥).preimage advance ≠ nativeForall argument ⊥ := by
  intro same
  have atZero : 0 ∈ ((nativeForall argument ⊥).preimage advance).obj world := by
    rw [same]
    exact universal_at_empty
  exact universal_at_inhabited_false atZero

theorem existential_at_empty_false : 0 ∉ (nativeExists argument ⊤).obj world := by
  rintro ⟨receipt, _, over⟩
  change receipt.1 = 0 at over
  rcases receipt with ⟨n, evidence⟩
  change n = 0 at over
  cases over
  exact Fin.elim0 evidence

theorem existential_at_inhabited : 1 ∈ (nativeExists argument ⊤).obj world :=
  ⟨⟨1, (⟨0, by decide⟩ : Fin 1)⟩, trivial, rfl⟩

theorem actual_existential_substitution :
    (nativeExists argument ⊤).preimage advance =
      nativeExists (argument.reindex advance)
        ((⊤ : Subfunctor (totalSpace argument.decoded)).preimage
          (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
            (C := (nativeLocalModel World).toCwf) advance argument)) :=
  nativeExists_substitution advance argument ⊤

theorem omitted_existential_substitution_changes_truth :
    (nativeExists argument ⊤).preimage advance ≠ nativeExists argument ⊤ := by
  intro same
  have atZero : 0 ∈ ((nativeExists argument ⊤).preimage advance).obj world :=
    existential_at_inhabited
  rw [same] at atZero
  exact existential_at_empty_false atZero

theorem actual_image_substitution :
    (nativeImage argument).preimage advance = nativeImage (argument.reindex advance) :=
  nativeImage_substitution advance argument

end Mettapedia.TypeTheory.PresheafNativePredicateQuantifierControls
