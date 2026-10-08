import Mathlib.CategoryTheory.Subobject.Classifier.Defs
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Types.Basic

/-!
# The Boolean subobject classifier for small types

The characteristic function tests membership in an actual monomorphism's
range. The pullback proof retains the preimage, and uniqueness follows from
the pullback's existence and commuting-square properties. This classical
set model is separate from future-sensitive presheaf classifiers.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.TypeSubobjectClassifier

open _root_.CategoryTheory _root_.CategoryTheory.Limits

def truth : PUnit ⟶ Bool := TypeCat.ofHom fun _ => true

instance truth_mono : Mono truth := by
  apply (mono_iff_injective truth).mpr
  intro _ _ _
  exact Subsingleton.elim _ _

def characteristic {domain codomain : Type} (inclusion : domain ⟶ codomain) : codomain ⟶ Bool :=
  TypeCat.ofHom fun value => @decide (∃ input, inclusion input = value) (Classical.propDecidable _)

@[simp] theorem characteristic_true_iff {domain codomain : Type}
    (inclusion : domain ⟶ codomain) (value : codomain) :
    characteristic inclusion value = true ↔ ∃ input, inclusion input = value := by
  simp only [characteristic, TypeCat.ofHom_apply, decide_eq_true_eq]

def toTruth (domain : Type) : domain ⟶ PUnit := TypeCat.ofHom fun _ => PUnit.unit

theorem characteristic_pullback {domain codomain : Type}
    (inclusion : domain ⟶ codomain) [Mono inclusion] :
    IsPullback inclusion (toTruth domain) (characteristic inclusion) truth := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · ext input
    exact (characteristic_true_iff inclusion (inclusion input)).mpr ⟨input, rfl⟩
  · intro first second equal
    exact (mono_iff_injective inclusion).mp inferInstance equal.1
  · intro value point held
    obtain ⟨input, reaches⟩ := (characteristic_true_iff inclusion value).mp held
    exact ⟨input, reaches, Subsingleton.elim _ _⟩

theorem characteristic_unique {domain codomain : Type}
    (inclusion : domain ⟶ codomain) [Mono inclusion]
    (candidate : codomain ⟶ Bool) (toUnit : domain ⟶ PUnit)
    (pullback : IsPullback inclusion toUnit candidate truth) :
    candidate = characteristic inclusion := by
  ext value
  have positive : candidate value = true ↔ ∃ input, inclusion input = value := by
    constructor
    · intro held
      obtain ⟨input, reaches, _⟩ := Types.exists_of_isPullback pullback value PUnit.unit held
      exact ⟨input, reaches⟩
    · rintro ⟨input, rfl⟩
      exact congrArg (fun arrow : domain ⟶ Bool => arrow input) pullback.w
  apply Bool.eq_iff_iff.mpr
  exact positive.trans (characteristic_true_iff inclusion value).symm

def classifier : Subobject.Classifier (Type) where
  Ω₀ := PUnit
  Ω := Bool
  truth := truth
  χ₀ := toTruth
  χ inclusion _ := characteristic inclusion
  isPullback inclusion _ := characteristic_pullback inclusion
  uniq inclusion _ χ₀' χ' held := characteristic_unique inclusion χ' χ₀' held

end Mettapedia.CategoryTheory.TypeSubobjectClassifier
