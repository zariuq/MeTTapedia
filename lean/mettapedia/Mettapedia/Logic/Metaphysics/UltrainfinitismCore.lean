import Foundation.FirstOrder.Ultraproduct
import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# The ultrainfinitist formal core: relative truth, the precise/open dial, Łoś transfer

The wrapper layer the ultrainfinitism paper names as its missing formal core:

* `UltraTrue 𝓤 P` (paper: *ultrainfinitistly true*) — truth from the perspective of the
  ultrafilter `𝓤`, the verdict of the relative One `(M, 𝓤)`.
* **Principal collapse** (`ultraTrue_pure`) — from a principal perspective, ultrafilter
  truth is just truth at the generating coordinate: the finite is the principal shadow.
* `PreciseFamily` / `OpenFamily` — the dial: a family of verdicts is *precise* when all
  perspectives agree, *open* when the verdict is genuinely perspectival. The envelope
  theorems (`ultraTrue_all_iff`, `ultraTrue_exists_iff`) identify the lower/upper
  envelope over all perspectives with the universal/existential coordinate verdicts, and
  `openFamily_iff_not_precise` is the dichotomy.
* **Free vs principal** (`hyperfilter_pure_disagree`) — the free One affirms what every
  cofinite stage affirms while a finite coordinate-shadow denies it.
* **Łoś transfer** (`ultraTrue_iff_uprod`, `ultrapower_elementary`) — ultrainfinitist
  truth of a first-order sentence along a family IS truth in the ultraproduct; in
  particular a structure is elementarily equivalent to all its ultrapowers. Thin
  restatements of `LO.FirstOrder.models_Uprod` in the wrapper vocabulary.

Invariance (`ultraTrue_map`): re-coordinatizing the index re-coordinatizes the One and
changes nothing else — the indexed-One invariance the paper promises.
-/

namespace Mettapedia.Logic.Metaphysics

universe u

variable {I : Type u}

/-- Truth from the perspective of the ultrafilter `𝓤` — the verdict of the relative One
`(M, 𝓤)`: the proposition holds `𝓤`-almost-everywhere. (Paper name:
*ultrainfinitistly true*.) -/
def UltraTrue (𝓤 : Ultrafilter I) (P : I → Prop) : Prop := ∀ᶠ i in 𝓤, P i

/-- **Principal collapse.** From a principal perspective, ultrafilter truth is truth at
the generating coordinate: the finite is the principal shadow of the One. -/
@[simp] theorem ultraTrue_pure (i : I) (P : I → Prop) :
    UltraTrue (pure i) P ↔ P i := by
  simp [UltraTrue]

/-- **Invariance.** Re-coordinatizing the index re-coordinatizes the One; the verdict
is unchanged. -/
theorem ultraTrue_map {J : Type u} (e : I → J) (𝓤 : Ultrafilter I) (P : J → Prop) :
    UltraTrue (𝓤.map e) P ↔ UltraTrue 𝓤 (fun i => P (e i)) := by
  simp [UltraTrue]

/-- An ultrafilter never suspends judgment: the negation of `𝓤`-truth is `𝓤`-truth of
the negation. -/
theorem ultraTrue_not_iff (𝓤 : Ultrafilter I) (P : I → Prop) :
    ¬ UltraTrue 𝓤 P ↔ UltraTrue 𝓤 (fun i => ¬ P i) := by
  rw [UltraTrue, UltraTrue, Filter.eventually_iff, Filter.eventually_iff]
  exact (Ultrafilter.compl_mem_iff_notMem (s := {i | P i})).symm

/-- A family of verdicts is **precise** when every perspective agrees. -/
def PreciseFamily (P : I → Prop) : Prop :=
  (∀ 𝓤 : Ultrafilter I, UltraTrue 𝓤 P) ∨ (∀ 𝓤 : Ultrafilter I, ¬ UltraTrue 𝓤 P)

/-- A family of verdicts is **open** when the verdict is genuinely perspectival: some
perspective affirms and some denies. -/
def OpenFamily (P : I → Prop) : Prop :=
  ∃ 𝓤 𝓥 : Ultrafilter I, UltraTrue 𝓤 P ∧ ¬ UltraTrue 𝓥 P

/-- Lower envelope: affirmed from every perspective iff true at every coordinate. -/
theorem ultraTrue_all_iff (P : I → Prop) :
    (∀ 𝓤 : Ultrafilter I, UltraTrue 𝓤 P) ↔ ∀ i, P i :=
  ⟨fun h i => (ultraTrue_pure i P).mp (h (pure i)),
   fun h _ => Filter.Eventually.of_forall h⟩

/-- Upper envelope: affirmed from some perspective iff true at some coordinate. -/
theorem ultraTrue_exists_iff (P : I → Prop) :
    (∃ 𝓤 : Ultrafilter I, UltraTrue 𝓤 P) ↔ ∃ i, P i :=
  ⟨fun ⟨_, h⟩ => Ultrafilter.nonempty_of_mem (Filter.eventually_iff.mp h),
   fun ⟨i, hi⟩ => ⟨pure i, (ultraTrue_pure i P).mpr hi⟩⟩

/-- Precision is degeneracy: a family is precise iff the coordinates never disagree. -/
theorem preciseFamily_iff (P : I → Prop) :
    PreciseFamily P ↔ (∀ i, P i) ∨ (∀ i, ¬ P i) := by
  unfold PreciseFamily
  rw [ultraTrue_all_iff]
  refine or_congr Iff.rfl ⟨fun h i hi => ?_, fun h 𝓤 hP => ?_⟩
  · exact h (pure i) ((ultraTrue_pure i P).mpr hi)
  · obtain ⟨i, hi⟩ := Ultrafilter.nonempty_of_mem (Filter.eventually_iff.mp hP)
    exact h i hi

/-- Openness is genuine disagreement among the coordinates. -/
theorem openFamily_iff (P : I → Prop) :
    OpenFamily P ↔ (∃ i, P i) ∧ (∃ i, ¬ P i) := by
  unfold OpenFamily
  constructor
  · rintro ⟨𝓤, 𝓥, h1, h2⟩
    refine ⟨(ultraTrue_exists_iff P).mp ⟨𝓤, h1⟩, ?_⟩
    rw [ultraTrue_not_iff] at h2
    exact (ultraTrue_exists_iff _).mp ⟨𝓥, h2⟩
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨pure i, pure j, (ultraTrue_pure i P).mpr hi, by simp [hj]⟩

/-- **The dial dichotomy.** A family is open exactly when it is not precise: the verdict
is perspectival exactly when the coordinates genuinely disagree. -/
theorem openFamily_iff_not_precise (P : I → Prop) :
    OpenFamily P ↔ ¬ PreciseFamily P := by
  rw [openFamily_iff, preciseFamily_iff]
  simp only [not_or, not_forall]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1.imp fun _ hi => not_not_intro hi⟩,
    fun ⟨h1, h2⟩ => ⟨h2.imp fun _ hi => not_not.mp hi, h1⟩⟩

/-- **Free vs principal.** The free One affirms what every cofinite stage affirms
(here: "is nonzero"), while a finite coordinate-shadow denies it: the same family is
true from the free perspective and false from a principal one. -/
theorem hyperfilter_pure_disagree :
    UltraTrue (Filter.hyperfilter ℕ) (fun n => n ≠ 0) ∧
      ¬ UltraTrue (pure 0) (fun n : ℕ => n ≠ 0) := by
  constructor
  · show {n : ℕ | n ≠ 0} ∈ Filter.hyperfilter ℕ
    apply Filter.mem_hyperfilter_of_finite_compl
    have : {n : ℕ | n ≠ 0}ᶜ = {0} := by ext n; simp
    rw [this]
    exact Set.finite_singleton 0
  · simp

/-! ## Łoś transfer -/

section Los

open LO FirstOrder FirstOrder.Structure

variable {L : Language.{u}} {A : I → Type u} [(i : I) → Structure L (A i)]
  [Nonempty I] [(i : I) → Nonempty (A i)]

/-- **Łoś transfer**, wrapper form: ultrainfinitist truth of a first-order sentence
along the family IS truth in the ultraproduct — the invariant bridge between the
coordinates and the One. -/
theorem ultraTrue_iff_uprod (𝓤 : Ultrafilter I) (φ : Sentence L) :
    UltraTrue 𝓤 (fun i => A i ⊧ₘ φ) ↔ (Uprod A 𝓤) ⊧ₘ φ := by
  rw [models_Uprod]
  exact Iff.rfl

/-- A structure is elementarily equivalent to every ultrapower of itself: the One built
over constant coordinates validates exactly the coordinate's first-order truths. -/
theorem ultrapower_elementary {B : Type u} [Structure L B] [Nonempty B]
    (𝓤 : Ultrafilter I) (φ : Sentence L) :
    (Uprod (fun _ : I => B) 𝓤) ⊧ₘ φ ↔ B ⊧ₘ φ := by
  rw [← ultraTrue_iff_uprod]
  constructor
  · intro h
    obtain ⟨_, hi⟩ := Ultrafilter.nonempty_of_mem (Filter.eventually_iff.mp h)
    exact hi
  · intro h
    exact Filter.Eventually.of_forall fun _ => h

end Los

end Mettapedia.Logic.Metaphysics

