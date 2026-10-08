import Mettapedia.CategoryTheory.ElementaryToposPredicateAdjoints

/-!
# Heyting fibres from an elementary subobject classifier

The least predicate is universal truth over the classifier. Binary joins use
the higher-order continuation formula, quantified over the classifier. The
proofs establish their order universal properties before assembling the
Heyting algebra; no initial object, coproduct, or pre-existing logical
lattice is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposPredicateHeyting

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open ElementaryToposPredicateAdjoints ElementaryToposStableEpimorphisms

universe u v
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable [HasPullbacks C] [HasEqualizers C]
variable (classifier : Subobject.Classifier C)

def truth : Subobject classifier.Ω := Subobject.mk classifier.truth

def characteristic {X : C} (P : Subobject X) : X ⟶ classifier.Ω :=
  classifier.χ P.arrow

omit [CartesianMonoidalCategory C] [MonoidalClosed C] [HasEqualizers C] in
theorem classifies {X : C} (P : Subobject X) :
    reindex (characteristic classifier P) (truth classifier) = P := by
  simpa only [reindex, characteristic, truth, Subobject.mk_arrow] using
    classifier.pullback_χ_obj_mk_truth P.arrow

omit [CartesianMonoidalCategory C] [MonoidalClosed C] [HasEqualizers C] in
theorem characteristic_unique {X : C} (P : Subobject X) (f : X ⟶ classifier.Ω)
    (same : reindex f (truth classifier) = P) : f = characteristic classifier P := by
  have classified := classifier.χ_pullback_obj_mk_truth_arrow f
  change characteristic classifier (reindex f (truth classifier)) = f at classified
  rw [same] at classified
  exact classified.symm

theorem reindex_implication_le {X Y : C} (f : X ⟶ Y) (P Q : Subobject Y) :
    reindex f (implication classifier P Q) ≤
      implication classifier (reindex f P) (reindex f Q) := by
  apply (implication_adj classifier _ _ _).mpr
  rw [← reindex_inf]
  exact reindex_mono f (implication_evaluation classifier P Q)

omit [CartesianMonoidalCategory C] [MonoidalClosed C] [HasEqualizers C] in
theorem mono_inf {X Y : C} (f : X ⟶ Y) [Mono f] (P : Subobject Y) :
    Subobject.mk f ⊓ P = (Subobject.map f).obj (reindex f P) :=
  Subobject.inf_eq_map_pullback' (MonoOver.mk f) P

/-- A monic parameter satisfying an implication's two sides lies in that
implication. This uses its actual mono direct-image adjunction. -/
theorem mono_reindex_implication_eq_top {X Y : C} (f : X ⟶ Y) [Mono f]
    (P Q : Subobject Y) (held : reindex f P ≤ reindex f Q) :
    reindex f (implication classifier P Q) = ⊤ := by
  apply eq_top_iff.mpr
  apply (map_adj f ⊤ (implication classifier P Q)).mp
  rw [Subobject.map_top, implication_adj, mono_inf]
  exact (map_adj f _ _).mpr held

def least (X : C) : Subobject X :=
  forallAlong classifier (fst X classifier.Ω)
    (reindex (snd X classifier.Ω) (truth classifier))

theorem least_le {X : C} (P : Subobject X) : least classifier X ≤ P := by
  have pulled := reindex_mono (graph (characteristic classifier P))
    (forall_counit classifier (fst X classifier.Ω)
      (reindex (snd X classifier.Ω) (truth classifier)))
  simpa only [least, ← reindex_comp, graph, lift_fst, lift_snd,
    reindex_id, classifies] using pulled

def union {X : C} (P Q : Subobject X) : Subobject X :=
  let p := reindex (fst X classifier.Ω) P
  let q := reindex (fst X classifier.Ω) Q
  let r := reindex (snd X classifier.Ω) (truth classifier)
  forallAlong classifier (fst X classifier.Ω)
    (implication classifier
      (implication classifier p r ⊓ implication classifier q r) r)

theorem le_union_left {X : C} (P Q : Subobject X) : P ≤ union classifier P Q := by
  apply (forall_adj classifier (fst X classifier.Ω) P _).mp
  apply (implication_adj classifier _ _ _).mpr
  exact (inf_le_inf le_rfl inf_le_left).trans
    (by simpa only [inf_comm] using (implication_evaluation classifier
      (reindex (fst X classifier.Ω) P) (reindex (snd X classifier.Ω) (truth classifier))))

theorem le_union_right {X : C} (P Q : Subobject X) : Q ≤ union classifier P Q := by
  apply (forall_adj classifier (fst X classifier.Ω) Q _).mp
  apply (implication_adj classifier _ _ _).mpr
  exact (inf_le_inf le_rfl inf_le_right).trans
    (by simpa only [inf_comm] using (implication_evaluation classifier
      (reindex (fst X classifier.Ω) Q) (reindex (snd X classifier.Ω) (truth classifier))))

theorem union_le {X : C} (P Q R : Subobject X) (first : P ≤ R) (second : Q ≤ R) :
    union classifier P Q ≤ R := by
  let k := graph (characteristic classifier R)
  let p := reindex (fst X classifier.Ω) P
  let q := reindex (fst X classifier.Ω) Q
  let r := reindex (snd X classifier.Ω) (truth classifier)
  have pRead : reindex k p = P := by
    simp only [k, p, ← reindex_comp, graph, lift_fst, reindex_id]
  have qRead : reindex k q = Q := by
    simp only [k, q, ← reindex_comp, graph, lift_fst, reindex_id]
  have rRead : reindex k r = R := by
    simp only [k, r, ← reindex_comp, graph, lift_snd, classifies]
  have firstTruth : reindex k (implication classifier p r) = ⊤ :=
    mono_reindex_implication_eq_top classifier k p r (by rw [pRead, rRead]; exact first)
  have secondTruth : reindex k (implication classifier q r) = ⊤ :=
    mono_reindex_implication_eq_top classifier k q r (by rw [qRead, rRead]; exact second)
  have candidate := reindex_implication_le classifier k
    (implication classifier p r ⊓ implication classifier q r) r
  rw [reindex_inf, firstTruth, secondTruth, top_inf_eq, rRead,
    implication_top_left] at candidate
  have universal := reindex_mono k (forall_counit classifier (fst X classifier.Ω)
    (implication classifier (implication classifier p r ⊓ implication classifier q r) r))
  have unionRead : reindex k (reindex (fst X classifier.Ω) (union classifier P Q)) =
      union classifier P Q := by
    simp only [k, ← reindex_comp, graph, lift_fst, reindex_id]
  change reindex k (reindex (fst X classifier.Ω) (union classifier P Q)) ≤ _ at universal
  rw [unionRead] at universal
  exact universal.trans candidate

@[instance_reducible]
def lattice (X : C) : Lattice (Subobject X) where
  __ := (inferInstance : SemilatticeInf (Subobject X))
  sup := union classifier
  le_sup_left := le_union_left classifier
  le_sup_right := le_union_right classifier
  sup_le := union_le classifier

@[instance_reducible]
def algebra (X : C) : HeytingAlgebra (Subobject X) where
  __ := lattice classifier X
  __ := (inferInstance : OrderTop (Subobject X))
  bot := least classifier X
  bot_le := least_le classifier
  himp := implication classifier
  compl P := implication classifier P (least classifier X)
  le_himp_iff := implication_adj classifier
  himp_bot _ := rfl

end Mettapedia.CategoryTheory.ElementaryToposPredicateHeyting
