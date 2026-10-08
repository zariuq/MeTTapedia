import Mettapedia.CategoryTheory.PredicateDoctrine

/-!
# Cartesian classification in an indexed predicate doctrine

A total arrow is Cartesian exactly when its domain predicate is the inverse
image of its codomain predicate. Hence the generic predicate's characteristic
map gives a Cartesian classification, and every Cartesian classification is
that unique arrow. These statements concern the actual Grothendieck projection.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.PredicateDoctrine

open _root_.CategoryTheory _root_.CategoryTheory.Functor Opposite

universe u v w
variable {B : Type u} [Category.{v} B]

namespace IndexedHeyting

variable (D : IndexedHeyting.{u,v,w} B)

abbrev predicate (a : D.Total) : D.Fiber a.base := a.fiber

theorem hom_ext {a b : D.Total} (f g : a ⟶ b) (base : f.base = g.base) : f = g := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ base ?_
  exact @Subsingleton.elim
    ((show D.Fiber a.base from a.fiber) ⟶ D.reindex f.base b.fiber)
    inferInstance _ _

def homOfEntailment {a b : D.Total} (f : a.base ⟶ b.base)
    (entails : D.predicate a ≤ D.reindex f (D.predicate b)) : a ⟶ b :=
  (D.totalHomEquiv a b).symm ⟨f, entails⟩

theorem hom_entailment {a b : D.Total} (f : a ⟶ b) :
    D.predicate a ≤ D.reindex f.base (D.predicate b) :=
  ((D.totalHomEquiv a b) f).property

/-- Predicate equality suffices for the full Cartesian universal property
over every preceding base map. -/
theorem cartesian_of_predicate_eq {a b : D.Total} (arrow : a ⟶ b)
    (exactDomain : D.predicate a = D.reindex arrow.base (D.predicate b)) :
    IsStronglyCartesian D.projection arrow.base arrow := by
  have : IsHomLift D.projection arrow.base arrow := IsHomLift.map D.projection arrow
  constructor
  intro preceding g supplied suppliedOver
  have base : supplied.base = g ≫ arrow.base :=
    (@IsHomLift.eq_of_isHomLift _ _ _ _ D.projection preceding b
      (g ≫ arrow.base) supplied suppliedOver).symm
  have entails : D.predicate preceding ≤ D.reindex g (D.predicate a) := by
    rw [exactDomain, ← D.reindex_comp, ← base]
    exact D.hom_entailment supplied
  let factor := D.homOfEntailment g entails
  refine ⟨factor, ⟨IsHomLift.map D.projection factor, ?_⟩, ?_⟩
  · apply D.hom_ext
    exact base.symm
  · intro other reading
    apply D.hom_ext
    exact (@IsHomLift.eq_of_isHomLift _ _ _ _ D.projection preceding a
      g other reading.1).symm

/-- Cartesian factorization of the canonical inverse-image lift recovers
the converse predicate equality. -/
theorem predicate_eq_of_cartesian {a b : D.Total} (arrow : a ⟶ b)
    [IsStronglyCartesian D.projection arrow.base arrow] :
    D.predicate a = D.reindex arrow.base (D.predicate b) := by
  apply le_antisymm (D.hom_entailment arrow)
  obtain ⟨factor, reading, _⟩ :=
    IsStronglyCartesian.universal_property D.projection arrow.base arrow
      (𝟙 a.base) arrow.base (by simp) (D.lift (D.predicate b) arrow.base)
  have base : factor.base = 𝟙 a.base :=
    (@IsHomLift.eq_of_isHomLift _ _ _ _ D.projection
      (D.liftDomain (D.predicate b) arrow.base) a (𝟙 a.base) factor reading.1).symm
  have entails := D.hom_entailment factor
  change D.reindex arrow.base (D.predicate b) ≤ D.reindex factor.base (D.predicate a)
    at entails
  rw [base, D.reindex_id] at entails
  exact entails

theorem cartesian_iff_predicate_eq {a b : D.Total} (arrow : a ⟶ b) :
    IsStronglyCartesian D.projection arrow.base arrow ↔
      D.predicate a = D.reindex arrow.base (D.predicate b) := by
  constructor
  · intro cartesian
    have := cartesian
    exact D.predicate_eq_of_cartesian arrow
  · exact D.cartesian_of_predicate_eq arrow

end IndexedHeyting

namespace GenericPredicate

variable {D : IndexedHeyting.{u,v,w} B} (G : GenericPredicate B D)

abbrev totalTruth : D.Total := ⟨G.object, G.truth⟩

/-- The characteristic map with the actual entailment into truth. -/
def classify (a : D.Total) : a ⟶ G.totalTruth :=
  D.homOfEntailment (G.characteristic a.base (D.predicate a))
    (le_of_eq (G.classifies a.base (D.predicate a)).symm)

theorem classify_base (a : D.Total) :
    (G.classify a).base = G.characteristic a.base (D.predicate a) := rfl

theorem classify_cartesian (a : D.Total) :
    IsStronglyCartesian D.projection (G.classify a).base (G.classify a) :=
  D.cartesian_of_predicate_eq (G.classify a)
    (G.classifies a.base (D.predicate a)).symm

/-- A Cartesian arrow to the generic predicate must have the independently
classified base map; faithfulness then determines its whole total arrow. -/
theorem classify_unique (a : D.Total) (arrow : a ⟶ G.totalTruth)
    [IsStronglyCartesian D.projection arrow.base arrow] : arrow = G.classify a := by
  apply D.hom_ext
  exact G.unique a.base (D.predicate a) arrow.base
    (D.predicate_eq_of_cartesian arrow).symm

/-- The generic object classifies every total predicate by exactly one
Cartesian arrow. Entailing arrows without exact inverse-image domains are
not included in this universal property. -/
theorem unique_cartesian_classification (a : D.Total) :
    ∃! arrow : a ⟶ G.totalTruth,
      IsStronglyCartesian D.projection arrow.base arrow := by
  refine ⟨G.classify a, G.classify_cartesian a, ?_⟩
  intro arrow cartesian
  have := cartesian
  exact G.classify_unique a arrow

end GenericPredicate

end Mettapedia.CategoryTheory.PredicateDoctrine
