import Mettapedia.CategoryTheory.PredicateDoctrine
import Mettapedia.GSLT.Topos.PresheafPredicateProjection
import Mettapedia.GSLT.Topos.PresheafPredicateHeyting
import Mettapedia.GSLT.Topos.PresheafPredicateQuantifierBaseChange
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-!
# First-order logic of the actual presheaf predicate projection

Inverse image is a Heyting substitution functor. Its two adjoints are the
actual existential image and the universal predicate quantifying every future
restriction. Their Frobenius and pullback base-change laws provide fibred
equality and simple quantification on the same indexed action whose
Grothendieck projection was already constructed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.PresheafPredicateFirstOrder

open _root_.CategoryTheory _root_.CategoryTheory.Limits
  _root_.CategoryTheory.Functor Opposite MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory.PredicateDoctrine

universe u
variable {C : Type u} [Category.{u} C]

/-- Substitution preserves disjunction, including predicates whose truth
varies over the indexing category. -/
theorem preimage_sup {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q) (φ ψ : Subfunctor Q) :
    (φ ⊔ ψ).preimage f = φ.preimage f ⊔ ψ.preimage f := rfl

theorem preimage_bot {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q) :
    (⊥ : Subfunctor Q).preimage f = ⊥ := rfl

/-- Frobenius retains the same existential witness while testing its
image against the target predicate. -/
theorem image_frobenius {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q)
    (φ : Subfunctor P) (ψ : Subfunctor Q) :
    (φ ⊓ ψ.preimage f).image f = φ.image f ⊓ ψ := by
  ext world value
  constructor
  · rintro ⟨argument, ⟨first, second⟩, over⟩
    exact ⟨⟨argument, first, over⟩, over ▸ second⟩
  · rintro ⟨⟨argument, first, over⟩, second⟩
    refine ⟨argument, ⟨first, ?_⟩, over⟩
    change f.app world argument ∈ ψ.obj world
    rw [over]
    exact second

/-- The actual indexed Heyting action, with all finite logical operations
and implication stable under arbitrary presheaf substitution. -/
noncomputable def indexed (C : Type u) [Category.{u} C] :
    IndexedHeyting.{u+1,u,u} (Cᵒᵖ ⥤ Type u) where
  Fiber := Subfunctor
  algebra _ := inferInstance
  reindex f φ := φ.preimage f
  reindex_mono _ := fun _ _ below world _ member => below world member
  reindex_id _ := Subfunctor.preimage_id
  reindex_comp f g := fun φ => Subfunctor.preimage_comp φ f g
  reindex_top _ := rfl
  reindex_bot _ := rfl
  reindex_inf _ _ _ := rfl
  reindex_sup _ _ _ := rfl
  reindex_himp f φ ψ := preimage_himp φ ψ f

/-- Both quantified adjunctions and Frobenius hold along every actual map.
The base-change hypotheses are genuine pullbacks, not commuting squares. -/
noncomputable def firstOrder (C : Type u) [Category.{u} C] :
    FirstOrder.{u+1,u,u} (Cᵒᵖ ⥤ Type u) where
  toIndexedHeyting := indexed C
  existsAlong f φ := φ.image f
  forallAlong f φ := Topos.forallAlong f φ
  exists_mono _ := fun _ _ below world _ ⟨argument, member, over⟩ =>
    ⟨argument, below world member, over⟩
  forall_mono f := forallAlong_mono f
  exists_adj f := fun φ ψ => Subfunctor.image_le_iff φ f ψ
  forall_adj f := galois_preimage_forallAlong f
  frobenius := image_frobenius
  exists_baseChange := image_beckChevalley
  forall_baseChange := forallAlong_beckChevalley

/-- The new categorical action is the original predicate action, including
its maps. It does not replace the chosen projection by a frame-only record. -/
theorem indexedFunctor_eq_original :
    (indexed C).indexedFunctor = presheafPredicateFunctor C := by
  rfl

/-- The actual total projection is therefore the doctrine projection. -/
theorem projection_eq_original :
    (indexed C).projection = presheafPredicateProjection C := by
  rfl

/-- The left categorical adjoint of the chosen actual reindexing functor. -/
noncomputable def existsAdjunction {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q) :
    (firstOrder C).existsFunctor f ⊣ predicateReindex f :=
  (firstOrder C).existsAdjunction f

/-- The right categorical adjoint of that same actual reindexing functor. -/
noncomputable def forallAdjunction {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q) :
    predicateReindex f ⊣ (firstOrder C).forallFunctor f :=
  (firstOrder C).forallAdjunction f

/-- Equality is the image of truth under the actual diagonal. -/
noncomputable def equality (P : Cᵒᵖ ⥤ Type u) : Subfunctor (P ⊗ P) :=
  (firstOrder C).equality P

/-- The equality predicate is genuine equality of the two supplied
generalized elements, rather than equality of their present truth values. -/
theorem mem_equality (P : Cᵒᵖ ⥤ Type u) (world : Cᵒᵖ)
    (value : (P ⊗ P).obj world) :
    value ∈ (equality P).obj world ↔ value.1 = value.2 := by
  change (∃ argument : P.obj world, argument ∈ (⊤ : Subfunctor P).obj world ∧
    (argument, argument) = value) ↔ value.1 = value.2
  constructor
  · rintro ⟨argument, _, same⟩
    exact (congrArg Prod.fst same).symm.trans (congrArg Prod.snd same)
  · intro same
    exact ⟨value.1, trivial, Prod.ext rfl same⟩

theorem equality_reflexive (P : Cᵒᵖ ⥤ Type u) :
    (equality P).preimage (lift (𝟙 P) (𝟙 P)) = ⊤ := by
  ext world argument
  constructor
  · intro _
    trivial
  · intro _
    exact (mem_equality P world ((lift (𝟙 P) (𝟙 P)).app world argument)).mpr rfl

/-- Diagonal equality is the left adjoint to contraction on predicate
categories, with its complete hom correspondence. -/
noncomputable def diagonalAdjunction (P : Cᵒᵖ ⥤ Type u) :
    (firstOrder C).existsFunctor (lift (𝟙 P) (𝟙 P)) ⊣
      predicateReindex (lift (𝟙 P) (𝟙 P)) :=
  existsAdjunction _

theorem diagonal_frobenius (P : Cᵒᵖ ⥤ Type u)
    (φ : Subfunctor P) (ψ : Subfunctor (P ⊗ P)) :
    (φ ⊓ ψ.preimage (lift (𝟙 P) (𝟙 P))).image (lift (𝟙 P) (𝟙 P)) =
      φ.image (lift (𝟙 P) (𝟙 P)) ⊓ ψ :=
  image_frobenius _ _ _

/-- The simple existential quantifier uses the actual projection. -/
noncomputable def simpleExistsAdjunction (P Q : Cᵒᵖ ⥤ Type u) :
    (firstOrder C).existsFunctor (snd P Q) ⊣ predicateReindex (snd P Q) :=
  existsAdjunction _

/-- The simple universal quantifier uses that same actual projection. -/
noncomputable def simpleForallAdjunction (P Q : Cᵒᵖ ⥤ Type u) :
    predicateReindex (snd P Q) ⊣ (firstOrder C).forallFunctor (snd P Q) :=
  forallAdjunction _

end Mettapedia.GSLT.Topos.PresheafPredicateFirstOrder
