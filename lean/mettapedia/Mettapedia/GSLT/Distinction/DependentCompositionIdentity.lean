import Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialIdentityObservation

/-!
# Dependent identity elimination through composite observations

`GroupoidIdentityElimination` constructs dependent `J` for coherent motives (functors
on the arrow category) and proves that it commutes with one path-respecting
substitution functor (`J_sub_section`). `MaterialIdentityObservation` applies this
to the discrete material readout of presentation identities (`J_readout`), and
shows that a family descending through a discrete observation, even up to a
natural fibre equivalence, acts trivially on every loop.

Exact observation maps act on identity witnesses as functors. This module proves
that the comparison survives composition with them.

* **The reflexivity comparison composes** (`reflexivitySquare_compose`,
  `reindexReflexivity_compose`): the boundary comparison of a composite is the
  composite of the boundary comparisons, on the nose.
* **J through composites** (`J_compose`, `J_compose_staged`): eliminating along a
  composite in one step and in two steps give the same section, the reindexing
  of the original `J`.
* **The material case** (`J_readout_compose`, `J_readout_compose_staged`): for
  every functor `φ` into the presentation groupoid, `J` through `φ` followed by
  the discrete readout is the material `J` reindexed, and the staged form passes
  through `J_readout`.
* **Natural descent composes** (`naturalTrans`, `naturalWhisker`,
  `descendCompose`): descent through `φ` up to natural fibre equivalence followed
  by descent through `ψ` is descent through the composite.
* **The loop obstruction persists** (`loop_trivial_through_readout`,
  `no_descent_through_readout`): a family descending through any composite that
  ends in the discrete readout acts trivially on loops; a family with a loop
  moving an element descends through none of them.

These are comparisons between constructed identity models. They do not
interpret a syntax, select a foundation, or replace intensional identity by
material equality.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.DependentCompositionIdentity

open CategoryTheory
open Mettapedia.TypeTheory.GroupoidIdentityElimination
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialIdentityObservation

universe u v w u' v' u'' v'' u₃ v₃

local infixr:80 " ⋙₀ " => compose

section Composites

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]

/-- **The boundary square of a composite substitution is the composite of the
boundary squares.** -/
theorem reflexivitySquare_compose (τ : E ⥤ D) (σ : D ⥤ C) (object : E) :
    reflexivitySquare σ (τ.obj object) ≫ σ.mapArrow.map (reflexivitySquare τ object) =
      reflexivitySquare (τ ⋙₀ σ) object := by
  apply Arrow.hom_ext
  · change 𝟙 (σ.obj (τ.obj object)) ≫ σ.map (𝟙 (τ.obj object)) = 𝟙 (σ.obj (τ.obj object))
    rw [σ.map_id, Category.id_comp]
  · change 𝟙 (σ.obj (τ.obj object)) ≫ σ.map (𝟙 (τ.obj object)) = 𝟙 (σ.obj (τ.obj object))
    rw [σ.map_id, Category.id_comp]

/-- **The reflexivity comparison of a composite is the composite of the
comparisons.** -/
theorem reindexReflexivity_compose (τ : E ⥤ D) (σ : D ⥤ C) (motive : Arrow C ⥤ Type w)
    (atReflexivity : NaturalSection (diagonal ⋙₀ motive)) :
    reindexReflexivity τ (σ.mapArrow ⋙₀ motive) (reindexReflexivity σ motive atReflexivity) =
      reindexReflexivity (τ ⋙₀ σ) motive atReflexivity := by
  apply NaturalSection.ext
  funext object
  change motive.map (σ.mapArrow.map (reflexivitySquare τ object))
      (motive.map (reflexivitySquare σ (τ.obj object))
        (atReflexivity.value (σ.obj (τ.obj object)))) =
    motive.map (reflexivitySquare (τ ⋙₀ σ) object) (atReflexivity.value (σ.obj (τ.obj object)))
  rw [← ConcreteCategory.comp_apply, ← motive.map_comp, reflexivitySquare_compose]
  rfl

/-- **J through a composite in one step** is the reindexed `J`. -/
theorem J_compose (τ : E ⥤ D) (σ : D ⥤ C) (motive : Arrow C ⥤ Type w)
    (atReflexivity : NaturalSection (diagonal ⋙₀ motive)) :
    J ((τ ⋙₀ σ).mapArrow ⋙₀ motive) (reindexReflexivity (τ ⋙₀ σ) motive atReflexivity) =
      ((J motive atReflexivity).reindex σ.mapArrow).reindex τ.mapArrow := by
  apply NaturalSection.ext
  funext witness
  exact J_sub (τ ⋙₀ σ) motive atReflexivity witness

/-- **J through a composite in two steps** is the same reindexed `J`. -/
theorem J_compose_staged (τ : E ⥤ D) (σ : D ⥤ C) (motive : Arrow C ⥤ Type w)
    (atReflexivity : NaturalSection (diagonal ⋙₀ motive)) :
    J (τ.mapArrow ⋙₀ σ.mapArrow ⋙₀ motive)
        (reindexReflexivity τ (σ.mapArrow ⋙₀ motive) (reindexReflexivity σ motive atReflexivity)) =
      ((J motive atReflexivity).reindex σ.mapArrow).reindex τ.mapArrow := by
  rw [J_sub_section τ (σ.mapArrow ⋙₀ motive), J_sub_section σ motive]

end Composites

/-! ## The material readout after an exact observation map -/

section Material

variable {E : Type u''} [Category.{v''} E]

/-- **J through a discrete readout survives composition with an exact
observation map** into the presentation groupoid. -/
theorem J_readout_compose (φ : E ⥤ AccessiblePointedGraph.{u})
    (motive : Arrow (Discrete HSet.{u}) ⥤ Type w)
    (atReflexivity : NaturalSection (diagonal ⋙₀ motive)) :
    J ((φ ⋙₀ readout).mapArrow ⋙₀ motive) (reindexReflexivity (φ ⋙₀ readout) motive atReflexivity) =
      ((J motive atReflexivity).reindex readout.mapArrow).reindex φ.mapArrow :=
  J_compose φ readout motive atReflexivity

/-- The staged form passes through the material comparison `J_readout`. -/
theorem J_readout_compose_staged (φ : E ⥤ AccessiblePointedGraph.{u})
    (motive : Arrow (Discrete HSet.{u}) ⥤ Type w)
    (atReflexivity : NaturalSection (diagonal ⋙₀ motive)) :
    J (φ.mapArrow ⋙₀ readout.mapArrow ⋙₀ motive)
        (reindexReflexivity φ (readout.mapArrow ⋙₀ motive)
          (reindexReflexivity readout motive atReflexivity)) =
      ((J motive atReflexivity).reindex readout.mapArrow).reindex φ.mapArrow := by
  rw [J_sub_section φ (readout.mapArrow ⋙₀ motive), J_readout]

end Material

/-! ## Natural descent through composites -/

section Natural

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]

/-- Natural fibre equivalences compose. -/
def naturalTrans {F G H : C ⥤ Type w} (first : NaturalEquivalence F G)
    (second : NaturalEquivalence G H) : NaturalEquivalence F H where
  fibre point := (first.fibre point).trans (second.fibre point)
  natural arrow element := by
    change second.fibre _ (first.fibre _ (F.map arrow element)) =
      H.map arrow (second.fibre _ (first.fibre _ element))
    rw [first.natural, second.natural]

/-- Natural fibre equivalences reindex along every functor. -/
def naturalWhisker (φ : E ⥤ C) {F G : C ⥤ Type w} (comparison : NaturalEquivalence F G) :
    NaturalEquivalence (φ ⋙₀ F) (φ ⋙₀ G) where
  fibre point := comparison.fibre (φ.obj point)
  natural arrow element := comparison.natural (φ.map arrow) element

/-- **Composites descend**: descent through `φ` followed by descent through `ψ`,
each up to natural fibre equivalence, is descent through the composite. -/
def descendCompose (φ : E ⥤ C) (ψ : C ⥤ D) {F : E ⥤ Type w} {G : C ⥤ Type w}
    {H : D ⥤ Type w} (first : NaturalEquivalence F (φ ⋙₀ G))
    (second : NaturalEquivalence G (ψ ⋙₀ H)) : NaturalEquivalence F ((φ ⋙₀ ψ) ⋙₀ H) :=
  naturalTrans first (naturalWhisker φ second)

/-- Conversely, descent through a composite is descent through its first stage,
with the rest of the composite as the observed family. -/
def descendFirst (φ : E ⥤ C) (ψ : C ⥤ D) {F : E ⥤ Type w} {H : D ⥤ Type w}
    (composite : NaturalEquivalence F ((φ ⋙₀ ψ) ⋙₀ H)) : NaturalEquivalence F (φ ⋙₀ (ψ ⋙₀ H)) :=
  composite

end Natural

section Obstruction

variable {E : Type u''} [Category.{v''} E]

/-- **A family descending through any composite ending in the discrete
readout acts trivially on every loop.** -/
theorem loop_trivial_through_readout (φ : E ⥤ AccessiblePointedGraph.{u})
    (family : E ⥤ Type w) (observed : Discrete HSet.{u} ⥤ Type w)
    (comparison : NaturalEquivalence family ((φ ⋙₀ readout) ⋙₀ observed)) {point : E}
    (loop : point ⟶ point) (element : family.obj point) : family.map loop element = element :=
  loop_action_trivial_of_discrete_descent (φ ⋙₀ readout) family observed comparison loop element

/-- **A loop moving an element blocks descent through every such composite.** -/
theorem no_descent_through_readout (φ : E ⥤ AccessiblePointedGraph.{u})
    (family : E ⥤ Type w) {point : E} (loop : point ⟶ point) (element : family.obj point)
    (moves : family.map loop element ≠ element) :
    ¬ ∃ observed : Discrete HSet.{u} ⥤ Type w,
      Nonempty (NaturalEquivalence family ((φ ⋙₀ readout) ⋙₀ observed)) := by
  rintro ⟨observed, ⟨comparison⟩⟩
  exact moves (loop_trivial_through_readout φ family observed comparison loop element)

end Obstruction

end Mettapedia.GSLT.Distinction.DependentCompositionIdentity
