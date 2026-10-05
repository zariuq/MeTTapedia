import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraQuotient
import Mettapedia.TypeTheory.MaterialSets.Hypersets.Finality

/-!
# Contextual coalgebra of bare material membership

Bare hypersets inhabit the successor host universe, while a graph's actual
root occurrences inhabit the original graph universe. Quotient induction
into propositions proves that membership has a small cover at every
future without choosing a graph or member representative.

Constant material membership gives a natural small-covered coalgebra. Its
contextual bisimilarity is exactly hyperset equality, by membership
coinduction at the identity future. Its greatest-bisimulation quotient has
constructed natural inverse maps to the original material carrier.

A source readout is a coalgebra map precisely when it preserves the entire
future membership-image law. Naturality into this constant material family
requires denotation preservation. No contextual finality or surjectivity
onto all stable future predicates is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialCoalgebra

open CategoryTheory PowerClassPresheafBaseChange
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u v
variable {D : Type u} [Category.{u} D]

def ambient : D ⥤ Type (u + 1) where
  obj _ := HSet.{u}
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def children (point : D) (value : HSet.{u}) :
    CoveredFuturePowerFamilies.Predicate (ambient (D := D)) point where
  holds argument := argument.2 ∈ value
  closed {_ _} move available := move.2 ▸ available

/-- Graph root occurrences give a common small cover of every future.
Graph induction is used only inside the proposition of cover existence. -/
theorem children_covered (point : D) (value : HSet.{u}) :
    Nonempty (CoveredFuturePowerFamilies.Enumeration (children point value)) := by
  induction value using HSet.ind with
  | mk graph =>
    refine ⟨{
      Carrier := fun _ => {node : graph.Node // graph.edge graph.point node}
      value := fun _ receipt => HSet.decorate graph.edge receipt.val
      covered := ?_ }⟩
    intro _future argument
    change argument ∈ HSet.mk graph ↔
      ∃ receipt : {node : graph.Node // graph.edge graph.point node},
        HSet.decorate graph.edge receipt.val = argument
    constructor
    · intro available
      obtain ⟨node, edge, same⟩ := HSet.mem_mk.mp available
      exact ⟨⟨node, edge⟩, same⟩
    · rintro ⟨receipt, same⟩
      exact HSet.mem_mk.mpr ⟨receipt.val, receipt.property, same⟩

def coalgebra : NaturalHom (ambient (D := D))
    (CoveredFuturePowerFamilies.family (ambient (D := D))) where
  app point value := ⟨children point value, children_covered point value⟩
  naturality _ _ := by
    apply Subtype.ext
    apply CoveredFuturePowerFamilies.Predicate.ext
    intro _
    exact Iff.rfl

theorem membership_truth (point : D) (value : HSet.{u})
    (future : Future.Objects point) (argument : HSet.{u}) :
    (coalgebra.app point value).val.holds ⟨future, argument⟩ ↔ argument ∈ value := Iff.rfl

theorem separated : ContextualCoalgebraQuotient.BehaviorallySeparated (coalgebra (D := D)) := by
  intro point left right related
  obtain ⟨relation, bisimulation, related⟩ := related
  apply HSet.eq_of_isBisimulation (R := relation point) _ related
  intro first second same
  constructor
  · intro child available
    exact bisimulation.forth same ⟨point, 𝟙 point⟩ available
  · intro child available
    exact bisimulation.back same ⟨point, 𝟙 point⟩ available

theorem bisimilar_iff_eq (point : D) (first second : HSet.{u}) :
    ContextualCoalgebraBisimulation.Bisimilar (coalgebra (D := D)) point first second ↔ first = second := by
  constructor
  · exact separated point first second
  · intro same
    cases same
    exact ContextualCoalgebraBisimulation.bisimilar_refl coalgebra point first

abbrev classes := ContextualCoalgebraQuotient.family (coalgebra (D := D))
abbrev observe := ContextualCoalgebraQuotient.projection (coalgebra (D := D))

theorem class_eq_iff (point : D) (first second : HSet.{u}) :
    observe.app point first = observe.app point second ↔ first = second :=
  (ContextualCoalgebraQuotient.projection_eq_iff coalgebra point first second).trans
    (bisimilar_iff_eq point first second)

def decode : NaturalHom (classes (D := D)) ambient :=
  ContextualCoalgebraQuotient.descend coalgebra (CoveredFuturePowerFunctor.identityHom ambient)
    (fun point {_ _} related => separated point _ _ related)

theorem decode_observe (point : D) (value : HSet.{u}) :
    decode.app point (observe.app point value) = value := rfl

theorem observe_decode (point : D) (value : classes.obj point) :
    observe.app point (decode.app point value) = value :=
  Quotient.inductionOn value fun _ => rfl

def materialEquiv (point : D) : classes.obj point ≃ HSet.{u} where
  toFun := decode.app point
  invFun := observe.app point
  left_inv := observe_decode point
  right_inv := decode_observe point

theorem decode_natural {first second : D} (step : first ⟶ second) (value : classes.obj first) :
    decode.app second (classes.map step value) = decode.app first value :=
  (decode.naturality step value).symm

theorem decode_coalgebra :
    (ContextualCoalgebraQuotient.coalgebra (coalgebra (D := D))).comp
      (CoveredFuturePowerFunctor.imageHom decode) = decode.comp coalgebra := by
  apply ContextualCoalgebraQuotient.descend_coalgebra
  apply NaturalHom.ext
  intro point value
  exact CoveredFuturePowerFunctor.imagePower_identity point (coalgebra.app point value)

variable {A : D ⥤ Type v}

/-- An authored denotation has a natural readout exactly when its context
action preserves that value. This construction selects no set graph. -/
def readout (values : ∀ point, A.obj point → HSet.{u})
    (stable : ∀ {first second} (step : first ⟶ second) (argument : A.obj first),
      values second (A.map step argument) = values first argument) : NaturalHom A ambient where
  app := values
  naturality step argument := (stable step argument).symm

theorem readout_restriction (reading : NaturalHom A (ambient (D := D)))
    {first second : D} (step : first ⟶ second) (argument : A.obj first) :
    reading.app second (A.map step argument) = reading.app first argument :=
  (reading.naturality step argument).symm

theorem coalgebra_readout_iff (source : NaturalHom A (CoveredFuturePowerFamilies.family A))
    (reading : NaturalHom A (ambient (D := D))) :
    source.comp (CoveredFuturePowerFunctor.imageHom reading) = reading.comp coalgebra ↔
      ∀ point (argument : A.obj point) (future : Future.Objects point) (value : HSet.{u}),
        HSet.Mem (reading.app point argument) value ↔
          ∃ child, reading.app future.1 child = value ∧
            (source.app point argument).val.holds ⟨future, child⟩ := by
  constructor
  · intro square point argument future value
    exact ContextualCoalgebraBisimulation.coalgebra_map_truth source reading coalgebra square
      point argument future value
  · intro exactImage
    apply NaturalHom.ext
    intro point argument
    apply Subtype.ext
    apply CoveredFuturePowerFamilies.Predicate.ext
    intro child
    exact (exactImage point argument child.1 child.2).symm

theorem source_bisimilar_iff_reading_eq
    (source : NaturalHom A (CoveredFuturePowerFamilies.family A))
    (reading : NaturalHom A (ambient (D := D)))
    (square : source.comp (CoveredFuturePowerFunctor.imageHom reading) = reading.comp coalgebra)
    (point : D) (first second : A.obj point) :
    ContextualCoalgebraBisimulation.Bisimilar source point first second ↔
      reading.app point first = reading.app point second :=
  (ContextualCoalgebraBisimulation.bisimilar_map_iff source reading coalgebra square point first second).symm.trans
    (bisimilar_iff_eq point (reading.app point first) (reading.app point second))

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialCoalgebra
