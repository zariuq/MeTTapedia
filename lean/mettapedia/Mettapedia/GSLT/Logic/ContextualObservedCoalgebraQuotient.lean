import Mettapedia.GSLT.Logic.ContextualObservedCoalgebraTransport
import Mettapedia.TypeTheory.ContextualKernelQuotients

/-!
# A natural quotient of complete observed contextual behavior

The actual material equality kernel is stable under every context arrow.
Its quotient is an actual contextual family. Matching all observed future
children constructs its whole coalgebra, and quotient elimination constructs
each atomic valuation. The projection has an exact observed-bisimulation
kernel and preserves its material value and all declared modal formulas.

The quotient has no further observed behavioral identifications. Its
natural maps are exactly the source maps that respect the observed kernel;
this gives exact predicate/term factorization without choosing a receipt.
Dependent families still need their family and term compatibility evidence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ContextualObservedCoalgebraQuotient

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualCoalgebraLabelledGraph ContextualObservedCoalgebra

universe u v
variable {D : Type u} [Category.{u} D] {A : D ⥤ Type u}
variable (source : NaturalHom A (CoveredFuturePowerFamilies.family A))
variable {Atom : Type u} (atoms : Atom → State A → Prop)
variable (worlds : ArgumentCoding D)
variable (arrows : (first second : D) → ArgumentCoding (first ⟶ second))
variable (atomCoding : ArgumentCoding Atom)

abbrev observed (point : D) (argument : A.obj point) : HSet.{u} :=
  value source atoms worlds arrows atomCoding ⟨point, argument⟩

def kernel (point : D) : Setoid (A.obj point) where
  r first second := observed source atoms worlds arrows atomCoding point first =
    observed source atoms worlds arrows atomCoding point second
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

theorem kernel_stable {first second : D} (step : first ⟶ second) {left right : A.obj first}
    (same : (kernel source atoms worlds arrows atomCoding first).r left right) :
    (kernel source atoms worlds arrows atomCoding second).r (A.map step left) (A.map step right) := by
  obtain ⟨relation, bisimulation, related⟩ :=
    (value_eq_iff source atoms worlds arrows atomCoding first left right).mp same
  exact (value_eq_iff source atoms worlds arrows atomCoding second _ _).mpr
    ⟨relation, bisimulation, bisimulation.underlying.stable step related⟩

def family : D ⥤ Type u where
  obj point := Quotient (kernel source atoms worlds arrows atomCoding point)
  map {first second} step := TypeCat.ofHom (Quotient.map
    (sa := kernel source atoms worlds arrows atomCoding first)
    (sb := kernel source atoms worlds arrows atomCoding second) (A.map step)
    (fun {_ _} same => kernel_stable source atoms worlds arrows atomCoding step same))
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro term
    refine Quotient.inductionOn term fun argument => ?_
    exact congrArg (Quotient.mk (kernel source atoms worlds arrows atomCoding point))
      (A.map_id_apply point argument)
  map_comp {first _middle last} earlier later := by
    apply ConcreteCategory.hom_ext
    intro term
    refine Quotient.inductionOn term fun argument => ?_
    exact congrArg (Quotient.mk (kernel source atoms worlds arrows atomCoding last))
      (A.map_comp_apply earlier later argument)

def projection : NaturalHom A (family source atoms worlds arrows atomCoding) where
  app point := Quotient.mk (kernel source atoms worlds arrows atomCoding point)
  naturality _ _ := rfl

theorem projection_cover (point : D) : Function.Surjective ((projection source atoms worlds arrows atomCoding).app point) :=
  fun term => Quotient.inductionOn term fun argument => ⟨argument, rfl⟩

theorem projection_eq_iff (point : D) (left right : A.obj point) :
    (projection source atoms worlds arrows atomCoding).app point left =
        (projection source atoms worlds arrows atomCoding).app point right ↔
      ObservedBisimilar source atoms point left right :=
  Iff.trans ⟨Quotient.exact, Quotient.sound⟩
    (value_eq_iff source atoms worlds arrows atomCoding point left right)

theorem projected_power_eq {point : D} {left right : A.obj point}
    (same : (kernel source atoms worlds arrows atomCoding point).r left right) :
    CoveredFuturePowerFunctor.imagePower (projection source atoms worlds arrows atomCoding) point (source.app point left) =
      CoveredFuturePowerFunctor.imagePower (projection source atoms worlds arrows atomCoding) point (source.app point right) := by
  obtain ⟨relation, bisimulation, related⟩ :=
    (value_eq_iff source atoms worlds arrows atomCoding point left right).mp same
  apply Subtype.ext
  apply CoveredFuturePowerFamilies.Predicate.ext
  intro future
  constructor
  · rintro ⟨child, represents, admitted⟩
    obtain ⟨matching, matched, children⟩ := bisimulation.underlying.forth related future.1 admitted
    exact ⟨matching, ((projection_eq_iff source atoms worlds arrows atomCoding future.1.1 child matching).mpr
      ⟨relation, bisimulation, children⟩).symm.trans represents, matched⟩
  · rintro ⟨child, represents, admitted⟩
    obtain ⟨matching, matched, children⟩ := bisimulation.underlying.back related future.1 admitted
    exact ⟨matching, ((projection_eq_iff source atoms worlds arrows atomCoding future.1.1 matching child).mpr
      ⟨relation, bisimulation, children⟩).trans represents, matched⟩

def coalgebra : NaturalHom (family source atoms worlds arrows atomCoding)
    (CoveredFuturePowerFamilies.family (family source atoms worlds arrows atomCoding)) where
  app point := Quotient.lift
    (fun argument => CoveredFuturePowerFunctor.imagePower (projection source atoms worlds arrows atomCoding) point
      (source.app point argument)) (fun _ _ same => projected_power_eq source atoms worlds arrows atomCoding same)
  naturality {first second} step term := by
    refine Quotient.inductionOn term fun argument => ?_
    exact (CoveredFuturePowerFunctor.imagePower_restrict (projection source atoms worlds arrows atomCoding) step
      (source.app first argument)).trans
        (congrArg (CoveredFuturePowerFunctor.imagePower (projection source atoms worlds arrows atomCoding) second)
          (source.naturality step argument))

theorem coalgebra_square : source.comp (CoveredFuturePowerFunctor.imageHom (projection source atoms worlds arrows atomCoding)) =
    (projection source atoms worlds arrows atomCoding).comp (coalgebra source atoms worlds arrows atomCoding) := by
  apply NaturalHom.ext
  intro _ _
  rfl

def quotientAtoms (atom : Atom) (state : State (family source atoms worlds arrows atomCoding)) : Prop :=
  Quotient.lift (fun argument => atoms atom ⟨state.1, argument⟩)
    (fun _ _ same => propext (observed_bisimilar_atoms source atoms
      ((value_eq_iff source atoms worlds arrows atomCoding state.1 _ _).mp same) atom)) state.2

theorem atoms_square (atom : Atom) (state : State A) : atoms atom state ↔
    quotientAtoms source atoms worlds arrows atomCoding atom (graphMap (projection source atoms worlds arrows atomCoding) state) :=
  Iff.rfl

abbrev quotientValue := value (coalgebra source atoms worlds arrows atomCoding)
  (quotientAtoms source atoms worlds arrows atomCoding) worlds arrows atomCoding

theorem value_square (state : State A) : value source atoms worlds arrows atomCoding state =
    quotientValue source atoms worlds arrows atomCoding (graphMap (projection source atoms worlds arrows atomCoding) state) :=
  ContextualObservedCoalgebraTransport.value_preservation source (coalgebra source atoms worlds arrows atomCoding)
    (projection source atoms worlds arrows atomCoding) (coalgebra_square source atoms worlds arrows atomCoding)
    atoms (quotientAtoms source atoms worlds arrows atomCoding) (atoms_square source atoms worlds arrows atomCoding)
    worlds arrows atomCoding state

theorem quotientValue_injective (point : D) : Function.Injective
    (fun term => quotientValue source atoms worlds arrows atomCoding ⟨point, term⟩) := by
  intro first second
  refine Quotient.inductionOn₂ first second fun left right same => ?_
  apply Quotient.sound
  exact (value_square source atoms worlds arrows atomCoding ⟨point, left⟩).trans
    (same.trans (value_square source atoms worlds arrows atomCoding ⟨point, right⟩).symm)

theorem observed_bisimilar_iff_eq (point : D) (left right : (family source atoms worlds arrows atomCoding).obj point) :
    ObservedBisimilar (coalgebra source atoms worlds arrows atomCoding)
        (quotientAtoms source atoms worlds arrows atomCoding) point left right ↔ left = right :=
  (value_eq_iff (coalgebra source atoms worlds arrows atomCoding) (quotientAtoms source atoms worlds arrows atomCoding)
    worlds arrows atomCoding point left right).symm.trans
      ⟨fun same => quotientValue_injective source atoms worlds arrows atomCoding point same,
        fun same => congrArg (fun term => quotientValue source atoms worlds arrows atomCoding ⟨point, term⟩) same⟩

variable {Z : D ⥤ Type v}

def Compatible (operation : NaturalHom A Z) : Prop := ∀ point {left right},
  ObservedBisimilar source atoms point left right → operation.app point left = operation.app point right

def descend (operation : NaturalHom A Z) (compatible : Compatible source atoms operation) :
    NaturalHom (family source atoms worlds arrows atomCoding) Z where
  app point := Quotient.lift (operation.app point)
    (fun _ _ same => compatible point ((value_eq_iff source atoms worlds arrows atomCoding point _ _).mp same))
  naturality step term := Quotient.inductionOn term fun argument => operation.naturality step argument

theorem descend_factorization (operation : NaturalHom A Z) (compatible : Compatible source atoms operation) :
    (projection source atoms worlds arrows atomCoding).comp (descend source atoms worlds arrows atomCoding operation compatible) =
      operation := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem descends_iff (operation : NaturalHom A Z) :
    (∃ factor : NaturalHom (family source atoms worlds arrows atomCoding) Z,
      (projection source atoms worlds arrows atomCoding).comp factor = operation) ↔ Compatible source atoms operation := by
  constructor
  · rintro ⟨factor, rfl⟩ point left right related
    exact congrArg (factor.app point) ((projection_eq_iff source atoms worlds arrows atomCoding point left right).mpr related)
  · intro compatible
    exact ⟨descend source atoms worlds arrows atomCoding operation compatible,
      descend_factorization source atoms worlds arrows atomCoding operation compatible⟩

theorem unique_descend (operation : NaturalHom A Z) (compatible : Compatible source atoms operation) :
    ∃! factor : NaturalHom (family source atoms worlds arrows atomCoding) Z,
      (projection source atoms worlds arrows atomCoding).comp factor = operation := by
  refine ⟨descend source atoms worlds arrows atomCoding operation compatible,
    descend_factorization source atoms worlds arrows atomCoding operation compatible, ?_⟩
  intro candidate factors
  apply NaturalHom.ext
  intro point term
  refine Quotient.inductionOn term fun argument => ?_
  exact congrArg (fun map : NaturalHom A Z => map.app point argument) factors

end Mettapedia.GSLT.ContextualObservedCoalgebraQuotient
