import Mettapedia.GSLT.Topos.PresheafTheoryPseudofunctor
import Mettapedia.GSLT.Topos.PresheafTheoryKanAdjunctions
import Mettapedia.GSLT.Core.LambdaTheoryClosedControls
import Mettapedia.GSLT.Topos.PresheafPredicateHeyting
import Mettapedia.CategoryTheory.PredicateDoctrineClosed
import Mathlib.CategoryTheory.Limits.Lattice

/-!
# Actual theory restriction, universal Kan readouts and logical boundaries

Exchange of diagram coordinates changes the actual restriction of a
representable presheaf. A closed finite-limit map of the Boolean order
has a genuine noninvertible cell whose presheaf direction is reversed.
The same theory map loses a future test and fails to preserve implication,
despite preserving every presheaf limit and colimit.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.GSLT.Topos.PresheafTheoryActionControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open Mettapedia.GSLT.Core PresheafTheoryAction
open scoped _root_.CategoryTheory.SemilatticeInf
open scoped Mettapedia.CategoryTheory.PredicateDoctrine.HeytingClosed

namespace Exchange

open Mettapedia.GSLT.Core.LambdaTheoryClosedControls

def represented : Diagramsᵒᵖ ⥤ Type := yoneda.obj numbers

def supplied : represented.obj (op numbers) := 𝟙 numbers

/-- The new action, evaluated on its actual mapped source arrow, exchanges
which independently authored coordinate increment is observed. -/
theorem swapped_restriction_readout :
    (((theoryInverseImage swapMap).obj represented).map shift.op supplied).app
      ⟨false⟩ (10 : Nat) = (12 : Nat) := rfl

theorem original_restriction_readout :
    (represented.map shift.op supplied).app ⟨false⟩ (10 : Nat) = (11 : Nat) := rfl

theorem omitted_theory_map_changes_value :
    (((theoryInverseImage swapMap).obj represented).map shift.op supplied).app
        ⟨false⟩ (10 : Nat) ≠
      (represented.map shift.op supplied).app ⟨false⟩ (10 : Nat) := by
  rw [swapped_restriction_readout, original_restriction_readout]
  change (12 : Nat) ≠ 11
  omega

theorem actual_composition_readout :
    (((compositionIso swapMap.functor reverseSwapMap.functor).hom.app represented).app
      (op numbers)) supplied = supplied := rfl

/-- Two independently supplied sections remain different in one fibre. -/
theorem represented_has_distinct_values :
    (𝟙 numbers : represented.obj (op numbers)) ≠ shift := by
  intro same
  have components := congrArg (fun value : represented.obj (op numbers) =>
    value.app ⟨false⟩ (10 : Nat)) same
  change (10 : Nat) = 11 at components
  omega

def emptyDiagram : Diagrams := Discrete.functor fun _ => Empty

/-- In contrast with the number-diagram fibre, every two sections in the
empty-diagram fibre agree. Thus the actual fibres have different sizes. -/
theorem empty_fibre_unique (first second : represented.obj (op emptyDiagram)) :
    first = second := by
  apply NatTrans.ext
  funext index
  apply ConcreteCategory.hom_ext
  intro value
  exact Empty.elim value

def empty_fibre_value : represented.obj (op emptyDiagram) := {
  app _ := ↾Empty.elim }

end Exchange

namespace Reversal

def theory : LambdaTheory.{0,0} := LambdaTheory.ofCategory Bool

def topFunctor : Bool ⥤ Bool := (Functor.const Bool).obj true
def bottomFunctor : Bool ⥤ Bool := (Functor.const Bool).obj false

private def bottomTopAdjunction : bottomFunctor ⊣ topFunctor :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun _ _ => {
      toFun := fun _ => homOfLE le_top
      invFun := fun _ => homOfLE bot_le
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _ }
    homEquiv_naturality_left_symm := by intros; apply Subsingleton.elim
    homEquiv_naturality_right := by intros; apply Subsingleton.elim }

instance top_lex : PreservesFiniteLimits topFunctor := by
  let : PreservesLimitsOfSize.{0,0} topFunctor := bottomTopAdjunction.rightAdjoint_preservesLimits
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance top_closed : MonoidalClosedFunctor topFunctor where
  comparison_iso domain := by
    suffices ∀ codomain : Bool,
        IsIso ((expComparison topFunctor domain).natTrans.app codomain) from
      NatIso.isIso_of_isIso_app _
    intro codomain
    have comparison : (expComparison topFunctor domain).natTrans.app codomain = 𝟙 true :=
      Subsingleton.elim _ _
    rw [comparison]
    infer_instance

def topMap : LambdaTheoryMap theory theory where
  functor := topFunctor
  preservesFiniteLimits := top_lex
  preservesExponentials := top_closed

def grow : Functor.id Bool ⟶ topFunctor where
  app _ := homOfLE le_top
  naturality := by intros; apply Subsingleton.elim

def representedFalse : Boolᵒᵖ ⥤ Type := yoneda.obj false

def reversedCell : (inverseImage topFunctor).obj representedFalse ⟶
    (inverseImage (Functor.id Bool)).obj representedFalse := (cell grow).app representedFalse

/-- The opposite direction is impossible on this actual presheaf fibre. -/
theorem no_unreversed_cell :
    ¬ Nonempty ((inverseImage (Functor.id Bool)).obj representedFalse ⟶
      (inverseImage topFunctor).obj representedFalse) := by
  rintro ⟨wrong⟩
  have impossible : (true : Bool) ⟶ false := wrong.app (op false) (𝟙 false)
  exact (not_le_of_gt Bool.false_lt_true) impossible.le

def truthPresheaf : Boolᵒᵖ ⥤ Type := (Functor.const Boolᵒᵖ).obj PUnit

def lower : Subfunctor truthPresheaf where
  obj U := { _value | U.unop = false }
  map {U V} f := by
    intro value lowerWorld
    have included := f.unop.le
    rw [lowerWorld] at included
    exact le_antisymm included bot_le

def restrictPredicate (predicate : Subfunctor truthPresheaf) :
    Subfunctor ((theoryInverseImage topMap).obj truthPresheaf) where
  obj U := predicate.obj (topFunctor.op.obj U)
  map f := predicate.map (topFunctor.op.map f)

theorem lower_future_test :
    PUnit.unit ∈ lower.obj (op false) ∧ PUnit.unit ∉ lower.obj (op true) := by
  exact ⟨rfl, Bool.noConfusion⟩

theorem lower_negation_empty : lower ⇨ (⊥ : Subfunctor truthPresheaf) = ⊥ := by
  rw [← himpPointwise_eq_himp]
  ext U value
  constructor
  · intro holds
    exact holds (op false) (homOfLE (show false ≤ U.unop from bot_le)).op rfl
  · exact False.elim

theorem restrict_lower_empty : restrictPredicate lower = ⊥ := by
  ext U value
  change (true = false) ↔ False
  exact ⟨Bool.noConfusion, False.elim⟩

/-- Losing the future source world changes negation. This is a genuine
closed source-theory map, not merely an arbitrary functor counterexample. -/
theorem implication_not_preserved :
    restrictPredicate (lower ⇨ (⊥ : Subfunctor truthPresheaf)) ≠
      restrictPredicate lower ⇨ restrictPredicate (⊥ : Subfunctor truthPresheaf) := by
  rw [lower_negation_empty, restrict_lower_empty, bot_himp]
  intro same
  have admitted : PUnit.unit ∈
      (⊤ : Subfunctor ((theoryInverseImage topMap).obj truthPresheaf)).obj (op false) :=
    Set.mem_univ _
  rw [← same] at admitted
  exact admitted

def numbers : Boolᵒᵖ ⥤ Type := (Functor.const Boolᵒᵖ).obj Nat

def suppliedMap : numbers ⟶ (inverseImage topFunctor).obj numbers where
  app _ := show Nat ⟶ Nat from ↾fun (value : Nat) => value + 7

/-- Universal left elimination retains the supplied independently authored
function's exact value, rather than only its inhabitation. -/
theorem kan_retains_supplied_value :
    (((leftAdjunction topFunctor).unit.app numbers ≫
      (inverseImage topFunctor).map
        ((leftHomEquiv topFunctor numbers numbers).symm suppliedMap)).app (op false))
      (5 : Nat) = (12 : Nat) := by
  rw [left_extension_readout]
  rfl

theorem kan_uniqueness (extension : (leftKan topFunctor).obj numbers ⟶ numbers)
    (readout : (leftAdjunction topFunctor).unit.app numbers ≫
      (inverseImage topFunctor).map extension = suppliedMap) :
    extension = (leftHomEquiv topFunctor numbers numbers).symm suppliedMap :=
  left_extension_unique topFunctor suppliedMap extension readout

def suppliedRightMap : (inverseImage topFunctor).obj numbers ⟶ numbers where
  app _ := show Nat ⟶ Nat from ↾fun (value : Nat) => value + 9

theorem right_kan_retains_supplied_value :
    (((inverseImage topFunctor).map (rightHomEquiv topFunctor numbers numbers suppliedRightMap) ≫
      (rightAdjunction topFunctor).counit.app numbers).app (op false))
      (5 : Nat) = (14 : Nat) := by
  rw [right_extension_readout]
  rfl

theorem inverseImage_still_preservesPushouts :
    PreservesColimitsOfShape WalkingSpan (theoryInverseImage topMap : (Boolᵒᵖ ⥤ Type) ⥤ _) :=
  inferInstance

end Reversal

end Mettapedia.GSLT.Topos.PresheafTheoryActionControls
