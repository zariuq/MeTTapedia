import Mettapedia.GSLT.Topos.PresheafElementaryToposAction
import Mettapedia.GSLT.Topos.PresheafTheoryActionControls

/-!
# Geometric presheaf action and its observation boundaries

Two independently supplied arrows between indexing worlds produce
different ordinary comparison cells between actual geometric evaluations.
Their varying input contains dependent positions; the comparisons retain
the chosen value while losing those positions. A source theory with
different object and arrow universe sizes supplies a nonconstant
representable readout through the complete new action. The constructed
classifier distinguishes a proper predicate from truth, while a qualified
theory map still fails to preserve predicate implication.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Topos.PresheafElementaryToposControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open Mettapedia.CategoryTheory Mettapedia.GSLT.Core
open PresheafElementaryTopos PresheafTheoryAction PresheafTheoryPseudofunctor

namespace Parallel

abbrev Point := Discrete PUnit
abbrev Receipt := (n : Nat) × Fin (n + 2)

def leftReadout : Receipt ⟶ Nat := TypeCat.ofHom fun receipt => receipt.1 + 7
def rightReadout : Receipt ⟶ Nat := TypeCat.ofHom fun receipt => receipt.1 + 9

def display : WalkingParallelPairᵒᵖ ⥤ Type :=
  walkingParallelPairOpEquiv.inverse ⋙ parallelPair leftReadout rightReadout

def atZero : Point ⥤ WalkingParallelPair := (Functor.const Point).obj .zero
def atOne : Point ⥤ WalkingParallelPair := (Functor.const Point).obj .one

def leftArrow : atZero ⟶ atOne where
  app _ := WalkingParallelPairHom.left
  naturality := by
    intros
    change 𝟙 WalkingParallelPair.zero ≫ WalkingParallelPairHom.left =
      WalkingParallelPairHom.left ≫ 𝟙 WalkingParallelPair.one
    rw [Category.id_comp, Category.comp_id]

def rightArrow : atZero ⟶ atOne where
  app _ := WalkingParallelPairHom.right
  naturality := by
    intros
    change 𝟙 WalkingParallelPair.zero ≫ WalkingParallelPairHom.right =
      WalkingParallelPairHom.right ≫ 𝟙 WalkingParallelPair.one
    rw [Category.id_comp, Category.comp_id]

def zeroEvaluation : ElementaryTopos.GeometricHom
    (object.{0,0,0} WalkingParallelPair) (object.{0,0,0} Point) := inverseImageMap atZero

def oneEvaluation : ElementaryTopos.GeometricHom
    (object.{0,0,0} WalkingParallelPair) (object.{0,0,0} Point) := inverseImageMap atOne

def nativeLeft : oneEvaluation ⟶ zeroEvaluation := cell leftArrow
def nativeRight : oneEvaluation ⟶ zeroEvaluation := cell rightArrow

def advance (receipt : Receipt) : Receipt :=
  ⟨receipt.1 + 1, receipt.2.castSucc⟩

def advancePair : parallelPair leftReadout rightReadout ⟶
    parallelPair leftReadout rightReadout :=
  parallelPairHomMk (TypeCat.ofHom advance) (TypeCat.ofHom fun n : Nat => n + 1)
    (by ext receipt; change receipt.1 + 7 + 1 = (receipt.1 + 1) + 7; omega)
    (by ext receipt; change receipt.1 + 9 + 1 = (receipt.1 + 1) + 9; omega)

def advanceDisplay : display ⟶ display :=
  Functor.whiskerLeft walkingParallelPairOpEquiv.inverse advancePair

theorem actual_evaluation_advance_value (receipt : Receipt) :
    ((oneEvaluation.functor.map advanceDisplay).app (op ⟨PUnit.unit⟩) receipt).1 =
      receipt.1 + 1 := rfl

theorem actual_evaluation_retains_position (receipt : Receipt) :
    ((oneEvaluation.functor.map advanceDisplay).app (op ⟨PUnit.unit⟩) receipt).2.val =
      receipt.2.val := rfl

theorem actual_left_cell_readout (receipt : Receipt) :
    (nativeLeft.app display).app (op ⟨PUnit.unit⟩) receipt = receipt.1 + 7 := rfl

theorem actual_right_cell_readout (receipt : Receipt) :
    (nativeRight.app display).app (op ⟨PUnit.unit⟩) receipt = receipt.1 + 9 := rfl

theorem actual_cell_after_advance (receipt : Receipt) :
    (nativeLeft.app display).app (op ⟨PUnit.unit⟩)
      ((oneEvaluation.functor.map advanceDisplay).app (op ⟨PUnit.unit⟩) receipt) =
        receipt.1 + 1 + 7 := rfl

def firstReceipt : Receipt := ⟨1, ⟨0, by decide⟩⟩
def secondReceipt : Receipt := ⟨1, ⟨1, by decide⟩⟩

theorem positions_differ : firstReceipt ≠ secondReceipt := by
  intro same
  have positions := congrArg (fun receipt : Receipt => receipt.2.val) same
  change (0 : Nat) = 1 at positions
  omega

theorem complete_cells_differ : nativeLeft ≠ nativeRight := by
  intro same
  have values := congrArg (fun change => change.app display |>.app
    (op ⟨PUnit.unit⟩) firstReceipt) same
  change (1 : Nat) + 7 = 1 + 9 at values
  omega

theorem cells_do_not_recover_positions :
    ¬ ∃ decode : Nat → Receipt, ∀ receipt,
      decode ((nativeLeft.app display).app (op ⟨PUnit.unit⟩) receipt) = receipt := by
  rintro ⟨decode, recovers⟩
  apply positions_differ
  exact (recovers firstReceipt).symm.trans (recovers secondReceipt)

/-- The noninvertibility is established at an actual component of the
new geometric comparison, with two retained input positions. -/
theorem actual_left_cell_not_iso : ¬ IsIso nativeLeft := by
  intro invertible
  let : IsIso nativeLeft := invertible
  apply cells_do_not_recover_positions
  refine ⟨(inv nativeLeft).app display |>.app (op ⟨PUnit.unit⟩), ?_⟩
  intro receipt
  exact congrArg (fun change : oneEvaluation ⟶ oneEvaluation =>
    change.app display |>.app (op ⟨PUnit.unit⟩) receipt) (IsIso.hom_inv_id nativeLeft)

end Parallel

namespace IndependentSizes

open Mettapedia.GSLT.Core.LambdaTheoryClosedControls
open PresheafTheoryActionControls.Exchange

/-- The indexing theory's objects live in Type 1 and its arrows in Type 0;
its full representable values are raised into the common Type 1 carrier. -/
def represented : Diagramsᵒᵖ ⥤ Type 1 :=
  PresheafTheoryActionControls.Exchange.represented ⋙ uliftFunctor.{1,0}

def nativeSwap := (PresheafElementaryTopos.action :
  Pseudofunctor Theories.{1,0} ElementaryTopos.{2,1}).map (route swapMap)

theorem actual_action_shift_readout :
    ((((nativeSwap.functor.obj represented).map shift.op) (ULift.up supplied)).down.app
      ⟨false⟩ (10 : Nat)) = (12 : Nat) := rfl

theorem omitting_action_changes_readout :
    ((((nativeSwap.functor.obj represented).map shift.op) (ULift.up supplied)).down.app
        ⟨false⟩ (10 : Nat)) ≠
      ((represented.map shift.op (ULift.up supplied)).down.app ⟨false⟩ (10 : Nat)) := by
  change (12 : Nat) ≠ 11
  omega

theorem empty_fibre_unique (first second : represented.obj (op emptyDiagram)) :
    first = second := by
  apply ULift.ext
  exact PresheafTheoryActionControls.Exchange.empty_fibre_unique first.down second.down

theorem actual_composition_recovers_readout :
    (((((nativeSwap ≫ nativeSwap).functor.obj represented).map shift.op)
      (ULift.up supplied)).down.app ⟨false⟩ (10 : Nat)) = (11 : Nat) := rfl

end IndependentSizes

namespace LogicalBoundary

open PresheafTheoryActionControls.Reversal

def properName := (classifier Bool).χ lower.ι
def truthName := (classifier Bool).χ (⊤ : Subfunctor truthPresheaf).ι

/-- The classifier constructed through the independent small-category
presentation distinguishes the actual proper predicate from truth. -/
theorem proper_name_differs : properName ≠ truthName := by
  intro same
  have subobjects : Subobject.mk lower.ι =
      Subobject.mk (⊤ : Subfunctor truthPresheaf).ι := by
    simpa only [properName, truthName, Subobject.Classifier.pullback_χ_obj_mk_truth]
      using congrArg (fun name => (Subobject.pullback name).obj
        (classifier Bool).truth_as_subobject) same
  have equal : lower = (⊤ : Subfunctor truthPresheaf) :=
    (Subfunctor.orderIsoSubobject truthPresheaf).injective subobjects
  have admitted : PUnit.unit ∈ lower.obj (op true) := by
    rw [equal]
    exact Set.mem_univ (PUnit.unit : truthPresheaf.obj (op true))
  exact Bool.noConfusion admitted

def nativeTop := (PresheafElementaryTopos.action :
  Pseudofunctor Theories.{0,0} ElementaryTopos.{1,0}).map (route topMap)

def restrictedPredicate (predicate : Subfunctor truthPresheaf) :
    Subfunctor (nativeTop.functor.obj truthPresheaf) where
  obj world := predicate.obj (topMap.functor.op.obj world)
  map arrow := predicate.map (topMap.functor.op.map arrow)

local instance restricted_frame : Order.Frame
    (Subfunctor (nativeTop.functor.obj truthPresheaf)) :=
  inferInstanceAs (Order.Frame (Subfunctor ((inverseImage topMap.functor).obj truthPresheaf)))

theorem geometric_does_not_preserve_implication :
    restrictedPredicate (lower ⇨ (⊥ : Subfunctor truthPresheaf)) ≠
      restrictedPredicate lower ⇨ restrictedPredicate (⊥ : Subfunctor truthPresheaf) :=
  implication_not_preserved

def nativeGrow := (PresheafElementaryTopos.action :
  Pseudofunctor Theories.{0,0} ElementaryTopos.{1,0}).map₂
    (change (F := LambdaTheoryMap.id theory) (G := topMap) grow)

theorem actual_theory_cell_readout (value : Nat) :
    (nativeGrow.app numbers).app (op false) value = value := rfl

theorem no_wrong_cell_direction :
    ¬ Nonempty ((inverseImage (Functor.id Bool)).obj representedFalse ⟶
      nativeTop.functor.obj representedFalse) := no_unreversed_cell

theorem actual_theory_cell_not_iso : ¬ IsIso nativeGrow := by
  intro invertible
  let : IsIso nativeGrow := invertible
  apply no_wrong_cell_direction
  exact ⟨(inv nativeGrow).app representedFalse⟩

end LogicalBoundary

end Mettapedia.GSLT.Topos.PresheafElementaryToposControls
