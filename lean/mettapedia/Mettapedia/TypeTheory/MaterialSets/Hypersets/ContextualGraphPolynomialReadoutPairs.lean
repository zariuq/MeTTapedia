import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadoutComponents
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphOrderedPairs

/-!
# Ordered observations of actual polynomial graph states and branches

The internal graph pairing retains both component receipts. Its material
value agrees with the independently constructed contextual Kuratowski
pair. State and branch equations consequently preserve their actual
label or argument body and the corresponding successor collection.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadoutPairs

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphPolynomialReadoutNodes ContextualGraphPolynomialReadoutComponents
universe u
variable {D : Type u} [Category.{u} D] {states : D ⥤ Type u}
variable (branches : states.Elements ⥤ Type u) (labels : NaturalHom states (values D))
variable (arguments : NaturalHom (total branches) (values D))
variable (successor : NaturalHom (total branches) states)

variable {point : D}

def pairFirst (left right : Node branches labels arguments point) :
    Member (value branches labels arguments successor left) (value branches labels arguments successor (.pair left right)) :=
  ⟨⟨.left left, Edge.pairFirst left right⟩, leftComparison branches labels arguments successor point left⟩

def pairSecond (left right : Node branches labels arguments point) :
    Member (value branches labels arguments successor right) (value branches labels arguments successor (.pair left right)) :=
  ⟨⟨.right right, Edge.pairSecond left right⟩, rightComparison branches labels arguments successor point right⟩

def pairEliminate {left right : Node branches labels arguments point} {element : Value D point}
    (proof : Member element (value branches labels arguments successor (.pair left right))) :
    Equal element (value branches labels arguments successor left) ⊕ Equal element (value branches labels arguments successor right) := by
  rcases proof with ⟨⟨node, available⟩, same⟩
  cases node with
  | left node =>
    have eq : node = left := by cases available; rfl
    subst node
    exact .inl (same.trans (leftComparison branches labels arguments successor point left).symm)
  | right node =>
    have eq : node = right := by cases available; rfl
    subst node
    exact .inr (same.trans (rightComparison branches labels arguments successor point right).symm)
  | state node => exact False.elim (by cases available)
  | collection node => exact False.elim (by cases available)
  | branch node => exact False.elim (by cases available)
  | label node => exact False.elim (by cases available)
  | argument node => exact False.elim (by cases available)
  | pair left right => exact False.elim (by cases available)

def pairToExternal {left right : Node branches labels arguments point} {element : Value D point}
    (proof : Member element (value branches labels arguments successor (.pair left right))) :
    Member element (ContextualGraphOrderedPairs.pair
      (value branches labels arguments successor left) (value branches labels arguments successor right)) :=
  match pairEliminate branches labels arguments successor proof with
  | .inl same => Member.transportChild same.symm (ContextualGraphOrderedPairs.pairFirst _ _)
  | .inr same => Member.transportChild same.symm (ContextualGraphOrderedPairs.pairSecond _ _)

def pairFromExternal {left right : Node branches labels arguments point} {element : Value D point}
    (proof : Member element (ContextualGraphOrderedPairs.pair
      (value branches labels arguments successor left) (value branches labels arguments successor right))) :
    Member element (value branches labels arguments successor (.pair left right)) :=
  match ContextualGraphOrderedPairs.pairEliminate proof with
  | .inl same => Member.transportChild same.symm (pairFirst branches labels arguments successor left right)
  | .inr same => Member.transportChild same.symm (pairSecond branches labels arguments successor left right)

def pairComparison (left right : Node branches labels arguments point) :
    Equal (value branches labels arguments successor (.pair left right))
      (ContextualGraphOrderedPairs.pair (value branches labels arguments successor left)
        (value branches labels arguments successor right)) :=
  extensionality
    (fun _ _ _ proof => pairToExternal branches labels arguments successor proof)
    (fun _ _ _ proof => pairFromExternal branches labels arguments successor proof)

def stateUnfold (state : states.obj point) : Node branches labels arguments point :=
  .pair (.pair (labelRoot branches labels arguments point state) (labelRoot branches labels arguments point state)) (.pair (labelRoot branches labels arguments point state) (.collection state))

theorem stateUnfold_natural {first second : D} (arrival : first ⟶ second)
    (state : states.obj first) :
    advance branches labels arguments arrival (stateUnfold branches labels arguments state) =
      stateUnfold branches labels arguments (states.map arrival state) := by
  change Node.pair (.pair (advance branches labels arguments arrival (labelRoot branches labels arguments first state))
      (advance branches labels arguments arrival (labelRoot branches labels arguments first state)))
    (.pair (advance branches labels arguments arrival (labelRoot branches labels arguments first state))
      (.collection (states.map arrival state))) = _
  rw [labelRoot_natural]
  rfl

theorem stateEdges (state : states.obj point) (node : Node branches labels arguments point) :
    Edge branches labels arguments successor point (.state state) node ↔
      Edge branches labels arguments successor point (stateUnfold branches labels arguments state) node := by
  constructor
  · intro proof
    cases proof with
    | stateFirst _ => exact Edge.pairFirst _ _
    | stateSecond _ => exact Edge.pairSecond _ _
  · intro proof
    cases proof with
    | pairFirst _ _ => exact Edge.stateFirst _
    | pairSecond _ _ => exact Edge.stateSecond _

def stateToUnfold {element : Value D point} {state : states.obj point}
    (proof : Member element (value branches labels arguments successor (.state state))) :
    Member element (value branches labels arguments successor (stateUnfold branches labels arguments state)) :=
  ⟨⟨proof.1.val, (stateEdges branches labels arguments successor state proof.1.val).mp proof.1.property⟩, proof.2⟩

def stateFromUnfold {element : Value D point} {state : states.obj point}
    (proof : Member element (value branches labels arguments successor (stateUnfold branches labels arguments state))) :
    Member element (value branches labels arguments successor (.state state)) :=
  ⟨⟨proof.1.val, (stateEdges branches labels arguments successor state proof.1.val).mpr proof.1.property⟩, proof.2⟩

def stateInternalComparison (state : states.obj point) :
    Equal (value branches labels arguments successor (.state state))
      (value branches labels arguments successor (stateUnfold branches labels arguments state)) := by
  apply extensionality
  · intro second arrival element proof
    change Member element (value branches labels arguments successor
      (advance branches labels arguments arrival (stateUnfold branches labels arguments state)))
    rw [stateUnfold_natural]
    exact stateToUnfold branches labels arguments successor proof
  · intro second arrival element proof
    change Member element (value branches labels arguments successor
      (advance branches labels arguments arrival (stateUnfold branches labels arguments state))) at proof
    rw [stateUnfold_natural] at proof
    exact stateFromUnfold branches labels arguments successor proof

def stateComparison (state : states.obj point) :
    Equal (value branches labels arguments successor (.state state))
      (ContextualGraphOrderedPairs.orderedPair (labels.app point state)
        (value branches labels arguments successor (.collection state))) :=
  (stateInternalComparison branches labels arguments successor state).trans
    ((pairComparison branches labels arguments successor _ _).trans
      ((ContextualGraphOrderedPairs.pairCongr (pairComparison branches labels arguments successor _ _)
        (pairComparison branches labels arguments successor _ _)).trans
        (ContextualGraphOrderedPairs.orderedPairCongr
          (labelComparison branches labels arguments successor point state).symm (Equal.refl _))))

def branchUnfold (receipt : (total branches).obj point) : Node branches labels arguments point :=
  .pair (.pair (argumentRoot branches labels arguments point receipt) (argumentRoot branches labels arguments point receipt)) (.pair (argumentRoot branches labels arguments point receipt) (.state (successor.app point receipt)))

theorem branchUnfold_natural {first second : D} (arrival : first ⟶ second)
    (receipt : (total branches).obj first) :
    advance branches labels arguments arrival (branchUnfold branches labels arguments successor receipt) =
      branchUnfold branches labels arguments successor ((total branches).map arrival receipt) := by
  change Node.pair (.pair (advance branches labels arguments arrival (argumentRoot branches labels arguments first receipt))
      (advance branches labels arguments arrival (argumentRoot branches labels arguments first receipt)))
    (.pair (advance branches labels arguments arrival (argumentRoot branches labels arguments first receipt))
      (.state (states.map arrival (successor.app first receipt)))) = _
  rw [argumentRoot_natural, successor.naturality]
  rfl

theorem branchEdges (receipt : (total branches).obj point) (node : Node branches labels arguments point) :
    Edge branches labels arguments successor point (.branch receipt) node ↔
      Edge branches labels arguments successor point (branchUnfold branches labels arguments successor receipt) node := by
  constructor
  · intro proof
    cases proof with
    | branchFirst _ => exact Edge.pairFirst _ _
    | branchSecond _ => exact Edge.pairSecond _ _
  · intro proof
    cases proof with
    | pairFirst _ _ => exact Edge.branchFirst _
    | pairSecond _ _ => exact Edge.branchSecond _

def branchToUnfold {element : Value D point} {receipt : (total branches).obj point}
    (proof : Member element (value branches labels arguments successor (.branch receipt))) :
    Member element (value branches labels arguments successor (branchUnfold branches labels arguments successor receipt)) :=
  ⟨⟨proof.1.val, (branchEdges branches labels arguments successor receipt proof.1.val).mp proof.1.property⟩, proof.2⟩

def branchFromUnfold {element : Value D point} {receipt : (total branches).obj point}
    (proof : Member element (value branches labels arguments successor (branchUnfold branches labels arguments successor receipt))) :
    Member element (value branches labels arguments successor (.branch receipt)) :=
  ⟨⟨proof.1.val, (branchEdges branches labels arguments successor receipt proof.1.val).mpr proof.1.property⟩, proof.2⟩

def branchInternalComparison (receipt : (total branches).obj point) :
    Equal (value branches labels arguments successor (.branch receipt))
      (value branches labels arguments successor (branchUnfold branches labels arguments successor receipt)) := by
  apply extensionality
  · intro second arrival element proof
    change Member element (value branches labels arguments successor
      (advance branches labels arguments arrival (branchUnfold branches labels arguments successor receipt)))
    rw [branchUnfold_natural]
    exact branchToUnfold branches labels arguments successor proof
  · intro second arrival element proof
    change Member element (value branches labels arguments successor
      (advance branches labels arguments arrival (branchUnfold branches labels arguments successor receipt))) at proof
    rw [branchUnfold_natural] at proof
    exact branchFromUnfold branches labels arguments successor proof

def branchComparison (receipt : (total branches).obj point) :
    Equal (value branches labels arguments successor (.branch receipt))
      (ContextualGraphOrderedPairs.orderedPair (arguments.app point receipt)
        (value branches labels arguments successor (.state (successor.app point receipt)))) :=
  (branchInternalComparison branches labels arguments successor receipt).trans
    ((pairComparison branches labels arguments successor _ _).trans
      ((ContextualGraphOrderedPairs.pairCongr (pairComparison branches labels arguments successor _ _)
        (pairComparison branches labels arguments successor _ _)).trans
        (ContextualGraphOrderedPairs.orderedPairCongr
          (argumentComparison branches labels arguments successor point receipt).symm (Equal.refl _))))

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadoutPairs
