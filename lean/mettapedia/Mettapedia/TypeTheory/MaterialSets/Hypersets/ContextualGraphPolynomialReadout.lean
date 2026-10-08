import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadoutPairs
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyComparison

/-!
# Natural polynomial readouts with actual material branch bodies

The constructed contextual graph solves its labelled polynomial equation.
The independently attached branch family supplies the material collection,
while its literal receipt decoder keeps the complete native branch type.
Every comparison matches at all future contexts, not only the current fibre.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadout

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphPolynomialReadoutNodes ContextualGraphPolynomialReadoutPairs
universe u
variable {D : Type u} [Category.{u} D] {states : D ⥤ Type u}
variable (branches : states.Elements ⥤ Type u) (labels : NaturalHom states (values D))
variable (arguments : NaturalHom (total branches) (values D))
variable (successor : NaturalHom (total branches) states)

/-- The actual branch body records both the argument and its recursively
read successor. The successor reading is the constructed state graph. -/
def branchReading : NaturalHom (total branches) (values D) :=
  ContextualGraphOrderedPairs.orderedReading arguments
    (successor.comp (reading branches labels arguments successor))

def collectionReading : NaturalHom states (values D) :=
  ContextualGraphFamilyBodies.parent branches (branchReading branches labels arguments successor)

variable {point : D}

def collectionIntro (state : states.obj point) (branch : branches.obj ⟨point, state⟩)
    (element : Value D point)
    (same : Equal element ((branchReading branches labels arguments successor).app point ⟨state, branch⟩)) :
    Member element (value branches labels arguments successor (.collection state)) :=
  ⟨⟨.branch ⟨state, branch⟩, Edge.collect state branch⟩,
    same.trans (branchComparison branches labels arguments successor ⟨state, branch⟩).symm⟩

def collectionDecode {state : states.obj point} {element : Value D point}
    (proof : Member element (value branches labels arguments successor (.collection state))) :
    Σ branch : branches.obj ⟨point, state⟩,
      Equal element ((branchReading branches labels arguments successor).app point ⟨state, branch⟩) := by
  rcases proof with ⟨⟨node, available⟩, same⟩
  cases node with
  | branch receipt =>
    rcases receipt with ⟨other, branch⟩
    have eq : other = state := by cases available; rfl
    subst other
    exact ⟨branch, same.trans (branchComparison branches labels arguments successor ⟨state, branch⟩)⟩
  | state node => exact False.elim (by cases available)
  | collection node => exact False.elim (by cases available)
  | label node => exact False.elim (by cases available)
  | argument node => exact False.elim (by cases available)
  | pair left right => exact False.elim (by cases available)
  | left node => exact False.elim (by cases available)
  | right node => exact False.elim (by cases available)

def collectionToCarrier {state : states.obj point} {element : Value D point}
    (proof : Member element (value branches labels arguments successor (.collection state))) :
    Member element ((collectionReading branches labels arguments successor).app point state) :=
  let decoded := collectionDecode branches labels arguments successor proof
  ContextualGraphFamilyBodyComparison.memberIntro branches
    (branchReading branches labels arguments successor) ⟨point, state⟩ element decoded.1 decoded.2

def collectionFromCarrier {state : states.obj point} {element : Value D point}
    (proof : Member element ((collectionReading branches labels arguments successor).app point state)) :
    Member element (value branches labels arguments successor (.collection state)) :=
  let decoded := ContextualGraphFamilyBodyComparison.memberDecode branches
    (branchReading branches labels arguments successor) ⟨point, state⟩ element proof
  collectionIntro branches labels arguments successor state decoded.1 element decoded.2

/-- The collection node agrees with independently attached actual branch
bodies. The proof uses both complete future membership directions. -/
def collectionComparison (state : states.obj point) :
    Equal (value branches labels arguments successor (.collection state))
      ((collectionReading branches labels arguments successor).app point state) := by
  apply extensionality
  · intro future arrival element proof
    change Member element ((values D).map arrival
      ((collectionReading branches labels arguments successor).app point state))
    rw [(collectionReading branches labels arguments successor).naturality]
    exact collectionToCarrier branches labels arguments successor proof
  · intro future arrival element proof
    change Member element ((values D).map arrival
      ((collectionReading branches labels arguments successor).app point state)) at proof
    rw [(collectionReading branches labels arguments successor).naturality] at proof
    exact collectionFromCarrier branches labels arguments successor proof

/-- The actual graph, constructed without a supplied state denotation,
satisfies the labelled polynomial unfolding equation in the same universe. -/
def unfold (state : states.obj point) :
    Equal ((reading branches labels arguments successor).app point state)
      (ContextualGraphOrderedPairs.orderedPair (labels.app point state)
        ((collectionReading branches labels arguments successor).app point state)) :=
  (stateComparison branches labels arguments successor state).trans
    (ContextualGraphOrderedPairs.orderedPairCongr (Equal.refl _)
      (collectionComparison branches labels arguments successor state))

def reflectLabel {first second : states.obj point}
    (same : Equal ((reading branches labels arguments successor).app point first)
      ((reading branches labels arguments successor).app point second)) :
    Equal (labels.app point first) (labels.app point second) :=
  ContextualGraphOrderedPairs.orderedPairReflectFirst
    ((unfold branches labels arguments successor first).symm.trans
      (same.trans (unfold branches labels arguments successor second)))

def reflectCollection {first second : states.obj point}
    (same : Equal ((reading branches labels arguments successor).app point first)
      ((reading branches labels arguments successor).app point second)) :
    Equal ((collectionReading branches labels arguments successor).app point first)
      ((collectionReading branches labels arguments successor).app point second) :=
  ContextualGraphOrderedPairs.orderedPairReflectSecond
    ((unfold branches labels arguments successor first).symm.trans
      (same.trans (unfold branches labels arguments successor second)))

/-- This is the exact root observation kernel. The collection component
still contains the recursively constructed successor values. -/
theorem kernel (first second : states.obj point) :
    Nonempty (Equal ((reading branches labels arguments successor).app point first)
      ((reading branches labels arguments successor).app point second)) ↔
      Nonempty (Equal (labels.app point first) (labels.app point second)) ∧
        Nonempty (Equal ((collectionReading branches labels arguments successor).app point first)
          ((collectionReading branches labels arguments successor).app point second)) := by
  constructor
  · rintro ⟨same⟩
    exact ⟨⟨reflectLabel branches labels arguments successor same⟩,
      ⟨reflectCollection branches labels arguments successor same⟩⟩
  · rintro ⟨⟨labelsSame⟩, ⟨branchesSame⟩⟩
    exact ⟨(unfold branches labels arguments successor first).trans
      ((ContextualGraphOrderedPairs.orderedPairCongr labelsSame branchesSame).trans
        (unfold branches labels arguments successor second).symm)⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphPolynomialReadout
