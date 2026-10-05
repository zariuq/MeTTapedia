import Mettapedia.TypeTheory.WiderContextualWAlgebras

/-!
# Comparison with the original small-result W algebra model

The complete branch tables have explicit inverses, preserving every arrow
and position. Evaluation induction compares the separately constructed
folds on the same actual contextual trees.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.WiderContextualWComparison

open CategoryTheory MaterialSets.Hypersets

universe u
variable {D : Type u} [Category.{u} D]
variable (shape : D ⥤ Type u) (position : shape.Elements ⥤ Type u)
variable {target : D ⥤ Type u}

def branchesForward {X : D} {label : shape.obj X}
    (branches : ContextualWTypes.Branches shape position target label) :
    WiderContextualWAlgebras.Branches shape position target label where
  app := branches.app
  naturality := branches.naturality

def branchesBackward {X : D} {label : shape.obj X}
    (branches : WiderContextualWAlgebras.Branches shape position target label) :
    ContextualWTypes.Branches shape position target label where
  app := branches.app
  naturality := branches.naturality

def branchesEquiv {X : D} (label : shape.obj X) :
    ContextualWTypes.Branches shape position target label ≃
      WiderContextualWAlgebras.Branches shape position target label where
  toFun := branchesForward shape position
  invFun := branchesBackward shape position
  left_inv _branches := ContextualWTypes.Branches.ext fun _ _ _ => rfl
  right_inv _branches := WiderContextualWAlgebras.Branches.ext fun _ _ _ => rfl

theorem backward_restrict {X Y : D} {label : shape.obj X}
    (branches : WiderContextualWAlgebras.Branches shape position target label) (arrow : X ⟶ Y) :
    branchesBackward shape position (branches.restrict arrow) =
      (branchesBackward shape position branches).restrict arrow := by
  apply ContextualWTypes.Branches.ext
  intro future later branch
  rfl

def algebraForward (algebra : ContextualWTypes.Algebra shape position target) :
    WiderContextualWAlgebras.Algebra shape position target where
  make X label branches := algebra.make X label (branchesBackward shape position branches)
  naturality X Y arrow label branches :=
    (algebra.naturality X Y arrow label (branchesBackward shape position branches)).trans
      (congrArg (algebra.make Y (shape.map arrow label))
        (backward_restrict shape position branches arrow).symm)

theorem evaluationForward (algebra : ContextualWTypes.Algebra shape position target)
    {X : D} {tree : ContextualWTypes.RawTree shape position X} {value : target.obj X}
    (evaluation : ContextualWTypes.Evaluates shape position algebra tree value) :
    WiderContextualWAlgebras.Evaluates shape position (algebraForward shape position algebra) tree value := by
  induction evaluation with
  | sup label children branches values ih =>
    exact WiderContextualWAlgebras.Evaluates.sup label children
      (branchesForward shape position branches) ih

theorem fold_agrees (algebra : ContextualWTypes.Algebra shape position target)
    {X : D} (tree : ContextualWTypes.NaturalTree shape position X) :
    WiderContextualWAlgebras.fold shape position (algebraForward shape position algebra) tree =
      ContextualWTypes.fold shape position algebra tree :=
  WiderContextualWAlgebras.evaluates_unique shape position (algebraForward shape position algebra)
    (WiderContextualWAlgebras.fold_evaluates shape position (algebraForward shape position algebra) tree)
    (evaluationForward shape position algebra (ContextualWTypes.fold_evaluates shape position algebra tree))

theorem foldMap_agrees (algebra : ContextualWTypes.Algebra shape position target) :
    WiderContextualWAlgebras.foldMap shape position (algebraForward shape position algebra) =
      WiderPresheafDependentFunctions.Hom.ofNatTrans (ContextualWTypes.foldMap shape position algebra) := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point tree
  exact fold_agrees shape position algebra tree

theorem tree_constructor_agrees {X : D} (label : shape.obj X)
    (branches : ContextualWTypes.Branches shape position (ContextualWTypes.family shape position) label) :
    (WiderContextualWAlgebras.treeAlgebra shape position).make X label
      (branchesForward shape position branches) =
      (ContextualWTypes.treeAlgebra shape position).make X label branches := by
  apply Subtype.ext
  apply ContextualWTypes.RawTree.sup_eq_of_cast rfl
  intro future arrow branch
  rfl

end Mettapedia.TypeTheory.WiderContextualWComparison
