import Mettapedia.TypeTheory.ContextualSiteWReindexing
import Mettapedia.TypeTheory.WiderContextualWAlgebras

/-!
# Full contextual W algebras and folds across successor sites

The two W carriers and their constructors are formed independently. The
comparison transports every compatible future branch, then proves the
constructor equation and equality of independently defined folds. Algebra
values may occupy an arbitrary universe; the original tree carrier remains
at its original bound and the raised tree carrier at its successor.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSiteWAlgebra

open CategoryTheory MaterialSets.Hypersets
open ContextualWTypes (RawTree NaturalTree Position)
open WiderContextualWAlgebras (Branches)
open ContextualSiteW (upperShape upperPosition)
open WiderPresheafDependentFunctions

universe u h
variable {D : Type u} [Category.{u} D]
variable (shape : D ⥤ Type u) (position : shape.Elements ⥤ Type u) (target : D ⥤ Type h)

abbrev upperTarget := PresheafSiteLift.compose (PresheafSiteLift.Site.downFunctor (D := D)) target

def lowerBranches (point : PresheafSiteLift.Site D) (label : (upperShape shape).obj point)
    (branches : Branches (upperShape shape) (upperPosition shape position) (upperTarget target) label) :
    Branches shape position target label.down where
  app next arrow branch := branches.app (ULift.up next) (ULift.up arrow) (ULift.up branch)
  naturality next last first later branch := by
    refine (branches.naturality (ULift.up next) (ULift.up last)
      (ULift.up first) (ULift.up later) (ULift.up branch)).trans ?_
    exact branches.app_eq rfl _ _ (ContextualSiteW.position_along_up shape position label.down first later branch)

def raiseBranches (point : PresheafSiteLift.Site D) (label : (upperShape shape).obj point)
    (branches : Branches shape position target label.down) :
    Branches (upperShape shape) (upperPosition shape position) (upperTarget target) label where
  app next arrow branch := branches.app next.down arrow.down branch.down
  naturality next last first later branch := by
    refine (branches.naturality next.down last.down first.down later.down branch.down).trans ?_
    apply branches.app_eq rfl
    exact heq_of_eq (congrArg ULift.down (eq_of_heq
      (ContextualSiteW.position_along_up shape position label.down first.down later.down branch.down))).symm

theorem lower_raise_branches (point : PresheafSiteLift.Site D) (label : (upperShape shape).obj point)
    (branches : Branches shape position target label.down) :
    lowerBranches shape position target point label (raiseBranches shape position target point label branches) = branches := by
  apply Branches.ext
  intro _ _ _
  rfl

theorem raise_lower_branches (point : PresheafSiteLift.Site D) (label : (upperShape shape).obj point)
    (branches : Branches (upperShape shape) (upperPosition shape position) (upperTarget target) label) :
    raiseBranches shape position target point label (lowerBranches shape position target point label branches) = branches := by
  apply Branches.ext
  intro _ _ _
  rfl

def branchEquiv (point : PresheafSiteLift.Site D) (label : (upperShape shape).obj point) :
    Branches (upperShape shape) (upperPosition shape position) (upperTarget target) label ≃
      Branches shape position target label.down where
  toFun := lowerBranches shape position target point label
  invFun := raiseBranches shape position target point label
  left_inv := raise_lower_branches shape position target point label
  right_inv := lower_raise_branches shape position target point label

theorem lower_branches_restrict {first second : PresheafSiteLift.Site D} (arrow : first ⟶ second)
    (label : (upperShape shape).obj first)
    (branches : Branches (upperShape shape) (upperPosition shape position) (upperTarget target) label) :
    lowerBranches shape position target second ((upperShape shape).map arrow label) (branches.restrict arrow) =
      (lowerBranches shape position target first label branches).restrict arrow.down := by
  apply Branches.ext
  intro next later branch
  exact branches.app_eq rfl _ _ (ContextualSiteW.composite_position_up shape position label.down arrow.down later branch)

def algebra (original : WiderContextualWAlgebras.Algebra shape position target) :
    WiderContextualWAlgebras.Algebra (upperShape shape) (upperPosition shape position) (upperTarget target) where
  make point label branches := original.make point.down label.down (lowerBranches shape position target point label branches)
  naturality first second arrow label branches :=
    (original.naturality first.down second.down arrow.down label.down
      (lowerBranches shape position target first label branches)).trans
      (congrArg (original.make second.down (shape.map arrow.down label.down))
        (lower_branches_restrict shape position target arrow label branches).symm)

theorem raise_evaluates_data (original : WiderContextualWAlgebras.Algebra shape position target)
    {X : D} {tree : RawTree shape position X} {value : target.obj X}
    (evaluation : WiderContextualWAlgebras.Evaluates shape position original tree value) :
    ∀ (point : PresheafSiteLift.Site D) (same : point.down = X),
      WiderContextualWAlgebras.Evaluates (upperShape shape) (upperPosition shape position)
        (algebra shape position target original) (ContextualSiteW.raiseRawData shape position tree point same)
        (cast (congrArg target.obj same.symm) value) := by
  induction evaluation with
  | @sup X label children branches values earlier =>
    intro point same
    cases same
    have smaller : ∀ next arrow branch,
        WiderContextualWAlgebras.Evaluates (upperShape shape) (upperPosition shape position)
          (algebra shape position target original)
          (ContextualSiteW.raiseRaw shape position next (children next.down arrow.down branch.down))
          ((raiseBranches shape position target point (ULift.up label) branches).app next arrow branch) := by
      intro next arrow branch
      exact earlier _ _ _ next rfl
    have constructed := WiderContextualWAlgebras.Evaluates.sup
      (algebra := algebra shape position target original) (ULift.up label) _
      (raiseBranches shape position target point (ULift.up label) branches) smaller
    have computes : (algebra shape position target original).make point (ULift.up label)
        (raiseBranches shape position target point (ULift.up label) branches) = original.make point.down label branches :=
      congrArg (original.make point.down label) (lower_raise_branches shape position target point (ULift.up label) branches)
    exact computes ▸ constructed

theorem fold_raise (original : WiderContextualWAlgebras.Algebra shape position target)
    (point : PresheafSiteLift.Site D) (tree : NaturalTree shape position point.down) :
    WiderContextualWAlgebras.fold (upperShape shape) (upperPosition shape position)
      (algebra shape position target original) (ContextualSiteW.raiseNatural shape position point tree) =
      WiderContextualWAlgebras.fold shape position original tree :=
  WiderContextualWAlgebras.evaluates_unique _ _ _ (WiderContextualWAlgebras.fold_evaluates _ _ _ _)
    (raise_evaluates_data shape position target original
      (WiderContextualWAlgebras.fold_evaluates shape position original tree) point rfl)

theorem fold_lower (original : WiderContextualWAlgebras.Algebra shape position target)
    {point : PresheafSiteLift.Site D}
    (tree : NaturalTree (upperShape shape) (upperPosition shape position) point) :
    WiderContextualWAlgebras.fold (upperShape shape) (upperPosition shape position)
      (algebra shape position target original) tree =
      WiderContextualWAlgebras.fold shape position original (ContextualSiteW.lowerNatural shape position tree) := by
  have same : ContextualSiteW.raiseNatural shape position point
      (ContextualSiteW.lowerNatural shape position tree) = tree :=
    (ContextualSiteW.naturalEquiv shape position point).symm_apply_apply tree
  exact (congrArg (WiderContextualWAlgebras.fold (upperShape shape) (upperPosition shape position)
    (algebra shape position target original)) same).symm.trans
      (fold_raise shape position target original point (ContextualSiteW.lowerNatural shape position tree))

noncomputable def lowerTrees : Hom
    (ContextualWTypes.family (upperShape shape) (upperPosition shape position))
    (upperTarget (ContextualWTypes.family shape position)) where
  app _ := ContextualSiteW.lowerNatural shape position
  naturality arrow tree := Subtype.ext (ContextualSiteW.lower_restrict shape position arrow tree.val).symm

noncomputable def raiseTrees : Hom
    (upperTarget (ContextualWTypes.family shape position))
    (ContextualWTypes.family (upperShape shape) (upperPosition shape position)) where
  app := ContextualSiteW.raiseNatural shape position
  naturality arrow tree := Subtype.ext (ContextualSiteW.raise_restrict shape position arrow tree.val).symm

noncomputable def treeBranches (point : PresheafSiteLift.Site D) (label : (upperShape shape).obj point)
    (branches : Branches shape position (ContextualWTypes.family shape position) label.down) :
    Branches (upperShape shape) (upperPosition shape position)
      (ContextualWTypes.family (upperShape shape) (upperPosition shape position)) label :=
  (raiseBranches shape position (ContextualWTypes.family shape position) point label branches).map
    (raiseTrees shape position)

theorem constructor_raise (point : PresheafSiteLift.Site D) (label : (upperShape shape).obj point)
    (branches : Branches shape position (ContextualWTypes.family shape position) label.down) :
    ContextualSiteW.raiseNatural shape position point
      ((WiderContextualWAlgebras.treeAlgebra shape position).make point.down label.down branches) =
      (WiderContextualWAlgebras.treeAlgebra (upperShape shape) (upperPosition shape position)).make point label
        (treeBranches shape position point label branches) := Subtype.ext rfl

def retainedHom {source : D ⥤ Type u} (operation : Hom source target) :
    Hom (upperTarget source) (upperTarget target) where
  app point := operation.app point.down
  naturality step := operation.naturality step.down

theorem fold_comparison (original : WiderContextualWAlgebras.Algebra shape position target) :
    WiderContextualWAlgebras.foldMap (upperShape shape) (upperPosition shape position)
        (algebra shape position target original) =
      (lowerTrees shape position).comp (retainedHom target (WiderContextualWAlgebras.foldMap shape position original)) := by
  apply Hom.ext
  intro point tree
  exact fold_lower shape position target original tree

end Mettapedia.TypeTheory.ContextualSiteWAlgebra
