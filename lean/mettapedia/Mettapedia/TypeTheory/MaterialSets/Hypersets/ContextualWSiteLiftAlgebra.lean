import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWSiteLift

/-!
# Constructor and arbitrary algebra computation across successor sites

Full compatible future branches are transported in both directions.
The resulting algebra on the raised site is natural, and its constructed
fold agrees with the lower fold. This covers arbitrary natural targets
and all future branches, rather than a selected tree or pointwise recursion.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWSiteLiftAlgebra

open CategoryTheory
open Mettapedia.TypeTheory
open ContextualWTypes (Branches RawTree NaturalTree Position)
open ContextualWSiteLift (upperShape upperPosition)

universe u
variable {C : Type u} [Category.{u} C]
variable (P : Cᵒᵖ ⥤ Type u) (shape : P.Elements ⥤ Type u) (position : shape.Elements ⥤ Type u)
variable (target : P.Elements ⥤ Type u)

def lowerBranches (point : (PresheafSiteLift.base P).Elements) (label : (upperShape P shape).obj point)
    (branches : Branches (upperShape P shape) (upperPosition P shape position) (PresheafSiteLift.family P target) label) :
    Branches shape position target label.down where
  app next arrow branch := (branches.app ((PresheafSiteLift.elementsUp P).obj next)
    ((PresheafSiteLift.elementsUp P).map arrow) (ULift.up branch)).down
  naturality next last first later branch := by
    refine (congrArg ULift.down (branches.naturality
      ((PresheafSiteLift.elementsUp P).obj next) ((PresheafSiteLift.elementsUp P).obj last)
      ((PresheafSiteLift.elementsUp P).map first) ((PresheafSiteLift.elementsUp P).map later) (ULift.up branch))).trans ?_
    exact congrArg ULift.down (branches.app_eq rfl _ _
      (ContextualWSiteLift.position_along_up P shape position label.down first later branch))

def raiseBranches (point : (PresheafSiteLift.base P).Elements) (label : (upperShape P shape).obj point)
    (branches : Branches shape position target label.down) :
    Branches (upperShape P shape) (upperPosition P shape position) (PresheafSiteLift.family P target) label where
  app next arrow branch := ULift.up (branches.app ((PresheafSiteLift.elementsDown P).obj next)
    ((PresheafSiteLift.elementsDown P).map arrow) branch.down)
  naturality next last first later branch := by
    refine (congrArg ULift.up (branches.naturality
      ((PresheafSiteLift.elementsDown P).obj next) ((PresheafSiteLift.elementsDown P).obj last)
      ((PresheafSiteLift.elementsDown P).map first) ((PresheafSiteLift.elementsDown P).map later) branch.down)).trans ?_
    apply congrArg ULift.up
    apply branches.app_eq rfl
    exact heq_of_eq (congrArg ULift.down (eq_of_heq
      (ContextualWSiteLift.position_along_up P shape position label.down
        ((PresheafSiteLift.elementsDown P).map first) ((PresheafSiteLift.elementsDown P).map later) branch.down))).symm

theorem lower_raise_branches (point : (PresheafSiteLift.base P).Elements) (label : (upperShape P shape).obj point)
    (branches : Branches shape position target label.down) :
    lowerBranches P shape position target point label (raiseBranches P shape position target point label branches) = branches := by
  apply Branches.ext
  intro _ _ _
  rfl

theorem raise_lower_branches (point : (PresheafSiteLift.base P).Elements) (label : (upperShape P shape).obj point)
    (branches : Branches (upperShape P shape) (upperPosition P shape position) (PresheafSiteLift.family P target) label) :
    raiseBranches P shape position target point label (lowerBranches P shape position target point label branches) = branches := by
  apply Branches.ext
  intro _ _ _
  rfl

def branchEquiv (point : (PresheafSiteLift.base P).Elements) (label : (upperShape P shape).obj point) :
    Branches (upperShape P shape) (upperPosition P shape position) (PresheafSiteLift.family P target) label ≃
      Branches shape position target label.down where
  toFun := lowerBranches P shape position target point label
  invFun := raiseBranches P shape position target point label
  left_inv := raise_lower_branches P shape position target point label
  right_inv := lower_raise_branches P shape position target point label

theorem lower_branches_restrict {first second : (PresheafSiteLift.base P).Elements} (arrow : first ⟶ second)
    (label : (upperShape P shape).obj first)
    (branches : Branches (upperShape P shape) (upperPosition P shape position) (PresheafSiteLift.family P target) label) :
    lowerBranches P shape position target second ((upperShape P shape).map arrow label) (branches.restrict arrow) =
      (lowerBranches P shape position target first label branches).restrict ((PresheafSiteLift.elementsDown P).map arrow) := by
  apply Branches.ext
  intro next later branch
  exact congrArg ULift.down (branches.app_eq rfl _ _
    (ContextualWSiteLift.composite_position_up P shape position label.down
      ((PresheafSiteLift.elementsDown P).map arrow) later branch))

def algebra (original : ContextualWTypes.Algebra shape position target) :
    ContextualWTypes.Algebra (upperShape P shape) (upperPosition P shape position) (PresheafSiteLift.family P target) where
  make point label branches := ULift.up (original.make ((PresheafSiteLift.elementsDown P).obj point) label.down
    (lowerBranches P shape position target point label branches))
  naturality first second arrow label branches := congrArg ULift.up
    ((original.naturality _ _ ((PresheafSiteLift.elementsDown P).map arrow) label.down
      (lowerBranches P shape position target first label branches)).trans
        (congrArg (original.make ((PresheafSiteLift.elementsDown P).obj second)
          (shape.map ((PresheafSiteLift.elementsDown P).map arrow) label.down))
          (lower_branches_restrict P shape position target arrow label branches).symm))

theorem raise_evaluates_data (original : ContextualWTypes.Algebra shape position target)
    {X : P.Elements} {tree : RawTree shape position X} {value : target.obj X}
    (evaluation : ContextualWTypes.Evaluates shape position original tree value) :
    ∀ (point : (PresheafSiteLift.base P).Elements) (same : (PresheafSiteLift.elementsDown P).obj point = X),
      ContextualWTypes.Evaluates (upperShape P shape) (upperPosition P shape position)
        (algebra P shape position target original) (ContextualWSiteLift.raiseRawData P shape position tree point same)
        (ULift.up (cast (congrArg target.obj same.symm) value)) := by
  induction evaluation with
  | @sup X label children branches values earlier =>
    intro point same
    cases same
    have smaller : ∀ next arrow branch,
        ContextualWTypes.Evaluates (upperShape P shape) (upperPosition P shape position)
          (algebra P shape position target original)
          (ContextualWSiteLift.raiseRaw P shape position next
            (children ((PresheafSiteLift.elementsDown P).obj next) ((PresheafSiteLift.elementsDown P).map arrow) branch.down))
          ((raiseBranches P shape position target point (ULift.up label) branches).app next arrow branch) := by
      intro next arrow branch
      exact earlier _ _ _ next rfl
    have constructed := ContextualWTypes.Evaluates.sup
      (algebra := algebra P shape position target original) (ULift.up label) _
      (raiseBranches P shape position target point (ULift.up label) branches) smaller
    have computes : (algebra P shape position target original).make point (ULift.up label)
        (raiseBranches P shape position target point (ULift.up label) branches) =
        ULift.up (original.make ((PresheafSiteLift.elementsDown P).obj point) label branches) :=
      congrArg ULift.up (congrArg (original.make ((PresheafSiteLift.elementsDown P).obj point) label)
        (lower_raise_branches P shape position target point (ULift.up label) branches))
    exact computes ▸ constructed

theorem fold_raise (original : ContextualWTypes.Algebra shape position target)
    (point : (PresheafSiteLift.base P).Elements)
    (tree : NaturalTree shape position ((PresheafSiteLift.elementsDown P).obj point)) :
    ContextualWTypes.fold (upperShape P shape) (upperPosition P shape position)
      (algebra P shape position target original) (ContextualWSiteLift.raiseNatural P shape position point tree) =
      ULift.up (ContextualWTypes.fold shape position original tree) :=
  ContextualWTypes.evaluates_unique _ _ _ (ContextualWTypes.fold_evaluates _ _ _ _)
    (raise_evaluates_data P shape position target original
      (ContextualWTypes.fold_evaluates shape position original tree) point rfl)

theorem fold_lower (original : ContextualWTypes.Algebra shape position target)
    {point : (PresheafSiteLift.base P).Elements}
    (tree : NaturalTree (upperShape P shape) (upperPosition P shape position) point) :
    ContextualWTypes.fold (upperShape P shape) (upperPosition P shape position)
      (algebra P shape position target original) tree =
      ULift.up (ContextualWTypes.fold shape position original (ContextualWSiteLift.lowerNatural P shape position tree)) := by
  have same : ContextualWSiteLift.raiseNatural P shape position point
      (ContextualWSiteLift.lowerNatural P shape position tree) = tree :=
    (ContextualWSiteLift.naturalEquiv P shape position point).symm_apply_apply tree
  exact (congrArg (ContextualWTypes.fold (upperShape P shape) (upperPosition P shape position)
    (algebra P shape position target original)) same).symm.trans
      (fold_raise P shape position target original point (ContextualWSiteLift.lowerNatural P shape position tree))

noncomputable def treeBranches (point : (PresheafSiteLift.base P).Elements)
    (label : (upperShape P shape).obj point)
    (branches : Branches shape position (ContextualWTypes.family shape position) label.down) :
    Branches (upperShape P shape) (upperPosition P shape position)
      (ContextualWTypes.family (upperShape P shape) (upperPosition P shape position)) label :=
  (raiseBranches P shape position (ContextualWTypes.family shape position) point label branches).map
    (ContextualWSiteLift.inverse P shape position)

theorem constructor_raise (point : (PresheafSiteLift.base P).Elements)
    (label : (upperShape P shape).obj point)
    (branches : Branches shape position (ContextualWTypes.family shape position) label.down) :
    ContextualWSiteLift.raiseNatural P shape position point
      ((ContextualWTypes.treeAlgebra shape position).make ((PresheafSiteLift.elementsDown P).obj point) label.down branches) =
      (ContextualWTypes.treeAlgebra (upperShape P shape) (upperPosition P shape position)).make point label
        (treeBranches P shape position point label branches) := Subtype.ext rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWSiteLiftAlgebra
