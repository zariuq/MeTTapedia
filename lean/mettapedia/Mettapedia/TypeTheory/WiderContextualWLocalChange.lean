import Mettapedia.TypeTheory.WiderContextualWAlgebras
import Mettapedia.TypeTheory.ContextualWLocalChange

/-!
# Wider W algebra values through constructed future inverses

Actual local future equivalences transport complete branch tables into an
independent result universe. Both branch inverses, algebra naturality and
fold comparison are proved while the raw and natural tree carriers remain
exactly the existing original-bound ones.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.WiderContextualWLocalChange

open CategoryTheory MaterialSets.Hypersets
open MaterialSets.Hypersets.ContextualWTypes (RawTree Position Natural NaturalTree)
open MaterialSets.Hypersets.PowerClassPresheafBaseChange
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open ContextualWLocalChange

universe u h
variable {D E : Type u} [Category.{u} D] [Category.{u} E]
variable (change : ContextualWLocalChange.LocalFutures D E)
variable (domain : E ⥤ Type u) (body : domain.Elements ⥤ Type u)

variable (target : E ⥤ Type h)

theorem dependentValue_heq {I : Type u} {values : I → Type h}
    (reading : (index : I) → values index) {first second : I} (same : first = second) :
    HEq (reading first) (reading second) := by
  cases same
  rfl

def pullBranches (point : D) (label : domain.obj (change.functor.obj point))
    (branches : WiderContextualWAlgebras.Branches domain body target label) :
    WiderContextualWAlgebras.Branches (sourceDomain change domain) (sourceBody change domain body)
      (restrict change.functor target) label where
  app next arrow position := branches.app (change.functor.obj next) (change.functor.map arrow) position
  naturality _Y _Z first later position :=
    (branches.naturality _ _ (change.functor.map first) (change.functor.map later) position).trans
      (branches.app_eq (change.functor.map_comp first later).symm
        (ContextualWTypes.positionAlong domain body label (change.functor.map first) (change.functor.map later) position)
        (ContextualWTypes.positionAlong (sourceDomain change domain) (sourceBody change domain body) label first later position)
        (positionAlong_reindex_heq change domain body label first later position).symm)

theorem mapValue_heq {D : Type u} [Category.{u} D] (target : D ⥤ Type h)
    {X X' Y Y' : D} (atSource : X = X') (atTarget : Y = Y')
    (first : X ⟶ Y) (second : X' ⟶ Y') (arrows : HEq first second)
    (left : target.obj X) (right : target.obj X') (values : HEq left right) :
    HEq (target.map first left) (target.map second right) := by
  cases atSource
  cases atTarget
  cases eq_of_heq arrows
  cases eq_of_heq values
  rfl

def pushBranches (point : D) (label : (sourceDomain change domain).obj point)
    (branches : WiderContextualWAlgebras.Branches (sourceDomain change domain) (sourceBody change domain body)
      (restrict change.functor target) label) :
    WiderContextualWAlgebras.Branches domain body target label where
  app next arrow position :=
    let original : TargetBranches change domain body point label := ⟨⟨next, arrow⟩, position⟩
    let source := branchEquiv change domain body point label original
    cast (congrArg target.obj (branch_target_image change domain body point label original))
      (branches.app source.1.1 source.1.2 source.2)
  naturality Y Z first later position := by
    let original : TargetBranches change domain body point label := ⟨⟨Y, first⟩, position⟩
    let last : TargetBranches change domain body point label :=
      ⟨⟨Z, first ≫ later⟩, ContextualWTypes.positionAlong domain body label first later position⟩
    let source := branchEquiv change domain body point label original
    let ending := branchEquiv change domain body point label last
    let step : original.1 ⟶ last.1 := ⟨later, rfl⟩
    let sourceLater := ((change.backward point).map step).1
    have sourceTriangle : source.1.2 ≫ sourceLater = ending.1.2 :=
      ((change.backward point).map step).2
    have arrowImage : HEq (change.functor.map sourceLater) later :=
      backward_map_image change step
    have positionImage := (positionAlong_reindex_heq change domain body label source.1.2 sourceLater source.2).trans
      (positionAlong_worlds_heq domain body label
        (branch_target_image change domain body point label original)
        (branch_target_image change domain body point label last)
        (change.functor.map source.1.2) first (change.functor.map sourceLater) later
        (branch_arrow_image change domain body point label original) arrowImage source.2 position (cast_heq _ _))
    have positionsSame : HEq
        (ContextualWTypes.positionAlong (sourceDomain change domain) (sourceBody change domain body)
          label source.1.2 sourceLater source.2) ending.2 :=
      positionImage.trans (cast_heq _ _).symm
    have childrenSame := branches.app_eq sourceTriangle
      (ContextualWTypes.positionAlong (sourceDomain change domain) (sourceBody change domain body)
        label source.1.2 sourceLater source.2) ending.2 positionsSame
    have mapped := mapValue_heq target
      (branch_target_image change domain body point label original).symm
      (branch_target_image change domain body point label last).symm
      later (change.functor.map sourceLater) arrowImage.symm
      (cast (congrArg target.obj (branch_target_image change domain body point label original))
        (branches.app source.1.1 source.1.2 source.2))
      (branches.app source.1.1 source.1.2 source.2) (cast_heq _ _)
    exact eq_of_heq (mapped.trans ((heq_of_eq
      ((branches.naturality _ _ source.1.2 sourceLater source.2).trans childrenSame)).trans (cast_heq _ _).symm))

theorem pull_pushBranches (point : D) (label : (sourceDomain change domain).obj point)
    (branches : WiderContextualWAlgebras.Branches (sourceDomain change domain) (sourceBody change domain body)
      (restrict change.functor target) label) :
    pullBranches change domain body target point label (pushBranches change domain body target point label branches) = branches := by
  apply WiderContextualWAlgebras.Branches.ext
  intro next arrow position
  let original : SourceBranches change domain body point label := ⟨⟨next, arrow⟩, position⟩
  have same := (branchEquiv change domain body point label).apply_symm_apply original
  exact eq_of_heq ((cast_heq _ _).trans (dependentValue_heq
    (fun branch : SourceBranches change domain body point label => branches.app branch.1.1 branch.1.2 branch.2) same))

theorem push_pullBranches (point : D) (label : domain.obj (change.functor.obj point))
    (branches : WiderContextualWAlgebras.Branches domain body target label) :
    pushBranches change domain body target point label (pullBranches change domain body target point label branches) = branches := by
  apply WiderContextualWAlgebras.Branches.ext
  intro next arrow position
  let original : TargetBranches change domain body point label := ⟨⟨next, arrow⟩, position⟩
  have same := (branchEquiv change domain body point label).symm_apply_apply original
  exact eq_of_heq ((cast_heq _ _).trans (dependentValue_heq
    (fun branch : TargetBranches change domain body point label => branches.app branch.1.1 branch.1.2 branch.2) same))

def branchesEquiv (point : D) (label : domain.obj (change.functor.obj point)) :
    WiderContextualWAlgebras.Branches domain body target label ≃
      WiderContextualWAlgebras.Branches (sourceDomain change domain) (sourceBody change domain body)
        (restrict change.functor target) label where
  toFun := pullBranches change domain body target point label
  invFun := pushBranches change domain body target point label
  left_inv := push_pullBranches change domain body target point label
  right_inv := pull_pushBranches change domain body target point label

theorem pullBranches_restrict {X Y : D} (arrow : X ⟶ Y)
    (label : domain.obj (change.functor.obj X)) (branches : WiderContextualWAlgebras.Branches domain body target label) :
    pullBranches change domain body target Y ((sourceDomain change domain).map arrow label)
      (branches.restrict (change.functor.map arrow)) =
      (pullBranches change domain body target X label branches).restrict arrow := by
  apply WiderContextualWAlgebras.Branches.ext
  intro Z later position
  exact branches.app_eq (change.functor.map_comp arrow later).symm
    (ContextualWTypes.compositePosition domain body label (change.functor.map arrow) (change.functor.map later) position)
    (ContextualWTypes.compositePosition (sourceDomain change domain) (sourceBody change domain body) label arrow later position)
    ((cast_heq _ _).trans (cast_heq _ _).symm)

theorem pushBranches_restrict {X Y : D} (arrow : X ⟶ Y)
    (label : (sourceDomain change domain).obj X)
    (branches : WiderContextualWAlgebras.Branches (sourceDomain change domain) (sourceBody change domain body)
      (restrict change.functor target) label) :
    pushBranches change domain body target Y ((sourceDomain change domain).map arrow label) (branches.restrict arrow) =
      (pushBranches change domain body target X label branches).restrict (change.functor.map arrow) := by
  apply (branchesEquiv change domain body target Y ((sourceDomain change domain).map arrow label)).injective
  change pullBranches change domain body target Y _ (pushBranches change domain body target Y _ _) =
    pullBranches change domain body target Y _ ((pushBranches change domain body target X label branches).restrict _)
  exact (pull_pushBranches change domain body target Y ((sourceDomain change domain).map arrow label)
    (branches.restrict arrow)).trans
      ((pullBranches_restrict change domain body target arrow label
        (pushBranches change domain body target X label branches)).trans
          (congrArg (fun term => term.restrict arrow)
            (pull_pushBranches change domain body target X label branches))).symm

def pullAlgebra (algebra : WiderContextualWAlgebras.Algebra domain body target) :
    WiderContextualWAlgebras.Algebra (sourceDomain change domain) (sourceBody change domain body)
      (restrict change.functor target) where
  make point label branches := algebra.make (change.functor.obj point) label
    (pushBranches change domain body target point label branches)
  naturality X Y arrow label branches :=
    (algebra.naturality _ _ (change.functor.map arrow) label
      (pushBranches change domain body target X label branches)).trans
        (congrArg (algebra.make (change.functor.obj Y) ((sourceDomain change domain).map arrow label))
          (pushBranches_restrict change domain body target arrow label branches).symm)

theorem pull_evaluates_data (algebra : WiderContextualWAlgebras.Algebra domain body target)
    {X : E} {tree : RawTree domain body X} {value : target.obj X}
    (evaluates : WiderContextualWAlgebras.Evaluates domain body algebra tree value) :
    ∀ point : D, ∀ atPoint : change.functor.obj point = X,
      WiderContextualWAlgebras.Evaluates (sourceDomain change domain) (sourceBody change domain body)
        (pullAlgebra change domain body target algebra) (pullRawData change domain body tree point atPoint)
          (cast (congrArg target.obj atPoint.symm) value) := by
  induction evaluates with
  | @sup X label children branches values earlier =>
    intro point atPoint
    cases atPoint
    change WiderContextualWAlgebras.Evaluates (sourceDomain change domain) (sourceBody change domain body)
      (pullAlgebra change domain body target algebra)
      (.sup label (fun next arrow position => pullRaw change domain body next
        (children (change.functor.obj next) (change.functor.map arrow) position)))
      (algebra.make (change.functor.obj point) label branches)
    have smaller : ∀ next arrow position,
        WiderContextualWAlgebras.Evaluates (sourceDomain change domain) (sourceBody change domain body)
          (pullAlgebra change domain body target algebra)
          (pullRaw change domain body next (children (change.functor.obj next) (change.functor.map arrow) position))
          ((pullBranches change domain body target point label branches).app next arrow position) := by
      intro next arrow position
      exact earlier _ _ _ next rfl
    have constructed := WiderContextualWAlgebras.Evaluates.sup
      (algebra := pullAlgebra change domain body target algebra) label _
      (pullBranches change domain body target point label branches) smaller
    have computation : (pullAlgebra change domain body target algebra).make point label
        (pullBranches change domain body target point label branches) =
        algebra.make (change.functor.obj point) label branches :=
      congrArg (algebra.make (change.functor.obj point) label)
        (push_pullBranches change domain body target point label branches)
    rw [computation] at constructed
    exact constructed

theorem fold_baseChange (algebra : WiderContextualWAlgebras.Algebra domain body target) (point : D)
    (tree : NaturalTree domain body (change.functor.obj point)) :
    WiderContextualWAlgebras.fold (sourceDomain change domain) (sourceBody change domain body)
      (pullAlgebra change domain body target algebra) (naturalEquiv change domain body point tree) =
        WiderContextualWAlgebras.fold domain body algebra tree :=
  WiderContextualWAlgebras.evaluates_unique _ _ _
    (WiderContextualWAlgebras.fold_evaluates _ _ _ _)
    (pull_evaluates_data change domain body target algebra
      (WiderContextualWAlgebras.fold_evaluates domain body algebra tree) point rfl)


end Mettapedia.TypeTheory.WiderContextualWLocalChange
