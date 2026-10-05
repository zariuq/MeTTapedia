import Mettapedia.TypeTheory.ContextualFutureConeChange
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWBaseChange

/-!
# W transport through constructed local future inverses

Only the actual context functor and its inverse functors on complete
future categories enter the input. Raw tree operations, their inverse
laws, restriction and hereditary naturality are constructed by indexed
tree recursion. Prefix maps are instantiated with independently proved
category inverses, even when their complete histories are not globally
injective.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualWLocalChange

open CategoryTheory
open MaterialSets.Hypersets
open MaterialSets.Hypersets.ContextualWTypes (RawTree Position Natural NaturalTree)
open MaterialSets.Hypersets.PowerClassPresheafProducts
open MaterialSets.Hypersets.PowerClassPresheafBaseChange
open Mettapedia.GSLT.Topos.ConstructivePresheaf

universe u
variable {D E : Type u} [Category.{u} D] [Category.{u} E]

/-- Actual inverse context functors on all local futures. There is no
W carrier, tree operation or W comparison among these fields. -/
structure LocalFutures (D E : Type u) [Category.{u} D] [Category.{u} E] where
  functor : D ⥤ E
  backward : (point : D) → Future.Objects (functor.obj point) ⥤ Future.Objects point
  left : ∀ point, Cat.compose (Future.map functor point) (backward point) = Cat.identity (Future.Objects point)
  right : ∀ point, Cat.compose (backward point) (Future.map functor point) =
    Cat.identity (Future.Objects (functor.obj point))

variable (change : LocalFutures D E)

theorem backward_forward_obj (point : D) (future : Future.Objects point) :
    (change.backward point).obj ((Future.map change.functor point).obj future) = future :=
  congrArg (fun operation : Future.Objects point ⥤ Future.Objects point => operation.obj future) (change.left point)

theorem forward_backward_obj (point : D) (future : Future.Objects (change.functor.obj point)) :
    (Future.map change.functor point).obj ((change.backward point).obj future) = future :=
  congrArg (fun operation : Future.Objects (change.functor.obj point) ⥤
    Future.Objects (change.functor.obj point) => operation.obj future) (change.right point)

theorem backward_target_image (point : D) (future : Future.Objects (change.functor.obj point)) :
    change.functor.obj ((change.backward point).obj future).1 = future.1 :=
  congrArg Future.Objects.fst (forward_backward_obj change point future)

theorem backward_map_image {point : D}
    {first second : Future.Objects (change.functor.obj point)} (step : first ⟶ second) :
    HEq (change.functor.map (((change.backward point).map step).1)) step.1 :=
  ContextualSmallFamilyTypeFormers.futureArrow_value_heq
    (forward_backward_obj change point first) (forward_backward_obj change point second) _ _
    (Cat.equalFunctor_arrow (change.right point) step)

variable (domain : E ⥤ Type u) (body : domain.Elements ⥤ Type u)

abbrev sourceDomain := restrict change.functor domain
abbrev sourceBody := restrict (Cat.elementsMap change.functor domain) body

abbrev TargetBranches (point : D) (label : domain.obj (change.functor.obj point)) :=
  (future : Future.Objects (change.functor.obj point)) × Position domain body label future.2

abbrev SourceBranches (point : D) (label : (sourceDomain change domain).obj point) :=
  (future : Future.Objects point) × Position (sourceDomain change domain) (sourceBody change domain body) label future.2

/-- Explicit transport of a dependent carrier through constructed inverse
index maps. No representative or inverse operation is selected. -/
def sigmaPullEquiv {I J : Type u} (forward : I → J) (backward : J → I)
    (left : ∀ index, backward (forward index) = index)
    (right : ∀ index, forward (backward index) = index) (family : J → Type u) :
    (Sigma family) ≃ ((index : I) × family (forward index)) where
  toFun entry := ⟨backward entry.1, cast (congrArg family (right entry.1).symm) entry.2⟩
  invFun entry := ⟨forward entry.1, entry.2⟩
  left_inv entry := Sigma.ext (right entry.1) (cast_heq _ _)
  right_inv entry := Sigma.ext (left entry.1) (cast_heq _ _)

def branchEquiv (point : D) (label : domain.obj (change.functor.obj point)) :
    TargetBranches change domain body point label ≃ SourceBranches change domain body point label :=
  sigmaPullEquiv (Future.map change.functor point).obj (change.backward point).obj
    (backward_forward_obj change point) (forward_backward_obj change point)
    (fun future => Position domain body label future.2)

theorem branch_target_image (point : D) (label : domain.obj (change.functor.obj point))
    (branch : TargetBranches change domain body point label) :
    change.functor.obj (branchEquiv change domain body point label branch).1.1 = branch.1.1 :=
  backward_target_image change point branch.1

theorem branch_forward (point : D) (label : (sourceDomain change domain).obj point)
    (branch : SourceBranches change domain body point label) :
    (branchEquiv change domain body point label).symm branch =
      ⟨⟨change.functor.obj branch.1.1, change.functor.map branch.1.2⟩, branch.2⟩ := rfl

noncomputable def pullRawData {target : E} (tree : RawTree domain body target) :
    (point : D) → change.functor.obj point = target →
      RawTree (sourceDomain change domain) (sourceBody change domain body) point :=
  RawTree.rec (motive := fun target _ => (point : D) → change.functor.obj point = target →
      RawTree (sourceDomain change domain) (sourceBody change domain body) point)
    (fun {target} label children earlier point same => by
      cases same
      exact .sup label (fun next arrow branch => earlier (change.functor.obj next)
        (change.functor.map arrow) branch next rfl)) tree

noncomputable def pullRaw (point : D) (tree : RawTree domain body (change.functor.obj point)) :
    RawTree (sourceDomain change domain) (sourceBody change domain body) point :=
  pullRawData change domain body tree point rfl

theorem pullRaw_sup (point : D) (label : domain.obj (change.functor.obj point))
    (children : (target : E) → (arrow : change.functor.obj point ⟶ target) →
      Position domain body label arrow → RawTree domain body target) :
    pullRaw change domain body point (.sup label children) =
      .sup label (fun next arrow branch => pullRaw change domain body next
        (children (change.functor.obj next) (change.functor.map arrow) branch)) := rfl

noncomputable def pushRaw {point : D}
    (tree : RawTree (sourceDomain change domain) (sourceBody change domain body) point) :
    RawTree domain body (change.functor.obj point) :=
  RawTree.rec (motive := fun point _ => RawTree domain body (change.functor.obj point))
    (fun {point} label _children earlier => .sup label (fun next arrow branch =>
      let lifted := branchEquiv change domain body point label ⟨⟨next, arrow⟩, branch⟩
      cast (congrArg (RawTree domain body) (branch_target_image change domain body point label ⟨⟨next, arrow⟩, branch⟩))
        (earlier lifted.1.1 lifted.1.2 lifted.2))) tree

theorem pushRaw_sup (point : D) (label : (sourceDomain change domain).obj point)
    (children : (next : D) → (arrow : point ⟶ next) →
      Position (sourceDomain change domain) (sourceBody change domain body) label arrow →
        RawTree (sourceDomain change domain) (sourceBody change domain body) next) :
    pushRaw change domain body (.sup label children) =
      .sup label (fun next arrow branch =>
        let lifted := branchEquiv change domain body point label ⟨⟨next, arrow⟩, branch⟩
        cast (congrArg (RawTree domain body) (branch_target_image change domain body point label ⟨⟨next, arrow⟩, branch⟩))
          (pushRaw change domain body (children lifted.1.1 lifted.1.2 lifted.2))) := rfl

theorem pullRawData_heq {first second : D} {X Y : E}
    (points : first = second) (left : RawTree domain body X) (right : RawTree domain body Y)
    (trees : HEq left right) (atFirst : change.functor.obj first = X)
    (atSecond : change.functor.obj second = Y) :
    HEq (pullRawData change domain body left first atFirst) (pullRawData change domain body right second atSecond) := by
  cases points
  have targets : X = Y := atFirst.symm.trans atSecond
  cases targets
  cases eq_of_heq trees
  rfl

theorem positionAlong_reindex_heq {X Y Z : D} (label : (sourceDomain change domain).obj X)
    (first : X ⟶ Y) (later : Y ⟶ Z)
    (branch : Position (sourceDomain change domain) (sourceBody change domain body) label first) :
    HEq (ContextualWTypes.positionAlong (sourceDomain change domain) (sourceBody change domain body) label first later branch)
      (ContextualWTypes.positionAlong domain body label (change.functor.map first) (change.functor.map later) branch) :=
  (cast_heq _ _).trans (cast_heq _ _).symm

theorem pullRaw_restrict {X Y : D} (arrow : X ⟶ Y)
    (tree : RawTree domain body (change.functor.obj X)) :
    pullRaw change domain body Y (ContextualWTypes.restrict domain body (change.functor.map arrow) tree) =
      ContextualWTypes.restrict (sourceDomain change domain) (sourceBody change domain body) arrow
        (pullRaw change domain body X tree) := by
  cases tree with
  | sup label children =>
    apply RawTree.sup_eq_of_cast rfl
    intro Z later branch
    apply congrArg (pullRaw change domain body Z)
    exact RawTree.children_eq label children (change.functor.map_comp arrow later).symm
      (ContextualWTypes.compositePosition domain body label (change.functor.map arrow) (change.functor.map later) branch)
      (ContextualWTypes.compositePosition (sourceDomain change domain) (sourceBody change domain body) label arrow later branch)
      ((cast_heq _ _).trans (cast_heq _ _).symm)

theorem pull_push {point : D}
    (tree : RawTree (sourceDomain change domain) (sourceBody change domain body) point) :
    pullRaw change domain body point (pushRaw change domain body tree) = tree := by
  induction tree with
  | @sup point label children earlier =>
    rw [pushRaw_sup]
    change RawTree.sup label (fun next arrow position => pullRaw change domain body next
      (cast (congrArg (RawTree domain body) (branch_target_image change domain body point label
        ⟨⟨change.functor.obj next, change.functor.map arrow⟩, position⟩))
        (pushRaw change domain body
          (children (branchEquiv change domain body point label
            ⟨⟨change.functor.obj next, change.functor.map arrow⟩, position⟩).1.1
            (branchEquiv change domain body point label
              ⟨⟨change.functor.obj next, change.functor.map arrow⟩, position⟩).1.2
            (branchEquiv change domain body point label
              ⟨⟨change.functor.obj next, change.functor.map arrow⟩, position⟩).2)))) = .sup label children
    apply RawTree.sup_eq_of_cast rfl
    intro next arrow position
    let original : SourceBranches change domain body point label := ⟨⟨next, arrow⟩, position⟩
    let target := (branchEquiv change domain body point label).symm original
    let recovered := branchEquiv change domain body point label target
    have same : recovered = original := (branchEquiv change domain body point label).apply_symm_apply original
    let child := children recovered.1.1 recovered.1.2 recovered.2
    let raised := cast (congrArg (RawTree domain body)
      (branch_target_image change domain body point label target)) (pushRaw change domain body child)
    change pullRaw change domain body next raised = children next arrow position
    have transported := pullRawData_heq change domain body
      (congrArg (fun branch : SourceBranches change domain body point label => branch.1.1) same.symm)
      raised (pushRaw change domain body child) (cast_heq _ _) rfl rfl
    have childSame := Cat.dependentValue_heq
      (fun branch : SourceBranches change domain body point label => children branch.1.1 branch.1.2 branch.2) same
    exact eq_of_heq (transported.trans ((heq_of_eq (earlier recovered.1.1 recovered.1.2 recovered.2)).trans childSame))

theorem push_pull_data {target : E} (tree : RawTree domain body target) :
    ∀ point : D, ∀ atPoint : change.functor.obj point = target,
      HEq (pushRaw change domain body (pullRawData change domain body tree point atPoint)) tree := by
  induction tree with
  | @sup target label children earlier =>
    intro point atPoint
    cases atPoint
    apply heq_of_eq
    rw [show pullRawData change domain body (.sup label children) point rfl =
      pullRaw change domain body point (.sup label children) from rfl, pullRaw_sup]
    change RawTree.sup label (fun next arrow position =>
      let source := branchEquiv change domain body point label ⟨⟨next, arrow⟩, position⟩
      cast (congrArg (RawTree domain body) (branch_target_image change domain body point label ⟨⟨next, arrow⟩, position⟩))
        (pushRaw change domain body (pullRaw change domain body source.1.1
          (children (change.functor.obj source.1.1) (change.functor.map source.1.2) source.2)))) =
      .sup label children
    apply RawTree.sup_eq_of_cast rfl
    intro next arrow position
    let original : TargetBranches change domain body point label := ⟨⟨next, arrow⟩, position⟩
    let source := branchEquiv change domain body point label original
    let recovered := (branchEquiv change domain body point label).symm source
    have same : recovered = original := (branchEquiv change domain body point label).symm_apply_apply original
    have childSame := Cat.dependentValue_heq
      (fun branch : TargetBranches change domain body point label => children branch.1.1 branch.1.2 branch.2) same
    exact eq_of_heq ((cast_heq _ _).trans
      ((earlier recovered.1.1 recovered.1.2 recovered.2 source.1.1 rfl).trans childSame))

theorem push_pull (point : D) (tree : RawTree domain body (change.functor.obj point)) :
    pushRaw change domain body (pullRaw change domain body point tree) = tree :=
  eq_of_heq (push_pull_data change domain body tree point rfl)

noncomputable def rawEquiv (point : D) :
    RawTree domain body (change.functor.obj point) ≃
      RawTree (sourceDomain change domain) (sourceBody change domain body) point where
  toFun := pullRaw change domain body point
  invFun := pushRaw change domain body
  left_inv := push_pull change domain body point
  right_inv := pull_push change domain body

theorem pushRaw_restrict {X Y : D} (arrow : X ⟶ Y)
    (tree : RawTree (sourceDomain change domain) (sourceBody change domain body) X) :
    pushRaw change domain body (ContextualWTypes.restrict (sourceDomain change domain)
      (sourceBody change domain body) arrow tree) =
      ContextualWTypes.restrict domain body (change.functor.map arrow) (pushRaw change domain body tree) := by
  apply (rawEquiv change domain body Y).injective
  change pullRaw change domain body Y (pushRaw change domain body _) =
    pullRaw change domain body Y (ContextualWTypes.restrict domain body (change.functor.map arrow) _)
  rw [pull_push, pullRaw_restrict, pull_push]

theorem pull_natural_data {target : E} (tree : RawTree domain body target) :
    ∀ point : D, ∀ atPoint : change.functor.obj point = target,
      Natural domain body tree →
        Natural (sourceDomain change domain) (sourceBody change domain body)
          (pullRawData change domain body tree point atPoint) := by
  induction tree with
  | @sup target label children earlier =>
    intro point atPoint natural
    cases atPoint
    constructor
    · intro next arrow position
      exact earlier _ _ _ next rfl (natural.1 (change.functor.obj next) (change.functor.map arrow) position)
    · intro Y Z first later position
      change ContextualWTypes.restrict (sourceDomain change domain) (sourceBody change domain body) later
        (pullRaw change domain body Y (children (change.functor.obj Y) (change.functor.map first) position)) =
        pullRaw change domain body Z
          (children (change.functor.obj Z) (change.functor.map (first ≫ later))
            (ContextualWTypes.positionAlong (sourceDomain change domain) (sourceBody change domain body) label first later position))
      rw [← pullRaw_restrict]
      apply congrArg (pullRaw change domain body Z)
      exact (natural.2 _ _ (change.functor.map first) (change.functor.map later) position).trans
        (RawTree.children_eq label children (change.functor.map_comp first later).symm
          (ContextualWTypes.positionAlong domain body label (change.functor.map first) (change.functor.map later) position)
          (ContextualWTypes.positionAlong (sourceDomain change domain) (sourceBody change domain body) label first later position)
          (positionAlong_reindex_heq change domain body label first later position).symm)

theorem pull_natural (point : D) (tree : RawTree domain body (change.functor.obj point))
    (natural : Natural domain body tree) :
    Natural (sourceDomain change domain) (sourceBody change domain body) (pullRaw change domain body point tree) :=
  pull_natural_data change domain body tree point rfl natural

theorem restrict_heq {D : Type u} [Category.{u} D] (shape : D ⥤ Type u)
    (position : shape.Elements ⥤ Type u) {X X' Y Y' : D}
    (atSource : X = X') (atTarget : Y = Y') (first : X ⟶ Y) (second : X' ⟶ Y')
    (arrows : HEq first second) (left : RawTree shape position X) (right : RawTree shape position X')
    (trees : HEq left right) :
    HEq (ContextualWTypes.restrict shape position first left) (ContextualWTypes.restrict shape position second right) := by
  cases atSource
  cases atTarget
  cases eq_of_heq arrows
  cases eq_of_heq trees
  rfl

theorem natural_heq {D : Type u} [Category.{u} D] (shape : D ⥤ Type u)
    (position : shape.Elements ⥤ Type u) {X Y : D} (worlds : X = Y)
    (first : RawTree shape position X) (second : RawTree shape position Y) (trees : HEq first second) :
    Natural shape position first ↔ Natural shape position second := by
  cases worlds
  cases eq_of_heq trees
  rfl

theorem positionAlong_worlds_heq {D : Type u} [Category.{u} D] (shape : D ⥤ Type u)
    (position : shape.Elements ⥤ Type u) {X Y Y' Z Z' : D} (label : shape.obj X)
    (atFirst : Y = Y') (atLast : Z = Z') (first : X ⟶ Y) (first' : X ⟶ Y')
    (later : Y ⟶ Z) (later' : Y' ⟶ Z') (firstArrows : HEq first first') (laterArrows : HEq later later')
    (branch : Position shape position label first) (branch' : Position shape position label first')
    (branches : HEq branch branch') :
    HEq (ContextualWTypes.positionAlong shape position label first later branch)
      (ContextualWTypes.positionAlong shape position label first' later' branch') := by
  cases atFirst
  cases atLast
  cases eq_of_heq firstArrows
  cases eq_of_heq laterArrows
  cases eq_of_heq branches
  rfl

theorem branch_arrow_image (point : D) (label : domain.obj (change.functor.obj point))
    (branch : TargetBranches change domain body point label) :
    HEq (change.functor.map (branchEquiv change domain body point label branch).1.2) branch.1.2 :=
  Cat.dependentValue_heq (fun future : Future.Objects (change.functor.obj point) => future.2)
    (forward_backward_obj change point branch.1)

theorem push_natural {point : D}
    (tree : RawTree (sourceDomain change domain) (sourceBody change domain body) point)
    (natural : Natural (sourceDomain change domain) (sourceBody change domain body) tree) :
    Natural domain body (pushRaw change domain body tree) := by
  induction tree with
  | @sup point label children earlier =>
    constructor
    · intro next arrow position
      let original : TargetBranches change domain body point label := ⟨⟨next, arrow⟩, position⟩
      let source := branchEquiv change domain body point label original
      exact (natural_heq domain body (branch_target_image change domain body point label original)
        (pushRaw change domain body (children source.1.1 source.1.2 source.2)) _ (cast_heq _ _).symm).mp
          (earlier source.1.1 source.1.2 source.2 (natural.1 _ _ _))
    · intro Y Z first later position
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
      have childrenSame := RawTree.children_eq label children sourceTriangle
        (ContextualWTypes.positionAlong (sourceDomain change domain) (sourceBody change domain body)
          label source.1.2 sourceLater source.2) ending.2 positionsSame
      have restrictImage := restrict_heq domain body
        (branch_target_image change domain body point label original).symm
        (branch_target_image change domain body point label last).symm
        later (change.functor.map sourceLater) arrowImage.symm
        (cast (congrArg (RawTree domain body) (branch_target_image change domain body point label original))
          (pushRaw change domain body (children source.1.1 source.1.2 source.2)))
        (pushRaw change domain body (children source.1.1 source.1.2 source.2)) (cast_heq _ _)
      exact eq_of_heq (restrictImage.trans
        ((heq_of_eq (pushRaw_restrict change domain body sourceLater (children source.1.1 source.1.2 source.2)).symm).trans
          ((heq_of_eq (congrArg (pushRaw change domain body)
            ((natural.2 _ _ source.1.2 sourceLater source.2).trans childrenSame))).trans (cast_heq _ _).symm)))

noncomputable def naturalEquiv (point : D) :
    NaturalTree domain body (change.functor.obj point) ≃
      NaturalTree (sourceDomain change domain) (sourceBody change domain body) point where
  toFun tree := ⟨pullRaw change domain body point tree.val, pull_natural change domain body point tree.val tree.property⟩
  invFun tree := ⟨pushRaw change domain body tree.val, push_natural change domain body tree.val tree.property⟩
  left_inv tree := Subtype.ext (push_pull change domain body point tree.val)
  right_inv tree := Subtype.ext (pull_push change domain body tree.val)


noncomputable def wBaseChange :
    NatTrans (restrict change.functor (ContextualWTypes.family domain body))
      (ContextualWTypes.family (sourceDomain change domain) (sourceBody change domain body)) where
  app point := TypeCat.ofHom (naturalEquiv change domain body point)
  naturality X Y arrow := by
    apply ConcreteCategory.hom_ext
    intro tree
    exact Subtype.ext (pullRaw_restrict change domain body arrow tree.val)

noncomputable def wBaseChangeInverse :
    NatTrans (ContextualWTypes.family (sourceDomain change domain) (sourceBody change domain body))
      (restrict change.functor (ContextualWTypes.family domain body)) :=
  PowerClassPresheafBaseChange.Nat.inverse (wBaseChange change domain body)
    (naturalEquiv change domain body) (fun _ _ => rfl)

theorem wBaseChange_left :
    Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose
      (wBaseChange change domain body) (wBaseChangeInverse change domain body) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity
        (restrict change.functor (ContextualWTypes.family domain body)) :=
  PowerClassPresheafBaseChange.Nat.inverse_left (wBaseChange change domain body)
    (naturalEquiv change domain body) (fun _ _ => rfl)

theorem wBaseChange_right :
    Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose
      (wBaseChangeInverse change domain body) (wBaseChange change domain body) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity
        (ContextualWTypes.family (sourceDomain change domain) (sourceBody change domain body)) :=
  PowerClassPresheafBaseChange.Nat.inverse_right (wBaseChange change domain body)
    (naturalEquiv change domain body) (fun _ _ => rfl)

variable (target : E ⥤ Type u)

def pullBranches (point : D) (label : domain.obj (change.functor.obj point))
    (branches : ContextualWTypes.Branches domain body target label) :
    ContextualWTypes.Branches (sourceDomain change domain) (sourceBody change domain body)
      (restrict change.functor target) label where
  app next arrow position := branches.app (change.functor.obj next) (change.functor.map arrow) position
  naturality _Y _Z first later position :=
    (branches.naturality _ _ (change.functor.map first) (change.functor.map later) position).trans
      (branches.app_eq (change.functor.map_comp first later).symm
        (ContextualWTypes.positionAlong domain body label (change.functor.map first) (change.functor.map later) position)
        (ContextualWTypes.positionAlong (sourceDomain change domain) (sourceBody change domain body) label first later position)
        (positionAlong_reindex_heq change domain body label first later position).symm)

theorem mapValue_heq {D : Type u} [Category.{u} D] (target : D ⥤ Type u)
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
    (branches : ContextualWTypes.Branches (sourceDomain change domain) (sourceBody change domain body)
      (restrict change.functor target) label) :
    ContextualWTypes.Branches domain body target label where
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
    (branches : ContextualWTypes.Branches (sourceDomain change domain) (sourceBody change domain body)
      (restrict change.functor target) label) :
    pullBranches change domain body target point label (pushBranches change domain body target point label branches) = branches := by
  apply ContextualWTypes.Branches.ext
  intro next arrow position
  let original : SourceBranches change domain body point label := ⟨⟨next, arrow⟩, position⟩
  have same := (branchEquiv change domain body point label).apply_symm_apply original
  exact eq_of_heq ((cast_heq _ _).trans (Cat.dependentValue_heq
    (fun branch : SourceBranches change domain body point label => branches.app branch.1.1 branch.1.2 branch.2) same))

theorem push_pullBranches (point : D) (label : domain.obj (change.functor.obj point))
    (branches : ContextualWTypes.Branches domain body target label) :
    pushBranches change domain body target point label (pullBranches change domain body target point label branches) = branches := by
  apply ContextualWTypes.Branches.ext
  intro next arrow position
  let original : TargetBranches change domain body point label := ⟨⟨next, arrow⟩, position⟩
  have same := (branchEquiv change domain body point label).symm_apply_apply original
  exact eq_of_heq ((cast_heq _ _).trans (Cat.dependentValue_heq
    (fun branch : TargetBranches change domain body point label => branches.app branch.1.1 branch.1.2 branch.2) same))

def branchesEquiv (point : D) (label : domain.obj (change.functor.obj point)) :
    ContextualWTypes.Branches domain body target label ≃
      ContextualWTypes.Branches (sourceDomain change domain) (sourceBody change domain body)
        (restrict change.functor target) label where
  toFun := pullBranches change domain body target point label
  invFun := pushBranches change domain body target point label
  left_inv := push_pullBranches change domain body target point label
  right_inv := pull_pushBranches change domain body target point label

theorem pullBranches_restrict {X Y : D} (arrow : X ⟶ Y)
    (label : domain.obj (change.functor.obj X)) (branches : ContextualWTypes.Branches domain body target label) :
    pullBranches change domain body target Y ((sourceDomain change domain).map arrow label)
      (branches.restrict (change.functor.map arrow)) =
      (pullBranches change domain body target X label branches).restrict arrow := by
  apply ContextualWTypes.Branches.ext
  intro Z later position
  exact branches.app_eq (change.functor.map_comp arrow later).symm
    (ContextualWTypes.compositePosition domain body label (change.functor.map arrow) (change.functor.map later) position)
    (ContextualWTypes.compositePosition (sourceDomain change domain) (sourceBody change domain body) label arrow later position)
    ((cast_heq _ _).trans (cast_heq _ _).symm)

theorem pushBranches_restrict {X Y : D} (arrow : X ⟶ Y)
    (label : (sourceDomain change domain).obj X)
    (branches : ContextualWTypes.Branches (sourceDomain change domain) (sourceBody change domain body)
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

def pullAlgebra (algebra : ContextualWTypes.Algebra domain body target) :
    ContextualWTypes.Algebra (sourceDomain change domain) (sourceBody change domain body)
      (restrict change.functor target) where
  make point label branches := algebra.make (change.functor.obj point) label
    (pushBranches change domain body target point label branches)
  naturality X Y arrow label branches :=
    (algebra.naturality _ _ (change.functor.map arrow) label
      (pushBranches change domain body target X label branches)).trans
        (congrArg (algebra.make (change.functor.obj Y) ((sourceDomain change domain).map arrow label))
          (pushBranches_restrict change domain body target arrow label branches).symm)

theorem pull_evaluates_data (algebra : ContextualWTypes.Algebra domain body target)
    {X : E} {tree : RawTree domain body X} {value : target.obj X}
    (evaluates : ContextualWTypes.Evaluates domain body algebra tree value) :
    ∀ point : D, ∀ atPoint : change.functor.obj point = X,
      ContextualWTypes.Evaluates (sourceDomain change domain) (sourceBody change domain body)
        (pullAlgebra change domain body target algebra) (pullRawData change domain body tree point atPoint)
          (cast (congrArg target.obj atPoint.symm) value) := by
  induction evaluates with
  | @sup X label children branches values earlier =>
    intro point atPoint
    cases atPoint
    change ContextualWTypes.Evaluates (sourceDomain change domain) (sourceBody change domain body)
      (pullAlgebra change domain body target algebra)
      (.sup label (fun next arrow position => pullRaw change domain body next
        (children (change.functor.obj next) (change.functor.map arrow) position)))
      (algebra.make (change.functor.obj point) label branches)
    have smaller : ∀ next arrow position,
        ContextualWTypes.Evaluates (sourceDomain change domain) (sourceBody change domain body)
          (pullAlgebra change domain body target algebra)
          (pullRaw change domain body next (children (change.functor.obj next) (change.functor.map arrow) position))
          ((pullBranches change domain body target point label branches).app next arrow position) := by
      intro next arrow position
      exact earlier _ _ _ next rfl
    have constructed := ContextualWTypes.Evaluates.sup
      (algebra := pullAlgebra change domain body target algebra) label _
      (pullBranches change domain body target point label branches) smaller
    have computation : (pullAlgebra change domain body target algebra).make point label
        (pullBranches change domain body target point label branches) =
        algebra.make (change.functor.obj point) label branches :=
      congrArg (algebra.make (change.functor.obj point) label)
        (push_pullBranches change domain body target point label branches)
    rw [computation] at constructed
    exact constructed

theorem fold_baseChange (algebra : ContextualWTypes.Algebra domain body target) (point : D)
    (tree : NaturalTree domain body (change.functor.obj point)) :
    ContextualWTypes.fold (sourceDomain change domain) (sourceBody change domain body)
      (pullAlgebra change domain body target algebra) (naturalEquiv change domain body point tree) =
        ContextualWTypes.fold domain body algebra tree :=
  ContextualWTypes.evaluates_unique _ _ _
    (ContextualWTypes.fold_evaluates _ _ _ _)
    (pull_evaluates_data change domain body target algebra
      (ContextualWTypes.fold_evaluates domain body algebra tree) point rfl)

noncomputable def pullTreeBranches (point : D) (label : domain.obj (change.functor.obj point))
    (branches : ContextualWTypes.Branches domain body (ContextualWTypes.family domain body) label) :
    ContextualWTypes.Branches (sourceDomain change domain) (sourceBody change domain body)
      (ContextualWTypes.family (sourceDomain change domain) (sourceBody change domain body)) label :=
  (pullBranches change domain body (ContextualWTypes.family domain body) point label branches).map
    (wBaseChange change domain body)

theorem constructor_baseChange (point : D) (label : domain.obj (change.functor.obj point))
    (branches : ContextualWTypes.Branches domain body (ContextualWTypes.family domain body) label) :
    naturalEquiv change domain body point
      ((ContextualWTypes.treeAlgebra domain body).make (change.functor.obj point) label branches) =
    (ContextualWTypes.treeAlgebra (sourceDomain change domain) (sourceBody change domain body)).make point label
      (pullTreeBranches change domain body point label branches) := Subtype.ext rfl


/-- Prefixing histories has constructed local future inverses. -/
def prefixChange {C : Type u} [Category.{u} C] {first second : C} (step : first ⟶ second) :
    LocalFutures (Future.Objects second) (Future.Objects first) where
  functor := ContextualSmallFamilyUniverse.futurePrefix step
  backward := ContextualFutureConeChange.backward step
  left := ContextualFutureConeChange.backward_forward step
  right := ContextualFutureConeChange.forward_backward step

end Mettapedia.TypeTheory.ContextualWLocalChange
