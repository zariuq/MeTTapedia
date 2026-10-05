import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWTypes

/-!
# Contextual indexed W base change along natural transformations

The comparison retains every future world, actual arrow and transported
position. The source-to-target direction uses the existing constructed full
future lift. Both raw tree operations use indexed induction rather than a
supplied W comparison or selected inverse.

This is a semantic presheaf comparison. It does not infer a host context
decoder or compare arbitrarily chosen material graph labels by equality.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWBaseChange

open CategoryTheory
open ContextualWTypes (RawTree Position Natural NaturalTree)
open PowerClassPresheafProducts
open PowerClassPresheafBaseChange
open Mettapedia.GSLT.Topos.ConstructivePresheaf

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q : Cᵒᵖ ⥤ Type u} (change : NatTrans Q P)
variable (domain : P.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)

abbrev sourceDomain := PowerClassPresheafProducts.reindex change domain
abbrev sourceBody := PowerClassPresheafBaseChange.bodyReindex change domain body

abbrev TargetBranches (point : Q.Elements) (label : domain.obj ((elementMap change).obj point)) :=
  (future : Future.Objects ((elementMap change).obj point)) × Position domain body label future.2

abbrev SourceBranches (point : Q.Elements) (label : (sourceDomain change domain).obj point) :=
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

def branchEquiv (point : Q.Elements) (label : domain.obj ((elementMap change).obj point)) :
    TargetBranches change domain body point label ≃ SourceBranches change domain body point label :=
  sigmaPullEquiv (Future.map (elementMap change) point).obj (PowerClassPresheafBaseChange.liftFuture change point).obj
    (PowerClassPresheafBaseChange.future_backward_forward change point) (PowerClassPresheafBaseChange.future_forward_backward change point)
    (fun future => Position domain body label future.2)

theorem branch_target_image (point : Q.Elements) (label : domain.obj ((elementMap change).obj point))
    (branch : TargetBranches change domain body point label) :
    (elementMap change).obj (branchEquiv change domain body point label branch).1.1 = branch.1.1 :=
  PowerClassPresheafBaseChange.liftTarget_image change point branch.1

theorem branch_forward (point : Q.Elements) (label : (sourceDomain change domain).obj point)
    (branch : SourceBranches change domain body point label) :
    (branchEquiv change domain body point label).symm branch =
      ⟨⟨(elementMap change).obj branch.1.1, (elementMap change).map branch.1.2⟩, branch.2⟩ := rfl

noncomputable def pullRawData {target : P.Elements} (tree : RawTree domain body target) :
    (point : Q.Elements) → (elementMap change).obj point = target →
      RawTree (sourceDomain change domain) (sourceBody change domain body) point :=
  RawTree.rec (motive := fun target _ => (point : Q.Elements) → (elementMap change).obj point = target →
      RawTree (sourceDomain change domain) (sourceBody change domain body) point)
    (fun {target} label children earlier point same => by
      cases same
      exact .sup label (fun next arrow branch => earlier ((elementMap change).obj next)
        ((elementMap change).map arrow) branch next rfl)) tree

noncomputable def pullRaw (point : Q.Elements) (tree : RawTree domain body ((elementMap change).obj point)) :
    RawTree (sourceDomain change domain) (sourceBody change domain body) point :=
  pullRawData change domain body tree point rfl

theorem pullRaw_sup (point : Q.Elements) (label : domain.obj ((elementMap change).obj point))
    (children : (target : P.Elements) → (arrow : (elementMap change).obj point ⟶ target) →
      Position domain body label arrow → RawTree domain body target) :
    pullRaw change domain body point (.sup label children) =
      .sup label (fun next arrow branch => pullRaw change domain body next
        (children ((elementMap change).obj next) ((elementMap change).map arrow) branch)) := rfl

noncomputable def pushRaw {point : Q.Elements}
    (tree : RawTree (sourceDomain change domain) (sourceBody change domain body) point) :
    RawTree domain body ((elementMap change).obj point) :=
  RawTree.rec (motive := fun point _ => RawTree domain body ((elementMap change).obj point))
    (fun {point} label _children earlier => .sup label (fun next arrow branch =>
      let lifted := branchEquiv change domain body point label ⟨⟨next, arrow⟩, branch⟩
      cast (congrArg (RawTree domain body) (branch_target_image change domain body point label ⟨⟨next, arrow⟩, branch⟩))
        (earlier lifted.1.1 lifted.1.2 lifted.2))) tree

theorem pushRaw_sup (point : Q.Elements) (label : (sourceDomain change domain).obj point)
    (children : (next : Q.Elements) → (arrow : point ⟶ next) →
      Position (sourceDomain change domain) (sourceBody change domain body) label arrow →
        RawTree (sourceDomain change domain) (sourceBody change domain body) next) :
    pushRaw change domain body (.sup label children) =
      .sup label (fun next arrow branch =>
        let lifted := branchEquiv change domain body point label ⟨⟨next, arrow⟩, branch⟩
        cast (congrArg (RawTree domain body) (branch_target_image change domain body point label ⟨⟨next, arrow⟩, branch⟩))
          (pushRaw change domain body (children lifted.1.1 lifted.1.2 lifted.2))) := rfl

theorem pullRawData_heq {first second : Q.Elements} {X Y : P.Elements}
    (points : first = second) (left : RawTree domain body X) (right : RawTree domain body Y)
    (trees : HEq left right) (atFirst : (elementMap change).obj first = X)
    (atSecond : (elementMap change).obj second = Y) :
    HEq (pullRawData change domain body left first atFirst) (pullRawData change domain body right second atSecond) := by
  cases points
  have targets : X = Y := atFirst.symm.trans atSecond
  cases targets
  cases eq_of_heq trees
  rfl

theorem positionAlong_reindex_heq {X Y Z : Q.Elements} (label : (sourceDomain change domain).obj X)
    (first : X ⟶ Y) (later : Y ⟶ Z)
    (branch : Position (sourceDomain change domain) (sourceBody change domain body) label first) :
    HEq (ContextualWTypes.positionAlong (sourceDomain change domain) (sourceBody change domain body) label first later branch)
      (ContextualWTypes.positionAlong domain body label ((elementMap change).map first) ((elementMap change).map later) branch) :=
  (cast_heq _ _).trans (cast_heq _ _).symm

theorem pullRaw_restrict {X Y : Q.Elements} (arrow : X ⟶ Y)
    (tree : RawTree domain body ((elementMap change).obj X)) :
    pullRaw change domain body Y (ContextualWTypes.restrict domain body ((elementMap change).map arrow) tree) =
      ContextualWTypes.restrict (sourceDomain change domain) (sourceBody change domain body) arrow
        (pullRaw change domain body X tree) := by
  cases tree with
  | sup label children =>
    apply RawTree.sup_eq_of_cast rfl
    intro Z later branch
    apply congrArg (pullRaw change domain body Z)
    exact RawTree.children_eq label children ((elementMap change).map_comp arrow later).symm
      (ContextualWTypes.compositePosition domain body label ((elementMap change).map arrow) ((elementMap change).map later) branch)
      (ContextualWTypes.compositePosition (sourceDomain change domain) (sourceBody change domain body) label arrow later branch)
      ((cast_heq _ _).trans (cast_heq _ _).symm)

theorem pull_push {point : Q.Elements}
    (tree : RawTree (sourceDomain change domain) (sourceBody change domain body) point) :
    pullRaw change domain body point (pushRaw change domain body tree) = tree := by
  induction tree with
  | @sup point label children earlier =>
    rw [pushRaw_sup]
    change RawTree.sup label (fun next arrow position => pullRaw change domain body next
      (cast (congrArg (RawTree domain body) (branch_target_image change domain body point label
        ⟨⟨(elementMap change).obj next, (elementMap change).map arrow⟩, position⟩))
        (pushRaw change domain body
          (children (branchEquiv change domain body point label
            ⟨⟨(elementMap change).obj next, (elementMap change).map arrow⟩, position⟩).1.1
            (branchEquiv change domain body point label
              ⟨⟨(elementMap change).obj next, (elementMap change).map arrow⟩, position⟩).1.2
            (branchEquiv change domain body point label
              ⟨⟨(elementMap change).obj next, (elementMap change).map arrow⟩, position⟩).2)))) = .sup label children
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

theorem push_pull_data {target : P.Elements} (tree : RawTree domain body target) :
    ∀ point : Q.Elements, ∀ atPoint : (elementMap change).obj point = target,
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
          (children ((elementMap change).obj source.1.1) ((elementMap change).map source.1.2) source.2)))) =
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

theorem push_pull (point : Q.Elements) (tree : RawTree domain body ((elementMap change).obj point)) :
    pushRaw change domain body (pullRaw change domain body point tree) = tree :=
  eq_of_heq (push_pull_data change domain body tree point rfl)

noncomputable def rawEquiv (point : Q.Elements) :
    RawTree domain body ((elementMap change).obj point) ≃
      RawTree (sourceDomain change domain) (sourceBody change domain body) point where
  toFun := pullRaw change domain body point
  invFun := pushRaw change domain body
  left_inv := push_pull change domain body point
  right_inv := pull_push change domain body

theorem pushRaw_restrict {X Y : Q.Elements} (arrow : X ⟶ Y)
    (tree : RawTree (sourceDomain change domain) (sourceBody change domain body) X) :
    pushRaw change domain body (ContextualWTypes.restrict (sourceDomain change domain)
      (sourceBody change domain body) arrow tree) =
      ContextualWTypes.restrict domain body ((elementMap change).map arrow) (pushRaw change domain body tree) := by
  apply (rawEquiv change domain body Y).injective
  change pullRaw change domain body Y (pushRaw change domain body _) =
    pullRaw change domain body Y (ContextualWTypes.restrict domain body ((elementMap change).map arrow) _)
  rw [pull_push, pullRaw_restrict, pull_push]

theorem pull_natural_data {target : P.Elements} (tree : RawTree domain body target) :
    ∀ point : Q.Elements, ∀ atPoint : (elementMap change).obj point = target,
      Natural domain body tree →
        Natural (sourceDomain change domain) (sourceBody change domain body)
          (pullRawData change domain body tree point atPoint) := by
  induction tree with
  | @sup target label children earlier =>
    intro point atPoint natural
    cases atPoint
    constructor
    · intro next arrow position
      exact earlier _ _ _ next rfl (natural.1 ((elementMap change).obj next) ((elementMap change).map arrow) position)
    · intro Y Z first later position
      change ContextualWTypes.restrict (sourceDomain change domain) (sourceBody change domain body) later
        (pullRaw change domain body Y (children ((elementMap change).obj Y) ((elementMap change).map first) position)) =
        pullRaw change domain body Z
          (children ((elementMap change).obj Z) ((elementMap change).map (first ≫ later))
            (ContextualWTypes.positionAlong (sourceDomain change domain) (sourceBody change domain body) label first later position))
      rw [← pullRaw_restrict]
      apply congrArg (pullRaw change domain body Z)
      exact (natural.2 _ _ ((elementMap change).map first) ((elementMap change).map later) position).trans
        (RawTree.children_eq label children ((elementMap change).map_comp first later).symm
          (ContextualWTypes.positionAlong domain body label ((elementMap change).map first) ((elementMap change).map later) position)
          (ContextualWTypes.positionAlong (sourceDomain change domain) (sourceBody change domain body) label first later position)
          (positionAlong_reindex_heq change domain body label first later position).symm)

theorem pull_natural (point : Q.Elements) (tree : RawTree domain body ((elementMap change).obj point))
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

theorem branch_arrow_image (point : Q.Elements) (label : domain.obj ((elementMap change).obj point))
    (branch : TargetBranches change domain body point label) :
    HEq ((elementMap change).map (branchEquiv change domain body point label branch).1.2) branch.1.2 :=
  Cat.dependentValue_heq (fun future : Future.Objects ((elementMap change).obj point) => future.2)
    (PowerClassPresheafBaseChange.future_forward_backward change point branch.1)

theorem push_natural {point : Q.Elements}
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
      let sourceLater := ((PowerClassPresheafBaseChange.liftFuture change point).map step).1
      have sourceTriangle : source.1.2 ≫ sourceLater = ending.1.2 :=
        ((PowerClassPresheafBaseChange.liftFuture change point).map step).2
      have arrowImage : HEq ((elementMap change).map sourceLater) later :=
        PowerClassPresheafBaseChange.liftFuture_map_image change step
      have positionImage := (positionAlong_reindex_heq change domain body label source.1.2 sourceLater source.2).trans
        (positionAlong_worlds_heq domain body label
          (branch_target_image change domain body point label original)
          (branch_target_image change domain body point label last)
          ((elementMap change).map source.1.2) first ((elementMap change).map sourceLater) later
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
        later ((elementMap change).map sourceLater) arrowImage.symm
        (cast (congrArg (RawTree domain body) (branch_target_image change domain body point label original))
          (pushRaw change domain body (children source.1.1 source.1.2 source.2)))
        (pushRaw change domain body (children source.1.1 source.1.2 source.2)) (cast_heq _ _)
      exact eq_of_heq (restrictImage.trans
        ((heq_of_eq (pushRaw_restrict change domain body sourceLater (children source.1.1 source.1.2 source.2)).symm).trans
          ((heq_of_eq (congrArg (pushRaw change domain body)
            ((natural.2 _ _ source.1.2 sourceLater source.2).trans childrenSame))).trans (cast_heq _ _).symm)))

noncomputable def naturalEquiv (point : Q.Elements) :
    NaturalTree domain body ((elementMap change).obj point) ≃
      NaturalTree (sourceDomain change domain) (sourceBody change domain body) point where
  toFun tree := ⟨pullRaw change domain body point tree.val, pull_natural change domain body point tree.val tree.property⟩
  invFun tree := ⟨pushRaw change domain body tree.val, push_natural change domain body tree.val tree.property⟩
  left_inv tree := Subtype.ext (push_pull change domain body point tree.val)
  right_inv tree := Subtype.ext (pull_push change domain body tree.val)

noncomputable def wBaseChange :
    NatTrans (PowerClassPresheafProducts.reindex change (ContextualWTypes.family domain body))
      (ContextualWTypes.family (sourceDomain change domain) (sourceBody change domain body)) where
  app point := TypeCat.ofHom (naturalEquiv change domain body point)
  naturality X Y arrow := by
    apply ConcreteCategory.hom_ext
    intro tree
    exact Subtype.ext (pullRaw_restrict change domain body arrow tree.val)

noncomputable def wBaseChangeInverse :
    NatTrans (ContextualWTypes.family (sourceDomain change domain) (sourceBody change domain body))
      (PowerClassPresheafProducts.reindex change (ContextualWTypes.family domain body)) :=
  PowerClassPresheafBaseChange.Nat.inverse (wBaseChange change domain body)
    (naturalEquiv change domain body) (fun _ _ => rfl)

theorem wBaseChange_left :
    Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose
      (wBaseChange change domain body) (wBaseChangeInverse change domain body) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity
        (PowerClassPresheafProducts.reindex change (ContextualWTypes.family domain body)) :=
  PowerClassPresheafBaseChange.Nat.inverse_left (wBaseChange change domain body)
    (naturalEquiv change domain body) (fun _ _ => rfl)

theorem wBaseChange_right :
    Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose
      (wBaseChangeInverse change domain body) (wBaseChange change domain body) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity
        (ContextualWTypes.family (sourceDomain change domain) (sourceBody change domain body)) :=
  PowerClassPresheafBaseChange.Nat.inverse_right (wBaseChange change domain body)
    (naturalEquiv change domain body) (fun _ _ => rfl)

variable (target : P.Elements ⥤ Type u)

def pullBranches (point : Q.Elements) (label : domain.obj ((elementMap change).obj point))
    (branches : ContextualWTypes.Branches domain body target label) :
    ContextualWTypes.Branches (sourceDomain change domain) (sourceBody change domain body)
      (PowerClassPresheafProducts.reindex change target) label where
  app next arrow position := branches.app ((elementMap change).obj next) ((elementMap change).map arrow) position
  naturality _Y _Z first later position :=
    (branches.naturality _ _ ((elementMap change).map first) ((elementMap change).map later) position).trans
      (branches.app_eq ((elementMap change).map_comp first later).symm
        (ContextualWTypes.positionAlong domain body label ((elementMap change).map first) ((elementMap change).map later) position)
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

def pushBranches (point : Q.Elements) (label : (sourceDomain change domain).obj point)
    (branches : ContextualWTypes.Branches (sourceDomain change domain) (sourceBody change domain body)
      (PowerClassPresheafProducts.reindex change target) label) :
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
    let sourceLater := ((PowerClassPresheafBaseChange.liftFuture change point).map step).1
    have sourceTriangle : source.1.2 ≫ sourceLater = ending.1.2 :=
      ((PowerClassPresheafBaseChange.liftFuture change point).map step).2
    have arrowImage : HEq ((elementMap change).map sourceLater) later :=
      PowerClassPresheafBaseChange.liftFuture_map_image change step
    have positionImage := (positionAlong_reindex_heq change domain body label source.1.2 sourceLater source.2).trans
      (positionAlong_worlds_heq domain body label
        (branch_target_image change domain body point label original)
        (branch_target_image change domain body point label last)
        ((elementMap change).map source.1.2) first ((elementMap change).map sourceLater) later
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
      later ((elementMap change).map sourceLater) arrowImage.symm
      (cast (congrArg target.obj (branch_target_image change domain body point label original))
        (branches.app source.1.1 source.1.2 source.2))
      (branches.app source.1.1 source.1.2 source.2) (cast_heq _ _)
    exact eq_of_heq (mapped.trans ((heq_of_eq
      ((branches.naturality _ _ source.1.2 sourceLater source.2).trans childrenSame)).trans (cast_heq _ _).symm))

theorem pull_pushBranches (point : Q.Elements) (label : (sourceDomain change domain).obj point)
    (branches : ContextualWTypes.Branches (sourceDomain change domain) (sourceBody change domain body)
      (PowerClassPresheafProducts.reindex change target) label) :
    pullBranches change domain body target point label (pushBranches change domain body target point label branches) = branches := by
  apply ContextualWTypes.Branches.ext
  intro next arrow position
  let original : SourceBranches change domain body point label := ⟨⟨next, arrow⟩, position⟩
  have same := (branchEquiv change domain body point label).apply_symm_apply original
  exact eq_of_heq ((cast_heq _ _).trans (Cat.dependentValue_heq
    (fun branch : SourceBranches change domain body point label => branches.app branch.1.1 branch.1.2 branch.2) same))

theorem push_pullBranches (point : Q.Elements) (label : domain.obj ((elementMap change).obj point))
    (branches : ContextualWTypes.Branches domain body target label) :
    pushBranches change domain body target point label (pullBranches change domain body target point label branches) = branches := by
  apply ContextualWTypes.Branches.ext
  intro next arrow position
  let original : TargetBranches change domain body point label := ⟨⟨next, arrow⟩, position⟩
  have same := (branchEquiv change domain body point label).symm_apply_apply original
  exact eq_of_heq ((cast_heq _ _).trans (Cat.dependentValue_heq
    (fun branch : TargetBranches change domain body point label => branches.app branch.1.1 branch.1.2 branch.2) same))

def branchesEquiv (point : Q.Elements) (label : domain.obj ((elementMap change).obj point)) :
    ContextualWTypes.Branches domain body target label ≃
      ContextualWTypes.Branches (sourceDomain change domain) (sourceBody change domain body)
        (PowerClassPresheafProducts.reindex change target) label where
  toFun := pullBranches change domain body target point label
  invFun := pushBranches change domain body target point label
  left_inv := push_pullBranches change domain body target point label
  right_inv := pull_pushBranches change domain body target point label

theorem pullBranches_restrict {X Y : Q.Elements} (arrow : X ⟶ Y)
    (label : domain.obj ((elementMap change).obj X)) (branches : ContextualWTypes.Branches domain body target label) :
    pullBranches change domain body target Y ((sourceDomain change domain).map arrow label)
      (branches.restrict ((elementMap change).map arrow)) =
      (pullBranches change domain body target X label branches).restrict arrow := by
  apply ContextualWTypes.Branches.ext
  intro Z later position
  exact branches.app_eq ((elementMap change).map_comp arrow later).symm
    (ContextualWTypes.compositePosition domain body label ((elementMap change).map arrow) ((elementMap change).map later) position)
    (ContextualWTypes.compositePosition (sourceDomain change domain) (sourceBody change domain body) label arrow later position)
    ((cast_heq _ _).trans (cast_heq _ _).symm)

theorem pushBranches_restrict {X Y : Q.Elements} (arrow : X ⟶ Y)
    (label : (sourceDomain change domain).obj X)
    (branches : ContextualWTypes.Branches (sourceDomain change domain) (sourceBody change domain body)
      (PowerClassPresheafProducts.reindex change target) label) :
    pushBranches change domain body target Y ((sourceDomain change domain).map arrow label) (branches.restrict arrow) =
      (pushBranches change domain body target X label branches).restrict ((elementMap change).map arrow) := by
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
      (PowerClassPresheafProducts.reindex change target) where
  make point label branches := algebra.make ((elementMap change).obj point) label
    (pushBranches change domain body target point label branches)
  naturality X Y arrow label branches :=
    (algebra.naturality _ _ ((elementMap change).map arrow) label
      (pushBranches change domain body target X label branches)).trans
        (congrArg (algebra.make ((elementMap change).obj Y) ((sourceDomain change domain).map arrow label))
          (pushBranches_restrict change domain body target arrow label branches).symm)

theorem pull_evaluates_data (algebra : ContextualWTypes.Algebra domain body target)
    {X : P.Elements} {tree : RawTree domain body X} {value : target.obj X}
    (evaluates : ContextualWTypes.Evaluates domain body algebra tree value) :
    ∀ point : Q.Elements, ∀ atPoint : (elementMap change).obj point = X,
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
        (children ((elementMap change).obj next) ((elementMap change).map arrow) position)))
      (algebra.make ((elementMap change).obj point) label branches)
    have smaller : ∀ next arrow position,
        ContextualWTypes.Evaluates (sourceDomain change domain) (sourceBody change domain body)
          (pullAlgebra change domain body target algebra)
          (pullRaw change domain body next (children ((elementMap change).obj next) ((elementMap change).map arrow) position))
          ((pullBranches change domain body target point label branches).app next arrow position) := by
      intro next arrow position
      exact earlier _ _ _ next rfl
    have constructed := ContextualWTypes.Evaluates.sup
      (algebra := pullAlgebra change domain body target algebra) label _
      (pullBranches change domain body target point label branches) smaller
    have computation : (pullAlgebra change domain body target algebra).make point label
        (pullBranches change domain body target point label branches) =
        algebra.make ((elementMap change).obj point) label branches :=
      congrArg (algebra.make ((elementMap change).obj point) label)
        (push_pullBranches change domain body target point label branches)
    rw [computation] at constructed
    exact constructed

theorem fold_baseChange (algebra : ContextualWTypes.Algebra domain body target) (point : Q.Elements)
    (tree : NaturalTree domain body ((elementMap change).obj point)) :
    ContextualWTypes.fold (sourceDomain change domain) (sourceBody change domain body)
      (pullAlgebra change domain body target algebra) (naturalEquiv change domain body point tree) =
        ContextualWTypes.fold domain body algebra tree :=
  ContextualWTypes.evaluates_unique _ _ _
    (ContextualWTypes.fold_evaluates _ _ _ _)
    (pull_evaluates_data change domain body target algebra
      (ContextualWTypes.fold_evaluates domain body algebra tree) point rfl)

noncomputable def pullTreeBranches (point : Q.Elements) (label : domain.obj ((elementMap change).obj point))
    (branches : ContextualWTypes.Branches domain body (ContextualWTypes.family domain body) label) :
    ContextualWTypes.Branches (sourceDomain change domain) (sourceBody change domain body)
      (ContextualWTypes.family (sourceDomain change domain) (sourceBody change domain body)) label :=
  (pullBranches change domain body (ContextualWTypes.family domain body) point label branches).map
    (wBaseChange change domain body)

theorem constructor_baseChange (point : Q.Elements) (label : domain.obj ((elementMap change).obj point))
    (branches : ContextualWTypes.Branches domain body (ContextualWTypes.family domain body) label) :
    naturalEquiv change domain body point
      ((ContextualWTypes.treeAlgebra domain body).make ((elementMap change).obj point) label branches) =
    (ContextualWTypes.treeAlgebra (sourceDomain change domain) (sourceBody change domain body)).make point label
      (pullTreeBranches change domain body point label branches) := Subtype.ext rfl

theorem pullRaw_identity (point : P.Elements) (tree : RawTree domain body point) :
    pullRaw (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity P) domain body point tree = tree := by
  induction tree with
  | @sup point label children earlier =>
    change RawTree.sup label (fun next arrow position =>
      pullRaw (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity P) domain body next (children next arrow position)) =
      .sup label children
    apply RawTree.sup_eq_of_cast rfl
    exact earlier

theorem naturalEquiv_identity (point : P.Elements) (tree : NaturalTree domain body point) :
    naturalEquiv (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity P) domain body point tree = tree :=
  Subtype.ext (pullRaw_identity domain body point tree.val)

theorem wBaseChange_identity :
    wBaseChange (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity P) domain body =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity (ContextualWTypes.family domain body) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro tree
  exact naturalEquiv_identity domain body point tree

variable {R : Cᵒᵖ ⥤ Type u} (earlier : NatTrans R Q)

theorem pullRaw_comp_data {X : P.Elements} (tree : RawTree domain body X) :
    ∀ point : R.Elements, ∀ atPoint :
      (elementMap (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose earlier change)).obj point = X,
      pullRawData (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose earlier change) domain body tree point atPoint =
        pullRaw earlier (sourceDomain change domain) (sourceBody change domain body) point
          (pullRawData change domain body tree ((elementMap earlier).obj point) atPoint) := by
  induction tree with
  | @sup X label children smaller =>
    intro point atPoint
    cases atPoint
    change RawTree.sup (shape := sourceDomain
      (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose earlier change) domain)
      (position := sourceBody (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose earlier change) domain body) label (fun (next : R.Elements) arrow position =>
      pullRaw (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose earlier change) domain body next
        (children ((elementMap change).obj ((elementMap earlier).obj next))
          ((elementMap change).map ((elementMap earlier).map arrow)) position)) =
      RawTree.sup (shape := sourceDomain earlier (sourceDomain change domain))
        (position := sourceBody earlier (sourceDomain change domain) (sourceBody change domain body)) label (fun (next : R.Elements) arrow position =>
        pullRaw earlier (sourceDomain change domain) (sourceBody change domain body) next
          (pullRaw change domain body ((elementMap earlier).obj next)
            (children ((elementMap change).obj ((elementMap earlier).obj next))
              ((elementMap change).map ((elementMap earlier).map arrow)) position)))
    apply RawTree.sup_eq_of_cast rfl
    intro next arrow position
    exact smaller _ _ _ next rfl

theorem pullRaw_comp (point : R.Elements)
    (tree : RawTree domain body ((elementMap change).obj ((elementMap earlier).obj point))) :
    pullRaw (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose earlier change) domain body point tree =
      pullRaw earlier (sourceDomain change domain) (sourceBody change domain body) point
        (pullRaw change domain body ((elementMap earlier).obj point) tree) :=
  pullRaw_comp_data change domain body earlier tree point rfl

theorem naturalEquiv_comp (point : R.Elements)
    (tree : NaturalTree domain body ((elementMap change).obj ((elementMap earlier).obj point))) :
    naturalEquiv (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose earlier change) domain body point tree =
      naturalEquiv earlier (sourceDomain change domain) (sourceBody change domain body) point
        (naturalEquiv change domain body ((elementMap earlier).obj point) tree) :=
  Subtype.ext (pullRaw_comp change domain body earlier point tree.val)

def reindexTransformation {first second : P.Elements ⥤ Type u} (operation : NatTrans first second) :
    NatTrans (PowerClassPresheafProducts.reindex change first) (PowerClassPresheafProducts.reindex change second) where
  app point := operation.app ((elementMap change).obj point)
  naturality _X _Y arrow := operation.naturality ((elementMap change).map arrow)

theorem wBaseChange_comp :
    wBaseChange (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose earlier change) domain body =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose
        (reindexTransformation earlier (wBaseChange change domain body))
        (wBaseChange earlier (sourceDomain change domain) (sourceBody change domain body)) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro tree
  exact naturalEquiv_comp change domain body earlier point tree

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWBaseChange
