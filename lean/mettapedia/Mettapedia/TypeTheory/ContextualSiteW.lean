import Mettapedia.TypeTheory.ContextualFutureSiteW

/-!
# Direct full contextual W transport for small future categories

This removes the auxiliary parameter comprehension from site transport.
The shapes and dependent positions of an arbitrary small category are
raised directly; indexed tree recursion retains every actual future arrow
and position, with proved naturality and both inverse laws. Complete future
cones instantiate this construction independently of wider parameters.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSiteW

open CategoryTheory MaterialSets.Hypersets
open Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWTypes (RawTree Natural NaturalTree Position)

universe u
variable {D : Type u} [Category.{u} D]

def shapeUp (shape : D ⥤ Type u) : PresheafSiteLift.Site D ⥤ Type (u+1) where
  obj point := ULift.{u+1,u} (shape.obj point.down)
  map step := TypeCat.ofHom fun code => ULift.up (shape.map step.down code.down)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro code
    exact ULift.ext _ _ (shape.map_id_apply point.down code.down)
  map_comp first later := by
    apply ConcreteCategory.hom_ext
    intro code
    exact ULift.ext _ _ (shape.map_comp_apply first.down later.down code.down)

def shapeElementsDown (shape : D ⥤ Type u) : (shapeUp shape).Elements ⥤ shape.Elements where
  obj point := ⟨point.1.down, point.2.down⟩
  map step := ⟨step.1.down, congrArg ULift.down step.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def positionUp (shape : D ⥤ Type u) (position : shape.Elements ⥤ Type u) :
    (shapeUp shape).Elements ⥤ Type (u+1) where
  obj point := ULift.{u+1,u} (position.obj ((shapeElementsDown shape).obj point))
  map step := TypeCat.ofHom fun code => ULift.up (position.map ((shapeElementsDown shape).map step) code.down)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro code
    exact ULift.ext _ _ (position.map_id_apply ((shapeElementsDown shape).obj point) code.down)
  map_comp first later := by
    apply ConcreteCategory.hom_ext
    intro code
    exact ULift.ext _ _ (position.map_comp_apply ((shapeElementsDown shape).map first) ((shapeElementsDown shape).map later) code.down)

variable (shape : D ⥤ Type u) (position : shape.Elements ⥤ Type u)

abbrev upperShape := shapeUp shape
abbrev upperPosition := positionUp shape position

private theorem up_heq {A B : Type u} {a : A} {b : B} (same : HEq a b) :
    HEq (ULift.up a : ULift.{u + 1, u} A) (ULift.up b : ULift.{u + 1, u} B) := by
  cases same
  rfl

private theorem down_heq {A : Type u} {a b : ULift.{u + 1, u} A}
    (same : HEq a b) : HEq a.down b.down := by
  exact heq_of_eq (congrArg ULift.down (eq_of_heq same))

noncomputable def lowerRaw {point : PresheafSiteLift.Site D}
    (tree : RawTree (upperShape shape) (upperPosition shape position) point) :
    RawTree shape position (PresheafSiteLift.Site.downFunctor.obj point) :=
  RawTree.rec (shape := upperShape shape) (position := upperPosition shape position)
    (motive := fun point _ => RawTree shape position (PresheafSiteLift.Site.downFunctor.obj point))
    (fun {_point} label _children earlier => .sup label.down (fun next arrow branch =>
      earlier (PresheafSiteLift.Site.upFunctor.obj next) (PresheafSiteLift.Site.upFunctor.map arrow) (ULift.up branch))) tree

noncomputable def raiseRawData {target : D} (tree : RawTree shape position target) :
    (point : PresheafSiteLift.Site D) → PresheafSiteLift.Site.downFunctor.obj point = target →
      RawTree (upperShape shape) (upperPosition shape position) point :=
  RawTree.rec (motive := fun target _ =>
    (point : PresheafSiteLift.Site D) → PresheafSiteLift.Site.downFunctor.obj point = target →
      RawTree (upperShape shape) (upperPosition shape position) point)
    (fun {target} label _children earlier point same => by
      cases same
      exact .sup (ULift.up label) (fun next arrow branch => earlier
        (PresheafSiteLift.Site.downFunctor.obj next) (PresheafSiteLift.Site.downFunctor.map arrow)
        branch.down next rfl)) tree

noncomputable def raiseRaw (point : PresheafSiteLift.Site D)
    (tree : RawTree shape position (PresheafSiteLift.Site.downFunctor.obj point)) :
    RawTree (upperShape shape) (upperPosition shape position) point := raiseRawData shape position tree point rfl

theorem lower_sup (point : PresheafSiteLift.Site D) (label : (upperShape shape).obj point)
    (children : (next : PresheafSiteLift.Site D) → (arrow : point ⟶ next) →
      Position (upperShape shape) (upperPosition shape position) label arrow →
        RawTree (upperShape shape) (upperPosition shape position) next) :
    lowerRaw shape position (.sup label children) = .sup label.down (fun next arrow branch =>
      lowerRaw shape position (children (PresheafSiteLift.Site.upFunctor.obj next)
        (PresheafSiteLift.Site.upFunctor.map arrow) (ULift.up branch))) := rfl

theorem raise_sup (point : PresheafSiteLift.Site D)
    (label : shape.obj (PresheafSiteLift.Site.downFunctor.obj point))
    (children : (next : D) → (arrow : PresheafSiteLift.Site.downFunctor.obj point ⟶ next) →
      Position shape position label arrow → RawTree shape position next) :
    raiseRaw shape position point (.sup label children) = .sup (ULift.up label) (fun next arrow branch =>
      raiseRaw shape position next (children (PresheafSiteLift.Site.downFunctor.obj next)
        (PresheafSiteLift.Site.downFunctor.map arrow) branch.down)) := rfl

theorem raise_lower {point : PresheafSiteLift.Site D}
    (tree : RawTree (upperShape shape) (upperPosition shape position) point) :
    raiseRaw shape position point (lowerRaw shape position tree) = tree := by
  induction tree with
  | @sup point label children earlier =>
    change RawTree.sup label (fun next arrow branch =>
      raiseRaw shape position next (lowerRaw shape position (children next arrow branch))) = RawTree.sup label children
    apply RawTree.sup_eq_of_cast rfl
    intro next arrow branch
    exact earlier next arrow branch

theorem lower_raise (point : PresheafSiteLift.Site D)
    (tree : RawTree shape position (PresheafSiteLift.Site.downFunctor.obj point)) :
    lowerRaw shape position (raiseRaw shape position point tree) = tree := by
  suffices general : ∀ {target} (tree : RawTree shape position target)
      (point : PresheafSiteLift.Site D) (same : PresheafSiteLift.Site.downFunctor.obj point = target),
      lowerRaw shape position (raiseRawData shape position tree point same) =
        cast (congrArg (RawTree shape position) same.symm) tree by
    exact general tree point rfl
  intro target tree
  induction tree with
  | @sup target label children earlier =>
    intro point same
    cases same
    change RawTree.sup label (fun next arrow branch =>
      lowerRaw shape position (raiseRawData shape position (children next arrow branch)
        (PresheafSiteLift.Site.upFunctor.obj next) rfl)) = RawTree.sup label children
    apply RawTree.sup_eq_of_cast rfl
    intro next arrow branch
    exact earlier next arrow branch (PresheafSiteLift.Site.upFunctor.obj next) rfl

noncomputable def rawEquiv (point : PresheafSiteLift.Site D) :
    RawTree (upperShape shape) (upperPosition shape position) point ≃
      RawTree shape position (PresheafSiteLift.Site.downFunctor.obj point) where
  toFun := lowerRaw shape position
  invFun := raiseRaw shape position point
  left_inv := raise_lower shape position
  right_inv := lower_raise shape position point

theorem composite_position_up {X Y Z : D} (label : shape.obj X) (first : X ⟶ Y) (later : Y ⟶ Z)
    (branch : Position shape position (shape.map first label) later) :
    HEq (ContextualWTypes.compositePosition (upperShape shape) (upperPosition shape position)
      (X := PresheafSiteLift.Site.upFunctor.obj X) (Y := PresheafSiteLift.Site.upFunctor.obj Y)
      (Z := PresheafSiteLift.Site.upFunctor.obj Z)
      (ULift.up label) (PresheafSiteLift.Site.upFunctor.map first) (PresheafSiteLift.Site.upFunctor.map later)
      (ULift.up branch))
      (ULift.up (ContextualWTypes.compositePosition shape position label first later branch) :
        ULift.{u + 1, u} (Position shape position label (first ≫ later))) :=
  (cast_heq _ _).trans (up_heq (cast_heq _ _)).symm

theorem position_along_up {X Y Z : D} (label : shape.obj X) (first : X ⟶ Y) (later : Y ⟶ Z)
    (branch : Position shape position label first) :
    HEq (ContextualWTypes.positionAlong (upperShape shape) (upperPosition shape position)
      (X := PresheafSiteLift.Site.upFunctor.obj X) (Y := PresheafSiteLift.Site.upFunctor.obj Y)
      (Z := PresheafSiteLift.Site.upFunctor.obj Z)
      (ULift.up label) (PresheafSiteLift.Site.upFunctor.map first) (PresheafSiteLift.Site.upFunctor.map later)
      (ULift.up branch))
      (ULift.up (ContextualWTypes.positionAlong shape position label first later branch) :
        ULift.{u + 1, u} (Position shape position label (first ≫ later))) :=
  (cast_heq _ _).trans (up_heq (cast_heq _ _)).symm

theorem lower_restrict {X Y : PresheafSiteLift.Site D} (arrow : X ⟶ Y)
    (tree : RawTree (upperShape shape) (upperPosition shape position) X) :
    lowerRaw shape position (ContextualWTypes.restrict (upperShape shape) (upperPosition shape position) arrow tree) =
      ContextualWTypes.restrict shape position (PresheafSiteLift.Site.downFunctor.map arrow)
        (lowerRaw shape position tree) := by
  cases tree with
  | sup label children =>
    apply RawTree.sup_eq_of_cast rfl
    intro next later branch
    apply congrArg (lowerRaw shape position)
    exact RawTree.children_eq label children rfl
      (ContextualWTypes.compositePosition (upperShape shape) (upperPosition shape position) label arrow
        (PresheafSiteLift.Site.upFunctor.map later) (ULift.up branch))
      (ULift.up (ContextualWTypes.compositePosition shape position label.down
        (PresheafSiteLift.Site.downFunctor.map arrow) later branch))
      (composite_position_up shape position label.down (PresheafSiteLift.Site.downFunctor.map arrow) later branch)

theorem raise_restrict {X Y : PresheafSiteLift.Site D} (arrow : X ⟶ Y)
    (tree : RawTree shape position (PresheafSiteLift.Site.downFunctor.obj X)) :
    raiseRaw shape position Y (ContextualWTypes.restrict shape position (PresheafSiteLift.Site.downFunctor.map arrow) tree) =
      ContextualWTypes.restrict (upperShape shape) (upperPosition shape position) arrow (raiseRaw shape position X tree) := by
  apply (rawEquiv shape position Y).injective
  exact (lower_raise shape position Y _).trans
    ((congrArg (ContextualWTypes.restrict shape position (PresheafSiteLift.Site.downFunctor.map arrow))
      (lower_raise shape position X tree)).symm.trans (lower_restrict shape position arrow _).symm)

theorem lower_natural {point : PresheafSiteLift.Site D}
    (tree : RawTree (upperShape shape) (upperPosition shape position) point)
    (natural : Natural (upperShape shape) (upperPosition shape position) tree) :
    Natural shape position (lowerRaw shape position tree) := by
  induction tree with
  | @sup point label children earlier =>
    constructor
    · intro next arrow branch
      exact earlier (PresheafSiteLift.Site.upFunctor.obj next) (PresheafSiteLift.Site.upFunctor.map arrow)
        (ULift.up branch) (natural.1 _ _ _)
    · intro next last first later branch
      refine (lower_restrict shape position (PresheafSiteLift.Site.upFunctor.map later) _).symm.trans ?_
      refine (congrArg (lowerRaw shape position) (natural.2 _ _
        (PresheafSiteLift.Site.upFunctor.map first) (PresheafSiteLift.Site.upFunctor.map later) (ULift.up branch))).trans ?_
      apply congrArg (lowerRaw shape position)
      exact RawTree.children_eq label children rfl _ _
        (position_along_up shape position label.down first later branch)

theorem raise_natural (point : PresheafSiteLift.Site D)
    (tree : RawTree shape position (PresheafSiteLift.Site.downFunctor.obj point))
    (natural : Natural shape position tree) :
    Natural (upperShape shape) (upperPosition shape position) (raiseRaw shape position point tree) := by
  suffices general : ∀ {target} (tree : RawTree shape position target), Natural shape position tree →
      ∀ (point : PresheafSiteLift.Site D) (same : PresheafSiteLift.Site.downFunctor.obj point = target),
      Natural (upperShape shape) (upperPosition shape position) (raiseRawData shape position tree point same) by
    exact general tree natural point rfl
  intro target tree
  induction tree with
  | @sup target label children earlier =>
    intro natural point same
    cases same
    constructor
    · intro next arrow branch
      exact earlier (PresheafSiteLift.Site.downFunctor.obj next) (PresheafSiteLift.Site.downFunctor.map arrow)
        branch.down (natural.1 _ _ _) next rfl
    · intro next last first later branch
      refine (raise_restrict shape position later _).symm.trans ?_
      refine (congrArg (raiseRaw shape position last) (natural.2 _ _
        (PresheafSiteLift.Site.downFunctor.map first) (PresheafSiteLift.Site.downFunctor.map later) branch.down)).trans ?_
      apply congrArg (raiseRaw shape position last)
      exact RawTree.children_eq label children rfl _ _
        (down_heq (position_along_up shape position label (PresheafSiteLift.Site.downFunctor.map first)
          (PresheafSiteLift.Site.downFunctor.map later) branch.down)).symm

noncomputable def lowerNatural {point : PresheafSiteLift.Site D}
    (tree : NaturalTree (upperShape shape) (upperPosition shape position) point) :
    NaturalTree shape position (PresheafSiteLift.Site.downFunctor.obj point) :=
  ⟨lowerRaw shape position tree.val, lower_natural shape position tree.val tree.property⟩

noncomputable def raiseNatural (point : PresheafSiteLift.Site D)
    (tree : NaturalTree shape position (PresheafSiteLift.Site.downFunctor.obj point)) :
    NaturalTree (upperShape shape) (upperPosition shape position) point :=
  ⟨raiseRaw shape position point tree.val, raise_natural shape position point tree.val tree.property⟩

noncomputable def naturalEquiv (point : PresheafSiteLift.Site D) :
    NaturalTree (upperShape shape) (upperPosition shape position) point ≃
      NaturalTree shape position (PresheafSiteLift.Site.downFunctor.obj point) where
  toFun := lowerNatural shape position
  invFun := raiseNatural shape position point
  left_inv tree := Subtype.ext (raise_lower shape position tree.val)
  right_inv tree := Subtype.ext (lower_raise shape position point tree.val)

noncomputable def comparison : NatTrans (ContextualWTypes.family (upperShape shape) (upperPosition shape position))
    (shapeUp (ContextualWTypes.family shape position)) where
  app point := TypeCat.ofHom fun tree => ULift.up (lowerNatural shape position tree)
  naturality {X Y} arrow := by
    apply ConcreteCategory.hom_ext
    intro tree
    exact congrArg ULift.up (Subtype.ext (lower_restrict shape position arrow tree.val))

noncomputable def inverse : NatTrans (shapeUp (ContextualWTypes.family shape position))
    (ContextualWTypes.family (upperShape shape) (upperPosition shape position)) where
  app point := TypeCat.ofHom fun tree => raiseNatural shape position point tree.down
  naturality {X Y} arrow := by
    apply ConcreteCategory.hom_ext
    intro tree
    exact Subtype.ext (raise_restrict shape position arrow tree.down.val)

theorem comparison_left : Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose
    (comparison shape position) (inverse shape position) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity _ := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro tree
  exact Subtype.ext (raise_lower shape position tree.val)

theorem comparison_right : Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose
    (inverse shape position) (comparison shape position) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity _ := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro tree
  exact congrArg ULift.up (Subtype.ext (lower_raise shape position point tree.down.val))

end Mettapedia.TypeTheory.ContextualSiteW
