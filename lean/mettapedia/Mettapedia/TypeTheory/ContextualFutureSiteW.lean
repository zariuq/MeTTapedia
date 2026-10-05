import Mettapedia.TypeTheory.ContextualFutureSiteLift
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWTypes

/-!
# Constructed contextual W transport on covariant successor sites

This transports the full indexed raw tree and its hereditary naturality
through the actual retained-parameter site maps. Every future world,
actual arrow and dependent position has its explicitly constructed inverse.
The structural recursion extends the opposite-site comparison to the
covariant site used by the actual larger material model.

The local category and signature are small at the original bound. Applying
this module to complete future cones keeps an arbitrary wider external
parameter outside the local tree carrier. It does not replace contextual
W by pointwise well-founded trees or infer a model universe enclosure.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualFutureSiteW

open CategoryTheory
open MaterialSets.Hypersets
open Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWTypes (RawTree Natural NaturalTree Position)

universe u
variable {D : Type u} [Category.{u} D]
variable (P : D ⥤ Type u) (shape : P.Elements ⥤ Type u) (position : shape.Elements ⥤ Type u)

abbrev upperShape := ContextualFutureSiteLift.family P shape
abbrev upperPosition := ContextualFutureSiteLift.body P shape position

private theorem up_heq {A B : Type u} {a : A} {b : B} (same : HEq a b) :
    HEq (ULift.up a : ULift.{u + 1, u} A) (ULift.up b : ULift.{u + 1, u} B) := by
  cases same
  rfl

private theorem down_heq {A : Type u} {a b : ULift.{u + 1, u} A}
    (same : HEq a b) : HEq a.down b.down := by
  exact heq_of_eq (congrArg ULift.down (eq_of_heq same))

noncomputable def lowerRaw {point : (ContextualFutureSiteLift.base P).Elements}
    (tree : RawTree (upperShape P shape) (upperPosition P shape position) point) :
    RawTree shape position ((ContextualFutureSiteLift.elementsDown P).obj point) :=
  RawTree.rec (shape := upperShape P shape) (position := upperPosition P shape position)
    (motive := fun point _ => RawTree shape position ((ContextualFutureSiteLift.elementsDown P).obj point))
    (fun {_point} label _children earlier => .sup label.down (fun next arrow branch =>
      earlier ((ContextualFutureSiteLift.elementsUp P).obj next) ((ContextualFutureSiteLift.elementsUp P).map arrow) (ULift.up branch))) tree

noncomputable def raiseRawData {target : P.Elements} (tree : RawTree shape position target) :
    (point : (ContextualFutureSiteLift.base P).Elements) → (ContextualFutureSiteLift.elementsDown P).obj point = target →
      RawTree (upperShape P shape) (upperPosition P shape position) point :=
  RawTree.rec (motive := fun target _ =>
    (point : (ContextualFutureSiteLift.base P).Elements) → (ContextualFutureSiteLift.elementsDown P).obj point = target →
      RawTree (upperShape P shape) (upperPosition P shape position) point)
    (fun {target} label _children earlier point same => by
      cases same
      exact .sup (ULift.up label) (fun next arrow branch => earlier
        ((ContextualFutureSiteLift.elementsDown P).obj next) ((ContextualFutureSiteLift.elementsDown P).map arrow)
        branch.down next rfl)) tree

noncomputable def raiseRaw (point : (ContextualFutureSiteLift.base P).Elements)
    (tree : RawTree shape position ((ContextualFutureSiteLift.elementsDown P).obj point)) :
    RawTree (upperShape P shape) (upperPosition P shape position) point := raiseRawData P shape position tree point rfl

theorem lower_sup (point : (ContextualFutureSiteLift.base P).Elements) (label : (upperShape P shape).obj point)
    (children : (next : (ContextualFutureSiteLift.base P).Elements) → (arrow : point ⟶ next) →
      Position (upperShape P shape) (upperPosition P shape position) label arrow →
        RawTree (upperShape P shape) (upperPosition P shape position) next) :
    lowerRaw P shape position (.sup label children) = .sup label.down (fun next arrow branch =>
      lowerRaw P shape position (children ((ContextualFutureSiteLift.elementsUp P).obj next)
        ((ContextualFutureSiteLift.elementsUp P).map arrow) (ULift.up branch))) := rfl

theorem raise_sup (point : (ContextualFutureSiteLift.base P).Elements)
    (label : shape.obj ((ContextualFutureSiteLift.elementsDown P).obj point))
    (children : (next : P.Elements) → (arrow : (ContextualFutureSiteLift.elementsDown P).obj point ⟶ next) →
      Position shape position label arrow → RawTree shape position next) :
    raiseRaw P shape position point (.sup label children) = .sup (ULift.up label) (fun next arrow branch =>
      raiseRaw P shape position next (children ((ContextualFutureSiteLift.elementsDown P).obj next)
        ((ContextualFutureSiteLift.elementsDown P).map arrow) branch.down)) := rfl

theorem raise_lower {point : (ContextualFutureSiteLift.base P).Elements}
    (tree : RawTree (upperShape P shape) (upperPosition P shape position) point) :
    raiseRaw P shape position point (lowerRaw P shape position tree) = tree := by
  induction tree with
  | @sup point label children earlier =>
    change RawTree.sup label (fun next arrow branch =>
      raiseRaw P shape position next (lowerRaw P shape position (children next arrow branch))) = RawTree.sup label children
    apply RawTree.sup_eq_of_cast rfl
    intro next arrow branch
    exact earlier next arrow branch

theorem lower_raise (point : (ContextualFutureSiteLift.base P).Elements)
    (tree : RawTree shape position ((ContextualFutureSiteLift.elementsDown P).obj point)) :
    lowerRaw P shape position (raiseRaw P shape position point tree) = tree := by
  suffices general : ∀ {target} (tree : RawTree shape position target)
      (point : (ContextualFutureSiteLift.base P).Elements) (same : (ContextualFutureSiteLift.elementsDown P).obj point = target),
      lowerRaw P shape position (raiseRawData P shape position tree point same) =
        cast (congrArg (RawTree shape position) same.symm) tree by
    exact general tree point rfl
  intro target tree
  induction tree with
  | @sup target label children earlier =>
    intro point same
    cases same
    change RawTree.sup label (fun next arrow branch =>
      lowerRaw P shape position (raiseRawData P shape position (children next arrow branch)
        ((ContextualFutureSiteLift.elementsUp P).obj next) rfl)) = RawTree.sup label children
    apply RawTree.sup_eq_of_cast rfl
    intro next arrow branch
    exact earlier next arrow branch ((ContextualFutureSiteLift.elementsUp P).obj next) rfl

noncomputable def rawEquiv (point : (ContextualFutureSiteLift.base P).Elements) :
    RawTree (upperShape P shape) (upperPosition P shape position) point ≃
      RawTree shape position ((ContextualFutureSiteLift.elementsDown P).obj point) where
  toFun := lowerRaw P shape position
  invFun := raiseRaw P shape position point
  left_inv := raise_lower P shape position
  right_inv := lower_raise P shape position point

theorem composite_position_up {X Y Z : P.Elements} (label : shape.obj X) (first : X ⟶ Y) (later : Y ⟶ Z)
    (branch : Position shape position (shape.map first label) later) :
    HEq (ContextualWTypes.compositePosition (upperShape P shape) (upperPosition P shape position)
      (X := (ContextualFutureSiteLift.elementsUp P).obj X) (Y := (ContextualFutureSiteLift.elementsUp P).obj Y)
      (Z := (ContextualFutureSiteLift.elementsUp P).obj Z)
      (ULift.up label) ((ContextualFutureSiteLift.elementsUp P).map first) ((ContextualFutureSiteLift.elementsUp P).map later)
      (ULift.up branch))
      (ULift.up (ContextualWTypes.compositePosition shape position label first later branch) :
        ULift.{u + 1, u} (Position shape position label (first ≫ later))) :=
  (cast_heq _ _).trans (up_heq (cast_heq _ _)).symm

theorem position_along_up {X Y Z : P.Elements} (label : shape.obj X) (first : X ⟶ Y) (later : Y ⟶ Z)
    (branch : Position shape position label first) :
    HEq (ContextualWTypes.positionAlong (upperShape P shape) (upperPosition P shape position)
      (X := (ContextualFutureSiteLift.elementsUp P).obj X) (Y := (ContextualFutureSiteLift.elementsUp P).obj Y)
      (Z := (ContextualFutureSiteLift.elementsUp P).obj Z)
      (ULift.up label) ((ContextualFutureSiteLift.elementsUp P).map first) ((ContextualFutureSiteLift.elementsUp P).map later)
      (ULift.up branch))
      (ULift.up (ContextualWTypes.positionAlong shape position label first later branch) :
        ULift.{u + 1, u} (Position shape position label (first ≫ later))) :=
  (cast_heq _ _).trans (up_heq (cast_heq _ _)).symm

theorem lower_restrict {X Y : (ContextualFutureSiteLift.base P).Elements} (arrow : X ⟶ Y)
    (tree : RawTree (upperShape P shape) (upperPosition P shape position) X) :
    lowerRaw P shape position (ContextualWTypes.restrict (upperShape P shape) (upperPosition P shape position) arrow tree) =
      ContextualWTypes.restrict shape position ((ContextualFutureSiteLift.elementsDown P).map arrow)
        (lowerRaw P shape position tree) := by
  cases tree with
  | sup label children =>
    apply RawTree.sup_eq_of_cast rfl
    intro next later branch
    apply congrArg (lowerRaw P shape position)
    exact RawTree.children_eq label children rfl
      (ContextualWTypes.compositePosition (upperShape P shape) (upperPosition P shape position) label arrow
        ((ContextualFutureSiteLift.elementsUp P).map later) (ULift.up branch))
      (ULift.up (ContextualWTypes.compositePosition shape position label.down
        ((ContextualFutureSiteLift.elementsDown P).map arrow) later branch))
      (composite_position_up P shape position label.down ((ContextualFutureSiteLift.elementsDown P).map arrow) later branch)

theorem raise_restrict {X Y : (ContextualFutureSiteLift.base P).Elements} (arrow : X ⟶ Y)
    (tree : RawTree shape position ((ContextualFutureSiteLift.elementsDown P).obj X)) :
    raiseRaw P shape position Y (ContextualWTypes.restrict shape position ((ContextualFutureSiteLift.elementsDown P).map arrow) tree) =
      ContextualWTypes.restrict (upperShape P shape) (upperPosition P shape position) arrow (raiseRaw P shape position X tree) := by
  apply (rawEquiv P shape position Y).injective
  exact (lower_raise P shape position Y _).trans
    ((congrArg (ContextualWTypes.restrict shape position ((ContextualFutureSiteLift.elementsDown P).map arrow))
      (lower_raise P shape position X tree)).symm.trans (lower_restrict P shape position arrow _).symm)

theorem lower_natural {point : (ContextualFutureSiteLift.base P).Elements}
    (tree : RawTree (upperShape P shape) (upperPosition P shape position) point)
    (natural : Natural (upperShape P shape) (upperPosition P shape position) tree) :
    Natural shape position (lowerRaw P shape position tree) := by
  induction tree with
  | @sup point label children earlier =>
    constructor
    · intro next arrow branch
      exact earlier ((ContextualFutureSiteLift.elementsUp P).obj next) ((ContextualFutureSiteLift.elementsUp P).map arrow)
        (ULift.up branch) (natural.1 _ _ _)
    · intro next last first later branch
      refine (lower_restrict P shape position ((ContextualFutureSiteLift.elementsUp P).map later) _).symm.trans ?_
      refine (congrArg (lowerRaw P shape position) (natural.2 _ _
        ((ContextualFutureSiteLift.elementsUp P).map first) ((ContextualFutureSiteLift.elementsUp P).map later) (ULift.up branch))).trans ?_
      apply congrArg (lowerRaw P shape position)
      exact RawTree.children_eq label children rfl _ _
        (position_along_up P shape position label.down first later branch)

theorem raise_natural (point : (ContextualFutureSiteLift.base P).Elements)
    (tree : RawTree shape position ((ContextualFutureSiteLift.elementsDown P).obj point))
    (natural : Natural shape position tree) :
    Natural (upperShape P shape) (upperPosition P shape position) (raiseRaw P shape position point tree) := by
  suffices general : ∀ {target} (tree : RawTree shape position target), Natural shape position tree →
      ∀ (point : (ContextualFutureSiteLift.base P).Elements) (same : (ContextualFutureSiteLift.elementsDown P).obj point = target),
      Natural (upperShape P shape) (upperPosition P shape position) (raiseRawData P shape position tree point same) by
    exact general tree natural point rfl
  intro target tree
  induction tree with
  | @sup target label children earlier =>
    intro natural point same
    cases same
    constructor
    · intro next arrow branch
      exact earlier ((ContextualFutureSiteLift.elementsDown P).obj next) ((ContextualFutureSiteLift.elementsDown P).map arrow)
        branch.down (natural.1 _ _ _) next rfl
    · intro next last first later branch
      refine (raise_restrict P shape position later _).symm.trans ?_
      refine (congrArg (raiseRaw P shape position last) (natural.2 _ _
        ((ContextualFutureSiteLift.elementsDown P).map first) ((ContextualFutureSiteLift.elementsDown P).map later) branch.down)).trans ?_
      apply congrArg (raiseRaw P shape position last)
      exact RawTree.children_eq label children rfl _ _
        (down_heq (position_along_up P shape position label ((ContextualFutureSiteLift.elementsDown P).map first)
          ((ContextualFutureSiteLift.elementsDown P).map later) branch.down)).symm

noncomputable def lowerNatural {point : (ContextualFutureSiteLift.base P).Elements}
    (tree : NaturalTree (upperShape P shape) (upperPosition P shape position) point) :
    NaturalTree shape position ((ContextualFutureSiteLift.elementsDown P).obj point) :=
  ⟨lowerRaw P shape position tree.val, lower_natural P shape position tree.val tree.property⟩

noncomputable def raiseNatural (point : (ContextualFutureSiteLift.base P).Elements)
    (tree : NaturalTree shape position ((ContextualFutureSiteLift.elementsDown P).obj point)) :
    NaturalTree (upperShape P shape) (upperPosition P shape position) point :=
  ⟨raiseRaw P shape position point tree.val, raise_natural P shape position point tree.val tree.property⟩

noncomputable def naturalEquiv (point : (ContextualFutureSiteLift.base P).Elements) :
    NaturalTree (upperShape P shape) (upperPosition P shape position) point ≃
      NaturalTree shape position ((ContextualFutureSiteLift.elementsDown P).obj point) where
  toFun := lowerNatural P shape position
  invFun := raiseNatural P shape position point
  left_inv tree := Subtype.ext (raise_lower P shape position tree.val)
  right_inv tree := Subtype.ext (lower_raise P shape position point tree.val)

noncomputable def comparison : NatTrans (ContextualWTypes.family (upperShape P shape) (upperPosition P shape position))
    (ContextualFutureSiteLift.family P (ContextualWTypes.family shape position)) where
  app point := TypeCat.ofHom fun tree => ULift.up (lowerNatural P shape position tree)
  naturality {X Y} arrow := by
    apply ConcreteCategory.hom_ext
    intro tree
    exact congrArg ULift.up (Subtype.ext (lower_restrict P shape position arrow tree.val))

noncomputable def inverse : NatTrans (ContextualFutureSiteLift.family P (ContextualWTypes.family shape position))
    (ContextualWTypes.family (upperShape P shape) (upperPosition P shape position)) where
  app point := TypeCat.ofHom fun tree => raiseNatural P shape position point tree.down
  naturality {X Y} arrow := by
    apply ConcreteCategory.hom_ext
    intro tree
    exact Subtype.ext (raise_restrict P shape position arrow tree.down.val)

theorem comparison_left : Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose
    (comparison P shape position) (inverse P shape position) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity _ := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro tree
  exact Subtype.ext (raise_lower P shape position tree.val)

theorem comparison_right : Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose
    (inverse P shape position) (comparison P shape position) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity _ := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro tree
  exact congrArg ULift.up (Subtype.ext (lower_raise P shape position point tree.down.val))

end Mettapedia.TypeTheory.ContextualFutureSiteW
