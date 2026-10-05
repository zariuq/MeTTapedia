import Mettapedia.TypeTheory.PresheafSiteLift
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWTypes

/-!
# Full contextual W trees on the constructed successor site

The raw comparison uses indexed induction in both directions. Every future
world, actual arrow and transported position is raised or lowered, including
arbitrary infinite branch carriers. Hereditary naturality and restriction
commute with these constructed operations. The comparison is independent
of material label dictionaries; no inverse for a host world is selected.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWSiteLift

open CategoryTheory
open Mettapedia.TypeTheory
open ContextualWTypes (RawTree Natural NaturalTree Position)

universe u
variable {C : Type u} [Category.{u} C]
variable (P : Cᵒᵖ ⥤ Type u) (shape : P.Elements ⥤ Type u) (position : shape.Elements ⥤ Type u)

abbrev upperShape := PresheafSiteLift.family P shape
abbrev upperPosition := PresheafSiteLift.body P shape position

private theorem up_heq {A B : Type u} {a : A} {b : B} (same : HEq a b) :
    HEq (ULift.up a : ULift.{u + 1, u} A) (ULift.up b : ULift.{u + 1, u} B) := by
  cases same
  rfl

private theorem down_heq {A : Type u} {a b : ULift.{u + 1, u} A}
    (same : HEq a b) : HEq a.down b.down := by
  exact heq_of_eq (congrArg ULift.down (eq_of_heq same))

noncomputable def lowerRaw {point : (PresheafSiteLift.base P).Elements}
    (tree : RawTree (upperShape P shape) (upperPosition P shape position) point) :
    RawTree shape position ((PresheafSiteLift.elementsDown P).obj point) :=
  RawTree.rec (shape := upperShape P shape) (position := upperPosition P shape position)
    (motive := fun point _ => RawTree shape position ((PresheafSiteLift.elementsDown P).obj point))
    (fun {_point} label _children earlier => .sup label.down (fun next arrow branch =>
      earlier ((PresheafSiteLift.elementsUp P).obj next) ((PresheafSiteLift.elementsUp P).map arrow) (ULift.up branch))) tree

noncomputable def raiseRawData {target : P.Elements} (tree : RawTree shape position target) :
    (point : (PresheafSiteLift.base P).Elements) → (PresheafSiteLift.elementsDown P).obj point = target →
      RawTree (upperShape P shape) (upperPosition P shape position) point :=
  RawTree.rec (motive := fun target _ =>
    (point : (PresheafSiteLift.base P).Elements) → (PresheafSiteLift.elementsDown P).obj point = target →
      RawTree (upperShape P shape) (upperPosition P shape position) point)
    (fun {target} label _children earlier point same => by
      cases same
      exact .sup (ULift.up label) (fun next arrow branch => earlier
        ((PresheafSiteLift.elementsDown P).obj next) ((PresheafSiteLift.elementsDown P).map arrow)
        branch.down next rfl)) tree

noncomputable def raiseRaw (point : (PresheafSiteLift.base P).Elements)
    (tree : RawTree shape position ((PresheafSiteLift.elementsDown P).obj point)) :
    RawTree (upperShape P shape) (upperPosition P shape position) point := raiseRawData P shape position tree point rfl

theorem lower_sup (point : (PresheafSiteLift.base P).Elements) (label : (upperShape P shape).obj point)
    (children : (next : (PresheafSiteLift.base P).Elements) → (arrow : point ⟶ next) →
      Position (upperShape P shape) (upperPosition P shape position) label arrow →
        RawTree (upperShape P shape) (upperPosition P shape position) next) :
    lowerRaw P shape position (.sup label children) = .sup label.down (fun next arrow branch =>
      lowerRaw P shape position (children ((PresheafSiteLift.elementsUp P).obj next)
        ((PresheafSiteLift.elementsUp P).map arrow) (ULift.up branch))) := rfl

theorem raise_sup (point : (PresheafSiteLift.base P).Elements)
    (label : shape.obj ((PresheafSiteLift.elementsDown P).obj point))
    (children : (next : P.Elements) → (arrow : (PresheafSiteLift.elementsDown P).obj point ⟶ next) →
      Position shape position label arrow → RawTree shape position next) :
    raiseRaw P shape position point (.sup label children) = .sup (ULift.up label) (fun next arrow branch =>
      raiseRaw P shape position next (children ((PresheafSiteLift.elementsDown P).obj next)
        ((PresheafSiteLift.elementsDown P).map arrow) branch.down)) := rfl

theorem raise_lower {point : (PresheafSiteLift.base P).Elements}
    (tree : RawTree (upperShape P shape) (upperPosition P shape position) point) :
    raiseRaw P shape position point (lowerRaw P shape position tree) = tree := by
  induction tree with
  | @sup point label children earlier =>
    change RawTree.sup label (fun next arrow branch =>
      raiseRaw P shape position next (lowerRaw P shape position (children next arrow branch))) = RawTree.sup label children
    apply RawTree.sup_eq_of_cast rfl
    intro next arrow branch
    exact earlier next arrow branch

theorem lower_raise (point : (PresheafSiteLift.base P).Elements)
    (tree : RawTree shape position ((PresheafSiteLift.elementsDown P).obj point)) :
    lowerRaw P shape position (raiseRaw P shape position point tree) = tree := by
  suffices general : ∀ {target} (tree : RawTree shape position target)
      (point : (PresheafSiteLift.base P).Elements) (same : (PresheafSiteLift.elementsDown P).obj point = target),
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
        ((PresheafSiteLift.elementsUp P).obj next) rfl)) = RawTree.sup label children
    apply RawTree.sup_eq_of_cast rfl
    intro next arrow branch
    exact earlier next arrow branch ((PresheafSiteLift.elementsUp P).obj next) rfl

noncomputable def rawEquiv (point : (PresheafSiteLift.base P).Elements) :
    RawTree (upperShape P shape) (upperPosition P shape position) point ≃
      RawTree shape position ((PresheafSiteLift.elementsDown P).obj point) where
  toFun := lowerRaw P shape position
  invFun := raiseRaw P shape position point
  left_inv := raise_lower P shape position
  right_inv := lower_raise P shape position point

theorem composite_position_up {X Y Z : P.Elements} (label : shape.obj X) (first : X ⟶ Y) (later : Y ⟶ Z)
    (branch : Position shape position (shape.map first label) later) :
    HEq (ContextualWTypes.compositePosition (upperShape P shape) (upperPosition P shape position)
      (X := (PresheafSiteLift.elementsUp P).obj X) (Y := (PresheafSiteLift.elementsUp P).obj Y)
      (Z := (PresheafSiteLift.elementsUp P).obj Z)
      (ULift.up label) ((PresheafSiteLift.elementsUp P).map first) ((PresheafSiteLift.elementsUp P).map later)
      (ULift.up branch))
      (ULift.up (ContextualWTypes.compositePosition shape position label first later branch) :
        ULift.{u + 1, u} (Position shape position label (first ≫ later))) :=
  (cast_heq _ _).trans (up_heq (cast_heq _ _)).symm

theorem position_along_up {X Y Z : P.Elements} (label : shape.obj X) (first : X ⟶ Y) (later : Y ⟶ Z)
    (branch : Position shape position label first) :
    HEq (ContextualWTypes.positionAlong (upperShape P shape) (upperPosition P shape position)
      (X := (PresheafSiteLift.elementsUp P).obj X) (Y := (PresheafSiteLift.elementsUp P).obj Y)
      (Z := (PresheafSiteLift.elementsUp P).obj Z)
      (ULift.up label) ((PresheafSiteLift.elementsUp P).map first) ((PresheafSiteLift.elementsUp P).map later)
      (ULift.up branch))
      (ULift.up (ContextualWTypes.positionAlong shape position label first later branch) :
        ULift.{u + 1, u} (Position shape position label (first ≫ later))) :=
  (cast_heq _ _).trans (up_heq (cast_heq _ _)).symm

theorem lower_restrict {X Y : (PresheafSiteLift.base P).Elements} (arrow : X ⟶ Y)
    (tree : RawTree (upperShape P shape) (upperPosition P shape position) X) :
    lowerRaw P shape position (ContextualWTypes.restrict (upperShape P shape) (upperPosition P shape position) arrow tree) =
      ContextualWTypes.restrict shape position ((PresheafSiteLift.elementsDown P).map arrow)
        (lowerRaw P shape position tree) := by
  cases tree with
  | sup label children =>
    apply RawTree.sup_eq_of_cast rfl
    intro next later branch
    apply congrArg (lowerRaw P shape position)
    exact RawTree.children_eq label children rfl
      (ContextualWTypes.compositePosition (upperShape P shape) (upperPosition P shape position) label arrow
        ((PresheafSiteLift.elementsUp P).map later) (ULift.up branch))
      (ULift.up (ContextualWTypes.compositePosition shape position label.down
        ((PresheafSiteLift.elementsDown P).map arrow) later branch))
      (composite_position_up P shape position label.down ((PresheafSiteLift.elementsDown P).map arrow) later branch)

theorem raise_restrict {X Y : (PresheafSiteLift.base P).Elements} (arrow : X ⟶ Y)
    (tree : RawTree shape position ((PresheafSiteLift.elementsDown P).obj X)) :
    raiseRaw P shape position Y (ContextualWTypes.restrict shape position ((PresheafSiteLift.elementsDown P).map arrow) tree) =
      ContextualWTypes.restrict (upperShape P shape) (upperPosition P shape position) arrow (raiseRaw P shape position X tree) := by
  apply (rawEquiv P shape position Y).injective
  exact (lower_raise P shape position Y _).trans
    ((congrArg (ContextualWTypes.restrict shape position ((PresheafSiteLift.elementsDown P).map arrow))
      (lower_raise P shape position X tree)).symm.trans (lower_restrict P shape position arrow _).symm)

theorem lower_natural {point : (PresheafSiteLift.base P).Elements}
    (tree : RawTree (upperShape P shape) (upperPosition P shape position) point)
    (natural : Natural (upperShape P shape) (upperPosition P shape position) tree) :
    Natural shape position (lowerRaw P shape position tree) := by
  induction tree with
  | @sup point label children earlier =>
    constructor
    · intro next arrow branch
      exact earlier ((PresheafSiteLift.elementsUp P).obj next) ((PresheafSiteLift.elementsUp P).map arrow)
        (ULift.up branch) (natural.1 _ _ _)
    · intro next last first later branch
      refine (lower_restrict P shape position ((PresheafSiteLift.elementsUp P).map later) _).symm.trans ?_
      refine (congrArg (lowerRaw P shape position) (natural.2 _ _
        ((PresheafSiteLift.elementsUp P).map first) ((PresheafSiteLift.elementsUp P).map later) (ULift.up branch))).trans ?_
      apply congrArg (lowerRaw P shape position)
      exact RawTree.children_eq label children rfl _ _
        (position_along_up P shape position label.down first later branch)

theorem raise_natural (point : (PresheafSiteLift.base P).Elements)
    (tree : RawTree shape position ((PresheafSiteLift.elementsDown P).obj point))
    (natural : Natural shape position tree) :
    Natural (upperShape P shape) (upperPosition P shape position) (raiseRaw P shape position point tree) := by
  suffices general : ∀ {target} (tree : RawTree shape position target), Natural shape position tree →
      ∀ (point : (PresheafSiteLift.base P).Elements) (same : (PresheafSiteLift.elementsDown P).obj point = target),
      Natural (upperShape P shape) (upperPosition P shape position) (raiseRawData P shape position tree point same) by
    exact general tree natural point rfl
  intro target tree
  induction tree with
  | @sup target label children earlier =>
    intro natural point same
    cases same
    constructor
    · intro next arrow branch
      exact earlier ((PresheafSiteLift.elementsDown P).obj next) ((PresheafSiteLift.elementsDown P).map arrow)
        branch.down (natural.1 _ _ _) next rfl
    · intro next last first later branch
      refine (raise_restrict P shape position later _).symm.trans ?_
      refine (congrArg (raiseRaw P shape position last) (natural.2 _ _
        ((PresheafSiteLift.elementsDown P).map first) ((PresheafSiteLift.elementsDown P).map later) branch.down)).trans ?_
      apply congrArg (raiseRaw P shape position last)
      exact RawTree.children_eq label children rfl _ _
        (down_heq (position_along_up P shape position label ((PresheafSiteLift.elementsDown P).map first)
          ((PresheafSiteLift.elementsDown P).map later) branch.down)).symm

noncomputable def lowerNatural {point : (PresheafSiteLift.base P).Elements}
    (tree : NaturalTree (upperShape P shape) (upperPosition P shape position) point) :
    NaturalTree shape position ((PresheafSiteLift.elementsDown P).obj point) :=
  ⟨lowerRaw P shape position tree.val, lower_natural P shape position tree.val tree.property⟩

noncomputable def raiseNatural (point : (PresheafSiteLift.base P).Elements)
    (tree : NaturalTree shape position ((PresheafSiteLift.elementsDown P).obj point)) :
    NaturalTree (upperShape P shape) (upperPosition P shape position) point :=
  ⟨raiseRaw P shape position point tree.val, raise_natural P shape position point tree.val tree.property⟩

noncomputable def naturalEquiv (point : (PresheafSiteLift.base P).Elements) :
    NaturalTree (upperShape P shape) (upperPosition P shape position) point ≃
      NaturalTree shape position ((PresheafSiteLift.elementsDown P).obj point) where
  toFun := lowerNatural P shape position
  invFun := raiseNatural P shape position point
  left_inv tree := Subtype.ext (raise_lower P shape position tree.val)
  right_inv tree := Subtype.ext (lower_raise P shape position point tree.val)

noncomputable def comparison : NatTrans (ContextualWTypes.family (upperShape P shape) (upperPosition P shape position))
    (PresheafSiteLift.family P (ContextualWTypes.family shape position)) where
  app point := TypeCat.ofHom fun tree => ULift.up (lowerNatural P shape position tree)
  naturality {X Y} arrow := by
    apply ConcreteCategory.hom_ext
    intro tree
    exact congrArg ULift.up (Subtype.ext (lower_restrict P shape position arrow tree.val))

noncomputable def inverse : NatTrans (PresheafSiteLift.family P (ContextualWTypes.family shape position))
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

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWSiteLift
