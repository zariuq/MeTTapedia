import Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualWTypes

/-!
# Dependent elimination and initial folds of actual material contextual W

The graph decoder's explicit inverses transfer arbitrary dependent motives
on actual material members, not only proposition-valued support. Natural
trees retain the full future-branch compatibility proof. The material fold
is natural and is uniquely determined by its actual constructor law.

The kernel recursion uses the existing indexed raw-tree recursor. Some
definitions are noncomputable because that indexed recursor has no Lean code
generator implementation; this does not select a tree, world, arrow, or
representative and requires no choice axiom.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualWElimination

open CategoryTheory
open ContextualWTypes (RawTree Position NaturalTree Natural Branches Algebra)
open MaterialContextualWTypes

universe u v
variable {D : Type u} [Category.{u} D]
variable (shape : D ⥤ Type u) (position : shape.Elements ⥤ Type u)
variable (worlds : ArgumentCoding D)
variable (arrows : (source target : D) → ArgumentCoding (source ⟶ target))
variable (shapes : (world : D) → PresentedType (shape.obj world))
variable (positions : (point : shape.Elements) → PresentedType (position.obj point))

section RawDependentElimination

variable (motive : (X : D) → MaterialContextualWTypes.Members shape position worlds arrows shapes positions X → Type v)
variable (step : (X : D) → (label : shape.obj X) →
  (children : (Y : D) → (arrow : X ⟶ Y) → Position shape position label arrow → RawTree shape position Y) →
  ((Y : D) → (arrow : X ⟶ Y) → (branch : Position shape position label arrow) →
    motive Y (treeMember shape position worlds arrows shapes positions (children Y arrow branch))) →
  motive X (treeMember shape position worlds arrows shapes positions (.sup label children)))

noncomputable def rawRecData {X : D} (tree : RawTree shape position X) :
    motive X (treeMember shape position worlds arrows shapes positions tree) :=
  RawTree.rec (motive := fun X tree => motive X (treeMember shape position worlds arrows shapes positions tree))
    (fun {X} label children earlier => step X label children earlier) tree

noncomputable def rawRec {X : D} (root : MaterialContextualWTypes.Members shape position worlds arrows shapes positions X) : motive X root :=
  cast (congrArg (motive X) (treeMember_decode shape position worlds arrows shapes positions root))
    (rawRecData shape position worlds arrows shapes positions motive step (decode shape position worlds arrows shapes positions root))

private theorem rawRecData_heq {X : D} {first second : RawTree shape position X} (same : first = second) :
    HEq (rawRecData shape position worlds arrows shapes positions motive step first)
      (rawRecData shape position worlds arrows shapes positions motive step second) := by
  cases same
  rfl

theorem rawRec_treeMember {X : D} (tree : RawTree shape position X) :
    HEq (rawRec shape position worlds arrows shapes positions motive step (treeMember shape position worlds arrows shapes positions tree))
      (rawRecData shape position worlds arrows shapes positions motive step tree) :=
  (cast_heq _ _).trans (rawRecData_heq shape position worlds arrows shapes positions motive step
    (decode_treeMember shape position worlds arrows shapes positions tree))

/-- Full dependent computation uses the recursively eliminated actual
material children at every retained future branch. -/
theorem rawRec_beta {X : D} (label : shape.obj X)
    (children : (Y : D) → (arrow : X ⟶ Y) → Position shape position label arrow → RawTree shape position Y) :
    rawRec shape position worlds arrows shapes positions motive step
        (treeMember shape position worlds arrows shapes positions (.sup label children)) =
      step X label children
        (fun Y arrow branch => rawRec shape position worlds arrows shapes positions motive step
          (treeMember shape position worlds arrows shapes positions (children Y arrow branch))) := by
  have values : (fun Y arrow branch => rawRec shape position worlds arrows shapes positions motive step
      (treeMember shape position worlds arrows shapes positions (children Y arrow branch))) =
      (fun Y arrow branch => rawRecData shape position worlds arrows shapes positions motive step (children Y arrow branch)) :=
    funext fun Y => funext fun arrow => funext fun branch => eq_of_heq
      (rawRec_treeMember shape position worlds arrows shapes positions motive step (children Y arrow branch))
  exact (eq_of_heq (rawRec_treeMember shape position worlds arrows shapes positions motive step (.sup label children))).trans
    (congrArg (step X label children) values).symm

end RawDependentElimination

section NaturalDependentElimination

variable (motive : (X : D) → NaturalMembers shape position worlds arrows shapes positions X → Type v)
variable (step : (X : D) → (label : shape.obj X) →
  (children : (Y : D) → (arrow : X ⟶ Y) → Position shape position label arrow → NaturalTree shape position Y) →
  (naturality : ∀ (Y Z : D) (first : X ⟶ Y) (later : Y ⟶ Z) branch,
    ContextualWTypes.restrict shape position later (children Y first branch).val =
      (children Z (first ≫ later) (ContextualWTypes.positionAlong shape position label first later branch)).val) →
  ((Y : D) → (arrow : X ⟶ Y) → (branch : Position shape position label arrow) →
    motive Y (naturalMember shape position worlds arrows shapes positions (children Y arrow branch))) →
  motive X (naturalMember shape position worlds arrows shapes positions
    (ContextualWTypes.sup shape position label children naturality)))

noncomputable def naturalRecData {X : D} (tree : NaturalTree shape position X) :
    motive X (naturalMember shape position worlds arrows shapes positions tree) :=
  (RawTree.rec (motive := fun X tree => (natural : Natural shape position tree) →
      motive X (naturalMember shape position worlds arrows shapes positions ⟨tree, natural⟩))
    (fun {X} label children earlier natural =>
      step X label (fun Y arrow branch => ⟨children Y arrow branch, natural.1 Y arrow branch⟩) natural.2
        (fun Y arrow branch => earlier Y arrow branch (natural.1 Y arrow branch))) tree.val) tree.property

noncomputable def naturalRec {X : D} (root : NaturalMembers shape position worlds arrows shapes positions X) : motive X root :=
  cast (congrArg (motive X) (natural_encode_decode shape position worlds arrows shapes positions root))
    (naturalRecData shape position worlds arrows shapes positions motive step
      ((naturalModel shape position worlds arrows shapes positions X).decode root))

private theorem naturalRecData_heq {X : D} {first second : NaturalTree shape position X} (same : first = second) :
    HEq (naturalRecData shape position worlds arrows shapes positions motive step first)
      (naturalRecData shape position worlds arrows shapes positions motive step second) := by
  cases same
  rfl

theorem naturalRec_member {X : D} (tree : NaturalTree shape position X) :
    HEq (naturalRec shape position worlds arrows shapes positions motive step (naturalMember shape position worlds arrows shapes positions tree))
      (naturalRecData shape position worlds arrows shapes positions motive step tree) :=
  (cast_heq _ _).trans (naturalRecData_heq shape position worlds arrows shapes positions motive step
    (natural_decode_encode shape position worlds arrows shapes positions tree))

theorem naturalRec_beta {X : D} (label : shape.obj X)
    (children : (Y : D) → (arrow : X ⟶ Y) → Position shape position label arrow → NaturalTree shape position Y)
    (naturality : ∀ (Y Z : D) (first : X ⟶ Y) (later : Y ⟶ Z) branch,
      ContextualWTypes.restrict shape position later (children Y first branch).val =
        (children Z (first ≫ later) (ContextualWTypes.positionAlong shape position label first later branch)).val) :
    naturalRec shape position worlds arrows shapes positions motive step
        (naturalMember shape position worlds arrows shapes positions (ContextualWTypes.sup shape position label children naturality)) =
      step X label children naturality
        (fun Y arrow branch => naturalRec shape position worlds arrows shapes positions motive step
          (naturalMember shape position worlds arrows shapes positions (children Y arrow branch))) := by
  have values : (fun Y arrow branch => naturalRec shape position worlds arrows shapes positions motive step
      (naturalMember shape position worlds arrows shapes positions (children Y arrow branch))) =
      (fun Y arrow branch => naturalRecData shape position worlds arrows shapes positions motive step (children Y arrow branch)) :=
    funext fun Y => funext fun arrow => funext fun branch => eq_of_heq
      (naturalRec_member shape position worlds arrows shapes positions motive step (children Y arrow branch))
  exact (eq_of_heq (naturalRec_member shape position worlds arrows shapes positions motive step
    (ContextualWTypes.sup shape position label children naturality))).trans
    (congrArg (step X label children naturality) values).symm

end NaturalDependentElimination

section InitialFold

variable {target : D ⥤ Type u} (algebra : Algebra shape position target)

noncomputable def materialFold {X : D} (root : NaturalMembers shape position worlds arrows shapes positions X) : target.obj X :=
  ContextualWTypes.fold shape position algebra ((naturalModel shape position worlds arrows shapes positions X).decode root)

theorem materialFold_natural {X Y : D} (arrow : X ⟶ Y)
    (root : NaturalMembers shape position worlds arrows shapes positions X) :
    target.map arrow (materialFold shape position worlds arrows shapes positions algebra root) =
      materialFold shape position worlds arrows shapes positions algebra
        (naturalMap shape position worlds arrows shapes positions arrow root) := by
  exact (ContextualWTypes.fold_natural shape position algebra arrow
    ((naturalModel shape position worlds arrows shapes positions X).decode root)).trans
      (congrArg (ContextualWTypes.fold shape position algebra)
        (naturalMap_decode shape position worlds arrows shapes positions arrow root)).symm

theorem materialFold_beta {X : D} (label : shape.obj X)
    (branches : Branches shape position (ContextualWTypes.family shape position) label) :
    materialFold shape position worlds arrows shapes positions algebra
        (naturalMember shape position worlds arrows shapes positions
          ((ContextualWTypes.treeAlgebra shape position).make X label branches)) =
      algebra.make X label (branches.map (ContextualWTypes.foldMap shape position algebra)) := by
  exact (congrArg (ContextualWTypes.fold shape position algebra)
    (natural_decode_encode shape position worlds arrows shapes positions
      ((ContextualWTypes.treeAlgebra shape position).make X label branches))).trans
    (ContextualWTypes.fold_beta shape position algebra label branches)

variable (candidate : (X : D) → NaturalMembers shape position worlds arrows shapes positions X → target.obj X)
variable (candidateNatural : ∀ {X Y : D} (arrow : X ⟶ Y) root,
  target.map arrow (candidate X root) = candidate Y (naturalMap shape position worlds arrows shapes positions arrow root))

def candidateMap : NatTrans (ContextualWTypes.family shape position) target where
  app X := TypeCat.ofHom fun tree => candidate X (naturalMember shape position worlds arrows shapes positions tree)
  naturality X Y arrow := by
    apply ConcreteCategory.hom_ext
    intro tree
    exact ((candidateNatural arrow (naturalMember shape position worlds arrows shapes positions tree)).trans
      (congrArg (candidate Y) (naturalMap_member shape position worlds arrows shapes positions arrow tree))).symm

/-- Every natural material algebra morphism is the actual constructed fold.
The constructor law observes all future branches through their member encodings. -/
theorem materialFold_unique
    (constructorLaw : ∀ (X : D) label branches,
      candidate X (naturalMember shape position worlds arrows shapes positions
        ((ContextualWTypes.treeAlgebra shape position).make X label branches)) =
          algebra.make X label (branches.map
            (candidateMap shape position worlds arrows shapes positions candidate candidateNatural)))
    {X : D} (root : NaturalMembers shape position worlds arrows shapes positions X) :
    candidate X root = materialFold shape position worlds arrows shapes positions algebra root := by
  have same := ContextualWTypes.fold_unique shape position algebra
    (candidateMap shape position worlds arrows shapes positions candidate candidateNatural) constructorLaw
  have value := congrArg (fun operation => operation.app X
    ((naturalModel shape position worlds arrows shapes positions X).decode root)) same
  change candidate X (naturalMember shape position worlds arrows shapes positions
    ((naturalModel shape position worlds arrows shapes positions X).decode root)) =
      materialFold shape position worlds arrows shapes positions algebra root at value
  exact (congrArg (candidate X) (natural_encode_decode shape position worlds arrows shapes positions root)).symm.trans value

end InitialFold

end Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualWElimination
