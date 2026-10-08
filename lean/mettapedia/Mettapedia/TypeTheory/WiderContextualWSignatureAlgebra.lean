import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWSignatureEquivalence
import Mettapedia.TypeTheory.WiderContextualWAlgebras

/-!
# Wider algebra values under complete dependent W signature equivalence

Every future dependent position is translated explicitly. The algebra
comparison and the equality of independently constructed folds permit
consumer values in a universe independent of the small tree signatures.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.WiderContextualWSignatureAlgebra

open CategoryTheory MaterialSets.Hypersets
open ContextualWTypes (RawTree NaturalTree)
open ContextualWSignature
open WiderContextualWAlgebras (Branches)

universe u h
variable {D : Type u} [Category.{u} D]
variable {shape nextShape : D ⥤ Type u}
variable {position : shape.Elements ⥤ Type u} {nextPosition : nextShape.Elements ⥤ Type u}
variable (signature : ContextualWSignature.Signature (shape := shape) (nextShape := nextShape)
  (position := position) (nextPosition := nextPosition))
variable (target : D ⥤ Type h)

def mapBranches {X : D} (label : shape.obj X) (branches : Branches shape position target label) :
    Branches nextShape nextPosition target (signature.shapes X label) where
  app Y arrow branch := branches.app Y arrow ((forwardPosition signature label arrow).symm branch)
  naturality Y Z first later branch :=
    (branches.naturality Y Z first later _).trans
      (congrArg (branches.app Z (first ≫ later)) (backwardPosition_along signature label first later branch))

def unmapBranches {X : D} (label : shape.obj X)
    (branches : Branches nextShape nextPosition target (signature.shapes X label)) :
    Branches shape position target label where
  app Y arrow branch := branches.app Y arrow (forwardPosition signature label arrow branch)
  naturality Y Z first later branch :=
    (branches.naturality Y Z first later _).trans
      (congrArg (branches.app Z (first ≫ later)) (forwardPosition_along signature label first later branch).symm)

theorem unmap_map_branches {X : D} (label : shape.obj X) (branches : Branches shape position target label) :
    unmapBranches signature target label (mapBranches signature target label branches) = branches := by
  apply Branches.ext
  intro Y arrow branch
  exact congrArg (branches.app Y arrow) ((forwardPosition signature label arrow).symm_apply_apply branch)

theorem map_unmap_branches {X : D} (label : shape.obj X)
    (branches : Branches nextShape nextPosition target (signature.shapes X label)) :
    mapBranches signature target label (unmapBranches signature target label branches) = branches := by
  apply Branches.ext
  intro Y arrow branch
  exact congrArg (branches.app Y arrow) ((forwardPosition signature label arrow).apply_symm_apply branch)

def branchEquiv {X : D} (label : shape.obj X) : Branches shape position target label ≃
    Branches nextShape nextPosition target (signature.shapes X label) where
  toFun := mapBranches signature target label
  invFun := unmapBranches signature target label
  left_inv := unmap_map_branches signature target label
  right_inv := map_unmap_branches signature target label

def pullAlgebra (algebra : WiderContextualWAlgebras.Algebra nextShape nextPosition target) :
    WiderContextualWAlgebras.Algebra shape position target where
  make X label branches := algebra.make X (signature.shapes X label) (mapBranches signature target label branches)
  naturality X Y arrow label branches := by
    refine (algebra.naturality X Y arrow (signature.shapes X label) (mapBranches signature target label branches)).trans ?_
    apply Eq.symm
    apply WiderContextualWAlgebras.Algebra.make_eq_of_cast nextShape nextPosition algebra (signature.shape_natural arrow label)
    intro Z later branch
    exact congrArg (branches.app Z (arrow ≫ later)) (backwardPosition_composite signature label arrow later branch).symm

theorem map_evaluates (algebra : WiderContextualWAlgebras.Algebra nextShape nextPosition target)
    {X : D} {tree : RawTree shape position X} {value : target.obj X}
    (evaluation : WiderContextualWAlgebras.Evaluates shape position (pullAlgebra signature target algebra) tree value) :
    WiderContextualWAlgebras.Evaluates nextShape nextPosition algebra (mapRaw signature tree) value := by
  induction evaluation with
  | @sup X label children branches values earlier =>
    exact WiderContextualWAlgebras.Evaluates.sup (signature.shapes X label)
      (fun Y arrow branch => mapRaw signature (children Y arrow ((forwardPosition signature label arrow).symm branch)))
      (mapBranches signature target label branches)
      (fun Y arrow branch => earlier Y arrow ((forwardPosition signature label arrow).symm branch))

theorem fold_map (algebra : WiderContextualWAlgebras.Algebra nextShape nextPosition target)
    {X : D} (tree : NaturalTree shape position X) :
    WiderContextualWAlgebras.fold nextShape nextPosition algebra (mapNatural signature tree) =
      WiderContextualWAlgebras.fold shape position (pullAlgebra signature target algebra) tree :=
  WiderContextualWAlgebras.evaluates_unique nextShape nextPosition algebra
    (WiderContextualWAlgebras.fold_evaluates nextShape nextPosition algebra _)
    (map_evaluates signature target algebra
      (WiderContextualWAlgebras.fold_evaluates shape position (pullAlgebra signature target algebra) tree))

noncomputable def treeMap : WiderPresheafDependentFunctions.Hom
    (ContextualWTypes.family shape position) (ContextualWTypes.family nextShape nextPosition) where
  app _ := mapNatural signature
  naturality arrow tree := (mapNatural_restrict signature arrow tree).symm

theorem constructor_map {X : D} (label : shape.obj X)
    (branches : Branches shape position (ContextualWTypes.family shape position) label) :
    mapNatural signature ((WiderContextualWAlgebras.treeAlgebra shape position).make X label branches) =
      (WiderContextualWAlgebras.treeAlgebra nextShape nextPosition).make X (signature.shapes X label)
        ((mapBranches signature (ContextualWTypes.family shape position) label branches).map (treeMap signature)) :=
  Subtype.ext rfl

theorem fold_inverse (algebra : WiderContextualWAlgebras.Algebra shape position target)
    {X : D} (tree : NaturalTree shape position X) :
    WiderContextualWAlgebras.fold nextShape nextPosition
      (pullAlgebra (ContextualWSignatureEquivalence.inverseSignature signature) target algebra)
      (mapNatural signature tree) = WiderContextualWAlgebras.fold shape position algebra tree := by
  have result := fold_map (ContextualWSignatureEquivalence.inverseSignature signature) target algebra
    (mapNatural signature tree)
  have recovered : mapNatural (ContextualWSignatureEquivalence.inverseSignature signature)
      (mapNatural signature tree) = tree :=
    Subtype.ext (ContextualWSignatureEquivalence.inverse_forward_raw signature tree.val)
  exact result.symm.trans (congrArg (WiderContextualWAlgebras.fold shape position algebra) recovered)

end Mettapedia.TypeTheory.WiderContextualWSignatureAlgebra
