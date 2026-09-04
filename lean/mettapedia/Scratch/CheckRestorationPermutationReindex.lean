import Mettapedia.GSLT.LanguageDef.CostRestorationRelation

namespace Mettapedia.GSLT.LanguageDef.CostStaticAtomKeyCospan

open Mettapedia.OSLF.MeTTaIL.Syntax

namespace CommonRestorationApex

private def listToForall₂
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl}
    {depth : Nat} {left right : List Pattern}
    (alignment : CommonRestorationApexList source cospan declaration depth
      left right) :
    List.Forall₂
      (CommonRestorationApex source cospan declaration depth) left right :=
  match alignment with
  | .nil _ => .nil
  | .cons head tail => .cons head (listToForall₂ tail)

private def listOfForall₂
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl}
    {depth : Nat} {left right : List Pattern}
    (alignment : List.Forall₂
      (CommonRestorationApex source cospan declaration depth) left right) :
    CommonRestorationApexList source cospan declaration depth left right :=
  match alignment with
  | .nil => .nil depth
  | .cons head tail => .cons head (listOfForall₂ tail)

/-- Reindex both endpoints of an aligned permutation without confusing
finite occurrence order with semantic alignment. -/
noncomputable def Permutation.of_endpoint_perms
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl} {depth : Nat}
    {left left' right right' : List Pattern}
    (alignment : Permutation (source := source) cospan declaration depth
      left right)
    (leftPermutation : List.Perm left' left)
    (rightPermutation : List.Perm right' right) :
    Permutation (source := source) cospan declaration depth left' right' := by
  let evidence :=
    List.perm_comp_forall₂ leftPermutation (listToForall₂ alignment.aligned)
  let middle' := Classical.choose evidence
  have middleSpec := Classical.choose_spec evidence
  exact
    { middle := middle'
      aligned := listOfForall₂ middleSpec.1
      permutation := middleSpec.2.trans
        (alignment.permutation.trans rightPermutation.symm) }

end CommonRestorationApex

end Mettapedia.GSLT.LanguageDef.CostStaticAtomKeyCospan
