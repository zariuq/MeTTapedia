import Mettapedia.CategoryTheory.FiniteActionTreeCofree
import Mettapedia.OSLF.Syntax.FiniteBranchingBehaviour

/-!
# The constructed cofree comonad for finite labelled GSOS

The arbitrary-action colored tree quotient supplies the actual right
adjoint of the same labelwise finite behavior functor used by the GSOS law.
The comparison imposes no finite action carrier or total support bound.
Root, whole successor sets and subtree duplication read the constructed
adjunction, retaining the independently proved quotient scope.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.Cofree

open _root_.CategoryTheory Mettapedia.CategoryTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)

universe u

variable (S : Signature.{u}) (Actions : S.Srt → Type u)

theorem behavior_agrees :
    FiniteActionTreeCofree.behavior PUnit.{u + 1} (fun _ => S.Srt) (fun _ => Actions) =
      behaviourFunctor S Actions := rfl

def functor : S.Families ⥤ Endofunctor.Coalgebra (behaviourFunctor S Actions) :=
  FiniteActionTreeCofree.cofree PUnit.{u + 1} (fun _ => S.Srt) (fun _ => Actions)

def adjunction : Endofunctor.Coalgebra.forget (behaviourFunctor S Actions) ⊣
    functor S Actions :=
  FiniteActionTreeCofree.adjunction PUnit.{u + 1} (fun _ => S.Srt) (fun _ => Actions)

def comonad : Comonad S.Families := (adjunction S Actions).toComonad

theorem carrier (X : S.Families) (base : PUnit.{u + 1}) (sort : S.Srt) :
    (comonad S Actions).obj X base sort = FiniteActionTree.Tree (Actions sort) (X base sort) := rfl

theorem counit_readout (X : S.Families) (base : PUnit.{u + 1}) (sort : S.Srt)
    (tree : FiniteActionTree.Tree (Actions sort) (X base sort)) :
    ((comonad S Actions).ε.app X) base sort tree = FiniteActionTree.Tree.root tree :=
  FiniteActionTreeCofree.counit_readout PUnit.{u + 1} (fun _ => S.Srt)
    (fun _ => Actions) X base sort tree

theorem comultiplication_readout (X : S.Families) (base : PUnit.{u + 1}) (sort : S.Srt)
    (tree : FiniteActionTree.Tree (Actions sort) (X base sort)) :
    ((comonad S Actions).δ.app X) base sort tree = FiniteActionTree.Tree.duplicate tree :=
  FiniteActionTreeCofree.comultiplication_readout PUnit.{u + 1} (fun _ => S.Srt)
    (fun _ => Actions) X base sort tree

theorem map_readout {X Y : S.Families} (mapping : X ⟶ Y)
    (base : PUnit.{u + 1}) (sort : S.Srt)
    (tree : FiniteActionTree.Tree (Actions sort) (X base sort)) :
    (comonad S Actions).map mapping base sort tree =
      FiniteActionTree.Tree.map (mapping base sort) tree := rfl

theorem extension_readout (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (X : S.Families) (colour : object.V ⟶ X)
    (base : PUnit.{u + 1}) (sort : S.Srt) (state : object.V base sort) :
    (((adjunction S Actions).homEquiv object X) colour).f base sort state =
      FiniteActionTree.Tree.coiterate (object.str base sort) (colour base sort) state :=
  FiniteActionTreeCofree.transpose_readout PUnit.{u + 1} (fun _ => S.Srt) (fun _ => Actions)
    object X colour base sort state

end Mettapedia.OSLF.FiniteBranching.Cofree
