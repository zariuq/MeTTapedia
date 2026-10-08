import Mettapedia.CategoryTheory.PartialActionTreeCofree
import Mettapedia.OSLF.Syntax.DeterministicGSOSBehaviour

/-!
# Actual cofree behavior for deterministic GSOS

The cofree object of the same arbitrary-action behavior functor used by
the abstract GSOS law is the indexed family of coloured partial action
trees. It retains every enabled finite path and the complete supplied
colour at that path. This construction adds no finiteness restriction on
the action carriers or the set of enabled actions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.Cofree

open _root_.CategoryTheory Mettapedia.CategoryTheory

universe u

variable (S : Signature.{u}) (Actions : S.Srt → Type u)

/-- The same behavior functor, instantiated in the independent indexed cofree construction. -/
theorem behavior_agrees :
    PartialActionTreeCofree.behavior PUnit.{u + 1} (fun _ => S.Srt) (fun _ => Actions) =
      behaviourFunctor S Actions := rfl

/-- The actual right adjoint for the GSOS behavior functor. -/
def functor : S.Families ⥤ Endofunctor.Coalgebra (behaviourFunctor S Actions) :=
  PartialActionTreeCofree.cofree PUnit.{u + 1} (fun _ => S.Srt) (fun _ => Actions)

/-- Its earned cofree universal property, for the existing category of GSOS coalgebras. -/
def adjunction : Endofunctor.Coalgebra.forget (behaviourFunctor S Actions) ⊣
    functor S Actions :=
  PartialActionTreeCofree.adjunction PUnit.{u + 1} (fun _ => S.Srt) (fun _ => Actions)

/-- The genuine cofree comonad, constructed from the earned adjunction. -/
def comonad : Comonad S.Families := (adjunction S Actions).toComonad

/-- The carrier retains all colours at all enabled finite paths. -/
theorem carrier (X : S.Families) (base : PUnit.{u + 1}) (sort : S.Srt) :
    (comonad S Actions).obj X base sort = PartialActionTree (Actions sort) (X base sort) := rfl

theorem counit_readout (X : S.Families) (base : PUnit.{u + 1}) (sort : S.Srt)
    (tree : PartialActionTree (Actions sort) (X base sort)) :
    ((comonad S Actions).ε.app X) base sort tree = tree.root :=
  PartialActionTreeCofree.derived_counit_readout PUnit.{u + 1} (fun _ => S.Srt)
    (fun _ => Actions) X base sort tree

theorem comultiplication_readout (X : S.Families) (base : PUnit.{u + 1}) (sort : S.Srt)
    (tree : PartialActionTree (Actions sort) (X base sort)) :
    ((comonad S Actions).δ.app X) base sort tree = PartialActionTree.duplicate tree :=
  PartialActionTreeCofree.derived_comultiplication_readout PUnit.{u + 1} (fun _ => S.Srt)
    (fun _ => Actions) X base sort tree

/-- The universal extension is actual finite-path unfolding, rather than a chosen semantic map. -/
theorem extension_readout (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (X : S.Families) (colour : object.V ⟶ X)
    (base : PUnit.{u + 1}) (sort : S.Srt) (state : object.V base sort) :
    (((adjunction S Actions).homEquiv object X) colour).f base sort state =
      PartialActionTree.coiterate (object.str base sort) (colour base sort) state :=
  PartialActionTreeCofree.transpose_readout PUnit.{u + 1} (fun _ => S.Srt) (fun _ => Actions)
    object X colour base sort state

end Mettapedia.OSLF.DeterministicGSOS.Cofree
