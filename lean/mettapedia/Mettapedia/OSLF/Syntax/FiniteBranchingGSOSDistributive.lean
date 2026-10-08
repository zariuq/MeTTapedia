import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSCofree
import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSOperational

/-!
# Finite branching GSOS over the constructed cofree comonad

The natural GSOS law earns the actual indexed free-monad lifting. Its
mapped cofree counit is transposed through the constructed colored-tree
adjunction to obtain `T D ⟶ D T`. The four Beck laws follow from the
independently proved lifting/cofree theorem. Complete successor and root
readouts tie that categorical law to its actual operational coiteration;
the original operational behavior is recovered exactly.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.Distributive

open _root_.CategoryTheory Mettapedia.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u} (law : Law S Actions)

/-- Compatibility is earned by the actual indexed operational fold. -/
def lifting : CoalgebraMonadDistributive.Lift (behaviourFunctor S Actions) S.termMonad :=
  IndexedGSOS.Operational.lifting (lawEquiv S Actions law)

def lawOverCofree :
    (Cofree.comonad S Actions).toFunctor ⋙ S.termMonad.toFunctor ⟶
      S.termMonad.toFunctor ⋙ (Cofree.comonad S Actions).toFunctor :=
  CoalgebraMonadDistributive.distributive (lifting law) (Cofree.functor S Actions)
    (Cofree.adjunction S Actions)

theorem unfolding_readout (X : S.Families) (base : PUnit.{u + 1}) (sort : S.Srt)
    (term : S.polynomial.Free ((Cofree.comonad S Actions).obj X) base sort) :
    (lawOverCofree law).app X base sort term =
      FiniteActionTree.Tree.coiterate
        ((IndexedGSOS.Operational.liftObject (lawEquiv S Actions law)
          ((Cofree.functor S Actions).obj X)).str base sort)
        (S.termMonad.map ((Cofree.comonad S Actions).ε.app X) base sort) term :=
  FiniteActionTreeCofree.transpose_readout PUnit.{u + 1} (fun _ => S.Srt) (fun _ => Actions)
    ((lifting law).object ((Cofree.functor S Actions).obj X)) (S.termMonad.obj X)
    (S.termMonad.map ((Cofree.comonad S Actions).ε.app X)) base sort term

theorem unit (X : S.Families) :
    S.termMonad.η.app ((Cofree.comonad S Actions).obj X) ≫ (lawOverCofree law).app X =
      (Cofree.comonad S Actions).map (S.termMonad.η.app X) :=
  CoalgebraMonadDistributive.beck_unit (lifting law) (Cofree.functor S Actions)
    (Cofree.adjunction S Actions) X

theorem multiplication (X : S.Families) :
    S.termMonad.μ.app ((Cofree.comonad S Actions).obj X) ≫ (lawOverCofree law).app X =
      S.termMonad.map ((lawOverCofree law).app X) ≫
        (lawOverCofree law).app (S.termMonad.obj X) ≫
          (Cofree.comonad S Actions).map (S.termMonad.μ.app X) :=
  CoalgebraMonadDistributive.beck_multiplication (lifting law) (Cofree.functor S Actions)
    (Cofree.adjunction S Actions) X

theorem counit (X : S.Families) :
    (lawOverCofree law).app X ≫ (Cofree.comonad S Actions).ε.app (S.termMonad.obj X) =
      S.termMonad.map ((Cofree.comonad S Actions).ε.app X) :=
  CoalgebraMonadDistributive.beck_counit (lifting law) (Cofree.functor S Actions)
    (Cofree.adjunction S Actions) X

theorem comultiplication (X : S.Families) :
    (lawOverCofree law).app X ≫ (Cofree.comonad S Actions).δ.app (S.termMonad.obj X) =
      S.termMonad.map ((Cofree.comonad S Actions).δ.app X) ≫
        (lawOverCofree law).app ((Cofree.comonad S Actions).obj X) ≫
          (Cofree.comonad S Actions).map ((lawOverCofree law).app X) :=
  CoalgebraMonadDistributive.beck_comultiplication (lifting law) (Cofree.functor S Actions)
    (Cofree.adjunction S Actions) X

theorem root_readout (X : S.Families) (base : PUnit.{u + 1}) (sort : S.Srt)
    (term : S.polynomial.Free ((Cofree.comonad S Actions).obj X) base sort) :
    FiniteActionTree.Tree.root ((lawOverCofree law).app X base sort term) =
      S.termMonad.map ((Cofree.comonad S Actions).ε.app X) base sort term :=
  congrArg (fun arrow => arrow base sort term) (counit law X)

theorem step_readout (X : S.Families) (base : PUnit.{u + 1}) (sort : S.Srt)
    (term : S.polynomial.Free ((Cofree.comonad S Actions).obj X) base sort)
    (action : Actions sort) :
    FiniteActionTree.Tree.step ((lawOverCofree law).app X base sort term) action =
      FinitePowerset.map ((lawOverCofree law).app X base sort)
        (Operational.coalgebra law ((Cofree.functor S Actions).obj X).str base sort term action) :=
  (congrArg (fun arrow => arrow base sort term action)
    (CoalgebraMonadDistributive.componentCoalgebra (lifting law)
      (Cofree.functor S Actions) (Cofree.adjunction S Actions) X).h).symm

theorem pure_readout (X : S.Families) (base : PUnit.{u + 1}) (sort : S.Srt)
    (tree : FiniteActionTree.Tree (Actions sort) (X base sort)) :
    (lawOverCofree law).app X base sort (IndexedPolynomial.Free.pure S.polynomial tree) =
      FiniteActionTree.Tree.map (IndexedPolynomial.Free.pure S.polynomial) tree :=
  congrArg (fun arrow => arrow base sort tree) (unit law X)

theorem operational_recovered (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    (IndexedGSOS.Operational.liftObject (lawEquiv S Actions law) object).str =
      S.termMonad.map ((Cofree.adjunction S Actions).unit.app object).f ≫
        (lawOverCofree law).app object.V ≫
          ((Cofree.functor S Actions).obj (S.termMonad.obj object.V)).str ≫
            (behaviourFunctor S Actions).map
              ((Cofree.comonad S Actions).ε.app (S.termMonad.obj object.V)) :=
  CoalgebraMonadDistributive.lifting_recovered (lifting law) (Cofree.functor S Actions)
    (Cofree.adjunction S Actions) object

/-- Complete constructor conclusions are recovered, including collisions. -/
theorem constructor_recovered (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt) (operator : S.Operator sort)
    (children : (position : S.Position operator) →
      S.polynomial.Free object.V base (S.argument operator position)) (action : Actions sort) :
    FinitePowerset.map FiniteActionTree.Tree.root
      (FiniteActionTree.Tree.step ((lawOverCofree law).app object.V base sort
        (S.termMonad.map ((Cofree.adjunction S Actions).unit.app object).f base sort
          (IndexedPolynomial.Free.node S.polynomial operator children))) action) =
      FinitePowerset.map (IndexedPolynomial.Free.join S.polynomial)
        (law.app (S.polynomial.Free object.V) base sort
          ⟨operator, fun position =>
            (children position, Operational.coalgebra law object.str base _
              (children position))⟩ action) := by
  have recovered := congrArg (fun arrow => arrow base sort
    (IndexedPolynomial.Free.node S.polynomial operator children) action)
      (operational_recovered law object)
  exact recovered.symm.trans (Operational.coalgebra_node law object.str operator children action)

end Mettapedia.OSLF.FiniteBranching.Distributive
