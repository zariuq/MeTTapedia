import Mettapedia.CategoryTheory.CoalgebraMonadDistributive
import Mettapedia.OSLF.Syntax.DeterministicGSOSCofree
import Mettapedia.OSLF.Syntax.DeterministicGSOSCoalgebraMonad

/-!
# GSOS over the actual cofree behavior comonad

The previously earned free-monad lifting supplies the local coalgebra
compatibilities. Transposing its mapped counit through the actual cofree
adjunction gives the distributive law. Each of the four Beck equations
and recovery of the original operational behavior is inherited from the
independently proved categorical construction.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.Distributive

open _root_.CategoryTheory Mettapedia.CategoryTheory Mettapedia.TypeTheory

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u} (law : Law S Actions)

/-- All compatibility fields are discharged by the actual operational coalgebra lifting. -/
noncomputable def lifting :
    CoalgebraMonadDistributive.Lift (behaviourFunctor S Actions) S.termMonad where
  structureMap object := (Operational.liftObject law object).str
  map_compatible mapping := (Operational.liftMap law mapping).h
  unit_compatible object := ((Operational.liftUnit law).app object).h
  multiplication_compatible object := ((Operational.liftMultiplication law).app object).h

/-- The actual natural transformation `T D ⟶ D T` for arbitrary deterministic action carriers. -/
noncomputable def lawOverCofree :
    (Cofree.comonad S Actions).toFunctor ⋙ S.termMonad.toFunctor ⟶
      S.termMonad.toFunctor ⋙ (Cofree.comonad S Actions).toFunctor :=
  CoalgebraMonadDistributive.distributive (lifting law) (Cofree.functor S Actions)
    (Cofree.adjunction S Actions)

/-- Its complete tree is actual operational coiteration, coloured by exact free-term root reading. -/
theorem unfolding_readout (X : S.Families) (base : PUnit.{u + 1}) (sort : S.Srt)
    (term : S.polynomial.Free ((Cofree.comonad S Actions).obj X) base sort) :
    (lawOverCofree law).app X base sort term =
      PartialActionTree.coiterate
        ((Operational.liftObject law ((Cofree.functor S Actions).obj X)).str base sort)
        (S.termMonad.map ((Cofree.comonad S Actions).ε.app X) base sort) term :=
  PartialActionTreeCofree.transpose_readout PUnit.{u + 1} (fun _ => S.Srt) (fun _ => Actions)
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

/-- The same complete operational transition behavior is recovered through the cofree readout. -/
theorem operational_recovered (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    (Operational.liftObject law object).str =
      S.termMonad.map ((Cofree.adjunction S Actions).unit.app object).f ≫
        (lawOverCofree law).app object.V ≫
          ((Cofree.functor S Actions).obj (S.termMonad.obj object.V)).str ≫
            (behaviourFunctor S Actions).map
              ((Cofree.comonad S Actions).ε.app (S.termMonad.obj object.V)) :=
  CoalgebraMonadDistributive.lifting_recovered (lifting law) (Cofree.functor S Actions)
    (Cofree.adjunction S Actions) object

/-- Cofree one-step reading recovers the original actual constructor conclusion and flattened target. -/
theorem constructor_recovered (object : Endofunctor.Coalgebra (behaviourFunctor S Actions))
    (base : PUnit.{u + 1}) (sort : S.Srt) (operator : S.Operator sort)
    (children : (position : S.Position operator) →
      S.polynomial.Free object.V base (S.argument operator position)) (action : Actions sort) :
    (((lawOverCofree law).app object.V base sort
      (S.termMonad.map ((Cofree.adjunction S Actions).unit.app object).f base sort
        (IndexedPolynomial.Free.node S.polynomial operator children))).step action).map
          PartialActionTree.root =
      (law.app (S.polynomial.Free object.V) base sort
        ⟨operator, fun position =>
          (children position, Operational.coalgebra law object.str base _ (children position))⟩ action).map
            (IndexedPolynomial.Free.join S.polynomial) := by
  have recovered := congrArg (fun arrow => arrow base sort
    (IndexedPolynomial.Free.node S.polynomial operator children) action) (operational_recovered law object)
  exact recovered.symm.trans (Operational.coalgebra_node law object.str operator children action)

end Mettapedia.OSLF.DeterministicGSOS.Distributive
