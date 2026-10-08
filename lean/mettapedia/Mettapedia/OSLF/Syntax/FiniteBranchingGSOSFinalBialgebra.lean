import Mettapedia.CategoryTheory.CoalgebraMonadBialgebra
import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSDistributive
import Mettapedia.OSLF.Syntax.FiniteBranchingFinalSemantics

/-!
# The final compatible algebra for labelwise finite GSOS

The actual GSOS lifting acts on the independently constructed final
unordered action trees. Finality supplies its complete free-term action,
including all successor sets. The action satisfies the original monad
laws and is terminal among compatible algebras. Complete operational
observation preserves this action; no action alphabet bound or recovery
of erased branch occurrences is needed.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.FinalBialgebra

open _root_.CategoryTheory Mettapedia.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u} (law : Law S Actions)

abbrev CompatibleAlgebra :=
  CoalgebraMonadBialgebra.CompatibleAlgebra (Distributive.lifting law)

def finalAlgebra : CompatibleAlgebra law :=
  CoalgebraMonadBialgebra.finalAlgebra (Distributive.lifting law)
    (FinalSemantics.isFinal S Actions)

def isFinal : Limits.IsTerminal (finalAlgebra law) :=
  CoalgebraMonadBialgebra.isFinalAlgebra (Distributive.lifting law)
    (FinalSemantics.isFinal S Actions)

theorem action_readout :
    (finalAlgebra law).a = FinalSemantics.observe S Actions
      (IndexedGSOS.Operational.liftObject (lawEquiv S Actions law)
        (FinalSemantics.finalObject S Actions)) :=
  FinalSemantics.observe_unique S Actions _ _

theorem action_coiteration (base : PUnit.{u + 1}) (sort : S.Srt)
    (term : S.polynomial.Free (FinalSemantics.finalObject S Actions).V base sort) :
    (finalAlgebra law).a.f base sort term =
      FiniteActionTree.Tree.coiterate
        (Operational.coalgebra law (FinalSemantics.finalObject S Actions).str base sort)
        (fun _ => PUnit.unit) term := by
  rw [action_readout]
  rfl

theorem action_unit :
    S.termMonad.η.app (FinalSemantics.finalObject S Actions).V ≫ (finalAlgebra law).a.f =
      𝟙 (FinalSemantics.finalObject S Actions).V :=
  congrArg Endofunctor.Coalgebra.Hom.f (finalAlgebra law).unit

theorem action_multiplication :
    S.termMonad.μ.app (FinalSemantics.finalObject S Actions).V ≫ (finalAlgebra law).a.f =
      S.termMonad.map (finalAlgebra law).a.f ≫ (finalAlgebra law).a.f :=
  congrArg Endofunctor.Coalgebra.Hom.f (finalAlgebra law).assoc

theorem action_successors (base : PUnit.{u + 1}) (sort : S.Srt)
    (term : S.polynomial.Free (FinalSemantics.finalObject S Actions).V base sort)
    (action : Actions sort) :
    FiniteActionTree.Tree.step ((finalAlgebra law).a.f base sort term) action =
      FinitePowerset.map ((finalAlgebra law).a.f base sort)
        (Operational.coalgebra law (FinalSemantics.finalObject S Actions).str
          base sort term action) :=
  (congrArg (fun arrow => arrow base sort term action) (finalAlgebra law).a.h).symm

def observation (algebra : CompatibleAlgebra law) : algebra ⟶ finalAlgebra law :=
  CoalgebraMonadBialgebra.observation (Distributive.lifting law)
    (FinalSemantics.isFinal S Actions) algebra

theorem observation_readout (algebra : CompatibleAlgebra law) :
    (observation law algebra).f = FinalSemantics.observe S Actions algebra.A :=
  FinalSemantics.observe_unique S Actions _ _

theorem observation_preserves_action (algebra : CompatibleAlgebra law) :
    S.termMonad.map (FinalSemantics.observe S Actions algebra.A).f ≫
        (finalAlgebra law).a.f =
      algebra.a.f ≫ (FinalSemantics.observe S Actions algebra.A).f := by
  have compatible := congrArg Endofunctor.Coalgebra.Hom.f (observation law algebra).h
  change S.termMonad.map (observation law algebra).f.f ≫ (finalAlgebra law).a.f =
    algebra.a.f ≫ (observation law algebra).f.f at compatible
  rw [observation_readout] at compatible
  exact compatible

theorem operational_observation
    (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    S.termMonad.map (FinalSemantics.observe S Actions object).f ≫ (finalAlgebra law).a.f =
      (FinalSemantics.observe S Actions
        (IndexedGSOS.Operational.liftObject (lawEquiv S Actions law) object)).f :=
  congrArg Endofunctor.Coalgebra.Hom.f
    (FinalSemantics.observe_unique S Actions _
      ((Distributive.lifting law).map (FinalSemantics.observe S Actions object) ≫
        (finalAlgebra law).a))

end Mettapedia.OSLF.FiniteBranching.FinalBialgebra
