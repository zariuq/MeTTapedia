import Mettapedia.CategoryTheory.CoalgebraMonadBialgebra
import Mettapedia.OSLF.Syntax.DeterministicGSOSDistributive
import Mettapedia.OSLF.Syntax.DeterministicGSOSFinalSemantics

/-!
# The actual final compatible GSOS algebra

The deterministic GSOS lifting acts on the independently constructed
final action-tree coalgebra. Its unique final coalgebra map supplies the
free-term algebra action. The unit and multiplication laws, terminality
among compatible algebras and algebraic final observation are earned
from the shared categorical construction. Complete action and observation
readouts identify these maps with actual operational path unfolding.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.FinalBialgebra

open _root_.CategoryTheory Mettapedia.CategoryTheory

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u} (law : Law S Actions)

/-- The compatible-algebra category retains the actual GSOS behavior on free terms. -/
abbrev CompatibleAlgebra :=
  CoalgebraMonadBialgebra.CompatibleAlgebra (Distributive.lifting law)

/-- The actual final behavior tree carries its earned free-term algebra structure. -/
noncomputable def finalAlgebra : CompatibleAlgebra law :=
  CoalgebraMonadBialgebra.finalAlgebra (Distributive.lifting law)
    (FinalSemantics.isFinal S Actions)

/-- Finality holds in the genuine category of compatible algebras. -/
noncomputable def isFinal : Limits.IsTerminal (finalAlgebra law) :=
  CoalgebraMonadBialgebra.isFinalAlgebra (Distributive.lifting law)
    (FinalSemantics.isFinal S Actions)

/-- The action is the actual final map of the operational lifted coalgebra. -/
theorem action_readout :
    (finalAlgebra law).a = FinalSemantics.observe S Actions
      (Operational.liftObject law (FinalSemantics.finalObject S Actions)) :=
  FinalSemantics.observe_unique S Actions _ _

/-- Every supplied free constructor tree is unfolded with its exact operational successors. -/
theorem action_coiteration (base : PUnit.{u + 1}) (sort : S.Srt)
    (term : S.polynomial.Free (FinalSemantics.finalObject S Actions).V base sort) :
    (finalAlgebra law).a.f base sort term =
      PartialActionTree.coiterate
        ((Operational.liftObject law (FinalSemantics.finalObject S Actions)).str base sort)
        (fun _ => PUnit.unit) term := by
  rw [action_readout]
  rfl

/-- The original free-monad unit is preserved by the complete behavior action. -/
theorem action_unit :
    S.termMonad.η.app (FinalSemantics.finalObject S Actions).V ≫ (finalAlgebra law).a.f =
      𝟙 (FinalSemantics.finalObject S Actions).V :=
  congrArg Endofunctor.Coalgebra.Hom.f (finalAlgebra law).unit

/-- Actual flattening and algebraic composition have equal complete final behavior. -/
theorem action_multiplication :
    S.termMonad.μ.app (FinalSemantics.finalObject S Actions).V ≫ (finalAlgebra law).a.f =
      S.termMonad.map (finalAlgebra law).a.f ≫ (finalAlgebra law).a.f :=
  congrArg Endofunctor.Coalgebra.Hom.f (finalAlgebra law).assoc

/-- The observation retains both its coalgebra and free-algebra compatibility. -/
noncomputable def observation (algebra : CompatibleAlgebra law) : algebra ⟶ finalAlgebra law :=
  CoalgebraMonadBialgebra.observation (Distributive.lifting law)
    (FinalSemantics.isFinal S Actions) algebra

theorem observation_readout (algebra : CompatibleAlgebra law) :
    (observation law algebra).f = FinalSemantics.observe S Actions algebra.A :=
  FinalSemantics.observe_unique S Actions _ _

/-- Every independent compatible action commutes with complete final observation. -/
theorem observation_preserves_action (algebra : CompatibleAlgebra law) :
    S.termMonad.map (FinalSemantics.observe S Actions algebra.A).f ≫
        (finalAlgebra law).a.f =
      algebra.a.f ≫ (FinalSemantics.observe S Actions algebra.A).f := by
  have compatible := congrArg Endofunctor.Coalgebra.Hom.f (observation law algebra).h
  change S.termMonad.map (observation law algebra).f.f ≫ (finalAlgebra law).a.f =
    algebra.a.f ≫ (observation law algebra).f.f at compatible
  rw [observation_readout] at compatible
  exact compatible

/-- Observing the inputs and then acting agrees with observing the complete operational term. -/
theorem operational_observation (object : Endofunctor.Coalgebra (behaviourFunctor S Actions)) :
    S.termMonad.map (FinalSemantics.observe S Actions object).f ≫ (finalAlgebra law).a.f =
      (FinalSemantics.observe S Actions (Operational.liftObject law object)).f := by
  exact congrArg Endofunctor.Coalgebra.Hom.f
    (FinalSemantics.observe_unique S Actions (Operational.liftObject law object)
      ((Distributive.lifting law).map (FinalSemantics.observe S Actions object) ≫
        (finalAlgebra law).a))

end Mettapedia.OSLF.DeterministicGSOS.FinalBialgebra
