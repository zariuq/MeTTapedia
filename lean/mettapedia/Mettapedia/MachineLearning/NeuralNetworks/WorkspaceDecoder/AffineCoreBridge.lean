import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.StateSpaceScan
import Mettapedia.Algebra.AffineSummary

/-!
# Continuous state-space transitions realize the shared affine core

Continuity is retained in the neural representation; the ordered-composition
law lives in the more general additive algebra. The scalar compiler and the
state-space scan therefore have checked maps to the same core, without
identifying exact integer arithmetic with floating-point execution.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.AffineTransition

open Mettapedia.Algebra

variable {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]

noncomputable def toCore (f : AffineTransition State) : AffineAction State where
  linear := f.linear.toLinearMap.toAddMonoidHom
  offset := f.offset

@[simp] theorem toCore_act (f : AffineTransition State) (x : State) :
    f.toCore.act x = f.act x := rfl

theorem toCore_compose (f g : AffineTransition State) :
    (f.compose g).toCore = f.toCore.compose g.toCore := rfl

theorem toCore_injective : Function.Injective (toCore (State := State)) := by
  intro f g h
  apply AffineTransition.ext'
  · ext x
    exact congrArg (fun c : AffineAction State => c.linear x) h
  · exact congrArg AffineAction.offset h

/-- Derive the continuous representation's associativity from the common
additive theorem via a faithful, composition-preserving map. -/
theorem compose_assoc_from_core (f g h : AffineTransition State) :
    (f.compose g).compose h = f.compose (g.compose h) := by
  apply toCore_injective
  simp only [toCore_compose, AffineAction.compose_assoc]

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.AffineTransition
