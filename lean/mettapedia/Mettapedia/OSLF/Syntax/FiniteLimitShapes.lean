import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Elementary shapes for finite-limit generation

Terminal objects, binary products and equalizers generate finite limits. The
same shape family is used for raw, equation-quotient and other small context
categories so their closure constructions can be compared definitionally.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding

open CategoryTheory
open CategoryTheory.Limits

inductive FiniteLimitShape where
  | terminal | binaryProduct | equalizer

def finiteLimitDiagram : FiniteLimitShape → Type
  | .terminal => Discrete PEmpty
  | .binaryProduct => Discrete WalkingPair
  | .equalizer => WalkingParallelPair

instance (shape : FiniteLimitShape) : Category (finiteLimitDiagram shape) := by
  cases shape <;> dsimp [finiteLimitDiagram] <;> infer_instance

end Mettapedia.OSLF.Binding
