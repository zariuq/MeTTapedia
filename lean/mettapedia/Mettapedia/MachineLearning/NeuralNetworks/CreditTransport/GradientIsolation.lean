import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Tactic

/-!
# Gradient-isolation boundaries

Löwe, O'Connor, and Veeling,
*Putting an End to End-to-End: Gradient-Isolated Learning of
Representations* (arXiv:1905.11786), define `GradientBlock(x)` to have the
same forward value `x` and zero reverse gradient.  Their Greedy InfoMax stack
places this boundary between locally trained modules.

This file gives the boundary an exact compositional semantics.  A
`DeclaredReverseMap` carries a forward map and a declared continuous-linear
pullback.  Composition obeys the reverse chain order.  `stopGradient` is
forward identity with zero pullback.  Inserting it between two arbitrary maps
leaves the composite forward value unchanged and makes the entire upstream
pullback zero.  An identity reverse boundary has the same forward value but
does not block credit; a scalar fixture separates the two.

The structure records executable first-order semantics; it does not assert
that the declared pullback is the analytic derivative of the forward map.
The source's InfoNCE mutual-information lower bound, density-ratio optimum,
module-local parameter gradients, asynchronous execution costs, learned
representations, and empirical results are not formalized here.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace GradientIsolation

noncomputable section

/-- A forward computation paired with its declared reverse-mode pullback. -/
structure DeclaredReverseMap
    (Input Output : Type*)
    [NormedAddCommGroup Input] [NormedSpace ℝ Input]
    [NormedAddCommGroup Output] [NormedSpace ℝ Output] where
  forward : Input → Output
  pullback : Input → Output →L[ℝ] Input

namespace DeclaredReverseMap

variable
    {Input Hidden Output : Type*}
    [NormedAddCommGroup Input] [NormedSpace ℝ Input]
    [NormedAddCommGroup Hidden] [NormedSpace ℝ Hidden]
    [NormedAddCommGroup Output] [NormedSpace ℝ Output]

/-- Composition carries forward values left-to-right and reverse credit in
the opposite order. -/
def comp
    (outer : DeclaredReverseMap Hidden Output)
    (inner : DeclaredReverseMap Input Hidden) :
    DeclaredReverseMap Input Output where
  forward input := outer.forward (inner.forward input)
  pullback input :=
    inner.pullback input ∘L outer.pullback (inner.forward input)

@[simp] theorem comp_forward
    (outer : DeclaredReverseMap Hidden Output)
    (inner : DeclaredReverseMap Input Hidden) (input : Input) :
    (outer.comp inner).forward input =
      outer.forward (inner.forward input) := rfl

@[simp] theorem comp_pullback_apply
    (outer : DeclaredReverseMap Hidden Output)
    (inner : DeclaredReverseMap Input Hidden)
    (input : Input) (credit : Output) :
    (outer.comp inner).pullback input credit =
      inner.pullback input
        (outer.pullback (inner.forward input) credit) := rfl

/-- Reverse identity: forward identity and identity pullback. -/
def identity : DeclaredReverseMap Input Input where
  forward input := input
  pullback _ := ContinuousLinearMap.id ℝ Input

/-- Gradient block: forward identity and zero pullback. -/
def stopGradient : DeclaredReverseMap Input Input where
  forward input := input
  pullback _ := 0

@[simp] theorem identity_forward (input : Input) :
    (identity : DeclaredReverseMap Input Input).forward input = input := rfl

@[simp] theorem identity_pullback (input credit : Input) :
    (identity : DeclaredReverseMap Input Input).pullback input credit =
      credit := rfl

@[simp] theorem stopGradient_forward (input : Input) :
    (stopGradient : DeclaredReverseMap Input Input).forward input = input := rfl

@[simp] theorem stopGradient_pullback (input credit : Input) :
    (stopGradient : DeclaredReverseMap Input Input).pullback input credit =
      0 := rfl

/-- A gradient block inserted between arbitrary modules preserves their
composite forward computation exactly. -/
theorem comp_stopGradient_forward_eq
    (outer : DeclaredReverseMap Hidden Output)
    (inner : DeclaredReverseMap Input Hidden)
    (input : Input) :
    (outer.comp (stopGradient.comp inner)).forward input =
      (outer.comp inner).forward input := by
  rfl

/-- The same inserted boundary annihilates every credit signal reaching the
upstream input. -/
theorem comp_stopGradient_pullback_eq_zero
    (outer : DeclaredReverseMap Hidden Output)
    (inner : DeclaredReverseMap Input Hidden)
    (input : Input) :
    (outer.comp (stopGradient.comp inner)).pullback input = 0 := by
  ext credit
  simp [comp, stopGradient]

/-- Pointwise form of upstream gradient isolation. -/
theorem comp_stopGradient_pullback_apply_eq_zero
    (outer : DeclaredReverseMap Hidden Output)
    (inner : DeclaredReverseMap Input Hidden)
    (input : Input) (credit : Output) :
    (outer.comp (stopGradient.comp inner)).pullback input credit = 0 := by
  rw [comp_stopGradient_pullback_eq_zero]
  rfl

/-- Replacing the gradient block by a reverse identity leaves both the forward
map and the original pullback unchanged. -/
theorem comp_identity_eq
    (outer : DeclaredReverseMap Hidden Output)
    (inner : DeclaredReverseMap Input Hidden) :
    outer.comp (identity.comp inner) = outer.comp inner := by
  cases outer with
  | mk outerForward outerPullback =>
    cases inner with
    | mk innerForward innerPullback =>
      rfl

/-- Scalar linear map with its exact constant pullback. -/
def scalarScale (scale : ℝ) : DeclaredReverseMap ℝ ℝ where
  forward input := scale * input
  pullback _ := scale • ContinuousLinearMap.id ℝ ℝ

@[simp] theorem scalarScale_forward (scale input : ℝ) :
    (scalarScale scale).forward input = scale * input := rfl

@[simp] theorem scalarScale_pullback
    (scale input credit : ℝ) :
    (scalarScale scale).pullback input credit = scale * credit := by
  simp [scalarScale]

/-- Positive fixture: a stop-gradient boundary preserves the value of a
two-times-three scalar stack while zeroing its upstream credit. -/
theorem scalar_stopGradient :
    ((scalarScale 3).comp
        (stopGradient.comp (scalarScale 2))).forward 5 = 30 ∧
      ((scalarScale 3).comp
        (stopGradient.comp (scalarScale 2))).pullback 5 1 = 0 := by
  norm_num

/-- Negative boundary: an identity reverse boundary computes the same forward
value but passes the nonzero six-unit upstream pullback. -/
theorem scalar_identity_does_not_isolate :
    ((scalarScale 3).comp
        (identity.comp (scalarScale 2))).forward 5 = 30 ∧
      ((scalarScale 3).comp
        (identity.comp (scalarScale 2))).pullback 5 1 = 6 ∧
      ((scalarScale 3).comp
        (identity.comp (scalarScale 2))).pullback 5 1 ≠ 0 := by
  norm_num

#print axioms comp_stopGradient_forward_eq
#print axioms comp_stopGradient_pullback_eq_zero
#print axioms comp_stopGradient_pullback_apply_eq_zero
#print axioms comp_identity_eq
#print axioms scalar_stopGradient
#print axioms scalar_identity_does_not_isolate

end DeclaredReverseMap

end

end GradientIsolation

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
