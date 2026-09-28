import Mettapedia.GSLT.Core.PolicyFamilySufficiency
import Mettapedia.TypeTheory.LocallyThinCellReflection

/-!
# Erasures and the observers they retain

An erasure `E : X → Y` discards information.  An observer `O : X → Z`
survives it when `O` factors through `E` (`NonFactorization.Factors E O`):
some readout `Ō : Y → Z` satisfies `Ō (E x) = O x` for every `x`.  This says
nothing about `E` being invertible, only that `O` needs nothing that `E`
discarded.

The criterion, its refutation by a non-trivial fibre and its behaviour under
coarsening are `Mettapedia.GSLT.Core.NonFactorization`.  A family of
observers is a `PolicyFamily`; a readout serves the whole family exactly when
the family's answer vector factors through it
(`PolicyFamily.supportsReadout_iff_vectorFactors`).

This module adds, in the `NonFactorization` namespace, the closure facts that
observer contracts use: every erasure retains itself (`factors_self`), an
observer computed from a retained one is retained (`Factors.post`), and pairing
an erasure with an observation retains that observation (`factors_retain`).  Descent to
the locally thin reflection of a cell fibre is factorization through the
reflection (`factorsThrough_iff_factors`, by definition).

Example: forgetting the cost of a run retains its result but not its cost, and
it does not serve the family of both observers.  Instances on graph walks are
in `Mettapedia.GraphTheory.Walk.ObserverLicences`; guard reuse under world
revision is in `Mettapedia.GSLT.Dynamics.GuardRevision`.
-/

set_option autoImplicit false

universe uX uY uZ uW

/-! ## Closure of factorization

These extend `NonFactorization` so that dot notation on `Factors` finds them. -/

namespace Mettapedia.GSLT.Core.NonFactorization

section Closure

variable {X : Sort uX} {Y : Sort uY} {Z : Sort uZ} {W : Sort uW}

/-- Every erasure retains itself. -/
theorem factors_self (E : X → Y) : Factors E E :=
  ⟨id, fun _ => rfl⟩

/-- An observer computed from a retained observer is retained. -/
theorem Factors.post {E : X → Y} {O : X → Z} (factors : Factors E O) (f : Z → W) :
    Factors E (fun x => f (O x)) :=
  let ⟨recover, recovers⟩ := factors
  ⟨fun y => f (recover y), fun x => congrArg f (recovers x)⟩

end Closure

/-- Pairing an erasure with an observation retains that observation. -/
theorem factors_retain {X : Type uX} {Y : Type uY} {Z : Type uZ} (E : X → Y) (O : X → Z) :
    Factors (fun x => (E x, O x)) O :=
  ⟨Prod.snd, fun _ => rfl⟩

end Mettapedia.GSLT.Core.NonFactorization

namespace Mettapedia.TypeTheory.ObserverErasure

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Core.NonFactorization

/-! ## The locally thin reflection -/

open LocallyThinCellReflection in
/-- Descent to the locally thin reflection of a cell fibre is factorization
through the reflection. -/
theorem factorsThrough_iff_factors {Cell : Type uX} {Output : Type uZ}
    (observe : Cell → Output) :
    FactorsThrough observe ↔ Factors (reflect (Cell := Cell)) observe :=
  Iff.rfl

/-! ## Results with costs -/

section Cost

/-- Forgetting the cost of a run `(result, cost)`. -/
def forgetCost (run : Nat × Nat) : Nat := run.1

/-- The result survives forgetting the cost. -/
theorem result_factors : Factors forgetCost (fun run : Nat × Nat => run.1) :=
  ⟨id, fun _ => rfl⟩

/-- Two runs with one result and different costs. -/
def costFiber : NonTrivialFiber forgetCost (fun run : Nat × Nat => run.2) where
  left := (7, 3)
  right := (7, 5)
  sameShadow := rfl
  differentValue := by decide

/-- The cost does not survive forgetting it. -/
theorem cost_not_factors : ¬ Factors forgetCost (fun run : Nat × Nat => run.2) :=
  costFiber.not_factors

/-- The two observers of a run. -/
inductive RunObservation where
  | result
  | cost
  deriving DecidableEq

/-- The result and cost observers as one policy family. -/
def runObservers : PolicyFamily (Nat × Nat) where
  Policy := RunObservation
  Result := fun _ => Nat
  decide := fun
    | .result => Prod.fst
    | .cost => Prod.snd

/-- Forgetting the cost serves the family that asks only for the result. -/
theorem resultFamily_supported :
    (runObservers.reindex fun _ : Unit => RunObservation.result).SupportsReadout
      forgetCost :=
  ⟨{ run := fun _ result => result
     agrees := fun _ _ => rfl }⟩

/-- Adding the cost observer withdraws that support: one collision of the
readout is separated by the cost policy. -/
theorem costFamily_not_supported : ¬ runObservers.SupportsReadout forgetCost := by
  apply runObservers.not_supportsReadout_of_policy_collision forgetCost
    (first := (7, 3)) (second := (7, 5)) rfl .cost
  change (3 : Nat) ≠ 5
  decide

end Cost

#print axioms Mettapedia.GSLT.Core.NonFactorization.factors_self
#print axioms Mettapedia.GSLT.Core.NonFactorization.Factors.post
#print axioms Mettapedia.GSLT.Core.NonFactorization.factors_retain
#print axioms factorsThrough_iff_factors
#print axioms result_factors
#print axioms cost_not_factors
#print axioms resultFamily_supported
#print axioms costFamily_not_supported

end Mettapedia.TypeTheory.ObserverErasure
