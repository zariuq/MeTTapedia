import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingUnaryOperational
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeValueObservation

/-!
# Returned-function adequacy through every tuple-protocol phase

The source observation is its independently defined returned lambda. The
target observation is a real public receiver on the reserved result channel.
Private tuple delivery may delay that receiver, but cannot invent it. The
generated finite-reachability native predicates therefore agree in both
directions, including actual intermediate states and structural representatives.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingUnaryNative

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda NamePassingUnaryForward NamePassingUnaryOperational
open MonadicProtocol.RuntimeValueObservation

def targetPredicate (Γ : Ctx sig) :
    EquationPredicate (NativeTypes.operationalTheory (.nm :: Γ)) :=
  ActiveObservation.predicate .input1 .zero

theorem current_return_reflected {Γ : Ctx sig} {source : Expr Γ} {current : Proc (.nm :: Γ)}
    (related : Related source current) (observed : (targetPredicate Γ).1 current) :
    (NamePassingValueNative.sourcePredicate Γ).1 source := by
  obtain ⟨before⟩ := related
  have returned := MonadicProtocol.RuntimeValueObservation.current_return_reflected source
    (references Γ) .zero (references_fresh Γ) before (.refl _) observed
  exact (NamePassing.ValueObservation.returning_iff source).mpr returned

/-- Exactly the existing occurrence debt suffices to make an already
returned function visible. No source transition is performed by this block. -/
theorem current_return_realized {Γ : Ctx sig} {source : Expr Γ} {current : Proc (.nm :: Γ)}
    (related : Related source current) (returned : (NamePassingValueNative.sourcePredicate Γ).1 source) :
    (semanticDiamond (NativeTypes.operationalTheory (.nm :: Γ)).closure (targetPredicate Γ)).1 current := by
  obtain ⟨before⟩ := related
  obtain ⟨endpoint, path, observed, _⟩ :=
    MonadicProtocol.RuntimeValueObservation.current_return_realized source (references Γ) .zero
      (references_fresh Γ) before (.refl _)
      ((NamePassing.ValueObservation.returning_iff source).mp returned)
  exact (closure_nativeDiamond_iff (NativeTypes.operationalTheory (.nm :: Γ)) _ current).mpr
    ⟨endpoint, executionPathToMultiStep path, observed⟩

/-- This is the two-sided allowed-observer theorem, rather than equality
of instantaneous readiness during private delivery. -/
theorem native_may_return_iff {Γ : Ctx sig} {source : Expr Γ} {current : Proc (.nm :: Γ)}
    (related : Related source current) :
    (semanticDiamond (NamePassingEnvironmentEquationsNative.sourceTheory Γ).closure
      (NamePassingValueNative.sourcePredicate Γ)).1 source ↔
    (semanticDiamond (NativeTypes.operationalTheory (.nm :: Γ)).closure
      (targetPredicate Γ)).1 current :=
  (correspondence Γ).nativeDiamond_iff_delayed
    (NamePassingValueNative.sourcePredicate Γ) (targetPredicate Γ)
    (fun comparison observed => current_return_reflected comparison observed)
    (fun comparison observed => current_return_realized comparison observed) related

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingUnaryNative
