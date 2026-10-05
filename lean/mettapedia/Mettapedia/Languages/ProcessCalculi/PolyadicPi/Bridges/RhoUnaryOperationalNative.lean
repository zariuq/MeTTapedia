import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryForward
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryPublicObservation
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInputObservation

/-!
# Native observations through the complete unary-to-rho correspondence

The independently proved forward and backward execution laws use the same
runtime inventory and source readout. Every related administrative phase can
implement every next source step, and every actual target step reads back
without changing its supplied endpoint. Public output and input observations
are reflected immediately and realized after finite administration. Their
generated finite-reachability types therefore agree in both directions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryOperationalNative

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryReadback RhoUnaryWorld

/-- Both laws concern the existing authored source and sorted rho GSLTs.
The relation includes initialization, rearming and all supplied equation
representatives, rather than restricting execution to a selected schedule. -/
def correspondence {Γ : Ctx sig} (world : SeedWorld Γ) :
    OperationalCorrespondence (NativeTypes.operationalTheory Γ) Target where
  toOperationalReadback := comparison world
  forward := by
    intro origin after current related firing
    obtain ⟨before⟩ := related
    obtain ⟨final, path, witness, _⟩ := RhoUnaryForward.forward before firing
    exact ⟨final, ⟨path⟩, witness⟩

theorem native_may_output_iff {Γ : Ctx sig} (world : SeedWorld Γ)
    (channel : Var Γ .nm) {origin : Proc Γ} {current : TargetProcess}
    (related : Related world origin current) :
    (semanticDiamond (NativeTypes.operationalTheory Γ).closure
      (PublicOutputObservation.closurePredicate channel)).1 origin ↔
    (semanticDiamond Target.closure
      (RhoUnaryPublicObservation.targetPredicate world channel)).1 current :=
  (correspondence world).nativeDiamond_iff_delayed
    (PublicOutputObservation.closurePredicate channel)
    (RhoUnaryPublicObservation.targetPredicate world channel)
    (fun relation observed => RhoUnaryPublicObservation.related_output_reflected world channel relation observed)
    (fun relation observed => RhoUnaryPublicObservation.native_current_output_preserved world channel relation observed)
    related

theorem native_may_input_iff {Γ : Ctx sig} (world : SeedWorld Γ)
    (channel : Var Γ .nm) {origin : Proc Γ} {current : TargetProcess}
    (related : Related world origin current) :
    (semanticDiamond (NativeTypes.operationalTheory Γ).closure
      (ActiveObservation.predicate .input1 channel)).1 origin ↔
    (semanticDiamond Target.closure
      (RhoUnaryInputObservation.targetPredicate world channel)).1 current :=
  (correspondence world).nativeDiamond_iff_delayed
    (ActiveObservation.predicate .input1 channel)
    (RhoUnaryInputObservation.targetPredicate world channel)
    (fun relation observed => RhoUnaryInputObservation.related_input_reflected world channel relation observed)
    (fun relation observed => RhoUnaryInputObservation.native_current_input_preserved world channel relation observed)
    related

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryOperationalNative
