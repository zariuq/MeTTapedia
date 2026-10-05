import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoNativeTransport
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEndpointControls

/-!
# Native observations distinguish an enabled network from its final sends

The existing two-communication example supplies invariant source safety.
Its first firing has an exact endpoint certificate in the rho native logic;
after both firings, neither source nor target has another successor.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoNativeTransportControls

open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEndpoint
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoNativeTransport
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEndpointControls

def initial : QualifiedNetwork :=
  ⟨independent, independent_variable_invariant.flat, independent_variable_invariant.reachableSafe⟩

def middle : QualifiedNetwork := by
  have stable := independent_variable_invariant.after independent_first
  exact ⟨afterFirst, stable.flat, stable.reachableSafe⟩

def final : QualifiedNetwork := by
  have stable := (independent_variable_invariant.after independent_first).after independent_second
  exact ⟨afterBoth, stable.flat, stable.reachableSafe⟩

def endpointPredicate (namespaceName valueName : String) : EquationPredicate canonicalRhoSystem :=
  ⟨fun target => target = canonicalNetwork middle.val namespaceName valueName,
    by intro first second equal; change first = second at equal; cases equal; rfl⟩

theorem first_firing_native_endpoint (namespaceName valueName : String) :
    (semanticDiamond canonicalRhoSystem (endpointPredicate namespaceName valueName)).1
      (canonicalNetwork initial.val namespaceName valueName) := by
  apply (canonicalDiamond_iff initial namespaceName valueName _).mpr
  apply (gsltDiamond_spec networkSystem _ initial).mpr
  exact ⟨middle, independent_first, rfl⟩

private theorem networkStep_hasInput {source target : List Process}
    (selected : NetworkStep source target) :
    ∃ channel binder body, Process.input channel binder body ∈ source := by
  cases selected with
  | comm i hi j hj channel binder datum body input output =>
    exact ⟨channel, binder, body, input ▸ List.getElem_mem hi⟩

theorem final_source_stuck (next : QualifiedNetwork) : ¬ networkSystem.Step final next := by
  intro selected
  obtain ⟨channel, binder, body, membership⟩ := networkStep_hasInput selected
  simp [final, afterBoth] at membership

theorem final_target_stuck (namespaceName valueName : String)
    (predicate : EquationPredicate canonicalRhoSystem) :
    ¬ (semanticDiamond canonicalRhoSystem predicate).1
      (canonicalNetwork final.val namespaceName valueName) := by
  intro possible
  obtain ⟨next, selected, _⟩ :=
    (gsltDiamond_spec networkSystem _ final).mp
      ((canonicalDiamond_iff final namespaceName valueName predicate).mp possible)
  exact final_source_stuck next selected

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoNativeTransportControls
