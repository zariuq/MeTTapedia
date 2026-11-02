import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CanonicalEmissionSupport

/-! Support of canonical class-entry bodies is parametric in the plan and
table. Library linkage checks only the fixed call vocabulary and namespace
ownership, without reducing an inlined compiler plan inside every body. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionCodeSupport

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval CompleteEmission WireCodeSupport

theorem plan_supported (spec : Spec) (allowed : String → Bool) (wire : WirePlanSupport.Supported allowed) :
    codeWithin allowed (planAtom spec) = true := by
  rw [planAtom, codeWithin_encode]
  exact WirePlanSupport.plan allowed wire _ _ _ _

theorem canonical_supported (spec : Spec) (allowed : String → Bool) (wire : WirePlanSupport.Supported allowed)
    (canonical : spec.mode = .canonical) : codeWithin allowed (standardAtom spec) = true := by
  rw [standardAtom, codeWithin_encode, canonical]
  exact CompleteEmissionSupport.canonical_wire_supported allowed wire _ _

theorem entry_bodies_supported (spec : Spec) (name : String) (allowed : String → Bool)
    (wire : WirePlanSupport.Supported allowed) (canonical : spec.mode = .canonical)
    (wrappers : CompleteEmissionSupport.wrapperHeads.all allowed = true) :
    (program spec name .classes).equations.all (fun equation => codeWithin allowed equation.body) = true := by
  have plan := plan_supported spec allowed wire
  have normal := canonical_supported spec allowed wire canonical
  simp only [CompleteEmissionSupport.wrapperHeads, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at wrappers
  obtain ⟨letAllowed, beginAllowed, advanceAllowed, traceAllowed, exploreAllowed, roundsAllowed, statesAllowed, edgesAllowed⟩ := wrappers
  simp only [program, List.all_cons, List.all_nil, Bool.and_true, beginEquation, runEquation,
    exploreEquation, edgesEquation, beginBody, runBody, exploreBody, edgesBody,
    codeWithin, expressionHeadWithin, atomsWithin, backendAtom, plan, normal,
    letAllowed, beginAllowed, advanceAllowed, traceAllowed, exploreAllowed, roundsAllowed, statesAllowed, edgesAllowed,
    Bool.true_and, Bool.and_true]
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionCodeSupport
