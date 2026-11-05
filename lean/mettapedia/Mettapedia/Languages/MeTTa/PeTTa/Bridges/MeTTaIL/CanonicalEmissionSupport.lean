import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionSupport

/-! Canonical commit data preserves code support for every plan and name
table. Concrete emitters check fixed runtime/entry metadata separately,
without expanding the plan again inside each generated entry body. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionSupport

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open CompleteEmission Eval WireCodeSupport

theorem canonical_wire_supported (allowed : String → Bool) (supported : WirePlanSupport.Supported allowed)
    (plan : GeneralExecutionAdmission.Plan) (table : List String) :
    check allowed (StandardWire.canonicalTerm plan table) = true := by
  apply WirePlanSupport.app allowed supported "Canonical" (by decide)
  have laws := WirePlanSupport.list allowed supported StandardWire.lawTerm (Complete.Normalized.laws plan)
    (fun item _ => WirePlanSupport.law allowed supported item)
  have extrusions := WirePlanSupport.list allowed supported StandardWire.extrusionTerm (Complete.Normalized.extrusions plan)
    (fun item _ => WirePlanSupport.extrusion allowed supported item)
  have names := WirePlanSupport.list allowed supported Term.string table (fun item _ => rfl)
  simp only [checkMany, laws, extrusions, names, Bool.true_and]

theorem canonical_supported (spec : Spec) (name : String) (canonical : spec.mode = .canonical) :
    codeWithin (allowed name) (standardAtom spec) = true := by
  rw [standardAtom, WireCodeSupport.codeWithin_encode, canonical]
  exact canonical_wire_supported _ (wire_supported name) _ _

theorem namesFresh_of_canonical_entryChecks (spec : Spec) (name : String) (canonical : spec.mode = .canonical)
    (checked : entryChecks name = true) : namesFresh spec name .classes = true := by
  have plan := plan_supported spec name
  have normal := canonical_supported spec name canonical
  simp only [entryChecks, Bool.and_eq_true] at checked
  obtain ⟨⟨⟨⟨distinct, heads⟩, equations⟩, declarations⟩, wrappers⟩ := checked
  simp only [wrapperHeads, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at wrappers
  obtain ⟨letAllowed, beginAllowed, advanceAllowed, traceAllowed, exploreAllowed, roundsAllowed, statesAllowed, edgesAllowed⟩ := wrappers
  unfold namesFresh
  simp only [distinct, heads, equations, declarations, letAllowed, Bool.true_and]
  simp only [beginBody, runBody, exploreBody, edgesBody, codeWithin, expressionHeadWithin, atomsWithin,
    backendAtom, plan, normal, beginAllowed, advanceAllowed, traceAllowed, exploreAllowed, roundsAllowed,
    statesAllowed, edgesAllowed, letAllowed, Bool.true_and, Bool.and_true]
  simp +decide

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionSupport
