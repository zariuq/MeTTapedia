import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WirePlanSupport

/-! Factored support proofs for the shared class emitter. The original
freshness predicate is unchanged. Fixed runtime/entry checks are separated
from universal support laws for the encoded plan and standard-form data. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionSupport

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open CompleteEmission Eval

private theorem wire_tags_no_colon : ∀ tag ∈ WirePlanSupport.tags, ':' ∉ tag.toList := by decide +kernel

private theorem entry_contains_colon (name : String) : ∀ entry ∈ entries name, ':' ∈ entry.toList := by
  intro entry member
  simp only [entries,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals simp [beginHead,runHead,exploreHead,edgesHead,String.toList_append]

theorem wire_supported (name : String) : WirePlanSupport.Supported (allowed name) := by
  intro tag member
  have absent := wire_tags_no_colon tag member
  have missing : tag ∉ entries name := by
    intro present
    exact absent (entry_contains_colon name tag present)
  simpa [allowed] using missing

theorem plan_supported (spec : Spec) (name : String) : codeWithin (allowed name) (planAtom spec) = true := by
  rw [planAtom,WireCodeSupport.codeWithin_encode]
  exact WirePlanSupport.plan _ (wire_supported name) _ _ _ _

theorem standard_supported (spec : Spec) (name : String) (standard : spec.mode = .standard) :
    codeWithin (allowed name) (standardAtom spec) = true := by
  rw [standardAtom,WireCodeSupport.codeWithin_encode,standard]
  exact WirePlanSupport.standard _ (wire_supported name) _

def wrapperHeads : List String :=
  ["let","gslt:runner:begin","gslt:runner:advance","gslt:runner:trace",
    "gslt:explore:begin","gslt:explore:rounds","gslt:explore:states","gslt:explore:edges"]

/-- Fixed entry/runtime checks, independent of a plan and its encoded size. -/
def entryChecks (name : String) : Bool :=
  (entries name).Nodup &&
  (entries name).all (fun head => !specialHeads.contains head && !ioHead head && !StdLib.known head) &&
  runtime.equations.all (fun equation => allowed name equation.head && codeWithin (allowed name) equation.body) &&
  runtime.declarations.all (declaredHeadAllowed name) && wrapperHeads.all (allowed name)

theorem namesFresh_of_entryChecks (spec : Spec) (name : String) (standard : spec.mode = .standard)
    (checked : entryChecks name = true) : namesFresh spec name .classes = true := by
  have plan := plan_supported spec name
  have normal := standard_supported spec name standard
  simp only [entryChecks,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨⟨distinct,heads⟩,equations⟩,declarations⟩,wrappers⟩ := checked
  simp only [wrapperHeads,List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true] at wrappers
  obtain ⟨letAllowed,beginAllowed,advanceAllowed,traceAllowed,exploreAllowed,roundsAllowed,statesAllowed,edgesAllowed⟩ := wrappers
  unfold namesFresh
  simp only [distinct,heads,equations,declarations,letAllowed,Bool.true_and]
  simp only [beginBody,runBody,exploreBody,edgesBody,codeWithin,expressionHeadWithin,atomsWithin,
    backendAtom,plan,normal,beginAllowed,advanceAllowed,traceAllowed,exploreAllowed,roundsAllowed,
    statesAllowed,edgesAllowed,letAllowed,Bool.true_and,Bool.and_true]
  simp +decide

#print axioms plan_supported
#print axioms namesFresh_of_entryChecks

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionSupport
