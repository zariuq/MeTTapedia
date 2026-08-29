import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitPresentCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitAbsentCanary

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitResultCanary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitInputData
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitPresentCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitAbsentCanary

theorem speculative_hit_pushes_exact_node :
    resolvedStackCell ∈ speculativeHitAfterDirect :=
  direct_hit_pushes_exact_node

theorem speculative_hit_leaves_no_lookup_request :
    directLookupOne ∉ speculativeHitAfterDirect :=
  direct_hit_leaves_no_lookup_request

theorem speculative_hit_leaves_no_pending_step :
    directStepPending ∉ speculativeHitAfterDirect :=
  direct_hit_leaves_no_pending_step

/-- Observable representation boundary of the generated direct proof-cell
transition.  It includes both stack views, the resumed scanner and successor
machine, and absence of the consumed request state. -/
def DirectProofHitFrame (space : List Atom) : Prop :=
  resolvedStackCell ∈ space ∧
    directNormalStackCell ∈ space ∧
    directNextMachine ∈ space ∧
    directResumedScan ∈ space ∧
    directStepPending ∉ space ∧
    directLookupOne ∉ space ∧
    machineWithTwoHeapEntries ∉ space

theorem speculative_hit_has_exact_observable_frame :
    DirectProofHitFrame speculativeHitAfterDirect := by
  rcases direct_hit_publishes_complete_continuation with
    ⟨nextMachine, normalStack, scan⟩
  exact ⟨direct_hit_pushes_exact_node, normalStack, nextMachine, scan,
    direct_hit_leaves_no_pending_step,
    direct_hit_leaves_no_lookup_request,
    direct_hit_consumes_old_machine⟩

#print axioms speculative_hit_pushes_exact_node
#print axioms speculative_hit_leaves_no_lookup_request
#print axioms speculative_hit_leaves_no_pending_step
#print axioms speculative_hit_has_exact_observable_frame

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitResultCanary
