import Mettapedia.TypeTheory.ObserverErasure
import Mettapedia.GraphTheory.Walk.ModeCellProofThinnessBoundary

/-!
# Observers of walks on the path graph

Erasing which walk witnesses reachability retains the endpoint observer and not
the edge-count observer: the direct walk and the detour from vertex zero to
vertex two have two and four edges. Retaining the edge count restores that
observer and everything computed from it.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.Walk.ObserverLicences

open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.TypeTheory.ObserverErasure

open Mettapedia.GraphTheory.Walk
open Mettapedia.GraphTheory.Walk.Examples
open Mettapedia.GraphTheory.Walk.ModeCellProofThinnessBoundary
open Mettapedia.GraphTheory.Walk.ProofTheory
open Mettapedia.TypeTheory.LocallyThinCellReflection

/-- Which walk witnesses reachability from vertex zero to vertex two. -/
abbrev Witness := NativeProof pathGraph vertex0 vertex2

/-- The endpoint observer: the walk ends at vertex two. -/
def endpoint (_ : Witness) : Unit := ()

/-- Erasing the walk retains the endpoint observer. -/
theorem endpoint_factors : Factors (reflect (Cell := Witness)) endpoint :=
  ⟨fun _ => (), fun _ => rfl⟩

/-- Erasing the walk does not retain the edge-count observer: the direct walk
and the detour reach the same endpoint with two and four edges. -/
theorem proofLength_not_factors : ¬ Factors (reflect (Cell := Witness)) proofLength :=
  (factorsThrough_iff_factors proofLength).not.mp
    proof_length_does_not_factor_through_thin_reflection

/-- Keeping the edge count alongside the erasure restores the edge-count
observer and everything computed from it, such as a bound on the work. -/
theorem boundedWork_factors_when_retained :
    Factors (fun w : Witness => (reflect w, proofLength w))
      (fun w => decide (proofLength w ≤ 3)) :=
  (factors_retain (reflect (Cell := Witness)) proofLength).post (fun n => decide (n ≤ 3))

#print axioms endpoint_factors
#print axioms proofLength_not_factors
#print axioms boundedWork_factors_when_retained

end Mettapedia.GraphTheory.Walk.ObserverLicences
