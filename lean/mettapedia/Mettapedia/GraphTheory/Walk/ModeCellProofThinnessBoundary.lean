import Mettapedia.GraphTheory.Walk.NativeTypeExamples
import Mettapedia.TypeTheory.OperationalIntensionalExtensionalCellThinness

/-!
# Thin mode cells and proof-relevant graph walks are independent

The graph-walk native type theory retains distinct reachability proofs at one
fixed endpoint boundary.  This module exhibits a direct walk and a longer
detour from vertex zero to vertex two in the same graph.  Both have generated
native certificates, while their lengths differ.

That proof relevance lives inside an endpoint-indexed dependent fibre.  It
does not automatically create two transformations between the same
modalities.  The graph proof-length observer fails to descend through a thin
reflection of its proof fibre even while the operational-to-extensional factor
cell remains inhabited in the locally thin mode theory.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.Walk
namespace ModeCellProofThinnessBoundary

open Examples
open NativeTypeTheory
open ProofTheory
open SimpleGraph
open Mettapedia.TypeTheory.LocallyThinCellReflection
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalCellThinness
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalTwoComputad

/-! ## Two authentic native proofs in one endpoint fibre -/

/-- The direct two-edge reachability proof from zero to two. -/
def directProof : NativeProof pathGraph vertex0 vertex2 :=
  NativeProof.ofWalk pathGraph walk02

/-- A four-edge proof with a final two-edge detour from two through one and
back to two. -/
def detourWalk : pathGraph.Walk vertex0 vertex2 :=
  walk02.append (walk12.reverse.append walk12)

/-- The longer walk also receives a certificate from the generated native
walk judgment. -/
def detourProof : NativeProof pathGraph vertex0 vertex2 :=
  NativeProof.ofWalk pathGraph detourWalk

/-- Observe exact edge count inside the fixed endpoint proof fibre. -/
def proofLength (proof : NativeProof pathGraph vertex0 vertex2) : Nat :=
  proof.walk.length

@[simp] theorem directProof_length : proofLength directProof = 2 := by
  rfl

@[simp] theorem detourProof_length : proofLength detourProof = 4 := by
  simp only [proofLength, detourProof, NativeProof.ofWalk, detourWalk,
    Walk.length_append, Walk.length_reverse, walk02, walk12,
    Walk.length_cons, Walk.length_nil]

/-- Both endpoint-compatible proof objects satisfy the generated native
judgment. -/
theorem direct_and_detour_are_native :
    NativeWalk pathGraph pathGraph Hom.id vertex0 vertex2 directProof.term /\
      NativeWalk pathGraph pathGraph Hom.id vertex0 vertex2 detourProof.term :=
  ⟨directProof.native, detourProof.native⟩

/-- Exact work separates the two proof objects despite their common endpoint
index. -/
theorem directProof_ne_detourProof : directProof ≠ detourProof := by
  intro equality
  have lengthEquality := congrArg proofLength equality
  simp at lengthEquality

/-- Length is a genuine observer on the fixed endpoint proof fibre. -/
def lengthDiscriminator :
    Discriminator (NativeProof pathGraph vertex0 vertex2) Nat where
  left := directProof
  right := detourProof
  observe := proofLength
  separates := by simp

/-- Thinning the reachability-proof fibre destroys its exact-work observer. -/
theorem proof_length_does_not_factor_through_thin_reflection :
    ¬ FactorsThrough proofLength :=
  lengthDiscriminator.not_factorsThrough

/-! ## Separation from mode-cell thinness -/

/-- The graph proof fibre can remain proof-relevant while the selected mode
factor cell remains inhabited and thin. -/
theorem graph_proof_mode_cell_thinness_boundary :
    Nonempty
        (ThinReflection
          (ModeCell evidenceReadoutPath observePath)) /\
      Subsingleton
        (ThinReflection
          (ModeCell evidenceReadoutPath observePath)) /\
      NativeWalk pathGraph pathGraph Hom.id vertex0 vertex2 directProof.term /\
      NativeWalk pathGraph pathGraph Hom.id vertex0 vertex2 detourProof.term /\
      ¬ FactorsThrough proofLength :=
  ⟨reflected_factor_cell_inhabited,
    inferInstance,
    directProof.native,
    detourProof.native,
    proof_length_does_not_factor_through_thin_reflection⟩

/-! ## Axiom audit -/

#print axioms directProof_length
#print axioms detourProof_length
#print axioms direct_and_detour_are_native
#print axioms directProof_ne_detourProof
#print axioms proof_length_does_not_factor_through_thin_reflection
#print axioms graph_proof_mode_cell_thinness_boundary

end ModeCellProofThinnessBoundary
end Mettapedia.GraphTheory.Walk
