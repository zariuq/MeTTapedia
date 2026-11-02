import Mettapedia.Languages.Micromath.SharedChecking
import Mettapedia.Languages.Micromath.CheckingControls

/-!
# Shared Micromath proof graphs and exact premise references

One checked derivation is cited in two premise positions. The stored graph
retains both references without duplicating that subproof. Future addresses,
changed results and the semantically invalid shared-input join are refused.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.Micromath.SharedCheckingControls
open SharedChecking Checking KernelControls

def graph : List (Node Nat) := [
  ⟨main,.assumption,[],0⟩,⟨left,.projectionFirst,[],1⟩,⟨right,.projectionSecond,[],2⟩,
  ⟨packed,.assumption,[],3⟩,⟨transferred,.substitute1,[0,1,2,3],4⟩,
  ⟨packed,.substitute2,[0,1,2,4],5⟩]
def cache : Array Claim := #[main,left,right,packed,transferred,packed]
theorem graph_accepted : replay CheckingControls.seeds graph = some cache := by decide +kernel
theorem graph_root_holds : Holds boolAssignment packed :=
  root_holds boolAssignment bool_projects CheckingControls.seeds CheckingControls.seeds_hold graph_accepted (by rfl : cache[5]? = some packed)

def sharedGraph : List (Node Nat) := [
  ⟨diagonalAnd,.assumption,[],0⟩,⟨firstIdentity,.assumption,[],1⟩,
  ⟨diagonalAnd,.substitute1,[0,1,1,1],2⟩]
theorem repeated_reference_accepted : replay [diagonalAnd,firstIdentity] sharedGraph =
    some #[diagonalAnd,firstIdentity,diagonalAnd] := by decide +kernel
theorem three_occurrences_one_parent : Mettapedia.Logic.DerivationGraph.lookupPremises #[diagonalAnd,firstIdentity] [1,1,1] =
    some [firstIdentity,firstIdentity,firstIdentity] := rfl

theorem forward_reference_refused : replay CheckingControls.seeds
    [⟨main,.assumption,[],0⟩,⟨transferred,.substitute1,[0,2,3,4],1⟩] = none := by decide +kernel
theorem wrong_root_claim_refused : (cache[4]?) ≠ some projectionCollapse := by decide +kernel
theorem wrong_shared_input_refused : replay CheckingControls.wrongJoinSeeds [
    ⟨diagonalAnd,.assumption,[],0⟩,⟨firstIdentity,.assumption,[],1⟩,
    ⟨differentFirstInput,.assumption,[],2⟩,⟨falseMixedAnd,.substitute1,[0,1,2,1],3⟩] = none := by decide +kernel

#print axioms graph_root_holds
#print axioms repeated_reference_accepted
#print axioms wrong_shared_input_refused
end Mettapedia.Languages.Micromath.SharedCheckingControls
