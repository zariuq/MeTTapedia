import Mettapedia.Languages.MeTTa.Prime.NativeFibredCost
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelExamples

/-!
# Prime-native parallel authority and rho branching worlds

An operational branch and a parallelization license are different kinds of
evidence.  A branch world retains one funded rho step, its exact receipt, and
its target.  A separation witness instead proves that two event occurrences
can inhabit one concurrent wave.

The distinction is constructive.  A separated pair inhabits Prime's native
parallel-license type.  A contested single-purse race has two distinct legal
branch worlds while that license type is empty.  Therefore failure to prove
independence neither rejects the branches nor manufactures a sequential
schedule; ordinary nondeterministic rho execution remains available.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeInteractionParallelWorlds

open Mettapedia.Languages.MeTTa.StagedReflective
open Mettapedia.Languages.MeTTa.Prime.NativeFibredCost
open Mettapedia.Languages.MeTTa.Prime.NativeInteraction
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-! ## Proof-relevant branch worlds as Prime semantic types -/

/-- A single funded rho branch retains its occurrence receipt, target, and
proof-relevant operational step. -/
def branchWorldTy {Ground : Type} (source : CostConfig Ground) :
    familiesCwF.Ty PrimeContext :=
  fun _ =>
    Σ receipt : Multiset (SpendEvent Ground (CostName Ground)),
      Σ target : CostConfig Ground,
        PLift (ParallelCostStep source receipt target)

/-- Internalize one already-established branch as a closed Prime term. -/
def internalBranchWorld {Ground : Type}
    {source target : CostConfig Ground}
    {receipt : Multiset (SpendEvent Ground (CostName Ground))}
    (step : ParallelCostStep source receipt target) :
    familiesCwF.Tm PrimeContext (branchWorldTy source) :=
  fun _ => ⟨receipt, target, ⟨step⟩⟩

/-- Read the target while retaining the full branch world behind it. -/
def branchTarget {Ground : Type} {source : CostConfig Ground}
    (world : familiesCwF.Tm PrimeContext (branchWorldTy source)) :
    CostConfig Ground :=
  (world PUnit.unit).2.1

/-! ## Positive parallel authority and preserved contested worlds -/

namespace Examples

namespace Separated

open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration.Examples

/-- Exact occurrence/resource separation inhabits the Prime-native
parallel-license type. -/
theorem sameChannel_has_native_parallel_authority :
    Nonempty
      ((separationTy source leftEvent rightEvent) PUnit.unit) :=
  ⟨sameChannelSeparation⟩

end Separated

namespace Contested

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ParallelExamples

def aliceWorld :
    familiesCwF.Tm PrimeContext (branchWorldTy contestedSource) :=
  internalBranchWorld contested_alice_branch_preserved

def competitorWorld :
    familiesCwF.Tm PrimeContext (branchWorldTy contestedSource) :=
  internalBranchWorld contested_competitor_branch_preserved

@[simp] theorem aliceWorld_target :
    branchTarget aliceWorld = aliceBranch.target :=
  rfl

@[simp] theorem competitorWorld_target :
    branchTarget competitorWorld = competitorBranch.target :=
  rfl

/-- The retained worlds are observationally distinct at their contracta. -/
theorem branchWorld_targets_differ :
    branchTarget aliceWorld ≠ branchTarget competitorWorld := by
  simpa using contested_branch_targets_differ

/-- The two raw branch worlds coexist even though their shared purse makes
one concurrent wave uninhabitable. -/
theorem raw_worlds_survive_without_parallel_authority :
    Nonempty
        { worlds :
            (familiesCwF.Tm PrimeContext (branchWorldTy contestedSource)) ×
              (familiesCwF.Tm PrimeContext (branchWorldTy contestedSource)) //
          branchTarget worlds.1 ≠ branchTarget worlds.2 } ∧
      ¬ Nonempty
        ((separationTy contestedSource aliceEvent aliceCompetitor)
          PUnit.unit) := by
  constructor
  · exact ⟨⟨(aliceWorld, competitorWorld), branchWorld_targets_differ⟩⟩
  · rintro ⟨separation⟩
    exact contested_branches_are_not_compatible separation.toCompatible

end Contested

end Examples

#print axioms Examples.Separated.sameChannel_has_native_parallel_authority
#print axioms Examples.Contested.branchWorld_targets_differ
#print axioms Examples.Contested.raw_worlds_survive_without_parallel_authority

end Mettapedia.Languages.MeTTa.Prime.NativeInteractionParallelWorlds
