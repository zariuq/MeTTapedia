import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Stream.Joined
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.Streams

/-!
# Stream observations in the Megalodon HOTG profile

This comparison reads the candidate's stream programs in the explicitly named
HOTG stream package. Equality of every observation identifies these streams;
agreement at the first position alone does not. It selects no native theory.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.MegalodonHOTG.Stream

open Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Stream
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.Logic.HOL.Embedding
open ZFSetTraceProducts (traceApp traceLam traceApp_graph_beta)
open ZFSetDependentProducts (graph)

universe u

/-! ## Observations determine the stream -/

/-- The value of a stream program is a stream over the numbers. -/
theorem direct_mem (p : StreamExpr) :
    direct p ∈ MegalodonHOTG.Streams.streamSet ZFSet.omega :=
  traceLam_graph_mem fun _ _ => numeral_mem_omega _

/-- The element at position `k`, read by `shead` after `k` uses of `stail`, is the number the
observation of that position runs to. -/
theorem observe_direct (p : StreamExpr) (k : Nat) :
    MegalodonHOTG.Streams.observeSet k (direct p) = numeral (p.observe k) := by
  rw [MegalodonHOTG.Streams.observeSet_eq_app (direct_mem p), direct,
    traceApp_graph_beta _ (numeral_mem_omega k), natOf_numeral]

/-- **`from n` means the numbers from `n` on.** -/
theorem direct_numbersFrom (n : Nat) :
    direct (.numbersFrom n) = MegalodonHOTG.Streams.numbersFromSet n := by
  apply MegalodonHOTG.Streams.streams_ext (direct_mem _) (MegalodonHOTG.Streams.numbersFromSet_mem n)
  intro k
  rw [observe_direct, MegalodonHOTG.Streams.observe_numbersFromSet, observe_numbersFrom]

/-- **`scons a (from n)` means `a` in front of the numbers from `n` on.** -/
theorem direct_sconsFrom (a n : Nat) :
    direct (.scons a (.numbersFrom n)) = MegalodonHOTG.Streams.sconsFromSet a n := by
  apply MegalodonHOTG.Streams.streams_ext (direct_mem _) (MegalodonHOTG.Streams.sconsFromSet_mem a n)
  intro k
  cases k with
  | zero =>
      rw [observe_direct, MegalodonHOTG.Streams.observe_sconsFromSet_zero, StreamExpr.observe]
  | succ k =>
      rw [observe_direct, MegalodonHOTG.Streams.observe_sconsFromSet_succ, StreamExpr.observe,
        observe_numbersFrom]

/-- **Positive example.** `from n` and `scons n (from (suc n))` are one stream: their
observations agree at every position. -/
theorem from_scons_same_stream (n : Nat) :
    direct (.numbersFrom n) = direct (.scons n (.numbersFrom (n + 1))) := by
  rw [direct_numbersFrom, direct_sconsFrom]
  exact MegalodonHOTG.Streams.numbersFrom_eq_sconsFrom n

/-- `from 0` and `scons 0 (from 5)` agree at the first position. -/
theorem from0_agrees_at_first :
    MegalodonHOTG.Streams.observeSet 0 (direct (.numbersFrom 0)) =
      MegalodonHOTG.Streams.observeSet 0 (direct (.scons 0 (.numbersFrom 5))) := by
  rw [direct_numbersFrom, direct_sconsFrom]
  exact MegalodonHOTG.Streams.from0_agrees_at_first

/-- They differ at the next position. -/
theorem from0_differs_at_one :
    MegalodonHOTG.Streams.observeSet 1 (direct (.numbersFrom 0)) ≠
      MegalodonHOTG.Streams.observeSet 1 (direct (.scons 0 (.numbersFrom 5))) := by
  rw [direct_numbersFrom, direct_sconsFrom]
  exact MegalodonHOTG.Streams.from0_differs_at_one

/-- **Negative example.** The two programs are different streams, because they differ at one
position. -/
theorem from0_ne_scons0_from5 :
    direct (.numbersFrom 0) ≠ direct (.scons 0 (.numbersFrom 5)) :=
  MegalodonHOTG.Streams.streams_ne_of_observe_ne from0_differs_at_one

end Mettapedia.Languages.MeTTa.PrimeComparisons.MegalodonHOTG.Stream
