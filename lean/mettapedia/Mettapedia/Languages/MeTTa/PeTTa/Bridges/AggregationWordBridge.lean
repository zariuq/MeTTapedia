import Mettapedia.Languages.MeTTa.PeTTa.Bridges.AggregationSource
import Mettapedia.Machines.InferredWordFold

/-!
# From a source certificate to an admitted word result

This bridge joins existing PeTTa operational returns, extracted additive
evidence and independently executed UInt64 addition. It covers one captured
source coordinate and an IR batch summary. It does not identify IR fold counts
with PeTTa evaluator instruction counts or fuse source interruption points.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.AggregationWordBridge

open Mettapedia.Machines.AdditiveFoldInference
open Mettapedia.Machines.InferredWordFold
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open AggregationSource MeTTaIL.WireKit Eval

/-- An accepted native result is an actual answer of the source expression,
with the same PeTTa store and exactly one answer occurrence. -/
theorem word_coordinate_returns {n : Nat} {environment : Environment n} {source : Fin n → Atom}
    (certificate : SourceCertificate environment source) (program : SpaceSemantics.Program)
    (caller : Subst) (state : Effects.State) (registers : Fin n → Nat) (input : Nat)
    (captured : Captured environment caller registers input) (values : Registers n)
    (admitted : cachedValues certificate.additive ⟨certificate.program, registers⟩ [input] = some values)
    (i : Fin n) : PureReturns program caller state (source i) state (number (values i)) := by
  have same := cachedValues_correct certificate.additive ⟨certificate.program, registers⟩ [input] values admitted
  have coordinate := congrFun same i
  change values i = (certificate.program i).eval registers input at coordinate
  rw [coordinate]
  exact (certificate.elaborated i).returns program caller state registers input captured

/-- The same extracted certificate supplies the source-loop meaning of an
accepted batch, independently of the word plan's arithmetic. -/
theorem word_batch_refines {n : Nat} {environment : Environment n} {source : Fin n → Atom}
    (certificate : SourceCertificate environment source) (registers : Registers n) (inputs : List Nat)
    (values : Registers n)
    (admitted : cachedValues certificate.additive ⟨certificate.program, registers⟩ inputs = some values) :
    values = sourceRun certificate.program inputs registers :=
  cachedValues_correct certificate.additive ⟨certificate.program, registers⟩ inputs values admitted

/-- Failed word admission does not lose the source's result: the existing
worker falls back using the current program and current register values. -/
theorem word_or_fallback_exact {n : Nat} {environment : Environment n} {source : Fin n → Atom}
    (certificate : SourceCertificate environment source) (world : World n) (request : Request n) :
    (worker certificate.additive).execute (base := ()) (index := ()) world request =
      (reference n).step world request := live_exact certificate.additive world request

namespace Controls

def certificate : SourceCertificate AggregationSource.Controls.environment AggregationSource.Controls.counter :=
  (inferSource AggregationSource.Controls.environment AggregationSource.Controls.counter).get
    AggregationSource.Controls.source_counter_admitted

def caller : Subst := [("s", number 5), ("x", number 7)]

theorem capture_valid : Captured AggregationSource.Controls.environment caller (fun _ => 5) 7 := by
  intro name role found
  by_cases stateName : name = "s"
  · subst name
    have same : role = .register 0 := by simpa [AggregationSource.Controls.environment] using found.symm
    subst role
    rfl
  · by_cases inputName : name = "x"
    · subst name
      have same : role = .inputValue := by simpa [AggregationSource.Controls.environment] using found.symm
      subst role
      rfl
    · simp [AggregationSource.Controls.environment, stateName, inputName] at found

/-- The certificate was computed from source atoms; its admitted UInt64 result
is checked against the existing source execution judgment. -/
theorem source_counter_returns_six (program : SpaceSemantics.Program) (state : Effects.State) :
    PureReturns program caller state (AggregationSource.Controls.counter 0) state (number 6) := by
  exact word_coordinate_returns certificate program caller state (fun _ => 5) 7 capture_valid
    (fun _ => 6) (by decide) 0

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.AggregationWordBridge
