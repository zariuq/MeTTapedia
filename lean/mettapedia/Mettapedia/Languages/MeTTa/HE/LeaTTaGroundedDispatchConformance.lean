import Mettapedia.Languages.MeTTa.HE.Spec.Eval
import Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
import MettaHyperonFull.Core.Grounding

/-!
# LeaTTa grounded-dispatch conformance

The specification treats host execution as an abstract relation.  LeaTTa
stores concrete grounded implementations in a name-indexed table.  This
module gives the exact boundary between them without requiring the two
evaluators to share an internal `call-native` plan.

LeaTTa grounded implementations return atoms only; the current bindings are
threaded by the evaluator.  The corresponding specification result therefore
attaches the empty native binding set to every raw host result, after which
the published call rule merges it with the caller bindings.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaGroundedDispatchConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaBridge
open Spec.Eval

/-- Exact translation of one concrete LeaTTa grounded outcome into the
executable-independent host-result carrier.  The diagnostic text carried by
LeaTTa's `incorrectArgument` constructor is intentionally forgotten because
the published result constructor carries no message. -/
inductive GroundedResultRuntimeRel : GroundedResult → Metta.ReduceResult → Prop where
  | ok (atoms : List Atom) :
      GroundedResultRuntimeRel
        (.ok (atoms.map fun atom => (atom, Bindings.empty)))
        (.ok (toLeaTTaAtoms atoms))
  | noReduce : GroundedResultRuntimeRel .noReduce .noReduce
  | incorrectArgument (message : String) :
      GroundedResultRuntimeRel .incorrectArgument (.incorrectArgument message)
  | runtimeError (message : String) :
      GroundedResultRuntimeRel (.runtimeError message) (.runtimeError message)

/-- The spec dispatch induced by one concrete LeaTTa grounding table.

Executability is table membership at the first matching name.  Outcomes are
the exact result of `callGrounded` on structurally translated arguments.
The relation remains meaningful for a missing name (`noReduce`), while the
separate executability field prevents the published grounded-call rule from
selecting that lane. -/
def groundingTableDispatch (table : Metta.GroundingTable) :
    Spec.Eval.GroundedDispatch where
  executable operator :=
    ∃ name grounding,
      operator = .symbol name ∧
        Metta.GroundingTable.lookup table name = some grounding
  outcome operator arguments outcome :=
    ∃ name,
      operator = .symbol name ∧
        GroundedResultRuntimeRel outcome
          (Metta.callGrounded table name (toLeaTTaAtoms arguments))

/-- Characterization of the concrete executable-head boundary. -/
theorem groundingTableDispatch_executable_iff
    (table : Metta.GroundingTable) (operator : Atom) :
    (groundingTableDispatch table).executable operator ↔
      ∃ name grounding,
        operator = .symbol name ∧
          Metta.GroundingTable.lookup table name = some grounding :=
  Iff.rfl

/-- Characterization of the concrete outcome boundary. -/
theorem groundingTableDispatch_outcome_iff
    (table : Metta.GroundingTable) (operator : Atom)
    (arguments : List Atom) (outcome : GroundedResult) :
    (groundingTableDispatch table).outcome operator arguments outcome ↔
      ∃ name,
        operator = .symbol name ∧
          GroundedResultRuntimeRel outcome
            (Metta.callGrounded table name (toLeaTTaAtoms arguments)) :=
  Iff.rfl

private def identityGrounding : Metta.Grounding where
  name := "identity"
  mode := .quoteArgs
  typeSig := none
  impl := fun arguments => .ok arguments

/-! ## Boundary canaries -/

/-- Positive: a table entry is executable under its exact symbol name. -/
example :
    (groundingTableDispatch [identityGrounding]).executable
      (.symbol "identity") := by
  refine ⟨"identity", identityGrounding, rfl, ?_⟩
  simp [Metta.GroundingTable.lookup, identityGrounding]

/-- Positive: raw host results are translated in order and receive empty
native bindings. -/
example :
    (groundingTableDispatch [identityGrounding]).outcome
      (.symbol "identity") [.symbol "a"]
      (.ok [(.symbol "a", Bindings.empty)]) := by
  refine ⟨"identity", rfl, ?_⟩
  simpa [Metta.callGrounded, Metta.GroundingTable.lookup,
    identityGrounding, toLeaTTaAtoms, toLeaTTaAtom] using
      (GroundedResultRuntimeRel.ok [.symbol "a"])

/-- Negative: an absent name is not executable, even though asking the raw
table to reduce it would return `noReduce`. -/
example :
    ¬(groundingTableDispatch [identityGrounding]).executable
      (.symbol "missing") := by
  rintro ⟨name, grounding, operatorEq, lookup⟩
  cases operatorEq
  simp [Metta.GroundingTable.lookup, identityGrounding] at lookup

end Mettapedia.Languages.MeTTa.HE.LeaTTaGroundedDispatchConformance
