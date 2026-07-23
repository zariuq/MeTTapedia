import Mettapedia.MachineLearning.NeuralNetworks.Architecture.CarrierInstances.RecurrentPolicy

/-!
# Recurrent policy-port provenance

This ledger separates source-shaped ideal semantics, reusable recurrence
theorems, and explicit negative boundaries. It counts theorem families rather
than declarations.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.Architecture.RecurrentPolicyProvenance

inductive ContributionKind
  | exactRestatement
  | newContent
  | scopeBoundary
  deriving DecidableEq, Repr

structure Contribution where
  kind : ContributionKind
  family : String
  source : String
  deriving Repr

def contributions : List Contribution :=
  [ ⟨.exactRestatement,
      "ordered seven-field input with argument, depth, and hole clamps",
      "TGAD O2 policy host source"⟩
  , ⟨.exactRestatement,
      "masked source summary added before recurrent transition",
      "TGAD recurrent decoder port source"⟩
  , ⟨.exactRestatement,
      "summary-derived initial hidden and one recurrent transition per action",
      "TGAD recurrent decoder port source"⟩
  , ⟨.exactRestatement,
      "hidden state as decision state through the common legal-policy readout",
      "TGAD recurrent decoder port and policy host sources"⟩
  , ⟨.newContent,
      "recurrent policy port as a nontrivial replacement-write state carrier",
      "RecurrentPolicy"⟩
  , ⟨.newContent,
      "teacher-forced sequence equals the tail of the carrier trajectory",
      "RecurrentPolicy"⟩
  , ⟨.newContent,
      "prefix-suffix decomposition and teacher-forced/incremental equality",
      "RecurrentPolicy"⟩
  , ⟨.newContent,
      "legal support remains checker-owned after an arbitrary recurrent step",
      "RecurrentPolicy"⟩
  , ⟨.scopeBoundary,
      "state-input field order is observable",
      "RecurrentPolicy"⟩
  , ⟨.scopeBoundary,
      "position is guarded rather than silently clamped",
      "RecurrentPolicy"⟩
  , ⟨.scopeBoundary,
      "resetting hidden state between actions changes a real trajectory",
      "RecurrentPolicy"⟩
  , ⟨.scopeBoundary,
      "binary32 and library-internal GRU arithmetic remain outside ideal semantics",
      "RecurrentPolicy"⟩ ]

def contributionCount (kind : ContributionKind) : Nat :=
  (contributions.filter fun contribution ↦ contribution.kind = kind).length

theorem contributionCounts :
    (contributionCount .exactRestatement,
      contributionCount .newContent,
      contributionCount .scopeBoundary) = (4, 4, 4) := by
  decide

#print axioms contributionCounts

end Mettapedia.MachineLearning.NeuralNetworks.Architecture.RecurrentPolicyProvenance
