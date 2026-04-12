import Mettapedia.Logic.MarkovDeFinettiFortiniBridgeCrux

/-! LLM primer:
- This file once attempted to prove `CrossRowCoherenceStep` directly inside the
  old local surface-theorem route.
- The goal: P.restrict{ω₀=a}(cyl(a::b::c::xs)) = ∫ K_a({b}) · stepProd(b::c::xs) dP.restrict{ω₀=a}
- Available: hStart (per-row product formula under restriction), IH (identity for shorter words),
  hRow (per-row de Finetti product formula), hExt (prefix measure extension), hμ (Markov exch).
-
- Strategy: Decompose the cylinder via wordSuccessorTupleMap into row-successor constraints.
  For the first constraint (rvp_a(0)=b), use the per-row de Finetti (hStart).
  For the remaining constraints, relate to the IH via the prefix measure.
-/

noncomputable section

namespace Mettapedia.Logic

open MarkovDeFinettiHard
open MarkovDeFinettiRecurrence
open MeasureTheory Finset
open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovExchangeability

variable {k : ℕ}

/-! ## Honest stopping point

This file is retained only as an exploratory scratchpad marker.

The direct route “start from `hStart`, `hIH`, and prefix-extension identities
and assemble `CrossRowCoherenceStep`” did not yield a sound bridge theorem.
Rather than leave a stale theorem attempt or brittle helper lemmas here, the
file now stops before introducing any claims beyond the imported development.

The active theorem frontier is upstream:
`SuccessorMatrixPE_of_markovExchangeable_strongRecurrence`.
Once that joint symmetry theorem is proved, the crux layer already knows how to
turn it into the cross-row coherence payload and the final mixture theorem.

Positive example:
- A future proof can still mine the active bridge files for word/fiber event
  normal forms and restricted-start identities.

Negative example:
- This file does **not** currently prove or even state a usable theorem toward
  `CrossRowCoherenceStep`; keeping an orphaned theorem attempt here would only
  mislead a later audit.
-/

end Mettapedia.Logic
