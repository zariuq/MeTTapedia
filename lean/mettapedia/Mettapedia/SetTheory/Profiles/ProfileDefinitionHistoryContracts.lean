import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.DefinitionHistories
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.DefinitionHistoryControls
import Mettapedia.Logic.HOL.DefinitionHistoryProofConservativity
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLDefinitionHistoryErasure
import Mettapedia.SetTheory.Profiles.MaterialDefinitionHistoryControls

/-!
# Checked definitions, conservative erasure and material meaning

The dependent calculus checks each fresh closed definition in the preceding
stage. Its general erasure transports actual typing, equality, subsumption,
dependent contexts and substitution derivations. Base declaration formation
and primitive computation stability give the corresponding properties at
every later stage. Old sequents and old-type inhabitation are conservative.
Normalization inheritance separately requires normalization of the base.

Fixed-simple-type HOL constructs an actual Henkin model at each entry and
proves agreement with independently expanded syntax, for open terms and closed
formulas. Complete retained proofs are translated through all 29 rules. The
ordered rule tree, every local hypothesis position and node count survive;
the original constant names need not be recoverable from their expansions.
The existing checked HOL/native prefix supplies the corresponding history.
Each expanded definition equation has a constructed reflexivity proof. Actual
hypothesis substitution discharges those equations through the complete
retained HOL calculus, proving old-sequent conservativity in both directions.
General hypothesis substitution can add proof branches. The constructed
definition equations have reflexivity leaves. Discharge changes hypothesis
observations even when a proof size agrees; it is distinct from expansion.

Concrete dependent definitions name a carrier, its function type, identity
and a genuinely dependent reflexivity family. A separate material instance
uses the actual hyperset quotient and its Quine atom. False old claims remain
false, even while distinct new and old formulas expand to the same query.

These results concern finite acyclic histories with bodies checked before
installation. They do not admit arbitrary recursive equations, prove the
general native checker correct, or choose a native foundation. Native type
alias admission and dependency currentness have separate execution controls.
-/
