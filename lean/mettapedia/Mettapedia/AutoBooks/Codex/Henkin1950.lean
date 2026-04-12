import Mettapedia.AutoBooks.Codex.Henkin1950.Syntax
import Mettapedia.AutoBooks.Codex.Henkin1950.Semantics
import Mettapedia.AutoBooks.Codex.Henkin1950.Soundness
import Mettapedia.AutoBooks.Codex.Henkin1950.AxiomSchemes
import Mettapedia.AutoBooks.Codex.Henkin1950.DerivedResults
import Mettapedia.AutoBooks.Codex.Henkin1950.InferenceRules
import Mettapedia.AutoBooks.Codex.Henkin1950.QuotedValidities
import Mettapedia.AutoBooks.Codex.Henkin1950.PrimeExtensions
import Mettapedia.AutoBooks.Codex.Henkin1950.CompleteTheories
import Mettapedia.AutoBooks.Codex.Henkin1950.MaximalTheories
import Mettapedia.AutoBooks.Codex.Henkin1950.TermQuotients
import Mettapedia.AutoBooks.Codex.Henkin1950.TruthValues
import Mettapedia.AutoBooks.Codex.Henkin1950.CanonicalAssignments
import Mettapedia.AutoBooks.Codex.Henkin1950.CanonicalTruth
import Mettapedia.AutoBooks.Codex.Henkin1950.RepresentativeIndependence
import Mettapedia.AutoBooks.Codex.Henkin1950.CanonicalTruthQuotients
import Mettapedia.AutoBooks.Codex.Henkin1950.CanonicalTruthLaws
import Mettapedia.AutoBooks.Codex.Henkin1950.CanonicalFrame
import Mettapedia.AutoBooks.Codex.Henkin1950.CanonicalPropClasses
import Mettapedia.AutoBooks.Codex.Henkin1950.TheoremTransport
import Mettapedia.AutoBooks.Codex.Henkin1950.CanonicalModel
import Mettapedia.AutoBooks.Codex.Henkin1950.Theorem1Bridge
import Mettapedia.AutoBooks.Codex.Henkin1950.Theorem1BridgeRegression
import Mettapedia.AutoBooks.Codex.Henkin1950.Compactness

/-!
# Henkin (1950) in Codex

Fresh Codex-side front-end for the paper
"Completeness in the Theory of Types".

Current scope:
- paper-specific types and constants,
- standard/general model notions,
- soundness and basic validity canaries.
- surfaced class-model form of Theorem 1 under the exact pp. 86-88 packaged
  maximal-theory hypotheses.
- surfaced forward half of Theorem 2 in open-formula and closed-sentence form.
- surfaced forward closed-theory direction of Theorem 3.
- an explicit proof-theoretic bridge from the paper-facing extensional
  consistency notion to raw derivation consistency.
- an explicit reverse-Theorem-3 precursor from finite-subtheory satisfiability
  to raw derivation consistency.
- an explicit Theorem-3 forward corollary from paper-facing satisfiability to
  raw derivation consistency.
- the first four paper axiom schemata as actual theorems.
- paper-facing formulations of inference rules `I`-`VI`.
- selected quoted derived results from p. 85.
- semantic Codex counterparts for further quoted p. 85 lines whose exact
  proof-theoretic bridge is still being aligned with the trusted core.
- direct paper-general semantic validation for the proposition-equality quoted
  fragment on p. 85 (results 14-20 except the higher-order argument-
  congruence step 21).
- a conditional paper-general validity bridge for quoted result 21 from an
  explicit model-side `EqAppArgSound` hypothesis.
- unconditional paper-standard validity of quoted result 21.
- prime-extension scaffolding for the closed-theory step on pp. 86-88.
- complete-theory, formula-quotient, and canonical-world interfaces for the
  pp. 86-88 maximal-consistent-set layer.
- a direct maximality-to-complete-theory bridge for the paper's p. 86 closed
  theory argument.
- typed quotient classes of closed terms and descended application maps for the
  pp. 86-87 domain construction.
- the p. 86 collapse of closed proposition classes to `⊤/⊥` over complete
  consistent theories.
- representative substitutions, their induced semantic valuations, and the
  first p. 87 assignment-by-closed-representatives bridge.
- canonical truth-by-membership for open formulas together with the closed-term
  existential/universal clauses available before full representative-
  independence.
- reusable representative-independence helpers linking term equality, formula
  equivalence, and representative-assignment quantifier clauses.
- quotient-class formulations of the canonical universal and existential truth
  clauses, no longer tied to a particular choice of representatives.
- compositional truth laws for the canonical relation at propositional
  connectives, aligning `Holds` with complete-theory membership.
- a paper-faithful class-based canonical frame layer whose carriers are
  `TermClass` quotients and whose formula denotation is `Holds`.
- a proposition-class interface showing when a `TermClass T o` is canonically
  true or false, and relating class application back to `Holds`.
- substitution transport for open derivations under representative closure,
  giving canonical-truth theorem canaries for open axiom schemata.
- a packaged paper-faithful canonical class model object built from the
  already-proved quotient, truth, proposition-class, and theorem-transport
  layers.
- an explicit theorem-facing `SentenceSoundBridge` interface isolating the
  exact remaining step from class-model Theorem 1 to paper-general
  satisfiability.
- an explicit obstruction theorem showing that any actual sentence-sound bridge
  from the canonical proposition-collapse semantics to the current
  `GeneralModel` interface already forces excluded middle.
- exact general-validity and standard-validity characterizations of the
  proposition-bivalence sentence by ambient excluded middle.
- regression canaries for the Theorem-1 bridge obstruction surface.
-/
