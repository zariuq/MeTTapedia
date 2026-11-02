import Mettapedia.Languages.ProcessCalculi.PiCalculus.Syntax
import Mettapedia.Languages.ProcessCalculi.PiCalculus.StructuralCongruence
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Reduction
import Mettapedia.Languages.ProcessCalculi.PiCalculus.MultiStep
import Mettapedia.Languages.ProcessCalculi.PiCalculus.RhoEncoding
import Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation
import Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakBisim
import Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakBisimDerived
import Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakBisimOpenMapBridge
import Mettapedia.Languages.ProcessCalculi.PiCalculus.BranchingBisim
import Mettapedia.Languages.ProcessCalculi.PiCalculus.OpenMapBridgeRegression
import Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization
import Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingMorphism
import Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardAdminReflection
import Mettapedia.Languages.ProcessCalculi.PiCalculus.NameServerLemmas
import Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
import Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredSemantics
import Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredRFComparison
import Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredControls
import Mettapedia.Languages.ProcessCalculi.PiCalculus.ReflectionControls
import Mettapedia.Languages.ProcessCalculi.PiCalculus.StaticEquationFamily
import Mettapedia.Languages.ProcessCalculi.PiCalculus.CongruenceToolkit
import Mettapedia.Languages.ProcessCalculi.PiCalculus.CongruenceKeys
import Mettapedia.Languages.ProcessCalculi.PiCalculus.CongruenceSubstitution
import Mettapedia.Languages.ProcessCalculi.PiCalculus.EarlyTransitions
import Mettapedia.Languages.ProcessCalculi.PiCalculus.SaturatedReduction
import Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexForm
import Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexCompleteness
import Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexCoherence
import Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexTyped
import Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexSubstitution
import Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexSteps
import Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexReflection
import Mettapedia.Languages.ProcessCalculi.PiCalculus.SynchronousStepReflection
import Mettapedia.Languages.ProcessCalculi.PiCalculus.SynchronousSteps
import Mettapedia.Languages.ProcessCalculi.PiCalculus.SynchronousSection
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Sums
import Mettapedia.Languages.ProcessCalculi.PiCalculus.SumsReflection
import Mettapedia.Languages.ProcessCalculi.PiCalculus.SumsSteps
import Mettapedia.Languages.ProcessCalculi.PiCalculus.SumsStore
import Mettapedia.Languages.ProcessCalculi.PiCalculus.PrenexClosing
import Mettapedia.Languages.ProcessCalculi.PiCalculus.NamedStaticAdequacy
import Mettapedia.Languages.ProcessCalculi.PiCalculus.ReadBack
import Mettapedia.Languages.ProcessCalculi.PiCalculus.ReadBackAlpha
import Mettapedia.Languages.ProcessCalculi.PiCalculus.ReadBackCanonical
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEndpointOperational
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEndpointControls
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoNativeTransport
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoNativeTransportControls
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoSpatial
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoSpatialControls
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedControls
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedAllocationRunsControls

/-!
# Process Calculi: π-Calculus

Language-focused facade for the π-calculus formalization.

This module provides the full π-calculus development (syntax through encoding and
forward-simulation artifacts) under `Mettapedia.Languages.ProcessCalculi.*`.

The authored internal executor has a complete frontier and an exact rule
comparison. Its static quotient remains the declared parallel monoid; the
larger binding-aware static family is available separately, with no implicit
claim that the two quotients coincide.

Structural congruence has its own toolkit: lists of components and restrictions up to congruence
(`CongruenceToolkit`), processes with equal locally nameless translations are congruent (`CongruenceKeys`), and
congruence is closed under substitution (`CongruenceSubstitution`). The early labelled transitions have shapes,
and every silent transition is a reduction (`EarlyTransitions`). Saturated reduction bisimilarity compares
processes by their reductions beside every process (`SaturatedReduction`).

`RhoEncodingCorrectness.lean` is a separate comparison API; its execution
theorems retain their explicit fragment and communication-safety conditions.
The scoped rho bridges provide payload-preserving core servers and a stateful
allocator with actual authored firing blocks. They do not identify the older
derived restriction/replication sketch with a complete core-rho compilation.
-/
