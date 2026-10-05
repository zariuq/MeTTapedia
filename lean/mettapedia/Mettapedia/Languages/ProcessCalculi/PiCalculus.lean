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

`RhoEncodingCorrectness.lean` is a separate comparison API; its execution
theorems retain their explicit fragment and communication-safety conditions.
The scoped rho bridges provide payload-preserving core servers and a stateful
allocator with actual authored firing blocks. They do not identify the older
derived restriction/replication sketch with a complete core-rho compilation.
-/
