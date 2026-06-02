import Mettapedia.Logic.IntensionalInheritance
import Mettapedia.Logic.EmpiricalIntensionalInformation
import Mettapedia.Logic.EmpiricalIntensionalFactorGraphBridge
import Mettapedia.Logic.IntensionalInheritanceSolomonoffBridge
import Mettapedia.Logic.IntensionalInheritanceApproximationBridge

/-!
# Intensional Inheritance (Entry Point)

This module collects the stable public entry points for the regrounded
Chapter-12 / intensional-inheritance line:

* the abstract-interpretation-based inheritance surface,
* the concrete finite empirical 2x2 instance,
* the tiny factor-graph / VE / BP bridge for that empirical instance,
* the Solomonoff-facing bridge,
* the approximation-facing bridge.

It is the focused public import surface for this topic, without routing through
the much larger PLN canonical facade.
-/
