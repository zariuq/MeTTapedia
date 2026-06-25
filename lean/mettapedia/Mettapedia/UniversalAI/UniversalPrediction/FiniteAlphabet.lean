import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.Basic
import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.ControlledPrefixMeasure
import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.ControlledFiniteHorizon
import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.ControlledSolomonoffBridge
import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.PrefixMeasure
import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.FiniteHorizon
import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.CompetitorBounds
import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.HutterEnumeration
import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.HutterEnumerationTheoremSemimeasure
import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.SolomonoffBridge

/-!
# Universal Prediction (Finite Alphabet) — Master Import

This module provides a single import point for the finite-alphabet universal prediction stack:

* core semimeasures/prefix measures on `Word α := List α`
* finite-horizon relative entropy / dominance→regret bounds
* Hutter-style lower-semicomputable semimeasure enumeration (concrete via `Nat.Partrec.Code`)
* the resulting theorem-grade “Solomonoff-style” universal mixture `M₂`

The corresponding binary-specialized development remains in:
* `Mettapedia.UniversalAI.UniversalPrediction` and `.../SolomonoffBridge.lean`.
-/
