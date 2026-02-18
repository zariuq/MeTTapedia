import Mettapedia.Languages.ProcessCalculi.PiCalculus.Syntax
import Mettapedia.Languages.ProcessCalculi.PiCalculus.StructuralCongruence
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Reduction
import Mettapedia.Languages.ProcessCalculi.PiCalculus.MultiStep
import Mettapedia.Languages.ProcessCalculi.PiCalculus.RhoEncoding
import Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation
import Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakBisim
import Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingMorphism
import Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance

/-!
# Process Calculi: π-Calculus

Language-focused facade for the π-calculus formalization.

This module provides the full π-calculus surface (syntax through encoding and
forward-simulation artifacts) under `Mettapedia.Languages.ProcessCalculi.*`.

`RhoEncodingCorrectness.lean` is intentionally excluded from this facade while
it remains legacy WIP.
-/
