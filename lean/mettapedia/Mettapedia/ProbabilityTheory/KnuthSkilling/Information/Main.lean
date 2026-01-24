import Mettapedia.ProbabilityTheory.KnuthSkilling.Information.Divergence
import Mettapedia.ProbabilityTheory.KnuthSkilling.Information.DivergenceMathlib
import Mettapedia.ProbabilityTheory.KnuthSkilling.Information.Entropy
import Mettapedia.ProbabilityTheory.KnuthSkilling.Information.EntropyMathlib

/-!
# Knuth-Skilling: Information Layer (Sections 6 and 8)

This directory packages the "information theory" layer that sits on top of the
Appendix A/B/C algebra:

- Section 6 (Divergence): KL-like divergence derived from the variational normal form.
- Section 8 (Information and Entropy): Shannon entropy and basic properties on finite distributions.

Import this file if you want the canonical K&S divergence/entropy results (and the optional
Mathlib bridges) without reaching into individual section-numbered modules.
-/
