import Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem.FunctionalEquation
import Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem.DirectProduct
import Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem.Main

/-!
This module is the public entry point for the Knuth–Skilling (Appendix B) *product theorem*.

The development is split as follows:

- `...ProductTheorem.FunctionalEquation`: a sorry-free solver for the product equation
  (K&S Appendix B), yielding exponential solutions under explicit regularity assumptions.
- `...ProductTheorem.Basic`: derives the product equation from the scalar axioms for `⊗`
  in the \"Independence\" section (Axioms 3–4) together with an additive order-isomorphism
  representation `Θ(x ⊗ t) = Θ x + Θ t`.
- `...ProductTheorem.Main`: combines the bridge and the solver to conclude that `⊗` is
  multiplication up to a global scale constant.
- `...ProductTheorem.DirectProduct`: lattice-level bookkeeping for the event product `×`
  used in the “Independence” subsection, with the canonical `Set` model.
-/
