import Mettapedia.ProbabilityTheory.KnuthSkilling
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Main

/-!
# Knuth–Skilling papers: formalization entry points

This file is a *map* from the “core K&S PDFs” to the Lean development already living under
`Mettapedia/ProbabilityTheory/KnuthSkilling/`.

Local PDFs:
- Knuth & Skilling (2012), “Foundations of Inference”:
  `literature/KS_codex/Knuth_Skilling_2012_Foundations_of_Inference.pdf`.
- Skilling & Knuth (2019), “Symmetrical foundation for measure, probability and quantum theory”:
  `literature/KS_codex/Skilling_Knuth_2019_Symmetrical_Foundation.pdf`.

Lean entry points (project-relative paths):
- `Mettapedia/ProbabilityTheory/KnuthSkilling/Core/Basic.lean` (high-level K&S structures)
- `Mettapedia/ProbabilityTheory/KnuthSkilling/Core/Algebra.lean` (core algebra)
- `Mettapedia/ProbabilityTheory/KnuthSkilling/Additive/Axioms/SandwichSeparation.lean` (sandwich separation: separation ⇒ commutativity)
- `Mettapedia/ProbabilityTheory/KnuthSkilling/_archive/Separation/Derivation.lean` (WIP derivation of `KSSeparation`)
- `Mettapedia/ProbabilityTheory/KnuthSkilling/Additive/Proofs/GridInduction/` (Appendix A grid/induction development)
- `Mettapedia/ProbabilityTheory/KnuthSkilling/Additive/Proofs/OrderedSemigroupEmbedding/HolderEmbedding.lean` (Hölder embedding path)
- `Mettapedia/ProbabilityTheory/AssociativityTheorem.lean` (context + alternative view)

Nothing in this file is “new mathematics”; it is a documentation-oriented import bridge so the
literature codex can refer to K&S-by-PDF without duplicating the main formalization.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Literature

end Mettapedia.ProbabilityTheory.KnuthSkilling.Literature
