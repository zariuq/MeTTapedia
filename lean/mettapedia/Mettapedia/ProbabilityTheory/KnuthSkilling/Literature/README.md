# K&S Codex Literature (Lean)

This folder is the Lean-facing “codex” for background literature used to understand and (eventually)
close the remaining Knuth–Skilling Appendix A gaps.

Source PDFs live under `literature/KS_codex/` (outside the Lean project); see
`literature/KS_codex/LITERATURE_INDEX.md` for a curated reading guide.

Important: per project policy, this `README.md` is **LLM-generated working documentation**; the user
decides what to commit.

## Files

- `Index.lean`: import bundle + map from PDFs → Lean modules.
- `FunctionalEquations.lean`: “additive regraduation” interface + small lemmas; Aczél/CDE context.
- `CoxTheorem.lean`: bridges Cox’s associativity equation to the additive-regraduation form.
- `OrderedGroups.lean`: Archimedean ordered-group lemmas available in mathlib; “Hölder-style” steps.
- `Residuated.lean`: core definitions for residuated monoids/lattices (Jipsen–Tuyt context).
- `ResiduatedHahnEmbedding.lean`: statement layer for Jenei’s partial sublex product / monoid-embedding results (no `sorry`).
- `SemigroupRepresentations.lean`: ordered-group representation wrappers using mathlib (Hölder + Hahn embedding).
- `KnuthSkillingPapers.lean`: entry-point map from the K&S PDFs → existing KnuthSkilling Lean files.

## Literature map (PDF → Lean entry point)

- Knuth & Skilling (2012) “Foundations of Inference”
  - PDF: `literature/KS_codex/Knuth_Skilling_2012_Foundations_of_Inference.pdf`
  - Lean: `KnuthSkillingPapers.lean` (map), plus the main development under `Mettapedia/ProbabilityTheory/KnuthSkilling/`
- Skilling & Knuth (2019) “Symmetrical foundation for measure, probability and quantum theory”
  - PDF: `literature/KS_codex/Skilling_Knuth_2019_Symmetrical_Foundation.pdf`
  - Lean: `KnuthSkillingPapers.lean` (map; the quantum-side formalization is tracked elsewhere)
- Dupré–Tipler (2006) Cox theorem (plausible values)
  - PDF: `literature/KS_codex/Dupre_Tipler_2006_Cox_Theorem.pdf`
  - Lean: `CoxTheorem.lean` (connectors) and `Mettapedia/ProbabilityTheory/Cox/`
- Terenin–Draper (2017) Cox theorem (Jaynesian)
  - PDF: `literature/KS_codex/Terenin_Draper_2017_Cox_Theorem_Jaynesian.pdf`
  - Lean: `CoxTheorem.lean` (connectors) and `Mettapedia/ProbabilityTheory/Cox/`
- Aczél excerpt (associativity functional equation)
  - PDF: `literature/KS_codex/Aczel_excerpt_pp319-324.pdf`
  - Lean: `FunctionalEquations.lean`
- CDE method for functional equations
  - PDF: `literature/KS_codex/CDE_Method_FuncEq.pdf`
  - Lean: `FunctionalEquations.lean`
- Evan Chen notes (worked FE techniques)
  - PDF: `literature/KS_codex/FuncEq_Intro_EvanChen.pdf`
  - Lean: `FunctionalEquations.lean`
- Clay–Rolfsen (Ordered groups and topology), Ch 2 “Hölder’s theorem”
  - PDF: `literature/KS_codex/Clay_Mann_2015_Ordered_Groups_Topology.pdf`
  - Lean: `OrderedGroups.lean`
- Fox (1975) “An embedding theorem for ordered groups”
  - PDF: `literature/KS_codex/Ordered_Semigroups_Hofner.pdf`
  - Lean: `SemigroupRepresentations.lean`
- Fuchs (2007) “Ordered groups”
  - PDF: `literature/KS_codex/Fuchs_2007_Ordered_Groups.pdf`
  - Lean: `SemigroupRepresentations.lean`
- Jenei (Hahn embedding for residuated semigroups)
  - PDF: `literature/KS_codex/Jipsen_Tuyt_2019_Hahn_Embedding.pdf`
  - Lean: `Residuated.lean` (residuated interfaces + lemmas) + `ResiduatedHahnEmbedding.lean` (explicit `Prop` statement interfaces)
- Bajri (2021) thesis “On representations of semigroups”
  - PDF: `literature/KS_codex/Bajri_2021_Semigroup_Representations.pdf`
  - Lean: `SemigroupRepresentations.lean`
- Kudryavtseva (2015) “Lattice ordered semigroups”
  - PDF: `literature/KS_codex/Kudryavtseva_2015_Lattice_Ordered_Semigroups.pdf`
  - Lean: `SemigroupRepresentations.lean`
- Survey: “Representation theorems for ordered structures”
  - PDF: `literature/KS_codex/Representation_Theorems_Ordered_Structures.pdf`
  - Lean: `SemigroupRepresentations.lean`
