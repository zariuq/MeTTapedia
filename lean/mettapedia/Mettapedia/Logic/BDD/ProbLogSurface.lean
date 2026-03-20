import Mettapedia.Logic.BDD.ProbMeTTaBridge
import Mettapedia.Logic.BDD.FirstOrderProbMeTTaBridge
import Mettapedia.Logic.BDD.FirstOrderADTranslation

/-!
# ProbLog Surface Theorems

Public entry points for the current ProbLog-to-BDD/WMC formalization.

Main theorems:

- Ground stratified normal programs:
  `Mettapedia.Logic.BDDCore.problog_full_ground_equivalence`
- Function-free first-order normal programs via explicit grounding:
  `Mettapedia.Logic.BDDCore.problog_functionFree_normal_equivalence`
- Function-free first-order normal programs with first-order query/evidence
  goals via explicit grounding:
  `Mettapedia.Logic.BDDCore.problog_functionFree_normal_surface_equivalence`
- Function-free first-order annotated-disjunction programs via explicit
  grounding and expansion:
  `Mettapedia.Logic.BDDCore.problog_functionFree_ad_equivalence`
- Function-free first-order annotated-disjunction programs with first-order
  query/evidence goals:
  `Mettapedia.Logic.BDDCore.problog_functionFree_ad_surface_equivalence`
- Function-free weighted first-order annotated-disjunction programs with
  first-order query/evidence goals and compiled switch layout:
  `Mettapedia.Logic.BDDCore.problog_functionFree_weighted_ad_surface_equivalence`
- The same weighted first-order AD result packaged around a compiled-program
  object:
  `Mettapedia.Logic.BDDCore.FirstOrderWeightedADCompiledProgram.surface_equivalence`
- A decomposed-stratification variant for weighted first-order AD programs:
  `Mettapedia.Logic.BDDCore.surface_equivalence_of_parts`
- A structured-stratification variant where AD body/head and switch/head
  ordering is proved per grounded AD instance:
  `Mettapedia.Logic.BDDCore.surface_equivalence_of_structured`
- The same structured route packaged as a proof-carrying compiled-program
  object:
  `Mettapedia.Logic.BDDCore.FirstOrderWeightedADStructuredCompiledProgram.surface_equivalence`
- A source-level structured-compilation wrapper that quantifies over explicit
  source-facing switch-slot and stratification obligations:
  `Mettapedia.Logic.BDDCore.FirstOrderWeightedADSourceStructuredCompilation.surface_equivalence`
- The highest-level honest source-facing existence wrapper for that route:
  `Mettapedia.Logic.BDDCore.exists_surface_equivalence_of_sourceStructuredEvidenceSatisfiable`
- A local-choice automation route: if each grounded AD instance merely admits a
  compatible slot assignment, the global source-structured witness is built
  automatically by choice:
  `Mettapedia.Logic.BDDCore.FirstOrderWeightedADProbLogProgram.surface_equivalence_of_locallyStructurablyCompilable`
- The corresponding highest-level existence wrapper:
  `Mettapedia.Logic.BDDCore.exists_surface_equivalence_of_locallyStructuredEvidenceSatisfiable`
- The highest-level honest source-facing wrapper for the structured route:
  `Mettapedia.Logic.BDDCore.exists_surface_equivalence_of_structuredEvidenceSatisfiable`
- Existence-style wrapper that hides the compiled witness in the assumptions:
  `Mettapedia.Logic.BDDCore.exists_surface_equivalence_of_exists_compiled`

Positive example:
- If you want the strongest currently formalized surface theorem, start from
  `exists_surface_equivalence_of_locallyStructuredEvidenceSatisfiable`,
  `FirstOrderWeightedADProbLogProgram.surface_equivalence_of_locallyStructurablyCompilable`,
  `exists_surface_equivalence_of_sourceStructuredEvidenceSatisfiable`,
  `FirstOrderWeightedADSourceStructuredCompilation.surface_equivalence`,
  `surface_equivalence_of_structured`,
  `FirstOrderWeightedADStructuredCompiledProgram.surface_equivalence`, or
  `exists_surface_equivalence_of_structuredEvidenceSatisfiable`.

Negative example:
- If you need unrestricted non-function-free first-order ProbLog, this module
  does not claim that yet.

0 sorry.
-/
