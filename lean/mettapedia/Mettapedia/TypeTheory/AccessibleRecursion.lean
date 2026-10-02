import Mettapedia.Order.AccessibilityCode
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Codes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Proofs
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Package
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Formation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Model
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Strong
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Unguarded
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Curry
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Inert
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Transport
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Confluence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Divergence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.AccessibleRecursionProp
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.AccessibleRecursionControls
import Mettapedia.Algorithms.WellFoundedServices.InertRecursor
import Mettapedia.Algorithms.WellFoundedServices.MeasuredLoop
import Mettapedia.Algorithms.WellFoundedServices.DependencyAnalysis
import Mettapedia.Algorithms.WellFoundedServices.DependencyExamples
import Mettapedia.Algorithms.WellFoundedServices.ConstraintPlanning
import Mettapedia.Algorithms.WellFoundedServices.ConstraintExamples
import Mettapedia.Algorithms.WellFoundedServices.Capabilities

/-!
# Accessible recursion

Well-founded recursion as an extension package of the parameterized Π/Σ/Id
calculus, and programs written through it.

* The package (`Calculi.ParameterizedPiSigmaId.AccessibleRecursion`): an
  accessibility code with introduction and inversion, an inert recursor, and
  its propositional unfolding under the accessibility premise. Conversion and
  the kernel's conversion algorithm are unchanged on problems without the new
  constants (`Signature.conv_iff`, `Signature.algorithm_iff`); a model that computes the
  recursor proves consistency (`consistent`), also for the variant with the
  definitional unfolding (`strong_consistent`); without the premise, the
  unfolding derives a closed proof of falsity (`CurryData.curry_falsum`). A concrete
  instance over the tower with an identity eliminator discharges every
  hypothesis (`Instances.AccessibleRecursionProp`).
* Controls (`Transport`, `Confluence`, `Divergence`, and the instance's
  `Instances.AccessibleRecursionControls`): transport along the propositional
  unfolding proves a goal about the unfolded call (`Signature.transport_goal`);
  the package's conversion is Church–Rosser (`Confluence.churchRosser`) and does
  not identify the recursor with its unfolding (`Signature.separation`); the
  strong variant has a typed term with no normal form
  (`Signature.loop_no_normal_form`), on which a budgeted weak-head checker is
  incomplete at every budget (`Signature.loop_whCheck_incomplete`).
* The code read in the model is `Mettapedia.Order.AccCode`, equivalent to
  `Acc`.
* Programs (`Algorithms.WellFoundedServices`): dependency analysis (affected
  items, rebuild waves, cycle detection, folds over dependencies, incremental
  rebuild soundness) and finite constraint planning (backtracking with
  witnesses and checked refutations), each measure-based and through an inert
  recursor, with agreement theorems; and the three capabilities kept apart:
  total computation, productive watchers, budgeted search.
-/
