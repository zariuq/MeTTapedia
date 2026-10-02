import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchLifting
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchProgress

/-!
# The facts about weak-head forms of the object package, without hypotheses

The transfer from the annotation (`objectRules_formFacts_of`) needs two premises. Both hold:

* derivations of the package lift to its annotation (`objectRules_liftType`,
  `objectRules_liftTypeEq`);
* annotated types of a universe take a weak-head step or erase to a weak-head form
  (`objectChurch_typeProgress`).

So the object package, the executable equations together with the proposition codes, has the
facts about weak-head forms (`objectRules_formFacts`), and its conversion algorithm is complete
(`objectRules_algorithmicComplete`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization

namespace CodeModel

/-- **The facts about weak-head forms of the object package.** -/
theorem objectRules_formFacts : FormFacts objectRules objectRoles :=
  objectRules_formFacts_of_progress objectChurch_typeProgress

/-- **The conversion algorithm of the object package is complete.** -/
theorem objectRules_algorithmicComplete : AlgorithmicComplete objectRules objectRoles :=
  objectRules_algorithmicComplete_of_progress objectChurch_typeProgress

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
