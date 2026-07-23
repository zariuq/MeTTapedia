import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Normal

/-!
# Normality of exact runtime type presentations

The exact application-inference relation starts with the empty finite
substitution and threads only the presentation-preserving type matcher.
Therefore every inferred result package carries a normal, idempotent
substitution.  This is the representation invariant needed by the concrete
runtime simulation; it is proved independently of any runtime executable.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ExactNormal

open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact

/-- The ordered argument fold preserves normality through every successful
type-presentation match. -/
theorem PresentationArgumentListMatchRel.output_normal
    {expected actual : List OSLFCore.Atom}
    {incoming output : TypeSubst}
    (derivation : PresentationArgumentListMatchRel
      expected actual incoming output)
    (normal : incoming.Normal) : output.Normal := by
  induction derivation with
  | nil => exact normal
  | cons head tail ih =>
      exact ih (head.output_normal normal)

/-- Every successful application-package inference starts from the empty
normal presentation and emits a package whose private substitution remains
normal. -/
theorem ApplicationPackageSuccessRel.substitution_normal
    {actualTypes : List OSLFCore.Atom} {operatorType : OSLFCore.Atom}
    {result : TypePackage}
    (success : ApplicationPackageSuccessRel
      actualTypes operatorType result) :
    result.substitution.Normal := by
  cases success with
  | mk _ arguments =>
      exact PresentationArgumentListMatchRel.output_normal
        arguments TypeSubst.normal_empty

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ExactNormal
