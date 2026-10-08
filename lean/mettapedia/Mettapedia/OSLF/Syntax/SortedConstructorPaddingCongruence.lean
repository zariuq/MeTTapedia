import Mettapedia.OSLF.Syntax.SortedConstructorPaddingRelativePushout
import Mettapedia.CategoryTheory.GroundPathContextCongruence

/-!
# Complete contextual congruence on the actual padding equation quotient

The earned normalization equivalence reflects all closed-origin RPOs,
including origin-identity spans. Literal-label IPO bisimilarity is therefore
preserved by every actual equation-class context for every chosen rule set.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.SortedConstructors.Padding

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence

universe u v

variable (signature : Signature.{u,v}) (paddingSort : signature.Srt)

theorem equation_origin_hasRPO {first second : EquationObject signature paddingSort}
    (left : (.origin : EquationObject signature paddingSort) ⟶ first)
    (right : (.origin : EquationObject signature paddingSort) ⟶ second) :
    HasRelativePushouts left right :=
  reflects_hasRelativePushouts (normalizationFunctor signature paddingSort)
    (normalization_objects signature paddingSort)
    (origin_hasRelativePushouts (action signature)
      ((normalizationFunctor signature paddingSort).map left)
      ((normalizationFunctor signature paddingSort).map right))

theorem equation_context_congruence
    (rules : ReactionRule (.origin : EquationObject signature paddingSort) → Prop)
    {first second : EquationObject signature paddingSort}
    (left right : (.origin : EquationObject signature paddingSort) ⟶ first)
    (related : IPOBisimilar rules left right) (context : first ⟶ second) :
    IPOBisimilar rules (left ≫ context) (right ≫ context) :=
  ipoBisimilar_comp (fun _ agent rule _ => equation_origin_hasRPO signature paddingSort agent rule.redex)
    related context

end Mettapedia.OSLF.SortedConstructors.Padding
