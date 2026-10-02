import Mettapedia.OSLF.Syntax.IntrinsicScopedEmptyEquationClassComparison
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalTreeSubstitution

/-!
# Firing coverage across the actual empty equation quotient

The independently proved inverse binding-clone maps transport complete
existing local trees. No events are identified merely because their
endpoints agree.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedEmptyEquationTreeComparison

open AuthoredPositionedRulePolynomial (Judgment mapJudgment mapJudgment_id mapJudgment_comp)
open IntrinsicScopedLocalPolynomial (LocalRule Tree mapTree)
open IntrinsicScopedEmptyEquationClassComparison (equations algebra decode projection_decode)

variable {S : Signature} (schema : List (MetaArity S))

/-- Decoding both projected endpoints recovers the complete original judgment. -/
theorem decode_judgment (j : Judgment (BindingCloneAlgebra.terms S)) :
    mapJudgment (decode schema)
      (mapJudgment (BindingEquationQuotientModel.projection (equations schema)) j) = j :=
  (mapJudgment_comp _ _ j).symm.trans
    ((congrArg (fun map => mapJudgment map j) (projection_decode schema)).trans
      (mapJudgment_id (BindingCloneAlgebra.terms S) j))

/-- The empty equation quotient admits exactly the original firing judgments. -/
theorem raw_iff_quotient (R : List (LocalRule S)) (j : Judgment (BindingCloneAlgebra.terms S)) :
    Nonempty (Tree R (BindingCloneAlgebra.terms S) j) ↔
      Nonempty (Tree R (algebra schema)
        (mapJudgment (BindingEquationQuotientModel.projection (equations schema)) j)) := by
  constructor
  · rintro ⟨tree⟩
    exact ⟨mapTree R (BindingEquationQuotientModel.projection (equations schema)) j tree⟩
  · rintro ⟨tree⟩
    exact ⟨decode_judgment schema j ▸ mapTree R (decode schema) _ tree⟩

end Mettapedia.OSLF.Binding.IntrinsicScopedEmptyEquationTreeComparison
