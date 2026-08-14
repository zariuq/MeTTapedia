import Mettapedia.Languages.MeTTa.PureKernel.RegularFundamental
import Mettapedia.Languages.MeTTa.PureKernel.RegularNormalizationAlgorithm

/-!
# Exact normalization for the regular Pure kernel

The executable accessibility normalizer and the regular fundamental theorem
meet here.  The former supplies computation on an honest termination domain;
the latter proves that every subject admitted by the regular kernel belongs to
that domain.  Type presupposition supplies the same result for every result
type, including the distinguished upper sort.

Consequently regular conversion is decided by direct comparison of computed
normal forms.  The domain evidence is propositional and is erased from the
executable decision path.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.GSLT.LanguageDef.NIKMetalogic

/-- The accessibility normalizer covers every subject and type admitted by the
regular kernel.  This is the exact coupling between the logical-relations
proof and executable normalization. -/
def regularNormalizationSpecification : RegularNormalizationSpecification where
  toNormalizationSpecification := accessibleNormalizationSpecification
  covers_subject := by
    intro n context term type judgment
    exact
      ⟨judgment.subject_accessible,
        (judgment.typing.constantFree_both
          judgment.context.constantFreeCtx).1⟩
  covers_type := by
    intro n context term type judgment
    refine
      ⟨?_, (judgment.typing.constantFree_both
        judgment.context.constantFreeCtx).2⟩
    rcases judgment.type_presupposed with typeIsTop | typeFormed
    · subst type
      exact u1_reductionAccessible n
    · exact
        (show RegularJudgment context type .u1 from
          ⟨judgment.context, typeFormed⟩).subject_accessible
  covers_u1 := by
    intro n
    exact ⟨u1_reductionAccessible n, .u1⟩

/-- Runtime carrier for exact regular conversion.  Its second projection is
only erased evidence that the normalizer terminates on the term. -/
abbrev RegularNormalizationTerm (n : Nat) :=
  regularNormalizationSpecification.toNormalizationSpecification.Term n

/-- Exact, certificate-free conversion authority for the regular kernel. -/
def regularDecidedConversion (n : Nat) :
    DecidedRelation (RegularNormalizationTerm n)
      regularNormalizationSpecification.toNormalizationSpecification.Converts :=
  regularNormalizationSpecification.toNormalizationSpecification.decidedConversion n

/-- The public regular decision is direct comparison of computed normal forms;
there is no supplied proof or certificate input. -/
theorem regularDecidedConversion_is_direct
    (left right : RegularNormalizationTerm n) :
    (regularDecidedConversion n).decide left right =
      decide
        (regularNormalizationSpecification.normalize left.1 left.2 =
          regularNormalizationSpecification.normalize right.1 right.2) :=
  rfl

/-- The executable Boolean accepts exactly fragment-internal conversion. -/
theorem regularDecidedConversion_correct
    (left right : RegularNormalizationTerm n) :
    (regularDecidedConversion n).decide left right = true ↔
      ConstantFreeConv left.1 right.1 :=
  (regularDecidedConversion n).correct left right

/-! ## Positive and negative boundary witnesses -/

/-- The ordinary identity term reaches the executable domain through a real
regular typing judgment, rather than through a hand-supplied accessibility
proof. -/
def coveredRegularIdentity : RegularNormalizationTerm 0 :=
  ⟨.lam (.var 0),
    regularNormalizationSpecification.covers_subject
      regular_identity_judgment⟩

/-- The lower universe reaches the domain as a regularly typed subject. -/
def coveredRegularU0 : RegularNormalizationTerm 0 :=
  ⟨.u0,
    regularNormalizationSpecification.covers_subject
      (show RegularJudgment (.nil : Ctx 0) .u0 .u1 from
        ⟨.nil, .u0_type .nil⟩)⟩

/-- The upper universe is covered explicitly even though it has no type in the
two-universe regular kernel. -/
def coveredRegularU1 : RegularNormalizationTerm 0 :=
  ⟨.u1, regularNormalizationSpecification.covers_u1 0⟩

/-- Positive executable witness: reflexive conversion of a genuinely regular
program is accepted. -/
theorem regular_decides_identity_reflexive :
    (regularDecidedConversion 0).decide
      coveredRegularIdentity coveredRegularIdentity = true := by
  rw [regularDecidedConversion_is_direct]
  exact decide_eq_true rfl

/-- Negative executable witness: the two universe constructors normalize to
distinct forms and are rejected. -/
theorem regular_rejects_u0_u1 :
    (regularDecidedConversion 0).decide
      coveredRegularU0 coveredRegularU1 = false := by
  rw [regularDecidedConversion_is_direct]
  have u0Normal :
      regularNormalizationSpecification.normalize
        coveredRegularU0.1 coveredRegularU0.2 = .u0 :=
    (u0_redNormal 0).redStar_eq (by
      simpa [coveredRegularU0] using
        (regularNormalizationSpecification.reduces
          coveredRegularU0.1 coveredRegularU0.2))
  have u1Normal :
      regularNormalizationSpecification.normalize
        coveredRegularU1.1 coveredRegularU1.2 = .u1 :=
    (u1_redNormal 0).redStar_eq (by
      simpa [coveredRegularU1] using
        (regularNormalizationSpecification.reduces
          coveredRegularU1.1 coveredRegularU1.2))
  rw [u0Normal, u1Normal]
  decide

/-- Negative domain witness: the untyped self-reducing omega term remains
outside the exact regular-normalization authority. -/
theorem regularOmega_not_in_regular_normalization_domain :
    ¬ regularNormalizationSpecification.Domain regularOmega :=
  regularNormalizationSpecification.toNormalizationSpecification.omega_not_in_domain

/-! ## Axiom audit -/

#print axioms regularNormalizationSpecification
#print axioms regularDecidedConversion_correct
#print axioms regular_decides_identity_reflexive
#print axioms regular_rejects_u0_u1
#print axioms regularOmega_not_in_regular_normalization_domain

end Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary
