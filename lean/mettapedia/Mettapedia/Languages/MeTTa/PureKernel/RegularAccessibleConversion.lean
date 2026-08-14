import Mettapedia.Languages.MeTTa.PureKernel.RegularContextualSigma

/-!
# The accessibility guard on semantic conversion

Raw fragment conversion is symmetric.  Strong normalization is not backward
closed: an erasing beta redex can convert to a normal form while retaining a
looping argument.  A logical relation may therefore transport a candidate
meaning across conversion only after accessibility of both type-code endpoints
has been earned, normally from the simultaneous formation theorem.

This module packages that exact guard and proves that it is an equivalence on
accessible constant-free terms.  It also gives positive and negative controls.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Reduction

/-- Fragment-internal conversion whose two endpoints have independently
earned accessibility.  The accessibility fields are semantic evidence, not a
claim that raw conversion preserves normalization backward. -/
structure AccessibleConstantFreeConv (source target : PureTm n) : Prop where
  converts : ConstantFreeConv source target
  source_accessible : ReductionAccessible source
  target_accessible : ReductionAccessible target

namespace AccessibleConstantFreeConv

theorem refl (term : PureTm n) (constantFree : ConstantFree term)
    (accessible : ReductionAccessible term) :
    AccessibleConstantFreeConv term term :=
  ⟨.refl term constantFree, accessible, accessible⟩

theorem symm {source target : PureTm n}
    (conversion : AccessibleConstantFreeConv source target) :
    AccessibleConstantFreeConv target source :=
  ⟨.symm conversion.converts,
    conversion.target_accessible, conversion.source_accessible⟩

theorem trans {first middle last : PureTm n}
    (left : AccessibleConstantFreeConv first middle)
    (right : AccessibleConstantFreeConv middle last) :
    AccessibleConstantFreeConv first last :=
  ⟨.trans left.converts right.converts,
    left.source_accessible, right.target_accessible⟩

theorem toConv {source target : PureTm n}
    (conversion : AccessibleConstantFreeConv source target) :
    Mettapedia.Languages.MeTTa.PureKernel.Typing.Conv source target :=
  conversion.converts.toConv

end AccessibleConstantFreeConv

/-! ## Positive beta control -/

theorem regularIdentityU0_reduces_to_u0 :
    Red regularIdentityU0 (.u0 : PureTm 0) := by
  simpa [regularIdentityU0, inst0, subst0, subst] using
    (Red.betaPi (.var (0 : Fin 1)) (.u0 : PureTm 0))

theorem regularIdentityU0_conv_u0 :
    ConstantFreeConv regularIdentityU0 (.u0 : PureTm 0) :=
  .rel ⟨regularIdentityU0_reduces_to_u0,
    regularIdentityU0_constantFree, .u0⟩

/-- Ordinary beta conversion lies inside the guarded relation because both
the redex and its normal form are independently accessible. -/
theorem regularIdentityU0_accessible_conversion :
    AccessibleConstantFreeConv regularIdentityU0 (.u0 : PureTm 0) :=
  ⟨regularIdentityU0_conv_u0,
    regularIdentityU0_reductionAccessible, reductionAccessible_u0⟩

/-! ## Negative erasing control -/

theorem regularErasingOmega_constantFree :
    ConstantFree regularErasingOmega :=
  .app (.lam .u0) regularOmega_constantFree

theorem regularErasingOmega_conv_u0 :
    ConstantFreeConv regularErasingOmega (.u0 : PureTm 0) :=
  .rel ⟨regularErasingOmega_reduces_to_u0,
    regularErasingOmega_constantFree, .u0⟩

/-- The same raw conversion shape is rejected by the semantic guard when the
source hides omega. -/
theorem regularErasingOmega_not_accessible_conversion :
    ¬ AccessibleConstantFreeConv regularErasingOmega (.u0 : PureTm 0) := by
  intro conversion
  exact regularErasingOmega_not_accessible conversion.source_accessible

/-- There is no unrestricted rule transporting accessibility backward across
fragment conversion.  Target-formation accessibility is a real premise of the
future conversion case, not bureaucratic decoration. -/
theorem unrestricted_conversion_transport_is_unsound :
    ¬ (∀ {source target : PureTm 0},
      ConstantFreeConv source target →
        ReductionAccessible target →
          ReductionAccessible source) := by
  intro transport
  exact regularErasingOmega_not_accessible
    (transport regularErasingOmega_conv_u0 reductionAccessible_u0)

/-! ## Axiom audit -/

#print axioms AccessibleConstantFreeConv.refl
#print axioms AccessibleConstantFreeConv.symm
#print axioms AccessibleConstantFreeConv.trans
#print axioms regularIdentityU0_accessible_conversion
#print axioms regularErasingOmega_conv_u0
#print axioms regularErasingOmega_not_accessible_conversion
#print axioms unrestricted_conversion_transport_is_unsound

end Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary
