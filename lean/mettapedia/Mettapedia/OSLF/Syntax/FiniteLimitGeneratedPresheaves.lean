import Mettapedia.OSLF.Syntax.LawvereFiniteLimitBoundary
import Mettapedia.OSLF.Syntax.FiniteLimitGeneratedYoneda

/-!
# Finite-limit-generated context presheaves

For any binding signature, Yoneda embeds the raw substitution contexts into
their presheaf category. Closing the representables under terminal objects,
binary products, and equalizers gives a finitely complete full subcategory.
Mathlib's inductive limit closure proves minimality among ambient object
properties closed under these three shapes.

This is a concrete finite-limit-closed realization. Its universal property as
the free finite-limit completion of the authored context category has not been
proved here; nor does finite-limit closure supply the Cartesian-closed and
predicate structure required by the full classifying theory.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding

open CategoryTheory
open CategoryTheory.Limits

variable (S : Signature)

abbrev ContextPresheaf :=
  Mettapedia.OSLF.FiniteLimitYoneda.Presheaf (Syntactic.Ctxt S)

/-- Presheaves isomorphic to an authored context's Yoneda image. -/
def representedContext : ObjectProperty (ContextPresheaf S) :=
  Mettapedia.OSLF.FiniteLimitYoneda.Representable (Syntactic.Ctxt S)

/-- The finite-limit-closed part of the context presheaf category generated
by the authored contexts. -/
def finiteLimitGenerated : ObjectProperty (ContextPresheaf S) :=
  Mettapedia.OSLF.FiniteLimitYoneda.Generated (Syntactic.Ctxt S)

theorem represented_in_finiteLimitGenerated (Γ : Syntactic.Ctxt S) :
    finiteLimitGenerated S (yoneda.obj Γ) := by
  exact Mettapedia.OSLF.FiniteLimitYoneda.represented (Syntactic.Ctxt S) Γ

theorem finiteLimitGenerated_hasFiniteLimits :
    HasFiniteLimits (finiteLimitGenerated S).FullSubcategory :=
  Mettapedia.OSLF.FiniteLimitYoneda.hasFiniteLimits (Syntactic.Ctxt S)

instance : HasFiniteLimits (finiteLimitGenerated S).FullSubcategory :=
  finiteLimitGenerated_hasFiniteLimits S

/-- The full-subcategory inclusion constructs each elementary limit in the
ambient presheaf category, including equalizers of represented arrows. -/
@[instance_reducible]
noncomputable def finiteLimitGenerated_inclusion_creates_shape
    (shape : FiniteLimitShape) :
    CreatesLimitsOfShape (finiteLimitDiagram shape)
      (finiteLimitGenerated S).ι := by
  have : (finiteLimitGenerated S).IsClosedUnderLimitsOfShape
      (finiteLimitDiagram shape) := by
    unfold finiteLimitGenerated Mettapedia.OSLF.FiniteLimitYoneda.Generated
    infer_instance
  exact createsLimitsOfShapeFullSubcategoryInclusion
    (finiteLimitDiagram shape) (finiteLimitGenerated S)

/-- This is the least isomorphism- and elementary-finite-limit-closed class of
presheaves that contains all represented contexts. -/
theorem finiteLimitGenerated_le (Q : ObjectProperty (ContextPresheaf S))
    [Q.IsClosedUnderIsomorphisms]
    [∀ shape, Q.IsClosedUnderLimitsOfShape (finiteLimitDiagram shape)]
    (h : representedContext S ≤ Q) : finiteLimitGenerated S ≤ Q :=
  Mettapedia.OSLF.FiniteLimitYoneda.least (Syntactic.Ctxt S) Q h

end Mettapedia.OSLF.Binding

namespace Mettapedia.OSLF.Binding.UnaryContextBoundary

open CategoryTheory
open CategoryTheory.Limits

theorem fixedPointPresheaf_in_finiteLimitGenerated :
    finiteLimitGenerated signature fixedPointPresheaf := by
  change (representedContext signature).limitsClosure finiteLimitDiagram
    (limit (parallelPair yonedaIdentity yonedaNext))
  have : ((representedContext signature).limitsClosure finiteLimitDiagram).IsClosedUnderLimitsOfShape
      WalkingParallelPair := by
    change ((representedContext signature).limitsClosure finiteLimitDiagram).IsClosedUnderLimitsOfShape
      (finiteLimitDiagram FiniteLimitShape.equalizer)
    infer_instance
  apply ObjectProperty.prop_limit
  intro j
  cases j with
  | zero => exact represented_in_finiteLimitGenerated signature one
  | one => exact represented_in_finiteLimitGenerated signature one

/-- The finite-limit-generated subcategory properly extends the represented
contexts for this signature. -/
theorem fixedPointPresheaf_not_representedContext :
    ¬ representedContext signature fixedPointPresheaf := by
  intro h
  rcases h.has_representation with ⟨Γ, ⟨representation⟩⟩
  exact fixedPointPresheaf_not_representable
    ⟨Γ, ⟨(Functor.representableByEquiv representation).symm⟩⟩

end Mettapedia.OSLF.Binding.UnaryContextBoundary
