import Mettapedia.OSLF.Syntax.CartesianModelLexInternalGeneration

/-!
# Transporting target properties through generated finite presentations

An interpretation preserving finite limits sends all relative finite
presentations into any target-side object class that contains the authored
contexts and is closed under the elementary finite limits. This is the
induction needed to recognize representable values in a presheaf extension;
it does not itself construct that extension.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.Binding (FiniteLimitShape finiteLimitDiagram)

universe u v

variable (C : Type) [SmallCategory C] [HasFiniteProducts C]
variable (D : Type u) [Category.{v} D]

/-- A property of target objects stable under finite limits can be checked
on authored contexts alone for a left-exact interpretation of all relative
presentations. -/
theorem targetProperty_of_authoredContexts
    (T : LeftExactTargetInterpretations C D)
    (Q : ObjectProperty D)
    [Q.IsClosedUnderIsomorphisms]
    [∀ a : FiniteLimitShape,
      Q.IsClosedUnderLimitsOfShape (finiteLimitDiagram a)]
    (hbase : ∀ X : C, Q (T.1.obj ((authoredContext C).obj X)))
    (X : FinitePresentationObjects C) :
    Q (T.1.obj X) := by
  let R : ObjectProperty (FinitePresentationObjects C) := Q.inverseImage T.1
  have hT : PreservesFiniteLimits T.1 := T.2
  have : R.IsClosedUnderIsomorphisms := by
    dsimp [R]
    infer_instance
  have (a : FiniteLimitShape) :
      R.IsClosedUnderLimitsOfShape (finiteLimitDiagram a) := by
    have : FinCategory (finiteLimitDiagram a) := by
      cases a <;> dsimp [finiteLimitDiagram] <;> infer_instance
    have : PreservesLimitsOfShape (finiteLimitDiagram a) T.1 :=
      hT.preservesFiniteLimits _
    dsimp [R]
    infer_instance
  have hclosure : AuthoredFiniteLimitClosure C ≤ R := by
    change (ObjectProperty.ofObj (authoredContext C).obj).limitsClosure
      finiteLimitDiagram ≤ R
    apply ObjectProperty.limitsClosure_le
    intro Y hY
    rcases hY with ⟨Z⟩
    exact hbase Z
  exact hclosure X (finitePresentationObjects_authoredFiniteLimitGenerated C X)

end Mettapedia.OSLF.CartesianContextModels
