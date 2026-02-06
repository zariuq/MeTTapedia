import Mettapedia.OSLF.Framework.RewriteSystem

/-!
# OSLF Category-Theoretic Bridge

This file documents the categorical interpretation of the OSLF construction,
connecting the abstract framework (RewriteSystem.lean) to the GSLT categorical
infrastructure (GSLT/Core/).

## The Categorical Picture

In the topos-theoretic setting (Williams & Stay, "Native Type Theory"):

1. A lambda-theory T gives a presheaf topos T-hat = Set^{T^op}
2. The Yoneda embedding y : T -> T-hat sends each sort to its representable presheaf
3. The subobject functor Sub : T-hat -> Set sends each presheaf to its set of subobjects
4. The Native Type functor NT = integral (Sub . y) is the Grothendieck construction

## Modal Operators via Change-of-Base

Per OSLF section 4 + section 6:

The reduction relation R ⊆ Proc x Proc gives a span:

```
        E (reduction graph)
       / \
  src /   \ tgt
     /     \
    v       v
   Proc    Proc
```

The modal operators arise from change-of-base along this span:

  diamond(phi) = directImage_tgt (pullback_src phi)  = exists_tgt . src*
  box(phi)     = universalImage_src (pullback_tgt phi) = forall_src . tgt*

These use the adjoint triple exists_f -| f* -| forall_f from GSLT/Core/ChangeOfBase.lean.

The Galois connection diamond -| box follows from the composition of adjunctions:
  exists_tgt . src* -| src_* . forall_tgt   (not quite, need careful composition)

In practice, for the rho-calculus instance (Framework/RhoInstance.lean):
  diamond = possiblyProp, box = relyProp
and the Galois connection is proven directly from the definitions.

## Connection Points

- **GSLT/Core/LambdaTheoryCategory.lean**: Proper Mathlib-based SubobjectFibration with
  categories, CartesianMonoidalCategory, MonoidalClosed, HasFiniteLimits

- **GSLT/Core/ChangeOfBase.lean**: The adjoint triple exists_f -| f* -| forall_f with
  `stepForward` = exists_tgt . src* and `secureStepForward` = forall_tgt . src*

- **Framework/RewriteSystem.lean**: Abstract OSLFTypeSystem with diamond/box/galois

- **Framework/RhoInstance.lean**: Concrete rho-calculus instance with proven Galois connection

## What Remains to Connect

To fully bridge the abstract and categorical layers, one would need:

1. **Categorical RewriteSystem**: Embed RewriteSystem into a category with
   proper products (not the placeholder `prod := fun X _ => X`)

2. **Reduction as morphism**: Express the reduction relation R as a
   morphism or subobject in the topos, giving the span E -> Proc x Proc

3. **Change-of-base diamond = OSLFTypeSystem.diamond**: Show that
   stepForward src tgt from ChangeOfBase agrees with diamond from OSLFTypeSystem
   when both are specialized to the rho-calculus

4. **Beck-Chevalley**: The GSLT ChangeOfBase includes a Beck-Chevalley condition;
   show it holds for the OSLF span

## References

- Meredith & Stay, "Operational Semantics in Logical Form" sections 4, 6
- Williams & Stay, "Native Type Theory" (ACT 2021) section 3
- Johnstone, "Sketches of an Elephant" Vol 1, section 1.1
-/

namespace Mettapedia.OSLF.Framework.CategoryBridge

open Mettapedia.OSLF.Framework

/-! ## The Categorical Correspondence (Specification)

These theorems specify what it MEANS for the categorical and abstract
constructions to agree. They require a full categorical model to prove.
-/

/-- Specification: For any OSLFTypeSystem whose diamond arises from
    change-of-base along a span, the Galois connection holds.

    This is the categorical EXPLANATION of why diamond -| box:
    it follows from exists_f -| f* -| forall_f applied to the reduction span.

    For the rho-calculus, this is proven constructively in RhoInstance.lean
    without needing the categorical machinery.
-/
theorem galois_from_adjoint_triple_spec :
    ∀ (R : RewriteSystem) (ts : OSLFTypeSystem R),
    -- If the type system has the Galois property (which it does by definition)...
    (∀ φ ψ, (∀ p, ts.satisfies p (ts.diamond φ) → ts.satisfies p ψ) ↔
             (∀ p, ts.satisfies p φ → ts.satisfies p (ts.box ψ))) →
    -- ...then the categorical interpretation (change-of-base) would also yield it.
    -- This is trivially true since we're just restating the hypothesis,
    -- but it documents WHERE the categorical proof would go.
    True := by
  intros
  trivial

/-! ## Summary

This file serves as a **specification document** for the categorical bridge.

**What IS proven:**
- The abstract OSLF framework (RewriteSystem.lean) correctly captures the paper
- The rho-calculus instance (RhoInstance.lean) has a proven Galois connection
- The GSLT infrastructure (GSLT/Core/) has the right categorical primitives

**What REMAINS to prove (future work):**
- Embed RewriteSystem into a proper category
- Express reduction as a span in the category
- Show categorical diamond = abstract diamond for concrete instances
- Derive the Galois connection from change-of-base adjunctions

**Key insight:** The abstract framework is CORRECT even without the categorical bridge.
The Galois connection is provable directly from the definitions (as done in
RhoInstance.lean). The categorical bridge would provide a SECOND proof via
general topos-theoretic machinery, which would:
1. Apply to any calculus, not just rho-calculus
2. Give additional structure (Beck-Chevalley, etc.)
3. Connect to the full presheaf topos picture
-/

end Mettapedia.OSLF.Framework.CategoryBridge
