import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# OSLF synthesis from a reduction span

A reduction span is the semantic core needed to generate the behavioral
modalities of OSLF.  This module packages an arbitrary span as a one-sorted
rewrite system and runs the full predicate-valued OSLF construction on it.

This is useful when an executable language already exposes proof-relevant
edges as a span.  It avoids inventing a second operational relation merely to
connect that language to rich native types.
-/

namespace Mettapedia.OSLF.Framework.ReductionSpanTypeSynthesis

open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

universe uTerm

/-- The GSLT denoted by a reduction span. Its equation theory is equality;
the span supplies the proof-relevant one-step relation. -/
def spanGSLT {Term : Type uTerm} (span : ReductionSpan Term) :
    Mettapedia.GSLT.GSLT :=
  equalityGSLT Term (fun source target =>
    ∃ edge : span.Edge,
      span.source edge = source ∧ span.target edge = target)

/-- The one-sorted rewrite-system view of `spanGSLT`. -/
def spanRewriteSystem {Term : Type uTerm} (span : ReductionSpan Term) :
    RewriteSystem :=
  gsltRewriteSystem (spanGSLT span)

/-- The generated diamond is exactly existential forward reachability along
one edge of the span. -/
theorem spanDiamond_spec {Term : Type uTerm} (span : ReductionSpan Term)
    (predicate : Term → Prop) (source : Term) :
    derivedDiamond span predicate source ↔
      ∃ target, (spanRewriteSystem span).Reduces source target ∧
        predicate target := by
  constructor
  · rintro ⟨edge, sourceEq, targetMeaning⟩
    exact ⟨span.target edge, ⟨edge, sourceEq, rfl⟩, targetMeaning⟩
  · rintro ⟨target, ⟨edge, sourceEq, targetEq⟩, targetMeaning⟩
    exact ⟨edge, sourceEq,
      Eq.mp (congrArg predicate targetEq.symm) targetMeaning⟩

/-- The generated box is exactly universal backward reachability along one
edge of the span. -/
theorem spanBox_spec {Term : Type uTerm} (span : ReductionSpan Term)
    (predicate : Term → Prop) (target : Term) :
    derivedBox span predicate target ↔
      ∀ source, (spanRewriteSystem span).Reduces source target →
        predicate source := by
  constructor
  · intro universal source reduction
    obtain ⟨edge, sourceEq, targetEq⟩ := reduction
    exact sourceEq ▸ universal edge targetEq
  · intro universal edge targetEq
    exact universal (span.source edge) ⟨edge, rfl, targetEq⟩

/-- The OSLF generated from the span's equality-equation GSLT. This is a thin
adapter to `gsltOSLF`, not an independent modal construction. -/
def spanOSLF {Term : Type uTerm} (span : ReductionSpan Term) :
    OSLFTypeSystem (spanRewriteSystem span) :=
  gsltOSLF (spanGSLT span)

/-- Embed any predicate as a rich OSLF native type over the span. -/
def predicateNativeType {Term : Type uTerm} (span : ReductionSpan Term)
    (predicate : Term → Prop) : NativeTypeOf (spanOSLF span) where
  sort := ()
  pred := saturatePredicate (spanGSLT span) predicate

/-- The predicate embedding preserves inhabitation definitionally. -/
theorem satisfies_predicateNativeType_iff {Term : Type uTerm}
    (span : ReductionSpan Term) (predicate : Term → Prop) (term : Term) :
    (spanOSLF span).satisfies term
        (predicateNativeType span predicate).pred ↔ predicate term :=
  saturatePredicate_apply_iff_of_equiv_iff_eq
    (spanGSLT span) (equalityGSLT_equiv _ _) predicate term

end Mettapedia.OSLF.Framework.ReductionSpanTypeSynthesis
