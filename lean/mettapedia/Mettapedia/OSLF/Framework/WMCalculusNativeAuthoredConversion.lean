import Mettapedia.OSLF.Framework.WMCalculusStructuralPresentation
import Mettapedia.OSLF.Framework.WMCalculusEvidenceConversionSorted

/-!
# Typed replay of WM evidence conversion through the authored presentation

This module retains a type certificate for every intermediate WM evidence
term while replaying generated evidence conversion through actual authored
equation and computation steps. The resulting native open-pattern path is
one-way completeness evidence. The raw authored relation may contain other
steps, and no reverse semantic-soundness claim is made for all of them.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusNativeAuthoredConversion

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusEncoding
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusSortedEncoding
open Mettapedia.OSLF.Framework.WMCalculusStructuralPresentation
open Mettapedia.OSLF.Framework.WMCalculusEvidenceConversion
open Mettapedia.OSLF.Framework.WMCalculusEvidenceConversionSorted
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- WM evidence syntax with its free-atom typing certificate. -/
abbrev TypedEvidence (free : FreeTypeContext) :=
  {term : WMTerm .evidence // AtomsTyped free term}

/-- The canonical WM encoder lands in the existing native open-pattern
carrier, with no new object syntax. -/
def asNativeOpen (free : FreeTypeContext) (bound : List TypeExpr)
    (term : TypedEvidence free) :
    OpenPattern wmStructuralLanguageDef free bound (sortType .evidence) :=
  ⟨encodeWM term.1,
    (encodeWM_openPatternWellSorted_iff_bound wmStructuralLanguageDef rfl
      free bound term.1).2 term.2⟩

/-- One actual authored equation-or-computation step between encoded,
individually typed WM evidence terms. -/
def typedAuthoredEdge (free : FreeTypeContext)
    (first second : TypedEvidence free) : Prop :=
  AuthoredContextStep (encodeWM first.1) (encodeWM second.1)

/-- Symmetric conversion paths whose every vertex is a typed WM evidence
term and whose every edge is an actual authored step. -/
def typedAuthoredPath (free : FreeTypeContext) :
    TypedEvidence free → TypedEvidence free → Prop :=
  Relation.EqvGen (typedAuthoredEdge free)

/-- The same authored steps induce a conversion setoid on the exact native
open-pattern carrier. This is a typed path relation, not an asserted semantic
equality for every raw authored generator. -/
def nativeOpenAuthoredSetoid (free : FreeTypeContext)
    (bound : List TypeExpr) :
    Setoid (OpenPattern wmStructuralLanguageDef free bound
      (sortType .evidence)) where
  r := Relation.EqvGen
    (fun first second => AuthoredContextStep first.1 second.1)
  iseqv :=
    { refl := Relation.EqvGen.refl
      symm := fun relation => Relation.EqvGen.symm _ _ relation
      trans := fun first second => Relation.EqvGen.trans _ _ _ first second }

/-- Forget only the WM syntax index, retaining every intermediate native
typed representative and the authored edge that relates it to the next. -/
theorem typedAuthoredPath_to_nativeOpen (free : FreeTypeContext)
    (bound : List TypeExpr) {first second : TypedEvidence free}
    (path : typedAuthoredPath free first second) :
    (nativeOpenAuthoredSetoid free bound).r
      (asNativeOpen free bound first) (asNativeOpen free bound second) := by
  induction path with
  | rel first second edge => exact Relation.EqvGen.rel _ _ edge
  | refl term => exact Relation.EqvGen.refl _
  | symm first second relation ih => exact Relation.EqvGen.symm _ _ ih
  | trans first middle second firstPath secondPath firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- Typed evidence combination uses the already-authored Combine constructor. -/
def typedCombine {free : FreeTypeContext}
    (first second : TypedEvidence free) : TypedEvidence free :=
  ⟨.combine first.1 second.1, ⟨first.2, second.2⟩⟩

theorem typedAuthoredEdge_combine_left {free : FreeTypeContext}
    {first second : TypedEvidence free} (other : TypedEvidence free)
    (edge : typedAuthoredEdge free first second) :
    typedAuthoredEdge free (typedCombine first other)
      (typedCombine second other) := by
  have filled := authoredContextStep_fill
    (.apply "Combine" [] .hole [encodeWM other.1]) edge
  simpa [typedAuthoredEdge, typedCombine, encodeWM, pCombine,
    OneHoleContext.fill] using filled

theorem typedAuthoredEdge_combine_right {free : FreeTypeContext}
    (other : TypedEvidence free) {first second : TypedEvidence free}
    (edge : typedAuthoredEdge free first second) :
    typedAuthoredEdge free (typedCombine other first)
      (typedCombine other second) := by
  have filled := authoredContextStep_fill
    (.apply "Combine" [encodeWM other.1] .hole []) edge
  simpa [typedAuthoredEdge, typedCombine, encodeWM, pCombine,
    OneHoleContext.fill] using filled

private theorem typedAuthoredPath_map {free : FreeTypeContext}
    (map : TypedEvidence free → TypedEvidence free)
    (mapEdge : ∀ {first second : TypedEvidence free},
      typedAuthoredEdge free first second →
        typedAuthoredEdge free (map first) (map second))
    {first second : TypedEvidence free}
    (path : typedAuthoredPath free first second) :
    typedAuthoredPath free (map first) (map second) := by
  induction path with
  | rel first second edge => exact Relation.EqvGen.rel _ _ (mapEdge edge)
  | refl term => exact Relation.EqvGen.refl _
  | symm first second relation ih => exact Relation.EqvGen.symm _ _ ih
  | trans first middle second firstPath secondPath firstIH secondIH =>
      exact Relation.EqvGen.trans _ _ _ firstIH secondIH

/-- Congruence of certified authored paths for the evidence constructor. -/
theorem typedAuthoredPath_combine {free : FreeTypeContext}
    {first first' second second' : TypedEvidence free}
    (left : typedAuthoredPath free first first')
    (right : typedAuthoredPath free second second') :
    typedAuthoredPath free
      (typedCombine first second) (typedCombine first' second') := by
  have leftPath := typedAuthoredPath_map
    (fun term => typedCombine term second)
    (fun edge => typedAuthoredEdge_combine_left second edge) left
  have rightPath := typedAuthoredPath_map
    (typedCombine first')
    (fun edge => typedAuthoredEdge_combine_right first' edge) right
  exact Relation.EqvGen.trans _ _ _ leftPath rightPath

/-- Every generator of the complete WM evidence conversion has a replay in
the authored presentation with typed WM evidence at every intermediate
vertex. The proof retains actual authored steps; it does not identify the
broader raw authored conversion with the generated WM relation. -/
theorem evidenceConversion_typedAuthoredPath
    (free : FreeTypeContext) {first second : WMTerm .evidence}
    (conversion : EvidenceConversion first second) :
    ∀ firstTyped : AtomsTyped free first,
      ∃ secondTyped : AtomsTyped free second,
        typedAuthoredPath free
          ⟨first, firstTyped⟩ ⟨second, secondTyped⟩ := by
  induction conversion with
  | refl term =>
      intro typed
      exact ⟨typed, Relation.EqvGen.refl _⟩
  | @symm first second original inductionHypothesis =>
      intro secondTyped
      have firstTyped : AtomsTyped free first :=
        (evidenceConversion_atomsTyped_iff free original).2 secondTyped
      obtain ⟨otherSecondTyped, path⟩ := inductionHypothesis firstTyped
      exact ⟨firstTyped, Relation.EqvGen.symm _ _ path⟩
  | trans _ _ firstIH secondIH =>
      intro firstTyped
      obtain ⟨middleTyped, firstPath⟩ := firstIH firstTyped
      obtain ⟨secondTyped, secondPath⟩ := secondIH middleTyped
      exact ⟨secondTyped,
        Relation.EqvGen.trans _ _ _ firstPath secondPath⟩
  | combine _ _ firstIH secondIH =>
      intro typed
      obtain ⟨firstTyped, leftPath⟩ := firstIH typed.1
      obtain ⟨secondTyped, rightPath⟩ := secondIH typed.2
      exact ⟨⟨firstTyped, secondTyped⟩,
        typedAuthoredPath_combine leftPath rightPath⟩
  | comm first second =>
      intro typed
      refine ⟨⟨typed.2, typed.1⟩, Relation.EqvGen.rel _ _ ?_⟩
      exact ⟨.hole, _, _, rfl, rfl,
        Or.inl (combine_comm_equivalent _ _)⟩
  | assoc first second third =>
      intro typed
      refine ⟨⟨typed.1.1, typed.1.2, typed.2⟩,
        Relation.EqvGen.rel _ _ ?_⟩
      exact ⟨.hole, _, _, rfl, rfl,
        Or.inl (combine_assoc_equivalent _ _ _)⟩
  | zero term =>
      intro typed
      refine ⟨typed.1, Relation.EqvGen.rel _ _ ?_⟩
      exact ⟨.hole, _, _, rfl, rfl,
        Or.inl (combine_zero_equivalent _)⟩
  | extract first second query =>
      intro typed
      refine ⟨⟨⟨typed.1.1, typed.2⟩, ⟨typed.1.2, typed.2⟩⟩,
        Relation.EqvGen.rel _ _ ?_⟩
      exact ⟨.hole, _, _, rfl, rfl,
        Or.inr (encoded_extraction_computes first second query)⟩

/-- Every equality valid in all lawful WM readings has a path through actual
authored equations and computations whose intermediate representatives all
belong to the native open-pattern fiber. This is one-way completeness only. -/
theorem allReadingsAgree_nativeOpenAuthoredPath
    (free : FreeTypeContext) (bound : List TypeExpr)
    (first second : WMTerm .evidence)
    (firstTyped : AtomsTyped free first)
    (agree : ∀ (State Query V : Type) (reading : WMReading State Query V),
      reading.CoreLaws → reading.denote first = reading.denote second) :
    ∃ secondTyped : AtomsTyped free second,
      (nativeOpenAuthoredSetoid free bound).r
        (asNativeOpen free bound ⟨first, firstTyped⟩)
        (asNativeOpen free bound ⟨second, secondTyped⟩) := by
  obtain ⟨secondTyped, path⟩ := evidenceConversion_typedAuthoredPath
    free ((conversion_iff_allReadings first second).2 agree) firstTyped
  exact ⟨secondTyped, typedAuthoredPath_to_nativeOpen free bound path⟩

#print axioms typedAuthoredPath_to_nativeOpen
#print axioms typedAuthoredPath_combine
#print axioms evidenceConversion_typedAuthoredPath
#print axioms allReadingsAgree_nativeOpenAuthoredPath

end Mettapedia.OSLF.Framework.WMCalculusNativeAuthoredConversion
