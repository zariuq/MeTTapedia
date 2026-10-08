import Mettapedia.OSLF.Framework.InstrumentSourceContextCategory
import Mettapedia.GSLT.Logic.RelativePushoutFunctor

/-!
# Exact source-relative RPO comparison for the typed observer extension

Factor lifting for actual embedded source paths reconstructs every competing
candidate and every mediator. The source inclusion preserves and reflects
complete RPO universal properties on source bounds, despite not being full on
all extension arrows. In particular different hole positions are not equated
by a coincident ground readout.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutContexts

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.CategoryTheory.OneVertexPathEmbedding
open Mettapedia.GSLT.RelativePushout

universe u

variable {Symbols : Type u} (arity : Symbols → Nat)

local instance instrumentSourceRelativePushoutQuiver : Quiver (Srt Symbols arity) := frameQuiver (signature arity)

def sourceValueArrow (supplied : InstrumentObservations.Tree Symbols arity) :
    (.origin : SourceObject Symbols arity) ⟶ .base := .value supplied

def sourceContextArrow (supplied : SourceContext arity) :
    (.base : SourceObject Symbols arity) ⟶ .base := .context supplied

variable (first second : InstrumentObservations.Tree Symbols arity) (left right : SourceContext arity)

abbrev SourceCandidate := Candidate (sourceValueArrow arity first) (sourceValueArrow arity second)
  (sourceContextArrow arity left) (sourceContextArrow arity right)

theorem source_factors_lift (supplied : SourceContext arity) {middle : Srt Symbols arity}
    (inner : Context (signature arity) .base middle) (outer : Context (signature arity) middle .base)
    (same : inner.comp outer = sourceContextImage arity supplied) :
    middle = .base ∧ ∃ first second : SourceContext arity,
      HEq inner (sourceContextImage arity first) ∧ HEq outer (sourceContextImage arity second) :=
  @factors_lift (Srt Symbols arity) (frameQuiver (signature arity)) (SourceFrame arity) .base
    (sourceFrameImage arity) supplied middle inner outer same

set_option backward.isDefEq.respectTransparency false in
theorem sourceCandidate_lift
    (candidate : Candidate (termArrow (signature arity) (embedSource arity first))
      (termArrow (signature arity) (embedSource arity second))
      (contextArrow (signature arity) (sourceContextImage arity left))
      (contextArrow (signature arity) (sourceContextImage arity right))) :
    ∃ original : SourceCandidate arity first second left right,
      mapCandidate (sourceFunctor arity) original = candidate := by
  rcases candidate with ⟨apex, inl, inr, down, comm, facLeft, facRight⟩
  cases apex with
  | origin => cases inl
  | interface sort =>
    cases inl with
    | context inlPath =>
      cases inr with
      | context inrPath =>
        cases down with
        | context downPath =>
          have leftFactor := Arrow.context.inj facLeft
          have rightFactor := Arrow.context.inj facRight
          obtain ⟨sortEq, originalLeft, originalDown, leftEq, downEq⟩ :=
            source_factors_lift arity left inlPath downPath leftFactor
          subst sort
          obtain ⟨_, originalRight, otherDown, rightEq, otherDownEq⟩ :=
            source_factors_lift arity right inrPath downPath rightFactor
          have downSame : originalDown = otherDown := sourceContextImage_injective arity
            ((eq_of_heq downEq).symm.trans (eq_of_heq otherDownEq))
          subst otherDown
          cases eq_of_heq leftEq
          cases eq_of_heq downEq
          cases eq_of_heq rightEq
          let original : SourceCandidate arity first second left right :=
            { apex := .base
              inl := sourceContextArrow arity originalLeft
              inr := sourceContextArrow arity originalRight
              down := sourceContextArrow arity originalDown
              comm := (sourceFunctor arity).map_injective (by
                rw [Functor.map_comp, Functor.map_comp]
                exact comm)
              fac_left := (sourceFunctor arity).map_injective (by
                rw [Functor.map_comp]
                exact facLeft)
              fac_right := (sourceFunctor arity).map_injective (by
                rw [Functor.map_comp]
                exact facRight) }
          exact ⟨original, rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem sourceMediator_lift
    (from_ to_ : SourceCandidate arity first second left right)
    (mediator : (sourceFunctor arity).obj from_.apex ⟶ (sourceFunctor arity).obj to_.apex)
    (equations : Candidate.Mediates (mapCandidate (sourceFunctor arity) from_)
      (mapCandidate (sourceFunctor arity) to_) mediator) :
    ∃ original : from_.apex ⟶ to_.apex, (sourceFunctor arity).map original = mediator := by
  rcases from_ with ⟨fromApex, fromInl, fromInr, fromDown, fromComm, fromLeft, fromRight⟩
  rcases to_ with ⟨toApex, toInl, toInr, toDown, toComm, toLeft, toRight⟩
  cases fromApex with
  | origin => cases fromInl
  | base =>
    cases toApex with
    | origin => cases toInl
    | base =>
      cases fromInl with
      | context fromContext =>
        cases toInl with
        | context toContext =>
          cases mediator with
          | context supplied =>
            have factor := Arrow.context.inj equations.1
            obtain ⟨_, _, original, _, readout⟩ := source_factors_lift arity toContext
              (sourceContextImage arity fromContext) supplied factor
            exact ⟨sourceContextArrow arity original, congrArg Arrow.context (eq_of_heq readout).symm⟩

set_option backward.isDefEq.respectTransparency false in
theorem source_map_mediates {from_ to_ : SourceCandidate arity first second left right}
    (mediator : from_.apex ⟶ to_.apex) (equations : Candidate.Mediates from_ to_ mediator) :
    Candidate.Mediates (mapCandidate (sourceFunctor arity) from_)
      (mapCandidate (sourceFunctor arity) to_) ((sourceFunctor arity).map mediator) :=
  ⟨by simpa only [mapCandidate, Functor.map_comp] using congrArg (sourceFunctor arity).map equations.1,
    by simpa only [mapCandidate, Functor.map_comp] using congrArg (sourceFunctor arity).map equations.2.1,
    by simpa only [mapCandidate, Functor.map_comp] using congrArg (sourceFunctor arity).map equations.2.2⟩

set_option backward.isDefEq.respectTransparency false in
theorem source_reflects_mediates {from_ to_ : SourceCandidate arity first second left right}
    (mediator : from_.apex ⟶ to_.apex)
    (equations : Candidate.Mediates (mapCandidate (sourceFunctor arity) from_)
      (mapCandidate (sourceFunctor arity) to_) ((sourceFunctor arity).map mediator)) :
    Candidate.Mediates from_ to_ mediator :=
  ⟨(sourceFunctor arity).map_injective (by simpa only [mapCandidate, Functor.map_comp] using equations.1),
    (sourceFunctor arity).map_injective (by simpa only [mapCandidate, Functor.map_comp] using equations.2.1),
    (sourceFunctor arity).map_injective (by simpa only [mapCandidate, Functor.map_comp] using equations.2.2)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Both directions quantify every candidate and retain all three mediator
equations and uniqueness, rather than just comparing chosen suffix depths. -/
theorem source_relativePushout_iff (candidate : SourceCandidate arity first second left right) :
    IsRelativePushout candidate ↔ IsRelativePushout (mapCandidate (sourceFunctor arity) candidate) := by
  constructor
  · intro universal other
    obtain ⟨original, readout⟩ := sourceCandidate_lift arity first second left right other
    cases readout
    obtain ⟨mediator, equations, unique⟩ := universal original
    refine ⟨(sourceFunctor arity).map mediator, source_map_mediates arity first second left right mediator equations, ?_⟩
    intro alternative laws
    obtain ⟨lifted, mapped⟩ := sourceMediator_lift arity first second left right candidate original alternative laws
    have originalLaws := laws
    rw [← mapped] at originalLaws
    have same := unique lifted (source_reflects_mediates arity first second left right lifted originalLaws)
    exact mapped.symm.trans (congrArg (sourceFunctor arity).map same)
  · intro universal other
    obtain ⟨mediator, equations, unique⟩ := universal (mapCandidate (sourceFunctor arity) other)
    obtain ⟨lifted, mapped⟩ := sourceMediator_lift arity first second left right candidate other mediator equations
    rw [← mapped] at equations
    refine ⟨lifted, source_reflects_mediates arity first second left right lifted equations, ?_⟩
    intro alternative laws
    apply (sourceFunctor arity).map_injective
    exact (unique ((sourceFunctor arity).map alternative)
      (source_map_mediates arity first second left right alternative laws)).trans mapped.symm

set_option backward.isDefEq.respectTransparency false in
theorem source_idemPushout_iff
    (square : sourceValueArrow arity first ≫ sourceContextArrow arity left =
      sourceValueArrow arity second ≫ sourceContextArrow arity right) :
    IsIdemPushout (sourceValueArrow arity first) (sourceValueArrow arity second)
      (sourceContextArrow arity left) (sourceContextArrow arity right) square ↔
      IsIdemPushout ((sourceFunctor arity).map (sourceValueArrow arity first))
        ((sourceFunctor arity).map (sourceValueArrow arity second))
        ((sourceFunctor arity).map (sourceContextArrow arity left))
        ((sourceFunctor arity).map (sourceContextArrow arity right))
        (by rw [← Functor.map_comp, square, Functor.map_comp]) := by
  have earned := source_relativePushout_iff arity first second left right
    (Candidate.self _ _ _ _ square)
  have sameSelf : mapCandidate (sourceFunctor arity) (Candidate.self _ _ _ _ square) =
      Candidate.self ((sourceFunctor arity).map (sourceValueArrow arity first))
        ((sourceFunctor arity).map (sourceValueArrow arity second))
        ((sourceFunctor arity).map (sourceContextArrow arity left))
        ((sourceFunctor arity).map (sourceContextArrow arity right))
        (by rw [← Functor.map_comp, square, Functor.map_comp]) := by
    rfl
  rw [sameSelf] at earned
  exact earned

set_option backward.isDefEq.respectTransparency false in
theorem source_hasRelativePushouts :
    HasRelativePushouts (sourceValueArrow arity first) (sourceValueArrow arity second) := by
  intro target leftArrow rightArrow square
  cases target with
  | origin => cases leftArrow
  | base =>
    cases leftArrow with
    | context leftContext =>
      cases rightArrow with
      | context rightContext =>
        have mappedSquare := congrArg (sourceFunctor arity).map square
        rw [Functor.map_comp, Functor.map_comp] at mappedSquare
        obtain ⟨candidate, universal⟩ := hasRelativePushouts (signature arity)
          (embedSource arity first) (embedSource arity second) _
          (contextArrow (signature arity) (sourceContextImage arity leftContext))
          (contextArrow (signature arity) (sourceContextImage arity rightContext)) mappedSquare
        obtain ⟨original, readout⟩ := sourceCandidate_lift arity first second leftContext rightContext candidate
        refine ⟨original, (source_relativePushout_iff arity first second leftContext rightContext original).mpr ?_⟩
        rw [readout]
        exact universal

end Mettapedia.OSLF.Framework.InstrumentCutContexts
