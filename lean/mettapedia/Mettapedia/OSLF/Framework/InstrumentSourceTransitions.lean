import Mettapedia.OSLF.Framework.InstrumentSourceFilling

/-!
# Exact proper-reaction comparison at actual source context labels

The source category has its own independently defined reaction family. Its
labelled IPO transitions are equivalent to transitions of the observer
extension at the traversed source labels. Complete constructor readouts
reconstruct reaction contexts; a hereditary source-purity invariant excludes
administrative reactions. Neither result assumes injective ground action or
infers interactive adequacy solely from fresh observer names.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutContexts

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence

universe u w

variable {Symbols : Type u} (arity : Symbols → Nat)

local instance instrumentSourceTransitionsQuiver : Quiver (Srt Symbols arity) := frameQuiver (signature arity)

def SourceRule.sourceReaction (rule : SourceRule arity) : ReactionRule (.origin : SourceObject Symbols arity) where
  codomain := .base
  redex := sourceValueArrow arity rule.redex
  reactum := sourceValueArrow arity rule.reactum

def properSourceRules (proper : SourceRule arity → Prop)
    (rule : ReactionRule (.origin : SourceObject Symbols arity)) : Prop :=
  ∃ sourceRule, proper sourceRule ∧ rule = sourceRule.sourceReaction

def properExtendedRules (proper : SourceRule arity → Prop)
    (rule : ReactionRule (.origin : ContextObject (signature arity))) : Prop :=
  ∃ sourceRule, proper sourceRule ∧ rule = sourceRule.reaction

set_option backward.isDefEq.respectTransparency false in
theorem proper_step_source_iff (proper : SourceRule arity → Prop)
    (label : SourceContext arity) (first second : InstrumentObservations.Tree Symbols arity) :
    ActIPO (properSourceRules arity proper) (sourceContextArrow arity label)
      (sourceValueArrow arity first) (sourceValueArrow arity second) ↔
      ActIPO (properExtendedRules arity proper) (contextArrow (signature arity) (sourceContextImage arity label))
        (termArrow (signature arity) (embedSource arity first))
        (termArrow (signature arity) (embedSource arity second)) := by
  constructor
  · rintro ⟨rule, ⟨sourceRule, admitted, rfl⟩, reaction, square, ipo, targetRead⟩
    cases reaction with
    | context supplied =>
      refine ⟨sourceRule.reaction, ⟨sourceRule, admitted, rfl⟩,
        contextArrow (signature arity) (sourceContextImage arity supplied), ?_, ?_, ?_⟩
      · have mapped := congrArg (sourceFunctor arity).map square
        rw [Functor.map_comp, Functor.map_comp] at mapped
        exact mapped
      · exact (source_idemPushout_iff arity first sourceRule.redex label supplied square).mp ipo
      · have mapped := congrArg (sourceFunctor arity).map targetRead
        rw [Functor.map_comp] at mapped
        exact mapped
  · rintro ⟨rule, ⟨sourceRule, admitted, rfl⟩, reaction, square, ipo, targetRead⟩
    cases reaction with
    | context supplied =>
      have complete : (action (signature arity)).path supplied (embedSource arity sourceRule.redex) =
          embedSource arity (SourceContext.fill arity label first) :=
        (Arrow.value.inj square).symm.trans (sourceContext_fill_readout arity label first).symm
      obtain ⟨original, contextRead, _⟩ := source_context_fill_lift arity supplied
        sourceRule.redex (SourceContext.fill arity label first) complete
      cases contextRead
      have sourceSquare : sourceValueArrow arity first ≫ sourceContextArrow arity label =
          sourceValueArrow arity sourceRule.redex ≫ sourceContextArrow arity original := by
        apply (sourceFunctor arity).map_injective
        rw [Functor.map_comp, Functor.map_comp]
        exact square
      refine ⟨sourceRule.sourceReaction, ⟨sourceRule, admitted, rfl⟩,
        sourceContextArrow arity original, sourceSquare,
        (source_idemPushout_iff arity first sourceRule.redex label original sourceSquare).mpr ipo, ?_⟩
      apply (sourceFunctor arity).map_injective
      rw [Functor.map_comp]
      exact targetRead

def sourcePure : {sort : Srt Symbols arity} → Term (signature arity) sort → Prop
  | _, .node (Constructor.original _) arguments => ∀ position, sourcePure (arguments position)
  | _, .node (Constructor.arguments _) _ => False
  | _, .node (Constructor.probe _) _ => False
  | _, .node (Constructor.cut _) _ => False

theorem embedSource_pure (supplied : InstrumentObservations.Tree Symbols arity) :
    sourcePure arity (embedSource arity supplied) := by
  induction supplied with
  | node constructor arguments inductionHypothesis => exact inductionHypothesis

theorem sourcePure_frame {source target : Srt Symbols arity}
    (frame : Frame (signature arity) source target) (supplied : Value arity source)
    (pure : sourcePure arity (frame.fill supplied)) : sourcePure arity supplied := by
  classical
  refine @Frame.casesOn (signature arity)
    (fun source _ frame => ∀ supplied : Term (signature arity) source,
      sourcePure arity (frame.fill supplied) → sourcePure arity supplied)
    source target frame ?_ supplied pure
  intro constructor position siblings value valuePure
  cases constructor with
  | original _ => simpa [Frame.fill, sourcePure] using valuePure position
  | arguments _ => exact valuePure.elim
  | probe _ => exact valuePure.elim
  | cut _ => exact valuePure.elim

theorem sourcePure_context {source target : Srt Symbols arity}
    (suppliedContext : Context (signature arity) source target) (supplied : Value arity source)
    (pure : sourcePure arity ((action (signature arity)).path suppliedContext supplied)) :
    sourcePure arity supplied := by
  induction suppliedContext with
  | nil => exact pure
  | cons previous frame inductionHypothesis =>
    exact inductionHypothesis (sourcePure_frame arity frame _ pure)

theorem administrative_redex_not_pure (instrument : Probe Symbols arity)
    (instance_ : AdministrativeInstance arity instrument) :
    ¬ sourcePure arity (cut arity instrument (probe arity instrument) instance_.body) := by
  intro impossible
  exact impossible

set_option backward.isDefEq.respectTransparency false in
theorem extended_source_step_iff (Origins : Type w) (proper : SourceRule arity → Prop)
    (label : SourceContext arity) (first second : InstrumentObservations.Tree Symbols arity) :
    ActIPO (extendedRules arity Origins proper) (contextArrow (signature arity) (sourceContextImage arity label))
      (termArrow (signature arity) (embedSource arity first))
      (termArrow (signature arity) (embedSource arity second)) ↔
    ActIPO (properSourceRules arity proper) (sourceContextArrow arity label)
      (sourceValueArrow arity first) (sourceValueArrow arity second) := by
  rw [proper_step_source_iff]
  constructor
  · rintro ⟨rule, membership, reaction, square, ipo, targetRead⟩
    rcases membership with administrative | properAdmission
    · obtain ⟨instrument, occurrence, rfl⟩ := administrative
      cases reaction with
      | context supplied =>
        have fullRead := Arrow.value.inj square
        have outputPure : sourcePure arity
            ((action (signature arity)).path supplied
              (cut arity instrument (probe arity instrument) occurrence.instance_.body)) := by
          rw [← fullRead, ← sourceContext_fill_readout]
          exact embedSource_pure arity _
        have inputPure := sourcePure_context arity supplied _ outputPure
        exact (administrative_redex_not_pure arity instrument occurrence.instance_ inputPure).elim
    · exact ⟨rule, properAdmission, reaction, square, ipo, targetRead⟩
  · rintro ⟨rule, properAdmission, reaction, square, ipo, targetRead⟩
    exact ⟨rule, Or.inr properAdmission, reaction, square, ipo, targetRead⟩

end Mettapedia.OSLF.Framework.InstrumentCutContexts
