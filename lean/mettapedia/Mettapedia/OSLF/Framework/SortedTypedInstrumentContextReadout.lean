import Mettapedia.OSLF.Framework.SortedTypedInstrumentContexts

/-!+# Conservative source context inclusion from complete partial readouts

The independently defined reading reconstructs a normalized source context
only after all siblings and the whole inner path have original readings.
Its parallel operation retains the complete residue inventory. Generated
context equations preserve the reading, which recovers source normalization
on every embedded context. This proves context-class injectivity without a
ground-action faithfulness assumption or a source-sort inhabitant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments

open Mettapedia.OSLF.SortedCommutative

universe u v

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop}

def ContextReading (first : source.Srt) : Srt source Parallel → Type (max u v)
  | .original second => Option (MixedContext source Parallel first second)
  | .arguments _ => PUnit
  | .probe _ => PUnit

def sourceResidue {sort : source.Srt} (parallel : Parallel sort) (supplied : Class source Parallel sort) :
    Multiset (ResiduePayload (signature := source) (Parallel := Parallel) sort) :=
  (inventoryQ supplied).map (fun head => ⟨head, parallel⟩)

theorem sourceResidue_cut {sort : source.Srt} (parallel : Parallel sort)
    (first second : Class source Parallel sort) :
    sourceResidue parallel (classCut parallel first second) =
      sourceResidue parallel first + sourceResidue parallel second := by
  rw [sourceResidue, inventoryQ_classCut, Multiset.map_add]
  rfl

def readContextParallel {first : source.Srt} {second : Srt source Parallel}
    (parallel : NativeParallel second) (inner : ContextReading first second)
    (sibling : SourceReading second) : ContextReading first second := by
  cases second with
  | original second => exact Option.map₂ (fun inner sibling => inner.addResidue (sourceResidue parallel sibling)) inner sibling
  | arguments => exact parallel.elim
  | probe => exact parallel.elim

def readContextFrame {first : source.Srt} (constructor : Constructor source Parallel)
    (position : Fin ((signature source Parallel).arity constructor))
    (siblings : (other : Fin ((signature source Parallel).arity constructor)) → other ≠ position →
      SourceReading ((signature source Parallel).input constructor other))
    (inner : ContextReading first ((signature source Parallel).input constructor position)) :
    ContextReading first ((signature source Parallel).output constructor) := by
  cases constructor with
  | original constructor =>
    exact Option.map₂
      (fun tuple inner => Mettapedia.CategoryTheory.MixedResidue.Context.frame 0
        (Frame.slot constructor position (fun other absent => tuple ⟨other, absent⟩)) inner)
      (optionTuple (fun other : {other : Fin (source.arity constructor) // other ≠ position} =>
        siblings other.val other.property)) inner
  | arguments => exact PUnit.unit
  | probe => exact PUnit.unit
  | cut instrument =>
    cases instrument with
    | ask => exact PUnit.unit
    | get => exact none
    | build => exact none

def readContext {first : source.Srt} {second : Srt source Parallel}
    (supplied : RawContext (signature source Parallel) NativeParallel (.original first) second) :
    ContextReading first second :=
  @RawContext.rec (signature source Parallel) NativeParallel (.original first)
    (fun second _ => ContextReading first second) (some (.parallel 0))
    (fun constructor position siblings _ inner =>
      readContextFrame constructor position (fun other absent => readSource (siblings other absent)) inner)
    (fun parallel _ sibling inner => readContextParallel parallel inner (readSource sibling))
    (fun parallel sibling _ inner => readContextParallel parallel inner (readSource sibling)) second supplied

theorem readContextParallel_assoc {first : source.Srt} {second : Srt source Parallel}
    (parallel : NativeParallel second) (inner : ContextReading first second)
    (before after : SourceReading second) :
    readContextParallel parallel (readContextParallel parallel inner before) after =
      readContextParallel parallel inner (readCut parallel before after) := by
  cases second with
  | original second =>
    cases inner <;> cases before <;> cases after <;> try rfl
    rename_i inner before after
    apply congrArg some
    change (inner.addResidue (sourceResidue parallel before)).addResidue (sourceResidue parallel after) =
      inner.addResidue (sourceResidue parallel (classCut parallel before after))
    rw [sourceResidue_cut, MixedContext.addResidue_add, add_comm]
  | arguments => exact parallel.elim
  | probe => exact parallel.elim

theorem readContextParallel_unit {first : source.Srt} {second : Srt source Parallel}
    (parallel : NativeParallel second) (inner : ContextReading first second) :
    readContextParallel parallel inner (readZero parallel) = inner := by
  cases second with
  | original second =>
    cases inner with
    | none => rfl
    | some inner =>
      change some (inner.addResidue 0) = some inner
      exact congrArg some (MixedContext.addResidue_zero inner)
  | arguments => exact parallel.elim
  | probe => exact parallel.elim

theorem readContext_equation {first : source.Srt} {second : Srt source Parallel}
    {before after : RawContext (signature source Parallel) NativeParallel (.original first) second}
    (equation : ContextEquation before after) : readContext before = readContext after := by
  apply @ContextEquation.rec (signature source Parallel) NativeParallel (.original first)
    (fun {_target} {before after} _ => readContext before = readContext after) (t := equation)
  · intro target context
    rfl
  · intro target before after equation inductionHypothesis
    exact inductionHypothesis.symm
  · intro target before middle after firstEq secondEq firstRead secondRead
    exact firstRead.trans secondRead
  · intro constructor position firstSiblings secondSiblings before after siblings equation inductionHypothesis
    exact congrArg₂ (readContextFrame constructor position)
      (funext (fun other => funext (fun absent => readSource_equation (siblings other absent)))) inductionHypothesis
  · intro target parallel before after first second inner sibling inductionHypothesis
    exact congrArg₂ (readContextParallel parallel) inductionHypothesis (readSource_equation sibling)
  · intro target parallel first second before after sibling inner inductionHypothesis
    exact congrArg₂ (readContextParallel parallel) inductionHypothesis (readSource_equation sibling)
  · intro target parallel inner sibling
    rfl
  · intro target parallel inner first second
    exact readContextParallel_assoc parallel _ _ _
  · intro target parallel inner
    exact readContextParallel_unit parallel _

def classContextReading {first : source.Srt} {second : Srt source Parallel} :
    ContextClass (signature source Parallel) NativeParallel (.original first) second → ContextReading first second :=
  Quotient.lift readContext (fun _ _ equation => readContext_equation equation)

theorem readContext_embed {first second : source.Srt} (supplied : RawContext source Parallel first second) :
    readContext (embedContext supplied) = some supplied.normalize := by
  induction supplied with
  | hole => rfl
  | frame constructor position siblings inner inductionHypothesis =>
    change Option.map₂
      (fun tuple inner => Mettapedia.CategoryTheory.MixedResidue.Context.frame 0
        (Frame.slot constructor position (fun other absent => tuple ⟨other, absent⟩)) inner)
      (optionTuple (fun other : {other : Fin (source.arity constructor) // other ≠ position} =>
        readSource (embed (siblings other.val other.property)))) (readContext (embedContext inner)) = _
    have siblingsRead :
        (fun other : {other : Fin (source.arity constructor) // other ≠ position} =>
          readSource (embed (siblings other.val other.property))) =
        fun other : {other : Fin (source.arity constructor) // other ≠ position} =>
          some (classOf (siblings other.val other.property)) :=
      funext (fun other => readSource_embed (siblings other.val other.property))
    rw [siblingsRead, optionTuple_some, inductionHypothesis]
    rfl
  | left parallel inner sibling inductionHypothesis =>
    change readContextParallel (source := source) (Parallel := Parallel) (second := .original _)
      parallel (readContext (embedContext inner)) (readSource (embed sibling)) = _
    rw [inductionHypothesis, readSource_embed]
    rfl
  | right parallel sibling inner inductionHypothesis =>
    change readContextParallel (source := source) (Parallel := Parallel) (second := .original _)
      parallel (readContext (embedContext inner)) (readSource (embed sibling)) = _
    rw [inductionHypothesis, readSource_embed]
    rfl

theorem classContextReading_embedding {first second : source.Srt}
    (supplied : ContextClass source Parallel first second) :
    classContextReading (contextEmbedding supplied) = some (normalizeContext supplied) :=
  Quotient.inductionOn supplied readContext_embed

theorem contextEmbedding_injective {first second : source.Srt} :
    Function.Injective (contextEmbedding (source := source) (Parallel := Parallel) (first := first) (second := second)) := by
  intro before after same
  have readings := congrArg classContextReading same
  rw [classContextReading_embedding, classContextReading_embedding] at readings
  exact (contextEquiv first second).injective (Option.some.inj readings)

theorem embedContext_equation_iff {first second : source.Srt}
    (before after : RawContext source Parallel first second) :
    ContextEquation (embedContext before) (embedContext after) ↔ ContextEquation before after := by
  refine ⟨fun equation => ?_, embedContext_equation⟩
  exact Quotient.exact (contextEmbedding_injective (Quotient.sound equation))

end Mettapedia.OSLF.Framework.SortedTypedInstruments
