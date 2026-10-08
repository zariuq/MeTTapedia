import Mettapedia.OSLF.Framework.SortedTypedInstrumentRigidProbeValues
import Mettapedia.GSLT.Logic.HigherOrderBisimulation

/-!
# Complete payload labels for genuine heterogeneous context classes

Every original or argument-bundle sibling occupies a separately typed
payload position. Only the independently unique nullary fresh probes stay
rigid in a label skeleton. A nonempty designated parallel residue contributes
its whole AC1 value; empty residues contribute no position.

The independently defined decoder reconstructs every normalized actual
context class, including heterogeneous constructor coordinates and complete
observer-bearing values. No source inhabitation or total erasure is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.PayloadLabels

open Mettapedia.OSLF.SortedCommutative

universe u v
variable {profile : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : profile.Srt → Prop}

inductive Skeleton : Srt profile Parallel → Srt profile Parallel → Type (max u v) where
  | hole {sort} : Skeleton sort sort
  | parallel {source target} (parallel : NativeParallel (source := profile) (Parallel := Parallel) target)
      (inner : Skeleton source target) : Skeleton source target
  | frame {source} (constructor : Constructor profile Parallel)
      (position : Fin ((signature profile Parallel).arity constructor))
      (inner : Skeleton source ((signature profile Parallel).input constructor position)) :
      Skeleton source ((signature profile Parallel).output constructor)

namespace Skeleton

def Slot {source target : Srt profile Parallel} (skeleton : Skeleton source target) : Type (max u v) := by
  induction skeleton with
  | hole => exact PEmpty.{max (u + 1) (v + 1)}
  | parallel _ _ slots => exact PUnit.{max (u + 1) (v + 1)} ⊕ slots
  | frame constructor position _ slots =>
    exact {other : Fin ((signature profile Parallel).arity constructor) //
      other ≠ position ∧ processSort ((signature profile Parallel).input constructor other) = true} ⊕ slots

def slotSort {source target : Srt profile Parallel} (skeleton : Skeleton source target) :
    Slot skeleton → Srt profile Parallel := by
  induction skeleton with
  | hole => exact PEmpty.elim
  | @parallel target parallel inner read =>
    exact fun slot => match slot with
      | .inl _ => target
      | .inr nested => read nested
  | frame constructor position inner read =>
    exact fun slot => match slot with
      | .inl other => (signature profile Parallel).input constructor other.val
      | .inr nested => read nested

abbrev Payload {source target : Srt profile Parallel} (skeleton : Skeleton source target) :=
  (slot : Slot skeleton) → ValueClass (source := profile) (Parallel := Parallel) (slotSort skeleton slot)

end Skeleton

def vocabulary (profile : Mettapedia.OSLF.SortedConstructors.Signature.{u,v})
    (Parallel : profile.Srt → Prop) :
    Mettapedia.GSLT.HigherOrderBisimulation.Vocabulary (Srt profile Parallel) where
  Skeleton := Skeleton
  Slot := Skeleton.Slot
  interface := Skeleton.slotSort

abbrev Label (profile : Mettapedia.OSLF.SortedConstructors.Signature.{u,v})
    (Parallel : profile.Srt → Prop) (source target : Srt profile Parallel) :=
  Mettapedia.GSLT.HigherOrderBisimulation.Label (vocabulary profile Parallel) (ValueClass (source := profile) (Parallel := Parallel)) source target

def holeLabel (sort : Srt profile Parallel) : Label profile Parallel sort sort :=
  ⟨.hole, fun absent => PEmpty.elim absent⟩

def parallelLabel {source target : Srt profile Parallel} (parallel : NativeParallel (source := profile) (Parallel := Parallel) target)
    (supplied : ValueClass (source := profile) (Parallel := Parallel) target) (inner : Label profile Parallel source target) :
    Label profile Parallel source target :=
  ⟨.parallel parallel inner.skeleton, fun slot => match slot with
    | .inl _ => supplied
    | .inr nested => inner.payload nested⟩

def frameLabel {source : Srt profile Parallel} (constructor : Constructor profile Parallel)
    (position : Fin ((signature profile Parallel).arity constructor))
    (siblings : (other : Fin ((signature profile Parallel).arity constructor)) → other ≠ position →
      ValueClass (source := profile) (Parallel := Parallel) ((signature profile Parallel).input constructor other))
    (inner : Label profile Parallel source ((signature profile Parallel).input constructor position)) :
    Label profile Parallel source ((signature profile Parallel).output constructor) :=
  ⟨.frame constructor position inner.skeleton,
    fun slot => match slot with
      | .inl other => siblings other.val other.property.1
      | .inr nested => inner.payload nested⟩

theorem rigid_of_not_process (sort : Srt profile Parallel) (absent : processSort sort ≠ true) :
    processSort sort = false := by
  cases read : processSort sort
  · rfl
  · exact (absent read).elim

def frameSiblings {source : Srt profile Parallel} (constructor : Constructor profile Parallel)
    (position : Fin ((signature profile Parallel).arity constructor))
    (inner : Skeleton source ((signature profile Parallel).input constructor position))
    (payload : Skeleton.Payload (.frame constructor position inner))
    (other : Fin ((signature profile Parallel).arity constructor)) (absent : other ≠ position) :
    ValueClass (source := profile) (Parallel := Parallel) ((signature profile Parallel).input constructor other) := by
  classical
  exact if process : processSort ((signature profile Parallel).input constructor other) = true then
    payload (.inl ⟨other, absent, process⟩)
  else rigidValue _ (rigid_of_not_process _ process)

def readSkeleton {source : Srt profile Parallel} : {target : Srt profile Parallel} →
    (skeleton : Skeleton source target) → Skeleton.Payload skeleton →
    MixedContext (signature profile Parallel) (NativeParallel (source := profile) (Parallel := Parallel)) source target
  | _, .hole, _ => .parallel 0
  | _, .parallel parallel inner, payload =>
      (readSkeleton inner (fun slot => payload (.inr slot))).addResidue
        (valueResidue parallel (payload (.inl PUnit.unit)))
  | _, .frame constructor position inner, payload =>
      .frame 0 (Frame.slot (signature := signature profile Parallel) (Parallel := NativeParallel (source := profile) (Parallel := Parallel))
        constructor position (frameSiblings constructor position inner payload))
        (readSkeleton inner (fun slot => payload (.inr slot)))

def readLabel {source target : Srt profile Parallel} (label : Label profile Parallel source target) :
    MixedContext (signature profile Parallel) (NativeParallel (source := profile) (Parallel := Parallel)) source target :=
  readSkeleton label.skeleton label.payload

def addBag {source target : Srt profile Parallel}
    (supplied : Multiset (ResiduePayload (signature := signature profile Parallel)
      (Parallel := NativeParallel (source := profile) (Parallel := Parallel)) target))
    (label : Label profile Parallel source target) : Label profile Parallel source target := by
  classical
  exact if parallel : NativeParallel (source := profile) (Parallel := Parallel) target then
    if supplied = 0 then label else parallelLabel parallel (residueValue parallel supplied) label
  else label

theorem addBag_zero {source target : Srt profile Parallel} (label : Label profile Parallel source target) :
    addBag 0 label = label := by
  classical
  by_cases parallel : NativeParallel (source := profile) (Parallel := Parallel) target
  · simp [addBag, parallel]
  · simp only [addBag, dif_neg parallel]

def frameFromEdge {source middle target : Srt profile Parallel}
    (edge : Frame (signature profile Parallel) (NativeParallel (source := profile) (Parallel := Parallel)) middle target)
    (inner : Label profile Parallel source middle) : Label profile Parallel source target :=
  @Frame.rec (signature profile Parallel) (NativeParallel (source := profile) (Parallel := Parallel))
    (fun middle target _ => Label profile Parallel source middle → Label profile Parallel source target)
    (fun constructor position siblings inner => frameLabel constructor position siblings inner)
    middle target edge inner

def encodeMixed {source : Interface (signature profile Parallel) (NativeParallel (source := profile) (Parallel := Parallel))} :
    {target : Interface (signature profile Parallel) (NativeParallel (source := profile) (Parallel := Parallel))} →
    Mettapedia.CategoryTheory.MixedResidue.Context
      (fun vertex : Interface (signature profile Parallel) (NativeParallel (source := profile) (Parallel := Parallel)) =>
        ResiduePayload (signature := signature profile Parallel) (Parallel := NativeParallel (source := profile) (Parallel := Parallel)) vertex.sort)
      source target → Label profile Parallel source.sort target.sort
  | _, .parallel supplied => addBag supplied (holeLabel _)
  | _, .frame supplied edge inner =>
      addBag supplied (frameFromEdge edge (encodeMixed inner))

theorem read_parallelLabel {source target : Srt profile Parallel} (parallel : NativeParallel (source := profile) (Parallel := Parallel) target)
    (supplied : ValueClass (source := profile) (Parallel := Parallel) target) (inner : Label profile Parallel source target) :
    readLabel (parallelLabel parallel supplied inner) =
      (readLabel inner).addResidue (valueResidue parallel supplied) := rfl

theorem read_frameLabel {source : Srt profile Parallel} (constructor : Constructor profile Parallel)
    (position : Fin ((signature profile Parallel).arity constructor))
    (siblings : (other : Fin ((signature profile Parallel).arity constructor)) → other ≠ position →
      ValueClass (source := profile) (Parallel := Parallel) ((signature profile Parallel).input constructor other))
    (inner : Label profile Parallel source ((signature profile Parallel).input constructor position)) :
    readLabel (frameLabel constructor position siblings inner) =
      Mettapedia.CategoryTheory.MixedResidue.Context.frame 0
        (Frame.slot (signature := signature profile Parallel) (Parallel := NativeParallel (source := profile) (Parallel := Parallel))
          constructor position siblings) (readLabel inner) := by
  classical
  change Mettapedia.CategoryTheory.MixedResidue.Context.frame 0
    (Frame.slot (signature := signature profile Parallel) (Parallel := NativeParallel (source := profile) (Parallel := Parallel)) constructor position
      (frameSiblings constructor position inner.skeleton (frameLabel constructor position siblings inner).payload))
    (readLabel inner) = _
  apply congrArg (fun edge => Mettapedia.CategoryTheory.MixedResidue.Context.frame 0 edge (readLabel inner))
  apply congrArg (Frame.slot (signature := signature profile Parallel) (Parallel := NativeParallel (source := profile) (Parallel := Parallel)) constructor position)
  funext other absent
  by_cases process : processSort ((signature profile Parallel).input constructor other) = true
  · simp only [frameSiblings, dif_pos process, frameLabel]
  · simp only [frameSiblings, dif_neg process]
    exact (rigidValue_read _ (rigid_of_not_process _ process) (siblings other absent)).symm

theorem read_frameFromEdge {source middle target : Srt profile Parallel}
    (edge : Frame (signature profile Parallel) (NativeParallel (source := profile) (Parallel := Parallel)) middle target)
    (inner : Label profile Parallel source middle) :
    readLabel (frameFromEdge edge inner) =
      Mettapedia.CategoryTheory.MixedResidue.Context.frame 0 edge (readLabel inner) := by
  exact @Frame.rec (signature profile Parallel) (NativeParallel (source := profile) (Parallel := Parallel))
    (fun middle target edge => ∀ inner : Label profile Parallel source middle,
      readLabel (frameFromEdge edge inner) =
        Mettapedia.CategoryTheory.MixedResidue.Context.frame 0 edge (readLabel inner))
    (fun constructor position siblings inner => read_frameLabel constructor position siblings inner)
    middle target edge inner

theorem read_addBag {source target : Srt profile Parallel}
    (supplied : Multiset (ResiduePayload (signature := signature profile Parallel)
      (Parallel := NativeParallel (source := profile) (Parallel := Parallel)) target))
    (label : Label profile Parallel source target) :
    readLabel (addBag supplied label) = (readLabel label).addResidue supplied := by
  classical
  by_cases parallel : NativeParallel (source := profile) (Parallel := Parallel) target
  · by_cases empty : supplied = 0
    · rw [addBag, dif_pos parallel, if_pos empty, empty, MixedContext.addResidue_zero]
    · simp only [addBag, dif_pos parallel, if_neg empty, read_parallelLabel,
        valueResidue_residueValue]
  · have empty := residue_empty_of_not_parallel parallel supplied
    simp only [addBag, dif_neg parallel, empty, MixedContext.addResidue_zero]

theorem read_encodeMixed {source target : Interface (signature profile Parallel) (NativeParallel (source := profile) (Parallel := Parallel))}
    (context : Mettapedia.CategoryTheory.MixedResidue.Context
      (fun vertex : Interface (signature profile Parallel) (NativeParallel (source := profile) (Parallel := Parallel)) =>
        ResiduePayload (signature := signature profile Parallel) (Parallel := NativeParallel (source := profile) (Parallel := Parallel)) vertex.sort)
      source target) :
    readLabel (encodeMixed context) = context := by
  induction context with
  | parallel supplied =>
    rw [encodeMixed, read_addBag]
    change Mettapedia.CategoryTheory.MixedResidue.Context.parallel (supplied + 0) = _
    rw [add_zero]
  | frame supplied edge inner inductionHypothesis =>
    rw [encodeMixed, read_addBag, read_frameFromEdge, inductionHypothesis]
    change Mettapedia.CategoryTheory.MixedResidue.Context.frame (supplied + 0) edge inner = _
    rw [add_zero]

def encodeContext {source target : Srt profile Parallel}
    (context : ContextClass (signature profile Parallel) (NativeParallel (source := profile) (Parallel := Parallel)) source target) :
    Label profile Parallel source target := encodeMixed (normalizeContext context)

def readContext {source target : Srt profile Parallel} (label : Label profile Parallel source target) :
    ContextClass (signature profile Parallel) (NativeParallel (source := profile) (Parallel := Parallel)) source target :=
  (contextEquiv source target).symm (readLabel label)

theorem read_encodeContext {source target : Srt profile Parallel}
    (context : ContextClass (signature profile Parallel) (NativeParallel (source := profile) (Parallel := Parallel)) source target) :
    readContext (encodeContext context) = context := by
  rw [readContext, encodeContext, read_encodeMixed]
  exact (contextEquiv (signature := signature profile Parallel) (Parallel := NativeParallel (source := profile) (Parallel := Parallel))
    source target).symm_apply_apply context

theorem encodeContext_injective {source target : Srt profile Parallel} :
    Function.Injective (encodeContext (profile := profile) (Parallel := Parallel) (source := source) (target := target)) := by
  intro first second same
  exact (read_encodeContext first).symm.trans
    ((congrArg readContext same).trans (read_encodeContext second))

end Mettapedia.OSLF.Framework.SortedTypedInstruments.PayloadLabels
