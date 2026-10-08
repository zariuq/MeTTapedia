import Mettapedia.OSLF.Framework.SortedCommutativeRigidProbeValues
import Mettapedia.GSLT.Logic.HigherOrderBisimulation

/-!
# Process-bearing labels for actual sorted context classes

A normalized free frame retains its constructor and selected hole position.
Its process siblings become separately typed payloads. A nonempty parallel
residue becomes one complete AC1 process payload. Empty residues contribute
no position, and the independently proved rigid probe values remain in the
skeleton. Reading these labels reconstructs the actual context class.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments.PayloadLabels

open Mettapedia.OSLF.SortedCommutative

universe u
variable {Symbols : Type u} {arity : Symbols → Nat}

inductive Skeleton : Srt arity → Srt arity → Type u where
  | hole {sort} : Skeleton sort sort
  | parallel {source target} (parallel : Parallel arity target)
      (inner : Skeleton source target) : Skeleton source target
  | frame {source} (constructor : Constructor arity)
      (position : Fin ((signature arity).arity constructor))
      (inner : Skeleton source ((signature arity).input constructor position)) :
      Skeleton source ((signature arity).output constructor)

namespace Skeleton

def Slot {source target : Srt arity} (skeleton : Skeleton source target) : Type u := by
  induction skeleton with
  | hole => exact PEmpty
  | parallel _ _ slots => exact PUnit ⊕ slots
  | frame constructor position _ slots =>
    exact {other : Fin ((signature arity).arity constructor) //
      other ≠ position ∧ processSort ((signature arity).input constructor other) = true} ⊕ slots

def slotSort {source target : Srt arity} (skeleton : Skeleton source target) :
    Slot skeleton → Srt arity := by
  induction skeleton with
  | hole => exact PEmpty.elim
  | @parallel target parallel inner read =>
    exact fun slot => match slot with
      | .inl _ => target
      | .inr nested => read nested
  | frame constructor position inner read =>
    exact fun slot => match slot with
      | .inl other => (signature arity).input constructor other.val
      | .inr nested => read nested

abbrev Payload {source target : Srt arity} (skeleton : Skeleton source target) :=
  (slot : Slot skeleton) → ValueClass arity (slotSort skeleton slot)

end Skeleton

def vocabulary (arity : Symbols → Nat) :
    Mettapedia.GSLT.HigherOrderBisimulation.Vocabulary (Srt arity) where
  Skeleton := Skeleton
  Slot := Skeleton.Slot
  interface := Skeleton.slotSort

abbrev Label (arity : Symbols → Nat) (source target : Srt arity) :=
  Mettapedia.GSLT.HigherOrderBisimulation.Label (vocabulary arity) (ValueClass arity) source target

def holeLabel (sort : Srt arity) : Label arity sort sort :=
  ⟨.hole, fun absent => PEmpty.elim absent⟩

def parallelLabel {source target : Srt arity} (parallel : Parallel arity target)
    (supplied : ValueClass arity target) (inner : Label arity source target) :
    Label arity source target :=
  ⟨.parallel parallel inner.skeleton, fun slot => match slot with
    | .inl _ => supplied
    | .inr nested => inner.payload nested⟩

def frameLabel {source : Srt arity} (constructor : Constructor arity)
    (position : Fin ((signature arity).arity constructor))
    (siblings : (other : Fin ((signature arity).arity constructor)) → other ≠ position →
      ValueClass arity ((signature arity).input constructor other))
    (inner : Label arity source ((signature arity).input constructor position)) :
    Label arity source ((signature arity).output constructor) :=
  ⟨.frame constructor position inner.skeleton,
    fun slot => match slot with
      | .inl other => siblings other.val other.property.1
      | .inr nested => inner.payload nested⟩

theorem rigid_of_not_process (sort : Srt arity) (absent : processSort sort ≠ true) :
    processSort sort = false := by
  cases read : processSort sort
  · rfl
  · exact (absent read).elim

def frameSiblings {source : Srt arity} (constructor : Constructor arity)
    (position : Fin ((signature arity).arity constructor))
    (inner : Skeleton source ((signature arity).input constructor position))
    (payload : Skeleton.Payload (.frame constructor position inner))
    (other : Fin ((signature arity).arity constructor)) (absent : other ≠ position) :
    ValueClass arity ((signature arity).input constructor other) := by
  classical
  exact if process : processSort ((signature arity).input constructor other) = true then
    payload (.inl ⟨other, absent, process⟩)
  else rigidValue _ (rigid_of_not_process _ process)

def readSkeleton {source : Srt arity} : {target : Srt arity} →
    (skeleton : Skeleton source target) → Skeleton.Payload skeleton →
    MixedContext (signature arity) (Parallel arity) source target
  | _, .hole, _ => .parallel 0
  | _, .parallel parallel inner, payload =>
      (readSkeleton inner (fun slot => payload (.inr slot))).addResidue
        (valueResidue parallel (payload (.inl PUnit.unit)))
  | _, .frame constructor position inner, payload =>
      .frame 0 (Frame.slot (signature := signature arity) (Parallel := Parallel arity)
        constructor position (frameSiblings constructor position inner payload))
        (readSkeleton inner (fun slot => payload (.inr slot)))

def readLabel {source target : Srt arity} (label : Label arity source target) :
    MixedContext (signature arity) (Parallel arity) source target :=
  readSkeleton label.skeleton label.payload

def addBag {source target : Srt arity}
    (supplied : Multiset (ResiduePayload (signature := signature arity)
      (Parallel := Parallel arity) target))
    (label : Label arity source target) : Label arity source target := by
  classical
  exact if parallel : Parallel arity target then
    if supplied = 0 then label else parallelLabel parallel (residueValue parallel supplied) label
  else label

theorem addBag_zero {source target : Srt arity} (label : Label arity source target) :
    addBag 0 label = label := by
  classical
  by_cases parallel : Parallel arity target
  · simp [addBag, parallel]
  · simp only [addBag, dif_neg parallel]

def frameFromEdge {source middle target : Srt arity}
    (edge : Frame (signature arity) (Parallel arity) middle target)
    (inner : Label arity source middle) : Label arity source target :=
  @Frame.rec (signature arity) (Parallel arity)
    (fun middle target _ => Label arity source middle → Label arity source target)
    (fun constructor position siblings inner => frameLabel constructor position siblings inner)
    middle target edge inner

def encodeMixed {source : Interface (signature arity) (Parallel arity)} :
    {target : Interface (signature arity) (Parallel arity)} →
    Mettapedia.CategoryTheory.MixedResidue.Context
      (fun vertex : Interface (signature arity) (Parallel arity) =>
        ResiduePayload (signature := signature arity) (Parallel := Parallel arity) vertex.sort)
      source target → Label arity source.sort target.sort
  | _, .parallel supplied => addBag supplied (holeLabel _)
  | _, .frame supplied edge inner =>
      addBag supplied (frameFromEdge edge (encodeMixed inner))

theorem read_parallelLabel {source target : Srt arity} (parallel : Parallel arity target)
    (supplied : ValueClass arity target) (inner : Label arity source target) :
    readLabel (parallelLabel parallel supplied inner) =
      (readLabel inner).addResidue (valueResidue parallel supplied) := rfl

theorem read_frameLabel {source : Srt arity} (constructor : Constructor arity)
    (position : Fin ((signature arity).arity constructor))
    (siblings : (other : Fin ((signature arity).arity constructor)) → other ≠ position →
      ValueClass arity ((signature arity).input constructor other))
    (inner : Label arity source ((signature arity).input constructor position)) :
    readLabel (frameLabel constructor position siblings inner) =
      Mettapedia.CategoryTheory.MixedResidue.Context.frame 0
        (Frame.slot (signature := signature arity) (Parallel := Parallel arity)
          constructor position siblings) (readLabel inner) := by
  classical
  change Mettapedia.CategoryTheory.MixedResidue.Context.frame 0
    (Frame.slot (signature := signature arity) (Parallel := Parallel arity) constructor position
      (frameSiblings constructor position inner.skeleton (frameLabel constructor position siblings inner).payload))
    (readLabel inner) = _
  apply congrArg (fun edge => Mettapedia.CategoryTheory.MixedResidue.Context.frame 0 edge (readLabel inner))
  apply congrArg (Frame.slot (signature := signature arity) (Parallel := Parallel arity) constructor position)
  funext other absent
  by_cases process : processSort ((signature arity).input constructor other) = true
  · simp only [frameSiblings, dif_pos process, frameLabel]
  · simp only [frameSiblings, dif_neg process]
    exact (rigidValue_read _ (rigid_of_not_process _ process) (siblings other absent)).symm

theorem read_frameFromEdge {source middle target : Srt arity}
    (edge : Frame (signature arity) (Parallel arity) middle target)
    (inner : Label arity source middle) :
    readLabel (frameFromEdge edge inner) =
      Mettapedia.CategoryTheory.MixedResidue.Context.frame 0 edge (readLabel inner) := by
  exact @Frame.rec (signature arity) (Parallel arity)
    (fun middle target edge => ∀ inner : Label arity source middle,
      readLabel (frameFromEdge edge inner) =
        Mettapedia.CategoryTheory.MixedResidue.Context.frame 0 edge (readLabel inner))
    (fun constructor position siblings inner => read_frameLabel constructor position siblings inner)
    middle target edge inner

theorem read_addBag {source target : Srt arity}
    (supplied : Multiset (ResiduePayload (signature := signature arity)
      (Parallel := Parallel arity) target))
    (label : Label arity source target) :
    readLabel (addBag supplied label) = (readLabel label).addResidue supplied := by
  classical
  by_cases parallel : Parallel arity target
  · by_cases empty : supplied = 0
    · rw [addBag, dif_pos parallel, if_pos empty, empty, MixedContext.addResidue_zero]
    · simp only [addBag, dif_pos parallel, if_neg empty, read_parallelLabel,
        valueResidue_residueValue]
  · have empty := residue_empty_of_not_parallel parallel supplied
    simp only [addBag, dif_neg parallel, empty, MixedContext.addResidue_zero]

theorem read_encodeMixed {source target : Interface (signature arity) (Parallel arity)}
    (context : Mettapedia.CategoryTheory.MixedResidue.Context
      (fun vertex : Interface (signature arity) (Parallel arity) =>
        ResiduePayload (signature := signature arity) (Parallel := Parallel arity) vertex.sort)
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

def encodeContext {source target : Srt arity}
    (context : ContextClass (signature arity) (Parallel arity) source target) :
    Label arity source target := encodeMixed (normalizeContext context)

def readContext {source target : Srt arity} (label : Label arity source target) :
    ContextClass (signature arity) (Parallel arity) source target :=
  (contextEquiv source target).symm (readLabel label)

theorem read_encodeContext {source target : Srt arity}
    (context : ContextClass (signature arity) (Parallel arity) source target) :
    readContext (encodeContext context) = context := by
  rw [readContext, encodeContext, read_encodeMixed]
  exact (contextEquiv (signature := signature arity) (Parallel := Parallel arity)
    source target).symm_apply_apply context

theorem encodeContext_injective {source target : Srt arity} :
    Function.Injective (encodeContext (arity := arity) (source := source) (target := target)) := by
  intro first second same
  exact (read_encodeContext first).symm.trans
    ((congrArg readContext same).trans (read_encodeContext second))

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments.PayloadLabels
