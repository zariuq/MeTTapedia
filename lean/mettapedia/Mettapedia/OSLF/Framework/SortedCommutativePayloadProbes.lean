import Mettapedia.OSLF.Framework.SortedCommutativePayloadLabels

/-!
# Actual administrative probes have no process payload positions

The selected hole receives the complete current process. The sole closed
sibling is the independently proved rigid nullary probe. Consequently the
fixed skeleton determines the whole label, even when other labels in the
same vocabulary carry arbitrary process payloads.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments.PayloadLabels

open Mettapedia.OSLF.SortedCommutative

universe u
variable {Symbols : Type u} {arity : Symbols → Nat}

def probeSkeleton (instrument : Probe arity) :
    Skeleton (InstrumentCutContexts.receiver (sourceArity arity) instrument)
      (InstrumentCutContexts.result (sourceArity arity) instrument) :=
  .frame (.cut instrument) 1 .hole

theorem probeSlot_absent (instrument : Probe arity)
    (slot : Skeleton.Slot (probeSkeleton instrument)) : False := by
  change {other : Fin 2 // other ≠ 1 ∧
    processSort ((signature arity).input (.cut instrument) other) = true} ⊕ PEmpty at slot
  rcases slot with other | absent
  · obtain ⟨other, distinct, process⟩ := other
    fin_cases other
    · change false = true at process
      cases process
    · exact distinct rfl
  · exact PEmpty.elim absent

def probeLabel (instrument : Probe arity) :
    Label arity (InstrumentCutContexts.receiver (sourceArity arity) instrument)
      (InstrumentCutContexts.result (sourceArity arity) instrument) :=
  ⟨probeSkeleton instrument, fun slot => (probeSlot_absent instrument slot).elim⟩

theorem encode_probeContext (instrument : Probe arity) :
    encodeContext (contextClassOf (probeContext arity instrument)) = probeLabel instrument := by
  change encodeMixed (RawContext.normalize (probeContext arity instrument)) = probeLabel instrument
  rw [probeContext, RawContext.normalize, encodeMixed, addBag_zero]
  simp only [RawContext.normalize, encodeMixed, addBag_zero]
  change (⟨probeSkeleton instrument, _⟩ :
    Label arity (InstrumentCutContexts.receiver (sourceArity arity) instrument)
      (InstrumentCutContexts.result (sourceArity arity) instrument)) = probeLabel instrument
  apply congrArg (fun payload : Skeleton.Payload (probeSkeleton instrument) =>
    (⟨probeSkeleton instrument, payload⟩ :
      Label arity (InstrumentCutContexts.receiver (sourceArity arity) instrument)
        (InstrumentCutContexts.result (sourceArity arity) instrument)))
  funext slot
  exact (probeSlot_absent instrument slot).elim

theorem read_probeLabel (instrument : Probe arity) :
    readContext (probeLabel instrument) = contextClassOf (probeContext arity instrument) := by
  rw [← encode_probeContext, read_encodeContext]

theorem probe_skeleton_recovers_label (instrument : Probe arity)
    (label : Label arity (InstrumentCutContexts.receiver (sourceArity arity) instrument)
      (InstrumentCutContexts.result (sourceArity arity) instrument))
    (same : label.skeleton = probeSkeleton instrument) : label = probeLabel instrument := by
  cases label with
  | mk skeleton payload =>
    change skeleton = probeSkeleton instrument at same
    subst skeleton
    apply congrArg (fun payload : Skeleton.Payload (probeSkeleton instrument) =>
      (⟨probeSkeleton instrument, payload⟩ :
        Label arity (InstrumentCutContexts.receiver (sourceArity arity) instrument)
          (InstrumentCutContexts.result (sourceArity arity) instrument)))
    funext slot
    exact (probeSlot_absent instrument slot).elim

theorem related_probe_forward
    (relation : Mettapedia.GSLT.HigherOrderBisimulation.RelationFamily (ValueClass arity))
    (instrument : Probe arity)
    (label : Label arity (InstrumentCutContexts.receiver (sourceArity arity) instrument)
      (InstrumentCutContexts.result (sourceArity arity) instrument))
    (related : Mettapedia.GSLT.HigherOrderBisimulation.Label.Relates relation
      (probeLabel instrument) label) : label = probeLabel instrument :=
  probe_skeleton_recovers_label instrument label
    (Mettapedia.GSLT.HigherOrderBisimulation.Label.skeleton_eq related).symm

theorem related_probe_backward
    (relation : Mettapedia.GSLT.HigherOrderBisimulation.RelationFamily (ValueClass arity))
    (instrument : Probe arity)
    (label : Label arity (InstrumentCutContexts.receiver (sourceArity arity) instrument)
      (InstrumentCutContexts.result (sourceArity arity) instrument))
    (related : Mettapedia.GSLT.HigherOrderBisimulation.Label.Relates relation
      label (probeLabel instrument)) : label = probeLabel instrument :=
  probe_skeleton_recovers_label instrument label
    (Mettapedia.GSLT.HigherOrderBisimulation.Label.skeleton_eq related)

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments.PayloadLabels
