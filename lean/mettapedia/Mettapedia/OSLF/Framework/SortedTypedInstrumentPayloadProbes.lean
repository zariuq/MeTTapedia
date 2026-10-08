import Mettapedia.OSLF.Framework.SortedTypedInstrumentPayloadLabels

/-!
# Fresh typed administrative labels have empty payload families

The complete current value fills the selected assay hole at its actual
receiver sort. Its sole closed sibling is the independently unique fresh
nullary probe. Consequently a matching skeleton recovers the exact
categorical label, while ordinary labels in the same vocabulary retain
all heterogeneous original and bundle payloads.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.PayloadLabels

open Mettapedia.OSLF.SortedCommutative

universe u v
variable {profile : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : profile.Srt → Prop}

def probeSkeleton (instrument : Probe profile Parallel) :
    Skeleton (receiver instrument)
      (result instrument) :=
  .frame (.cut instrument) 1 .hole

theorem probeSlot_absent (instrument : Probe profile Parallel)
    (slot : Skeleton.Slot (probeSkeleton instrument)) : False := by
  change {other : Fin 2 // other ≠ 1 ∧
    processSort ((signature profile Parallel).input (.cut instrument) other) = true} ⊕ PEmpty at slot
  rcases slot with other | absent
  · obtain ⟨other, distinct, process⟩ := other
    fin_cases other
    · change false = true at process
      cases process
    · exact distinct rfl
  · exact PEmpty.elim absent

def probeLabel (instrument : Probe profile Parallel) :
    Label profile Parallel (receiver instrument)
      (result instrument) :=
  ⟨probeSkeleton instrument, fun slot => (probeSlot_absent instrument slot).elim⟩

theorem encode_probeContext (instrument : Probe profile Parallel) :
    encodeContext (contextClassOf (SortedTypedInstruments.probeContext instrument)) = probeLabel instrument := by
  change encodeMixed (RawContext.normalize (SortedTypedInstruments.probeContext instrument)) = probeLabel instrument
  rw [probeContext, RawContext.normalize, encodeMixed, addBag_zero]
  simp only [RawContext.normalize, encodeMixed, addBag_zero]
  change (⟨probeSkeleton instrument, _⟩ :
    Label profile Parallel (receiver instrument)
      (result instrument)) = probeLabel instrument
  apply congrArg (fun payload : Skeleton.Payload (probeSkeleton instrument) =>
    (⟨probeSkeleton instrument, payload⟩ :
      Label profile Parallel (receiver instrument)
        (result instrument)))
  funext slot
  exact (probeSlot_absent instrument slot).elim

theorem read_probeLabel (instrument : Probe profile Parallel) :
    readContext (probeLabel instrument) = contextClassOf (SortedTypedInstruments.probeContext instrument) := by
  rw [← encode_probeContext, read_encodeContext]

theorem probe_skeleton_recovers_label (instrument : Probe profile Parallel)
    (label : Label profile Parallel (receiver instrument)
      (result instrument))
    (same : label.skeleton = probeSkeleton instrument) : label = probeLabel instrument := by
  cases label with
  | mk skeleton payload =>
    change skeleton = probeSkeleton instrument at same
    subst skeleton
    apply congrArg (fun payload : Skeleton.Payload (probeSkeleton instrument) =>
      (⟨probeSkeleton instrument, payload⟩ :
        Label profile Parallel (receiver instrument)
          (result instrument)))
    funext slot
    exact (probeSlot_absent instrument slot).elim

theorem related_probe_forward
    (relation : Mettapedia.GSLT.HigherOrderBisimulation.RelationFamily (ValueClass (source := profile) (Parallel := Parallel)))
    (instrument : Probe profile Parallel)
    (label : Label profile Parallel (receiver instrument)
      (result instrument))
    (related : Mettapedia.GSLT.HigherOrderBisimulation.Label.Relates relation
      (probeLabel instrument) label) : label = probeLabel instrument :=
  probe_skeleton_recovers_label instrument label
    (Mettapedia.GSLT.HigherOrderBisimulation.Label.skeleton_eq related).symm

theorem related_probe_backward
    (relation : Mettapedia.GSLT.HigherOrderBisimulation.RelationFamily (ValueClass (source := profile) (Parallel := Parallel)))
    (instrument : Probe profile Parallel)
    (label : Label profile Parallel (receiver instrument)
      (result instrument))
    (related : Mettapedia.GSLT.HigherOrderBisimulation.Label.Relates relation
      label (probeLabel instrument)) : label = probeLabel instrument :=
  probe_skeleton_recovers_label instrument label
    (Mettapedia.GSLT.HigherOrderBisimulation.Label.skeleton_eq related)

end Mettapedia.OSLF.Framework.SortedTypedInstruments.PayloadLabels
