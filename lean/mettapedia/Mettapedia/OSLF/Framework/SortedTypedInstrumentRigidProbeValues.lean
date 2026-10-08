import Mettapedia.OSLF.Framework.SortedTypedInstrumentProfile

/-!
# Rigid typed probes and complete heterogeneous residue payloads

Each fresh probe sort has exactly its declared nullary value. Original
sorts and argument bundles retain arbitrary complete values, including
observer-bearing values at an uninhabited original source sort. A parallel
residue is read as its whole AC1 value with both inventory roundtrips.
No source-sort inhabitant or total erasure is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.PayloadLabels

open Mettapedia.OSLF.SortedCommutative

universe u v

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop}

def processSort : Srt source Parallel → Bool
  | .original _ => true
  | .arguments _ => true
  | .probe _ => false

theorem probe_value_unique (instrument : Probe source Parallel)
    (supplied : Value (source := source) (Parallel := Parallel) (.probe instrument)) :
    supplied = probe instrument := by
  have read : ∀ {sort : Srt source Parallel} (value : Value (source := source) (Parallel := Parallel) sort)
      (selected : Probe source Parallel), sort = .probe selected → HEq value (probe selected) := by
    refine @Term.rec (signature source Parallel) NativeParallel
      (fun sort value => ∀ selected : Probe source Parallel,
        sort = .probe selected → HEq value (probe selected)) ?_ ?_ ?_
    · intro sort parallel selected same
      exact (probe_not_parallel selected (same ▸ parallel)).elim
    · intro sort parallel _ _ _ _ selected same
      exact (probe_not_parallel selected (same ▸ parallel)).elim
    · intro constructor arguments _ selected same
      cases constructor with
      | original symbol => cases same
      | arguments head => cases same
      | probe instrument =>
        have equal : instrument = selected := Srt.probe.inj same
        subst selected
        apply heq_of_eq
        apply congrArg (Term.node (signature := signature source Parallel) (Parallel := NativeParallel)
          (Constructor.probe instrument))
        funext position
        exact Fin.elim0 position
      | cut instrument => cases instrument <;> cases same
  exact eq_of_heq (read supplied instrument rfl)

theorem probe_class_unique (instrument : Probe source Parallel)
    (supplied : ValueClass (source := source) (Parallel := Parallel) (.probe instrument)) :
    supplied = classOf (probe instrument) := by
  refine Quotient.inductionOn supplied ?_
  intro value
  exact congrArg classOf (probe_value_unique instrument value)

def rigidValue (sort : Srt source Parallel) (rigid : processSort sort = false) :
    ValueClass (source := source) (Parallel := Parallel) sort := by
  cases sort with
  | original _ => cases rigid
  | arguments head => cases rigid
  | probe instrument => exact classOf (probe instrument)

theorem rigidValue_read (sort : Srt source Parallel) (rigid : processSort sort = false)
    (supplied : ValueClass (source := source) (Parallel := Parallel) sort) :
    supplied = rigidValue sort rigid := by
  cases sort with
  | original _ => cases rigid
  | arguments head => cases rigid
  | probe instrument => exact probe_class_unique instrument supplied

def residueValue {sort : Srt source Parallel} (parallel : NativeParallel sort)
    (supplied : Multiset (ResiduePayload (signature := signature source Parallel)
      (Parallel := NativeParallel) sort)) : ValueClass (source := source) (Parallel := Parallel) sort :=
  assemble parallel (supplied.map Subtype.val)

def valueResidue {sort : Srt source Parallel} (parallel : NativeParallel sort)
    (supplied : ValueClass (source := source) (Parallel := Parallel) sort) :
    Multiset (ResiduePayload (signature := signature source Parallel) (Parallel := NativeParallel) sort) :=
  (inventoryQ supplied).map (fun head => ⟨head, parallel⟩)

theorem valueResidue_residueValue {sort : Srt source Parallel} (parallel : NativeParallel sort)
    (supplied : Multiset (ResiduePayload (signature := signature source Parallel)
      (Parallel := NativeParallel) sort)) :
    valueResidue parallel (residueValue parallel supplied) = supplied := by
  rw [valueResidue, residueValue, inventoryQ_assemble, Multiset.map_map]
  have identity : (fun head : ResiduePayload (signature := signature source Parallel)
      (Parallel := NativeParallel) sort =>
      (⟨head.val, parallel⟩ : ResiduePayload (signature := signature source Parallel)
        (Parallel := NativeParallel) sort)) = id := by
    funext head
    exact Subtype.ext rfl
  change Multiset.map (fun head : ResiduePayload (signature := signature source Parallel)
    (Parallel := NativeParallel) sort =>
      (⟨head.val, parallel⟩ : ResiduePayload (signature := signature source Parallel)
        (Parallel := NativeParallel) sort)) supplied = supplied
  rw [identity, Multiset.map_id]

theorem residueValue_valueResidue {sort : Srt source Parallel} (parallel : NativeParallel sort)
    (supplied : ValueClass (source := source) (Parallel := Parallel) sort) :
    residueValue parallel (valueResidue parallel supplied) = supplied := by
  apply inventoryQ_injective
  rw [residueValue, inventoryQ_assemble, valueResidue, Multiset.map_map]
  exact Multiset.map_id _

theorem residue_empty_of_not_parallel {sort : Srt source Parallel}
    (absent : ¬NativeParallel sort)
    (supplied : Multiset (ResiduePayload (signature := signature source Parallel)
      (Parallel := NativeParallel) sort)) : supplied = 0 :=
  Multiset.eq_zero_of_forall_notMem (fun head _ => absent head.property)

end Mettapedia.OSLF.Framework.SortedTypedInstruments.PayloadLabels
