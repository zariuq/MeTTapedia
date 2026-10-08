import Mettapedia.OSLF.Framework.SortedCommutativeInstrumentProfile

/-!
# Rigid probe values and complete parallel payloads

The fresh probe sorts have exactly their declared nullary value. They can
therefore remain in a label skeleton while base values and argument bundles
occupy process-bearing positions. A parallel context residue is represented
by its complete AC1 value, with both independently computed inventory
roundtrips. No process occurrence or payload is discarded.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments

open Mettapedia.OSLF.SortedCommutative

universe u
variable {Symbols : Type u} {arity : Symbols → Nat}

namespace PayloadLabels

def processSort : Srt arity → Bool
  | .base => true
  | .arguments _ => true
  | .probe _ => false

theorem probe_value_unique (instrument : Probe arity)
    (supplied : Value arity (.probe instrument)) : supplied = probe arity instrument := by
  have read : ∀ {sort : Srt arity} (value : Value arity sort) (selected : Probe arity),
      sort = .probe selected → HEq value (probe arity selected) := by
    refine @Term.rec (signature arity) (Parallel arity)
      (fun sort value => ∀ selected : Probe arity,
        sort = .probe selected → HEq value (probe arity selected)) ?_ ?_ ?_
    · intro sort parallel selected same
      exact (probe_not_parallel arity selected (same ▸ parallel)).elim
    · intro sort parallel _ _ _ _ selected same
      exact (probe_not_parallel arity selected (same ▸ parallel)).elim
    · intro constructor arguments _ selected same
      cases constructor with
      | original symbol => cases same
      | arguments constructor => cases same
      | probe instrument =>
        have equal : instrument = selected := InstrumentCutContexts.Srt.probe.inj same
        subst selected
        apply heq_of_eq
        apply congrArg (Term.node (signature := signature arity) (Parallel := Parallel arity)
          (Constructor.probe instrument))
        funext position
        exact Fin.elim0 position
      | cut instrument => cases instrument <;> cases same
  exact eq_of_heq (read supplied instrument rfl)

theorem probe_class_unique (instrument : Probe arity)
    (supplied : ValueClass arity (.probe instrument)) :
    supplied = classOf (probe arity instrument) := by
  refine Quotient.inductionOn supplied ?_
  intro value
  exact congrArg classOf (probe_value_unique instrument value)

def rigidValue (sort : Srt arity) (rigid : processSort sort = false) : ValueClass arity sort := by
  cases sort with
  | base => cases rigid
  | arguments constructor => cases rigid
  | probe instrument => exact classOf (probe arity instrument)

theorem rigidValue_read (sort : Srt arity) (rigid : processSort sort = false)
    (supplied : ValueClass arity sort) : supplied = rigidValue sort rigid := by
  cases sort with
  | base => cases rigid
  | arguments constructor => cases rigid
  | probe instrument => exact probe_class_unique instrument supplied

def residueValue {sort : Srt arity} (parallel : Parallel arity sort)
    (supplied : Multiset (ResiduePayload (signature := signature arity)
      (Parallel := Parallel arity) sort)) : ValueClass arity sort :=
  assemble parallel (supplied.map Subtype.val)

def valueResidue {sort : Srt arity} (parallel : Parallel arity sort)
    (supplied : ValueClass arity sort) :
    Multiset (ResiduePayload (signature := signature arity) (Parallel := Parallel arity) sort) :=
  (inventoryQ supplied).map (fun head => ⟨head, parallel⟩)

theorem valueResidue_residueValue {sort : Srt arity} (parallel : Parallel arity sort)
    (supplied : Multiset (ResiduePayload (signature := signature arity)
      (Parallel := Parallel arity) sort)) :
    valueResidue parallel (residueValue parallel supplied) = supplied := by
  rw [valueResidue, residueValue, inventoryQ_assemble, Multiset.map_map]
  have identity : (fun head : ResiduePayload (signature := signature arity)
      (Parallel := Parallel arity) sort =>
      (⟨head.val, parallel⟩ : ResiduePayload (signature := signature arity)
        (Parallel := Parallel arity) sort)) = id := by
    funext head
    exact Subtype.ext rfl
  change Multiset.map (fun head : ResiduePayload (signature := signature arity)
    (Parallel := Parallel arity) sort =>
      (⟨head.val, parallel⟩ : ResiduePayload (signature := signature arity)
        (Parallel := Parallel arity) sort)) supplied = supplied
  rw [identity, Multiset.map_id]

theorem residueValue_valueResidue {sort : Srt arity} (parallel : Parallel arity sort)
    (supplied : ValueClass arity sort) :
    residueValue parallel (valueResidue parallel supplied) = supplied := by
  apply inventoryQ_injective
  rw [residueValue, inventoryQ_assemble, valueResidue, Multiset.map_map]
  exact Multiset.map_id _

theorem residue_empty_of_not_parallel {sort : Srt arity}
    (absent : ¬ Parallel arity sort)
    (supplied : Multiset (ResiduePayload (signature := signature arity)
      (Parallel := Parallel arity) sort)) : supplied = 0 :=
  Multiset.eq_zero_of_forall_notMem (fun head _ => absent head.property)

end PayloadLabels

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments
