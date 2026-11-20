import Mettapedia.GSLT.Core.OperationalReadback

/-!
# Delivered observations compose through actual intermediate phases

An implementation may expose an answer only after finite initialization or
completion. A delivered observation therefore has separate reflection and
realization laws. Their composition uses the existing operational path
lifting, including the actual intermediate state. No progress, cost or
universal scheduling guarantee is inferred from these may-observation laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Readouts

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational

universe uS uM uT uI

structure Delivery {S : GSLT.{uS}} {T : GSLT.{uT}}
    (comparison : OperationalCorrespondence S T) {Index : Type uI}
    (source : Index → S.Term → Prop) (target : Index → T.Term → Prop) : Prop where
  reflects : ∀ {s t}, comparison.related s t → ∀ i, target i t → source i s
  realizes : ∀ {s t}, comparison.related s t → ∀ i, source i s →
    ∃ after, T.MultiStep t after ∧ target i after

namespace Delivery

variable {S : GSLT.{uS}} {M : GSLT.{uM}} {T : GSLT.{uT}} {Index : Type uI}
  {source : Index → S.Term → Prop} {middle : Index → M.Term → Prop} {target : Index → T.Term → Prop}

theorem of_exact {comparison : OperationalCorrespondence S T}
    (exactReadout : ∀ {s t}, comparison.related s t → ∀ i, source i s ↔ target i t) :
    Delivery comparison source target :=
  ⟨fun related i observed => (exactReadout related i).mpr observed,
    fun {_ t} related i observed => ⟨t, .refl t, (exactReadout related i).mp observed⟩⟩

theorem comp {first : OperationalCorrespondence S M} {second : OperationalCorrespondence M T}
    (one : Delivery first source middle) (two : Delivery second middle target) :
    Delivery (first.comp second) source target := by
  constructor
  · rintro s t ⟨m, before, after⟩ i observed
    exact one.reflects before i (two.reflects after i observed)
  · rintro s t ⟨m, before, after⟩ i observed
    obtain ⟨m', path, delivered⟩ := one.realizes before i observed
    obtain ⟨t', implementation, there⟩ := second.liftMultiStep after path
    obtain ⟨t'', completion, result⟩ := two.realizes there i delivered
    exact ⟨t'', multiStepAppend implementation completion, result⟩

theorem reachable_iff {comparison : OperationalCorrespondence S T}
    (delivery : Delivery comparison source target) {s t} (related : comparison.related s t) (i : Index) :
    (∃ after, S.MultiStep s after ∧ source i after) ↔
      ∃ after, T.MultiStep t after ∧ target i after :=
  comparison.reachable_iff_delayed (source i) (target i)
    (fun related => delivery.reflects related i) (fun related => delivery.realizes related i) related

end Delivery

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Readouts

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Readouts.Delivery.comp
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Readouts.Delivery.reachable_iff
