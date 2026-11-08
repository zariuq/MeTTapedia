import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObserverFirstOrder

/-!
# Internal observers: records inside the state, renamed jointly with it

Clients inside the system are part of its state. Escape layers stack (`Transport.Natural.escaping`):
the inner layer's record is what the system's own processes sighted, and it is part of the state of
the outer layer, whose record is what the environment knows (`observedTransport`). Here the
environment records nothing more than it held at the start (`Transport.Escape.silent`), so
sightings stay inside the system.

An isomorphism of the outer layer renames the state and the internal records jointly, as
α-equivalence of the whole system, and carries the environment's record to the environment's record.

## Controls (`InternalControls`)

At `{5, 6}`, both labelled `0`:

* **Joint renaming** (`internal_renamed`): the system whose internal client sighted `{5}` and the
  system whose internal client sighted `{6}` are different states of one class: the exchange of `5`
  and `6`, applied to the state and the internal record together, is an isomorphism, although the
  internal client sighted `5`.
* **An external observer holding the same name blocks it** (`external_blocks`): when the environment
  holds a reference to `5` in both, no isomorphism relates them.
* **Sightings stay inside** (`internal_sighting_identified`, `internal_run_records`): taking `5` and
  taking `6`, both sighting `{5, 6}`, are trace equivalent; the sighted set is in the internal record
  and the environment's record stays empty.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Interface (Frames Transport Escaped)
open Observation (Record)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

section Internal

variable (A : SubstitutionAction T S) (label : O → T)

/-- **The system with internal records**: the one-frame instance, renaming occurrences, whose
processes record what their predicate queries sighted. -/
abbrev internalStep := (renamingEscape A label).step

/-- **The environment over the system with internal records**: escape relative to the transport with
internal records, recording nothing more. -/
abbrev observedTransport :=
  (renamingEscaping A label).escaping (Transport.Natural.escaping (renamingNatural A label) (renamingEscape A label))
    (Transport.Escape.silent _)

end Internal

namespace InternalControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature)
open EscapeControls (blank twins takeFive swapTwins takeFive_valid takeSix_valid)
open ObserverControls (swapIso)
open Observation.Record (sighting references)

/-- The environment over the controls' system with internal records. -/
abbrev observed := observedTransport ConstraintMultisetRewriting.Controls.A blank

/-- The system at `{5, 6}` whose internal client sighted `{o}`, with the environment's record `R`. -/
abbrev sawOne (o : ℕ) (R : Record ℕ) : Escaped (internalStep ConstraintMultisetRewriting.Controls.A blank) :=
  ⟨⟨twins, [], [sighting {o}]⟩, [], R⟩

/-- The exchange of `5` and `6`, applied to the state and the internal record together. -/
def jointSwap : observed.Iso (sawOne 5 []) (sawOne 6 []) :=
  ⟨⟨swapIso, .nil, by decide⟩, .nil, rfl⟩

/-- **A joint renaming of the state and the internal records is an isomorphism**, even for an
identity the internal client sighted: the system where it sighted `{5}` and the one where it
sighted `{6}` are different states of one class. -/
theorem internal_renamed :
    sawOne 5 [] ≠ sawOne 6 [] ∧
      Transport.StateClass.mk observed (sawOne 5 []) = Transport.StateClass.mk observed (sawOne 6 []) :=
  ⟨fun same => absurd (congrArg (fun x => x.state.record) same) (by decide),
    (Transport.StateClass.mk_eq_mk_iff observed).mpr ⟨jointSwap⟩⟩

/-- **An external observer holding `5` blocks it.** -/
theorem external_blocks : ¬ Nonempty (observed.Iso (sawOne 5 (references [5])) (sawOne 6 (references [5]))) := by
  rintro ⟨i⟩
  have outer : i.base.base.rename 5 = 5 :=
    Observation.Record.references_rename_eq_iff.mp i.record 5 (List.mem_singleton_self 5)
  have inner := i.base.record
  change Observation.Record.rename i.base.base.rename [sighting {5}] = [sighting {6}] at inner
  simp only [Observation.Record.rename, List.map_cons, List.map_nil, List.cons.injEq, and_true,
    Observation.Record.renameEntry_sighting, Finset.map_singleton, Equiv.coe_toEmbedding] at inner
  have same := Finset.singleton_inj.mp (Finset.map_injective Observation.Record.single inner)
  rw [outer] at same
  exact absurd same (by decide)

/-- The system at `{5, 6}` with nothing recorded inside or outside. -/
abbrev fresh : Escaped (internalStep ConstraintMultisetRewriting.Controls.A blank) := ⟨⟨twins, [], []⟩, [], []⟩

/-- Take `5` and sight `{5, 6}`, inside the system. -/
abbrev internalFive : (Transport.Escape.silent (renamingEscaping ConstraintMultisetRewriting.Controls.A blank)).step.Run fresh :=
  .cons takeFive takeFive_valid (.nil _)

/-- Take `6` and sight `{5, 6}`, inside the system. -/
abbrev internalSix : (Transport.Escape.silent (renamingEscaping ConstraintMultisetRewriting.Controls.A blank)).step.Run fresh :=
  .cons (takeFive.rename swapTwins) takeSix_valid (.nil _)

/-- The exchange of `5` and `6`, at the system with nothing recorded. -/
def freshSwap : observed.Iso fresh fresh := ⟨⟨swapIso, .nil, rfl⟩, .nil, rfl⟩

/-- **Internal sightings are renamed with the state**: taking `5` and taking `6` are trace
equivalent. -/
theorem internal_sighting_identified : observed.TraceEquiv fresh internalFive internalSix :=
  .rel _ _ (.inr (Transport.Similar.single freshSwap takeFive_valid takeSix_valid rfl))

/-- **The sighted set stays inside**: it is in the internal record at the end, and the environment's
record is empty. -/
theorem internal_run_records :
    internalFive.last.state.record = [sighting {5, 6}] ∧ internalFive.last.record = [] :=
  ⟨rfl, rfl⟩

end InternalControls

#print axioms InternalControls.jointSwap
#print axioms InternalControls.internal_renamed
#print axioms InternalControls.external_blocks
#print axioms InternalControls.internal_sighting_identified
#print axioms InternalControls.internal_run_records

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
