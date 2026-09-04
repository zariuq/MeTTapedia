import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic

/-!
# Dependent writer extension in set families

A writer computation can expose both a returned value and an accumulated
log.  If result types may inspect that log, dependent sequencing needs more
than ordinary monadic bind: a value available in the fibre over the neutral
log must produce a value in every fibre which execution may expose.

This module isolates the set-family data required before any unit,
composition, or coherence law is considered.  The existence criterion is
exact at that weak level.  Constant families and a genuinely log-dependent
growing family provide positive controls.  An identity-only family provides
a negative control for list-valued writer logs.

The result is an effect-specific boundary.  It does not select a programming
calculus or assert that the positive constructions satisfy the full laws of a
dependent call-by-push-value model.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.WriterSetFamilyDependentExtension

universe uIndex uLog uFamily

/-! ## The raw extension problem -/

/-- The underlying set-family operation required by dependent writer
sequencing.  The input result inhabits the neutral-log fibre; the extension
must return a result in the fibre indexed by the observed log.

No equation is imposed here.  Failure of this raw operation is consequently
a necessary obstruction to every stronger lawful extension. -/
abbrev RawWriterDependentExtension
    {Index : Type uIndex} {Log : Type uLog} [One Log]
    (Family : Index → Log → Type uFamily) :=
  (index : Index) → (Family index 1 × Log) →
    (log : Log) → Family index log × Log

/-- Fibre transport out of the neutral writer state. -/
structure NeutralFibreTransport
    {Index : Type uIndex} {Log : Type uLog} [One Log]
    (Family : Index → Log → Type uFamily) where
  transport : (index : Index) → (log : Log) →
    Family index 1 → Family index log

/-- Every raw dependent writer extension induces neutral-fibre transport.
Only the returned value is used; no writer equation is needed. -/
def neutralFibreTransportOfRawExtension
    {Index : Type uIndex} {Log : Type uLog} [One Log]
    {Family : Index → Log → Type uFamily}
    (extension : RawWriterDependentExtension Family) :
    NeutralFibreTransport Family where
  transport index log value :=
    (extension index (value, 1) log).1

/-- Neutral-fibre transport supplies the raw dependent writer operation.  The
output log is accumulated in the ordinary writer order. -/
def rawExtensionOfNeutralFibreTransport
    {Index : Type uIndex} {Log : Type uLog} [Monoid Log]
    {Family : Index → Log → Type uFamily}
    (transport : NeutralFibreTransport Family) :
    RawWriterDependentExtension Family :=
  fun index seed log =>
    (transport.transport index log seed.1, seed.2 * log)

/-- At the lawless set-family level, existence of dependent writer extension
is exactly existence of transport from every neutral-log fibre. -/
theorem rawExtension_exists_iff_neutralFibreTransport
    {Index : Type uIndex} {Log : Type uLog} [Monoid Log]
    {Family : Index → Log → Type uFamily} :
    Nonempty (RawWriterDependentExtension Family) ↔
      Nonempty (NeutralFibreTransport Family) := by
  constructor
  · rintro ⟨extension⟩
    exact ⟨neutralFibreTransportOfRawExtension extension⟩
  · rintro ⟨transport⟩
    exact ⟨rawExtensionOfNeutralFibreTransport transport⟩

/-! ## Positive families -/

/-- Constant result families transport across every writer log. -/
def constantNeutralFibreTransport
    (Index : Type uIndex) (Log : Type uLog) [One Log]
    (Value : Type uFamily) :
    NeutralFibreTransport (fun _index : Index => fun _log : Log => Value) where
  transport _index _log value := value

/-- A genuinely log-dependent family whose fibre grows with the visible list
log. -/
def growingLogFamily (_index : Unit) (log : FreeMonoid Unit) : Type :=
  Fin (log.length + 1)

/-- The neutral fibre of `growingLogFamily` has a canonical image in every
later fibre. -/
def growingLogNeutralFibreTransport :
    NeutralFibreTransport growingLogFamily where
  transport _index log _value :=
    ⟨0, Nat.succ_pos log.length⟩

/-- The growing family therefore supports the raw dependent writer operation. -/
def growingLogRawExtension :
    RawWriterDependentExtension growingLogFamily :=
  rawExtensionOfNeutralFibreTransport growingLogNeutralFibreTransport

/-- The positive family is genuinely varying: its empty-log and one-event
fibres have different finite cardinalities. -/
theorem growingLogFamily_not_constant :
    ¬ ∃ Constant : Type,
      ∀ log : FreeMonoid Unit,
        Nonempty (growingLogFamily () log ≃ Constant) := by
  rintro ⟨Constant, familyEquiv⟩
  obtain ⟨atNeutral⟩ := familyEquiv 1
  obtain ⟨atOneEvent⟩ := familyEquiv (FreeMonoid.of ())
  have impossibleEquiv : Fin 1 ≃ Fin 2 := by
    simpa [growingLogFamily] using atNeutral.trans atOneEvent.symm
  have equalCardinality := Fintype.card_congr impossibleEquiv
  simp at equalCardinality

/-! ## A list-writer obstruction -/

/-- Results exist only before any writer event has occurred. -/
def identityOnlyFamily (_index : Unit) (log : FreeMonoid Unit) : Type :=
  if log.length = 0 then Unit else Empty

def identityOnlySeed :
    identityOnlyFamily () (1 : FreeMonoid Unit) × FreeMonoid Unit :=
  ((), 1)

/-- Even a lawless dependent extension is impossible for the identity-only
family: executing one writer event asks for an inhabitant of `Empty`. -/
theorem identityOnlyFamily_has_no_rawExtension :
    ¬ Nonempty (RawWriterDependentExtension identityOnlyFamily) := by
  rintro ⟨extension⟩
  have output := extension () identityOnlySeed (FreeMonoid.of ())
  have impossible : Empty := by
    simpa [identityOnlyFamily] using output.1
  exact impossible.elim

/-- Consequently the list writer cannot provide one unrestricted dependent
extension operation for every set-valued family. -/
theorem listWriter_has_no_unrestricted_rawExtension :
    ¬ ∀ Family : Unit → FreeMonoid Unit → Type,
      Nonempty (RawWriterDependentExtension Family) := by
  intro unrestricted
  exact identityOnlyFamily_has_no_rawExtension
    (unrestricted identityOnlyFamily)

/-- Positive and negative controls for effect-specific admission. -/
theorem writer_set_family_dependent_extension_boundary :
    Nonempty
        (RawWriterDependentExtension
          (fun _index : Bool => fun _log : FreeMonoid Unit => Bool)) /\
      Nonempty (RawWriterDependentExtension growingLogFamily) /\
      ¬ Nonempty (RawWriterDependentExtension identityOnlyFamily) := by
  constructor
  · exact ⟨rawExtensionOfNeutralFibreTransport
      (constantNeutralFibreTransport Bool (FreeMonoid Unit) Bool)⟩
  · exact ⟨⟨growingLogRawExtension⟩,
      identityOnlyFamily_has_no_rawExtension⟩

#print axioms neutralFibreTransportOfRawExtension
#print axioms rawExtensionOfNeutralFibreTransport
#print axioms rawExtension_exists_iff_neutralFibreTransport
#print axioms growingLogFamily_not_constant
#print axioms identityOnlyFamily_has_no_rawExtension
#print axioms listWriter_has_no_unrestricted_rawExtension
#print axioms writer_set_family_dependent_extension_boundary

end Mettapedia.TypeTheory.WriterSetFamilyDependentExtension
