import Mettapedia.Machines.Cursor.ReadAdmissionProfiles

/-!
# Actual retirement requires a valid timestamp history

The store and take operation are the existing stamped-snapshot construction.
Birth/death bounds are derived for its constructors, not postulated as a take
result. They exclude a malformed future-death record which removal would
otherwise leave unchanged. Retained historical offers are not current takes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.TakeValidity

open Mettapedia.Machines.Cursor
open StampedSnapshots (Store Row)

variable {Value : Type}

def Valid (store : Store Value) : Prop :=
  ∀ id row, store.row id = some row →
    id < store.next ∧ row.born ≤ store.clock ∧
      ∀ death, row.death = some death → row.born ≤ death ∧ death ≤ store.clock

theorem empty_valid : Valid (StampedSnapshots.empty : Store Value) := by
  intro id row found
  cases found

theorem add_valid (store : Store Value) (valid : Valid store) (value : Value) :
    Valid (StampedSnapshots.add store value) := by
  intro id row found
  by_cases same : id = store.next
  · subst id
    simp only [StampedSnapshots.add, Function.update_self] at found
    obtain rfl := Option.some.inj found
    refine ⟨Nat.lt_succ_self _, le_rfl, ?_⟩
    intro death impossible
    cases impossible
  · have old : store.row id = some row := by
      simpa only [StampedSnapshots.add, Function.update_of_ne same] using found
    obtain ⟨position, born, dies⟩ := valid id row old
    exact ⟨position.trans_le (Nat.le_succ _), born.trans (Nat.le_succ _),
      fun death retired => ⟨(dies death retired).1, (dies death retired).2.trans (Nat.le_succ _)⟩⟩

theorem remove_valid (store : Store Value) (valid : Valid store) (retired : Nat) :
    Valid (StampedSnapshots.remove store retired) := by
  cases found : store.row retired with
  | none => simpa only [StampedSnapshots.remove, found] using valid
  | some previous =>
      cases death : previous.death with
      | some stamp => simpa only [StampedSnapshots.remove, found, death] using valid
      | none =>
          simp only [StampedSnapshots.remove, found, death]
          intro id row current
          by_cases same : id = retired
          · subst id
            simp only [Function.update_self] at current
            obtain rfl := Option.some.inj current
            have old := valid retired previous found
            refine ⟨old.1, old.2.1.trans (Nat.le_succ _), ?_⟩
            intro stamp dies
            have equal : store.clock + 1 = stamp := Option.some.inj dies
            subst stamp
            exact ⟨old.2.1.trans (Nat.le_succ _), le_rfl⟩
          · have oldFound : store.row id = some row := by
              simpa only [Function.update_of_ne same] using current
            obtain ⟨position, born, dies⟩ := valid id row oldFound
            exact ⟨position, born.trans (Nat.le_succ _),
              fun stamp retired => ⟨(dies stamp retired).1, (dies stamp retired).2.trans (Nat.le_succ _)⟩⟩

theorem retired_is_not_current (store : Store Value) (valid : Valid store) (id : Nat)
    (row : Row Value) (found : store.row id = some row) (death : Nat) (retired : row.death = some death) :
    ReadAdmissionProfiles.current store id = none := by
  have past := (valid id row found).2.2 death retired
  simp [ReadAdmissionProfiles.current, StampedSnapshots.atTime, found,
    StampedSnapshots.visible, retired, Nat.not_lt_of_ge past.2]

theorem current_requires_live_record (store : Store Value) (valid : Valid store)
    (offered : ReadAdmissionProfiles.Offer Value)
    (ready : ReadAdmissionProfiles.current store offered.1 = some offered)
    (row : Row Value) (found : store.row offered.1 = some row) : row.death = none := by
  cases death : row.death with
  | none => rfl
  | some stamp =>
      have missing := retired_is_not_current store valid offered.1 row found stamp death
      rw [missing] at ready
      cases ready

theorem take_retires (store : Store Value) (valid : Valid store)
    (offered : ReadAdmissionProfiles.Offer Value)
    (ready : ReadAdmissionProfiles.current store offered.1 = some offered) :
    ReadAdmissionProfiles.current (StampedSnapshots.remove store offered.1) offered.1 = none := by
  cases found : store.row offered.1 with
  | none => simp [ReadAdmissionProfiles.current, StampedSnapshots.atTime, found] at ready
  | some row =>
      have alive := current_requires_live_record store valid offered ready row found
      simp [ReadAdmissionProfiles.current, StampedSnapshots.remove, found, alive,
        StampedSnapshots.atTime, StampedSnapshots.visible]

theorem take_and_historical_read (store : Store Value) (valid : Valid store)
    (reader : StampedSnapshots.Reader) (admissible : StampedSnapshots.Admissible store reader)
    (offered : ReadAdmissionProfiles.Offer Value)
    (ready : ReadAdmissionProfiles.current store offered.1 = some offered) :
    ReadAdmissionProfiles.current (StampedSnapshots.remove store offered.1) offered.1 = none ∧
      ReadAdmissionProfiles.offers (StampedSnapshots.remove store offered.1) reader =
        ReadAdmissionProfiles.offers store reader :=
  ⟨take_retires store valid offered ready, ReadAdmissionProfiles.offers_remove store reader offered.1 admissible⟩

#print axioms add_valid
#print axioms remove_valid
#print axioms take_retires
#print axioms take_and_historical_read

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.TakeValidity
