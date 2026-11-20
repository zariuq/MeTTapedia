import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.AlphaKey

/-!
# A payload set with alpha-invariant schematic insertion

This is the unlocated payload-set profile. Shared terms retain literal identity;
schematic values retain the existing whole-schema alpha key and rigid captures.
Duplicate insertion is determined by this key. It does not deduplicate
occurrence bags, erase provenance or identify rows merely because their readings
happen to agree. Zones and authorities belong outside this payload abstraction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.AlphaSet

open Mettapedia.Logic.LP
open OneFrame (Terms)

variable {signature : LPSignature}

abbrev Payload := Row (Terms (Term signature)) PUnit.unit
abbrev Key (signature : LPSignature) := Sum (Term signature) (AlphaKey.Key signature)
abbrev Store (signature : LPSignature) := Finset (Key signature)
abbrev X := OneFrame.frames (FirstOrder.action signature)

def key : Payload (signature := signature) → Key signature
  | .shared value => .inl value
  | .schematic closure => .inr (AlphaKey.key closure)

theorem same_key_readings (first second : Payload (signature := signature)) (same : key first = key second)
    (source : Subst signature) (value : Term signature) :
    first.ReadsAt X (b := PUnit.unit) source value ↔ second.ReadsAt X (b := PUnit.unit) source value := by
  cases first with
  | shared first =>
    cases second with
    | shared second =>
      have equality := Sum.inl.inj same
      cases equality
      rfl
    | schematic second => cases same
  | schematic first =>
    cases second with
    | shared second => cases same
    | schematic second => exact AlphaKey.key_eq_readings (Sum.inr.inj same) source value

def denotes (stored : Key signature) (source : Subst signature) (value : Term signature) : Prop :=
  ∃ row : Payload (signature := signature), key row = stored ∧ row.ReadsAt X (b := PUnit.unit) source value

theorem denotes_key (row : Payload (signature := signature)) (source : Subst signature) (value : Term signature) :
    denotes (key row) source value ↔ row.ReadsAt X (b := PUnit.unit) source value := by
  constructor
  · rintro ⟨other, same, reading⟩
    exact (same_key_readings other row same source value).mp reading
  · intro reading
    exact ⟨row, rfl, reading⟩

def answers (store : Store signature) (source : Subst signature) : Set (Term signature) :=
  {value | ∃ stored ∈ store, denotes stored source value}

noncomputable def insert (row : Payload (signature := signature)) (store : Store signature) : Store signature := by
  classical
  exact Insert.insert (key row) store

theorem insert_answers (row : Payload (signature := signature)) (store : Store signature) (source : Subst signature) :
    answers (insert row store) source = {value | row.ReadsAt X (b := PUnit.unit) source value} ∪ answers store source := by
  classical
  ext value
  change (∃ stored ∈ Insert.insert (key row) store, denotes stored source value) ↔
    row.ReadsAt X (b := PUnit.unit) source value ∨ ∃ stored ∈ store, denotes stored source value
  constructor
  · rintro ⟨stored, member, reading⟩
    rcases Finset.mem_insert.mp member with rfl | old
    · exact Or.inl ((denotes_key row source value).mp reading)
    · exact Or.inr ⟨stored, old, reading⟩
  · rintro (reading | ⟨stored, member, reading⟩)
    · exact ⟨key row, Finset.mem_insert_self _ _, (denotes_key row source value).mpr reading⟩
    · exact ⟨stored, Finset.mem_insert_of_mem member, reading⟩

theorem insert_same_key (first second : Payload (signature := signature)) (same : key first = key second)
    (store : Store signature) : insert second (insert first store) = insert first store := by
  classical
  change Insert.insert (key second) (Insert.insert (key first) store) = Insert.insert (key first) store
  rw [← same, Finset.insert_idem]

theorem two_insertions_eq_one_iff (first second : Payload (signature := signature)) :
    insert second (insert first ∅) = insert first ∅ ↔ key second = key first := by
  classical
  constructor
  · intro same
    have member : key second ∈ insert second (insert first ∅) := Finset.mem_insert_self _ _
    rw [same] at member
    simpa only [insert, Finset.mem_insert, Finset.notMem_empty, or_false] using member
  · intro same
    exact insert_same_key first second same.symm ∅

theorem insert_renamed (names : JointFirings.SymmetricMatches.Names signature.vars)
    (row : AlphaKey.RowClosure signature) (store : Store signature) :
    insert (.schematic (AlphaKey.renamed names.forward row)) (insert (.schematic row) store) =
      insert (.schematic row) store := by
  apply insert_same_key
  change Sum.inr (AlphaKey.key row) = Sum.inr (AlphaKey.key (AlphaKey.renamed names.forward row))
  exact congrArg Sum.inr (AlphaKey.key_renamed names row).symm

theorem captured_shared_still_distinct (value : Term signature) :
    key (.shared value) ≠ key (.schematic (Closure.captured value)) := by
  intro same
  cases same

theorem captured_shared_same_readings (value : Term signature) (source : Subst signature) (observed : Term signature) :
    (Row.shared value : Payload (signature := signature)).ReadsAt X (b := PUnit.unit) source observed ↔
      (Row.schematic (Closure.captured value) : Payload (signature := signature)).ReadsAt
        X (b := PUnit.unit) source observed := (Row.captured_is_shared X source value observed).symm

theorem captured_shared_two_keys (value : Term signature) :
    (insert (.schematic (Closure.captured value)) (insert (.shared value) ∅)).card = 2 := by
  classical
  simp [insert, key]

#print axioms same_key_readings
#print axioms insert_answers
#print axioms insert_same_key
#print axioms two_insertions_eq_one_iff
#print axioms insert_renamed
#print axioms captured_shared_still_distinct
#print axioms captured_shared_same_readings
#print axioms captured_shared_two_keys

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.AlphaSet
