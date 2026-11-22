import Mettapedia.Languages.HOLLight.ExportCodec

/-!
# Source-conclusion metadata and actual proof-cache addresses

This relation connects a stored named source conclusion to the same source
ID's actual registered cache entry. It is independent of registered history:
a valid derivation graph alone does not justify an arbitrary metadata table.
The update lemmas concern the existing graph/address/source-table functions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceMetadata

open Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution ExportReplay

def ConclusionsChecked (state : ExportReplay.State) (sources : Std.TreeMap Nat SourceTerm) : Prop :=
  ∀ (id : Nat) (source : SourceTerm), sources[id]? = some source →
    ∃ (position : Nat) (fact : Theorem), state.addresses[id]? = some position ∧ state.registered.cache[position]? = some fact ∧
      source.check = some fact.sequent.concl

theorem empty_conclusions_checked (state : ExportReplay.State) :
    ConclusionsChecked state ∅ := by
  intro id source found
  simp at found

theorem insert_lookup_other {A : Type} (table : Std.TreeMap Nat A) (key query : Nat) (value : A)
    (different : key ≠ query) : (table.insert key value)[query]? = table[query]? := by
  simp [Std.TreeMap.getElem?_insert, different]

theorem addresses_lookup_other (table : Std.TreeMap Nat Nat) (start : Nat) (ids : List Nat)
    (query : Nat) (outside : query ∉ ids) : (ExportReplay.addAddresses table start ids)[query]? = table[query]? := by
  induction ids generalizing table start with
  | nil => rfl
  | cons id rest ih =>
      have notHead : query ≠ id := fun same => outside (same ▸ List.mem_cons_self)
      have notRest : query ∉ rest := fun inside => outside (List.mem_cons_of_mem _ inside)
      rw [ExportReplay.addAddresses, ih _ _ notRest]
      exact insert_lookup_other table id query start notHead.symm

theorem addresses_lookup_at (table : Std.TreeMap Nat Nat) (start : Nat) (ids : List Nat)
    (unique : ids.Nodup) (index id : Nat) (found : ids[index]? = some id) :
    (ExportReplay.addAddresses table start ids)[id]? = some (start+index) := by
  induction ids generalizing table start index with
  | nil => simp at found
  | cons first rest ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst id
          rw [ExportReplay.addAddresses, addresses_lookup_other _ _ _ _ (List.nodup_cons.mp unique).1]
          simp only [Std.TreeMap.getElem?_insert_self, Nat.add_zero]
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          change (ExportReplay.addAddresses (table.insert first start) (start+1) rest)[id]? = some (start+(index+1))
          calc
            _ = some ((start+1)+index) := ih _ _ (List.nodup_cons.mp unique).2 index found
            _ = some (start+(index+1)) := congrArg some (by omega)

theorem conclusions_lookup_origin (table : Std.TreeMap Nat SourceTerm) (ids : List Nat)
    (sources : List SourceTerm) (query : Nat) (source : SourceTerm)
    (found : (ExportCodec.addConclusions table ids sources)[query]? = some source) :
    table[query]? = some source ∨ ∃ index : Nat, ids[index]? = some query ∧ sources[index]? = some source := by
  induction ids generalizing table sources with
  | nil => exact .inl found
  | cons id rest ih =>
      cases sources with
      | nil => exact .inl found
      | cons value later =>
          obtain old | ⟨index,idAt,sourceAt⟩ := ih (table.insert id value) later found
          · by_cases same : id = query
            · subst query
              simp only [Std.TreeMap.getElem?_insert_self, Option.some.injEq] at old
              exact .inr ⟨0,rfl,by simpa only [List.getElem?_cons_zero] using congrArg some old⟩
            · exact .inl ((insert_lookup_other table id query value same).symm.trans old)
          · exact .inr ⟨index+1,by simpa only [List.getElem?_cons_succ] using idAt,
              by simpa only [List.getElem?_cons_succ] using sourceAt⟩

theorem append_cache_old (before added : Array Theorem) (position : Nat) (fact : Theorem)
    (found : before[position]? = some fact) : (before ++ added)[position]? = some fact := by
  have inside : position < before.size := by
    obtain ⟨inside,_⟩ := Array.getElem?_eq_some_iff.mp found
    exact inside
  rw [Array.getElem?_append_left inside]
  exact found

theorem append_cache_new (before : Array Theorem) (added : List Theorem) (index : Nat) (fact : Theorem)
    (found : added[index]? = some fact) :
    (before ++ added.toArray)[before.size+index]? = some fact := by
  rw [Array.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
  simpa only [List.getElem?_toArray] using found

theorem apply_data (policy : AxiomPolicy) [DecidablePred policy]
    (before after : ExportReplay.State) (event : Event)
    (accepted : ExportReplay.apply policy before event = some after) :
    ∃ output : Registered.Output,
      event.command.check policy before.registered.context before.registered.cache = some output ∧
      event.sourceIds.Nodup ∧ (∀ id ∈ event.sourceIds, before.addresses[id]? = none) ∧
      event.sourceIds.length = output.theorems.length ∧
      event.claims = output.theorems.map Theorem.sequent ∧
      after.registered.cache = before.registered.cache ++ output.theorems.toArray ∧
      after.addresses = ExportReplay.addAddresses before.addresses before.registered.cache.size event.sourceIds := by
  have checked := ExportReplay.apply_checked policy accepted
  obtain ⟨output,commandChecked,length,claims⟩ := checked.2.2.2.2
  have fresh : event.sourceIds.Nodup ∧ ∀ id ∈ event.sourceIds, before.addresses[id]? = none := by
    simpa [ExportReplay.idsFreshB,List.all_eq_true] using checked.2.2.1
  have unique := fresh.1
  have absent := fresh.2
  have claimsChecked := (ExportReplay.claimsSame_eq_true_iff _ _).mpr claims
  let actual : ExportReplay.State :=
    ⟨⟨output.context,before.registered.cache ++ output.theorems.toArray,
        before.registered.receipts.push ⟨event.command,output.theorems⟩⟩,
      ExportReplay.addAddresses before.addresses before.registered.cache.size event.sourceIds,
      before.receipts.push event⟩
  have computes : ExportReplay.apply policy before event = some actual := by
    simp [ExportReplay.apply,checked.2.1,checked.2.2.1,commandChecked,length,claimsChecked,actual]
  have same := Option.some.inj (computes.symm.trans accepted)
  subst after
  exact ⟨output,commandChecked,unique,absent,length,claims,rfl,rfl⟩

private theorem checks_against_outputs (sources : List SourceTerm) (outputs : List Theorem)
    (checked : List.Forall₂ (fun source claim => source.check = some claim.concl)
      sources (outputs.map Theorem.sequent)) :
    List.Forall₂ (fun source fact => source.check = some fact.sequent.concl) sources outputs := by
  induction outputs generalizing sources with
  | nil => cases checked; exact .nil
  | cons fact rest ih =>
      cases checked with
      | cons first later => exact .cons first (ih _ later)

theorem apply_preserves_conclusions (policy : AxiomPolicy) [DecidablePred policy]
    (before after : ExportReplay.State) (event : Event)
    (oldSources : Std.TreeMap Nat SourceTerm) (sources : List SourceTerm)
    (beforeChecked : ConclusionsChecked before oldSources)
    (sourceChecks : List.Forall₂ (fun source claim => source.check = some claim.concl) sources event.claims)
    (accepted : ExportReplay.apply policy before event = some after) :
    ConclusionsChecked after (ExportCodec.addConclusions oldSources event.sourceIds sources) := by
  obtain ⟨output,_,unique,absent,length,claims,cacheEq,addressesEq⟩ := apply_data policy before after event accepted
  rw [claims] at sourceChecks
  have against := checks_against_outputs sources output.theorems sourceChecks
  intro id source found
  obtain old | ⟨index,idAt,sourceAt⟩ := conclusions_lookup_origin oldSources event.sourceIds sources id source found
  · obtain ⟨position,fact,addressAt,factAt,sourceChecked⟩ := beforeChecked id source old
    have outside : id ∉ event.sourceIds := by
      intro inside
      have impossible := (absent id inside).symm.trans addressAt
      cases impossible
    refine ⟨position,fact,?_,?_,sourceChecked⟩
    · rw [addressesEq,addresses_lookup_other _ _ _ _ outside]
      exact addressAt
    · rw [cacheEq]
      exact append_cache_old _ _ position fact factAt
  · obtain ⟨inside,sourceEq⟩ := List.getElem?_eq_some_iff.mp sourceAt
    have outputInside : index < output.theorems.length := by rw [← against.length_eq]; exact inside
    let fact := output.theorems[index]
    have factAt : output.theorems[index]? = some fact := List.getElem?_eq_getElem outputInside
    have sourceChecked : source.check = some fact.sequent.concl := by
      have pair := against.get inside outputInside
      change (sources[index]).check = some (output.theorems[index]).sequent.concl at pair
      rw [sourceEq] at pair
      exact pair
    refine ⟨before.registered.cache.size+index,fact,?_,?_,sourceChecked⟩
    · rw [addressesEq]
      exact addresses_lookup_at _ _ _ unique index id idAt
    · rw [cacheEq]
      exact append_cache_new _ _ index fact factAt

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceMetadata
