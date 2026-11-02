import Mathlib.Tactic

/-!
# Domain-qualified occurrences across segments, delta and compaction

An occurrence key is a persistent domain and serial number, not a payload,
revision, file offset or traversal counter. Immutable segments and a live
delta store identified records. Retirement hides a record but preserves the
issued-ID history. Compaction coalesces that history without renaming it.

An import plan records source ID, target ID and target payload for every
occurrence. Its request receipt records the whole association, so retries do
not silently change mappings or resurrect retired records. Payload/reference
recoding is supplied explicitly by the plan; byte codecs, allocator freshness,
atomic publication, crash recovery and reclamation are not verified here.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PersistentOccurrenceSegments

abbrev OccId (Domain : Type) := Domain × Nat
abbrev Entry (Domain Payload : Type) := OccId Domain × Payload
abbrev Plan (Domain Payload : Type) := Finset (OccId Domain × Entry Domain Payload)

structure Store (Domain Payload : Type) where
  domain : Domain
  segments : List (Finset (Entry Domain Payload))
  delta : Finset (Entry Domain Payload)
  retired : Finset (OccId Domain)
  receipts : Nat → Option (Plan Domain Payload)

variable {Domain Payload : Type} [DecidableEq Domain] [DecidableEq Payload]

def records (s : Store Domain Payload) : Finset (Entry Domain Payload) :=
  s.segments.foldr (· ∪ ·) ∅ ∪ s.delta

def live (s : Store Domain Payload) : Finset (Entry Domain Payload) :=
  (records s).filter (fun e => e.1 ∉ s.retired)

def payloadBag (s : Store Domain Payload) : Multiset Payload := (live s).val.map Prod.snd

abbrev Resolves (s : Store Domain Payload) (id : OccId Domain) (payload : Payload) : Prop :=
  (id, payload) ∈ live s

def issued (s : Store Domain Payload) : Finset (OccId Domain) := (records s).image Prod.fst

def planEntries (plan : Plan Domain Payload) : Finset (Entry Domain Payload) := plan.image Prod.snd

def Functional (entries : Finset (Entry Domain Payload)) : Prop :=
  ∀ e ∈ entries, ∀ f ∈ entries, e.1 = f.1 → e.2 = f.2

def Valid (s : Store Domain Payload) : Prop :=
  Functional (records s) ∧
  (∀ e ∈ records s, e.1.1 = s.domain) ∧
  ∀ request plan, s.receipts request = some plan → planEntries plan ⊆ records s

def empty (domain : Domain) : Store Domain Payload := ⟨domain, [], ∅, ∅, fun _ => none⟩

def compact (s : Store Domain Payload) : Store Domain Payload :=
  { s with segments := [records s], delta := ∅ }

def flush (s : Store Domain Payload) : Store Domain Payload :=
  { s with segments := s.delta :: s.segments, delta := ∅ }

@[simp] theorem records_compact (s : Store Domain Payload) : records (compact s) = records s := by
  simp [records, compact]

@[simp] theorem records_flush (s : Store Domain Payload) : records (flush s) = records s := by
  simp [records, flush, Finset.union_comm]

@[simp] theorem live_compact (s : Store Domain Payload) : live (compact s) = live s := by
  unfold live
  rw [records_compact]
  rfl

@[simp] theorem live_flush (s : Store Domain Payload) : live (flush s) = live s := by
  unfold live
  rw [records_flush]
  rfl

theorem compaction_preserves_ids_and_bag (s : Store Domain Payload) :
    live (compact s) = live s ∧ payloadBag (compact s) = payloadBag s ∧
      (compact s).receipts = s.receipts := by
  exact ⟨live_compact s, congrArg (fun rows => rows.val.map Prod.snd) (live_compact s), rfl⟩

theorem compact_resolves (s : Store Domain Payload) (id : OccId Domain) (p : Payload) :
    Resolves (compact s) id p ↔ Resolves s id p := by simp [Resolves]

theorem resolves_functional (s : Store Domain Payload) (valid : Valid s)
    (id : OccId Domain) (p q : Payload) (hp : Resolves s id p) (hq : Resolves s id q) : p = q :=
  valid.1 (id, p) (Finset.mem_filter.mp hp).1 (id, q) (Finset.mem_filter.mp hq).1 rfl

def eraseId (id : OccId Domain) (s : Store Domain Payload) : Store Domain Payload :=
  if id ∈ (live s).image Prod.fst then { s with retired := insert id s.retired } else s

@[simp] theorem records_eraseId (id : OccId Domain) (s : Store Domain Payload) :
    records (eraseId id s) = records s := by unfold eraseId; split <;> rfl

@[simp] theorem receipts_eraseId (id : OccId Domain) (s : Store Domain Payload) :
    (eraseId id s).receipts = s.receipts := by unfold eraseId; split <;> rfl

theorem live_eraseId (id : OccId Domain) (s : Store Domain Payload) :
    live (eraseId id s) = (live s).filter (fun e => e.1 ≠ id) := by
  by_cases present : id ∈ (live s).image Prod.fst
  · rw [eraseId, if_pos present]
    ext e
    simp [live, records, and_assoc, and_comm]
  · rw [eraseId, if_neg present]
    symm
    apply Finset.filter_eq_self.mpr
    intro e he equal
    exact present (Finset.mem_image.mpr ⟨e, he, equal⟩)

theorem eraseId_self (id : OccId Domain) (s : Store Domain Payload) (p : Payload) :
    ¬ Resolves (eraseId id s) id p := by simp [Resolves, live_eraseId]

theorem eraseId_other (id other : OccId Domain) (different : other ≠ id)
    (s : Store Domain Payload) (p : Payload) :
    Resolves (eraseId id s) other p ↔ Resolves s other p := by
  simp [Resolves, live_eraseId, different]

/-- With functional IDs, removal discards exactly the selected identified record. -/
theorem eraseId_exact (s : Store Domain Payload) (valid : Valid s)
    (id : OccId Domain) (p : Payload) (found : Resolves s id p) :
    live (eraseId id s) = (live s).erase (id, p) := by
  rw [live_eraseId]
  ext e
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨member, different⟩
    exact ⟨fun same => different (congrArg Prod.fst same), member⟩
  · rintro ⟨different, member⟩
    refine ⟨member, ?_⟩
    intro sameId
    have samePayload := valid.1 e (Finset.mem_filter.mp member).1 (id, p)
      (Finset.mem_filter.mp found).1 sameId
    exact different (Prod.ext sameId samePayload)

theorem payloadBag_eraseId (s : Store Domain Payload) (valid : Valid s)
    (id : OccId Domain) (p : Payload) (found : Resolves s id p) :
    payloadBag (eraseId id s) = (payloadBag s).erase p := by
  simp only [payloadBag, eraseId_exact s valid id p found, Finset.erase_val]
  exact Multiset.map_erase_of_mem Prod.snd (live s).val found

theorem valid_empty (domain : Domain) : Valid (empty (Payload := Payload) domain) := by
  simp [Valid, Functional, empty, records]

theorem valid_compact (s : Store Domain Payload) (valid : Valid s) : Valid (compact s) := by
  unfold Valid
  rw [records_compact]
  exact valid

theorem valid_eraseId (id : OccId Domain) (s : Store Domain Payload) (valid : Valid s) :
    Valid (eraseId id s) := by
  unfold eraseId
  split <;> simpa [Valid, records] using valid

/-- Source and target assignments are both unambiguous within a plan. -/
abbrev PlanValid (plan : Plan Domain Payload) : Prop :=
  ∀ a ∈ plan, ∀ b ∈ plan, a.1 = b.1 ∨ a.2.1 = b.2.1 → a = b

abbrev Allowed (plan : Plan Domain Payload) (s : Store Domain Payload) : Prop :=
  PlanValid plan ∧ ∀ a ∈ plan,
    a.2.1.1 = s.domain ∧ a.2.1 ∉ issued s ∧ a.2.1 ∉ s.retired

def install (request : Nat) (plan : Plan Domain Payload) (s : Store Domain Payload) : Store Domain Payload :=
  { s with
    delta := s.delta ∪ planEntries plan
    receipts := Function.update s.receipts request (some plan) }

@[simp] theorem records_install (request : Nat) (plan : Plan Domain Payload) (s : Store Domain Payload) :
    records (install request plan s) = records s ∪ planEntries plan := by
  simp [records, install, Finset.union_assoc]

def importPlan (request : Nat) (plan : Plan Domain Payload) (s : Store Domain Payload) :
    Option (Store Domain Payload) :=
  match s.receipts request with
  | some previous => if previous = plan then some s else none
  | none => if Allowed plan s then
      some (install request plan s)
    else none

theorem import_fresh (request : Nat) (plan : Plan Domain Payload) (s : Store Domain Payload)
    (fresh : s.receipts request = none) (allowed : Allowed plan s) :
    importPlan request plan s = some (install request plan s) := by
  simp only [importPlan, fresh, if_pos allowed]

/-- Receipts bind the source/target associations, not only the resulting payload set. -/
theorem import_retry (request : Nat) (plan : Plan Domain Payload)
    (s s' : Store Domain Payload) (done : importPlan request plan s = some s') :
    importPlan request plan s' = some s' := by
  unfold importPlan at done
  cases old : s.receipts request with
  | none =>
    simp only [old] at done
    split at done
    · cases done; simp [importPlan, install]
    · cases done
  | some prior =>
    simp only [old] at done
    split at done
    · rename_i equal; cases done; simp [importPlan, old, equal]
    · cases done

theorem receipt_after_import (request : Nat) (plan : Plan Domain Payload)
    (s s' : Store Domain Payload) (done : importPlan request plan s = some s') :
    s'.receipts request = some plan := by
  unfold importPlan at done
  cases old : s.receipts request with
  | none =>
    simp only [old] at done
    split at done
    · cases done; simp [install]
    · cases done
  | some prior =>
    simp only [old] at done
    split at done
    · rename_i equal; cases done; simpa [equal] using old
    · cases done

theorem retry_after_removal (request : Nat) (plan : Plan Domain Payload)
    (s s' : Store Domain Payload) (done : importPlan request plan s = some s') (id : OccId Domain) :
    importPlan request plan (eraseId id s') = some (eraseId id s') := by
  simp [importPlan, receipt_after_import request plan s s' done]

theorem retry_after_compaction (request : Nat) (plan : Plan Domain Payload)
    (s s' : Store Domain Payload) (done : importPlan request plan s = some s') :
    importPlan request plan (compact s') = some (compact s') := by
  simp [importPlan, compact, receipt_after_import request plan s s' done]

theorem mapped_records_present (request : Nat) (plan : Plan Domain Payload)
    (s : Store Domain Payload) (fresh : s.receipts request = none) (allowed : Allowed plan s) :
    ∃ s', importPlan request plan s = some s' ∧
      ∀ a ∈ plan, Resolves s' a.2.1 a.2.2 := by
  refine ⟨_, import_fresh request plan s fresh allowed, ?_⟩
  intro a ha
  have retained := (allowed.2 a ha).2.2
  have member : a.2 ∈ planEntries plan := Finset.mem_image.mpr ⟨a, ha, rfl⟩
  change a.2 ∈ live (install request plan s)
  rw [live, Finset.mem_filter, records_install]
  exact ⟨Finset.mem_union_right _ member, retained⟩

/-- A previously issued ID cannot be reassigned by a new import request. -/
theorem reuse_refused (request : Nat) (plan : Plan Domain Payload) (s : Store Domain Payload)
    (fresh : s.receipts request = none) (a : OccId Domain × Entry Domain Payload)
    (member : a ∈ plan) (used : a.2.1 ∈ issued s) : importPlan request plan s = none := by
  have forbidden : ¬ Allowed plan s := fun h => (h.2 a member).2.1 used
  simp [importPlan, fresh, forbidden]

theorem planEntries_functional (plan : Plan Domain Payload) (valid : PlanValid plan) :
    Functional (planEntries plan) := by
  intro e he f hf equal
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hf
  have same := valid a ha b hb (.inr equal)
  exact congrArg (fun x => x.2.2) same

theorem allowed_separates_ids (plan : Plan Domain Payload) (s : Store Domain Payload)
    (allowed : Allowed plan s) (e f : Entry Domain Payload)
    (old : e ∈ records s) (incoming : f ∈ planEntries plan) : e.1 ≠ f.1 := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp incoming
  intro same
  exact (allowed.2 a ha).2.1 (Finset.mem_image.mpr ⟨e, old, same⟩)

theorem valid_install (request : Nat) (plan : Plan Domain Payload) (s : Store Domain Payload)
    (valid : Valid s) (allowed : Allowed plan s) : Valid (install request plan s) := by
  rw [Valid, records_install]
  refine ⟨?_, ?_, ?_⟩
  · intro e he f hf same
    rcases Finset.mem_union.mp he with he | he <;> rcases Finset.mem_union.mp hf with hf | hf
    · exact valid.1 e he f hf same
    · exact (allowed_separates_ids plan s allowed e f he hf same).elim
    · exact (allowed_separates_ids plan s allowed f e hf he same.symm).elim
    · exact planEntries_functional plan allowed.1 e he f hf same
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact valid.2.1 e he
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      exact (allowed.2 a ha).1
  · intro q prior found
    by_cases same : q = request
    · subst q
      simp only [install, Function.update_self, Option.some.injEq] at found
      subst prior
      exact Finset.subset_union_right
    · have old : s.receipts q = some prior := by
        simpa only [install, Function.update_of_ne same] using found
      exact (valid.2.2 q prior old).trans Finset.subset_union_left

theorem import_valid (request : Nat) (plan : Plan Domain Payload) (s s' : Store Domain Payload)
    (valid : Valid s) (done : importPlan request plan s = some s') : Valid s' := by
  unfold importPlan at done
  cases old : s.receipts request with
  | none =>
    simp only [old] at done
    split at done
    · rename_i allowed; cases done; exact valid_install request plan s valid allowed
    · cases done
  | some prior =>
    simp only [old] at done
    split at done
    · cases done; exact valid
    · cases done

/-- A new import cannot alter the meaning of an already issued reference. -/
theorem install_preserves_old_reference (request : Nat) (plan : Plan Domain Payload)
    (s : Store Domain Payload) (allowed : Allowed plan s) (id : OccId Domain)
    (old : id ∈ issued s) (payload : Payload) :
    Resolves (install request plan s) id payload ↔ Resolves s id payload := by
  have absent : (id, payload) ∉ planEntries plan := by
    intro member
    obtain ⟨a, ha, equal⟩ := Finset.mem_image.mp member
    have same := congrArg Prod.fst equal
    exact (allowed.2 a ha).2.1 (same.symm ▸ old)
  simp only [Resolves, live, Finset.mem_filter, records_install, Finset.mem_union,
    absent, or_false]
  rfl

theorem import_preserves_old_reference (request : Nat) (plan : Plan Domain Payload)
    (s s' : Store Domain Payload) (done : importPlan request plan s = some s')
    (id : OccId Domain) (oldId : id ∈ issued s) (payload : Payload) :
    Resolves s' id payload ↔ Resolves s id payload := by
  unfold importPlan at done
  cases receipt : s.receipts request with
  | none =>
    simp only [receipt] at done
    split at done
    · rename_i allowed
      cases done
      exact install_preserves_old_reference request plan s allowed id oldId payload
    · cases done
  | some previous =>
    simp only [receipt] at done
    split at done
    · cases done; rfl
    · cases done

theorem foreign_reference_rejected (s : Store Domain Payload) (valid : Valid s)
    (id : OccId Domain) (foreign : id.1 ≠ s.domain) (payload : Payload) :
    ¬ Resolves s id payload := by
  intro found
  exact foreign (valid.2.1 (id, payload) (Finset.mem_filter.mp found).1)

/-- Construct the declared finite import association, including an explicit payload recoding. -/
def fromMapping (source : Finset (Entry Domain Payload)) (rename : OccId Domain → OccId Domain)
    (recode : Payload → Payload) : Plan Domain Payload :=
  source.image (fun e => (e.1, (rename e.1, recode e.2)))

theorem mapping_identity (source : Finset (Entry Domain Payload)) :
    planEntries (fromMapping source id id) = source := by
  simp [planEntries, fromMapping, Finset.image_image, Function.comp_def]

/-- Successive declared maps compose on records; transaction receipt histories remain separate. -/
theorem mapping_composition (source : Finset (Entry Domain Payload))
    (first second : OccId Domain → OccId Domain) (body₁ body₂ : Payload → Payload) :
    planEntries (fromMapping (planEntries (fromMapping source first body₁)) second body₂) =
      planEntries (fromMapping source (second ∘ first) (body₂ ∘ body₁)) := by
  simp [planEntries, fromMapping, Finset.image_image, Function.comp_def]

theorem fromMapping_valid (source : Finset (Entry Domain Payload))
    (functional : Functional source) (rename : OccId Domain → OccId Domain)
    (injective : Set.InjOn rename (source.image Prod.fst)) (recode : Payload → Payload) :
    PlanValid (fromMapping source rename recode) := by
  intro a ha b hb equal
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hb
  have same : e.1 = f.1 := by
    rcases equal with equal | equal
    · exact equal
    · exact injective (Finset.mem_image.mpr ⟨e, he, rfl⟩) (Finset.mem_image.mpr ⟨f, hf, rfl⟩) equal
  have body := functional e he f hf same
  simp only [same, body]

theorem changed_import_mapping_refused (request : Nat) (old new : Plan Domain Payload)
    (s : Store Domain Payload) (recorded : s.receipts request = some old) (changed : old ≠ new) :
    importPlan request new s = none := by simp only [importPlan, recorded, if_neg changed]

theorem compact_idempotent (s : Store Domain Payload) : compact (compact s) = compact s := by
  cases s
  simp [compact, records]

theorem compact_flush (s : Store Domain Payload) : compact (flush s) = compact s := by
  cases s
  simp [compact, records, flush, Finset.union_comm]

theorem compact_eraseId (id : OccId Domain) (s : Store Domain Payload) :
    compact (eraseId id s) = eraseId id (compact s) := by
  unfold eraseId
  simp only [live_compact]
  split <;> rfl

/-- Inert references do not fall back to another occurrence with an equal body. -/
def duplicateExample : Store Nat Nat :=
  ⟨9, [{((9, 0), 7)}, {((9, 1), 7)}], ∅, ∅, fun _ => none⟩

example : payloadBag duplicateExample = {7, 7} := by decide
example : ¬ Resolves (eraseId (9, 0) duplicateExample) (9, 0) 7 ∧
    Resolves (eraseId (9, 0) duplicateExample) (9, 1) 7 := by decide
example : Resolves duplicateExample (9, 0) 7 ∧ ¬ Resolves duplicateExample (10, 0) 7 := by decide
example : (compact duplicateExample).segments.length = 1 ∧
    payloadBag (compact duplicateExample) = {7, 7} := by decide

def examplePlan : Plan Nat Nat := {((1, 0), ((9, 4), 7)), ((1, 1), ((9, 5), 7))}

example : ∃ s', importPlan 42 examplePlan (empty 9) = some s' ∧ payloadBag s' = {7, 7} := by
  refine ⟨_, import_fresh 42 examplePlan (empty 9) rfl (by decide), ?_⟩
  decide

/-- Mapping two source occurrences to one target ID is rejected. -/
example : importPlan 42 ({((1, 0), ((9, 4), 7)), ((1, 1), ((9, 4), 7))} : Plan Nat Nat)
    (empty 9) = none := by decide

example : importPlan 42 ({((1, 0), ((8, 4), 7))} : Plan Nat Nat) (empty 9) = none := by decide

/-- Equal output bags do not authorize changing the source-to-target association on retry. -/
example :
    let state := install 42 examplePlan (empty 9)
    importPlan 42 ({((1, 0), ((9, 5), 7)), ((1, 1), ((9, 4), 7))} : Plan Nat Nat) state = none := by decide

#print axioms compaction_preserves_ids_and_bag
#print axioms eraseId_exact
#print axioms payloadBag_eraseId
#print axioms import_retry
#print axioms retry_after_removal
#print axioms mapped_records_present
#print axioms reuse_refused
#print axioms import_valid
#print axioms install_preserves_old_reference
#print axioms import_preserves_old_reference
#print axioms fromMapping_valid
#print axioms mapping_composition
#print axioms compact_eraseId

end Mettapedia.Machines.PersistentOccurrenceSegments
