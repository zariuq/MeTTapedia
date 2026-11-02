import Mettapedia.Machines.MatchExistenceAdmission

/-!
# Existence evidence is indexed by its observation domain

A Boolean query over the mixed store is the disjunction of its compact and
ordinary-row queries. A coordinate helper may therefore observe only rows
after the caller has certified that the compact part contains no match.
That certificate cannot be dropped when reusing the helper for the whole
store. Partial evidence also keeps unknown distinct from proved absence.

All transport results hold for one fixed matching predicate. Changing its
bindings, program meaning or captured revision needs separate justification.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.MatchExistencePartition

open ShapeHeadRouting MatchExistenceAdmission
variable {Head Fact : Type}

def plainView (state : State Head Fact) : State Head Fact :=
  { state with data := ⟨∅, state.data.rows⟩ }

def compactView (state : State Head Fact) : State Head Fact :=
  { state with data := ⟨state.data.compact, 0⟩ }

theorem whole_exists_iff (accept : Fact → Bool) (state : State Head Fact) :
    existsMatch accept state = true ↔
      existsMatch accept (compactView state) = true ∨ existsMatch accept (plainView state) = true := by
  simp only [existsMatch_iff, observe, HybridShapeStore.denote, compactView, plainView,
    Finset.empty_val, add_zero, zero_add, Multiset.mem_add]
  constructor
  · rintro ⟨fact, kept | plain, matched⟩
    · exact Or.inl ⟨fact, kept, matched⟩
    · exact Or.inr ⟨fact, plain, matched⟩
  · rintro (⟨fact, member, matched⟩ | ⟨fact, member, matched⟩)
    · exact ⟨fact, Or.inl member, matched⟩
    · exact ⟨fact, Or.inr member, matched⟩

theorem whole_exists (accept : Fact → Bool) (state : State Head Fact) :
    existsMatch accept state =
      (existsMatch accept (compactView state) || existsMatch accept (plainView state)) := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.or_eq_true, whole_exists_iff]

theorem certified_compact_miss_restricts_domain (accept : Fact → Bool) (state : State Head Fact)
    (absent : existsMatch accept (compactView state) = false) :
    existsMatch accept state = existsMatch accept (plainView state) := by
  rw [whole_exists, absent, Bool.false_or]

theorem certified_compact_hit_finishes (accept : Fact → Bool) (state : State Head Fact)
    (present : existsMatch accept (compactView state) = true) : existsMatch accept state = true := by
  rw [whole_exists, present, Bool.true_or]

/-- None is an unclassified domain, not a domain proved empty. Any positive
witness suffices; absence needs negative evidence for both domains. -/
def merge : Option Bool → Option Bool → Option Bool
  | some true, _ | _, some true => some true
  | some false, some false => some false
  | _, _ => none

def Sound (actual : Bool) (evidence : Option Bool) : Prop :=
  ∀ answer, evidence = some answer → answer = actual

theorem merge_sound (left right : Option Bool) (a b : Bool)
    (leftSound : Sound a left) (rightSound : Sound b right) :
    Sound (a || b) (merge left right) := by
  cases left with
  | none => cases right with
      | none => simp [merge, Sound]
      | some value => cases value <;> simp_all [merge, Sound]
  | some value => cases value <;> cases right with
      | none => simp_all [merge, Sound]
      | some other => cases other <;> simp_all [merge, Sound]

theorem partition_evidence_sound (accept : Fact → Bool) (state : State Head Fact)
    (compact rows : Option Bool)
    (compactSound : Sound (existsMatch accept (compactView state)) compact)
    (rowSound : Sound (existsMatch accept (plainView state)) rows) :
    Sound (existsMatch accept state) (merge compact rows) := by
  rw [whole_exists]
  exact merge_sound compact rows _ _ compactSound rowSound

theorem admitted_partition_answer_correct (accept : Fact → Bool) (state : State Head Fact)
    (compact rows : Option Bool)
    (compactSound : Sound (existsMatch accept (compactView state)) compact)
    (rowSound : Sound (existsMatch accept (plainView state)) rows)
    (answer : Bool) (returned : merge compact rows = some answer) :
    answer = existsMatch accept state :=
  partition_evidence_sound accept state compact rows compactSound rowSound answer returned

theorem evidence_merge_commutes (left right : Option Bool) : merge left right = merge right left := by
  cases left with
  | none => cases right with
      | none => rfl
      | some value => cases value <;> rfl
  | some value => cases value <;> cases right with
      | none => rfl
      | some other => cases other <;> rfl

/-- A fixed query's positive witness transports along support inclusion;
duplicate counts are irrelevant to this Boolean observation. -/
theorem positive_survives_extension (accept : Fact → Bool) (before after : State Head Fact)
    (retained : ∀ fact ∈ observe before, fact ∈ observe after)
    (present : existsMatch accept before = true) : existsMatch accept after = true := by
  obtain ⟨fact, member, matched⟩ := (existsMatch_iff accept before).mp present
  exact (existsMatch_iff accept after).mpr ⟨fact, retained fact member, matched⟩

theorem absence_survives_restriction (accept : Fact → Bool) (before after : State Head Fact)
    (restricted : ∀ fact ∈ observe after, fact ∈ observe before)
    (absent : existsMatch accept before = false) : existsMatch accept after = false := by
  cases result : existsMatch accept after with
  | false => rfl
  | true =>
      have impossible := positive_survives_extension accept after before restricted result
      rw [absent] at impossible
      cases impossible

variable [DecidableEq Fact]
omit [DecidableEq Fact] in
theorem representation_preserves_existence (accept : Fact → Bool) (before after : State Head Fact)
    (same : observe before = observe after) : existsMatch accept before = existsMatch accept after := by
  simp only [existsMatch, same]

variable [DecidableEq Head]

/- Materializing the one relevant head suffices. Unrelated compact heads
may remain stored, even when their terms contain variables. -/
omit [DecidableEq Fact] in
theorem settled_head_has_no_compact_match (head : Fact → Head) (queryHead : Head)
    (accept : Fact → Bool) (state : State Head Fact)
    (compatible : ∀ fact ∈ state.data.compact, accept fact = true → head fact = queryHead) :
    existsMatch accept (compactView (settleHead head queryHead state)) = false := by
  apply Bool.eq_false_iff.mpr
  intro present
  obtain ⟨fact, member, matched⟩ := (existsMatch_iff accept _).mp present
  simp only [compactView, settleHead, observe, HybridShapeStore.denote,
    add_zero, Finset.mem_val, Finset.mem_filter] at member
  exact member.2 (compatible fact member.1 matched)

omit [DecidableEq Fact] in
theorem settling_relevant_head_licenses_row_observation (head : Fact → Head) (queryHead : Head)
    (accept : Fact → Bool) (state : State Head Fact)
    (compatible : ∀ fact ∈ state.data.compact, accept fact = true → head fact = queryHead) :
    existsMatch accept state = existsMatch accept (plainView (settleHead head queryHead state)) := by
  have same := observe_settleHead head queryHead state
  rw [representation_preserves_existence accept state (settleHead head queryHead state) same.symm]
  exact certified_compact_miss_restricts_domain accept _
    (settled_head_has_no_compact_match head queryHead accept state compatible)

omit [DecidableEq Head] in

theorem row_certificate_after_compact_miss (query : Fact) (accept : Fact → Bool)
    (state : State Head Fact) (self : accept query = true) (certified : Bool)
    (complete : certified = true → ∀ fact ∈ observe (plainView state), accept fact = true → fact = query)
    (compactAbsent : existsMatch accept (compactView state) = false)
    (answer : Bool)
    (returned : decideWithCertificate query certified (plainView state) = some answer) :
    answer = existsMatch accept state := by
  rw [certified_compact_miss_restricts_domain accept state compactAbsent]
  exact certificate_sound query accept (plainView state) self certified complete answer returned

namespace Controls

open MatchExistenceAdmission.Controls

theorem a_row_only_answer_is_not_a_whole_space_answer :
    existsMatch (acceptsAtom 2) (plainView compactVariable) = false ∧
      existsMatch (acceptsAtom 2) compactVariable = true := by decide

theorem unknown_is_not_absence : merge none (some false) = none := rfl

theorem a_row_hit_does_not_need_compact_classification : merge none (some true) = some true := rfl

def oneGround : State Unit (Option Nat) := ⟨fun _ => true, ⟨{some 1}, 0⟩⟩
def twoGround : State Unit (Option Nat) := ⟨fun _ => true, ⟨{some 1, some 2}, 0⟩⟩

theorem a_negative_certificate_does_not_survive_arbitrary_insertion :
    existsMatch (acceptsAtom 2) oneGround = false ∧ existsMatch (acceptsAtom 2) twoGround = true := by decide

theorem a_positive_certificate_does_not_survive_arbitrary_removal :
    existsMatch (acceptsAtom 2) twoGround = true ∧ existsMatch (acceptsAtom 2) oneGround = false := by decide

end Controls
end Mettapedia.Machines.MatchExistencePartition
