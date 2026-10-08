import Mettapedia.Logic.LP.ClauseSubsumption

/-! All clause-alignment witnesses, including distinct selections with equal
substitutions. The occurrence policy checks selected indices before solving;
no answer-set quotient removes duplicate evidence selections. -/

namespace Mettapedia.Logic.LP.ClauseSubsumption

universe u v
variable {σ : LPSignature.{u, u, v, u}}
variable [DecidableEq σ.vars] [DecidableEq σ.constants]
variable [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]

def searchAll (consume : Bool) (source target : Clause σ) :
    List (List (Fin target.length) × Subst σ) :=
  (selections target.length source.length).filterMap fun indices =>
    (check consume source target indices).map (indices, ·)

theorem mem_searchAll (consume : Bool) (source target : Clause σ)
    (indices : List (Fin target.length)) (answer : Subst σ) :
    (indices, answer) ∈ searchAll consume source target ↔
      indices.length = source.length ∧ check consume source target indices = some answer := by
  constructor
  · intro member
    obtain ⟨candidate, included, accepted⟩ := List.mem_filterMap.mp member
    cases hc : check consume source target candidate with
    | none => simp [hc] at accepted
    | some value =>
      have equal : candidate = indices ∧ value = answer := by simpa [hc] using accepted
      rcases equal with ⟨rfl, rfl⟩
      exact ⟨(mem_selections _).mp included, hc⟩
  · rintro ⟨lengthEq, accepted⟩
    exact List.mem_filterMap.mpr
      ⟨indices, (mem_selections indices).mpr lengthEq, by simp [accepted]⟩

theorem searchAll_sound (consume : Bool) (source target : Clause σ)
    (indices : List (Fin target.length)) (answer : Subst σ)
    (member : (indices, answer) ∈ searchAll consume source target) :
    RigidUnification.Fixes (fun x => x ∈ clauseVars target) answer ∧
      Covers answer source target ∧ (consume = true → indices.Nodup) :=
  check_sound consume source target indices answer
    ((mem_searchAll consume source target indices answer).mp member).2

/-- Every admissible alignment is returned with a checked, usable witness,
    even if another alignment induces exactly the same images. -/
theorem searchAll_alignment_complete (consume : Bool) (source target : Clause σ)
    (indices : List (Fin target.length)) (answer : Subst σ)
    (fixed : RigidUnification.Fixes (fun x => x ∈ clauseVars target) answer)
    (aligned : source.map (apply answer) = selected target indices)
    (distinct : consume = true → indices.Nodup) :
    ∃ result, (indices, result) ∈ searchAll consume source target := by
  obtain ⟨result, accepted⟩ := check_complete consume source target indices answer fixed aligned distinct
  refine ⟨result, (mem_searchAll consume source target indices result).mpr ⟨?_, accepted⟩⟩
  simpa [selected] using (congrArg List.length aligned).symm

theorem searchAll_set_complete (source target : Clause σ) (answer : Subst σ)
    (fixed : RigidUnification.Fixes (fun x => x ∈ clauseVars target) answer)
    (covers : Covers answer source target) :
    ∃ hit, hit ∈ searchAll false source target := by
  obtain ⟨indices, aligned⟩ := alignment_of_covers source target answer covers
  obtain ⟨result, member⟩ := searchAll_alignment_complete false source target indices
    answer fixed aligned (by simp)
  exact ⟨(indices, result), member⟩

theorem searchAll_set_empty_iff (source target : Clause σ) :
    searchAll false source target = [] ↔ ¬∃ answer,
      RigidUnification.Fixes (fun x => x ∈ clauseVars target) answer ∧ Covers answer source target := by
  constructor
  · rintro empty ⟨answer, fixed, covers⟩
    obtain ⟨hit, member⟩ := searchAll_set_complete source target answer fixed covers
    simp [empty] at member
  · intro impossible
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨indices, answer⟩ member
    have sound := searchAll_sound false source target indices answer member
    exact impossible ⟨answer, sound.1, sound.2.1⟩

#print axioms searchAll_sound
#print axioms searchAll_alignment_complete
#print axioms searchAll_set_complete
#print axioms searchAll_set_empty_iff

end Mettapedia.Logic.LP.ClauseSubsumption
