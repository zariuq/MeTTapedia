import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SearchSpace

/-!
# Tabling bounded search

A **memo table** records, for some states, an outcome of their search; a tabled run uses the
record instead of exploring the state (`Space.runMemo`).

* **Sound tables** (`SoundMemo`): every record lies below an approximant of its state in the
  information order. A record of a finished run is sound, and so is a record of a cut-off run
  **that keeps its cut-off status** (`soundMemo_approx`).
* **Tabling is sound** (`runMemo_le_approx`): a tabled run over a sound table lies below an
  approximant; finished, it is the unbounded semantics with its multiplicities
  (`count_runMemo_of_finished`).
* **A finished record must be the whole answer** (`finished_record_iff`): it is sound exactly when
  some approximant of its state is finished with those answers. Reusing a cut-off record as
  finished therefore breaks soundness where the state's search never finishes; the control is in
  `SearchControls` (`Controls.misread_record_unsound`, `Controls.misread_refutes`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search

universe u v

namespace Space

variable {σ : Type u} {α : Type v} (S : Space σ α)

/-- **A tabled run**: a state with a record is not explored; the record is its outcome. -/
def runMemo (memo : σ → Option (Outcome α)) : ℕ → α ⊕ σ → Outcome α
  | _, .inl a => Outcome.pure a
  | 0, .inr s => (memo s).getD Outcome.unknown
  | n + 1, .inr s => (memo s).getD ((S.unfold s).map (runMemo memo n)).sum

/-- **A sound table**: every record lies below an approximant of its state. -/
def SoundMemo (memo : σ → Option (Outcome α)) : Prop :=
  ∀ s o, memo s = some o → ∃ N, o ≤ S.approx N (.inr s)

/-- Without records, a tabled run is the budgeted run. -/
theorem runMemo_none : ∀ (n : ℕ) (x : α ⊕ σ), S.runMemo (fun _ => none) n x = S.approx n x
  | n, .inl a => by rw [runMemo, approx_inl]
  | 0, .inr s => by rw [runMemo, approx_zero, Option.getD_none]
  | n + 1, .inr s => by
      rw [runMemo, approx_succ, Option.getD_none]
      exact congrArg List.sum (List.map_congr_left fun y _ => runMemo_none n y)

/-- **Recording runs with their status is sound**, finished or cut off. -/
theorem soundMemo_approx (depth : σ → ℕ) (keep : σ → Prop) [DecidablePred keep] :
    S.SoundMemo fun s => if keep s then some (S.approx (depth s) (.inr s)) else none := by
  intro s o h
  dsimp only at h
  by_cases kept : keep s
  · rw [if_pos kept] at h
    obtain rfl := Option.some.inj h
    exact ⟨depth s, le_rfl⟩
  · rw [if_neg kept] at h
    cases h

/-- A common budget below which every alternative is approximated. -/
theorem common_budget {f : α ⊕ σ → Outcome α} :
    ∀ l : List (α ⊕ σ), (∀ y ∈ l, ∃ N, f y ≤ S.approx N y) → ∃ N, ∀ y ∈ l, f y ≤ S.approx N y
  | [], _ => ⟨0, fun y member => absurd member List.not_mem_nil⟩
  | y :: ys, h => by
      obtain ⟨N, below⟩ := h y (by simp)
      obtain ⟨M, rest⟩ := common_budget ys fun y' member => h y' (by simp [member])
      refine ⟨max N M, fun y' member => ?_⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact below.trans (S.approx_mono y' (le_max_left N M))
      · exact (rest y' member).trans (S.approx_mono y' (le_max_right N M))

/-- **Tabling is sound**: over a sound table, a tabled run lies below an approximant. -/
theorem runMemo_le_approx {memo : σ → Option (Outcome α)} (sound : S.SoundMemo memo) :
    ∀ (n : ℕ) (x : α ⊕ σ), ∃ N, S.runMemo memo n x ≤ S.approx N x
  | n, .inl a => ⟨0, by rw [runMemo, approx_inl]⟩
  | 0, .inr s => by
      cases h : memo s with
      | some o =>
          obtain ⟨N, below⟩ := sound s o h
          exact ⟨N, by rw [runMemo, h, Option.getD_some]; exact below⟩
      | none => exact ⟨0, by rw [runMemo, h, Option.getD_none]; exact bot_le⟩
  | n + 1, .inr s => by
      cases h : memo s with
      | some o =>
          obtain ⟨N, below⟩ := sound s o h
          exact ⟨N, by rw [runMemo, h, Option.getD_some]; exact below⟩
      | none =>
          obtain ⟨N, below⟩ := S.common_budget (S.unfold s)
            fun y _ => runMemo_le_approx sound n y
          refine ⟨N + 1, ?_⟩
          rw [runMemo, h, Option.getD_none, approx_succ]
          exact Outcome.list_sum_le_list_sum _ below

/-- **A finished tabled run over a sound table is the unbounded semantics.** -/
theorem count_runMemo_of_finished [DecidableEq α] {memo : σ → Option (Outcome α)}
    (sound : S.SoundMemo memo) {n : ℕ} {x : α ⊕ σ}
    (finished : (S.runMemo memo n x).status = .finished) (a : α) :
    ((S.runMemo memo n x).answers.count a : ℕ∞) = S.multiplicity x a := by
  obtain ⟨N, below⟩ := S.runMemo_le_approx sound n x
  have same := Outcome.eq_of_finished_le finished below
  have approxFinished : (S.run N x).status = .finished := by
    have := congrArg Outcome.status same
    rw [finished] at this
    exact this
  rw [← same]
  exact S.count_approx_eq_of_finished approxFinished a

/-- **A finished record must be the whole answer**: it is sound exactly when an approximant of its
state is finished with those answers. -/
theorem finished_record_iff (s : σ) (A : Multiset α) :
    (∃ N, (⟨A, .finished⟩ : Outcome α) ≤ S.approx N (.inr s)) ↔
      ∃ N, S.approx N (.inr s) = ⟨A, .finished⟩ := by
  constructor
  · rintro ⟨N, below⟩
    exact ⟨N, Outcome.eq_of_finished_le rfl below⟩
  · rintro ⟨N, same⟩
    exact ⟨N, same ▸ le_rfl⟩

/-- **A cut-off state never has a sound finished record**: if no approximant of the state is
finished, any record of it marked finished is unsound. -/
theorem finished_record_unsound (s : σ) (A : Multiset α)
    (never : ∀ N, (S.run N (.inr s)).status = .cutOff) :
    ¬ ∃ N, (⟨A, .finished⟩ : Outcome α) ≤ S.approx N (.inr s) := by
  rw [finished_record_iff]
  rintro ⟨N, same⟩
  have := congrArg Outcome.status same
  change (S.run N (.inr s)).status = .finished at this
  rw [never N] at this
  cases this

end Space

#print axioms Space.runMemo_none
#print axioms Space.soundMemo_approx
#print axioms Space.runMemo_le_approx
#print axioms Space.count_runMemo_of_finished
#print axioms Space.finished_record_iff
#print axioms Space.finished_record_unsound

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search
