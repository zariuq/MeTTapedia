import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SearchStep

/-!
# A staged certificate search, and the budgeted check of independence

**A chain of checks** (`Space.chain`): stage `i` passes to stage `i + 1` when its check holds, and
the last stage passing is the answer. It is a certificate search for the conjunction of the checks
(`chain_certifies`) that is finished at the budget of its length (`chain_finished`). It is refuted
at budget one when the first check fails (`chain_refuted_early`), and suspended at budget one when
the first check holds and more remain (`chain_suspended`).

**The check of independence** (`independenceCheck`): where diamonds close and admission is decided,
independence is the four admissions (`Transport.independent_iff_admits`), so it is a chain of four
checks (`independence_iff_checks`). This constructs the hypothesis of `checkOfSearch`: the budgeted
check is sound at every budget, never unknown from budget four on
(`independenceCheck_ne_unknown`), and unknown at budget zero (`independenceCheck_zero`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search

open Interface

universe uO uT uH uOcc uS uF uI u v

theorem Certifies.of_iff {σ : Type u} {α : Type v} {S : Space σ α} {x : α ⊕ σ} {Q Q' : Prop}
    (c : Certifies S x Q) (same : Q ↔ Q') : Certifies S x Q' :=
  ⟨fun p h => same.mp (c.sound p h), fun holds => c.complete (same.mpr holds)⟩

namespace Space

/-- **A chain of checks**: stage `i` passes when `ok i` holds; the last stage passing is the
answer. -/
def chain (ok : ℕ → Prop) [DecidablePred ok] (length : ℕ) : Space ℕ Unit where
  unfold i := if ok i then (if i + 1 = length then [.inl ()] else [.inr (i + 1)]) else []

variable (ok : ℕ → Prop) [DecidablePred ok] (length : ℕ)

/-- Stage `j` reaches an answer exactly when every check from `j` on holds. -/
theorem chain_reach : ∀ (d j : ℕ), j + d + 1 = length →
    ((∃ w u, (chain ok length).item (.inr j) w = some (.inl u)) ↔ ∀ i, j ≤ i → i < length → ok i)
  | 0, j, last => by
      constructor
      · rintro ⟨w, u, h⟩ i low high
        have : i = j := by omega
        subst this
        cases w with
        | nil => simp at h
        | cons k w =>
            rw [item_inr_cons] at h
            by_contra fails
            simp [chain, fails] at h
      · intro all
        refine ⟨[0], (), ?_⟩
        rw [item_inr_cons]
        simp [chain, all j le_rfl (by omega), show j + 1 = length by omega]
  | d + 1, j, last => by
      have next := chain_reach d (j + 1) (by omega)
      have notLast : j + 1 ≠ length := by omega
      constructor
      · rintro ⟨w, u, h⟩
        cases w with
        | nil => simp at h
        | cons k w =>
            rw [item_inr_cons] at h
            by_cases holds : ok j
            · simp only [chain, holds, if_true, notLast, if_false, Option.bind_eq_some_iff] at h
              obtain ⟨z, get, h⟩ := h
              cases k with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at get
                  subst get
                  have rest := next.mp ⟨w, u, h⟩
                  intro i low high
                  rcases Nat.eq_or_lt_of_le low with same | later
                  · exact same ▸ holds
                  · exact rest i later high
              | succ k => simp at get
            · simp [chain, holds] at h
      · intro all
        obtain ⟨w, u, h⟩ := next.mpr fun i low high => all i (by omega) high
        refine ⟨0 :: w, u, ?_⟩
        rw [item_inr_cons]
        have unfold : (chain ok length).unfold j = [.inr (j + 1)] := by
          simp [chain, all j le_rfl (by omega), notLast]
        rw [unfold]
        exact h

/-- **A chain is a certificate search for the conjunction of its checks.** -/
theorem chain_certifies (positive : 0 < length) :
    Certifies (chain ok length) (.inr 0) (∀ i < length, ok i) where
  sound p h := by
    have := (chain_reach ok length (length - 1) 0 (by omega)).mp ⟨p.1, p.2, h⟩
    exact fun i high => this i (Nat.zero_le i) high
  complete holds := by
    obtain ⟨w, u, h⟩ := (chain_reach ok length (length - 1) 0 (by omega)).mpr
      fun i _ high => holds i high
    exact ⟨(w, u), h⟩

/-- The states of a chain below a stage before its end lie at their stage, before the end. -/
theorem chain_state : ∀ (w : List ℕ) (j t : ℕ), j < length →
    (chain ok length).item (.inr j) w = some (.inr t) → t = j + w.length ∧ t < length
  | [], j, t, early, h => by
      simp only [item_nil, Option.some.injEq, Sum.inr.injEq] at h
      subst h
      exact ⟨rfl, early⟩
  | k :: w, j, t, early, h => by
      rw [item_inr_cons] at h
      by_cases holds : ok j
      · by_cases last : j + 1 = length
        · simp only [chain, holds, if_true, last, Option.bind_eq_some_iff] at h
          obtain ⟨z, get, h⟩ := h
          cases k with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at get
              subst get
              cases w <;> simp at h
          | succ k => simp at get
        · simp only [chain, holds, if_true, last, if_false, Option.bind_eq_some_iff] at h
          obtain ⟨z, get, h⟩ := h
          cases k with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at get
              subst get
              have := chain_state w (j + 1) t (by omega) h
              simp only [List.length_cons]
              omega
          | succ k => simp at get
      · simp [chain, holds] at h

/-- **A chain is finished at the budget of its length.** -/
theorem chain_finished (positive : 0 < length) :
    ((chain ok length).run length (.inr 0)).status = .finished := by
  rw [status_run_eq_finished_iff]
  intro w t h
  have := chain_state ok length w 0 t positive h
  omega

/-- **A failing first check refutes at budget one.** -/
theorem chain_refuted_early (fails : ¬ ok 0) :
    ((chain ok length).approx 1 (.inr 0)).verdict = .refuted := by
  rw [approx_succ]
  simp only [chain, fails, if_false, List.map_nil, List.sum_nil]
  rfl

/-- **A passing first check with more checks left is suspended at budget one.** -/
theorem chain_suspended (holds : ok 0) (more : 1 < length) :
    ((chain ok length).approx 1 (.inr 0)).verdict = .suspended := by
  rw [approx_succ]
  simp only [chain, holds, if_true, show (0 + 1 = length) = False by simp; omega, if_false,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, approx_zero, add_zero]
  rfl

end Space

/-! ## The budgeted check of independence -/

section Independence

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Interface.Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS}
  {Firing : State → Type uF} {P : Interface.Step X O State Firing}
  (T : Interface.Transport.{uO, uT, uH, uOcc, uS, uF, uI} P)

/-- The four checks of independence, in order: each firing's admission, then each residual's.
Stages from four on are never reached. -/
def independenceChecks {s : State} (f g : Firing s) : ℕ → Prop
  | 0 => P.Admits f
  | 1 => P.Admits g
  | 2 => ∃ first : P.Admits f, P.Admits (T.residual f first g)
  | 3 => ∃ second : P.Admits g, P.Admits (T.residual g second f)
  | _ + 4 => False

instance independenceChecks.decidable [∀ (t : State) (f : Firing t), Decidable (P.Admits f)]
    {s : State} (f g : Firing s) : DecidablePred (independenceChecks T f g)
  | 0 => inferInstanceAs (Decidable (P.Admits f))
  | 1 => inferInstanceAs (Decidable (P.Admits g))
  | 2 => inferInstanceAs (Decidable (∃ first : P.Admits f, P.Admits (T.residual f first g)))
  | 3 => inferInstanceAs (Decidable (∃ second : P.Admits g, P.Admits (T.residual g second f)))
  | _ + 4 => inferInstanceAs (Decidable False)

/-- **Where diamonds close, independence is the four checks.** -/
theorem independence_iff_checks (closes : T.Closes) {s : State} (f g : Firing s) :
    T.Independent s f g ↔ ∀ i < 4, independenceChecks T f g i := by
  rw [T.independent_iff_admits closes]
  constructor
  · rintro ⟨first, second, afterFirst, afterSecond⟩ i small
    match i, small with
    | 0, _ => exact first
    | 1, _ => exact second
    | 2, _ => exact ⟨first, afterFirst⟩
    | 3, _ => exact ⟨second, afterSecond⟩
  · intro checks
    obtain ⟨first, afterFirst⟩ : ∃ first : P.Admits f, P.Admits (T.residual f first g) := checks 2 (by omega)
    obtain ⟨second, afterSecond⟩ : ∃ second : P.Admits g, P.Admits (T.residual g second f) :=
      checks 3 (by omega)
    exact ⟨first, second, afterFirst, afterSecond⟩

variable [∀ (t : State) (f : Firing t), Decidable (P.Admits f)]

/-- **The staged search for independence certifies it**, where diamonds close. -/
theorem independenceSearch_certifies (closes : T.Closes) {s : State} (f g : Firing s) :
    Certifies (Space.chain (independenceChecks T f g) 4) (.inr 0) (T.Independent s f g) :=
  (Space.chain_certifies _ 4 (by omega)).of_iff (independence_iff_checks T closes f g).symm

/-- **The budgeted check of independence**: sound at every budget. -/
def independenceCheck (closes : T.Closes) (s : State) (n : ℕ) : T.Check s :=
  checkOfSearch T s (fun f g => Space.chain (independenceChecks T f g) 4) (fun _ _ => .inr 0)
    (independenceSearch_certifies T closes) n

/-- **From budget four on, the check never answers unknown.** -/
theorem independenceCheck_ne_unknown (closes : T.Closes) {s : State} {n : ℕ} (enough : 4 ≤ n)
    (f g : Firing s) : (independenceCheck T closes s n).verdict f g ≠ .unknown := by
  apply checkOfSearch_ne_unknown
  have finished := Space.chain_finished (independenceChecks T f g) 4 (by omega)
  rw [Space.run_eq_of_finished _ enough finished]
  exact finished

/-- **At budget zero the check answers unknown**, whatever holds. -/
theorem independenceCheck_zero (closes : T.Closes) {s : State} (f g : Firing s) :
    (independenceCheck T closes s 0).verdict f g = .unknown := by
  exact (checkOfSearch_unknown_iff f g).mpr ⟨rfl, rfl⟩

end Independence

#print axioms Certifies.of_iff
#print axioms Space.chain_reach
#print axioms Space.chain_certifies
#print axioms Space.chain_state
#print axioms Space.chain_finished
#print axioms Space.chain_refuted_early
#print axioms Space.chain_suspended
#print axioms independence_iff_checks
#print axioms independenceSearch_certifies
#print axioms independenceCheck
#print axioms independenceCheck_ne_unknown
#print axioms independenceCheck_zero

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search
