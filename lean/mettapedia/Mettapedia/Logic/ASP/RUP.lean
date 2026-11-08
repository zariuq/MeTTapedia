import Mettapedia.Logic.ASP.LRAT
import Mettapedia.Logic.ASP.FirstUIP

/-!
# Reverse unit propagation for learned nogoods: the proof events a solver emits

`LRAT` proves that an accepted LRAT proof refutes a program. This module proves
the other direction of the trust boundary: the nogoods the solver derives are
LRAT additions the checker accepts, with hints the solver already has.

## Reverse unit propagation over nogoods

`rupNogood α hints` assumes the literals `α` and walks the hints in order. A
hint whose literals are all assumed is violated and ends the check; a hint with
exactly one literal `m` not assumed is unit and assumes the complement of `m`;
anything else fails. With `α` the literals of a nogood `ε`, success means that
the clause of `ε` is a reverse-unit-propagation (RUP) consequence of the clauses
of the hints. On numbered clauses without repeated literals
(`Program.lratClause`) this is exactly the RUP check of the action-by-action
LRAT checker (`Program.rupCheck_lratClause`).

## Results

* **First-UIP nogoods are RUP** (`firstUIP_rup`): the nogood first-UIP analysis
  learns is a RUP consequence of the reasons it resolved, taken in the reverse of
  the order the analysis used them (that is, in trail order, oldest first),
  followed by the conflict nogood (`firstUIPHints`). The proof is syntactic: it
  needs nothing about the trail. On numbered clauses the checker accepts it
  (`Program.firstUIP_rupCheck`).
* **The trail refutes at a conflict** (`trail_rup`): with the decisions assumed,
  the reasons of the trail, oldest first, followed by a falsified nogood, are a
  RUP derivation. At level 0 this is the final step of a refutation, the empty
  clause (`Program.refutation_rupCheck`); above level 0 it is the RUP check of
  the nogood of the decisions (`Program.decisions_rupCheck`).
* **The checker accepts the emitted step** (`Program.lratAddition`, the action
  `rup id clause hints`). If a prefix of actions is accepted by the action
  checker and the hint identifiers name the hinted clauses, the prefix extended
  by the step is accepted, and the new identifier names the new clause
  (`check_append_rup`). A step adding the empty clause completes a refutation
  (`check_append_empty`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

open Mettapedia.GSLT.Logic

universe u

variable {A : Type u}

section RUP

variable [DecidableEq A]

/-! ## Reverse unit propagation over nogoods -/

/-- The literals of a hint, each once, that are not assumed. -/
def openOf (α ρ : List (Lit A)) : List (Lit A) := ρ.dedup.filter fun m => decide (m ∉ α)

/-- **Reverse unit propagation over nogoods.** `α` lists the literals assumed true. A hint with
no literal left open is violated, and the check succeeds; a hint with one literal `m` left open
is unit, and the complement of `m` is assumed; any other hint fails the check. -/
def rupNogood (α : List (Lit A)) : List (List (Lit A)) → Bool
  | [] => false
  | ρ :: rest =>
    match openOf α ρ with
    | [] => true
    | [m] => rupNogood (m.compl :: α) rest
    | _ :: _ :: _ => false

theorem mem_openOf {α ρ : List (Lit A)} {m : Lit A} : m ∈ openOf α ρ ↔ m ∈ ρ ∧ m ∉ α := by
  simp [openOf, List.mem_filter, List.mem_dedup]

theorem openOf_nodup (α ρ : List (Lit A)) : (openOf α ρ).Nodup := (List.nodup_dedup ρ).filter _

theorem openOf_eq_nil {α ρ : List (Lit A)} : openOf α ρ = [] ↔ ∀ m ∈ ρ, m ∈ α := by
  rw [List.eq_nil_iff_forall_not_mem]
  simp only [mem_openOf, not_and, not_not]

theorem rupNogood_cons_of_nil {α ρ : List (Lit A)} {rest : List (List (Lit A))} (h : openOf α ρ = []) :
    rupNogood α (ρ :: rest) = true := by
  simp [rupNogood, h]

theorem rupNogood_cons_of_single {α ρ : List (Lit A)} {rest : List (List (Lit A))} {m : Lit A}
    (h : openOf α ρ = [m]) : rupNogood α (ρ :: rest) = rupNogood (m.compl :: α) rest := by
  simp [rupNogood, h]

omit [DecidableEq A] in
theorem eq_nil_or_eq_singleton {l : List (Lit A)} {x : Lit A} (nodup : l.Nodup) (h : ∀ y ∈ l, y = x) :
    l = [] ∨ l = [x] := by
  rcases l with _ | ⟨y, l⟩
  · exact Or.inl rfl
  · right
    have hy := h y List.mem_cons_self
    subst hy
    rcases l with _ | ⟨z, l⟩
    · rfl
    · have hz := h z (List.mem_cons_of_mem _ List.mem_cons_self)
      subst hz
      exact absurd List.mem_cons_self (List.nodup_cons.mp nodup).1

/-- A hint all of whose literals other than `x` are assumed is violated or unit on `x`. -/
theorem rupNogood_cons_of_others {α ρ : List (Lit A)} {rest : List (List (Lit A))} {x : Lit A}
    (others : ∀ m ∈ ρ, m ≠ x → m ∈ α) (next : rupNogood (x.compl :: α) rest = true) :
    rupNogood α (ρ :: rest) = true := by
  have only : ∀ y ∈ openOf α ρ, y = x := by
    intro y hy
    rw [mem_openOf] at hy
    by_contra ne
    exact hy.2 (others y hy.1 ne)
  rcases eq_nil_or_eq_singleton (openOf_nodup α ρ) only with h | h
  · exact rupNogood_cons_of_nil h
  · rw [rupNogood_cons_of_single h]
    exact next

/-- **Replacing the last hint.** If a RUP walk ends on the hint `x`, and every walk that has
assumed `α` and the literals of `x` succeeds on `T`, then the walk with `T` in place of `x`
succeeds. -/
theorem rupNogood_append :
    ∀ (H : List (List (Lit A))) {α x : List (Lit A)} {T : List (List (Lit A))},
      rupNogood α (H ++ [x]) = true →
      (∀ β : List (Lit A), (∀ m ∈ α, m ∈ β) → (∀ m ∈ x, m ∈ β) → rupNogood β T = true) →
      rupNogood α (H ++ T) = true
  | [], α, x, T, h, tail => by
    simp only [List.nil_append] at h ⊢
    have empty : openOf α x = [] := by
      rcases hop : openOf α x with _ | ⟨m, _ | ⟨m', rest⟩⟩
      · rfl
      · simp [rupNogood, hop] at h
      · simp [rupNogood, hop] at h
    exact tail α (fun _ hm => hm) (openOf_eq_nil.mp empty)
  | ρ :: H, α, x, T, h, tail => by
    simp only [List.cons_append] at h ⊢
    rcases hop : openOf α ρ with _ | ⟨m, _ | ⟨m', rest⟩⟩
    · exact rupNogood_cons_of_nil hop
    · rw [rupNogood_cons_of_single hop] at h ⊢
      exact rupNogood_append H h fun β hα hx => tail β (fun n hn => hα n (List.mem_cons_of_mem _ hn)) hx
    · simp [rupNogood, hop] at h

/-! ## First-UIP nogoods are RUP -/

/-- **The reasons first-UIP analysis resolves**, in the order it uses them (newest entry first).
It follows `uipWalk` case by case. -/
def uipReasons : List (Lit A) → List (Entry A) → List (Nogood A)
  | _, [] => []
  | c, e :: seg =>
    if e.lit ∈ c then
      if ∃ m ∈ c, m ≠ e.lit ∧ m ∈ seg.map Entry.lit then
        match e.reason with
        | some ρ => ρ :: uipReasons (resolveOn c ρ.lits e.lit) seg
        | none => []
      else []
    else uipReasons c seg

/-- The hints of a first-UIP nogood: the resolved reasons, oldest first, then the conflict. -/
def firstUIPHints (s : State A) (δ : Nogood A) : List (Nogood A) :=
  (uipReasons δ.lits.dedup (currentLevel s.trail)).reverse ++ [δ]

theorem rupNogood_resolveOn {c x : List (Lit A)} {ρ : List (Lit A)} {e : Lit A} (hx : ∀ m ∈ x, m ∈ c)
    {β : List (Lit A)} (hβ : ∀ m ∈ resolveOn c ρ e, m ∈ β) : rupNogood β [ρ, x] = true := by
  apply rupNogood_cons_of_others (x := e.compl)
  · intro m hm ne
    exact hβ m (List.mem_dedup.mpr (List.mem_append_right _
      ((List.mem_erase_of_ne ne).mpr (List.mem_dedup.mpr hm))))
  · rw [Lit.compl_compl]
    apply rupNogood_cons_of_nil
    rw [openOf_eq_nil]
    intro m hm
    by_cases same : m = e
    · subst same
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hβ m (List.mem_dedup.mpr (List.mem_append_left _
        ((List.mem_erase_of_ne same).mpr (hx m hm)))))

/-- **The walk invariant of RUP emission.** For any final hint `x` whose literals are in the
nogood `c` the walk starts from, the result of the walk is RUP with the resolved reasons in
reverse order followed by `x`. -/
theorem rupNogood_uipWalk : ∀ (seg : List (Entry A)) (c x α : List (Lit A)),
    (∀ m ∈ x, m ∈ c) → (∀ m ∈ uipWalk c seg, m ∈ α) →
      rupNogood α ((uipReasons c seg).reverse.map Nogood.lits ++ [x]) = true
  | [], c, x, α, hx, hα => by
    simp only [uipReasons, List.reverse_nil, List.map_nil, List.nil_append]
    exact rupNogood_cons_of_nil (openOf_eq_nil.mpr fun m hm => hα m (hx m hm))
  | e :: seg, c, x, α, hx, hα => by
    have base : (∀ m ∈ c, m ∈ α) → rupNogood α (([] : List (Nogood A)).reverse.map Nogood.lits ++ [x]) = true :=
      fun hc => rupNogood_cons_of_nil (openOf_eq_nil.mpr fun m hm => hc m (hx m hm))
    by_cases he : e.lit ∈ c
    · by_cases other : ∃ m ∈ c, m ≠ e.lit ∧ m ∈ seg.map Entry.lit
      · cases hρ : e.reason with
        | none =>
          simp only [uipWalk, uipReasons, he, other, hρ, if_true] at hα ⊢
          exact base hα
        | some ρ =>
          simp only [uipWalk, uipReasons, he, other, hρ, if_true] at hα ⊢
          rw [List.reverse_cons, List.map_append, List.append_assoc, List.map_singleton,
            List.singleton_append]
          exact rupNogood_append _ (rupNogood_uipWalk seg _ _ α (fun _ hm => hm) hα)
            fun β _ hβ => rupNogood_resolveOn hx hβ
      · simp only [uipWalk, uipReasons, he, other, if_true, if_false] at hα ⊢
        exact base hα
    · simp only [uipWalk, uipReasons, he, if_false] at hα ⊢
      exact rupNogood_uipWalk seg c x α hx hα

/-- **The nogood first-UIP learns is a RUP consequence of the reasons it resolved and the
conflict**, the reasons in trail order (the reverse of the order the analysis used them).
Any assumed set containing the learned nogood succeeds. -/
theorem firstUIP_rup (s : State A) (δ : Nogood A) {α : List (Lit A)} (h : ∀ m ∈ firstUIP s δ, m ∈ α) :
    rupNogood α ((firstUIPHints s δ).map Nogood.lits) = true := by
  rw [firstUIPHints, List.map_append, List.map_singleton]
  exact rupNogood_uipWalk _ _ _ _ (fun _ hm => List.mem_dedup.mpr hm) h

theorem uipReasons_mem : ∀ {c : List (Lit A)} {seg : List (Entry A)} {ρ : Nogood A},
    ρ ∈ uipReasons c seg → ∃ e ∈ seg, e.reason = some ρ
  | _, [], _, h => by simp [uipReasons] at h
  | c, e :: seg, ρ, h => by
    by_cases he : e.lit ∈ c
    · by_cases other : ∃ m ∈ c, m ≠ e.lit ∧ m ∈ seg.map Entry.lit
      · cases hρ : e.reason with
        | none => simp only [uipReasons, he, other, hρ, if_true, List.not_mem_nil] at h
        | some ρ' =>
          simp only [uipReasons, he, other, hρ, if_true, List.mem_cons] at h
          rcases h with rfl | h
          · exact ⟨e, List.mem_cons_self, hρ⟩
          · obtain ⟨f, hf, hfρ⟩ := uipReasons_mem h
            exact ⟨f, List.mem_cons_of_mem _ hf, hfρ⟩
      · simp only [uipReasons, he, other, if_true, if_false, List.not_mem_nil] at h
    · simp only [uipReasons, he, if_false] at h
      obtain ⟨f, hf, hfρ⟩ := uipReasons_mem h
      exact ⟨f, List.mem_cons_of_mem _ hf, hfρ⟩

theorem uipWalk_mem : ∀ {c : List (Lit A)} {seg : List (Entry A)} {m : Lit A},
    m ∈ uipWalk c seg → m ∈ c ∨ ∃ ρ ∈ uipReasons c seg, m ∈ ρ.lits
  | _, [], _, h => Or.inl h
  | c, e :: seg, m, h => by
    by_cases he : e.lit ∈ c
    · by_cases other : ∃ m ∈ c, m ≠ e.lit ∧ m ∈ seg.map Entry.lit
      · cases hρ : e.reason with
        | none =>
          simp only [uipWalk, he, other, hρ, if_true] at h
          exact Or.inl h
        | some ρ =>
          simp only [uipWalk, he, other, hρ, if_true] at h
          simp only [uipReasons, he, other, hρ, if_true, List.mem_cons, exists_eq_or_imp]
          rcases uipWalk_mem h with h | ⟨ρ', hρ', hm⟩
          · rcases List.mem_append.mp (List.mem_dedup.mp h) with h | h
            · exact Or.inl (List.mem_of_mem_erase h)
            · exact Or.inr (Or.inl (List.mem_dedup.mp (List.mem_of_mem_erase h)))
          · exact Or.inr (Or.inr ⟨ρ', hρ', hm⟩)
      · simp only [uipWalk, he, other, if_true, if_false] at h
        exact Or.inl h
    · simp only [uipWalk, he, if_false] at h
      simp only [uipReasons, he, if_false]
      exact uipWalk_mem h

/-! ## The trail refutes at a conflict -/

/-- The reasons on a trail, newest first. -/
def trailReasons (t : List (Entry A)) : List (Nogood A) := t.filterMap Entry.reason

/-- **A conflict is RUP from the trail.** With the decisions of a justified trail assumed, its
reasons oldest first, followed by any hint whose literals are assumed or on the trail, form a
RUP walk. -/
theorem trail_rup : ∀ (t : List (Entry A)), Justified t → ∀ (x α : List (Lit A)),
    (∀ e ∈ t, e.reason = none → e.lit ∈ α) → (∀ m ∈ x, m ∈ α ∨ m ∈ t.map Entry.lit) →
      rupNogood α ((trailReasons t).reverse.map Nogood.lits ++ [x]) = true
  | [], _, x, α, _, hx => by
    simp only [trailReasons, List.filterMap_nil, List.reverse_nil, List.map_nil, List.nil_append]
    apply rupNogood_cons_of_nil
    rw [openOf_eq_nil]
    intro m hm
    rcases hx m hm with h | h
    · exact h
    · simp at h
  | e :: t, just, x, α, decisions, hx => by
    cases hρ : e.reason with
    | none =>
      have reasons : trailReasons (e :: t) = trailReasons t := by
        simp [trailReasons, hρ]
      rw [reasons]
      refine trail_rup t just.tail x α (fun f hf => decisions f (List.mem_cons_of_mem _ hf)) ?_
      intro m hm
      rcases hx m hm with h | h
      · exact Or.inl h
      · rw [List.map_cons, List.mem_cons] at h
        rcases h with rfl | h
        · exact Or.inl (decisions e List.mem_cons_self hρ)
        · exact Or.inr h
    | some ρ =>
      have reasons : trailReasons (e :: t) = ρ :: trailReasons t := by
        simp [trailReasons, hρ]
      obtain ⟨-, rest⟩ := just.reason_spec hρ
      rw [reasons, List.reverse_cons, List.map_append, List.append_assoc, List.map_singleton,
        List.singleton_append]
      refine rupNogood_append _ (trail_rup t just.tail (t.map Entry.lit) α
        (fun f hf => decisions f (List.mem_cons_of_mem _ hf)) fun m hm => Or.inr hm) ?_
      intro β hα ht
      apply rupNogood_cons_of_others (x := e.lit.compl) (fun m hm ne => ht m (rest m hm ne))
      rw [Lit.compl_compl]
      apply rupNogood_cons_of_nil
      rw [openOf_eq_nil]
      intro m hm
      rcases hx m hm with h | h
      · exact List.mem_cons_of_mem _ (hα m h)
      · rw [List.map_cons, List.mem_cons] at h
        rcases h with rfl | h
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ht m h)

omit [DecidableEq A] in
theorem trailReasons_mem {t : List (Entry A)} {ρ : Nogood A} (h : ρ ∈ trailReasons t) :
    ∃ e ∈ t, e.reason = some ρ := by
  obtain ⟨e, he, hρ⟩ := List.mem_filterMap.mp h
  exact ⟨e, he, hρ⟩

/-- The hints of a refutation at a conflict: the reasons of the trail, oldest first, then the
falsified nogood. -/
def refutationHints (s : State A) (δ : Nogood A) : List (Nogood A) := (trailReasons s.trail).reverse ++ [δ]

omit [DecidableEq A] in
theorem no_decision_of_levelOf_eq_zero {t : List (Entry A)} (h : levelOf t = 0) :
    ∀ e ∈ t, e.reason = none → False := by
  intro e he decision
  have : e ∈ t.filter fun e => e.reason.isNone := List.mem_filter.mpr ⟨he, by simp [decision]⟩
  rw [levelOf, List.length_eq_zero_iff] at h
  rw [h] at this
  exact List.not_mem_nil this

/-- **At level 0 a falsified nogood refutes by RUP from nothing.** -/
theorem refutation_rup {s : State A} (just : Justified s.trail) (ground : levelOf s.trail = 0) {δ : Nogood A}
    (falsified : s.Falsifies δ) : rupNogood [] ((refutationHints s δ).map Nogood.lits) = true := by
  rw [refutationHints, List.map_append, List.map_singleton]
  exact trail_rup _ just _ _ (fun e he decision => (no_decision_of_levelOf_eq_zero ground e he decision).elim)
    fun m hm => Or.inr (falsified m hm)

/-- **The nogood of the decisions is RUP** from the trail's reasons and a falsified nogood. -/
theorem decisions_rup {s : State A} (just : Justified s.trail) {δ : Nogood A} (falsified : s.Falsifies δ)
    {α : List (Lit A)} (h : ∀ m ∈ Program.decisionLits s.trail, m ∈ α) :
    rupNogood α ((refutationHints s δ).map Nogood.lits) = true := by
  rw [refutationHints, List.map_append, List.map_singleton]
  refine trail_rup _ just _ _ (fun e he decision => h _ ?_) fun m hm => Or.inr (falsified m hm)
  exact List.mem_map_of_mem (List.mem_filter.mpr ⟨he, by simp [decision]⟩)

/-! ## Numbered clauses -/

namespace Program

variable (P : Program A)

/-- A solver literal as a native literal over its variable number. -/
def nativeLit (l : Lit A) : PropositionalFormula.Literal := CNF.Literal.toLRAT ⟨P.index l.var, l.sign⟩

/-- **The emitted clause of a nogood**: its negated literals, numbered, each once. -/
def lratClause (lits : List (Lit A)) : PropositionalFormula.Clause := lits.dedup.map fun l => P.nativeLit l.compl

theorem nativeLit_compl (l : Lit A) : (P.nativeLit l).complement = P.nativeLit l.compl := by
  obtain ⟨x, b⟩ := l
  cases b <;> rfl

theorem nativeLit_injOn {l m : Lit A} (hl : P.IsVar l.var) (hm : P.IsVar m.var)
    (h : P.nativeLit l = P.nativeLit m) : l = m := by
  obtain ⟨x, b⟩ := l
  obtain ⟨y, c⟩ := m
  have same := congrArg CNF.Literal.ofLRAT h
  simp only [nativeLit, CNF.Literal.ofLRAT_toLRAT, CNF.Literal.mk.injEq] at same
  obtain ⟨index, rfl⟩ := same
  obtain rfl := P.index_injOn (x := x) (y := y) hl hm index
  rfl

@[simp] theorem lratClause_nil : P.lratClause [] = [] := rfl

theorem openLiterals_lratClause {α ρ : List (Lit A)} (hα : ∀ l ∈ α, P.IsVar l.var)
    (hρ : ∀ l ∈ ρ, P.IsVar l.var) :
    PropositionalLRATActions.openLiterals (α.map P.nativeLit) (P.lratClause ρ) =
      (openOf α ρ).map fun l => P.nativeLit l.compl := by
  unfold PropositionalLRATActions.openLiterals lratClause openOf
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro m hm
  simp only [Function.comp, nativeLit_compl, Lit.compl_compl]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, List.mem_map, not_exists, not_and]
  constructor
  · intro h member
    exact h m member rfl
  · intro h l hl same
    exact h (P.nativeLit_injOn (hα l hl) (hρ m (List.mem_dedup.mp hm)) same ▸ hl)

/-- **The native RUP walk is the nogood RUP walk** on numbered clauses of program variables. -/
theorem propagate_lratClause : ∀ (H : List (List (Lit A))) (α : List (Lit A)),
    (∀ l ∈ α, P.IsVar l.var) → (∀ ρ ∈ H, ∀ l ∈ ρ, P.IsVar l.var) →
      PropositionalLRATActions.propagate (α.map P.nativeLit) (H.map P.lratClause) = rupNogood α H
  | [], _, _, _ => rfl
  | ρ :: H, α, hα, hH => by
    have hρ := hH ρ List.mem_cons_self
    simp only [List.map_cons, PropositionalLRATActions.propagate, P.openLiterals_lratClause hα hρ, rupNogood]
    rcases hop : openOf α ρ with _ | ⟨m, _ | ⟨m', rest⟩⟩
    · rfl
    · have hm : m ∈ ρ := (mem_openOf.mp (hop ▸ List.mem_cons_self)).1
      simp only [List.map_cons, List.map_nil]
      have := propagate_lratClause H (m.compl :: α) (by
        rintro l (_ | ⟨_, hl⟩)
        · exact hρ m hm
        · exact hα l hl) fun ρ' h => hH ρ' (List.mem_cons_of_mem _ h)
      rw [List.map_cons] at this
      exact this
    · rfl

/-- **The checker's RUP test is the nogood RUP walk**: on numbered clauses of program variables,
`rupCheck` accepts the clause of `ε` with the clauses of the hints exactly when `rupNogood` does. -/
theorem rupCheck_lratClause {H : List (List (Lit A))} {ε : List (Lit A)} (hε : ∀ l ∈ ε, P.IsVar l.var)
    (hH : ∀ ρ ∈ H, ∀ l ∈ ρ, P.IsVar l.var) :
    PropositionalLRATActions.rupCheck (H.map P.lratClause) (P.lratClause ε) = rupNogood ε.dedup H := by
  unfold PropositionalLRATActions.rupCheck
  have assumed : (P.lratClause ε).map PropositionalFormula.Literal.complement = ε.dedup.map P.nativeLit := by
    simp only [lratClause, List.map_map]
    apply List.map_congr_left
    intro l _
    simp [nativeLit_compl]
  rw [assumed]
  exact P.propagate_lratClause H _ (fun l hl => hε l (List.mem_dedup.mp hl)) hH

/-- The literals of the reasons on a justified trail of program variables are program variables. -/
theorem reason_vars : ∀ {t : List (Entry A)}, Justified t → (∀ e ∈ t, P.IsVar e.lit.var) →
    ∀ e ∈ t, ∀ ρ, e.reason = some ρ → ∀ l ∈ ρ.lits, P.IsVar l.var
  | [], _, _, _, he, _, _, _, _ => absurd he List.not_mem_nil
  | f :: t, just, vars, e, he, ρ, hρ, l, hl => by
    rcases List.mem_cons.mp he with rfl | he
    · obtain ⟨-, rest⟩ := just.reason_spec hρ
      by_cases same : l = e.lit.compl
      · subst same
        exact vars e List.mem_cons_self
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (rest l hl same)
        exact vars g (List.mem_cons_of_mem _ hg)
    · exact reason_vars just.tail (fun g hg => vars g (List.mem_cons_of_mem _ hg)) e he ρ hρ l hl

theorem firstUIPHints_vars {s : State A} (inv : P.Inv s) (just : Justified s.trail) {δ : Nogood A}
    (falsified : s.Falsifies δ) : ∀ ρ ∈ firstUIPHints s δ, ∀ l ∈ ρ.lits, P.IsVar l.var := by
  intro ρ hρ l hl
  rcases List.mem_append.mp hρ with hρ | hρ
  · obtain ⟨e, he, hreason⟩ := uipReasons_mem (List.mem_reverse.mp hρ)
    have he' : e ∈ s.trail := by
      rw [← currentLevel_append_belowLevel s.trail]
      exact List.mem_append_left _ he
    exact P.reason_vars just inv.vars e he' ρ hreason l hl
  · rw [List.mem_singleton] at hρ
    subst hρ
    exact P.mem_lits_isVar inv (falsified l hl)

theorem firstUIP_vars {s : State A} (inv : P.Inv s) (just : Justified s.trail) {δ : Nogood A}
    (falsified : s.Falsifies δ) : ∀ l ∈ firstUIP s δ, P.IsVar l.var := by
  intro l hl
  rcases uipWalk_mem hl with h | ⟨ρ, hρ, hm⟩
  · exact P.mem_lits_isVar inv (falsified l (List.mem_dedup.mp h))
  · exact P.firstUIPHints_vars inv just falsified ρ
      (List.mem_append_left _ (List.mem_reverse.mpr hρ)) l hm

/-- **The checker accepts the first-UIP nogood**: on numbered clauses, the RUP check of the
action-by-action LRAT checker accepts the clause of the learned nogood, with the clauses of the
resolved reasons, oldest first, and of the conflict as premises. -/
theorem firstUIP_rupCheck {s : State A} (inv : P.Inv s) (just : Justified s.trail) {δ : Nogood A}
    (falsified : s.Falsifies δ) :
    PropositionalLRATActions.rupCheck ((firstUIPHints s δ).map fun ρ => P.lratClause ρ.lits)
      (P.lratClause (firstUIP s δ)) = true := by
  have hints := P.firstUIPHints_vars inv just falsified
  rw [show (firstUIPHints s δ).map (fun ρ => P.lratClause ρ.lits) =
      ((firstUIPHints s δ).map Nogood.lits).map P.lratClause by rw [List.map_map]; rfl,
    P.rupCheck_lratClause (P.firstUIP_vars inv just falsified) (by
      intro ρ hρ l hl
      obtain ⟨ρ', hρ', rfl⟩ := List.mem_map.mp hρ
      exact hints ρ' hρ' l hl)]
  exact firstUIP_rup s δ fun m hm => List.mem_dedup.mpr hm

theorem refutationHints_vars {s : State A} (inv : P.Inv s) (just : Justified s.trail) {δ : Nogood A}
    (falsified : s.Falsifies δ) : ∀ ρ ∈ refutationHints s δ, ∀ l ∈ ρ.lits, P.IsVar l.var := by
  intro ρ hρ l hl
  rcases List.mem_append.mp hρ with hρ | hρ
  · obtain ⟨e, he, hreason⟩ := trailReasons_mem (List.mem_reverse.mp hρ)
    exact P.reason_vars just inv.vars e he ρ hreason l hl
  · rw [List.mem_singleton] at hρ
    subst hρ
    exact P.mem_lits_isVar inv (falsified l hl)

theorem rupCheck_hints {Γ : List (Nogood A)} {ε : List (Lit A)} (hε : ∀ l ∈ ε, P.IsVar l.var)
    (hΓ : ∀ ρ ∈ Γ, ∀ l ∈ ρ.lits, P.IsVar l.var) :
    PropositionalLRATActions.rupCheck (Γ.map fun ρ => P.lratClause ρ.lits) (P.lratClause ε) =
      rupNogood ε.dedup (Γ.map Nogood.lits) := by
  rw [show Γ.map (fun ρ => P.lratClause ρ.lits) = (Γ.map Nogood.lits).map P.lratClause by
    rw [List.map_map]; rfl]
  apply P.rupCheck_lratClause hε
  intro ρ hρ l hl
  obtain ⟨ρ', hρ', rfl⟩ := List.mem_map.mp hρ
  exact hΓ ρ' hρ' l hl

/-- **The final step of a refutation**: at a level-0 conflict the checker accepts the empty
clause, with the trail's reasons, oldest first, and the conflict as premises. -/
theorem refutation_rupCheck {s : State A} (inv : P.Inv s) (just : Justified s.trail)
    (ground : levelOf s.trail = 0) {δ : Nogood A} (falsified : s.Falsifies δ) :
    PropositionalLRATActions.rupCheck ((refutationHints s δ).map fun ρ => P.lratClause ρ.lits) [] = true := by
  rw [← P.lratClause_nil, P.rupCheck_hints (by simp) (P.refutationHints_vars inv just falsified)]
  exact refutation_rup just ground falsified

/-- At a conflict above level 0 the checker accepts the nogood of the decisions. -/
theorem decisions_rupCheck {s : State A} (inv : P.Inv s) (just : Justified s.trail) {δ : Nogood A}
    (falsified : s.Falsifies δ) :
    PropositionalLRATActions.rupCheck ((refutationHints s δ).map fun ρ => P.lratClause ρ.lits)
      (P.lratClause (decisionLits s.trail)) = true := by
  rw [P.rupCheck_hints (fun l hl => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hl
      exact inv.vars e (List.mem_filter.mp he).1) (P.refutationHints_vars inv just falsified)]
  exact decisions_rup just falsified fun m hm => List.mem_dedup.mpr hm

/-- **The emitted LRAT addition**: clause identifier, the clause of the nogood, hint identifiers. -/
def lratAddition (id : ℕ) (lits : List (Lit A)) (hints : List ℕ) : PropositionalLRATActions.Action :=
  .rup id (P.lratClause lits) hints

end Program

end RUP

/-! ## The action checker accepts emitted steps -/

namespace LRATEmission

open PropositionalLRATActions PropositionalFormula DerivationGraph

/-- In an accepted prefix, with retained state `R` and replay cache `cache`, the identifier `id`
names the clause `c`. -/
def Names (R : Retained) (cache : Array Clause) (id : ℕ) (c : Clause) : Prop :=
  ∃ p, lookupId R.live id = some p ∧ cache[p]? = some c

theorem compile_append (F : CNF) (actions : List Action) (a : Action) :
    compile F (actions ++ [a]) = (compile F actions).bind fun R => compileStep R a := by
  unfold compile
  rw [List.foldlM_append]
  cases List.foldlM compileStep (start F) actions with
  | none => rfl
  | some R =>
    simp only [List.foldlM_cons, List.foldlM_nil, Option.bind_some]
    cases h : compileStep R a <;> simp [h]

theorem replayFrom_size {formula : CNF} :
    ∀ {cache result : Array Clause} {nodes : List (Node Clause ActionCode ℕ)},
      replayFrom (interface formula) cache nodes = some result → result.size = cache.size + nodes.length
  | cache, result, [], h => by
    cases Option.some.inj h
    simp
  | cache, result, node :: rest, h => by
    cases first : node.replay (interface formula) cache with
    | none => simp [replayFrom, first] at h
    | some next =>
      have remaining : replayFrom (interface formula) next rest = some result := by
        simpa [replayFrom, first] using h
      rw [replayFrom_size remaining, node.replay_eq_push (interface formula) first, Array.size_push,
        List.length_cons]
      omega

theorem lookupId_cons_self (live : List (ℕ × ℕ)) (id p : ℕ) : lookupId ((id, p) :: live) id = some p := by
  simp [lookupId]

theorem lookupId_cons_of_ne (live : List (ℕ × ℕ)) {id i : ℕ} (p : ℕ) (ne : i ≠ id) :
    lookupId ((id, p) :: live) i = lookupId live i := by
  have : (id == i) = false := by simpa using Ne.symm ne
  simp [lookupId, this]

theorem names_mapM {R : Retained} {cache : Array Clause} :
    ∀ {hints : List ℕ} {premises : List Clause}, List.Forall₂ (Names R cache) hints premises →
      ∃ parents, hints.mapM (lookupId R.live) = some parents ∧ lookupPremises cache parents = some premises
  | [], [], .nil => ⟨[], rfl, rfl⟩
  | h :: hints, c :: premises, .cons ⟨p, hp, hc⟩ rest => by
    obtain ⟨parents, hparents, hlookup⟩ := names_mapM rest
    refine ⟨p :: parents, ?_, ?_⟩
    · simp [List.mapM_cons, hp, hparents]
    · simp [lookupPremises, hc, hlookup]

/-- **The action checker accepts an emitted RUP step.** If the prefix `actions` compiles and
replays, the step's identifier is fresh, its hint identifiers name the premise clauses, and the
RUP test accepts, then the extended stream compiles and replays, the new identifier names the
new clause, and every earlier name is kept. -/
theorem check_append_rup {F : CNF} {actions : List Action} {R : Retained} {cache : Array Clause}
    (compiled : compile F actions = some R) (replayed : replay (interface F) R.nodes = some cache)
    {id : ℕ} {clause : Clause} {hints : List ℕ} {premises : List Clause}
    (fresh : lookupId R.live id = none) (named : List.Forall₂ (Names R cache) hints premises)
    (rup : rupCheck premises clause = true) :
    ∃ R', compile F (actions ++ [.rup id clause hints]) = some R' ∧
      replay (interface F) R'.nodes = some (cache.push clause) ∧ Names R' (cache.push clause) id clause ∧
      ∀ i c, Names R cache i c → Names R' (cache.push clause) i c := by
  obtain ⟨parents, hparents, hlookup⟩ := names_mapM named
  have size : cache.size = R.nodes.length := by
    simpa using replayFrom_size replayed
  refine ⟨⟨(id, R.nodes.length) :: R.live, R.nodes ++ [⟨clause, .rup, parents, id⟩]⟩, ?_, ?_, ?_, ?_⟩
  · rw [compile_append, compiled]
    simp [compileStep, fresh, hparents]
  · have node : (⟨clause, .rup, parents, id⟩ : Node Clause (interface F).W ℕ).replay (interface F) cache =
        some (cache.push clause) :=
      (Node.replay_eq_some_iff _ _ _ _).mpr ⟨premises, hlookup, rup, rfl⟩
    have last : replayFrom (interface F) cache [(⟨clause, .rup, parents, id⟩ : Node Clause (interface F).W ℕ)] =
        some (cache.push clause) := by
      simp [replayFrom, node]
    exact replayFrom_append (interface F) replayed last
  · refine ⟨R.nodes.length, lookupId_cons_self _ _ _, ?_⟩
    rw [Array.getElem?_push, if_pos size.symm]
  · rintro i c ⟨p, hp, hc⟩
    have ne : i ≠ id := by
      rintro rfl
      rw [fresh] at hp
      cases hp
    refine ⟨p, by rw [lookupId_cons_of_ne _ _ ne, hp], ?_⟩
    have inside : p < cache.size := (Array.getElem?_eq_some_iff.mp hc).1
    rw [Array.getElem?_push, if_neg (Nat.ne_of_lt inside)]
    exact hc

/-- **A step adding the empty clause completes a refutation** the action checker accepts. -/
theorem check_append_empty {F : CNF} {actions : List Action} {R : Retained} {cache : Array Clause}
    (compiled : compile F actions = some R) (replayed : replay (interface F) R.nodes = some cache)
    {id : ℕ} {hints : List ℕ} {premises : List Clause}
    (fresh : lookupId R.live id = none) (named : List.Forall₂ (Names R cache) hints premises)
    (rup : rupCheck premises [] = true) :
    check F (actions ++ [.rup id [] hints]) = true := by
  obtain ⟨R', compiled', replayed', -, -⟩ := check_append_rup compiled replayed fresh named rup
  unfold check
  rw [compiled']
  simp only [replayed']
  simp

end LRATEmission

end Mettapedia.Logic.ASP
