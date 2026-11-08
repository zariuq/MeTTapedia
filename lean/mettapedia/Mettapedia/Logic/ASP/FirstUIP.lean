import Mettapedia.Logic.ASP.Solver

/-!
# First-UIP conflict analysis

The solver transition system (`Solver`) lets `learn` and `backjump` use any
entailed nogood. This module defines the standard choice, first-UIP conflict
analysis, over the solver's trail, and proves that it produces an asserting
nogood that is `Derived`, hence entailed.

## Justified trails

`Justified` records how propagated literals were pushed: the reason of a
propagated literal contains its complement, and every other literal of the
reason lies below it on the trail. Every reachable state has a justified trail
(`reachable_justified`).

## The analysis

* The current decision level of a trail (`currentLevel`) is its entries down to
  and including the newest decision; the rest lies below (`belowLevel`).
* `uipWalk` makes one pass over the current level, newest entry first. When the
  entry's literal is in the nogood and another literal of the nogood lies further
  down the level, it resolves the nogood with the entry's reason
  (`resolveOn`, which keeps the nogood free of repeated literals); when the
  entry's literal is the only one of the level left, it stops.
  The pass is structurally recursive on the level, so it terminates after at most
  one resolution per entry.
* `firstUIP s δ` analyses the conflict nogood `δ`.

## Results

* `firstUIP_derived`: the result is `Derived` from the database and the trail
  reasons by resolution and weakening, hence entailed (`firstUIP_entailed`).
* `firstUIP_uip`: if the conflict nogood is falsified and has a literal at the
  current level, the result has exactly one literal `u` at the current level, the
  first unique implication point, and every other literal lies below.
* `assertionLevel` is the highest level among the other literals, and
  `cutTo j t` the trail backjumped to level `j` (`levelOf_cutTo`).
* `firstUIP_unit_after_backjump`: after backjumping to the assertion level, the
  result is unit on `u`.
* `firstUIP_backjump`: the backjump to the assertion level, pushing the
  complement of `u` with the result as its reason, is a step of the solver.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

universe u

variable {A : Type u}

/-! ## Justified trails -/

/-- A trail is justified when the reason of each propagated literal contains its complement and
the rest of the reason lies below it. -/
inductive Justified : List (Entry A) → Prop
  | nil : Justified []
  | decision {e : Entry A} {t : List (Entry A)} : e.reason = none → Justified t → Justified (e :: t)
  | implied {e : Entry A} {t : List (Entry A)} {ρ : Nogood A} : e.reason = some ρ → e.lit.compl ∈ ρ.lits →
      (∀ m ∈ ρ.lits, m ≠ e.lit.compl → m ∈ t.map Entry.lit) → Justified t → Justified (e :: t)

namespace Justified

theorem tail {e : Entry A} {t : List (Entry A)} (h : Justified (e :: t)) : Justified t := by
  cases h with
  | decision _ h => exact h
  | implied _ _ _ h => exact h

theorem append_right {older : List (Entry A)} : ∀ {newer : List (Entry A)}, Justified (newer ++ older) →
    Justified older
  | [], h => h
  | _ :: _, h => append_right h.tail

theorem reason_spec {e : Entry A} {t : List (Entry A)} (h : Justified (e :: t)) {ρ : Nogood A}
    (hρ : e.reason = some ρ) : e.lit.compl ∈ ρ.lits ∧ ∀ m ∈ ρ.lits, m ≠ e.lit.compl → m ∈ t.map Entry.lit := by
  cases h with
  | decision none _ => rw [none] at hρ; cases hρ
  | implied some mem rest _ =>
    rw [some] at hρ
    cases hρ
    exact ⟨mem, rest⟩

end Justified

section Analysis

variable [DecidableEq A]

namespace Program

variable (P : Program A)

/-- **Every step keeps the trail justified.** -/
theorem Step.justified {s s' : State A} (step : P.Step (.running s) (.running s')) (h : Justified s.trail) :
    Justified s'.trail := by
  cases step with
  | propagate _ unit _ =>
    obtain ⟨member, rest, _⟩ := unit
    exact .implied rfl (by rw [Lit.compl_compl]; exact member)
      (fun m hm ne => rest m hm (by rwa [Lit.compl_compl] at ne)) h
  | decide _ _ => exact .decision rfl h
  | backjump _ _ split _ _ member rest _ _ =>
    rw [split] at h
    exact .implied rfl (by rw [Lit.compl_compl]; exact member)
      (fun m hm ne => rest m hm (by rwa [Lit.compl_compl] at ne)) h.append_right.tail
  | learn _ _ _ => exact h
  | restart split _ _ =>
    rw [split] at h
    exact h.append_right

/-- **Every reachable state has a justified trail.** -/
theorem reachable_justified {s : State A} (h : P.Reachable (.running s)) : Justified s.trail := by
  suffices ∀ c, P.Reachable c → ∀ s, c = .running s → Justified s.trail from this _ h s rfl
  intro c reach
  induction reach with
  | refl =>
    intro s same
    cases same
    exact .nil
  | @tail b c _ step ih =>
    intro s same
    subst same
    cases b with
    | done r => exact absurd step P.done_no_step
    | running s₀ => exact Step.justified P step (ih s₀ rfl)

end Program

/-! ## Decision levels -/

omit [DecidableEq A] in
theorem levelOf_cons (e : Entry A) (t : List (Entry A)) :
    levelOf (e :: t) = if e.reason = none then levelOf t + 1 else levelOf t := by
  unfold levelOf
  rw [List.filter_cons]
  by_cases h : e.reason = none <;> simp [h]

omit [DecidableEq A] in
theorem levelOf_append (x y : List (Entry A)) : levelOf (x ++ y) = levelOf x + levelOf y := by
  simp [levelOf, List.filter_append]

omit [DecidableEq A] in
theorem levelOf_le_cons (e : Entry A) (t : List (Entry A)) : levelOf t ≤ levelOf (e :: t) := by
  rw [levelOf_cons]
  split <;> omega

omit [DecidableEq A] in
theorem levelOf_eq_zero_of_propagated {t : List (Entry A)} (h : ∀ e ∈ t, e.reason ≠ none) : levelOf t = 0 := by
  rw [levelOf, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro e he
  simpa using h e he

/-- The current decision level: the entries down to and including the newest decision. -/
def currentLevel : List (Entry A) → List (Entry A)
  | [] => []
  | e :: t => if e.reason.isNone then [e] else e :: currentLevel t

/-- The entries below the newest decision. -/
def belowLevel : List (Entry A) → List (Entry A)
  | [] => []
  | e :: t => if e.reason.isNone then t else belowLevel t

omit [DecidableEq A] in
theorem currentLevel_append_belowLevel : ∀ t : List (Entry A), currentLevel t ++ belowLevel t = t
  | [] => rfl
  | e :: t => by
    unfold currentLevel belowLevel
    split
    · rfl
    · rw [List.cons_append, currentLevel_append_belowLevel t]

omit [DecidableEq A] in
/-- Only the last entry of the current level is a decision. -/
theorem currentLevel_dropLast : ∀ (t : List (Entry A)), ∀ e ∈ (currentLevel t).dropLast, e.reason ≠ none
  | [], _, he => by simp [currentLevel] at he
  | f :: t, e, he => by
    unfold currentLevel at he
    split at he
    · simp at he
    · rename_i propagated
      by_cases empty : currentLevel t = []
      · rw [empty] at he
        simp at he
      · rw [List.dropLast_cons_of_ne_nil empty] at he
        rcases List.mem_cons.mp he with rfl | he
        · simpa using propagated
        · exact currentLevel_dropLast t e he

omit [DecidableEq A] in
theorem levelOf_belowLevel : ∀ {t : List (Entry A)}, levelOf t ≠ 0 → levelOf t = levelOf (belowLevel t) + 1
  | [], h => absurd rfl h
  | e :: t, h => by
    unfold belowLevel
    rw [levelOf_cons] at h ⊢
    by_cases decision : e.reason = none
    · simp [decision]
    · simp only [decision, if_false] at h ⊢
      simp only [Option.isNone_iff_eq_none, decision, if_false]
      exact levelOf_belowLevel h

/-! ## Backjumping to a level -/

/-- The trail backjumped to level `j`: its longest suffix of level at most `j`. -/
def cutTo (j : ℕ) : List (Entry A) → List (Entry A)
  | [] => []
  | e :: t => if levelOf (e :: t) ≤ j then e :: t else cutTo j t

omit [DecidableEq A] in
theorem cutTo_of_lt {j : ℕ} {rest : List (Entry A)} (h : j < levelOf rest) :
    ∀ pre : List (Entry A), cutTo j (pre ++ rest) = cutTo j rest
  | [] => rfl
  | e :: pre => by
    have : j < levelOf (e :: (pre ++ rest)) := by
      have := levelOf_le_cons e (pre ++ rest)
      rw [levelOf_append] at this
      omega
    rw [List.cons_append, cutTo, if_neg (by omega), cutTo_of_lt h pre]

omit [DecidableEq A] in
theorem cutTo_of_le {j : ℕ} {rest : List (Entry A)} (h : levelOf rest ≤ j) :
    ∀ pre : List (Entry A), ∃ pre', cutTo j (pre ++ rest) = pre' ++ rest
  | [] => by
    cases rest with
    | nil => exact ⟨[], rfl⟩
    | cons e t => exact ⟨[], by rw [List.nil_append, cutTo, if_pos h]⟩
  | e :: pre => by
    rw [List.cons_append, cutTo]
    split
    · exact ⟨e :: pre, rfl⟩
    · exact cutTo_of_le h pre

omit [DecidableEq A] in
theorem cutTo_suffix (j : ℕ) : ∀ t : List (Entry A), ∃ pre, t = pre ++ cutTo j t
  | [] => ⟨[], rfl⟩
  | e :: t => by
    rw [cutTo]
    split
    · exact ⟨[], rfl⟩
    · obtain ⟨pre, h⟩ := cutTo_suffix j t
      exact ⟨e :: pre, by rw [List.cons_append, ← h]⟩

omit [DecidableEq A] in
/-- The backjumped trail has exactly the target level. -/
theorem levelOf_cutTo {j : ℕ} : ∀ {t : List (Entry A)}, j ≤ levelOf t → levelOf (cutTo j t) = j
  | [], h => by simp [levelOf] at h; simp [cutTo, levelOf, h]
  | e :: t, h => by
    rw [cutTo]
    split
    · omega
    · rename_i above
      apply levelOf_cutTo
      rw [levelOf_cons] at above
      split at above <;> omega

omit [DecidableEq A] in
/-- Below the current level, the entry just above the backjumped trail is a decision. -/
theorem cutTo_split {j : ℕ} : ∀ {t : List (Entry A)}, j < levelOf t →
    ∃ pre d, t = pre ++ d :: cutTo j t ∧ d.reason = none
  | [], h => by simp [levelOf] at h
  | e :: t, h => by
    have skip : cutTo j (e :: t) = cutTo j t := by rw [cutTo, if_neg (by omega)]
    rw [skip]
    by_cases below : j < levelOf t
    · obtain ⟨pre, d, split, decision⟩ := cutTo_split below
      exact ⟨e :: pre, d, by rw [List.cons_append, ← split], decision⟩
    · have whole : cutTo j t = t := by
        cases t with
        | nil => rfl
        | cons f t => rw [cutTo, if_pos (by omega)]
      rw [levelOf_cons] at h
      by_cases decision : e.reason = none
      · exact ⟨[], e, by rw [whole]; rfl, decision⟩
      · rw [if_neg decision] at h
        omega

/-- The level of a literal on a trail: the level of the suffix starting at its newest entry. -/
def litLevel (m : Lit A) : List (Entry A) → ℕ
  | [] => 0
  | e :: t => if e.lit = m then levelOf (e :: t) else litLevel m t

theorem litLevel_append_cons {m : Lit A} {e : Entry A} {post : List (Entry A)} (same : e.lit = m) :
    ∀ {pre : List (Entry A)}, m ∉ pre.map Entry.lit → litLevel m (pre ++ e :: post) = levelOf (e :: post)
  | [], _ => by rw [List.nil_append, litLevel, if_pos same]
  | f :: pre, fresh => by
    rw [List.map_cons, List.mem_cons, not_or] at fresh
    rw [List.cons_append, litLevel, if_neg (Ne.symm fresh.1), litLevel_append_cons same fresh.2]

/-- The assertion level of `r` with respect to `u`: the highest level of its other literals. -/
def assertionLevel (t : List (Entry A)) (r : List (Lit A)) (u : Lit A) : ℕ :=
  ((r.filter (· ≠ u)).map fun m => litLevel m t).foldr max 0

omit [DecidableEq A] in
theorem le_foldr_max {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons y l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

omit [DecidableEq A] in
theorem foldr_max_le {l : List ℕ} {b : ℕ} (h : ∀ x ∈ l, x ≤ b) : l.foldr max 0 ≤ b := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons y l ih => exact max_le (h y List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem litLevel_le_assertionLevel {t : List (Entry A)} {r : List (Lit A)} {u m : Lit A} (hm : m ∈ r)
    (ne : m ≠ u) : litLevel m t ≤ assertionLevel t r u :=
  le_foldr_max (List.mem_map_of_mem (List.mem_filter.mpr ⟨hm, by simpa using ne⟩))

/-! ## The analysis -/

/-- Resolve `c` with the reason `ρ` on the literal `m`, keeping no repeated literals. -/
def resolveOn (c ρ : List (Lit A)) (m : Lit A) : List (Lit A) := (c.erase m ++ ρ.dedup.erase m.compl).dedup

/-- **First-UIP analysis over one decision level**, newest entry first. -/
def uipWalk : List (Lit A) → List (Entry A) → List (Lit A)
  | c, [] => c
  | c, e :: seg =>
    if e.lit ∈ c then
      if ∃ m ∈ c, m ≠ e.lit ∧ m ∈ seg.map Entry.lit then
        match e.reason with
        | some ρ => uipWalk (resolveOn c ρ.lits e.lit) seg
        | none => c
      else c
    else uipWalk c seg

/-- **First-UIP conflict analysis** of the conflict nogood `δ`. -/
def firstUIP (s : State A) (δ : Nogood A) : List (Lit A) := uipWalk δ.lits.dedup (currentLevel s.trail)

namespace Program

variable (P : Program A)

theorem derived_resolveOn {s : State A} {c : List (Lit A)} {e : Entry A} {ρ : Nogood A}
    (hc : P.Derived s c) (he : e ∈ s.trail) (hρ : e.reason = some ρ) :
    P.Derived s (resolveOn c ρ.lits e.lit) :=
  .weaken (.resolve e.lit hc (.weaken (.reason he hρ) (List.subset_dedup _))) (List.subset_dedup _)

theorem derived_uipWalk {s : State A} : ∀ {seg : List (Entry A)}, (∀ e ∈ seg, e ∈ s.trail) →
    ∀ {c : List (Lit A)}, P.Derived s c → P.Derived s (uipWalk c seg)
  | [], _, _, hc => hc
  | e :: seg, within, c, hc => by
    have rest : ∀ f ∈ seg, f ∈ s.trail := fun f hf => within f (List.mem_cons_of_mem _ hf)
    unfold uipWalk
    split
    · split
      · split
        · rename_i ρ hρ
          exact derived_uipWalk rest (P.derived_resolveOn hc (within e List.mem_cons_self) hρ)
        · exact hc
      · exact hc
    · exact derived_uipWalk rest hc

/-- **The result of first-UIP analysis is derived** by resolution from the conflict nogood and
the reasons on the trail. -/
theorem firstUIP_derived {s : State A} {δ : Nogood A} (database : P.InDatabase s δ) :
    P.Derived s (firstUIP s δ) := by
  refine P.derived_uipWalk (fun e he => ?_) (.weaken (.database database) (List.subset_dedup _))
  rw [← currentLevel_append_belowLevel s.trail]
  exact List.mem_append_left _ he

theorem firstUIP_entailed {s : State A} (inv : P.Inv s) {δ : Nogood A} (database : P.InDatabase s δ) :
    P.Entailed (firstUIP s δ) :=
  (P.firstUIP_derived database).entailed P inv

end Program

omit [DecidableEq A] in
theorem dropLast_tail_subset (e : Entry A) (seg : List (Entry A)) : ∀ f ∈ seg.dropLast, f ∈ (e :: seg).dropLast := by
  intro f hf
  cases seg with
  | nil => simp at hf
  | cons g seg => rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _)]; exact List.mem_cons_of_mem _ hf

/-- **The walk invariant.** Over a level segment `seg` above `older`, whose entries other than
the last are propagated, a nogood without repeated literals that lies on the trail and has a
literal in `seg` ends with exactly one literal in `seg`; the others lie in `older`. -/
theorem uipWalk_spec {older : List (Entry A)} :
    ∀ (seg : List (Entry A)) (c : List (Lit A)), Justified (seg ++ older) →
      (∀ e ∈ seg.dropLast, e.reason ≠ none) → c.Nodup → (∀ m ∈ c, m ∈ (seg ++ older).map Entry.lit) →
      (∃ m ∈ c, m ∈ seg.map Entry.lit) →
      (uipWalk c seg).Nodup ∧ ∃ u ∈ uipWalk c seg, u ∈ seg.map Entry.lit ∧
        ∀ m ∈ uipWalk c seg, m ≠ u → m ∈ older.map Entry.lit
  | [], _, _, _, _, _, ⟨_, _, h⟩ => by simp at h
  | e :: seg, c, just, propagated, nodup, onTrail, ⟨m₀, hm₀, inSeg⟩ => by
    have off : ∀ m, m ∈ ((e :: seg) ++ older).map Entry.lit → m ≠ e.lit → m ∈ (seg ++ older).map Entry.lit := by
      intro m hm ne
      rw [List.cons_append, List.map_cons, List.mem_cons] at hm
      exact hm.resolve_left ne
    unfold uipWalk
    split
    · rename_i he
      split
      · rename_i other
        obtain ⟨m₁, hm₁, ne₁, below₁⟩ := other
        have nonempty : seg ≠ [] := by
          rintro rfl
          simp at below₁
        have hasReason : e.reason ≠ none :=
          propagated e (by rw [List.dropLast_cons_of_ne_nil nonempty]; exact List.mem_cons_self)
        obtain ⟨ρ, hρ⟩ := Option.ne_none_iff_exists'.mp hasReason
        simp only [hρ]
        rw [List.cons_append] at just
        obtain ⟨_, rest⟩ := just.reason_spec hρ
        have onTrail' : ∀ m ∈ resolveOn c ρ.lits e.lit, m ∈ (seg ++ older).map Entry.lit := by
          intro m hm
          rcases List.mem_append.mp (List.mem_dedup.mp hm) with hm | hm
          · rw [nodup.mem_erase_iff] at hm
            exact off m (onTrail m hm.2) hm.1
          · rw [(List.nodup_dedup _).mem_erase_iff, List.mem_dedup] at hm
            exact rest m hm.2 hm.1
        obtain ⟨nodup', u, hu, inSeg', others⟩ := uipWalk_spec seg _ just.tail
          (fun f hf => propagated f (dropLast_tail_subset e seg f hf)) (List.nodup_dedup _) onTrail'
          ⟨m₁, List.mem_dedup.mpr (List.mem_append_left _ ((nodup.mem_erase_iff).mpr ⟨ne₁, hm₁⟩)), below₁⟩
        exact ⟨nodup', u, hu, by rw [List.map_cons]; exact List.mem_cons_of_mem _ inSeg', others⟩
      · rename_i alone
        refine ⟨nodup, e.lit, he, List.mem_cons_self, fun m hm ne => ?_⟩
        have := off m (onTrail m hm) ne
        rw [List.map_append, List.mem_append] at this
        exact this.resolve_left fun inSeg => alone ⟨m, hm, ne, inSeg⟩
    · rename_i he
      have ne₀ : m₀ ≠ e.lit := fun same => he (same ▸ hm₀)
      obtain ⟨nodup', u, hu, inSeg', others⟩ := uipWalk_spec seg c (by rw [List.cons_append] at just; exact just.tail)
        (fun f hf => propagated f (dropLast_tail_subset e seg f hf)) nodup
        (fun m hm => off m (onTrail m hm) fun same => he (same ▸ hm))
        ⟨m₀, hm₀, by rw [List.map_cons, List.mem_cons] at inSeg; exact inSeg.resolve_left ne₀⟩
      exact ⟨nodup', u, hu, by rw [List.map_cons]; exact List.mem_cons_of_mem _ inSeg', others⟩

/-- **First-UIP finds the unique implication point**: if the conflict nogood is falsified and has
a literal at the current level, the result has exactly one literal `u` at the current level and
every other literal lies below it. -/
theorem firstUIP_uip {s : State A} (just : Justified s.trail) {δ : Nogood A} (falsified : s.Falsifies δ)
    (current : ∃ m ∈ δ.lits, m ∈ (currentLevel s.trail).map Entry.lit) :
    (firstUIP s δ).Nodup ∧ ∃ u ∈ firstUIP s δ, u ∈ (currentLevel s.trail).map Entry.lit ∧
      ∀ m ∈ firstUIP s δ, m ≠ u → m ∈ (belowLevel s.trail).map Entry.lit := by
  have split := currentLevel_append_belowLevel s.trail
  obtain ⟨m, hm, inLevel⟩ := current
  refine uipWalk_spec _ _ (split.symm ▸ just) (currentLevel_dropLast s.trail) (List.nodup_dedup _) ?_
    ⟨m, List.mem_dedup.mpr hm, inLevel⟩
  intro l hl
  rw [split]
  exact falsified l (List.mem_dedup.mp hl)

omit [DecidableEq A] in
theorem nodup_split {t pre post : List (Entry A)} {e : Entry A} (nodup : (t.map fun e => e.lit.var).Nodup)
    (split : t = pre ++ e :: post) : (∀ f ∈ pre, f.lit.var ≠ e.lit.var) ∧ ∀ f ∈ post, f.lit.var ≠ e.lit.var := by
  rw [split, List.map_append, List.map_cons] at nodup
  have := List.nodup_middle.mp nodup
  rw [List.nodup_cons, List.mem_append, not_or] at this
  exact ⟨fun f hf same => this.1.1 (same ▸ List.mem_map_of_mem hf),
    fun f hf same => this.1.2 (same ▸ List.mem_map_of_mem hf)⟩

omit [DecidableEq A] in
theorem not_mem_map_lit {pre : List (Entry A)} {e : Entry A} (fresh : ∀ f ∈ pre, f.lit.var ≠ e.lit.var) :
    e.lit ∉ pre.map Entry.lit := by
  intro h
  obtain ⟨f, hf, same⟩ := List.mem_map.mp h
  exact fresh f hf (by rw [same])

namespace Program

variable (P : Program A)

/-- **After backjumping to the assertion level, the learned nogood is unit** on its first unique
implication point, and the backjump is a step of the solver. -/
theorem firstUIP_backjump {s : State A} (inv : P.Inv s) (just : Justified s.trail) {δ : Nogood A}
    (database : P.InDatabase s δ) (falsified : s.Falsifies δ) (level : levelOf s.trail ≠ 0)
    (current : ∃ m ∈ δ.lits, m ∈ (currentLevel s.trail).map Entry.lit) (origin : Origin A) :
    ∃ u ∈ firstUIP s δ, u ∈ (currentLevel s.trail).map Entry.lit ∧
      assertionLevel s.trail (firstUIP s δ) u < levelOf s.trail ∧
      levelOf (cutTo (assertionLevel s.trail (firstUIP s δ) u) s.trail) =
        assertionLevel s.trail (firstUIP s δ) u ∧
      (⟨cutTo (assertionLevel s.trail (firstUIP s δ) u) s.trail, s.learned, s.restartMark⟩ : State A).UnitOn
        ⟨firstUIP s δ, origin⟩ u ∧
      P.Step (.running s) (.running ⟨⟨u.compl, assertionLevel s.trail (firstUIP s δ) u,
        some ⟨firstUIP s δ, origin⟩⟩ :: cutTo (assertionLevel s.trail (firstUIP s δ) u) s.trail,
          s.learned, s.restartMark⟩) := by
  obtain ⟨_, u, hu, uCurrent, others⟩ := firstUIP_uip just falsified current
  set t := s.trail with ht
  set r := firstUIP s δ with hr
  set j := assertionLevel t r u with hj
  have whole := currentLevel_append_belowLevel t
  have levels := levelOf_belowLevel level
  have dropLast := currentLevel_dropLast t
  generalize hC : currentLevel t = C at whole dropLast
  generalize hB : belowLevel t = B at whole levels others
  -- every other literal lies below the current level, at a level of at most `j`
  have otherLevel : ∀ m ∈ r, m ≠ u → litLevel m t ≤ levelOf B := by
    intro m hm ne
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp (others m hm ne)
    obtain ⟨pre, post, split⟩ := List.append_of_mem hf
    have full : t = (C ++ pre) ++ f :: post := by rw [List.append_assoc, ← split, whole]
    rw [full, litLevel_append_cons rfl (not_mem_map_lit (nodup_split inv.nodup full).1)]
    have := levelOf_append pre (f :: post)
    rw [← split] at this
    omega
  have below : j < levelOf t := by
    have : j ≤ levelOf B := foldr_max_le fun x hx => by
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      obtain ⟨hm, ne⟩ := List.mem_filter.mp hm
      exact otherLevel m hm (by simpa using ne)
    omega
  -- the entry of `u` lies in the current level, above every decision but the newest
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp uCurrent
  rw [hC] at hg
  obtain ⟨pre, post, levelSplit⟩ := List.append_of_mem hg
  have full : t = pre ++ g :: (post ++ B) := by
    rw [← whole, levelSplit, List.append_assoc, List.cons_append]
  have preFree : ∀ f ∈ pre, f.reason ≠ none := by
    intro f hf
    apply dropLast f
    rw [levelSplit, List.dropLast_append_cons]
    exact List.mem_append_left _ hf
  have gLevel : levelOf (g :: (post ++ B)) = levelOf t := by
    have := levelOf_append pre (g :: (post ++ B))
    rw [← full, levelOf_eq_zero_of_propagated preFree] at this
    omega
  have cutBelow : cutTo j t = cutTo j (post ++ B) := by
    rw [full, cutTo_of_lt (by omega) pre, cutTo, if_neg (by omega)]
  have gFresh := (nodup_split inv.nodup full).2
  have unassigned : ∀ f ∈ cutTo j t, f.lit.var ≠ g.lit.var := by
    intro f hf
    obtain ⟨pre', split'⟩ := cutTo_suffix j (post ++ B)
    rw [cutBelow] at hf
    exact gFresh f (by rw [split']; exact List.mem_append_right _ hf)
  have othersIn : ∀ m ∈ r, m ≠ g.lit → m ∈ (cutTo j t).map Entry.lit := by
    intro m hm ne
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp (others m hm ne)
    obtain ⟨pre', post', split'⟩ := List.append_of_mem hf
    have full' : t = (C ++ pre') ++ f :: post' := by rw [List.append_assoc, ← split', whole]
    have atF : litLevel f.lit t = levelOf (f :: post') := by
      rw [full']
      exact litLevel_append_cons rfl (not_mem_map_lit (nodup_split inv.nodup full').1)
    have fLevel : levelOf (f :: post') ≤ j := by
      rw [← atF]
      exact litLevel_le_assertionLevel hm ne
    obtain ⟨pre'', cut⟩ := cutTo_of_le fLevel (C ++ pre')
    rw [← full'] at cut
    rw [cut]
    exact List.mem_map_of_mem (List.mem_append_right _ List.mem_cons_self)
  have isVar : P.IsVar g.lit.var :=
    inv.vars g (show g ∈ t by rw [full]; exact List.mem_append_right _ List.mem_cons_self)
  obtain ⟨preCut, d, cutSplit, decision⟩ := cutTo_split below
  have cutLevel := levelOf_cutTo below.le
  refine ⟨g.lit, hu, by rw [← hC]; exact uCurrent, below, cutLevel, ⟨hu, othersIn, ?_⟩, ?_⟩
  · rintro ⟨f, hf, same⟩
    exact unassigned f hf same
  · have step := Step.backjump (P := P) (ε := ⟨r, origin⟩) (l := g.lit) database falsified cutSplit decision
      (P.firstUIP_entailed inv database) hu othersIn unassigned isVar
    rwa [cutLevel] at step

end Program

end Analysis

end Mettapedia.Logic.ASP
