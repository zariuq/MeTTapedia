import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.Bisimulation

/-!
# Where bisimulation over borrowed contexts and contextual equivalence part

Three controls, each with its positive half proved.

* **The predicate-query gap** (`else_gap`). `e` fires one of two branches: when `x` is absent it
  makes `q`; when `x` is present it reads `x` and makes `q`. This is `(else (transform (read x) q)
  q)`: fire the first branch if it can fire now, otherwise the second. Beside every environment it
  makes `q`, exactly as the plain step `p → q` does, so `{e}` and `{p}` are contextually equivalent.
  They are not bisimilar over borrowed contexts: the plain step's label borrows nothing and closes
  no region, and each branch of `e` either closes the region of `x` or borrows `x`. Completeness
  fails exactly here: an answer that must decide a predicate query by looking at the environment
  beyond the challenger's label.
* **The catalyst gap** (`catalyst_gap`), without any predicate query. A rule that uses `b` as a
  catalyst (`a + b → d + b`) beside a rule `a → d` gives `a` a step with label `b`; `e → d` has no
  such label. Every environment sees the same reductions, so `{a}` and `{e}` are contextually
  equivalent and bisimilar in the semi-saturated game, but not in the literal game of matching
  labels.
* **Conditions on labels are necessary** (`blind_not_congruence`). Drop the comparison of
  conditions from the game: the plain step and the absence-guarded step become "bisimilar", and
  adding `x` beside both separates them, so the condition-blind relation is not a congruence and
  not sound for contextual equivalence.

The positive halves use one tool: a relation that swaps one copy of a label for one copy of
another beside a common rest is closed under contexts by construction, so it is contextual as soon
as reductions match (`contextual_of_swap`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence

universe u v

variable {R : Type u} [DecidableEq R]

/-! ## Swapping one label for another -/

/-- Equal bags, or bags that differ by one copy of `a` against one copy of `b` beside a common rest. -/
def SwapRel (a b : R) (X Y : Multiset R) : Prop :=
  X = Y ∨ (∃ Z, X = a ::ₘ Z ∧ Y = b ::ₘ Z) ∨ (∃ Z, X = b ::ₘ Z ∧ Y = a ::ₘ Z)

omit [DecidableEq R] in
theorem SwapRel.symm {a b : R} {X Y : Multiset R} (h : SwapRel a b X Y) : SwapRel a b Y X := by
  rcases h with rfl | ⟨Z, rfl, rfl⟩ | ⟨Z, rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨Z, rfl, rfl⟩)
  · exact Or.inr (Or.inl ⟨Z, rfl, rfl⟩)

omit [DecidableEq R] in
theorem SwapRel.add {a b : R} {X Y : Multiset R} (h : SwapRel a b X Y) (C : Multiset R) :
    SwapRel a b (X + C) (Y + C) := by
  rcases h with rfl | ⟨Z, rfl, rfl⟩ | ⟨Z, rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨Z + C, Multiset.cons_add _ _ _, Multiset.cons_add _ _ _⟩)
  · exact Or.inr (Or.inr ⟨Z + C, Multiset.cons_add _ _ _, Multiset.cons_add _ _ _⟩)

section Swap

variable {Γ : Rule R → Prop} {Adm : R → Prop} {ι : Type v} {obs : ι → R → Prop}

/-- **A swap is contextual when reductions match.** If `a` and `b` show no barb, and beside every
rest the reductions of `a` and of `b` match up to the swap, then `a` and `b` are contextually
equivalent beside every rest. -/
theorem contextual_of_swap {a b : R} (obsA : ∀ i, ¬ obs i a) (obsB : ∀ i, ¬ obs i b)
    (fwd : ∀ Z X', Reduces Γ (a ::ₘ Z) X' → ∃ Y', Reduces Γ (b ::ₘ Z) Y' ∧ SwapRel a b X' Y')
    (bwd : ∀ Z Y', Reduces Γ (b ::ₘ Z) Y' → ∃ X', Reduces Γ (a ::ₘ Z) X' ∧ SwapRel a b X' Y')
    (Z : Multiset R) : Contextual Γ Adm obs (a ::ₘ Z) (b ::ₘ Z) := by
  have barbSwap : ∀ {c d : R}, (∀ i, ¬ obs i c) → ∀ (W : Multiset R) i,
      Barb (obs i) (c ::ₘ W) → Barb (obs i) (d ::ₘ W) := by
    intro c d obsC W i ⟨y, member, shows⟩
    rcases Multiset.mem_cons.mp member with rfl | inW
    · exact absurd shows (obsC i)
    · exact ⟨y, Multiset.mem_cons_of_mem inW, shows⟩
  refine ⟨SwapRel a b, ⟨fun _ _ h => h.symm, ?_, ?_, fun _ _ h C _ => h.add C⟩,
    Or.inr (Or.inl ⟨Z, rfl, rfl⟩)⟩
  · rintro X Y (rfl | ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩) i shows
    · exact shows
    · exact barbSwap obsA W i shows
    · exact barbSwap obsB W i shows
  · rintro X Y (rfl | ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩) X' reduces
    · exact ⟨X', reduces, Or.inl rfl⟩
    · exact fwd W X' reduces
    · obtain ⟨Y', reducesY, rel⟩ := bwd W X' reduces
      exact ⟨Y', reducesY, rel.symm⟩

end Swap

/-! ## A literal game, and a condition-blind game -/

section Variants

variable (Γ : Rule R → Prop) (Adm : R → Prop) {ι : Type v} (obs : ι → R → Prop)

/-- **The literal game**: the answer is a step of the other side with the same label, under a weaker
condition. -/
structure IsLiteralBisimulation (B : Multiset R → Multiset R → Prop) : Prop where
  symm : ∀ ⦃M N⦄, B M N → B N M
  barb : ∀ ⦃M N⦄, B M N → ∀ i, Barb (obs i) M → Barb (obs i) N
  step : ∀ ⦃M N⦄, B M N → ∀ ⦃J F M'⦄, Admissible Adm J → BStep Γ M ⟨J, F⟩ M' →
    ∃ G N', Weaker Adm G F ∧ BStep Γ N ⟨J, G⟩ N' ∧ B M' N'

def LiteralBisimilar (M N : Multiset R) : Prop := ∃ B, IsLiteralBisimulation Γ Adm obs B ∧ B M N

/-- **The condition-blind game**: the answer's condition is not compared with the challenger's. -/
structure IsBlindBisimulation (B : Multiset R → Multiset R → Prop) : Prop where
  symm : ∀ ⦃M N⦄, B M N → B N M
  barb : ∀ ⦃M N⦄, B M N → ∀ i, Barb (obs i) M → Barb (obs i) N
  step : ∀ ⦃M N⦄, B M N → ∀ ⦃J F M'⦄, Admissible Adm J → BStep Γ M ⟨J, F⟩ M' →
    ∃ G N', BStep Γ (N + J) ⟨0, G⟩ N' ∧ B M' N'

def BlindBisimilar (M N : Multiset R) : Prop := ∃ B, IsBlindBisimulation Γ Adm obs B ∧ B M N

variable {Γ Adm obs}

/-- The literal game is finer than the semi-saturated one. -/
theorem bisimilar_of_literal {M N : Multiset R} (h : LiteralBisimilar Γ Adm obs M N) :
    Bisimilar Γ Adm obs M N := by
  obtain ⟨B, bisim, related⟩ := h
  refine ⟨B, ⟨bisim.symm, bisim.barb, ?_⟩, related⟩
  intro M N rel J F M' adm step
  obtain ⟨G, N', weaker, answer, rel'⟩ := bisim.step rel adm step
  exact ⟨G, N', weaker, answer.absorb, rel'⟩

/-- The semi-saturated game is finer than the condition-blind one. -/
theorem blind_of_bisimilar {M N : Multiset R} (h : Bisimilar Γ Adm obs M N) :
    BlindBisimilar Γ Adm obs M N := by
  obtain ⟨B, bisim, related⟩ := h
  refine ⟨B, ⟨bisim.symm, bisim.barb, ?_⟩, related⟩
  intro M N rel J F M' adm step
  obtain ⟨G, N', -, answer, rel'⟩ := bisim.step rel adm step
  exact ⟨G, N', answer, rel'⟩

end Variants

/-! ## Controls -/

namespace Controls

/-! ### The predicate-query gap: `else` with two equal branches -/

section Else

/-- Labels: a plain process `p`, its result `q`, the region `x`, and the choice `e`. -/
inductive ElseAtom where
  | p
  | q
  | x
  | e
  deriving DecidableEq, Repr

open ElseAtom

/-- The region of `x`. -/
def isX : ElseAtom → Bool
  | x => true
  | _ => false

/-- `p → q`. -/
def plain : Rule ElseAtom := ⟨{p}, 0, {q}, fun _ => false⟩

/-- `e → q` when `x` is absent. -/
def elseAbsent : Rule ElseAtom := ⟨{e}, 0, {q}, isX⟩

/-- `e → q` reading `x`. -/
def elseRead : Rule ElseAtom := ⟨{e}, {x}, {q}, fun _ => false⟩

/-- The rules of the `else` control. -/
def elseRules : Rule ElseAtom → Prop := fun ρ => ρ = plain ∨ ρ = elseAbsent ∨ ρ = elseRead

/-- One barb: `q` is visible. -/
def showsQ : Unit → ElseAtom → Prop := fun _ y => y = q

theorem avoids_isX_of_not_mem {Z : Multiset ElseAtom} (h : x ∉ Z) : Avoids Z isX := by
  intro y member
  cases y with
  | x => exact absurd member h
  | _ => rfl

theorem not_mem_of_avoids_isX {Z : Multiset ElseAtom} (h : Avoids Z isX) : x ∉ Z := fun member => by
  have := h x member
  exact absurd this (by decide)

theorem plain_result (Z : Multiset ElseAtom) : plain.result (p ::ₘ Z) = Z + {q} := by
  simp [plain, Rule.result, Multiset.sub_singleton, Multiset.erase_cons_head]

theorem else_result (Z : Multiset ElseAtom) (ρ : Rule ElseAtom) (take : ρ.take = {e}) (make : ρ.make = {q}) :
    ρ.result (e ::ₘ Z) = Z + {q} := by
  simp [Rule.result, take, make, Multiset.sub_singleton, Multiset.erase_cons_head]

/-- Reductions of `p` beside a rest are matched by reductions of `e`, up to the swap. -/
theorem else_fwd (Z X' : Multiset ElseAtom) (reduces : Reduces elseRules (p ::ₘ Z) X') :
    ∃ Y', Reduces elseRules (e ::ₘ Z) Y' ∧ SwapRel p e X' Y' := by
  obtain ⟨ρ, hρ | hρ | hρ, ⟨sub, avoids⟩, rfl⟩ := reduces <;> subst hρ
  · -- `p` fired; `e` fires whichever branch the rest allows, to the same bag.
    rw [plain_result]
    by_cases hx : x ∈ Z
    · refine ⟨elseRead.result (e ::ₘ Z), ⟨elseRead, Or.inr (Or.inr rfl), ⟨?_, fun _ _ => rfl⟩, rfl⟩,
        Or.inl (else_result Z elseRead rfl rfl).symm⟩
      have : ({e} + {x} : Multiset ElseAtom) ≤ e ::ₘ Z := by
        rw [← Multiset.singleton_add]
        exact add_le_add (le_refl _) (Multiset.singleton_le.mpr hx)
      simpa [elseRead, Rule.redex] using this
    · refine ⟨elseAbsent.result (e ::ₘ Z), ⟨elseAbsent, Or.inr (Or.inl rfl), ⟨?_, ?_⟩, rfl⟩,
        Or.inl (else_result Z elseAbsent rfl rfl).symm⟩
      · simp [elseAbsent, Rule.redex]
      · simpa [elseAbsent, Rule.redex, Multiset.sub_singleton, Multiset.erase_cons_head] using
          avoids_isX_of_not_mem hx
  · -- a copy of `e` in the rest fired its absence branch; so does the swapped copy.
    have eZ : e ∈ Z := by simpa [elseAbsent, Rule.redex] using sub
    have frame : (p ::ₘ Z) - elseAbsent.redex = p ::ₘ Z.erase e := by
      simp [elseAbsent, Rule.redex, Multiset.sub_singleton, Multiset.erase_cons_tail Z (by decide : p ≠ e)]
    rw [frame] at avoids
    have hx : x ∉ Z := fun hx => by
      have := not_mem_of_avoids_isX avoids
      exact this (Multiset.mem_cons_of_mem ((Multiset.mem_erase_of_ne (by decide)).mpr hx))
    refine ⟨elseAbsent.result (e ::ₘ Z), ⟨elseAbsent, Or.inr (Or.inl rfl),
      ⟨by simp [elseAbsent, Rule.redex], ?_⟩, rfl⟩, Or.inr (Or.inl ⟨Z.erase e + {q}, ?_, ?_⟩)⟩
    · simpa [elseAbsent, Rule.redex, Multiset.sub_singleton, Multiset.erase_cons_head] using
        avoids_isX_of_not_mem hx
    · simp [elseAbsent, Rule.result, Multiset.sub_singleton, Multiset.erase_cons_tail Z (by decide : p ≠ e)]
    · rw [else_result Z elseAbsent rfl rfl, ← Multiset.cons_add, Multiset.cons_erase eZ]
  · -- a copy of `e` in the rest fired its reading branch; so does the swapped copy.
    have sub' : ({e} + {x} : Multiset ElseAtom) ≤ p ::ₘ Z := by simpa [elseRead, Rule.redex] using sub
    have eZ : e ∈ Z := by
      have := Multiset.mem_of_le sub' (Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self e)))
      rcases Multiset.mem_cons.mp this with h | h
      · exact absurd h (by decide)
      · exact h
    have hx : x ∈ Z.erase e := by
      have := (Multiset.le_iff_count.mp sub') x
      simp only [Multiset.count_add, Multiset.count_singleton, Multiset.count_cons] at this
      have pos : 0 < Multiset.count x (Z.erase e) := by
        rw [Multiset.count_erase_of_ne (by decide)]
        simp at this
        omega
      exact Multiset.count_pos.mp pos
    refine ⟨elseRead.result (e ::ₘ Z), ⟨elseRead, Or.inr (Or.inr rfl), ⟨?_, fun _ _ => rfl⟩, rfl⟩,
      Or.inr (Or.inl ⟨Z.erase e + {q}, ?_, ?_⟩)⟩
    · have : ({e} + {x} : Multiset ElseAtom) ≤ e ::ₘ Z := by
        rw [← Multiset.singleton_add]
        exact add_le_add (le_refl _) (Multiset.singleton_le.mpr (Multiset.mem_of_mem_erase hx))
      simpa [elseRead, Rule.redex] using this
    · simp [elseRead, Rule.result, Multiset.sub_singleton, Multiset.erase_cons_tail Z (by decide : p ≠ e)]
    · rw [else_result Z elseRead rfl rfl, ← Multiset.cons_add, Multiset.cons_erase eZ]

/-- Reductions of `e` beside a rest are matched by reductions of `p`, up to the swap. -/
theorem else_bwd (Z Y' : Multiset ElseAtom) (reduces : Reduces elseRules (e ::ₘ Z) Y') :
    ∃ X', Reduces elseRules (p ::ₘ Z) X' ∧ SwapRel p e X' Y' := by
  obtain ⟨ρ, hρ | hρ | hρ, ⟨sub, avoids⟩, rfl⟩ := reduces <;> subst hρ
  · -- a copy of `p` in the rest fired; so does the swapped copy.
    have pZ : p ∈ Z := by simpa [plain, Rule.redex] using sub
    refine ⟨plain.result (p ::ₘ Z), ⟨plain, Or.inl rfl, ⟨by simp [plain, Rule.redex],
      fun _ _ => rfl⟩, rfl⟩, Or.inr (Or.inl ⟨Z.erase p + {q}, ?_, ?_⟩)⟩
    · rw [plain_result, ← Multiset.cons_add, Multiset.cons_erase pZ]
    · simp [plain, Rule.result, Multiset.sub_singleton, Multiset.erase_cons_tail Z (by decide : e ≠ p)]
  · -- `e` fired its absence branch: `p` fires to the same bag.
    refine ⟨plain.result (p ::ₘ Z), ⟨plain, Or.inl rfl, ⟨by simp [plain, Rule.redex],
      fun _ _ => rfl⟩, rfl⟩, Or.inl ?_⟩
    rw [plain_result, else_result Z elseAbsent rfl rfl]
  · -- `e` fired its reading branch: `p` fires to the same bag.
    refine ⟨plain.result (p ::ₘ Z), ⟨plain, Or.inl rfl, ⟨by simp [plain, Rule.redex],
      fun _ _ => rfl⟩, rfl⟩, Or.inl ?_⟩
    rw [plain_result, else_result Z elseRead rfl rfl]

/-- **The predicate-query gap.** `{p}` and `{e}` are contextually equivalent for every admissible
class, and not bisimilar over borrowed contexts once `x` is admissible. -/
theorem else_gap (Adm : ElseAtom → Prop) (admX : Adm x) :
    Contextual elseRules Adm showsQ {p} {e} ∧ ¬ Bisimilar elseRules Adm showsQ {p} {e} := by
  refine ⟨?_, ?_⟩
  · have := contextual_of_swap (Γ := elseRules) (Adm := Adm) (obs := showsQ)
      (fun _ h => by cases h) (fun _ h => by cases h) else_fwd else_bwd 0
    simpa using this
  · rintro ⟨B, bisim, related⟩
    have step : BStep elseRules {p} ⟨0, fun _ => false⟩ {q} :=
      ⟨plain, Or.inl rfl, by decide, rfl, fun _ _ => rfl, by decide⟩
    obtain ⟨G, N', weaker, ⟨ρ, hρ | hρ | hρ, hJ, hG, -, -⟩, -⟩ :=
      bisim.step related (admissible_zero Adm) step
    · subst hρ; simp only at hJ; exact absurd hJ (by decide)
    · subst hρ
      have := weaker x admX (by simp at hG; rw [hG]; rfl)
      exact absurd this (by decide)
    · subst hρ; simp only at hJ; exact absurd hJ (by decide)

end Else

/-! ### The catalyst gap: literal labels are incomplete without predicate queries -/

section Catalyst

/-- Labels: `a`, a catalyst `b`, the result `d`, and `e`. -/
inductive CAtom where
  | a
  | b
  | d
  | e
  deriving DecidableEq, Repr

open CAtom

/-- `a → d`. -/
def solo : Rule CAtom := ⟨{a}, 0, {d}, fun _ => false⟩

/-- `a + b → d + b`: `b` is a catalyst. -/
def catalysed : Rule CAtom := ⟨{a}, {b}, {d}, fun _ => false⟩

/-- `e → d`. -/
def other : Rule CAtom := ⟨{e}, 0, {d}, fun _ => false⟩

/-- The rules of the catalyst control: positive. -/
def catalystRules : Rule CAtom → Prop := fun ρ => ρ = solo ∨ ρ = catalysed ∨ ρ = other

theorem catalystRules_positive : PositiveRules catalystRules := by
  rintro ρ (rfl | rfl | rfl) _ <;> rfl

theorem take_result (Z : Multiset CAtom) (ρ : Rule CAtom) (c : CAtom) (take : ρ.take = {c})
    (make : ρ.make = {d}) : ρ.result (c ::ₘ Z) = Z + {d} := by
  simp [Rule.result, take, make, Multiset.sub_singleton, Multiset.erase_cons_head]

theorem mem_of_singleton_le_cons {c c' : CAtom} {Z : Multiset CAtom} (ne : c ≠ c')
    (sub : ({c} : Multiset CAtom) ≤ c' ::ₘ Z) : c ∈ Z := by
  rcases Multiset.mem_cons.mp (Multiset.singleton_le.mp sub) with h | h
  · exact absurd h ne
  · exact h

theorem catalyst_fwd (Z X' : Multiset CAtom) (reduces : Reduces catalystRules (a ::ₘ Z) X') :
    ∃ Y', Reduces catalystRules (e ::ₘ Z) Y' ∧ SwapRel a e X' Y' := by
  have otherFires : Reduces catalystRules (e ::ₘ Z) (Z + {d}) :=
    ⟨other, Or.inr (Or.inr rfl), ⟨by simp [other, Rule.redex], fun _ _ => rfl⟩,
      (take_result Z other e rfl rfl).symm⟩
  obtain ⟨ρ, hρ | hρ | hρ, ⟨sub, -⟩, rfl⟩ := reduces <;> subst hρ
  · exact ⟨Z + {d}, otherFires, Or.inl (take_result Z solo a rfl rfl)⟩
  · exact ⟨Z + {d}, otherFires, Or.inl (take_result Z catalysed a rfl rfl)⟩
  · have eZ : e ∈ Z := by simpa [other, Rule.redex] using sub
    refine ⟨Z + {d}, otherFires, Or.inr (Or.inl ⟨Z.erase e + {d}, ?_, ?_⟩)⟩
    · simp [other, Rule.result, Multiset.sub_singleton, Multiset.erase_cons_tail Z (by decide : a ≠ e)]
    · rw [← Multiset.cons_add, Multiset.cons_erase eZ]

theorem catalyst_bwd (Z Y' : Multiset CAtom) (reduces : Reduces catalystRules (e ::ₘ Z) Y') :
    ∃ X', Reduces catalystRules (a ::ₘ Z) X' ∧ SwapRel a e X' Y' := by
  have soloFires : Reduces catalystRules (a ::ₘ Z) (Z + {d}) :=
    ⟨solo, Or.inl rfl, ⟨by simp [solo, Rule.redex], fun _ _ => rfl⟩,
      (take_result Z solo a rfl rfl).symm⟩
  obtain ⟨ρ, hρ | hρ | hρ, ⟨sub, -⟩, rfl⟩ := reduces <;> subst hρ
  · have aZ : a ∈ Z := by simpa [solo, Rule.redex] using sub
    refine ⟨Z + {d}, soloFires, Or.inr (Or.inl ⟨Z.erase a + {d}, ?_, ?_⟩)⟩
    · rw [← Multiset.cons_add, Multiset.cons_erase aZ]
    · simp [solo, Rule.result, Multiset.sub_singleton, Multiset.erase_cons_tail Z (by decide : e ≠ a)]
  · have aZ : a ∈ Z := by
      have sub' : ({a} + {b} : Multiset CAtom) ≤ e ::ₘ Z := by
        simpa [catalysed, Rule.redex] using sub
      exact mem_of_singleton_le_cons (by decide)
        ((Multiset.le_add_right _ _).trans sub')
    refine ⟨Z + {d}, soloFires, Or.inr (Or.inl ⟨Z.erase a + {d}, ?_, ?_⟩)⟩
    · rw [← Multiset.cons_add, Multiset.cons_erase aZ]
    · simp [catalysed, Rule.result, Multiset.sub_singleton,
        Multiset.erase_cons_tail Z (by decide : e ≠ a)]
  · exact ⟨Z + {d}, soloFires, Or.inl (take_result Z other e rfl rfl).symm⟩

/-- **The catalyst gap.** `{a}` and `{e}` are contextually equivalent and bisimilar in the
semi-saturated game, for every admissible class and every barbs that do not see `a` or `e`; they
are not bisimilar in the literal game once `b` is admissible. -/
theorem catalyst_gap (Adm : CAtom → Prop) (admB : Adm b) {ι : Type v} (obs : ι → CAtom → Prop)
    (obsA : ∀ i, ¬ obs i a) (obsE : ∀ i, ¬ obs i e) :
    Contextual catalystRules Adm obs {a} {e} ∧ Bisimilar catalystRules Adm obs {a} {e} ∧
      ¬ LiteralBisimilar catalystRules Adm obs {a} {e} := by
  have ctx : Contextual catalystRules Adm obs {a} {e} := by
    have := contextual_of_swap (Γ := catalystRules) (Adm := Adm) (obs := obs) obsA obsE
      catalyst_fwd catalyst_bwd 0
    simpa using this
  refine ⟨ctx, bisimilar_of_contextual catalystRules_positive ctx, ?_⟩
  rintro ⟨B, bisim, related⟩
  have step : BStep catalystRules {a} ⟨{b}, fun _ => false⟩ ({b} + {d}) :=
    ⟨catalysed, Or.inr (Or.inl rfl), by decide, rfl, by
      intro y member; rfl, by decide⟩
  obtain ⟨G, N', -, ⟨ρ, hρ | hρ | hρ, hJ, -, -, -⟩, -⟩ :=
    bisim.step related (by simpa [Admissible] using admB) step
  all_goals (subst hρ; simp only at hJ; exact absurd hJ (by decide))

end Catalyst

/-! ### Conditions on labels are necessary -/

section Blind

open ElseAtom

/-- The plain step and the absence branch alone. -/
def guardRules : Rule ElseAtom → Prop := fun ρ => ρ = plain ∨ ρ = elseAbsent

/-- No barbs. -/
def noBarbs : Empty → ElseAtom → Prop := Empty.elim

theorem guard_label_free {M M' J : Multiset ElseAtom} {F : ElseAtom → Bool}
    (step : BStep guardRules M ⟨J, F⟩ M') : x ∉ J := by
  obtain ⟨ρ, hρ | hρ, hJ, -, -, -⟩ := step <;> subst hρ <;> simp only at hJ <;> rw [hJ] <;>
    intro member <;> have := Multiset.mem_of_le (Multiset.sub_le_self _ _) member <;>
    simp [plain, elseAbsent, Rule.redex] at this

theorem guard_result_free {M M' J : Multiset ElseAtom} {F : ElseAtom → Bool}
    (step : BStep guardRules M ⟨J, F⟩ M') (hM : x ∉ M) : x ∉ M' := by
  have hJ := guard_label_free step
  obtain ⟨ρ, hρ | hρ, -, -, -, rfl⟩ := step <;> subst hρ <;> intro member <;>
    simp only [Rule.result, plain, elseAbsent, Multiset.mem_add, Multiset.mem_singleton] at member <;>
    rcases member with member | member
  all_goals first
    | (have := Multiset.mem_of_le (Multiset.sub_le_self _ _) member
       rcases Multiset.mem_add.mp this with h | h
       · exact hM h
       · exact hJ h)
    | exact absurd member (by decide)

/-- The relation that relates `p` and `e` beside every rest without `x`. -/
def blindRel (X Y : Multiset ElseAtom) : Prop := X = Y ∨ (x ∉ X ∧ x ∉ Y ∧ SwapRel p e X Y)

theorem guard_fwd (W X' : Multiset ElseAtom) (hW : x ∉ W) (reduces : Reduces guardRules (p ::ₘ W) X') :
    ∃ Y', Reduces guardRules (e ::ₘ W) Y' ∧ SwapRel p e X' Y' := by
  have r : Reduces elseRules (p ::ₘ W) X' := by
    obtain ⟨ρ, hρ, rest⟩ := reduces
    exact ⟨ρ, hρ.elim Or.inl (fun h => Or.inr (Or.inl h)), rest⟩
  obtain ⟨Y', ⟨ρ, hρ | hρ | hρ, enabled, hY⟩, rel⟩ := else_fwd W X' r
  · exact ⟨Y', ⟨ρ, Or.inl hρ, enabled, hY⟩, rel⟩
  · exact ⟨Y', ⟨ρ, Or.inr hρ, enabled, hY⟩, rel⟩
  · -- the reading branch needs `x`, which the rest lacks
    subst hρ
    exfalso
    have : x ∈ e ::ₘ W := Multiset.mem_of_le enabled.1 (by simp [elseRead, Rule.redex])
    rcases Multiset.mem_cons.mp this with h | h
    · exact absurd h (by decide)
    · exact hW h

theorem guard_bwd (W Y' : Multiset ElseAtom) (hW : x ∉ W) (reduces : Reduces guardRules (e ::ₘ W) Y') :
    ∃ X', Reduces guardRules (p ::ₘ W) X' ∧ SwapRel p e X' Y' := by
  have r : Reduces elseRules (e ::ₘ W) Y' := by
    obtain ⟨ρ, hρ, rest⟩ := reduces
    exact ⟨ρ, hρ.elim Or.inl (fun h => Or.inr (Or.inl h)), rest⟩
  obtain ⟨X', ⟨ρ, hρ | hρ | hρ, enabled, hX⟩, rel⟩ := else_bwd W Y' r
  · exact ⟨X', ⟨ρ, Or.inl hρ, enabled, hX⟩, rel⟩
  · exact ⟨X', ⟨ρ, Or.inr hρ, enabled, hX⟩, rel⟩
  · subst hρ
    exfalso
    have : x ∈ p ::ₘ W := Multiset.mem_of_le enabled.1 (by simp [elseRead, Rule.redex])
    rcases Multiset.mem_cons.mp this with h | h
    · exact absurd h (by decide)
    · exact hW h

theorem guard_reduces_free {M M' : Multiset ElseAtom} (reduces : Reduces guardRules M M') (hM : x ∉ M) :
    x ∉ M' := by
  obtain ⟨G, step⟩ := reduces_iff_step_zero.mp reduces
  exact guard_result_free step hM

/-- `blindRel` is a condition-blind bisimulation. -/
theorem blindRel_isBlind : IsBlindBisimulation guardRules (fun _ => True) noBarbs blindRel where
  symm := by
    rintro X Y (rfl | ⟨hX, hY, rel⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨hY, hX, rel.symm⟩
  barb := fun _ _ _ i => i.elim
  step := by
    rintro X Y (rfl | ⟨hX, hY, rel⟩) J F X' _ step
    · exact ⟨F, X', step.absorb, Or.inl rfl⟩
    · have hJ := guard_label_free step
      have hX' := guard_result_free step hX
      have reduces : Reduces guardRules (X + J) X' := reduces_iff_step_zero.mpr ⟨F, step.absorb⟩
      rcases rel with rfl | ⟨W, rfl, rfl⟩ | ⟨W, rfl, rfl⟩
      · exact ⟨F, X', step.absorb, Or.inl rfl⟩
      · rw [Multiset.cons_add] at reduces
        have hWJ : x ∉ W + J := by
          rw [Multiset.mem_add]; rintro (h | h)
          · exact hX (Multiset.mem_cons_of_mem h)
          · exact hJ h
        obtain ⟨Y', reducesY, rel'⟩ := guard_fwd (W + J) X' hWJ reduces
        obtain ⟨G, answer⟩ := reduces_iff_step_zero.mp reducesY
        refine ⟨G, Y', by rw [Multiset.cons_add]; exact answer, Or.inr ⟨hX', ?_, rel'⟩⟩
        refine guard_reduces_free reducesY ?_
        rw [Multiset.mem_cons]; rintro (h | h)
        · exact absurd h (by decide)
        · exact hWJ h
      · rw [Multiset.cons_add] at reduces
        have hWJ : x ∉ W + J := by
          rw [Multiset.mem_add]; rintro (h | h)
          · exact hX (Multiset.mem_cons_of_mem h)
          · exact hJ h
        obtain ⟨Y', reducesY, rel'⟩ := guard_bwd (W + J) X' hWJ reduces
        obtain ⟨G, answer⟩ := reduces_iff_step_zero.mp reducesY
        refine ⟨G, Y', by rw [Multiset.cons_add]; exact answer, Or.inr ⟨hX', ?_, rel'.symm⟩⟩
        refine guard_reduces_free reducesY ?_
        rw [Multiset.mem_cons]; rintro (h | h)
        · exact absurd h (by decide)
        · exact hWJ h

/-- **Conditions on labels are necessary.** In the condition-blind game the plain step and the
absence-guarded step are related; beside `x` they are not, and they are not contextually
equivalent. So the condition-blind relation is neither a congruence nor sound. -/
theorem blind_not_congruence :
    BlindBisimilar guardRules (fun _ => True) noBarbs {p} {e} ∧
      ¬ BlindBisimilar guardRules (fun _ => True) noBarbs ({p} + {x}) ({e} + {x}) ∧
      ¬ Contextual guardRules (fun _ => True) noBarbs {p} {e} := by
  have plainBesideX : BStep guardRules ({p} + {x}) ⟨0, fun _ => false⟩ ({x} + {q}) :=
    ⟨plain, Or.inl rfl, by decide, rfl, fun _ _ => rfl, by decide⟩
  have noAnswer : ∀ G N', ¬ BStep guardRules ({e} + {x} + 0) ⟨0, G⟩ N' := by
    rintro G N' ⟨ρ, hρ | hρ, hJ, -, avoids, -⟩ <;> subst hρ
    · simp only at hJ; exact absurd hJ (by decide)
    · have := avoids x (by decide)
      exact absurd this (by decide)
  refine ⟨⟨blindRel, blindRel_isBlind, Or.inr ⟨by decide, by decide, Or.inr (Or.inl ⟨0, rfl, rfl⟩)⟩⟩,
    ?_, ?_⟩
  · rintro ⟨B, bisim, related⟩
    obtain ⟨G, N', answer, -⟩ := bisim.step related (admissible_zero _) plainBesideX
    exact noAnswer G N' answer
  · rintro ⟨B, ctx, related⟩
    have inContext := ctx.context related (C := {x}) (fun _ _ => trivial)
    obtain ⟨N', reduces, -⟩ := ctx.reduce inContext
      (reduces_iff_step_zero.mpr ⟨_, by simpa using plainBesideX⟩)
    obtain ⟨G, answer⟩ := reduces_iff_step_zero.mp reduces
    exact noAnswer G N' (by simpa using answer)

end Blind

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence
