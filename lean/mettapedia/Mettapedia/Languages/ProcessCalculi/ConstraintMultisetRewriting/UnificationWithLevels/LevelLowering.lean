import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.LevelConstraints

/-!
# The level solver to run: lowering to the greatest bounded solution

`decideSat` searches all bounded valuations. The solver to run instead starts every variable at the
small-model bound `B` and lowers: a variable that occurs `k` steps up in the left side of a
constraint is lowered to at most the right side's current value minus `k` (`lower`). Solutions are
closed under maximum, so below the bound there is a greatest solution; lowering never passes below
any solution (`le_iterLower`), it stops moving within `|V| · B` rounds (`iterLower_fix`), and at a
point where it stops the valuation satisfies the store if any solution lies below it
(`fixpoint_solves`). So one final check decides (`lowerSat_iff`).

Each round is tabulated over the variables (`tab`), which is the same function (`tab_eq`), so a
round is one pass over the store for each variable.

**Cost.** The unit of cost is a **lowering step**: one constraint inspected for one variable
(`lowerStep`), and, at the end, one constraint checked. A copy of `lowerSat` that counts these units
by the same recursion (`lowerSatCounted`) computes the same value (`lowerSatCounted_fst`) and makes
exactly `|V| · B · (|V'| · |C|) + |C|` of them (`lowerSatCounted_snd`), where `|V|` counts the
variable occurrences, `B` is the small-model bound, `|V'|` the distinct variables and `|C|` the
constraints. In the unary size `s` of the store (closed levels and successors counted in unary,
`LevelStore.usize`) this is at most `s³ (s + 1)² + s` (`lowerSat_cost`). One unit evaluates one
constraint's two levels at a valuation read from a table of `|V'|` entries, so it is polynomial in
`s` as well; that per-unit cost is not formalized here. With binary constants the bound is
pseudo-polynomial, as for max-atom problems.

Positive and negative examples are those of `LevelConstraints`, transported by `lowerSat_iff`; the
counts of one satisfiable and one unsatisfiable store are computed in the kernel
(`counted_satisfiable`, `counted_unsatisfiable`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

open Mettapedia.TypeTheory.UniverseLevel

namespace Level

/-- The larger of two optional offsets. -/
def maxOpt : Option Nat → Option Nat → Option Nat
  | some a, some b => some (max a b)
  | some a, none => some a
  | none, some b => some b
  | none, none => none

/-- The largest offset at which a variable occurs in a level. -/
def offset (x : Nat) : Level → Option Nat
  | .const _ => none
  | .param i => if i = x then some 0 else none
  | .succ l => (offset x l).map (· + 1)
  | .max l m => maxOpt (offset x l) (offset x m)

theorem offset_mem {x : Nat} : ∀ {l : Level} {k : Nat}, offset x l = some k → x ∈ varList l
  | .const _, _, h => by simp [offset] at h
  | .param i, _, h => by
      simp only [offset] at h
      split_ifs at h with hix
      subst hix
      simp [varList]
  | .succ l, _, h => by
      simp only [offset, Option.map_eq_some_iff] at h
      obtain ⟨k', hk', _⟩ := h
      exact offset_mem (l := l) hk'
  | .max l m, k, h => by
      simp only [offset] at h
      simp only [varList, List.mem_append]
      cases hl : offset x l with
      | some a => exact Or.inl (offset_mem hl)
      | none =>
          cases hm : offset x m with
          | some b => exact Or.inr (offset_mem hm)
          | none => rw [hl, hm] at h; simp [maxOpt] at h

/-- Monotone in the values of its variables. -/
theorem value_mono {σ ρ : Nat → Nat} (h : ∀ i, σ i ≤ ρ i) (l : Level) : value σ l ≤ value ρ l :=
  LevelExpr.eval_mono h l

theorem atoms_maxOpt {ρ : Nat → Nat} {N : Nat} (l m : Level) :
    (∀ x k, maxOpt (offset x l) (offset x m) = some k → ρ x + k ≤ N) ↔
      (∀ x k, offset x l = some k → ρ x + k ≤ N) ∧ (∀ x k, offset x m = some k → ρ x + k ≤ N) := by
  constructor
  · intro h
    constructor
    · intro x a ha
      cases hm : offset x m with
      | some b =>
          have := h x (max a b) (by rw [ha, hm]; rfl)
          exact le_trans (Nat.add_le_add_left (le_max_left a b) _) this
      | none => exact h x a (by rw [ha, hm]; rfl)
    · intro x b hb
      cases hl : offset x l with
      | some a =>
          have := h x (max a b) (by rw [hl, hb]; rfl)
          exact le_trans (Nat.add_le_add_left (le_max_right a b) _) this
      | none => exact h x b (by rw [hl, hb]; rfl)
  · rintro ⟨hl, hm⟩ x k hk
    cases ha : offset x l with
    | some a =>
        cases hb : offset x m with
        | some b =>
            rw [ha, hb] at hk
            cases hk
            rcases le_total a b with hab | hab
            · rw [max_eq_right hab]
              exact hm x b hb
            · rw [max_eq_left hab]
              exact hl x a ha
        | none =>
            rw [ha, hb] at hk
            have hak : a = k := Option.some.inj hk
            subst hak
            exact hl x a ha
    | none =>
        cases hb : offset x m with
        | some b =>
            rw [ha, hb] at hk
            have hbk : b = k := Option.some.inj hk
            subst hbk
            exact hm x b hb
        | none =>
            rw [ha, hb] at hk
            cases hk

/-- **A level is at most `N` exactly when its value at zero and each of its atoms are.** -/
theorem value_le_iff (ρ : Nat → Nat) : ∀ (l : Level) (N : Nat),
    value ρ l ≤ N ↔ value (fun _ => 0) l ≤ N ∧ ∀ x k, offset x l = some k → ρ x + k ≤ N
  | .const c, N => by simp [offset]
  | .param i, N => by
      constructor
      · intro h
        refine ⟨Nat.zero_le _, fun x k hk => ?_⟩
        simp only [offset] at hk
        split_ifs at hk with hix
        cases hk
        subst hix
        simpa using h
      · rintro ⟨_, h⟩
        simpa using h i 0 (by simp [offset])
  | .succ l, N => by
      have ih := value_le_iff ρ l (N - 1)
      simp only [value_succ]
      constructor
      · intro h
        obtain ⟨b, atoms⟩ := ih.mp (by omega)
        refine ⟨by omega, fun x k hk => ?_⟩
        simp only [offset, Option.map_eq_some_iff] at hk
        obtain ⟨k', hk', rfl⟩ := hk
        have := atoms x k' hk'
        omega
      · rintro ⟨b, atoms⟩
        have h' := ih.mpr ⟨by omega, fun x k hk => by
          have := atoms x (k + 1) (by simp [offset, hk])
          omega⟩
        omega
  | .max l m, N => by
      rw [value_max, max_le_iff, value_le_iff ρ l N, value_le_iff ρ m N, value_max, max_le_iff]
      simp only [offset]
      rw [atoms_maxOpt]
      constructor
      · rintro ⟨⟨bl, al⟩, ⟨bm, am⟩⟩
        exact ⟨⟨bl, bm⟩, al, am⟩
      · rintro ⟨⟨bl, bm⟩, al, am⟩
        exact ⟨⟨bl, al⟩, ⟨bm, am⟩⟩

end Level

/-! ## Lowering -/

/-- The cap a constraint puts on a variable at a valuation. -/
def cap (ρ : Nat → Nat) (x : Nat) (c : LevelLe) : Option Nat :=
  (Level.offset x c.lhs).map fun k => Level.value ρ c.rhs - k

/-- One constraint's lowering of a variable. -/
def lowerStep (ρ : Nat → Nat) (x : Nat) (y : Nat) (c : LevelLe) : Nat :=
  (cap ρ x c).elim y (min y)

/-- **One round of lowering**: each variable goes down to every cap on it. -/
def lower (C : LevelStore) (ρ : Nat → Nat) : Nat → Nat :=
  fun x => C.foldl (lowerStep ρ x) (ρ x)

theorem fold_le (ρ : Nat → Nat) (x : Nat) : ∀ (C : LevelStore) (y : Nat),
    C.foldl (lowerStep ρ x) y ≤ y
  | [], _ => le_rfl
  | c :: C, y => by
      simp only [List.foldl_cons]
      refine le_trans (fold_le ρ x C _) ?_
      unfold lowerStep
      cases cap ρ x c with
      | none => exact le_rfl
      | some z => exact min_le_left y z

theorem fold_le_cap (ρ : Nat → Nat) (x : Nat) {c : LevelLe} {z : Nat} (hz : cap ρ x c = some z) :
    ∀ (C : LevelStore) (y : Nat), c ∈ C → C.foldl (lowerStep ρ x) y ≤ z
  | [], _, h => by cases h
  | d :: C, y, h => by
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp h with rfl | h
      · refine le_trans (fold_le ρ x C _) ?_
        simp only [lowerStep, hz, Option.elim]
        exact min_le_right y z
      · exact fold_le_cap ρ x hz C _ h

theorem le_fold (ρ : Nat → Nat) (x s : Nat) : ∀ (C : LevelStore) (y : Nat), s ≤ y →
    (∀ c ∈ C, ∀ z, cap ρ x c = some z → s ≤ z) → s ≤ C.foldl (lowerStep ρ x) y
  | [], _, hy, _ => hy
  | c :: C, y, hy, caps => by
      simp only [List.foldl_cons]
      apply le_fold ρ x s C
      · unfold lowerStep
        cases hc : cap ρ x c with
        | none => exact hy
        | some z => exact le_min hy (caps c List.mem_cons_self z hc)
      · exact fun d hd z hz => caps d (List.mem_cons_of_mem _ hd) z hz

theorem fold_of_none (ρ : Nat → Nat) (x : Nat) : ∀ (C : LevelStore) (y : Nat),
    (∀ c ∈ C, cap ρ x c = none) → C.foldl (lowerStep ρ x) y = y
  | [], _, _ => rfl
  | c :: C, y, h => by
      simp only [List.foldl_cons]
      rw [show lowerStep ρ x y c = y by simp [lowerStep, h c List.mem_cons_self]]
      exact fold_of_none ρ x C y (fun d hd => h d (List.mem_cons_of_mem _ hd))

theorem lower_le (C : LevelStore) (ρ : Nat → Nat) (x : Nat) : lower C ρ x ≤ ρ x :=
  fold_le ρ x C (ρ x)

/-- A variable that occurs in no constraint is not lowered. -/
theorem lower_off {C : LevelStore} {x : Nat} (hx : x ∉ LevelStore.varList C) (ρ : Nat → Nat) :
    lower C ρ x = ρ x := by
  apply fold_of_none
  intro c hc
  cases ho : Level.offset x c.lhs with
  | none => simp [cap, ho]
  | some k =>
      exact absurd (LevelStore.varList_of_mem hc (List.mem_append_left _ (Level.offset_mem ho))) hx

/-- The atom bound of a satisfied constraint. -/
theorem atom_le {σ : Nat → Nat} {c : LevelLe} (holds : c.Holds σ) {x k : Nat}
    (hk : Level.offset x c.lhs = some k) : σ x + k ≤ Level.value σ c.rhs :=
  ((Level.value_le_iff σ c.lhs _).mp holds).2 x k hk

/-- **Lowering never passes below a solution.** -/
theorem le_lower {C : LevelStore} {σ ρ : Nat → Nat} (sat : C.Satisfies σ) (below : ∀ x, σ x ≤ ρ x)
    (x : Nat) : σ x ≤ lower C ρ x := by
  apply le_fold ρ x (σ x) C (ρ x) (below x)
  intro c hc z hz
  simp only [cap, Option.map_eq_some_iff] at hz
  obtain ⟨k, hk, rfl⟩ := hz
  have one := atom_le (sat c hc) hk
  have two := Level.value_mono below c.rhs
  omega

/-- **Where lowering stops, the valuation is a solution, if any solution lies below it.** -/
theorem fixpoint_solves {C : LevelStore} {σ ρ : Nat → Nat} (fix : ∀ x, lower C ρ x = ρ x)
    (sat : C.Satisfies σ) (below : ∀ x, σ x ≤ ρ x) : C.Satisfies ρ := by
  intro c hc
  have holds := sat c hc
  have up : Level.value σ c.rhs ≤ Level.value ρ c.rhs := Level.value_mono below c.rhs
  apply (Level.value_le_iff ρ c.lhs _).mpr
  refine ⟨?_, fun x k hk => ?_⟩
  · have zero : Level.value (fun _ => 0) c.lhs ≤ Level.value σ c.lhs :=
      Level.value_mono (fun _ => Nat.zero_le _) c.lhs
    exact le_trans zero (le_trans holds up)
  · have capped : lower C ρ x ≤ Level.value ρ c.rhs - k :=
      fold_le_cap ρ x (by simp [cap, hk]) C (ρ x) hc
    rw [fix x] at capped
    have := atom_le holds hk
    omega

/-! ## Iteration -/

/-- `n` rounds of lowering. -/
def iterLower (C : LevelStore) : Nat → (Nat → Nat) → (Nat → Nat)
  | 0, ρ => ρ
  | n + 1, ρ => iterLower C n (lower C ρ)

theorem le_iterLower {C : LevelStore} {σ : Nat → Nat} (sat : C.Satisfies σ) :
    ∀ (n : Nat) (ρ : Nat → Nat), (∀ x, σ x ≤ ρ x) → ∀ x, σ x ≤ iterLower C n ρ x
  | 0, _, below => below
  | n + 1, ρ, below => le_iterLower sat n (lower C ρ) (le_lower sat below)

theorem iterLower_of_fix {C : LevelStore} {ρ : Nat → Nat} (fix : lower C ρ = ρ) :
    ∀ n, iterLower C n ρ = ρ
  | 0 => rfl
  | n + 1 => by
      show iterLower C n (lower C ρ) = ρ
      rw [fix]
      exact iterLower_of_fix fix n

/-- The potential: the sum of the values of the listed variables. -/
def pot (V : List Nat) (ρ : Nat → Nat) : Nat := (V.map ρ).sum

theorem pot_lt {V : List Nat} {f g : Nat → Nat} (le : ∀ x, f x ≤ g x) {x₀ : Nat} (hx₀ : x₀ ∈ V)
    (lt : f x₀ < g x₀) : pot V f < pot V g := by
  induction V with
  | nil => cases hx₀
  | cons a V ih =>
      simp only [pot, List.map_cons, List.sum_cons] at ih ⊢
      have rest : (V.map f).sum ≤ (V.map g).sum := by
        clear ih hx₀
        induction V with
        | nil => exact le_rfl
        | cons b V ihV =>
            simp only [List.map_cons, List.sum_cons]
            exact Nat.add_le_add (le b) ihV
      rcases List.mem_cons.mp hx₀ with rfl | hx₀
      · exact Nat.add_lt_add_of_lt_of_le lt rest
      · exact Nat.add_lt_add_of_le_of_lt (le a) (ih hx₀)

/-- **Lowering stops moving within the potential's number of rounds.** -/
theorem iterLower_fix (C : LevelStore) :
    ∀ (n : Nat) (ρ : Nat → Nat), pot (LevelStore.varList C) ρ ≤ n →
      ∀ x, lower C (iterLower C n ρ) x = iterLower C n ρ x := by
  intro n
  induction n with
  | zero =>
      intro ρ hpot x
      by_cases h : ∀ y ∈ LevelStore.varList C, lower C ρ y = ρ y
      · have fix : lower C ρ = ρ := funext fun y =>
          if hy : y ∈ LevelStore.varList C then h y hy else lower_off hy ρ
        show lower C ρ x = ρ x
        rw [fix]
      · obtain ⟨y, hy, ne⟩ : ∃ y ∈ LevelStore.varList C, lower C ρ y ≠ ρ y := by
          by_contra none
          exact h fun y hy => by
            by_contra ne
            exact none ⟨y, hy, ne⟩
        have := pot_lt (lower_le C ρ) hy (lt_of_le_of_ne (lower_le C ρ y) ne)
        omega
  | succ n ih =>
      intro ρ hpot x
      by_cases h : ∀ y ∈ LevelStore.varList C, lower C ρ y = ρ y
      · have fix : lower C ρ = ρ := funext fun y =>
          if hy : y ∈ LevelStore.varList C then h y hy else lower_off hy ρ
        rw [iterLower_of_fix fix, fix]
      · obtain ⟨y, hy, ne⟩ : ∃ y ∈ LevelStore.varList C, lower C ρ y ≠ ρ y := by
          by_contra none
          exact h fun y hy => by
            by_contra ne
            exact none ⟨y, hy, ne⟩
        have := pot_lt (lower_le C ρ) hy (lt_of_le_of_ne (lower_le C ρ y) ne)
        exact ih (lower C ρ) (by omega) x

/-! ## Tabulated rounds -/

/-- A round tabulated over the listed variables: computed once per variable. -/
def tab (V : List Nat) (f : Nat → Nat) : Nat → Nat :=
  let t := V.zip (V.map f)
  fun x => (t.lookup x).getD (f x)

theorem lookup_zip_map (f : Nat → Nat) (x : Nat) :
    ∀ (V : List Nat) (y : Nat), (V.zip (V.map f)).lookup x = some y → y = f x
  | [], _, h => by simp at h
  | a :: V, y, h => by
      simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons] at h
      split at h
      · rename_i hxa
        cases h
        rw [beq_iff_eq.mp hxa]
      · exact lookup_zip_map f x V y h

/-- **A tabulated round is the same function.** -/
theorem tab_eq (V : List Nat) (f : Nat → Nat) : tab V f = f := by
  funext x
  unfold tab
  cases h : (V.zip (V.map f)).lookup x with
  | none => rfl
  | some y => exact lookup_zip_map f x V y h

/-- `n` tabulated rounds of lowering. -/
def iterTab (C : LevelStore) : Nat → (Nat → Nat) → (Nat → Nat)
  | 0, ρ => ρ
  | n + 1, ρ => iterTab C n (tab (LevelStore.varList C).dedup (lower C ρ))

theorem iterTab_eq (C : LevelStore) : ∀ (n : Nat) (ρ : Nat → Nat), iterTab C n ρ = iterLower C n ρ
  | 0, _ => rfl
  | n + 1, ρ => by
      show iterTab C n (tab _ (lower C ρ)) = iterLower C n (lower C ρ)
      rw [tab_eq]
      exact iterTab_eq C n (lower C ρ)

/-- **The level solver to run**: lower from the bound, then check once. -/
def lowerSat (C : LevelStore) : Bool :=
  let B := LevelStore.bound C
  let ρ := iterTab C ((LevelStore.varList C).length * B) (fun _ => B)
  C.all fun c => decide (c.Holds ρ)

theorem pot_const (V : List Nat) (B : Nat) : pot V (fun _ => B) = V.length * B := by
  induction V with
  | nil => simp [pot]
  | cons a V ih =>
      simp only [pot, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      rw [ih, Nat.succ_mul]
      omega

/-- **The level solver to run is sound and complete.** -/
theorem lowerSat_iff (C : LevelStore) : lowerSat C = true ↔ LevelStore.Satisfiable C := by
  unfold lowerSat
  simp only [iterTab_eq]
  constructor
  · intro all
    refine ⟨iterLower C ((LevelStore.varList C).length * LevelStore.bound C)
      (fun _ => LevelStore.bound C), fun c hc => ?_⟩
    exact of_decide_eq_true (List.all_eq_true.mp all c hc)
  · intro sat
    obtain ⟨σ, bounded, satσ⟩ := (LevelStore.satisfiable_iff_bounded C).mp sat
    refine List.all_eq_true.mpr fun c hc => decide_eq_true ?_
    apply fixpoint_solves (σ := σ)
    · exact iterLower_fix C _ _ (by rw [pot_const])
    · exact satσ
    · exact le_iterLower satσ _ _ bounded
    · exact hc

/-- The two decisions agree. -/
theorem lowerSat_eq_decideSat (C : LevelStore) : lowerSat C = decideSat C := by
  cases h : decideSat C with
  | true => exact (lowerSat_iff C).mpr ((decideSat_iff C).mp h)
  | false =>
      cases h' : lowerSat C with
      | true =>
          have := (decideSat_iff C).mpr ((lowerSat_iff C).mp h')
          rw [h] at this
          cases this
      | false => rfl

/-! ## Cost: the lowering steps `lowerSat` makes -/

/-- The unary size of a level: closed levels and successors are counted in unary. -/
def Level.usize : Level → Nat
  | .const c => c + 1
  | .param _ => 1
  | .succ l => Level.usize l + 1
  | .max l m => Level.usize l + Level.usize m + 1

/-- The unary size of a constraint. -/
def LevelLe.usize (c : LevelLe) : Nat := Level.usize c.lhs + Level.usize c.rhs

/-- The unary size of a store. -/
def LevelStore.usize (C : LevelStore) : Nat := (C.map LevelLe.usize).sum

theorem Level.depth_lt_usize : ∀ l : Level, Level.depth l < Level.usize l
  | .const _ => by simp [Level.depth, Level.usize]
  | .param _ => by simp [Level.depth, Level.usize]
  | .succ l => by
      have := Level.depth_lt_usize l
      simp only [Level.depth, Level.usize]
      omega
  | .max l m => by
      have := Level.depth_lt_usize l
      have := Level.depth_lt_usize m
      simp only [Level.depth, Level.usize]
      omega

theorem Level.varList_length_le_usize : ∀ l : Level, (Level.varList l).length ≤ Level.usize l
  | .const _ => by simp [Level.varList, Level.usize]
  | .param _ => by simp [Level.varList, Level.usize]
  | .succ l => by
      have := Level.varList_length_le_usize l
      simp only [Level.varList, Level.usize]
      omega
  | .max l m => by
      have := Level.varList_length_le_usize l
      have := Level.varList_length_le_usize m
      simp only [Level.varList, Level.usize, List.length_append]
      omega

namespace LevelStore

theorem usize_cons (c : LevelLe) (C : LevelStore) : usize (c :: C) = c.usize + usize C := by
  simp [usize]

theorem varList_length_le_usize : ∀ C : LevelStore, (varList C).length ≤ usize C
  | [] => by simp [varList, usize]
  | c :: C => by
      have := varList_length_le_usize C
      have := Level.varList_length_le_usize c.lhs
      have := Level.varList_length_le_usize c.rhs
      simp only [varList, LevelLe.varList, List.length_append, usize_cons, LevelLe.usize]
      omega

theorem depth_le_usize : ∀ C : LevelStore, depth C ≤ usize C
  | [] => by simp [depth, usize]
  | c :: C => by
      have := depth_le_usize C
      have := Level.depth_lt_usize c.lhs
      have := Level.depth_lt_usize c.rhs
      simp only [depth, LevelLe.depth, usize_cons, LevelLe.usize]
      omega

theorem length_le_usize : ∀ C : LevelStore, C.length ≤ usize C
  | [] => by simp [usize]
  | c :: C => by
      have := length_le_usize C
      have := Level.depth_lt_usize c.lhs
      simp only [List.length_cons, usize_cons, LevelLe.usize]
      omega

theorem bound_le_usize (C : LevelStore) : bound C ≤ (usize C + 1) * (usize C + 1) := by
  have card : (vars C).card ≤ usize C :=
    le_trans (List.toFinset_card_le _) (varList_length_le_usize C)
  have deep := depth_le_usize C
  exact Nat.mul_le_mul (by omega) (by omega)

end LevelStore

/-- A left fold that counts its steps. -/
def foldlCounted {α β : Type} (f : β → α → β) : List α → β → Nat → β × Nat
  | [], b, n => (b, n)
  | a :: as, b, n => foldlCounted f as (f b a) (n + 1)

theorem foldlCounted_eq {α β : Type} (f : β → α → β) :
    ∀ (as : List α) (b : β) (n : Nat), foldlCounted f as b n = (as.foldl f b, n + as.length)
  | [], _, _ => rfl
  | a :: as, b, n => by
      simp only [foldlCounted, foldlCounted_eq f as, List.foldl_cons, List.length_cons,
        Prod.mk.injEq, true_and]
      omega

theorem sum_map_const {α : Type} (k : Nat) : ∀ V : List α, (V.map fun _ => k).sum = V.length * k
  | [] => by simp
  | _ :: V => by
      simp only [List.map_cons, List.sum_cons, List.length_cons, sum_map_const k V, Nat.add_mul,
        Nat.one_mul]
      omega

/-- **One round of lowering, counted**: the round tabulates each variable of the store by one pass
over the store, and the pass makes one lowering step per constraint. -/
def lowerCounted (C : LevelStore) (ρ : Nat → Nat) : (Nat → Nat) × Nat :=
  let V := (LevelStore.varList C).dedup
  let passes := V.map fun x => foldlCounted (lowerStep ρ x) C (ρ x) 0
  (fun x => ((V.zip (passes.map Prod.fst)).lookup x).getD (lower C ρ x),
    (passes.map Prod.snd).sum)

theorem lowerCounted_fst (C : LevelStore) (ρ : Nat → Nat) :
    (lowerCounted C ρ).1 = tab (LevelStore.varList C).dedup (lower C ρ) := by
  have passes : (((LevelStore.varList C).dedup.map
      fun x => foldlCounted (lowerStep ρ x) C (ρ x) 0).map Prod.fst) =
      (LevelStore.varList C).dedup.map (lower C ρ) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x _
    simp [foldlCounted_eq, lower]
  simp only [lowerCounted, tab, passes]

theorem lowerCounted_snd (C : LevelStore) (ρ : Nat → Nat) :
    (lowerCounted C ρ).2 = (LevelStore.varList C).dedup.length * C.length := by
  have passes : (((LevelStore.varList C).dedup.map
      fun x => foldlCounted (lowerStep ρ x) C (ρ x) 0).map Prod.snd) =
      (LevelStore.varList C).dedup.map fun _ => C.length := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x _
    simp [foldlCounted_eq]
  simp only [lowerCounted, passes, sum_map_const]

/-- `n` rounds of lowering, counted. -/
def iterCounted (C : LevelStore) : Nat → (Nat → Nat) → Nat → (Nat → Nat) × Nat
  | 0, ρ, k => (ρ, k)
  | n + 1, ρ, k => iterCounted C n (lowerCounted C ρ).1 (k + (lowerCounted C ρ).2)

theorem iterCounted_eq (C : LevelStore) : ∀ (n : Nat) (ρ : Nat → Nat) (k : Nat),
    iterCounted C n ρ k =
      (iterTab C n ρ, k + n * ((LevelStore.varList C).dedup.length * C.length))
  | 0, _, _ => by simp [iterCounted, iterTab]
  | n + 1, ρ, k => by
      rw [iterCounted, lowerCounted_fst, lowerCounted_snd, iterCounted_eq C n]
      simp only [iterTab, Prod.mk.injEq, true_and, Nat.add_mul, Nat.one_mul]
      omega

/-- **`lowerSat`, counted**: the lowering steps of its rounds, then one check per constraint. -/
def lowerSatCounted (C : LevelStore) : Bool × Nat :=
  let B := LevelStore.bound C
  let r := iterCounted C ((LevelStore.varList C).length * B) (fun _ => B) 0
  (C.all fun c => decide (c.Holds r.1), r.2 + C.length)

/-- The counted copy computes `lowerSat`. -/
theorem lowerSatCounted_fst (C : LevelStore) : (lowerSatCounted C).1 = lowerSat C := by
  simp only [lowerSatCounted, lowerSat, iterCounted_eq]

/-- **The exact count**: `|V| · B` rounds of `|V'| · |C|` lowering steps, then `|C|` checks. -/
theorem lowerSatCounted_snd (C : LevelStore) :
    (lowerSatCounted C).2 =
      (LevelStore.varList C).length * LevelStore.bound C *
        ((LevelStore.varList C).dedup.length * C.length) + C.length := by
  simp only [lowerSatCounted, iterCounted_eq, Nat.zero_add]

/-- **The level solver to run makes polynomially many lowering steps in the unary size**: at most
`s³ (s + 1)² + s`, for `s` the unary size of the store. -/
theorem lowerSat_cost (C : LevelStore) :
    (lowerSatCounted C).2 ≤
      LevelStore.usize C ^ 3 * (LevelStore.usize C + 1) ^ 2 + LevelStore.usize C := by
  rw [lowerSatCounted_snd]
  have hV := LevelStore.varList_length_le_usize C
  have hB := LevelStore.bound_le_usize C
  have hD : (LevelStore.varList C).dedup.length ≤ LevelStore.usize C :=
    le_trans (List.dedup_sublist _).length_le hV
  have hC := LevelStore.length_le_usize C
  calc (LevelStore.varList C).length * LevelStore.bound C *
          ((LevelStore.varList C).dedup.length * C.length) + C.length
      ≤ LevelStore.usize C * ((LevelStore.usize C + 1) * (LevelStore.usize C + 1)) *
          (LevelStore.usize C * LevelStore.usize C) + LevelStore.usize C :=
        Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul hV hB) (Nat.mul_le_mul hD hC)) hC
    _ = LevelStore.usize C ^ 3 * (LevelStore.usize C + 1) ^ 2 + LevelStore.usize C := by ring

/-- Positive control: `u ≤ 1` is satisfiable; one variable occurrence, bound `4`, so four rounds of
one step and one check. -/
theorem counted_satisfiable : lowerSatCounted [⟨.param 0, .const 1⟩] = (true, 5) := by decide

/-- Negative control: `u + 1 ≤ u` is unsatisfiable; two occurrences of one variable, bound `4`, so
eight rounds of one step and one check. -/
theorem counted_unsatisfiable : lowerSatCounted [⟨.succ (.param 0), .param 0⟩] = (false, 9) := by
  decide

#print axioms Level.value_le_iff
#print axioms le_lower
#print axioms fixpoint_solves
#print axioms iterLower_fix
#print axioms tab_eq
#print axioms lowerSat_iff
#print axioms lowerSat_eq_decideSat
#print axioms lowerSatCounted_fst
#print axioms lowerSatCounted_snd
#print axioms lowerSat_cost
#print axioms counted_satisfiable
#print axioms counted_unsatisfiable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
