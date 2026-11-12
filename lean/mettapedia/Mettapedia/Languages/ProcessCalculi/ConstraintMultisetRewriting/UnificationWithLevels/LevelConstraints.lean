import Mettapedia.TypeTheory.UniverseLevel.Algebra

/-!
# Level constraints over the natural numbers: satisfiability decided

Levels are the expressions of `LevelExpr ℕ`: closed levels, level variables, successor and
maximum. `imax` is not included: no rule of the unifier needs a level that collapses at a
proposition. Cumulativity is a constraint `u ≤ v` between levels (`LevelLe`). A store of level
constraints is satisfiable when one valuation of its variables in ℕ satisfies all of them.

**Small models.** A satisfiable store is satisfied by a valuation bounded by
`(number of variables + 1) * (largest depth + 1)` (`LevelStore.satisfiable_iff_bounded`). The proof
squeezes any solution: it counts, below each value, the points that lie at most the largest depth
above zero or above a value of a variable. The squeeze is monotone (`squeeze_mono`), it keeps every
difference up to the largest depth (`squeeze_add`), and every level commutes with it
(`value_squeeze`), so every constraint survives.

**Decision.** `decideSat` searches the bounded valuations of the variables of the store; it is
sound and complete (`decideSat_iff`). Entailment `C ⊨ u ≤ v` reduces to it, because over ℕ the
negation of `u ≤ v` is `v + 1 ≤ u` (`LevelStore.entails_iff`). The search is exponential in the
number of variables: it is the decision and the specification, not the solver to run (the
pseudo-polynomial lowering to the greatest bounded solution is the solver to build on it).

**As equations.** `u ≤ v` holds exactly when `max u v = v` (`LevelLe.holds_iff_max_eq`), so a
postponed level constraint is an ordinary equation of level terms in a store of equations.

Positive examples: `0 ≤ 1`; `u ≤ v` together with `v ≤ max u 1`; `a ≤ b` and then `b ≤ a`.
Negative examples: `u + 1 ≤ u`; `1 ≤ 0`; `u + 1 ≤ v` together with `v + 1 ≤ u`; and `a ≤ b` does
not entail `b ≤ a`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

open Mettapedia.TypeTheory.UniverseLevel

/-- Levels: closed levels, variables, successor and maximum, over ℕ. -/
abbrev Level := LevelExpr Nat

namespace Level

/-- The value of a level under a valuation of its variables. -/
abbrev value (v : Nat → Nat) (l : Level) : Nat := LevelExpr.eval v l

@[simp] theorem value_const (v : Nat → Nat) (c : Nat) : value v (.const c) = c := rfl
@[simp] theorem value_param (v : Nat → Nat) (i : Nat) : value v (.param i) = v i := rfl
@[simp] theorem value_succ (v : Nat → Nat) (l : Level) : value v (.succ l) = value v l + 1 := rfl
@[simp] theorem value_max (v : Nat → Nat) (l m : Level) :
    value v (.max l m) = max (value v l) (value v m) := rfl

/-- The variables of a level, with repetitions. -/
def varList : Level → List Nat
  | .const _ => []
  | .param i => [i]
  | .succ l => varList l
  | .max l m => varList l ++ varList m

/-- How far a level reaches above a variable or above zero: its largest successor offset, a
closed level `c` counting as `c` steps above zero. -/
def depth : Level → Nat
  | .const c => c
  | .param _ => 0
  | .succ l => depth l + 1
  | .max l m => max (depth l) (depth m)

/-- A level depends only on its variables. -/
theorem value_congr {v w : Nat → Nat} :
    ∀ l : Level, (∀ i ∈ varList l, v i = w i) → value v l = value w l
  | .const _, _ => rfl
  | .param i, h => h i (by simp [varList])
  | .succ l, h => by
      simp only [value_succ]
      rw [value_congr l h]
  | .max l m, h => by
      simp only [value_max]
      rw [value_congr l (fun i hi => h i (List.mem_append_left _ hi)),
        value_congr m (fun i hi => h i (List.mem_append_right _ hi))]

end Level

/-- A level constraint `lhs ≤ rhs`. Equality is two constraints; `lhs < rhs` is
`succ lhs ≤ rhs`. -/
structure LevelLe where
  lhs : Level
  rhs : Level
  deriving DecidableEq, Repr

namespace LevelLe

/-- A valuation satisfies the constraint. -/
def Holds (v : Nat → Nat) (c : LevelLe) : Prop := Level.value v c.lhs ≤ Level.value v c.rhs

instance (v : Nat → Nat) (c : LevelLe) : Decidable (c.Holds v) :=
  inferInstanceAs (Decidable (_ ≤ _))

def varList (c : LevelLe) : List Nat := Level.varList c.lhs ++ Level.varList c.rhs

def depth (c : LevelLe) : Nat := max (Level.depth c.lhs) (Level.depth c.rhs)

/-- **A level constraint is an equation of levels**: `u ≤ v` holds exactly when `max u v = v`. -/
theorem holds_iff_max_eq (v : Nat → Nat) (c : LevelLe) :
    c.Holds v ↔ Level.value v (.max c.lhs c.rhs) = Level.value v c.rhs := by
  simp only [Holds, Level.value_max]
  exact max_eq_right_iff.symm

end LevelLe

/-- A store of level constraints. -/
abbrev LevelStore := List LevelLe

namespace LevelStore

/-- A valuation satisfies every constraint of the store. -/
def Satisfies (v : Nat → Nat) (C : LevelStore) : Prop := ∀ c ∈ C, c.Holds v

/-- Some valuation in ℕ satisfies the store. -/
def Satisfiable (C : LevelStore) : Prop := ∃ v : Nat → Nat, Satisfies v C

/-- Every valuation that satisfies the store satisfies the constraint. -/
def Entails (C : LevelStore) (c : LevelLe) : Prop := ∀ v : Nat → Nat, Satisfies v C → c.Holds v

def varList : LevelStore → List Nat
  | [] => []
  | c :: C => c.varList ++ varList C

/-- The variables of the store. -/
def vars (C : LevelStore) : Finset Nat := (varList C).toFinset

def depth : LevelStore → Nat
  | [] => 0
  | c :: C => max c.depth (depth C)

/-- The small-model bound. -/
def bound (C : LevelStore) : Nat := ((vars C).card + 1) * (depth C + 1)

theorem varList_of_mem {C : LevelStore} {c : LevelLe} (hc : c ∈ C) {i : Nat}
    (hi : i ∈ c.varList) : i ∈ varList C := by
  induction C with
  | nil => cases hc
  | cons d C ih =>
      rcases List.mem_cons.mp hc with rfl | hc
      · exact List.mem_append_left _ hi
      · exact List.mem_append_right _ (ih hc)

theorem depth_of_mem {C : LevelStore} {c : LevelLe} (hc : c ∈ C) : c.depth ≤ depth C := by
  induction C with
  | nil => cases hc
  | cons d C ih =>
      rcases List.mem_cons.mp hc with rfl | hc
      · exact le_max_left _ _
      · exact le_trans (ih hc) (le_max_right _ _)

end LevelStore

/-! ## The squeeze -/

namespace Squeeze

/-- A point is covered when it lies at most `K` above some anchor. -/
def Covered (A : Finset Nat) (K t : Nat) : Prop := ∃ s ∈ A, s ≤ t ∧ t ≤ s + K

instance (A : Finset Nat) (K t : Nat) : Decidable (Covered A K t) := by
  unfold Covered
  infer_instance

/-- The number of covered points below `x`. -/
def squeeze (A : Finset Nat) (K x : Nat) : Nat :=
  ((Finset.range x).filter (Covered A K)).card

theorem squeeze_zero (A : Finset Nat) (K : Nat) : squeeze A K 0 = 0 := by
  simp [squeeze]

theorem squeeze_succ (A : Finset Nat) (K x : Nat) :
    squeeze A K (x + 1) = squeeze A K x + if Covered A K x then 1 else 0 := by
  unfold squeeze
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    simp
  · simp

/-- The squeeze keeps the order. -/
theorem squeeze_mono (A : Finset Nat) (K : Nat) : Monotone (squeeze A K) := by
  intro x y h
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr h))

/-- Up to `K + 1` above an anchor, the squeeze keeps every difference. -/
theorem squeeze_add {A : Finset Nat} {K s x : Nat} (hs : s ∈ A) (hx : s ≤ x) :
    ∀ d : Nat, x + d ≤ s + K + 1 → squeeze A K (x + d) = squeeze A K x + d
  | 0, _ => rfl
  | d + 1, h => by
      rw [← Nat.add_assoc, squeeze_succ, squeeze_add hs hx d (by omega),
        if_pos ⟨s, hs, by omega, by omega⟩]
      omega

/-- The squeeze is bounded by the number of anchors times `K + 1`. -/
theorem squeeze_le (A : Finset Nat) (K x : Nat) : squeeze A K x ≤ A.card * (K + 1) := by
  unfold squeeze
  calc ((Finset.range x).filter (Covered A K)).card
      ≤ (A.biUnion fun s => Finset.Icc s (s + K)).card := by
        apply Finset.card_le_card
        intro t ht
        obtain ⟨_, s, hs, lo, hi⟩ := Finset.mem_filter.mp ht
        exact Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_Icc.mpr ⟨lo, hi⟩⟩
    _ ≤ A.card * (K + 1) :=
        Finset.card_biUnion_le_card_mul _ _ _ (fun s _ => by rw [Nat.card_Icc]; omega)

/-- **Every level commutes with the squeeze**, for a level whose variables are among `V` and
whose depth is at most `K + 1`; and its value lies at most its depth above an anchor. -/
theorem value_squeeze {V : Finset Nat} {ρ : Nat → Nat} {K : Nat} :
    ∀ l : Level, (∀ i ∈ Level.varList l, i ∈ V) → Level.depth l ≤ K + 1 →
      (∃ s ∈ insert 0 (V.image ρ), s ≤ Level.value ρ l ∧ Level.value ρ l ≤ s + Level.depth l) ∧
      Level.value (fun i => squeeze (insert 0 (V.image ρ)) K (ρ i)) l =
        squeeze (insert 0 (V.image ρ)) K (Level.value ρ l)
  | .const c, _, hd => by
      have hd' : c ≤ K + 1 := hd
      refine ⟨⟨0, Finset.mem_insert_self _ _, Nat.zero_le _, by simp [Level.depth]⟩, ?_⟩
      have shift := squeeze_add (K := K) (Finset.mem_insert_self 0 (V.image ρ)) (le_refl 0) c
        (by omega)
      rw [Nat.zero_add, squeeze_zero, Nat.zero_add] at shift
      simp only [Level.value_const]
      exact shift.symm
  | .param i, hv, _ =>
      ⟨⟨ρ i, Finset.mem_insert_of_mem (Finset.mem_image_of_mem ρ (hv i (by simp [Level.varList]))),
        le_refl _, by simp [Level.depth]⟩, rfl⟩
  | .succ l, hv, hd => by
      have hd' : Level.depth l + 1 ≤ K + 1 := hd
      obtain ⟨⟨s, hs, lo, hi⟩, ih⟩ := value_squeeze (V := V) (ρ := ρ) (K := K) l hv (by omega)
      refine ⟨⟨s, hs, ?_, ?_⟩, ?_⟩
      · simp only [Level.value_succ]
        omega
      · simp only [Level.value_succ, Level.depth]
        omega
      · simp only [Level.value_succ]
        rw [ih, squeeze_add hs lo 1 (by omega)]
  | .max l m, hv, hd => by
      have hd' : max (Level.depth l) (Level.depth m) ≤ K + 1 := hd
      obtain ⟨⟨s, hs, lo, hi⟩, ihl⟩ := value_squeeze (V := V) (ρ := ρ) (K := K) l
        (fun i hi => hv i (List.mem_append_left _ hi)) (le_trans (le_max_left _ _) hd')
      obtain ⟨⟨s', hs', lo', hi'⟩, ihm⟩ := value_squeeze (V := V) (ρ := ρ) (K := K) m
        (fun i hi => hv i (List.mem_append_right _ hi)) (le_trans (le_max_right _ _) hd')
      refine ⟨?_, ?_⟩
      · have dl : Level.depth l ≤ Level.depth (.max l m) := le_max_left _ _
        have dm : Level.depth m ≤ Level.depth (.max l m) := le_max_right _ _
        rcases le_total (Level.value ρ l) (Level.value ρ m) with h | h
        · refine ⟨s', hs', ?_, ?_⟩
          · simp only [Level.value_max]
            exact le_trans lo' (le_max_right _ _)
          · simp only [Level.value_max]
            exact max_le (by omega) (by omega)
        · refine ⟨s, hs, ?_, ?_⟩
          · simp only [Level.value_max]
            exact le_trans lo (le_max_left _ _)
          · simp only [Level.value_max]
            exact max_le (by omega) (by omega)
      · simp only [Level.value_max]
        rw [ihl, ihm, (squeeze_mono _ _).map_max]

end Squeeze

open Squeeze

namespace LevelStore

/-- **Small models**: a satisfiable store has a solution bounded by `bound`. -/
theorem satisfiable_iff_bounded (C : LevelStore) :
    Satisfiable C ↔ ∃ v : Nat → Nat, (∀ i, v i ≤ bound C) ∧ Satisfies v C := by
  constructor
  · rintro ⟨ρ, sat⟩
    refine ⟨fun i => squeeze (insert 0 ((vars C).image ρ)) (depth C) (ρ i), fun i => ?_,
      fun c hc => ?_⟩
    · calc squeeze (insert 0 ((vars C).image ρ)) (depth C) (ρ i)
          ≤ (insert 0 ((vars C).image ρ)).card * (depth C + 1) := squeeze_le _ _ _
        _ ≤ ((vars C).card + 1) * (depth C + 1) := by
          apply Nat.mul_le_mul_right
          exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le 1)
    · have inside : ∀ (l : Level), (∀ i ∈ Level.varList l, i ∈ c.varList) →
          ∀ i ∈ Level.varList l, i ∈ vars C := fun l sub i hi =>
        List.mem_toFinset.mpr (varList_of_mem hc (sub i hi))
      have dc := depth_of_mem hc
      have dl : Level.depth c.lhs ≤ depth C + 1 := by
        have : Level.depth c.lhs ≤ c.depth := le_max_left _ _
        omega
      have dr : Level.depth c.rhs ≤ depth C + 1 := by
        have : Level.depth c.rhs ≤ c.depth := le_max_right _ _
        omega
      obtain ⟨_, el⟩ := value_squeeze (ρ := ρ) c.lhs
        (inside c.lhs (fun i hi => List.mem_append_left _ hi)) dl
      obtain ⟨_, er⟩ := value_squeeze (ρ := ρ) c.rhs
        (inside c.rhs (fun i hi => List.mem_append_right _ hi)) dr
      show Level.value _ c.lhs ≤ Level.value _ c.rhs
      rw [el, er]
      exact squeeze_mono _ _ (sat c hc)
  · rintro ⟨v, _, sat⟩
    exact ⟨v, sat⟩

/-- The negation of `u ≤ v` over ℕ: `v + 1 ≤ u`. -/
def negation (c : LevelLe) : LevelLe := ⟨.succ c.rhs, c.lhs⟩

/-- **Entailment is refutation of the negation.** -/
theorem entails_iff (C : LevelStore) (c : LevelLe) :
    Entails C c ↔ ¬ Satisfiable (negation c :: C) := by
  constructor
  · rintro entails ⟨v, sat⟩
    have holds := entails v (fun d hd => sat d (List.mem_cons_of_mem _ hd))
    have flipped : (negation c).Holds v := sat _ List.mem_cons_self
    simp only [negation, LevelLe.Holds, Level.value_succ] at flipped
    exact absurd holds (by simp only [LevelLe.Holds]; omega)
  · intro none v sat
    by_contra fails
    apply none
    refine ⟨v, fun d hd => ?_⟩
    rcases List.mem_cons.mp hd with rfl | hd
    · simp only [negation, LevelLe.Holds, Level.value_succ]
      simp only [LevelLe.Holds] at fails
      omega
    · exact sat d hd

end LevelStore

/-! ## The decision -/

/-- All valuations of the listed variables by values at most `B`; other variables are `0`. -/
def assignments (B : Nat) : List Nat → List (Nat → Nat)
  | [] => [fun _ => 0]
  | i :: rest =>
      (List.range (B + 1)).flatMap fun k => (assignments B rest).map fun w => Function.update w i k

theorem exists_assignment (B : Nat) (v : Nat → Nat) (hv : ∀ i, v i ≤ B) :
    ∀ vs : List Nat, ∃ w ∈ assignments B vs, ∀ i ∈ vs, w i = v i
  | [] => ⟨fun _ => 0, by simp [assignments], by simp⟩
  | i :: rest => by
      obtain ⟨w, hw, agree⟩ := exists_assignment B v hv rest
      refine ⟨Function.update w i (v i), ?_, ?_⟩
      · simp only [assignments, List.mem_flatMap, List.mem_range, List.mem_map]
        exact ⟨v i, Nat.lt_succ_of_le (hv i), w, hw, rfl⟩
      · intro j hj
        by_cases h : j = i
        · subst h
          simp
        · rw [Function.update_of_ne h]
          exact agree j ((List.mem_cons.mp hj).resolve_left h)

/-- **The decision**: search the bounded valuations of the store's variables. -/
def decideSat (C : LevelStore) : Bool :=
  (assignments (LevelStore.bound C) (LevelStore.varList C).dedup).any fun w =>
    C.all fun c => decide (c.Holds w)

/-- **The decision is sound and complete.** -/
theorem decideSat_iff (C : LevelStore) : decideSat C = true ↔ LevelStore.Satisfiable C := by
  unfold decideSat
  rw [List.any_eq_true]
  constructor
  · rintro ⟨w, _, all⟩
    refine ⟨w, fun c hc => ?_⟩
    have := List.all_eq_true.mp all c hc
    exact of_decide_eq_true this
  · intro sat
    obtain ⟨v, bounded, satV⟩ := (LevelStore.satisfiable_iff_bounded C).mp sat
    obtain ⟨w, hw, agree⟩ := exists_assignment _ v bounded (LevelStore.varList C).dedup
    refine ⟨w, hw, List.all_eq_true.mpr fun c hc => decide_eq_true ?_⟩
    have same : ∀ l : Level, (∀ i ∈ Level.varList l, i ∈ c.varList) →
        Level.value w l = Level.value v l :=
      fun l sub => Level.value_congr l fun i hi =>
        agree i (List.mem_dedup.mpr (LevelStore.varList_of_mem hc (sub i hi)))
    show Level.value w c.lhs ≤ Level.value w c.rhs
    rw [same c.lhs (fun i hi => List.mem_append_left _ hi),
      same c.rhs (fun i hi => List.mem_append_right _ hi)]
    exact satV c hc

instance (C : LevelStore) : Decidable (LevelStore.Satisfiable C) :=
  decidable_of_iff _ (decideSat_iff C)

instance (C : LevelStore) (c : LevelLe) : Decidable (LevelStore.Entails C c) :=
  decidable_of_iff _ (LevelStore.entails_iff C c).symm

/-! ## Controls -/

namespace LevelControls

/-- The level variables `a`, `u` (index 0) and `b`, `v` (index 1). -/
abbrev a : Level := .param 0
abbrev b : Level := .param 1

/-- Positive: `0 ≤ 1` is satisfiable. -/
theorem zero_le_one : LevelStore.Satisfiable [⟨.const 0, .const 1⟩] := by decide

/-- Positive: `u ≤ v` with `v ≤ max u 1`. -/
theorem le_and_bounded : LevelStore.Satisfiable [⟨a, b⟩, ⟨b, .max a (.const 1)⟩] := by decide

/-- Positive: cumulativity `a ≤ b` together with `b ≤ a`. -/
theorem cross_both : LevelStore.Satisfiable [⟨a, b⟩, ⟨b, a⟩] := by decide

/-- Negative: `u + 1 ≤ u` has no solution. -/
theorem succ_le_self : ¬ LevelStore.Satisfiable [⟨.succ a, a⟩] := by decide

/-- Negative: `1 ≤ 0` has no solution. -/
theorem one_le_zero : ¬ LevelStore.Satisfiable [⟨.const 1, .const 0⟩] := by decide

/-- Negative: a strict cycle has no solution. -/
theorem strict_cycle : ¬ LevelStore.Satisfiable [⟨.succ a, b⟩, ⟨.succ b, a⟩] := by decide

/-- Negative: cumulativity `a ≤ b` does not entail `b ≤ a`. -/
theorem cross_not_entailed : ¬ LevelStore.Entails [⟨a, b⟩] ⟨b, a⟩ := by decide

/-- Positive: `a ≤ b` and `b ≤ a` entail `a = b` read as `max a b ≤ a`. -/
theorem cross_entailed : LevelStore.Entails [⟨a, b⟩, ⟨b, a⟩] ⟨.max a b, a⟩ := by decide

end LevelControls

#print axioms LevelStore.satisfiable_iff_bounded
#print axioms decideSat_iff
#print axioms LevelStore.entails_iff
#print axioms LevelLe.holds_iff_max_eq
#print axioms LevelControls.cross_not_entailed
#print axioms LevelControls.strict_cycle

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
