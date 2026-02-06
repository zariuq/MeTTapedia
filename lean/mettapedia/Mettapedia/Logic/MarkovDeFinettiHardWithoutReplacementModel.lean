import Mettapedia.Logic.MarkovDeFinettiHardWithoutReplacement
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Count
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Markov de Finetti (Hard Direction) — Without‑replacement model

This file defines a simple finite‑population sampling model and proves a
basic without‑replacement vs with‑replacement step bound. It is designed to be
instantiated later for excursion‑type sampling in the Diaconis–Freedman core.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped BigOperators

namespace MarkovDeFinettiHardWithoutReplacementModel

variable {α : Type*} [DecidableEq α]

/-- Probability weight `c/R`, with the convention `0/0 = 0`. -/
def probWeight (c R : ℕ) : ℝ :=
  if R = 0 then 0 else (c : ℝ) / (R : ℝ)

lemma probWeight_nonneg (c R : ℕ) : 0 ≤ probWeight c R := by
  by_cases h : R = 0
  · simp [probWeight, h]
  · have : (0:ℝ) ≤ (c:ℝ) / (R:ℝ) := by
      have hR : (0:ℝ) < (R:ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero h
      exact div_nonneg (by exact_mod_cast (Nat.zero_le _)) (le_of_lt hR)
    simp [probWeight, h, this]

lemma probWeight_le_one (c R : ℕ) (hc : c ≤ R) : probWeight c R ≤ 1 := by
  by_cases h : R = 0
  · simp [probWeight, h]
  · have hR : (0:ℝ) < (R:ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero h
    have hdiv : (c:ℝ) / (R:ℝ) ≤ 1 := by
      exact (div_le_one hR).2 (by exact_mod_cast hc)
    simp [probWeight, h, hdiv]

/-- With‑replacement product probability for a list, using the empirical distribution of `ms`. -/
def wrProb (ms : Multiset α) (xs : List α) : ℝ :=
  let R := ms.card
  (xs.map (fun a => probWeight (ms.count a) R)).prod

/-- Without‑replacement product probability for a list, sampling sequentially from `ms`. -/
def worProb : Multiset α → List α → ℝ
  | _, [] => 1
  | ms, a :: xs =>
      let R := ms.card
      let c := ms.count a
      probWeight c R * worProb (ms.erase a) xs

/-- Step probabilities used to form `worProb` (with a fixed base multiset `ms0`). -/
def stepPairs (ms0 : Multiset α) : Multiset α → List α → List (ℝ × ℝ)
  | _, [] => []
  | ms, a :: xs =>
      let R := ms.card
      let c := ms.count a
      let p := probWeight c R
      let q := probWeight (ms0.count a) (ms0.card)
      (p, q) :: stepPairs ms0 (ms.erase a) xs

lemma worProb_eq_prod_stepPairs (ms0 ms : Multiset α) (xs : List α) :
    worProb ms xs = List.prod ((stepPairs ms0 ms xs).map Prod.fst) := by
  induction xs generalizing ms with
  | nil =>
      simp [worProb, stepPairs]
  | cons a xs ih =>
      simp [worProb, stepPairs, ih (ms := ms.erase a), List.prod_cons]

@[simp] lemma length_stepPairs (ms0 ms : Multiset α) (xs : List α) :
    (stepPairs ms0 ms xs).length = xs.length := by
  induction xs generalizing ms with
  | nil =>
      simp [stepPairs]
  | cons a xs ih =>
      simpa [stepPairs] using (ih (ms := ms.erase a))

lemma stepPairs_snd (ms0 ms : Multiset α) (xs : List α) :
    (stepPairs ms0 ms xs).map Prod.snd =
      xs.map (fun a => probWeight (ms0.count a) ms0.card) := by
  induction xs generalizing ms with
  | nil =>
      simp [stepPairs]
  | cons a xs ih =>
      simp [stepPairs, ih (ms := ms.erase a)]

lemma wrProb_eq_prod_stepPairs (ms0 ms : Multiset α) (xs : List α) :
    wrProb ms0 xs = List.prod ((stepPairs ms0 ms xs).map Prod.snd) := by
  simp [wrProb, stepPairs_snd]

/-- A crude one‑step bound for the without‑replacement vs with‑replacement
probability at a single step, assuming a large population. -/
lemma stepProb_bound
    (R L t : ℕ) (c u : ℕ)
    (hR : 2 * L ≤ R) (ht : t ≤ L) (hu : u ≤ t) (hc : c ≤ R) :
    |((c - u : ℝ) / (R - t : ℝ)) - (c : ℝ) / (R : ℝ)| ≤ (4 * (L : ℝ)) / (R : ℝ) := by
  by_cases hL0 : L = 0
  · subst hL0
    have ht' : t = 0 := by exact Nat.le_zero.mp (by simpa using ht)
    subst ht'
    have hu' : u = 0 := by
      exact Nat.le_zero.mp (by simpa using hu)
    by_cases hR0 : R = 0
    · simp [hR0]
    · simp [hu']  -- both fractions are `c/R`
  -- now L > 0, hence R > 0 and R - t > 0
  have hRpos : 0 < R := by
    have : 0 < 2 * L := Nat.mul_pos (by decide) (Nat.pos_of_ne_zero hL0)
    exact lt_of_lt_of_le this hR
  have hRt : (0:ℝ) < (R - t : ℝ) := by
    have hL1 : L + 1 ≤ 2 * L := by nlinarith [Nat.pos_of_ne_zero hL0]
    have hLR : L + 1 ≤ R := le_trans hL1 hR
    have hLt : L < R := lt_of_lt_of_le (Nat.lt_succ_self L) hLR
    have hRt_lt : t < R := lt_of_le_of_lt ht hLt
    have hRt_le : t ≤ R := le_of_lt hRt_lt
    have hRt_real : (0:ℝ) < (R:ℝ) - (t:ℝ) := by
      exact sub_pos_of_lt (by exact_mod_cast hRt_lt)
    simpa [Nat.cast_sub hRt_le] using hRt_real
  -- coarse bound: |(c-u)/(R-t) - c/R| ≤ 2t/(R-t)
  have hnum : |((c - u : ℝ) / (R - t : ℝ)) - (c : ℝ) / (R : ℝ)| ≤ (2 * (t:ℝ)) / (R - t : ℝ) := by
    have hRpos' : (0:ℝ) < (R:ℝ) := by exact_mod_cast hRpos
    have hRt' : (0:ℝ) < (R - t : ℝ) := hRt
    -- rewrite the difference
    have h1 :
        ((c - u : ℝ) / (R - t : ℝ)) - (c : ℝ) / (R : ℝ) =
          ((c:ℝ) * (t:ℝ) - (u:ℝ) * (R:ℝ)) / ((R:ℝ) * (R - t : ℝ)) := by
      field_simp [hRpos'.ne', hRt'.ne']
      ring_nf
    -- bound numerator
    have hc' : (c:ℝ) ≤ (R:ℝ) := by exact_mod_cast hc
    have hu' : (u:ℝ) ≤ (t:ℝ) := by exact_mod_cast hu
    have hnum' : |(c:ℝ) * (t:ℝ) - (u:ℝ) * (R:ℝ)| ≤ (2:ℝ) * (t:ℝ) * (R:ℝ) := by
      calc
        |(c:ℝ) * (t:ℝ) - (u:ℝ) * (R:ℝ)|
            = |(c:ℝ) * (t:ℝ) + (-(u:ℝ) * (R:ℝ))| := by ring_nf
        _ ≤ |(c:ℝ) * (t:ℝ)| + |-(u:ℝ) * (R:ℝ)| := by
            simpa using abs_add_le ( (c:ℝ) * (t:ℝ) ) (-(u:ℝ) * (R:ℝ))
        _ = (c:ℝ) * (t:ℝ) + (u:ℝ) * (R:ℝ) := by
            simp [abs_of_nonneg, mul_nonneg, (by exact_mod_cast (Nat.zero_le c) : (0:ℝ) ≤ (c:ℝ)),
              (by exact_mod_cast (Nat.zero_le t) : (0:ℝ) ≤ (t:ℝ)),
              (by exact_mod_cast (Nat.zero_le u) : (0:ℝ) ≤ (u:ℝ)),
              (by exact_mod_cast (Nat.zero_le R) : (0:ℝ) ≤ (R:ℝ))]
        _ ≤ (R:ℝ) * (t:ℝ) + (t:ℝ) * (R:ℝ) := by
            nlinarith
        _ = (2:ℝ) * (t:ℝ) * (R:ℝ) := by ring_nf
    have hdenpos : 0 < (R:ℝ) * (R - t : ℝ) := by nlinarith [hRpos', hRt']
    have hdiv :
        |((c - u : ℝ) / (R - t : ℝ)) - (c : ℝ) / (R : ℝ)| ≤
          ((2:ℝ) * (t:ℝ) * (R:ℝ)) / ((R:ℝ) * (R - t : ℝ)) := by
      -- divide by positive denominator
      have habs :
          |((c - u : ℝ) / (R - t : ℝ)) - (c : ℝ) / (R : ℝ)| =
            |(c:ℝ) * (t:ℝ) - (u:ℝ) * (R:ℝ)| / ((R:ℝ) * (R - t : ℝ)) := by
        have hdenpos' : 0 < (R:ℝ) * (R - t : ℝ) := hdenpos
        calc
          |((c - u : ℝ) / (R - t : ℝ)) - (c : ℝ) / (R : ℝ)|
              = |((c:ℝ) * (t:ℝ) - (u:ℝ) * (R:ℝ)) / ((R:ℝ) * (R - t : ℝ))| := by
                  simp [h1]
          _ = |(c:ℝ) * (t:ℝ) - (u:ℝ) * (R:ℝ)| / ((R:ℝ) * (R - t : ℝ)) := by
                  simp [abs_div, abs_of_pos hdenpos']
      have := (div_le_div_of_nonneg_right hnum' (le_of_lt hdenpos))
      simpa [habs] using this
    -- simplify
    have hRpos'' : (0:ℝ) < (R:ℝ) := hRpos'
    calc
      |((c - u : ℝ) / (R - t : ℝ)) - (c : ℝ) / (R : ℝ)|
          ≤ ((2:ℝ) * (t:ℝ) * (R:ℝ)) / ((R:ℝ) * (R - t : ℝ)) := hdiv
      _ = (2 * (t:ℝ)) / (R - t : ℝ) := by
          field_simp [hRpos''.ne']
  -- use R - t ≥ R/2 when 2L ≤ R and t ≤ L
  have hden : (R - t : ℝ) ≥ (R : ℝ) / 2 := by
    have ht' : (t:ℝ) ≤ (L:ℝ) := by exact_mod_cast ht
    have hR' : (2:ℝ) * (L:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    nlinarith
  have hfinal : (2 * (t:ℝ)) / (R - t : ℝ) ≤ (4 * (L:ℝ)) / (R:ℝ) := by
    have hRpos' : (0:ℝ) < (R:ℝ) := by exact_mod_cast hRpos
    have ht' : (t:ℝ) ≤ (L:ℝ) := by exact_mod_cast ht
    -- 2t/(R - t) ≤ 2L/(R/2) = 4L/R
    have : (2 * (t:ℝ)) / (R - t : ℝ) ≤ (2 * (L:ℝ)) / ((R:ℝ) / 2) := by
      have hnum : (2 * (t:ℝ)) ≤ (2 * (L:ℝ)) := by nlinarith
      have hdenpos : (0:ℝ) < (R:ℝ) / 2 := by nlinarith [hRpos']
      have hden_le : (R - t : ℝ) ≥ (R:ℝ) / 2 := hden
      -- smaller denominator gives larger fraction
      have hfrac : (2 * (t:ℝ)) / (R - t : ℝ) ≤ (2 * (t:ℝ)) / ((R:ℝ) / 2) := by
        have hnum0 : 0 ≤ (2 * (t:ℝ)) := by nlinarith
        exact (div_le_div_of_nonneg_left hnum0 hdenpos (by nlinarith [hden_le]))
      exact hfrac.trans ((div_le_div_iff_of_pos_right hdenpos).2 hnum)
    have hrewrite : (2 * (L:ℝ)) / ((R:ℝ) / 2) = (4 * (L:ℝ)) / (R:ℝ) := by
      field_simp [hRpos'.ne']
      ring
    simpa [hrewrite] using this
  exact hnum.trans hfinal

/-! ## Product bounds via step‑pair bounds -/

lemma abs_worProb_sub_wrProb_le_length_mul_eps
    (ms0 ms : Multiset α) (xs : List α) (ε : ℝ)
    (hbound : ∀ p ∈ stepPairs ms0 ms xs, |p.1 - p.2| ≤ ε)
    (h :
      ∀ p ∈ stepPairs ms0 ms xs,
        0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1) :
    |worProb ms xs - wrProb ms0 xs| ≤ (xs.length : ℝ) * ε := by
  have hprod :
      |List.prod ((stepPairs ms0 ms xs).map Prod.fst) -
        List.prod ((stepPairs ms0 ms xs).map Prod.snd)| ≤
        ((stepPairs ms0 ms xs).length : ℝ) * ε := by
    -- apply product bound to the list of step pairs
    have hbound' :
        ∀ p ∈ stepPairs ms0 ms xs, |Prod.fst p - Prod.snd p| ≤ ε := by
      intro p hp
      simpa using hbound p hp
    have hrange :
        ∀ p ∈ stepPairs ms0 ms xs,
          0 ≤ Prod.fst p ∧ Prod.fst p ≤ 1 ∧ 0 ≤ Prod.snd p ∧ Prod.snd p ≤ 1 := by
      intro p hp
      simpa using h p hp
    simpa using
      (MarkovDeFinettiHardWithoutReplacement.abs_prod_diff_le_length_mul_eps
        (xs := stepPairs ms0 ms xs)
        (p := Prod.fst) (q := Prod.snd) (ε := ε)
        hbound' hrange)
  -- repackage in terms of worProb/wrProb
  have hwor := worProb_eq_prod_stepPairs ms0 ms xs
  have hwr := wrProb_eq_prod_stepPairs ms0 ms xs
  have hprod' :
      |List.prod ((stepPairs ms0 ms xs).map Prod.fst) -
        List.prod ((stepPairs ms0 ms xs).map Prod.snd)| ≤
        (xs.length : ℝ) * ε := by
    simpa [length_stepPairs] using hprod
  -- rewrite and finish
  simpa [hwor, hwr] using hprod'

lemma stepPairs_range
    (ms0 ms : Multiset α) (xs : List α) :
    ∀ p ∈ stepPairs ms0 ms xs,
      0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := by
  intro p hp
  -- unfold `stepPairs` and reason by induction on `xs`
  induction xs generalizing ms with
  | nil =>
      simp [stepPairs] at hp
  | cons a xs ih =>
      simp [stepPairs] at hp
      rcases hp with hp | hp
      · -- head pair
        rcases hp with rfl
        constructor
        · exact probWeight_nonneg _ _
        · constructor
          · exact probWeight_le_one _ _ (Multiset.count_le_card _ _)
          · constructor
            · exact probWeight_nonneg _ _
            · exact probWeight_le_one _ _ (Multiset.count_le_card _ _)
      · -- tail
        exact ih (ms := ms.erase a) hp

/-! ## Step‑pair bound under submultiset assumptions -/

lemma tail_submultiset_of_cons
    (a : α) (xs : List α) (ms0 : Multiset α)
    (hsub : (a ::ₘ Multiset.ofList xs) ≤ ms0) :
    (Multiset.ofList xs) ≤ ms0.erase a := by
  classical
  -- show `a ∈ ms0`
  have hcount := (Multiset.le_iff_count).1 hsub a
  have hcount_pos : 0 < Multiset.count a (a ::ₘ Multiset.ofList xs) := by
    -- count of the head is at least 1
    simp
  have hcount_ms0 : 0 < Multiset.count a ms0 := lt_of_lt_of_le hcount_pos hcount
  have ha : a ∈ ms0 := (Multiset.count_pos).1 hcount_ms0
  -- rewrite `ms0` as `a ::ₘ ms0.erase a`
  have hcons : a ::ₘ Multiset.ofList xs ≤ a ::ₘ ms0.erase a := by
    simpa [Multiset.cons_erase ha] using hsub
  -- cancel the head
  exact (Multiset.cons_le_cons_iff _).1 hcons

lemma stepPairs_bound_aux
    (ms0 ms : Multiset α) (xs : List α) (L : ℕ)
    (hL : xs.length ≤ L)
    (hsub : (Multiset.ofList xs) ≤ ms)
    (hms : ms ≤ ms0)
    (hR : 2 * L ≤ ms0.card)
    (hcard : ms.card = ms0.card - (L - xs.length)) :
    ∀ p ∈ stepPairs ms0 ms xs,
      |p.1 - p.2| ≤ (4 * (L : ℝ)) / (ms0.card : ℝ) := by
  classical
  induction xs generalizing ms with
  | nil =>
      intro p hp
      simp [stepPairs] at hp
  | cons a xs ih =>
      intro p hp
      -- split on head/tail
      simp [stepPairs] at hp
      rcases hp with hp | hp
      · -- head pair: apply the one‑step bound
        rcases hp with rfl
        -- set up parameters for `stepProb_bound`
        let R : ℕ := ms0.card
        let t : ℕ := L - (List.length (a :: xs))
        let c : ℕ := ms0.count a
        have hcount_le : ms.count a ≤ c := (Multiset.le_iff_count).1 hms a
        let u : ℕ := c - ms.count a
        have ht : t ≤ L := by
          exact Nat.sub_le _ _
        have hu : u ≤ t := by
          -- use multiset difference: u counts removed `a`'s, bounded by total removed `t`
          have hdiff : u = Multiset.count a (ms0 - ms) := by
            -- `count_sub` gives the difference
            have := (Multiset.count_sub (a := a) (s := ms0) (t := ms))
            -- rewrite `u` and simplify
            simp [u, c, this]  -- `count_sub` is already `count a ms0 - count a ms`
          have hcard' : (ms0 - ms).card = ms0.card - ms.card := by
            exact Multiset.card_sub hms
          -- `count a (ms0 - ms) ≤ card (ms0 - ms)`
          have hle : Multiset.count a (ms0 - ms) ≤ (ms0 - ms).card := by
            exact Multiset.count_le_card _ _
          -- compute `t = ms0.card - ms.card`
          have ht' : t = ms0.card - ms.card := by
            -- using the card relation and the definition of `t`
            omega
          -- finish
          have hle' : u ≤ ms0.card - ms.card := by
            simpa [hdiff, hcard', ht'] using hle
          simpa [ht'] using hle'
        have hc : c ≤ R := by
          exact Multiset.count_le_card _ _
        have hR' : 2 * L ≤ R := hR
        -- rewrite p.1 and p.2 as the target fractions
        have hp1 :
            (probWeight (ms.count a) ms.card) =
              ( (c - u : ℕ) : ℝ) / ((R - t : ℕ) : ℝ) := by
          -- show `ms.count a = c - u` and `ms.card = R - t`
          have hcount_eq : ms.count a = c - u := by
            -- u = c - ms.count a
            omega
          have hcard_eq : ms.card = R - t := by
            -- unfold and use `hcard`
            -- `t = L - length (a::xs)`
            -- `ms.card = R - (L - length (a::xs))`
            simpa [R, t] using hcard
          -- rewrite `probWeight` using positivity of `R - t`
          have hRtpos : 0 < R - t := by
            -- `t ≤ L` and `2*L ≤ R` imply `R - t ≥ L`
            have hLpos : 0 < L := by
              -- `a :: xs` has length ≥ 1, and `length ≤ L`
              have : 1 ≤ L := by
                have hlen : 1 ≤ (a :: xs).length := by simp
                exact le_trans hlen hL
              exact lt_of_lt_of_le (by decide : 0 < 1) this
            -- use omega for Nat arithmetic
            omega
          have hRt0 : R - t ≠ 0 := by exact ne_of_gt hRtpos
          simp [probWeight, hRt0, hcount_eq, hcard_eq]
        have hp2 :
            (probWeight (ms0.count a) ms0.card) =
              ( (c : ℕ) : ℝ) / ((R : ℕ) : ℝ) := by
          have hRpos : 0 < R := by
            -- since `2*L ≤ R` and `L > 0`
            have hLpos : 0 < L := by
              have : 1 ≤ L := by
                have hlen : 1 ≤ (a :: xs).length := by simp
                exact le_trans hlen hL
              exact lt_of_lt_of_le (by decide : 0 < 1) this
            exact lt_of_lt_of_le (Nat.mul_pos (by decide) hLpos) hR
          have hR0 : R ≠ 0 := by exact ne_of_gt hRpos
          simp [probWeight, hR0, R, c]
        -- apply the step bound
        have hstep :=
          stepProb_bound (R := R) (L := L) (t := t) (c := c) (u := u) hR' ht hu hc
        -- finish
        -- align casts of subtraction
        have hcu : ((c - u : ℕ) : ℝ) = (c : ℝ) - (u : ℝ) := by
          -- `u ≤ c`
          have hc' : u ≤ c := by
            -- u = c - ms.count a
            omega
          simp [Nat.cast_sub hc']
        have hRt : ((R - t : ℕ) : ℝ) = (R : ℝ) - (t : ℝ) := by
          have ht' : t ≤ R := by
            -- from `t ≤ L` and `2*L ≤ R`
            have hR' : 2 * L ≤ R := hR
            omega
          simp [Nat.cast_sub ht']
        -- `simp` using the cast equalities
        simpa [hp1, hp2, hcu, hRt] using hstep
      · -- tail: apply IH to the erased multiset
        have hsub' : (Multiset.ofList xs) ≤ ms.erase a := by
          simpa using
            (tail_submultiset_of_cons (a := a) (xs := xs) (ms0 := ms)
              (hsub := by simpa using hsub))
        have hms' : ms.erase a ≤ ms0 := by
          exact le_trans (Multiset.erase_le_erase a hms) (Multiset.erase_le a ms0)
        have hcard' : (ms.erase a).card = ms0.card - (L - xs.length) := by
          have ha : a ∈ ms := by
            -- `a` appears in `ms` since it appears in the submultiset
            have hcount := (Multiset.le_iff_count).1 hsub a
            have hcount_pos : 0 < Multiset.count a (a ::ₘ Multiset.ofList xs) := by
              simp
            have hcount_ms : 0 < Multiset.count a ms := lt_of_lt_of_le hcount_pos hcount
            exact (Multiset.count_pos).1 hcount_ms
          have hcard1 : (ms.erase a).card + 1 = ms.card := Multiset.card_erase_add_one ha
          -- simplify using `hcard`
          have hlen : (List.length (a :: xs)) = xs.length + 1 := by simp
          -- arithmetic with naturals
          omega
        exact ih (ms := ms.erase a) (hL := by
          -- tail length ≤ L
          have : xs.length ≤ (a :: xs).length := by simp
          exact le_trans this hL)
          (hsub := hsub') (hms := hms') (hcard := hcard') p hp

lemma stepPairs_bound_of_submultiset
    (ms0 : Multiset α) (xs : List α)
    (hsub : (Multiset.ofList xs) ≤ ms0)
    (hR : 2 * xs.length ≤ ms0.card) :
    ∀ p ∈ stepPairs ms0 ms0 xs,
      |p.1 - p.2| ≤ (4 * (xs.length : ℝ)) / (ms0.card : ℝ) := by
  -- instantiate the auxiliary lemma with `ms = ms0` and `L = xs.length`
  have hcard : ms0.card = ms0.card - (xs.length - xs.length) := by
    simp
  -- use `L = xs.length`
  simpa using
    (stepPairs_bound_aux (ms0 := ms0) (ms := ms0) (xs := xs)
      (L := xs.length) (hL := by simp) (hsub := hsub) (hms := le_rfl) (hR := hR) (hcard := hcard))

end MarkovDeFinettiHardWithoutReplacementModel

end Mettapedia.Logic
