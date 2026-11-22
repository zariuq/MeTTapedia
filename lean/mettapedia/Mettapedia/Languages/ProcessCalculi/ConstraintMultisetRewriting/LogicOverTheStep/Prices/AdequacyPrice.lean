import Mettapedia.GSLT.Logic.ConstructiveModalStrength
import Mettapedia.Logic.ReverseMathematics.Omniscience

/-!
# The price of finitary adequacy

`ConstructiveModalStrength.image_finite_reflection_implies_llpo`: if logical equivalence implies
bisimilarity on every image-finite system, then LLPO. This module gives the matching upper bounds, by
proofs that use no `Classical.choice` (each headline theorem is audited with `#print axioms`), and
shows that the price depends on how successors and observations are given.

* **Explicit successor lists, decided observations, countably many atoms and labels**
  (`ListPresented`): adequacy on every such system is equivalent to LLPO
  (`listAdequacy_iff_llpo`). The upper bound (`bisimilar_of_llpo`) uses LLPO for finitely many
  searches (`llpo_list`), from its De Morgan form (`deMorgan_iff_llpo`); the lower bound is the tree's
  stream probe, which is such a system.
* **Successor sets with finite covers** (the tree's `ImageFiniteModulo`): the tree's reflection
  principle is equivalent to excluded middle (`imageFiniteReflection_iff_em`), already when the
  observations are decided (`coverAdequacy_iff_em`).
* **Explicit lists, observations that are only propositions**: again excluded middle
  (`listPropAdequacy_iff_em`).

The lower bounds for excluded middle use one probe (`probeSystem`): a root whose successor can take
its step, or see its observation, exactly when a proposition holds. Under the double negation of that
proposition the roots agree on every formula (`probe_logicallyEquivalent`); a bisimulation proves the
proposition (`probe_of_bisimilar`).

## What a checker can use with no principle

**Apartness with a witness** (`Apart`): a formula true at one state and false at the other. It refutes
bisimilarity (`not_bisimilar_of_apart`) and is symmetric (`apart_symm`). On list-presented systems it
is found by a search through finite levels of formulas (`apart_iff_exists_level`), its absence is
exactly logical equivalence (`not_apart_iff_logicallyEquivalent`), Markov's principle turns "not
logically equivalent" into a witness (`apart_of_mp`), and LPO decides between the two
(`logicallyEquivalent_or_apart_of_lpo`). With no principle, "the same type" is carried by a
bisimulation, given as a certificate, and "a different type" by a distinguishing formula; logical
equivalence is only the absence of the second.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.AdequacyPrice

open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner
open Mettapedia.Logic.ReverseMathematics.Omniscience

universe u uA uL

/-! ## Searches, intuitionistically -/

theorem boolCases (b : Bool) : b = false ∨ b = true := by
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem false_of_not_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

theorem false_of_not_eq_true {b : Bool} (h : (!b) = true) : b = false := by
  cases b
  · rfl
  · exact Bool.noConfusion h

theorem true_of_not_eq_false {b : Bool} (h : (!b) = false) : b = true := by
  cases b
  · exact Bool.noConfusion h
  · rfl

/-- **LLPO in De Morgan form**: of two searches that do not both succeed, one never succeeds. -/
def DeMorganLLPO : Prop :=
  ∀ α β : ℕ → Bool, ¬ ((∃ n, α n = true) ∧ ∃ n, β n = true) →
    (∀ n, α n = false) ∨ ∀ n, β n = false

/-- A success of either search. -/
def hit (α β : ℕ → Bool) (n : ℕ) : Bool := α n || β n

theorem hit_left {α β : ℕ → Bool} {n : ℕ} (h : α n = true) : hit α β n = true := by
  unfold hit
  rw [h]
  rfl

theorem hit_right {α β : ℕ → Bool} {n : ℕ} (h : β n = true) : hit α β n = true := by
  unfold hit
  rw [h]
  cases α n <;> rfl

/-- The first success of either search: at an even place when `α` succeeds there, at an odd place
when only `β` does. -/
def firstSuccess (α β : ℕ → Bool) (k : ℕ) : Bool :=
  if k % 2 = 0 then α (k / 2) && decide (∀ m < k / 2, hit α β m = false)
  else β (k / 2) && !α (k / 2) && decide (∀ m < k / 2, hit α β m = false)

theorem firstSuccess_even (α β : ℕ → Bool) (n : ℕ) :
    firstSuccess α β (2 * n) = (α n && decide (∀ m < n, hit α β m = false)) := by
  rw [firstSuccess, if_pos (by omega), show 2 * n / 2 = n by omega]

theorem firstSuccess_odd (α β : ℕ → Bool) (n : ℕ) :
    firstSuccess α β (2 * n + 1) = (β n && !α n && decide (∀ m < n, hit α β m = false)) := by
  rw [firstSuccess, if_neg (by omega), show (2 * n + 1) / 2 = n by omega]

theorem firstSuccess_even_true {α β : ℕ → Bool} {n : ℕ} (h : firstSuccess α β (2 * n) = true) :
    α n = true ∧ ∀ m < n, hit α β m = false := by
  rw [firstSuccess_even, Bool.and_eq_true, decide_eq_true_iff] at h
  exact h

theorem firstSuccess_odd_true {α β : ℕ → Bool} {n : ℕ} (h : firstSuccess α β (2 * n + 1) = true) :
    β n = true ∧ α n = false ∧ ∀ m < n, hit α β m = false := by
  rw [firstSuccess_odd, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff] at h
  obtain ⟨⟨hβ, hα⟩, below⟩ := h
  exact ⟨hβ, false_of_not_eq_true hα, below⟩

theorem first_unique {α β : ℕ → Bool} {n n' : ℕ} (hn : hit α β n = true)
    (below : ∀ m < n, hit α β m = false) (hn' : hit α β n' = true)
    (below' : ∀ m < n', hit α β m = false) : n = n' := by
  rcases Nat.lt_trichotomy n n' with lt | eq | gt
  · have early := below' n lt
    rw [hn] at early
    exact Bool.noConfusion early
  · exact eq
  · have early := below n' gt
    rw [hn'] at early
    exact Bool.noConfusion early

/-- The first success happens at most once. -/
theorem firstSuccess_atMostOneTrue (α β : ℕ → Bool) : AtMostOneTrue (firstSuccess α β) := by
  intro i j hi hj
  obtain ⟨n, rfl | rfl⟩ : ∃ n, i = 2 * n ∨ i = 2 * n + 1 := ⟨i / 2, by omega⟩ <;>
    obtain ⟨n', rfl | rfl⟩ : ∃ n', j = 2 * n' ∨ j = 2 * n' + 1 := ⟨j / 2, by omega⟩
  · obtain ⟨ha, hb⟩ := firstSuccess_even_true hi
    obtain ⟨ha', hb'⟩ := firstSuccess_even_true hj
    have same := first_unique (hit_left ha) hb (hit_left ha') hb'
    omega
  · obtain ⟨ha, hb⟩ := firstSuccess_even_true hi
    obtain ⟨hβ', hα', hb'⟩ := firstSuccess_odd_true hj
    have same := first_unique (hit_left ha) hb (hit_right hβ') hb'
    rw [same, hα'] at ha
    exact Bool.noConfusion ha
  · obtain ⟨hβ, hα, hb⟩ := firstSuccess_odd_true hi
    obtain ⟨ha', hb'⟩ := firstSuccess_even_true hj
    have same := first_unique (hit_right hβ) hb (hit_left ha') hb'
    rw [← same, hα] at ha'
    exact Bool.noConfusion ha'
  · obtain ⟨hβ, _, hb⟩ := firstSuccess_odd_true hi
    obtain ⟨hβ', _, hb'⟩ := firstSuccess_odd_true hj
    have same := first_unique (hit_right hβ) hb (hit_right hβ') hb'
    omega

/-- **LLPO gives its De Morgan form.** -/
theorem deMorgan_of_llpo (llpo : LLPO) : DeMorganLLPO := by
  intro α β notBoth
  have first : ∀ {n}, hit α β n = true → ∃ m, hit α β m = true ∧ ∀ k < m, hit α β k = false := by
    intro n hn
    have found : ∃ k, hit α β k = true := ⟨n, hn⟩
    exact ⟨Nat.find found, Nat.find_spec found, fun k lt => false_of_not_true (Nat.find_min found lt)⟩
  rcases llpo (firstSuccess α β) (firstSuccess_atMostOneTrue α β) with evens | odds
  · left
    intro n
    rcases boolCases (α n) with h | h
    · exact h
    · exfalso
      obtain ⟨m, hm, below⟩ := first (hit_left h)
      rcases boolCases (α m) with hαm | hαm
      · have hβm : β m = true := by
          have either : (α m || β m) = true := hm
          rw [hαm] at either
          exact either
        exact notBoth ⟨⟨n, h⟩, ⟨m, hβm⟩⟩
      · have atM := evens m
        rw [firstSuccess_even, hαm, decide_eq_true_iff.mpr below] at atM
        exact Bool.noConfusion atM
  · right
    intro n
    rcases boolCases (β n) with h | h
    · exact h
    · exfalso
      obtain ⟨m, hm, below⟩ := first (hit_right h)
      rcases boolCases (α m) with hαm | hαm
      · have hβm : β m = true := by
          have either : (α m || β m) = true := hm
          rw [hαm] at either
          exact either
        have atM := odds m
        rw [firstSuccess_odd, hβm, hαm, decide_eq_true_iff.mpr below] at atM
        exact Bool.noConfusion atM
      · exact notBoth ⟨⟨m, hαm⟩, ⟨n, h⟩⟩

/-- The De Morgan form gives LLPO. -/
theorem llpo_of_deMorgan (deMorgan : DeMorganLLPO) : LLPO := by
  intro α unique
  apply deMorgan (fun n => α (2 * n)) (fun n => α (2 * n + 1))
  rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
  have same := unique _ _ hm hn
  omega

theorem deMorgan_iff_llpo : DeMorganLLPO ↔ LLPO := ⟨llpo_of_deMorgan, deMorgan_of_llpo⟩

/-- Finitely many successful searches succeed by a common bound. -/
theorem bound_of_forall {ι : Type*} (α : ι → ℕ → Bool) :
    ∀ L : List ι, (∀ i ∈ L, ∃ n, α i n = true) → ∃ m, ∀ i ∈ L, ∃ n ≤ m, α i n = true
  | [], _ => ⟨0, fun _ member => absurd member List.not_mem_nil⟩
  | i :: rest, all => by
      obtain ⟨n, hn⟩ := all i (List.mem_cons.mpr (Or.inl rfl))
      obtain ⟨m, hm⟩ := bound_of_forall α rest fun j member => all j (List.mem_cons.mpr (Or.inr member))
      refine ⟨max n m, fun j member => ?_⟩
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨n, le_max_left n m, hn⟩
      · obtain ⟨k, le, hk⟩ := hm j inRest
        exact ⟨k, le.trans (le_max_right n m), hk⟩

/-- **LLPO for finitely many searches**: if not all of finitely many searches succeed, one of them
never succeeds. -/
theorem llpo_list (llpo : LLPO) {ι : Type*} (α : ι → ℕ → Bool) :
    ∀ L : List ι, ¬ (∀ i ∈ L, ∃ n, α i n = true) → ∃ i ∈ L, ∀ n, α i n = false
  | [], notAll => absurd (fun _ member => absurd member List.not_mem_nil) notAll
  | i :: rest, notAll => by
      rcases deMorgan_of_llpo llpo (α i) (fun m => decide (∀ j ∈ rest, ∃ n ≤ m, α j n = true)) (by
          rintro ⟨⟨n, hn⟩, ⟨m, hm⟩⟩
          have all := decide_eq_true_iff.mp hm
          refine notAll fun j member => ?_
          rcases List.mem_cons.mp member with rfl | inRest
          · exact ⟨n, hn⟩
          · obtain ⟨k, _, hk⟩ := all j inRest
            exact ⟨k, hk⟩) with never | noBound
      · exact ⟨i, List.mem_cons.mpr (Or.inl rfl), never⟩
      · have notRest : ¬ ∀ j ∈ rest, ∃ n, α j n = true := by
          intro all
          obtain ⟨m, bounded⟩ := bound_of_forall α rest all
          have atM : decide (∀ j ∈ rest, ∃ n ≤ m, α j n = true) = false := noBound m
          rw [decide_eq_true_iff.mpr bounded] at atM
          exact Bool.noConfusion atM
        obtain ⟨j, member, never⟩ := llpo_list llpo α rest notRest
        exact ⟨j, List.mem_cons.mpr (Or.inr member), never⟩

/-! ## Systems whose successors are given as lists -/

variable {S : GSLT.{u}} {M : System.{uA, uL} S}

/-- **Successors given as explicit lists.** -/
structure ListSuccessors (M : System.{uA, uL} S) where
  succ : M.Label → S.Term → List S.Term
  act_iff : ∀ (label : M.Label) (source target : S.Term),
    M.act label source target ↔ target ∈ succ label source

/-- **Successors given as explicit lists, and observations decided.** -/
structure ListPresented (M : System.{uA, uL} S) extends ListSuccessors M where
  decideAtom : ∀ (atom : M.Atom) (term : S.Term), Decidable (M.observes atom term)

/-- On a list-presented system every formula is decided at every state. -/
def ListPresented.decideSat (P : ListPresented M) :
    (φ : Formula M.Atom M.Label) → (s : S.Term) → Decidable (M.sat φ s)
  | .top, _ => isTrue trivial
  | .atom a, s => P.decideAtom a s
  | .conj φ ψ, s =>
      haveI := P.decideSat φ s
      haveI := P.decideSat ψ s
      inferInstanceAs (Decidable (M.sat φ s ∧ M.sat ψ s))
  | .neg φ, s =>
      haveI := P.decideSat φ s
      inferInstanceAs (Decidable (¬ M.sat φ s))
  | .dia l φ, s =>
      haveI : DecidablePred fun t => M.sat φ t := fun t => P.decideSat φ t
      decidable_of_iff (∃ t ∈ P.succ l s, M.sat φ t)
        ⟨fun ⟨t, member, holds⟩ => ⟨t, (P.act_iff l s t).mpr member, holds⟩,
          fun ⟨t, step, holds⟩ => ⟨t, (P.act_iff l s t).mp step, holds⟩⟩

/-! ## Finite levels of formulas -/

section Levels

variable {Atom : Type uA} {Label : Type uL} (atoms : ℕ → Option Atom) (labels : ℕ → Option Label)

/-- **The formulas of level `d`**: built in `d` rounds from the first `d` atoms and labels. -/
def level : ℕ → List (Formula Atom Label)
  | 0 => [.top]
  | d + 1 =>
      level d ++
        ((atoms d).toList.map Formula.atom ++ (level d).map Formula.neg ++
          (level d).flatMap (fun φ => (level d).map (Formula.conj φ)) ++
          (List.range (d + 1)).flatMap fun i =>
            (labels i).toList.flatMap fun l => (level d).map (Formula.dia l))

variable {atoms labels}

theorem mem_level_mono {d e : ℕ} (le : d ≤ e) {φ : Formula Atom Label}
    (h : φ ∈ level atoms labels d) : φ ∈ level atoms labels e := by
  induction le with
  | refl => exact h
  | step _ ih => exact List.mem_append_left _ ih

theorem mem_level_atom {i : ℕ} {a : Atom} (hi : atoms i = some a) :
    Formula.atom a ∈ level atoms labels (i + 1) := by
  have inList : a ∈ (atoms i).toList := by
    rw [hi]
    exact List.mem_singleton.mpr rfl
  exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_map_of_mem inList))))

theorem mem_level_neg {d : ℕ} {φ : Formula Atom Label} (h : φ ∈ level atoms labels d) :
    Formula.neg φ ∈ level atoms labels (d + 1) :=
  List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map_of_mem h))))

theorem mem_level_conj {d : ℕ} {φ ψ : Formula Atom Label} (hφ : φ ∈ level atoms labels d)
    (hψ : ψ ∈ level atoms labels d) : Formula.conj φ ψ ∈ level atoms labels (d + 1) :=
  List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨φ, hφ, List.mem_map_of_mem hψ⟩)))

theorem mem_level_dia {d i : ℕ} {l : Label} (hi : labels i = some l) (le : i ≤ d)
    {φ : Formula Atom Label} (h : φ ∈ level atoms labels d) :
    Formula.dia l φ ∈ level atoms labels (d + 1) := by
  have inList : l ∈ (labels i).toList := by
    rw [hi]
    exact List.mem_singleton.mpr rfl
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le le),
      List.mem_flatMap.mpr ⟨l, inList, List.mem_map_of_mem h⟩⟩))

/-- **Every formula has a level**, when the atoms and labels are enumerated. -/
theorem exists_level (atomsOnto : ∀ a, ∃ i, atoms i = some a)
    (labelsOnto : ∀ l, ∃ i, labels i = some l) :
    ∀ φ : Formula Atom Label, ∃ d, φ ∈ level atoms labels d
  | .top => ⟨0, List.mem_singleton.mpr rfl⟩
  | .atom a =>
      let ⟨i, hi⟩ := atomsOnto a
      ⟨i + 1, mem_level_atom hi⟩
  | .conj φ ψ =>
      let ⟨d, hd⟩ := exists_level atomsOnto labelsOnto φ
      let ⟨e, he⟩ := exists_level atomsOnto labelsOnto ψ
      ⟨max d e + 1, mem_level_conj (mem_level_mono (le_max_left d e) hd)
        (mem_level_mono (le_max_right d e) he)⟩
  | .neg φ =>
      let ⟨d, hd⟩ := exists_level atomsOnto labelsOnto φ
      ⟨d + 1, mem_level_neg hd⟩
  | .dia l φ =>
      let ⟨i, hi⟩ := labelsOnto l
      let ⟨d, hd⟩ := exists_level atomsOnto labelsOnto φ
      ⟨max i d + 1, mem_level_dia hi (le_max_left i d) (mem_level_mono (le_max_right i d) hd)⟩

end Levels

/-! ## The search for a distinguishing formula -/

/-- **Agreement up to level `d`**: decided on a list-presented system. -/
def agreeAt (P : ListPresented M) (atoms : ℕ → Option M.Atom) (labels : ℕ → Option M.Label)
    (x y : S.Term) (d : ℕ) : Bool :=
  (level atoms labels d).all fun φ =>
    @decide (M.sat φ x ↔ M.sat φ y) (@instDecidableIff _ _ (P.decideSat φ x) (P.decideSat φ y))

theorem agreeAt_true_iff (P : ListPresented M) {atoms : ℕ → Option M.Atom}
    {labels : ℕ → Option M.Label} {x y : S.Term} {d : ℕ} :
    agreeAt P atoms labels x y d = true ↔ ∀ φ ∈ level atoms labels d, (M.sat φ x ↔ M.sat φ y) := by
  unfold agreeAt
  rw [List.all_eq_true]
  exact forall₂_congr fun φ _ =>
    @decide_eq_true_iff _ (@instDecidableIff _ _ (P.decideSat φ x) (P.decideSat φ y))

theorem exists_of_all_eq_false {α : Type*} (p : α → Bool) :
    ∀ l : List α, l.all p = false → ∃ a ∈ l, p a = false
  | [], h => Bool.noConfusion h
  | a :: l, h => by
      rcases boolCases (p a) with ha | ha
      · exact ⟨a, List.mem_cons.mpr (Or.inl rfl), ha⟩
      · have rest : l.all p = false := by
          have unfolded : (p a && l.all p) = false := h
          rw [ha] at unfolded
          exact unfolded
        obtain ⟨b, hb, hpb⟩ := exists_of_all_eq_false p l rest
        exact ⟨b, List.mem_cons.mpr (Or.inr hb), hpb⟩

/-- A disagreement on decided formulas is oriented into a separating formula. -/
theorem orient (P : ListPresented M) {φ : Formula M.Atom M.Label} {x y : S.Term}
    (notIff : ¬ (M.sat φ x ↔ M.sat φ y)) : ∃ ψ : Formula M.Atom M.Label, M.sat ψ x ∧ ¬ M.sat ψ y := by
  cases P.decideSat φ x with
  | isTrue holds => exact ⟨φ, holds, fun holdsY => notIff ⟨fun _ => holdsY, fun _ => holds⟩⟩
  | isFalse fails =>
      cases P.decideSat φ y with
      | isTrue holdsY => exact ⟨.neg φ, fails, fun notY => notY holdsY⟩
      | isFalse failsY => exact absurd ⟨fun h => absurd h fails, fun h => absurd h failsY⟩ notIff

theorem separator_of_disagree (P : ListPresented M) {atoms : ℕ → Option M.Atom}
    {labels : ℕ → Option M.Label} {x y : S.Term} {d : ℕ}
    (disagree : agreeAt P atoms labels x y d = false) :
    ∃ ψ : Formula M.Atom M.Label, M.sat ψ x ∧ ¬ M.sat ψ y := by
  obtain ⟨φ, _, hφ⟩ := exists_of_all_eq_false _ _ disagree
  refine orient P (φ := φ) fun same => ?_
  have decided := @decide_eq_true _ (@instDecidableIff _ _ (P.decideSat φ x) (P.decideSat φ y)) same
  rw [decided] at hφ
  exact Bool.noConfusion hφ

/-- **On a list-presented countable system, logical equivalence is agreement at every level.** -/
theorem logicallyEquivalent_iff_agree (P : ListPresented M) {atoms : ℕ → Option M.Atom}
    {labels : ℕ → Option M.Label} (atomsOnto : ∀ a, ∃ i, atoms i = some a)
    (labelsOnto : ∀ l, ∃ i, labels i = some l) (x y : S.Term) :
    M.LogicallyEquivalent x y ↔ ∀ d, agreeAt P atoms labels x y d = true :=
  ⟨fun equivalent _ => (agreeAt_true_iff P).mpr fun φ _ => equivalent φ,
    fun all φ =>
      let ⟨d, hd⟩ := exists_level atomsOnto labelsOnto φ
      (agreeAt_true_iff P).mp (all d) φ hd⟩

/-- Separators of finitely many states, on a condition, combine into one formula. -/
theorem conjSeparatorOn (Q : S.Term → Prop) {x : S.Term} :
    ∀ L : List S.Term, (∀ y ∈ L, ∃ φ : Formula M.Atom M.Label, M.sat φ x ∧ (Q y → ¬ M.sat φ y)) →
      ∃ ψ : Formula M.Atom M.Label, M.sat ψ x ∧ ∀ y ∈ L, Q y → ¬ M.sat ψ y
  | [], _ => ⟨.top, trivial, fun _ member => absurd member List.not_mem_nil⟩
  | y :: rest, separators => by
      obtain ⟨φ, holds, fails⟩ := separators y (List.mem_cons.mpr (Or.inl rfl))
      obtain ⟨ψ, holdsψ, failsψ⟩ := conjSeparatorOn Q rest fun z member =>
        separators z (List.mem_cons.mpr (Or.inr member))
      refine ⟨.conj φ ψ, ⟨holds, holdsψ⟩, fun z member condition => ?_⟩
      rcases List.mem_cons.mp member with rfl | inRest
      · exact fun both => fails condition both.1
      · exact fun both => failsψ z inRest condition both.2

/-- A matching step for every step gives a bisimulation. -/
theorem isBisimulation_of_forth
    (forth : ∀ (x y : S.Term), M.LogicallyEquivalent x y → ∀ (label : M.Label) (x' : S.Term),
      M.act label x x' → ∃ y', M.act label y y' ∧ M.LogicallyEquivalent x' y') :
    M.IsBisimulation M.LogicallyEquivalent := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y equivalent label x' step
    exact forth x y equivalent label x' step
  · intro x y equivalent label y' step
    obtain ⟨x', step', equivalent'⟩ :=
      forth y x (M.logicallyEquivalent_symm equivalent) label y' step
    exact ⟨x', step', M.logicallyEquivalent_symm equivalent'⟩
  · intro x y equivalent atom
    exact equivalent (.atom atom)

/-! ## LLPO is the price on list-presented systems -/

/-- The matching step under LLPO. -/
theorem exists_match_of_llpo (llpo : LLPO) (P : ListPresented M) {atoms : ℕ → Option M.Atom}
    {labels : ℕ → Option M.Label} (atomsOnto : ∀ a, ∃ i, atoms i = some a)
    (labelsOnto : ∀ l, ∃ i, labels i = some l) {x y : S.Term} (equivalent : M.LogicallyEquivalent x y)
    (label : M.Label) {x' : S.Term} (step : M.act label x x') :
    ∃ y', M.act label y y' ∧ M.LogicallyEquivalent x' y' := by
  have notAll : ¬ ∀ y' ∈ P.succ label y, ∃ d, (!agreeAt P atoms labels x' y' d) = true := by
    intro all
    have separators : ∀ y' ∈ P.succ label y, ∃ φ : Formula M.Atom M.Label,
        M.sat φ x' ∧ (True → ¬ M.sat φ y') := by
      intro y' member
      obtain ⟨d, hd⟩ := all y' member
      obtain ⟨φ, holds, fails⟩ := separator_of_disagree P (false_of_not_eq_true hd)
      exact ⟨φ, holds, fun _ => fails⟩
    obtain ⟨ψ, holds, fails⟩ := conjSeparatorOn (fun _ => True) (P.succ label y) separators
    obtain ⟨y'', step'', holds''⟩ := (equivalent (.dia label ψ)).mp ⟨x', step, holds⟩
    exact fails y'' ((P.act_iff label y y'').mp step'') trivial holds''
  obtain ⟨y', member, never⟩ :=
    llpo_list llpo (fun y' d => !agreeAt P atoms labels x' y' d) (P.succ label y) notAll
  exact ⟨y', (P.act_iff label y y').mpr member,
    (logicallyEquivalent_iff_agree P atomsOnto labelsOnto x' y').mpr fun d =>
      true_of_not_eq_false (never d)⟩

/-- **LLPO gives finitary adequacy on every list-presented system with countably many atoms and
labels.** -/
theorem bisimilar_of_llpo (llpo : LLPO) (P : ListPresented M) {atoms : ℕ → Option M.Atom}
    {labels : ℕ → Option M.Label} (atomsOnto : ∀ a, ∃ i, atoms i = some a)
    (labelsOnto : ∀ l, ∃ i, labels i = some l) {x y : S.Term}
    (equivalent : M.LogicallyEquivalent x y) : M.Bisimilar x y :=
  ⟨M.LogicallyEquivalent, isBisimulation_of_forth fun _ _ equivalent' label _ step =>
    exists_match_of_llpo llpo P atomsOnto labelsOnto equivalent' label step, equivalent⟩

/-- Finitary adequacy on every list-presented system with countably many atoms and labels. -/
def ListAdequacy : Prop :=
  ∀ (S : GSLT.{0}) (M : System.{0, 0} S), ListPresented M →
    (∃ atoms : ℕ → Option M.Atom, ∀ a, ∃ i, atoms i = some a) →
    (∃ labels : ℕ → Option M.Label, ∀ l, ∃ i, labels i = some l) →
      ∀ x y, M.LogicallyEquivalent x y → M.Bisimilar x y

/-- The tree's stream probe is list-presented. -/
def probeListPresented (stream : ℕ → Bool) :
    ListPresented (ConstructiveModalStrength.system stream) where
  succ _ s := ConstructiveModalStrength.successors s
  act_iff _ _ _ := Iff.rfl
  decideAtom atom state :=
    (inferInstance : DecidableEq Bool) atom (ConstructiveModalStrength.observedBit stream state)

/-- **Adequacy on list-presented systems gives LLPO**, through the tree's stream probe. -/
theorem llpo_of_listAdequacy (adequacy : ListAdequacy) : LLPO := by
  intro stream unique
  refine ConstructiveModalStrength.llpo_of_bisimilar_roots stream
    (adequacy ConstructiveModalStrength.theory (ConstructiveModalStrength.system stream)
      (probeListPresented stream) ⟨fun i => some (Nat.beq i 1), fun a => ?_⟩
      ⟨fun _ => some PUnit.unit, fun l => ⟨0, by cases l; rfl⟩⟩ _ _
      (ConstructiveModalStrength.roots_logicallyEquivalent stream unique))
  cases a
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

/-- **On list-presented systems with decided observations and countably many atoms and labels,
finitary adequacy is exactly LLPO.** -/
theorem listAdequacy_iff_llpo : ListAdequacy ↔ LLPO :=
  ⟨llpo_of_listAdequacy, fun llpo _ _ P atoms labels _ _ equivalent =>
    let ⟨_, atomsOnto⟩ := atoms
    let ⟨_, labelsOnto⟩ := labels
    bisimilar_of_llpo llpo P atomsOnto labelsOnto equivalent⟩

/-! ## Excluded middle is the price with finite covers or undecided observations -/

/-- Successor sets covered, up to the equations, by finite lists. -/
def ListCover (M : System.{uA, uL} S) : Prop :=
  ∀ (label : M.Label) (source : S.Term), ∃ R : List S.Term,
    ∀ ⦃target : S.Term⦄, M.act label source target → ∃ r ∈ R, S.Equiv target r

/-- **The tree's finite covers are list covers.** -/
theorem listCover_of_imageFiniteModulo (finite : M.ImageFiniteModulo) : ListCover M := by
  intro label source
  obtain ⟨reps, repsFinite, covered⟩ := finite label source
  obtain ⟨n, ⟨e⟩⟩ := @Finite.exists_equiv_fin _ repsFinite
  refine ⟨List.ofFn fun i => (e.symm i).1, fun target step => ?_⟩
  obtain ⟨r, member, equivalent⟩ := covered step
  exact ⟨r, List.mem_ofFn.mpr ⟨e ⟨r, member⟩, by rw [Equiv.symm_apply_apply]⟩, equivalent⟩

theorem listCover_of_listSuccessors (P : ListSuccessors M) : ListCover M :=
  fun label source => ⟨P.succ label source, fun target step =>
    ⟨target, (P.act_iff label source target).mp step, S.equations.iseqv.refl target⟩⟩

/-- Excluded middle gives a separating formula for logically inequivalent states. -/
theorem separate_of_em (em : ∀ p : Prop, p ∨ ¬ p) {a b : S.Term}
    (notEquivalent : ¬ M.LogicallyEquivalent a b) :
    ∃ φ : Formula M.Atom M.Label, M.sat φ a ∧ ¬ M.sat φ b := by
  rcases em (∃ φ : Formula M.Atom M.Label, ¬ (M.sat φ a ↔ M.sat φ b)) with ⟨φ, disagree⟩ | none
  · rcases em (M.sat φ a) with holds | fails
    · exact ⟨φ, holds, fun holdsB => disagree ⟨fun _ => holdsB, fun _ => holds⟩⟩
    · rcases em (M.sat φ b) with holdsB | failsB
      · exact ⟨.neg φ, fails, fun notB => notB holdsB⟩
      · exact absurd ⟨fun h => absurd h fails, fun h => absurd h failsB⟩ disagree
  · exact absurd (fun φ => (em (M.sat φ a ↔ M.sat φ b)).resolve_right fun d => none ⟨φ, d⟩)
      notEquivalent

/-- The matching step under excluded middle, for list covers. -/
theorem exists_match_of_em (em : ∀ p : Prop, p ∨ ¬ p) (cover : ListCover M) {x y : S.Term}
    (equivalent : M.LogicallyEquivalent x y) (label : M.Label) {x' : S.Term}
    (step : M.act label x x') : ∃ y', M.act label y y' ∧ M.LogicallyEquivalent x' y' := by
  rcases em (∃ y', M.act label y y' ∧ M.LogicallyEquivalent x' y') with found | none
  · exact found
  · exfalso
    obtain ⟨R, covered⟩ := cover label y
    have separators : ∀ r ∈ R, ∃ φ : Formula M.Atom M.Label, M.sat φ x' ∧
        ((∃ t, M.act label y t ∧ S.Equiv t r) → ¬ M.sat φ r) := by
      intro r _
      rcases em (∃ t, M.act label y t ∧ S.Equiv t r) with ⟨t, stepT, equivalentT⟩ | unreachable
      · have notEquivalent : ¬ M.LogicallyEquivalent x' r := fun same =>
          none ⟨t, stepT, fun φ => (same φ).trans (M.sat_resp φ equivalentT).symm⟩
        obtain ⟨φ, holds, fails⟩ := separate_of_em em notEquivalent
        exact ⟨φ, holds, fun _ => fails⟩
      · exact ⟨.top, trivial, fun reached => absurd reached unreachable⟩
    obtain ⟨ψ, holds, fails⟩ := conjSeparatorOn (fun r => ∃ t, M.act label y t ∧ S.Equiv t r) R separators
    obtain ⟨y'', step'', holds''⟩ := (equivalent (.dia label ψ)).mp ⟨x', step, holds⟩
    obtain ⟨r, member, equivalentR⟩ := covered step''
    exact fails r member ⟨y'', step'', equivalentR⟩ ((M.sat_resp ψ equivalentR).mp holds'')

/-- **Excluded middle gives finitary adequacy on every system with list covers**, with no
`Classical.choice`. -/
theorem bisimilar_of_em (em : ∀ p : Prop, p ∨ ¬ p) (cover : ListCover M) {x y : S.Term}
    (equivalent : M.LogicallyEquivalent x y) : M.Bisimilar x y :=
  ⟨M.LogicallyEquivalent, isBisimulation_of_forth fun _ _ equivalent' label _ step =>
    exists_match_of_em em cover equivalent' label step, equivalent⟩

theorem em_of_dne (dne : ∀ p : Prop, ¬ ¬ p → p) : ∀ p : Prop, p ∨ ¬ p :=
  fun p => dne (p ∨ ¬ p) fun notEither => notEither (Or.inr fun holds => notEither (Or.inl holds))

/-! ### The probe -/

/-- The probe's states. -/
inductive Probe
  | x | y | a1 | a2 | b | c | d
  deriving DecidableEq

/-- `x` steps to `a1` and `a2`, `y` to `b`; `a2` and `b` step to `c`; `a1` steps to `d` exactly when
`stepProp` holds. -/
def probeAct (stepProp : Prop) : Probe → Probe → Prop
  | .x, t => t = .a1 ∨ t = .a2
  | .y, t => t = .b
  | .a1, t => t = .d ∧ stepProp
  | .a2, t => t = .c
  | .b, t => t = .c
  | .c, _ => False
  | .d, _ => False

/-- `c` is observed; `d` is observed exactly when `observeProp` holds. -/
def probeObs (observeProp : Prop) : Probe → Prop
  | .c => True
  | .d => observeProp
  | _ => False

/-- The probe's theory: equality as the equations. -/
@[implicit_reducible] def probeTheory (stepProp : Prop) : GSLT where
  Term := Probe
  equations := ⟨Eq, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
  rewrites := probeAct stepProp
  rewrites_resp_left := by
    intro left right target same reduces
    exact ⟨target, same ▸ reduces, rfl⟩
  rewrites_resp_right := by
    intro source target other reduces same
    exact same ▸ reduces

/-- **The probe**, with one unit atom and one unit label. -/
def probeSystem (stepProp observeProp : Prop) : System (probeTheory stepProp) where
  Atom := Unit
  Label := Unit
  observes _ s := probeObs observeProp s
  observes_resp := by
    intro atom left right same
    exact same ▸ Iff.rfl
  act _ := probeAct stepProp
  act_resp_left := by
    intro label left right target same reduces
    exact ⟨target, same ▸ reduces, rfl⟩
  act_resp_right := by
    intro label source target other reduces same
    exact same ▸ reduces

section Probe

variable {stepProp observeProp : Prop}

theorem probe_dia_dead_c (l : Unit) (φ : Formula Unit Unit) :
    ¬ (probeSystem stepProp observeProp).sat (.dia l φ) Probe.c := by
  rintro ⟨t, step, _⟩
  exact step

theorem probe_dia_dead_d (l : Unit) (φ : Formula Unit Unit) :
    ¬ (probeSystem stepProp observeProp).sat (.dia l φ) Probe.d := by
  rintro ⟨t, step, _⟩
  exact step

theorem probe_dia_a1 (l : Unit) (φ : Formula Unit Unit) :
    (probeSystem stepProp observeProp).sat (.dia l φ) Probe.a1 ↔
      stepProp ∧ (probeSystem stepProp observeProp).sat φ Probe.d := by
  constructor
  · rintro ⟨t, ⟨rfl, holdsS⟩, holds⟩
    exact ⟨holdsS, holds⟩
  · rintro ⟨holdsS, holds⟩
    exact ⟨Probe.d, ⟨rfl, holdsS⟩, holds⟩

theorem probe_dia_to_c {s : Probe} (toC : ∀ t, probeAct stepProp s t ↔ t = Probe.c) (l : Unit)
    (φ : Formula Unit Unit) :
    (probeSystem stepProp observeProp).sat (.dia l φ) s ↔
      (probeSystem stepProp observeProp).sat φ Probe.c := by
  constructor
  · rintro ⟨t, step, holds⟩
    rw [(toC t).mp step] at holds
    exact holds
  · intro holds
    exact ⟨Probe.c, (toC Probe.c).mpr rfl, holds⟩

theorem probe_dia_x (l : Unit) (φ : Formula Unit Unit) :
    (probeSystem stepProp observeProp).sat (.dia l φ) Probe.x ↔
      (probeSystem stepProp observeProp).sat φ Probe.a1 ∨
        (probeSystem stepProp observeProp).sat φ Probe.a2 := by
  constructor
  · rintro ⟨t, step | step, holds⟩
    · rw [step] at holds
      exact Or.inl holds
    · rw [step] at holds
      exact Or.inr holds
  · rintro (holds | holds)
    · exact ⟨Probe.a1, Or.inl rfl, holds⟩
    · exact ⟨Probe.a2, Or.inr rfl, holds⟩

theorem probe_dia_y (l : Unit) (φ : Formula Unit Unit) :
    (probeSystem stepProp observeProp).sat (.dia l φ) Probe.y ↔
      (probeSystem stepProp observeProp).sat φ Probe.b := by
  constructor
  · rintro ⟨t, step, holds⟩
    have same : t = Probe.b := step
    rw [same] at holds
    exact holds
  · intro holds
    exact ⟨Probe.b, rfl, holds⟩

/-- The two dead states, under the double negation of `observeProp`. -/
theorem probe_dead (nnQ : ¬ ¬ observeProp) (φ : Formula Unit Unit) :
    ((probeSystem stepProp observeProp).sat φ Probe.d →
        (probeSystem stepProp observeProp).sat φ Probe.c) ∧
      ((probeSystem stepProp observeProp).sat φ Probe.c ↔
        ¬ ¬ (probeSystem stepProp observeProp).sat φ Probe.d) := by
  induction φ with
  | top => exact ⟨fun _ => trivial, ⟨fun _ notTop => notTop trivial, fun _ => trivial⟩⟩
  | atom _ =>
    show (observeProp → True) ∧ (True ↔ ¬ ¬ observeProp)
    exact ⟨fun _ => trivial, ⟨fun _ => nnQ, fun _ => trivial⟩⟩
  | conj φ ψ ihφ ihψ =>
    obtain ⟨forthφ, nnφ⟩ := ihφ
    obtain ⟨forthψ, nnψ⟩ := ihψ
    refine ⟨fun both => ⟨forthφ both.1, forthψ both.2⟩, ⟨fun both notBoth => ?_, fun nn => ?_⟩⟩
    · exact nnφ.mp both.1 fun hφ => nnψ.mp both.2 fun hψ => notBoth ⟨hφ, hψ⟩
    · exact ⟨nnφ.mpr fun notφ => nn fun both => notφ both.1,
        nnψ.mpr fun notψ => nn fun both => notψ both.2⟩
  | neg φ ih =>
    obtain ⟨forth, nn⟩ := ih
    exact ⟨fun notD holdsC => nn.mp holdsC notD,
      ⟨fun notC nnnD => notC (nn.mpr nnnD), fun nnnD holdsC => nnnD (nn.mp holdsC)⟩⟩
  | dia l φ _ =>
    exact ⟨fun holds => absurd holds (probe_dia_dead_d l φ),
      ⟨fun holds => absurd holds (probe_dia_dead_c l φ),
        fun nn => absurd (nn (probe_dia_dead_d l φ)) id⟩⟩

/-- The two middle states, under the double negation of both propositions. -/
theorem probe_middle (nn : ¬ ¬ (stepProp ∧ observeProp)) (φ : Formula Unit Unit) :
    ((probeSystem stepProp observeProp).sat φ Probe.a1 →
        (probeSystem stepProp observeProp).sat φ Probe.a2) ∧
      ((probeSystem stepProp observeProp).sat φ Probe.a2 ↔
        ¬ ¬ (probeSystem stepProp observeProp).sat φ Probe.a1) := by
  have nnS : ¬ ¬ stepProp := fun notS => nn fun both => notS both.1
  have nnQ : ¬ ¬ observeProp := fun notQ => nn fun both => notQ both.2
  induction φ with
  | top => exact ⟨fun _ => trivial, ⟨fun _ notTop => notTop trivial, fun _ => trivial⟩⟩
  | atom _ =>
    show (False → False) ∧ (False ↔ ¬ ¬ False)
    exact ⟨id, ⟨False.elim, fun nnF => nnF id⟩⟩
  | conj φ ψ ihφ ihψ =>
    obtain ⟨forthφ, nnφ⟩ := ihφ
    obtain ⟨forthψ, nnψ⟩ := ihψ
    refine ⟨fun both => ⟨forthφ both.1, forthψ both.2⟩, ⟨fun both notBoth => ?_, fun nnBoth => ?_⟩⟩
    · exact nnφ.mp both.1 fun hφ => nnψ.mp both.2 fun hψ => notBoth ⟨hφ, hψ⟩
    · exact ⟨nnφ.mpr fun notφ => nnBoth fun both => notφ both.1,
        nnψ.mpr fun notψ => nnBoth fun both => notψ both.2⟩
  | neg φ ih =>
    obtain ⟨forth, nnIff⟩ := ih
    exact ⟨fun notA1 holdsA2 => nnIff.mp holdsA2 notA1,
      ⟨fun notA2 nnnA1 => notA2 (nnIff.mpr nnnA1), fun nnnA1 holdsA2 => nnnA1 (nnIff.mp holdsA2)⟩⟩
  | dia l φ _ =>
    obtain ⟨forthD, nnD⟩ := probe_dead (stepProp := stepProp) nnQ φ
    have a1Iff := probe_dia_a1 (stepProp := stepProp) (observeProp := observeProp) l φ
    have a2Iff := probe_dia_to_c (stepProp := stepProp) (observeProp := observeProp)
      (s := Probe.a2) (fun _ => Iff.rfl) l φ
    refine ⟨fun holds => a2Iff.mpr (forthD (a1Iff.mp holds).2), ⟨fun holds notA1 => ?_,
      fun nnA1 => a2Iff.mpr (nnD.mpr fun notD => nnA1 fun holdsA1 => notD (a1Iff.mp holdsA1).2)⟩⟩
    exact nnD.mp (a2Iff.mp holds) fun holdsD => nnS fun holdsS => notA1 (a1Iff.mpr ⟨holdsS, holdsD⟩)

/-- `a2` and `b` agree on every formula. -/
theorem probe_a2_b (φ : Formula Unit Unit) :
    (probeSystem stepProp observeProp).sat φ Probe.a2 ↔
      (probeSystem stepProp observeProp).sat φ Probe.b := by
  induction φ with
  | top => exact Iff.rfl
  | atom _ => exact Iff.rfl
  | conj φ ψ ihφ ihψ => exact and_congr ihφ ihψ
  | neg φ ih => exact not_congr ih
  | dia l φ _ =>
    exact (probe_dia_to_c (stepProp := stepProp) (observeProp := observeProp) (s := Probe.a2)
      (fun _ => Iff.rfl) l φ).trans (probe_dia_to_c (stepProp := stepProp)
        (observeProp := observeProp) (s := Probe.b) (fun _ => Iff.rfl) l φ).symm

/-- **Under the double negation of the two propositions, the probe's roots are logically
equivalent.** -/
theorem probe_logicallyEquivalent (nn : ¬ ¬ (stepProp ∧ observeProp)) :
    (probeSystem stepProp observeProp).LogicallyEquivalent Probe.x Probe.y := by
  intro φ
  induction φ with
  | top => exact Iff.rfl
  | atom _ => exact Iff.rfl
  | conj φ ψ ihφ ihψ => exact and_congr ihφ ihψ
  | neg φ ih => exact not_congr ih
  | dia l φ _ =>
    have xIff := probe_dia_x (stepProp := stepProp) (observeProp := observeProp) l φ
    have yIff := probe_dia_y (stepProp := stepProp) (observeProp := observeProp) l φ
    refine xIff.trans (Iff.trans ⟨?_, ?_⟩ yIff.symm)
    · rintro (holds | holds)
      · exact (probe_a2_b φ).mp ((probe_middle nn φ).1 holds)
      · exact (probe_a2_b φ).mp holds
    · intro holds
      exact Or.inr ((probe_a2_b φ).mpr holds)

/-- **A bisimulation between the probe's roots proves both propositions.** -/
theorem probe_of_bisimilar
    (bisimilar : (probeSystem stepProp observeProp).Bisimilar Probe.x Probe.y) :
    stepProp ∧ observeProp := by
  obtain ⟨R, bisimulation, related⟩ := bisimilar
  obtain ⟨t, stepT, relatedT⟩ := bisimulation.1 related () (show probeAct stepProp .x .a1 from Or.inl rfl)
  have isB : t = Probe.b := stepT
  subst isB
  obtain ⟨t', stepT', relatedT'⟩ :=
    bisimulation.2.1 relatedT () (show probeAct stepProp .b .c from rfl)
  obtain ⟨isD, holdsS⟩ := (show t' = Probe.d ∧ stepProp from stepT')
  subst isD
  exact ⟨holdsS, (bisimulation.2.2 relatedT' ()).mpr trivial⟩

/-- The probe's states, numbered. -/
def probeIndex : Probe → Fin 7
  | .x => 0
  | .y => 1
  | .a1 => 2
  | .a2 => 3
  | .b => 4
  | .c => 5
  | .d => 6

def probeOfIndex (i : Fin 7) : Probe :=
  match i.val with
  | 0 => .x
  | 1 => .y
  | 2 => .a1
  | 3 => .a2
  | 4 => .b
  | 5 => .c
  | _ => .d

def probeFin : Probe ≃ Fin 7 where
  toFun := probeIndex
  invFun := probeOfIndex
  left_inv s := by cases s <;> rfl
  right_inv := by
    intro i
    revert i
    decide

/-- The probe has finitely many states, with no choice. -/
theorem probe_univ_finite : (Set.univ : Set Probe).Finite :=
  Finite.intro ((Equiv.Set.univ Probe).trans probeFin)

/-- The probe is image-finite in the tree's sense. -/
theorem probe_imageFinite : (probeSystem stepProp observeProp).ImageFiniteModulo :=
  fun _ _ => ⟨Set.univ, probe_univ_finite, fun t _ => ⟨t, trivial, rfl⟩⟩

/-- With `observeProp` true the probe's observations are decided. -/
def probeDecideTrue : ∀ (a : Unit) (s : Probe), Decidable ((probeSystem stepProp True).observes a s)
  | _, .c => isTrue trivial
  | _, .d => isTrue trivial
  | _, .x => isFalse id
  | _, .y => isFalse id
  | _, .a1 => isFalse id
  | _, .a2 => isFalse id
  | _, .b => isFalse id

/-- The successors as lists. -/
def probeList : Probe → List Probe
  | .x => [.a1, .a2]
  | .y => [.b]
  | .a1 => [.d]
  | .a2 => [.c]
  | .b => [.c]
  | .c => []
  | .d => []

/-- With `stepProp` true the probe's successors are explicit lists. -/
def probeListSuccessors : ListSuccessors (probeSystem True observeProp) where
  succ _ s := probeList s
  act_iff _ s t := by
    cases s <;> simp [probeSystem, probeAct, probeList]

end Probe

/-- The tree's reflection principle: finitary adequacy on every system image-finite up to its
equations. -/
def ImageFiniteReflection : Prop :=
  ∀ (S : GSLT.{0}) (M : System.{0, 0} S), M.ImageFiniteModulo →
    ∀ left right, M.LogicallyEquivalent left right → M.Bisimilar left right

/-- Finitary adequacy on every system with finite covers and decided observations. -/
def CoverAdequacy : Prop :=
  ∀ (S : GSLT.{0}) (M : System.{0, 0} S), (∀ a t, Decidable (M.observes a t)) →
    M.ImageFiniteModulo → ∀ x y, M.LogicallyEquivalent x y → M.Bisimilar x y

/-- Finitary adequacy on every system with explicit successor lists, observations undecided. -/
def ListPropAdequacy : Prop :=
  ∀ (S : GSLT.{0}) (M : System.{0, 0} S), ListSuccessors M →
    ∀ x y, M.LogicallyEquivalent x y → M.Bisimilar x y

theorem em_of_coverAdequacy (adequacy : CoverAdequacy) : ∀ p : Prop, p ∨ ¬ p :=
  em_of_dne fun A nnA => (probe_of_bisimilar (adequacy (probeTheory A) (probeSystem A True)
    probeDecideTrue probe_imageFinite Probe.x Probe.y
    (probe_logicallyEquivalent fun notBoth => nnA fun a => notBoth ⟨a, trivial⟩))).1

theorem em_of_listPropAdequacy (adequacy : ListPropAdequacy) : ∀ p : Prop, p ∨ ¬ p :=
  em_of_dne fun A nnA => (probe_of_bisimilar (adequacy (probeTheory True) (probeSystem True A)
    probeListSuccessors Probe.x Probe.y
    (probe_logicallyEquivalent fun notBoth => nnA fun a => notBoth ⟨trivial, a⟩))).2

theorem imageFiniteReflection_of_em (em : ∀ p : Prop, p ∨ ¬ p) : ImageFiniteReflection :=
  fun _ _ finite _ _ equivalent => bisimilar_of_em em (listCover_of_imageFiniteModulo finite) equivalent

/-- **The tree's reflection principle is excluded middle.** -/
theorem imageFiniteReflection_iff_em : ImageFiniteReflection ↔ ∀ p : Prop, p ∨ ¬ p :=
  ⟨fun reflection => em_of_coverAdequacy fun S M _ finite => reflection S M finite,
    imageFiniteReflection_of_em⟩

/-- **With finite covers, deciding the observations does not lower the price.** -/
theorem coverAdequacy_iff_em : CoverAdequacy ↔ ∀ p : Prop, p ∨ ¬ p :=
  ⟨em_of_coverAdequacy, fun em S M _ finite => imageFiniteReflection_of_em em S M finite⟩

/-- **With explicit lists and undecided observations, the price is excluded middle.** -/
theorem listPropAdequacy_iff_em : ListPropAdequacy ↔ ∀ p : Prop, p ∨ ¬ p :=
  ⟨em_of_listPropAdequacy, fun em _ _ P _ _ equivalent =>
    bisimilar_of_em em (listCover_of_listSuccessors P) equivalent⟩

/-! ## Apartness with a witness -/

/-- **Apartness with a witness**: a formula true at the first state and false at the second. -/
def Apart (M : System.{uA, uL} S) (x y : S.Term) : Prop :=
  ∃ φ : Formula M.Atom M.Label, M.sat φ x ∧ ¬ M.sat φ y

/-- **A witness refutes bisimilarity.** -/
theorem not_bisimilar_of_apart {x y : S.Term} (apart : Apart M x y) : ¬ M.Bisimilar x y :=
  fun bisimilar =>
    let ⟨φ, holds, fails⟩ := apart
    fails ((M.logicallyEquivalent_of_bisimilar bisimilar φ).mp holds)

theorem apart_symm {x y : S.Term} (apart : Apart M x y) : Apart M y x :=
  let ⟨φ, holds, fails⟩ := apart
  ⟨.neg φ, fails, fun notHolds => notHolds holds⟩

/-- **On list-presented systems, the absence of a witness is logical equivalence.** -/
theorem not_apart_iff_logicallyEquivalent (P : ListPresented M) {x y : S.Term} :
    ¬ Apart M x y ↔ M.LogicallyEquivalent x y := by
  constructor
  · intro notApart φ
    cases P.decideSat φ x with
    | isTrue holds =>
        cases P.decideSat φ y with
        | isTrue holdsY => exact ⟨fun _ => holdsY, fun _ => holds⟩
        | isFalse failsY => exact absurd ⟨φ, holds, failsY⟩ notApart
    | isFalse fails =>
        cases P.decideSat φ y with
        | isTrue holdsY => exact absurd ⟨.neg φ, fails, fun notY => notY holdsY⟩ notApart
        | isFalse failsY => exact ⟨fun h => absurd h fails, fun h => absurd h failsY⟩
  · rintro equivalent ⟨φ, holds, fails⟩
    exact fails ((equivalent φ).mp holds)

/-- **A witness is found by a search through the levels.** -/
theorem apart_iff_exists_level (P : ListPresented M) {atoms : ℕ → Option M.Atom}
    {labels : ℕ → Option M.Label} (atomsOnto : ∀ a, ∃ i, atoms i = some a)
    (labelsOnto : ∀ l, ∃ i, labels i = some l) {x y : S.Term} :
    Apart M x y ↔ ∃ d, agreeAt P atoms labels x y d = false := by
  constructor
  · rintro ⟨φ, holds, fails⟩
    obtain ⟨d, hd⟩ := exists_level atomsOnto labelsOnto φ
    refine ⟨d, false_of_not_true fun agree => fails ?_⟩
    exact ((agreeAt_true_iff P).mp agree φ hd).mp holds
  · rintro ⟨d, disagree⟩
    exact separator_of_disagree P disagree

/-- **Markov's principle turns "not logically equivalent" into a witness.** -/
theorem apart_of_mp (mp : MP) (P : ListPresented M) {atoms : ℕ → Option M.Atom}
    {labels : ℕ → Option M.Label} (atomsOnto : ∀ a, ∃ i, atoms i = some a)
    (labelsOnto : ∀ l, ∃ i, labels i = some l) {x y : S.Term}
    (notEquivalent : ¬ M.LogicallyEquivalent x y) : Apart M x y := by
  obtain ⟨d, hd⟩ := mp (fun d => !agreeAt P atoms labels x y d) fun allFalse =>
    notEquivalent ((logicallyEquivalent_iff_agree P atomsOnto labelsOnto x y).mpr fun d =>
      true_of_not_eq_false (allFalse d))
  exact (apart_iff_exists_level P atomsOnto labelsOnto).mpr ⟨d, false_of_not_eq_true hd⟩

/-- **LPO decides between logical equivalence and a witness.** -/
theorem logicallyEquivalent_or_apart_of_lpo (lpo : LPO) (P : ListPresented M)
    {atoms : ℕ → Option M.Atom} {labels : ℕ → Option M.Label}
    (atomsOnto : ∀ a, ∃ i, atoms i = some a) (labelsOnto : ∀ l, ∃ i, labels i = some l)
    (x y : S.Term) : M.LogicallyEquivalent x y ∨ Apart M x y := by
  rcases lpo fun d => !agreeAt P atoms labels x y d with ⟨d, hd⟩ | allFalse
  · exact Or.inr ((apart_iff_exists_level P atomsOnto labelsOnto).mpr ⟨d, false_of_not_eq_true hd⟩)
  · exact Or.inl ((logicallyEquivalent_iff_agree P atomsOnto labelsOnto x y).mpr fun d =>
      true_of_not_eq_false (allFalse d))

/-! ## Controls -/

namespace Controls

/-- Positive control: with a zero stream the tree's probe roots are bisimilar, so the probe does not
force any principle there. -/
theorem zero_stream_bisimilar :
    (ConstructiveModalStrength.system fun _ => false).Bisimilar (.root true) (.root false) :=
  ConstructiveModalStrength.Controls.zero_roots_bisimilar

/-- Positive control: when the proposition holds, the probe's roots are bisimilar. -/
theorem probe_bisimilar_of_true : (probeSystem True True).Bisimilar Probe.x Probe.y := by
  refine ⟨fun s t => s = t ∨ (s = .x ∧ t = .y) ∨ (s = .a1 ∧ t = .b) ∨ (s = .a2 ∧ t = .b) ∨
    (s = .d ∧ t = .c), ⟨?_, ?_, ?_⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · rintro s t (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) _ s' step
    · exact ⟨s', step, Or.inl rfl⟩
    · rcases step with rfl | rfl
      · exact ⟨Probe.b, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      · exact ⟨Probe.b, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
    · obtain ⟨rfl, _⟩ := (show s' = Probe.d ∧ True from step)
      exact ⟨Probe.c, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩
    · have isC : s' = Probe.c := step
      subst isC
      exact ⟨Probe.c, rfl, Or.inl rfl⟩
    · exact absurd step id
  · rintro s t (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) _ t' step
    · exact ⟨t', step, Or.inl rfl⟩
    · have isB : t' = Probe.b := step
      subst isB
      exact ⟨Probe.a1, Or.inl rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · have isC : t' = Probe.c := step
      subst isC
      exact ⟨Probe.d, ⟨rfl, trivial⟩, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩
    · have isC : t' = Probe.c := step
      subst isC
      exact ⟨Probe.c, rfl, Or.inl rfl⟩
    · exact absurd step id
  · rintro s t (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) _
    · exact Iff.rfl
    · exact Iff.rfl
    · exact Iff.rfl
    · exact Iff.rfl
    · exact ⟨fun _ => trivial, fun _ => trivial⟩

/-- Negative control: when the step fails, the probe's roots are apart (`a1` is stuck, `b` is not),
so a witness is available and no principle is needed to refute bisimilarity. -/
theorem probe_apart_of_false : Apart (probeSystem False True) Probe.y Probe.x := by
  refine ⟨.neg (.dia () (.neg (.dia () .top))), ?_, ?_⟩
  · rintro ⟨t, step, notStep⟩
    have isB : t = Probe.b := step
    subst isB
    exact notStep ⟨Probe.c, rfl, trivial⟩
  · intro notHolds
    exact notHolds ⟨Probe.a1, Or.inl rfl, fun ⟨_, ⟨_, impossible⟩, _⟩ => impossible⟩

end Controls

#print axioms deMorgan_of_llpo
#print axioms llpo_of_deMorgan
#print axioms llpo_list
#print axioms exists_level
#print axioms logicallyEquivalent_iff_agree
#print axioms bisimilar_of_llpo
#print axioms llpo_of_listAdequacy
#print axioms listAdequacy_iff_llpo
#print axioms listCover_of_imageFiniteModulo
#print axioms bisimilar_of_em
#print axioms probe_logicallyEquivalent
#print axioms probe_of_bisimilar
#print axioms probe_imageFinite
#print axioms em_of_coverAdequacy
#print axioms em_of_listPropAdequacy
#print axioms imageFiniteReflection_iff_em
#print axioms coverAdequacy_iff_em
#print axioms listPropAdequacy_iff_em
#print axioms not_bisimilar_of_apart
#print axioms apart_symm
#print axioms not_apart_iff_logicallyEquivalent
#print axioms apart_iff_exists_level
#print axioms apart_of_mp
#print axioms logicallyEquivalent_or_apart_of_lpo
#print axioms Controls.probe_bisimilar_of_true
#print axioms Controls.probe_apart_of_false

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.AdequacyPrice
