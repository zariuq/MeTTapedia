import Mettapedia.Logic.ASP.Nogoods

/-!
# Hall steps: a counting step for answer-set certificates

A *constraint rule* is a rule of the program whose head is a falsum atom (`Program.Falsum`):
every rule for that head, this one included, has the negation of the head in its body. No
stable model holds a falsum atom, so no stable model satisfies the body of any of its rules;
many constraint rules may share one head, as integrity constraints `:- B` all read as rules
`f :- B, not f` of one atom `f`. Two shapes of constraint rule matter here:

* an **at-least-one** rule `h :- not a₁, …, not aₖ, not h`: every stable model holds some
  `aᵢ` other than `h` (its *group*);
* an **exclusion** rule `h :- a, b, not h`: no stable model holds both `a` and `b`.

A *clique* is a set of atoms any two of which an exclusion rule forbids together.  When the
groups of some at-least-one rules are pairwise disjoint and each of their atoms is either in a
set `E` or in one of fewer cliques than there are groups, every stable model holds an atom of
`E` (`hall_step_sound`): otherwise each group would need a true atom in its own clique.  The
clause `E` is a sound certificate step that resolution needs exponentially many steps to
derive for pigeonhole-shaped programs; the check is counting.
-/

namespace Mettapedia.Logic.ASP

universe u v w

variable {A : Type u}

namespace Program

variable (P : Program A)

/-- A stable model is supported: `step M M = M`. -/
theorem stable_step_eq {M : Set A} (h : P.Stable M) : P.step M M = M := by
  have hfix := P.glOp_fixed M
  rw [← h] at hfix
  exact hfix

/-- A rule whose body a stable model satisfies has its head in the model. -/
theorem head_mem_of_holds {M : Set A} (hM : P.Stable M) {r : Rule A} (hr : r ∈ P)
    (hb : r.Holds M M) : r.head ∈ M := by
  rw [← P.stable_step_eq hM]
  exact ⟨r, hr, rfl, hb⟩

/-- A constraint rule: a rule of the program with the negation of its head in its body, of a
head that every rule for it negates. -/
def ConstraintRule (r : Rule A) : Prop :=
  r ∈ P ∧ r.head ∈ r.neg ∧ ∀ q ∈ P, q.head = r.head → r.head ∈ q.neg

/-- A constraint rule is a rule of a falsum atom. -/
theorem constraintRule_iff {r : Rule A} : P.ConstraintRule r ↔ r ∈ P ∧ P.Falsum r.head := by
  constructor
  · rintro ⟨hr, -, every⟩
    exact ⟨hr, ⟨r, hr, rfl⟩, every⟩
  · rintro ⟨hr, -, every⟩
    exact ⟨hr, every r hr rfl, every⟩

theorem constraint_head_not_mem {M : Set A} (hM : P.Stable M) {r : Rule A}
    (hc : P.ConstraintRule r) : r.head ∉ M :=
  P.not_mem_of_falsum (P.stable_supported hM) ((P.constraintRule_iff).mp hc).2

theorem constraint_body_fails {M : Set A} (hM : P.Stable M) {r : Rule A}
    (hc : P.ConstraintRule r) : ¬ r.Holds M M := fun hb =>
  P.constraint_head_not_mem hM hc (P.head_mem_of_holds hM hc.1 hb)

/-- An at-least-one rule: some atom of its group holds. -/
theorem at_least_one {M : Set A} (hM : P.Stable M) {r : Rule A} (hc : P.ConstraintRule r)
    (hpos : r.pos = []) : ∃ a ∈ r.neg, a ≠ r.head ∧ a ∈ M := by
  by_contra hno
  push Not at hno
  apply P.constraint_body_fails hM hc
  refine ⟨by simp [hpos], fun b hb hbM => ?_⟩
  by_cases hbh : b = r.head
  · rw [hbh] at hbM
    exact P.constraint_head_not_mem hM hc hbM
  · exact hno b hb hbh hbM

/-- An exclusion rule: its two atoms do not both hold. -/
theorem exclusion {M : Set A} (hM : P.Stable M) {r : Rule A} (hc : P.ConstraintRule r)
    {a b : A} (hpos : r.pos = [a, b]) (hneg : r.neg = [r.head]) : ¬ (a ∈ M ∧ b ∈ M) := by
  rintro ⟨ha, hb⟩
  apply P.constraint_body_fails hM hc
  refine ⟨fun x hx => ?_, fun x hx hxM => ?_⟩
  · rw [hpos] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · rw [hneg, List.mem_singleton] at hx
    rw [hx] at hxM
    exact P.constraint_head_not_mem hM hc hxM

end Program

/-- **Counting.**  Pairwise disjoint groups, each with a member in `M`; cliques, none with two
members in `M`; every group member in `E` or in a clique; `E` disjoint from `M`.  Then there
are at least as many cliques as groups. -/
theorem hall_count {ι : Type v} {κ : Type w} (S : Finset ι) (G : ι → Set A) (N : Finset κ)
    (C : κ → Set A) (E M : Set A)
    (alo : ∀ i ∈ S, ∃ a ∈ G i, a ∈ M)
    (amo : ∀ k ∈ N, ∀ a ∈ C k, ∀ b ∈ C k, a ∈ M → b ∈ M → a = b)
    (disj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ a, a ∈ G i → a ∉ G j)
    (cover : ∀ i ∈ S, ∀ a ∈ G i, a ∈ E ∨ ∃ k ∈ N, a ∈ C k)
    (outside : ∀ a ∈ E, a ∉ M) :
    S.card ≤ N.card := by
  classical
  rcases S.eq_empty_or_nonempty with hS | ⟨i0, hi0⟩
  · simp [hS]
  have pick : ∀ i ∈ S, ∃ k ∈ N, ∃ a, a ∈ G i ∧ a ∈ M ∧ a ∈ C k := by
    intro i hi
    obtain ⟨a, ha, hMa⟩ := alo i hi
    rcases cover i hi a ha with hE | ⟨k, hk, hak⟩
    · exact absurd hMa (outside a hE)
    · exact ⟨k, hk, a, ha, hMa, hak⟩
  obtain ⟨k0, -, a0, -⟩ := pick i0 hi0
  have : Nonempty κ := ⟨k0⟩
  have : Nonempty A := ⟨a0⟩
  choose! f hfN g hgG hgM hgC using pick
  refine Finset.card_le_card_of_injOn f (fun i hi => hfN i hi) ?_
  intro i hi j hj hij
  by_contra hne
  have hgj : g j ∈ C (f i) := by
    rw [hij]
    exact hgC j hj
  have hsame : g i = g j :=
    amo (f i) (hfN i hi) (g i) (hgC i hi) (g j) hgj (hgM i hi) (hgM j hj)
  have hgi : g i ∈ G j := by
    rw [hsame]
    exact hgG j hj
  exact disj i hi j hj hne (g i) (hgG i hi) hgi

namespace Program

variable (P : Program A)

/-- **A Hall step is sound.**  Take at-least-one rules `R i` (`i ∈ S`) whose groups are pairwise
disjoint, and cliques `C k` (`k ∈ N`), sets of atoms any two distinct of which an exclusion rule
of the program forbids together.  If every group atom is in `E` or in some clique, and there are
fewer cliques than groups, then every stable model holds an atom of `E`. -/
theorem hall_step_sound {ι : Type v} {κ : Type w} {M : Set A} (hM : P.Stable M)
    (S : Finset ι) (R : ι → Rule A) (N : Finset κ) (C : κ → Set A) (E : Set A)
    (hR : ∀ i ∈ S, P.ConstraintRule (R i) ∧ (R i).pos = [])
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ a, a ∈ (R i).neg → a ≠ (R i).head →
      ¬ (a ∈ (R j).neg ∧ a ≠ (R j).head))
    (hclique : ∀ k ∈ N, ∀ a ∈ C k, ∀ b ∈ C k, a ≠ b →
      ∃ r, P.ConstraintRule r ∧ (r.pos = [a, b] ∨ r.pos = [b, a]) ∧ r.neg = [r.head])
    (hcover : ∀ i ∈ S, ∀ a ∈ (R i).neg, a ≠ (R i).head → a ∈ E ∨ ∃ k ∈ N, a ∈ C k)
    (hcard : N.card < S.card) :
    ∃ a ∈ E, a ∈ M := by
  by_contra hno
  push Not at hno
  refine absurd (hall_count S (fun i => {a | a ∈ (R i).neg ∧ a ≠ (R i).head}) N C E M
    ?_ ?_ ?_ ?_ hno) (not_le.mpr hcard)
  · intro i hi
    obtain ⟨a, ha, hah, haM⟩ := P.at_least_one hM (hR i hi).1 (hR i hi).2
    exact ⟨a, ⟨ha, hah⟩, haM⟩
  · intro k hk a ha b hb haM hbM
    by_contra hab
    obtain ⟨r, hc, hpos | hpos, hneg⟩ := hclique k hk a ha b hb hab
    · exact P.exclusion hM hc hpos hneg ⟨haM, hbM⟩
    · exact P.exclusion hM hc hpos hneg ⟨hbM, haM⟩
  · intro i hi j hj hij a hai haj
    exact hdisj i hi j hj hij a hai.1 hai.2 haj
  · intro i hi a ha
    exact hcover i hi a ha.1 ha.2

end Program

/-! ## Deciding the rule shapes

The certificate checker recognizes the rules of a Hall step by Boolean tests on the program. A
rule of the program is a constraint rule exactly when its head passes the falsum test
(`Program.isConstraintRule_iff`). -/

section Decide

variable [DecidableEq A]

namespace Program

variable (P : Program A)

/-- `r` is a rule of a falsum atom. -/
def isConstraintRule (r : Rule A) : Bool := P.falsum r.head

/-- `r` is an at-least-one rule with a nonempty group. -/
def isAtLeastOne (r : Rule A) : Bool :=
  P.isConstraintRule r && r.pos.isEmpty && !r.group.isEmpty

/-- Some exclusion rule of the program forbids `a` and `b` together. -/
def excludes (a b : A) : Bool :=
  P.any fun r => P.isConstraintRule r && r.neg == [r.head] && (r.pos == [a, b] || r.pos == [b, a])

theorem isConstraintRule_iff {r : Rule A} (hr : r ∈ P) : P.isConstraintRule r = true ↔ P.ConstraintRule r := by
  rw [isConstraintRule, falsum_iff, constraintRule_iff]
  exact ⟨fun h => ⟨hr, h⟩, And.right⟩

theorem constraintRule_of_isConstraintRule {r : Rule A} (hr : r ∈ P) (h : P.isConstraintRule r = true) :
    P.ConstraintRule r :=
  (P.isConstraintRule_iff hr).mp h

theorem atLeastOne_of_isAtLeastOne {r : Rule A} (hr : r ∈ P) (h : P.isAtLeastOne r = true) :
    P.ConstraintRule r ∧ r.pos = [] := by
  simp only [isAtLeastOne, Bool.and_eq_true, List.isEmpty_iff] at h
  exact ⟨P.constraintRule_of_isConstraintRule hr h.1.1, h.1.2⟩

theorem exclusion_of_excludes {a b : A} (h : P.excludes a b = true) :
    ∃ r, P.ConstraintRule r ∧ (r.pos = [a, b] ∨ r.pos = [b, a]) ∧ r.neg = [r.head] := by
  obtain ⟨r, hr, hok⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
  exact ⟨r, P.constraintRule_of_isConstraintRule hr hok.1.1, hok.2, hok.1.2⟩

end Program

end Decide

/-! ## Controls -/

section Controls

/-- Three pigeons, two holes, over atoms `0..5` (`in p h` is `2p + h`) and violation atoms:
three at-least-one rules and, per hole, three exclusion rules. -/
def php32 : Program Nat :=
  [⟨10, [], [0, 1, 10]⟩, ⟨11, [], [2, 3, 11]⟩, ⟨12, [], [4, 5, 12]⟩,
   ⟨20, [0, 2], [20]⟩, ⟨21, [0, 4], [21]⟩, ⟨22, [2, 4], [22]⟩,
   ⟨23, [1, 3], [23]⟩, ⟨24, [1, 5], [24]⟩, ⟨25, [3, 5], [25]⟩]

/-- Positive control: the Hall step with the empty clause refutes three pigeons in two holes. -/
theorem php32_no_stable_model (M : Set Nat) : ¬ php32.Stable M := by
  intro hM
  have hcons : ∀ r ∈ php32, php32.ConstraintRule r := by
    intro r hr
    refine ⟨hr, ?_, ?_⟩ <;> simp [php32] at hr <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [php32]
  obtain ⟨a, ha, -⟩ := php32.hall_step_sound hM (Finset.univ : Finset (Fin 3))
    (fun i => [⟨10, [], [0, 1, 10]⟩, ⟨11, [], [2, 3, 11]⟩, ⟨12, [], [4, 5, 12]⟩][i])
    (Finset.univ : Finset (Fin 2))
    (fun k => if k = 0 then {0, 2, 4} else {1, 3, 5}) (∅ : Set Nat)
    (by
      intro i _
      refine ⟨hcons _ ?_, ?_⟩ <;> fin_cases i <;> simp [php32])
    (by intro i _ j _ hij a; fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega)
    (by
      intro k _ a ha b hb hab
      fin_cases k <;> simp at ha hb <;>
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        first
        | exact absurd rfl hab
        | exact ⟨⟨20, [0, 2], [20]⟩, hcons _ (by simp [php32]), Or.inl rfl, rfl⟩
        | exact ⟨⟨20, [0, 2], [20]⟩, hcons _ (by simp [php32]), Or.inr rfl, rfl⟩
        | exact ⟨⟨21, [0, 4], [21]⟩, hcons _ (by simp [php32]), Or.inl rfl, rfl⟩
        | exact ⟨⟨21, [0, 4], [21]⟩, hcons _ (by simp [php32]), Or.inr rfl, rfl⟩
        | exact ⟨⟨22, [2, 4], [22]⟩, hcons _ (by simp [php32]), Or.inl rfl, rfl⟩
        | exact ⟨⟨22, [2, 4], [22]⟩, hcons _ (by simp [php32]), Or.inr rfl, rfl⟩
        | exact ⟨⟨23, [1, 3], [23]⟩, hcons _ (by simp [php32]), Or.inl rfl, rfl⟩
        | exact ⟨⟨23, [1, 3], [23]⟩, hcons _ (by simp [php32]), Or.inr rfl, rfl⟩
        | exact ⟨⟨24, [1, 5], [24]⟩, hcons _ (by simp [php32]), Or.inl rfl, rfl⟩
        | exact ⟨⟨24, [1, 5], [24]⟩, hcons _ (by simp [php32]), Or.inr rfl, rfl⟩
        | exact ⟨⟨25, [3, 5], [25]⟩, hcons _ (by simp [php32]), Or.inl rfl, rfl⟩
        | exact ⟨⟨25, [3, 5], [25]⟩, hcons _ (by simp [php32]), Or.inr rfl, rfl⟩)
    (by intro i _ a ha hah; fin_cases i <;> simp at ha hah ⊢ <;> omega)
    (by simp)
  exact ha

/-- Negative control: a constraint rule's head never holds, but the head of an ordinary rule
may: `p :- not q` alone has the stable model `{p}`, so its rule is no constraint rule. -/
theorem even_rule_not_constraint :
    ¬ Program.ConstraintRule ([⟨0, [], [1]⟩] : Program Nat) ⟨0, [], [1]⟩ := by
  simp [Program.ConstraintRule]

end Controls

end Mettapedia.Logic.ASP
