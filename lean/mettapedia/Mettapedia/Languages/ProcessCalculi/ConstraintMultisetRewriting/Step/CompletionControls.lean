import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CompletionFiring
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionControls

/-!
# Controls for ground completion: a convergent run, a word problem, an unfair run

The signature of the superposition controls: one unary function `p` and constants `⊤ < a < b`,
ordered by depth and then by the constant, a total ground simplification order.

* **A fair run completes** (`classic_run`, `classic_convergent`): from `E₀ = {p²(a) ≈ a,
  p³(a) ≈ a}`, seven admitted moves (Orient, Orient, Collapse, Orient, Collapse, Simplify, Delete)
  reach the single rule `p(a) → a`. The run is fair and no equation is left, so the correctness
  theorem applies: `p(a) → a` is convergent and decides the theory of `E₀`.
* **A word problem decided by normal forms** (`iterate_follows`, `b_not_a`, `word_commit`,
  `word_refuted`): `pᵏ(a) ≈ a` follows from `E₀` for every `k`, and the readout commits on
  `p⁵(a) ≈ a`; `b ≈ a` does not follow, the normal forms `b` and `a` differ, and the readout is
  refuted.
* **An unfair run** (`unfair_run`, `unfair_not_confluent`, `unfair_not_fair`,
  `unfair_misses`): it orients both equations and stops. The critical pair `p(a) ≈ a` of
  `p²(a) → a` inside `p³(a) → a` is never deduced; the rules `{p²(a) → a, p³(a) → a}` are not
  confluent, `p(a) ≈ a` follows from `E₀` yet `p(a)` and `a` are distinct normal forms, and the run
  is not fair.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Completion.Controls

open Mettapedia.Logic.LP
open Superposition (Ctx Ctx.fill_comp Rw Joins Plain clauses syntactic guarded)
open Superposition.Controls (sig a b p lt_p ctxP)
open _root_.Relation (ReflTransGen EqvGen Join)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-! ## Terms -/

theorem fill_app (args : Fin 1 → GroundTerm sig) (inner : Ctx sig) (t : GroundTerm sig) :
    (Ctx.app () args 0 inner).fill t = p (inner.fill t) := by
  show GroundTerm.app () (Function.update args 0 (inner.fill t)) = GroundTerm.app () fun _ => inner.fill t
  congr 1
  funext i
  rw [Subsingleton.elim i 0, Function.update_self]

theorem fillP (t : GroundTerm sig) : ctxP.fill t = p t := fill_app _ .hole t

/-- `p²(a)`. -/
def p2 : GroundTerm sig := p (p a)
/-- `p³(a)`. -/
def p3 : GroundTerm sig := p p2

theorem a_lt_pa : a < p a := lt_p a
theorem a_lt_p2 : a < p2 := (lt_p a).trans (lt_p (p a))
theorem a_lt_p3 : a < p3 := a_lt_p2.trans (lt_p p2)
theorem pa_lt_p2 : p a < p2 := lt_p (p a)
theorem ctxP_proper : ctxP ≠ .hole := fun same => by cases same

/-- A term is irreducible by rules whose left sides are all above it. -/
theorem irreducible_of_below {R : GroundTerm sig → GroundTerm sig → Prop} {u : GroundTerm sig}
    (above : ∀ l r, R l r → u < l) : IsNormal (Rw R) u := by
  rintro v ⟨c, l, r, rule, same, -⟩
  exact absurd ((Superposition.Ctx.le_fill c l).trans_eq same.symm) (not_le.mpr (above l r rule))

/-! ## Occurrences and moves -/

/-- The items of the occurrences. -/
def label : ℕ → Item sig
  | 0 => .eqn s(p2, a)
  | 1 => .eqn s(p3, a)
  | 2 => .rule p2 a
  | 3 => .rule p3 a
  | 4 => .eqn s(p a, a)
  | 5 => .rule (p a) a
  | 6 => .eqn s(p a, a)
  | 8 => .eqn s(p a, a)
  | _ => .eqn s(a, a)

/-- Orient `p²(a) ≈ a`. -/
def m0 : Move sig ℕ := orientMove 0 2 p2 a
/-- Orient `p³(a) ≈ a`. -/
def m1 : Move sig ℕ := orientMove 1 3 p3 a
/-- Collapse `p³(a) → a` by `p²(a) → a` inside it, making `p(a) ≈ a`. -/
def m2 : Move sig ℕ := collapseMove 3 2 4 p3 a p2 a ctxP
/-- Orient `p(a) ≈ a`. -/
def m3 : Move sig ℕ := orientMove 4 5 (p a) a
/-- Collapse `p²(a) → a` by `p(a) → a` inside it, making `p(a) ≈ a`. -/
def m4 : Move sig ℕ := collapseMove 2 5 6 p2 a (p a) a ctxP
/-- Simplify `p(a) ≈ a` by `p(a) → a` to `a ≈ a`. -/
def m5 : Move sig ℕ := simplifyMove 6 5 7 (p a) a (p a) a .hole
/-- Delete `a ≈ a`. -/
def m6 : Move sig ℕ := deleteMove 7 a a

def c0 : Configuration (Item sig) ℕ := ⟨[], {0, 1}⟩
def c1 : Configuration (Item sig) ℕ := m0.firing.firing.result label c0
def c2 : Configuration (Item sig) ℕ := m1.firing.firing.result label c1
def c3 : Configuration (Item sig) ℕ := m2.firing.firing.result label c2
def c4 : Configuration (Item sig) ℕ := m3.firing.firing.result label c3
def c5 : Configuration (Item sig) ℕ := m4.firing.firing.result label c4
def c6 : Configuration (Item sig) ℕ := m5.firing.firing.result label c5
def c7 : Configuration (Item sig) ℕ := m6.firing.firing.result label c6

theorem c1_present : c1.present = {1, 2} := by decide
theorem c2_present : c2.present = {2, 3} := by decide
theorem c3_present : c3.present = {2, 4} := by decide
theorem c4_present : c4.present = {2, 5} := by decide
theorem c5_present : c5.present = {5, 6} := by decide
theorem c6_present : c6.present = {5, 7} := by decide
theorem c7_present : c7.present = {5} := by decide

theorem plain0 : Plain c0 := fun e member => by cases member

theorem admits0 : (guarded (syntactic _) label).Admits (s := c0) m0.firing :=
  (orient_admits_iff label c0 0 2 p2 a).mpr ⟨⟨by decide, rfl⟩, ⟨by decide, rfl⟩, plain0, a_lt_p2⟩

theorem admits1 : (guarded (syntactic _) label).Admits (s := c1) m1.firing :=
  (orient_admits_iff label c1 1 3 p3 a).mpr ⟨⟨by rw [c1_present]; decide, rfl⟩,
    ⟨by rw [c1_present]; decide, rfl⟩, Move.plain label admits0, a_lt_p3⟩

theorem admits2 : (guarded (syntactic _) label).Admits (s := c2) m2.firing :=
  (collapse_admits_iff label c2 3 2 4 p3 a p2 a ctxP).mpr ⟨⟨by rw [c2_present]; decide, rfl⟩,
    ⟨by rw [c2_present]; decide, rfl⟩, by decide, ⟨by rw [c2_present]; decide, by rw [fillP]; rfl⟩,
    Move.plain label admits1, (fillP p2).symm, ctxP_proper⟩

theorem admits3 : (guarded (syntactic _) label).Admits (s := c3) m3.firing :=
  (orient_admits_iff label c3 4 5 (p a) a).mpr ⟨⟨by rw [c3_present]; decide, rfl⟩,
    ⟨by rw [c3_present]; decide, rfl⟩, Move.plain label admits2, a_lt_pa⟩

theorem admits4 : (guarded (syntactic _) label).Admits (s := c4) m4.firing :=
  (collapse_admits_iff label c4 2 5 6 p2 a (p a) a ctxP).mpr ⟨⟨by rw [c4_present]; decide, rfl⟩,
    ⟨by rw [c4_present]; decide, rfl⟩, by decide, ⟨by rw [c4_present]; decide, by rw [fillP]; rfl⟩,
    Move.plain label admits3, (fillP (p a)).symm, ctxP_proper⟩

theorem admits5 : (guarded (syntactic _) label).Admits (s := c5) m5.firing :=
  (simplify_admits_iff label c5 6 5 7 (p a) a (p a) a .hole).mpr ⟨⟨by rw [c5_present]; decide, rfl⟩,
    ⟨by rw [c5_present]; decide, rfl⟩, by decide, ⟨by rw [c5_present]; decide, rfl⟩,
    Move.plain label admits4, rfl⟩

theorem admits6 : (guarded (syntactic _) label).Admits (s := c6) m6.firing :=
  (delete_admits_iff label c6 7 a a).mpr ⟨⟨by rw [c6_present]; decide, rfl⟩, Move.plain label admits5, rfl⟩

/-! ## Refused moves and independent moves -/

/-- **Orient the wrong way is refused**: `a → p(a)` would not decrease. -/
theorem orient_wrong_way_refused (C : Configuration (Item sig) ℕ) (o made : ℕ) :
    ¬ (guarded (syntactic _) label).Admits (s := C) (orientMove o made a (p a)).firing :=
  fun admitted => absurd ((orient_admits_iff label C o made a (p a)).mp admitted).2.2.2 (not_lt.mpr a_lt_pa.le)

/-- **Collapse at the root is refused**: the left side must strictly encompass the rule's. -/
theorem collapse_root_refused (C : Configuration (Item sig) ℕ) (o oRule made : ℕ) (s t l r : GroundTerm sig) :
    ¬ (guarded (syntactic _) label).Admits (s := C) (collapseMove o oRule made s t l r .hole).firing :=
  fun admitted => ((collapse_admits_iff label C o oRule made s t l r .hole).mp admitted).2.2.2.2.2.2 rfl

/-- **Simplify by a rule that does not match is refused**: `p²(a)` is not `p(a)`. -/
theorem simplify_mismatch_refused (C : Configuration (Item sig) ℕ) (o oRule made : ℕ) :
    ¬ (guarded (syntactic _) label).Admits (s := C) (simplifyMove o oRule made (p a) a p2 a .hole).firing :=
  fun admitted => absurd ((simplify_admits_iff label C o oRule made (p a) a p2 a .hole).mp admitted).2.2.2.2.2
    (ne_of_lt pa_lt_p2)

theorem admits1_at_start : (guarded (syntactic _) label).Admits (s := c0) m1.firing :=
  (orient_admits_iff label c0 1 3 p3 a).mpr ⟨⟨by decide, rfl⟩, ⟨by decide, rfl⟩, plain0, a_lt_p3⟩

theorem orients_apart : Apart m0 m1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [m0, m1, orientMove, Move.takePairs, Move.readPairs, Move.makePairs, Rule.takes, Rule.reads,
      Rule.makes]

/-- **The two Orient moves on different equations are independent**, and their two orders are
trace-equivalent runs. -/
theorem orients_independent :
    (Superposition.guardedTransport (syntactic _) label).Independent c0 m0.firing m1.firing ∧
      ∃ r r' : (guarded (syntactic _) label).Run c0,
        r.word.map Sigma.snd = [m0.firing, m1.firing] ∧ r'.word.map Sigma.snd = [m1.firing, m0.firing] ∧
        (Superposition.guardedTransport (syntactic _) label).TraceEquiv c0 r r' :=
  ⟨Move.independent label orients_apart admits0 admits1_at_start,
    Move.traceEquiv label orients_apart admits0 admits1_at_start⟩

/-- **Deduce of the critical pair `p(a) ≈ a`**, of `p²(a) → a` inside `p³(a) → a`, is admitted; **the
Collapse of `p³(a) → a` takes its premise, so the two are dependent.** -/
theorem collapse_deduce_controls :
    (guarded (syntactic _) label).Admits (s := c2) (deduceMove 2 3 8 p2 a p3 a ctxP).firing ∧
      ¬ (Superposition.guardedTransport (syntactic _) label).Independent c2 m2.firing
        (deduceMove 2 3 8 p2 a p3 a ctxP).firing :=
  ⟨(deduce_admits_iff label c2 2 3 8 p2 a p3 a ctxP).mpr ⟨⟨by rw [c2_present]; decide, rfl⟩,
      ⟨by rw [c2_present]; decide, rfl⟩, ⟨by rw [c2_present]; decide, by rw [fillP]; rfl⟩,
      Move.plain label admits1, fillP p2⟩,
    (Move.takes_premise_dependent label (by simp [m2, collapseMove, Rule.takes])
      (by simp [m2, collapseMove, deduceMove, Move.takePairs, Move.readPairs, Rule.takes, Rule.reads])
      admits2).2⟩

/-! ## A fair run completes -/

/-- The configurations of the run, idle after the seventh move. -/
def config : ℕ → Configuration (Item sig) ℕ
  | 0 => c0
  | 1 => c1
  | 2 => c2
  | 3 => c3
  | 4 => c4
  | 5 => c5
  | 6 => c6
  | _ => c7

/-- **The run of seven admitted moves.** -/
theorem classic_run : IsRun label config := fun i => match i with
  | 0 => Or.inr ⟨m0, admits0, rfl⟩
  | 1 => Or.inr ⟨m1, admits1, rfl⟩
  | 2 => Or.inr ⟨m2, admits2, rfl⟩
  | 3 => Or.inr ⟨m3, admits3, rfl⟩
  | 4 => Or.inr ⟨m4, admits4, rfl⟩
  | 5 => Or.inr ⟨m5, admits5, rfl⟩
  | 6 => Or.inr ⟨m6, admits6, rfl⟩
  | _ + 7 => Or.inl rfl

/-- The start: `p²(a) ≈ a` and `p³(a) ≈ a`. -/
def E₀ : Set (Item sig) := clauses label c0

/-- The completed system: `p(a) → a`. -/
def Rinf : Set (Item sig) := {Item.rule (p a) a}

theorem clauses_c0 (x : Item sig) : x ∈ E₀ ↔ x = .eqn s(p2, a) ∨ x = .eqn s(p3, a) := by
  constructor
  · rintro ⟨o, member, rfl⟩
    have : o = 0 ∨ o = 1 := by simpa [c0] using member
    rcases this with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩

theorem clauses_c7 : clauses label c7 = Rinf := by
  ext x
  constructor
  · rintro ⟨o, member, rfl⟩
    rw [c7_present, Finset.mem_singleton] at member
    subst member
    rfl
  · intro member
    rw [Set.mem_singleton_iff.mp member]
    exact ⟨5, by rw [c7_present]; exact Finset.mem_singleton_self 5, rfl⟩

theorem limit_classic : limit (fun i => clauses label (config i)) = Rinf := by
  rw [limit_of_idle (k := 7) fun j le => ?_]
  · exact clauses_c7
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' le
    rfl

theorem start_decreasing : Decreasing (clauses label (config 0)) := by
  intro l r member
  rcases (clauses_c0 _).mp member with same | same <;> cases same

theorem classic_fair : Fair (fun i => clauses label (config i)) := by
  intro l₁ r₁ l₂ r₂ d one two overlap
  rw [limit_classic] at one two
  simp only [Rinf, Set.mem_singleton_iff, Item.rule.injEq] at one two
  obtain ⟨rfl, rfl⟩ := one
  obtain ⟨rfl, rfl⟩ := two
  have hole := Superposition.Ctx.eq_hole_of_fill_eq d overlap
  subst hole
  exact ⟨0, EqvGen.refl _⟩

theorem classic_noEquations : ∀ e, Item.eqn e ∉ limit (fun i => clauses label (config i)) := by
  intro e member
  rw [limit_classic] at member
  simp [Rinf] at member

/-- **A fair run completes**: `p(a) → a` is decreasing, terminating and confluent, and decides the
theory of `E₀` by joinability. -/
theorem classic_convergent :
    Decreasing Rinf ∧ (∀ u, Acc (fun v u => Rw (rules Rinf) u v) u) ∧ Confluent (Rw (rules Rinf)) ∧
      ∀ s t, EqvGen (EqStep E₀) s t ↔ Joins (rules Rinf) s t := by
  have result := (classic_run.derivation label).convergent start_decreasing classic_fair classic_noEquations
  rw [limit_classic] at result
  exact result

/-! ## A word problem decided by normal forms -/

/-- The context `pᵏ(□)`. -/
def ctxIter : ℕ → Ctx sig
  | 0 => .hole
  | k + 1 => (ctxIter k).comp ctxP

theorem ctxIter_fill : ∀ (k : ℕ) (t : GroundTerm sig), (ctxIter k).fill t = p^[k] t
  | 0, _ => rfl
  | k + 1, t => by
      rw [ctxIter, Ctx.fill_comp, fillP, ctxIter_fill k, Function.iterate_succ_apply]

theorem iterate_rewrites : ∀ k, ReflTransGen (Rw (rules Rinf)) (p^[k] a) a
  | 0 => .refl
  | k + 1 => by
      refine ReflTransGen.head ?_ (iterate_rewrites k)
      refine ⟨ctxIter k, p a, a, Set.mem_singleton _, ?_, ?_⟩
      · rw [ctxIter_fill, Function.iterate_succ_apply]
      · rw [ctxIter_fill]

/-- **`pᵏ(a) ≈ a` follows from `E₀` for every `k`**, decided by normal forms. -/
theorem iterate_follows (k : ℕ) : EqvGen (EqStep E₀) (p^[k] a) a :=
  (classic_convergent.2.2.2 _ _).mpr ⟨a, iterate_rewrites k, .refl⟩

theorem const_normal (c : Fin 3) : IsNormal (Rw (rules Rinf)) (GroundTerm.const c) := by
  rintro v ⟨d, l, r, rule, same, -⟩
  simp only [rules, Rinf, Set.mem_singleton_iff, Item.rule.injEq] at rule
  obtain ⟨rfl, rfl⟩ := rule
  cases d with
  | hole => cases same
  | app f args i inner => cases same

/-- **`b ≈ a` does not follow from `E₀`**: `b` and `a` are distinct normal forms. -/
theorem b_not_a : ¬ EqvGen (EqStep E₀) b a := by
  intro derived
  obtain ⟨w, left, right⟩ := (classic_convergent.2.2.2 _ _).mp derived
  have one := (const_normal 2).reflTransGen_eq left
  have two := (const_normal 1).reflTransGen_eq right
  have same : (2 : Fin 3) = 1 := GroundTerm.const.inj (one.symm.trans two)
  exact absurd same (by decide)

theorem classic_reports : Reports E₀ Rinf true := by
  have reports := (classic_run.derivation label).reports start_decreasing classic_fair classic_noEquations
  rw [limit_classic] at reports
  exact reports

theorem classic_succeeded : Succeeded Rinf true := ⟨rfl, fun e member => by simp [Rinf] at member⟩

/-- **The word readout commits on `p⁵(a) ≈ a`.** -/
theorem word_commit : (wordReadout Rinf true (p^[5] a) a).verdict = .commit := by
  rw [wordReadout_of_succeeded classic_succeeded, if_pos (show Joins (rules Rinf) (p^[5] a) a from ⟨a, iterate_rewrites 5, .refl⟩),
    Search.Outcome.verdict_eq_commit_iff]
  simp

/-- **The word readout refutes `b ≈ a`.** -/
theorem word_refuted : (wordReadout Rinf true b a).verdict = .refuted := by
  have notJoined : ¬ Joins (rules Rinf) b a := fun joined =>
    b_not_a ((classic_convergent.2.2.2 _ _).mpr joined)
  rw [wordReadout_of_succeeded classic_succeeded, if_neg notJoined, Search.Outcome.verdict_eq_refuted_iff]

/-- **The committed readout is sound**: `p⁵(a) ≈ a` follows from `E₀`. -/
theorem word_commit_sound : EqvGen (EqStep E₀) (p^[5] a) a := wordReadout_commit classic_reports word_commit

/-- **The refuted readout is sound**: `b ≈ a` does not follow, and the normal forms differ. -/
theorem word_refuted_sound : ¬ EqvGen (EqStep E₀) b a ∧
    ∀ (nb : Mettapedia.Logic.Relation.NormalizationResult (Rw (rules Rinf)) b)
      (na : Mettapedia.Logic.Relation.NormalizationResult (Rw (rules Rinf)) a), nb.normalForm ≠ na.normalForm :=
  wordReadout_refuted classic_reports word_refuted

/-! ## An unfair run -/

/-- The unfair run: it orients both equations and stops. -/
def unfairConfig : ℕ → Configuration (Item sig) ℕ
  | 0 => c0
  | 1 => c1
  | _ => c2

theorem unfair_run : IsRun label unfairConfig := fun i => match i with
  | 0 => Or.inr ⟨m0, admits0, rfl⟩
  | 1 => Or.inr ⟨m1, admits1, rfl⟩
  | _ + 2 => Or.inl rfl

/-- The rules it stops with: `p²(a) → a` and `p³(a) → a`. -/
def R₂ : Set (Item sig) := {Item.rule p2 a, Item.rule p3 a}

theorem clauses_c2 : clauses label c2 = R₂ := by
  ext x
  constructor
  · rintro ⟨o, member, rfl⟩
    rw [c2_present] at member
    rcases Finset.mem_insert.mp member with rfl | member
    · exact Or.inl rfl
    · rw [Finset.mem_singleton.mp member]
      exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨2, by rw [c2_present]; decide, rfl⟩
    · exact ⟨3, by rw [c2_present]; decide, rfl⟩

theorem limit_unfair : limit (fun i => clauses label (unfairConfig i)) = R₂ := by
  rw [limit_of_idle (k := 2) fun j le => ?_]
  · exact clauses_c2
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' le
    rfl

theorem below_R₂ {u : GroundTerm sig} (below : u < p2) : IsNormal (Rw (rules R₂)) u := by
  refine irreducible_of_below fun l r rule => ?_
  simp only [rules, R₂, Set.mem_insert_iff, Set.mem_singleton_iff, Item.rule.injEq] at rule
  rcases rule with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact below
  · exact below.trans (lt_p p2)

/-- **The unfair rules are not confluent**: `p³(a)` rewrites to `a` and to `p(a)`, distinct normal
forms. -/
theorem unfair_not_confluent : ¬ Confluent (Rw (rules R₂)) := by
  intro confluent
  have root : Rw (rules R₂) p3 a := ⟨.hole, p3, a, Or.inr rfl, rfl, rfl⟩
  have inner : Rw (rules R₂) p3 (p a) := ⟨ctxP, p2, a, Or.inl rfl, (fillP p2).symm, (fillP a).symm⟩
  obtain ⟨w, left, right⟩ := confluent p3 (p a) a (.single inner) (.single root)
  have one := (below_R₂ pa_lt_p2).reflTransGen_eq left
  have two := (below_R₂ a_lt_p2).reflTransGen_eq right
  exact absurd (one.symm.trans two) (ne_of_gt a_lt_pa)

/-- **The unfair run misses a consequence**: `p(a) ≈ a` follows from `E₀`, yet `p(a)` and `a` are
distinct normal forms of its rules. -/
theorem unfair_misses : EqvGen (EqStep E₀) (p a) a ∧ ¬ Joins (rules R₂) (p a) a := by
  refine ⟨iterate_follows 1, fun ⟨w, left, right⟩ => ?_⟩
  have one := (below_R₂ pa_lt_p2).reflTransGen_eq left
  have two := (below_R₂ a_lt_p2).reflTransGen_eq right
  exact absurd (one.symm.trans two) (ne_of_gt a_lt_pa)

/-- **The unfair run is not fair**: were it fair, the correctness theorem would make its rules
confluent. -/
theorem unfair_not_fair : ¬ Fair (fun i => clauses label (unfairConfig i)) := by
  intro fair
  have confluent := (unfair_run.derivation label).confluent start_decreasing fair fun e member => by
    rw [limit_unfair] at member
    simp [R₂] at member
  rw [limit_unfair] at confluent
  exact unfair_not_confluent confluent

#print axioms fillP
#print axioms c7_present
#print axioms admits0
#print axioms admits2
#print axioms admits4
#print axioms admits5
#print axioms admits6
#print axioms classic_run
#print axioms limit_classic
#print axioms classic_fair
#print axioms classic_convergent
#print axioms iterate_follows
#print axioms b_not_a
#print axioms word_commit
#print axioms word_refuted
#print axioms word_commit_sound
#print axioms orient_wrong_way_refused
#print axioms collapse_root_refused
#print axioms simplify_mismatch_refused
#print axioms orients_independent
#print axioms collapse_deduce_controls
#print axioms word_refuted_sound
#print axioms unfair_not_confluent
#print axioms unfair_misses
#print axioms unfair_not_fair

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Completion.Controls
