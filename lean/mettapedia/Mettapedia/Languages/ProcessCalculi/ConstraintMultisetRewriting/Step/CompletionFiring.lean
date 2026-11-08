import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CompletionCorrectness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionSaturation

/-!
# Completion rules as firings of the guarded step

Equations and rules are stored items: occurrences of the guarded one-frame step
(`Superposition.guarded`) over the syntactic action, each labelled by its item.

## Moves

A **move** (`Move`) is a rule of completion together with the occurrences it takes, reads and
makes. As a firing (`Move.firing`) it **takes** the occurrence of the item the rule takes, **reads**
the occurrences of the rules it uses, **makes** a fresh occurrence of its conclusion, and **guards**
the rule: the match of its premises and its order condition.

* **Admission** (`Move.admits_iff`), and for each rule (`deduce_admits_iff`, `orient_admits_iff`,
  `delete_admits_iff`, `simplify_admits_iff`, `compose_admits_iff`, `collapse_admits_iff`): a move
  is admitted exactly when its premises are present with their items, the taken occurrence is not
  also read, the made occurrence is fresh and carries the conclusion, the knowledge is plain, and
  the guard holds. Orient asks `t < s`; Collapse asks that `s` strictly encompass `l`.
* **An admitted move is one transition** on the items present (`Move.transition`), so it keeps the
  equational theory (`Move.theory_iff`) and keeps rules decreasing (`Move.decreasing`).
* **What a move takes is redundant in what remains** (`Move.takes_redundant`): the taken occurrence
  is gone, and every step by its item is provable from the remaining items by steps of smaller
  cost. This is how Simplify, Compose and Collapse take only what the rest proves more simply.
* **Runs of admitted moves are derivations** (`IsRun.derivation`), so the correctness theorem of
  `CompletionCorrectness` applies to them.

## Independence

* Two admitted moves that are **apart** (`Apart`: neither takes an occurrence the other uses, and
  they make different occurrences) are **independent** (`Move.independent`): each is admitted
  after the other, and the two orders are trace-equivalent runs (`Move.traceEquiv`).
* A move that **takes a premise** of another makes the two **dependent**
  (`Move.takes_premise_dependent`); for instance a Collapse that takes a rule a Deduce reads
  (`collapse_deduce_dependent`).

Joinable critical pairs are not independent firings: joinability is confluence of one rewrite
system, while independence asks that each firing survive the other.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Completion

open Mettapedia.Logic.LP
open Superposition (Ctx Ctx.fill_comp syntactic clauseFiring clauseFiring_admits_iff clauseFiring_plain
  guarded guardedTransport guarded_independent_iff Plain clauses GuardedFiring)
open Interface (Transport)
open _root_.Relation (EqvGen)

universe uO

variable {sig : LPSignature} {O : Type uO}

theorem Rule.takes_cases (ρ : Rule sig) : ρ.takes = [] ∨ ∃ x, ρ.takes = [x] := by
  cases ρ <;> simp [Rule.takes]

theorem Rule.makes_cases (ρ : Rule sig) : ρ.makes = [] ∨ ∃ x, ρ.makes = [x] := by
  cases ρ <;> simp [Rule.makes]

/-- **A completion move**: a rule with the occurrences it takes, reads and makes. -/
structure Move (sig : LPSignature) (O : Type uO) where
  rule : Rule sig
  taken : O
  reads : List O
  made : O
  arity : reads.length = rule.reads.length

namespace Move

/-- The taken occurrence with its item, if the rule takes one. -/
def takePairs (m : Move sig O) : List (O × Item sig) := m.rule.takes.map fun x => (m.taken, x)

/-- The read occurrences with their items. -/
def readPairs (m : Move sig O) : List (O × Item sig) := m.reads.zip m.rule.reads

/-- The made occurrence with its item, if the rule makes one. -/
def makePairs (m : Move sig O) : List (O × Item sig) := m.rule.makes.map fun x => (m.made, x)

theorem readPairs_snd (m : Move sig O) : m.readPairs.map Prod.snd = m.rule.reads :=
  List.map_snd_zip (le_of_eq m.arity.symm)

theorem mem_takePairs {m : Move sig O} {p : O × Item sig} : p ∈ m.takePairs ↔ p.1 = m.taken ∧ p.2 ∈ m.rule.takes := by
  unfold takePairs
  constructor
  · rintro member
    obtain ⟨x, inX, rfl⟩ := List.mem_map.mp member
    exact ⟨rfl, inX⟩
  · rintro ⟨first, second⟩
    exact List.mem_map.mpr ⟨p.2, second, by rw [← first]⟩

theorem mem_makePairs {m : Move sig O} {p : O × Item sig} : p ∈ m.makePairs ↔ p.1 = m.made ∧ p.2 ∈ m.rule.makes := by
  unfold makePairs
  constructor
  · rintro member
    obtain ⟨x, inX, rfl⟩ := List.mem_map.mp member
    exact ⟨rfl, inX⟩
  · rintro ⟨first, second⟩
    exact List.mem_map.mpr ⟨p.2, second, by rw [← first]⟩

theorem takePairs_nodup (m : Move sig O) : (m.takePairs.map Prod.fst).Nodup := by
  rcases m.rule.takes_cases with none | ⟨x, one⟩ <;> simp [takePairs, *]

theorem makePairs_nodup (m : Move sig O) : (m.makePairs.map Prod.fst).Nodup := by
  rcases m.rule.makes_cases with none | ⟨x, one⟩ <;> simp [makePairs, *]

variable [Preorder (GroundTerm sig)]

/-- **A move as a firing**: it takes, reads and makes its occurrences and guards its rule. -/
def firing (m : Move sig O) : GuardedFiring (Item sig) Unit O :=
  clauseFiring m.takePairs m.readPairs m.makePairs m.rule.guard

end Move

section Firings

variable [Preorder (GroundTerm sig)] [DecidableEq O] (label : O → Item sig)

/-- **Admission of a move**: its premises are present with their items, the taken occurrence is not
also read, the made occurrence is fresh and carries the conclusion, the knowledge is plain, and the
guard holds. -/
theorem Move.admits_iff (C : Configuration (Item sig) O) (m : Move sig O) :
    (guarded (syntactic _) label).Admits (s := C) m.firing ↔
      (∀ p ∈ m.takePairs ++ m.readPairs, p.1 ∈ C.present ∧ label p.1 = p.2) ∧
      (∀ p ∈ m.takePairs, ∀ q ∈ m.readPairs, p.1 ≠ q.1) ∧
      (∀ p ∈ m.makePairs, p.1 ∉ C.present ∧ label p.1 = p.2) ∧ Plain C ∧ m.rule.guard := by
  rw [Move.firing, clauseFiring_admits_iff]
  constructor
  · rintro ⟨-, -, present, apart, fresh, plain, guard⟩
    exact ⟨present, apart, fresh, plain, guard⟩
  · rintro ⟨present, apart, fresh, plain, guard⟩
    exact ⟨m.takePairs_nodup, m.makePairs_nodup, present, apart, fresh, plain, guard⟩

/-- The occurrences present after a move. -/
theorem Move.present_result (C : Configuration (Item sig) O) (m : Move sig O) :
    (m.firing.firing.result label C).present =
      (C.present \ (m.takePairs.map Prod.fst).toFinset) ∪ (m.makePairs.map Prod.fst).toFinset :=
  rfl

/-- **An admitted move is one transition** on the items present. -/
theorem Move.transition {C : Configuration (Item sig) O} {m : Move sig O}
    (admitted : (guarded (syntactic _) label).Admits (s := C) m.firing) :
    Transition m.rule (clauses label C) (clauses label (m.firing.firing.result label C)) := by
  obtain ⟨present, apart, fresh, -, guard⟩ := (Move.admits_iff label C m).mp admitted
  have after := Move.present_result label C m
  have read_of : ∀ x ∈ m.rule.reads, ∃ p ∈ m.readPairs, p.2 = x := by
    intro x member
    rw [← m.readPairs_snd] at member
    obtain ⟨p, inP, rfl⟩ := List.mem_map.mp member
    exact ⟨p, inP, rfl⟩
  have taken_of : ∀ o, o ∈ (m.takePairs.map Prod.fst).toFinset → ∃ x ∈ m.rule.takes, o = m.taken ∧
      (m.taken, x) ∈ m.takePairs := by
    intro o member
    obtain ⟨p, inP, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    obtain ⟨first, second⟩ := Move.mem_takePairs.mp inP
    exact ⟨p.2, second, first, Move.mem_takePairs.mpr ⟨rfl, second⟩⟩
  refine ⟨guard, fun x member => ?_, fun x member => ?_, fun x member => ?_, fun x member notTaken => ?_,
    fun x member => ?_⟩
  · rcases List.mem_append.mp member with inT | inR
    · have pair : (m.taken, x) ∈ m.takePairs := Move.mem_takePairs.mpr ⟨rfl, inT⟩
      exact ⟨m.taken, (present _ (List.mem_append_left _ pair)).1, (present _ (List.mem_append_left _ pair)).2⟩
    · obtain ⟨p, inP, rfl⟩ := read_of x inR
      exact ⟨p.1, (present p (List.mem_append_right _ inP)).1, (present p (List.mem_append_right _ inP)).2⟩
  · obtain ⟨p, inP, rfl⟩ := read_of x member
    refine ⟨p.1, ?_, (present p (List.mem_append_right _ inP)).2⟩
    rw [after]
    refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨(present p (List.mem_append_right _ inP)).1, ?_⟩)
    intro taken
    obtain ⟨y, -, same, pair⟩ := taken_of _ taken
    exact apart _ pair p inP same.symm
  · have pair : (m.made, x) ∈ m.makePairs := Move.mem_makePairs.mpr ⟨rfl, member⟩
    refine ⟨m.made, ?_, (fresh _ pair).2⟩
    rw [after]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, pair, rfl⟩))
  · obtain ⟨o, inC, rfl⟩ := member
    refine ⟨o, ?_, rfl⟩
    rw [after]
    refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨inC, fun taken => ?_⟩)
    obtain ⟨y, inY, same, pair⟩ := taken_of _ taken
    have labelled := (present _ (List.mem_append_left _ pair)).2
    rw [← same] at labelled
    exact notTaken (labelled ▸ inY)
  · obtain ⟨o, inAfter, rfl⟩ := member
    rw [after] at inAfter
    rcases Finset.mem_union.mp inAfter with kept | made
    · exact Or.inl ⟨o, (Finset.mem_sdiff.mp kept).1, rfl⟩
    · obtain ⟨p, inP, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp made)
      obtain ⟨-, item⟩ := Move.mem_makePairs.mp inP
      exact Or.inr ((fresh p inP).2 ▸ item)

/-- **Admitted moves keep the knowledge plain.** -/
theorem Move.plain {C : Configuration (Item sig) O} {m : Move sig O}
    (admitted : (guarded (syntactic _) label).Admits (s := C) m.firing) :
    Plain (m.firing.firing.result label C) :=
  clauseFiring_plain label admitted

variable [SimplificationOrder sig]

/-- **Every admitted move keeps the equational theory** of the items present. -/
theorem Move.theory_iff {C : Configuration (Item sig) O} {m : Move sig O}
    (admitted : (guarded (syntactic _) label).Admits (s := C) m.firing) (a b : GroundTerm sig) :
    EqvGen (EqStep (clauses label C)) a b ↔ EqvGen (EqStep (clauses label (m.firing.firing.result label C))) a b :=
  (Move.transition label admitted).theory_iff a b

/-- **Admitted moves keep rules decreasing.** -/
theorem Move.decreasing {C : Configuration (Item sig) O} {m : Move sig O}
    (admitted : (guarded (syntactic _) label).Admits (s := C) m.firing) (decreasing : Decreasing (clauses label C)) :
    Decreasing (clauses label (m.firing.firing.result label C)) :=
  (Move.transition label admitted).decreasing decreasing

/-- **What a move takes is redundant in what remains**: the taken occurrence is gone, and every
step by its item is provable from the remaining items by steps of smaller cost. -/
theorem Move.takes_redundant {C : Configuration (Item sig) O} {m : Move sig O}
    (admitted : (guarded (syntactic _) label).Admits (s := C) m.firing) (decreasing : Decreasing (clauses label C))
    {x : Item sig} (taken : x ∈ m.rule.takes) :
    m.taken ∉ (m.firing.firing.result label C).present ∧
      Redundant (clauses label (m.firing.firing.result label C)) x := by
  obtain ⟨present, -, fresh, -, -⟩ := (Move.admits_iff label C m).mp admitted
  have pair : (m.taken, x) ∈ m.takePairs := Move.mem_takePairs.mpr ⟨rfl, taken⟩
  refine ⟨?_, (Move.transition label admitted).taken_redundant decreasing x taken⟩
  rw [Move.present_result]
  intro member
  rcases Finset.mem_union.mp member with kept | made
  · exact (Finset.mem_sdiff.mp kept).2 (List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, pair, rfl⟩))
  · obtain ⟨p, inP, same⟩ := List.mem_map.mp (List.mem_toFinset.mp made)
    exact (fresh p inP).1 (same ▸ (present _ (List.mem_append_left _ pair)).1)

end Firings

/-! ## Each rule as a firing -/

section Rules

variable [Preorder (GroundTerm sig)] [DecidableEq O] (label : O → Item sig) (C : Configuration (Item sig) O)

/-- Deduce: read `l₁ → r₁` at `o₁` and `l₂ → r₂` at `o₂`, make `d[r₁] ≈ r₂` at `made`. -/
def deduceMove (o₁ o₂ made : O) (l₁ r₁ l₂ r₂ : GroundTerm sig) (d : Ctx sig) : Move sig O :=
  ⟨.deduce l₁ r₁ l₂ r₂ d, made, [o₁, o₂], made, rfl⟩

/-- Orient: take `s ≈ t` at `o`, make `s → t` at `made`. -/
def orientMove (o made : O) (s t : GroundTerm sig) : Move sig O := ⟨.orient s t, o, [], made, rfl⟩

/-- Delete: take `s ≈ t` at `o`. -/
def deleteMove (o : O) (s t : GroundTerm sig) : Move sig O := ⟨.delete s t, o, [], o, rfl⟩

/-- Simplify: take `s ≈ t` at `o`, read `l → r` at `oRule`, make `c[r] ≈ t` at `made`. -/
def simplifyMove (o oRule made : O) (s t l r : GroundTerm sig) (c : Ctx sig) : Move sig O :=
  ⟨.simplify s t l r c, o, [oRule], made, rfl⟩

/-- Compose: take `s → t` at `o`, read `l → r` at `oRule`, make `s → c[r]` at `made`. -/
def composeMove (o oRule made : O) (s t l r : GroundTerm sig) (c : Ctx sig) : Move sig O :=
  ⟨.compose s t l r c, o, [oRule], made, rfl⟩

/-- Collapse: take `s → t` at `o`, read `l → r` at `oRule`, make `c[r] ≈ t` at `made`. -/
def collapseMove (o oRule made : O) (s t l r : GroundTerm sig) (c : Ctx sig) : Move sig O :=
  ⟨.collapse s t l r c, o, [oRule], made, rfl⟩

/-- **Deduce is admitted** exactly when both rules are present, the made occurrence is fresh and
carries the critical pair, and the rules overlap. -/
theorem deduce_admits_iff (o₁ o₂ made : O) (l₁ r₁ l₂ r₂ : GroundTerm sig) (d : Ctx sig) :
    (guarded (syntactic _) label).Admits (s := C) (deduceMove o₁ o₂ made l₁ r₁ l₂ r₂ d).firing ↔
      (o₁ ∈ C.present ∧ label o₁ = .rule l₁ r₁) ∧ (o₂ ∈ C.present ∧ label o₂ = .rule l₂ r₂) ∧
      (made ∉ C.present ∧ label made = .eqn s(d.fill r₁, r₂)) ∧ Plain C ∧ d.fill l₁ = l₂ := by
  rw [Move.admits_iff]
  simp [deduceMove, Move.takePairs, Move.readPairs, Move.makePairs, Rule.takes, Rule.reads, Rule.makes,
    Rule.guard, and_assoc]

/-- **Orient is admitted** exactly when the equation is present, the made occurrence is fresh and
carries the rule, and the order orients it: `t < s`. -/
theorem orient_admits_iff (o made : O) (s t : GroundTerm sig) :
    (guarded (syntactic _) label).Admits (s := C) (orientMove o made s t).firing ↔
      (o ∈ C.present ∧ label o = .eqn s(s, t)) ∧ (made ∉ C.present ∧ label made = .rule s t) ∧
        Plain C ∧ t < s := by
  rw [Move.admits_iff]
  simp [orientMove, Move.takePairs, Move.readPairs, Move.makePairs, Rule.takes, Rule.reads, Rule.makes,
    Rule.guard, and_assoc]

/-- **Delete is admitted** exactly when the trivial equation is present. -/
theorem delete_admits_iff (o : O) (s t : GroundTerm sig) :
    (guarded (syntactic _) label).Admits (s := C) (deleteMove o s t).firing ↔
      (o ∈ C.present ∧ label o = .eqn s(s, t)) ∧ Plain C ∧ s = t := by
  rw [Move.admits_iff]
  simp [deleteMove, Move.takePairs, Move.readPairs, Move.makePairs, Rule.takes, Rule.reads, Rule.makes,
    Rule.guard, and_assoc]

/-- **Simplify is admitted** exactly when the equation and the rule are present at different
occurrences, the made occurrence is fresh and carries the simplified equation, and the rule
matches: `s = c[l]`. -/
theorem simplify_admits_iff (o oRule made : O) (s t l r : GroundTerm sig) (c : Ctx sig) :
    (guarded (syntactic _) label).Admits (s := C) (simplifyMove o oRule made s t l r c).firing ↔
      (o ∈ C.present ∧ label o = .eqn s(s, t)) ∧ (oRule ∈ C.present ∧ label oRule = .rule l r) ∧ o ≠ oRule ∧
        (made ∉ C.present ∧ label made = .eqn s(c.fill r, t)) ∧ Plain C ∧ s = c.fill l := by
  rw [Move.admits_iff]
  simp [simplifyMove, Move.takePairs, Move.readPairs, Move.makePairs, Rule.takes, Rule.reads, Rule.makes,
    Rule.guard, and_assoc]

/-- **Compose is admitted** exactly when both rules are present at different occurrences, the made
occurrence is fresh and carries the composed rule, and the rule matches: `t = c[l]`. -/
theorem compose_admits_iff (o oRule made : O) (s t l r : GroundTerm sig) (c : Ctx sig) :
    (guarded (syntactic _) label).Admits (s := C) (composeMove o oRule made s t l r c).firing ↔
      (o ∈ C.present ∧ label o = .rule s t) ∧ (oRule ∈ C.present ∧ label oRule = .rule l r) ∧ o ≠ oRule ∧
        (made ∉ C.present ∧ label made = .rule s (c.fill r)) ∧ Plain C ∧ t = c.fill l := by
  rw [Move.admits_iff]
  simp [composeMove, Move.takePairs, Move.readPairs, Move.makePairs, Rule.takes, Rule.reads, Rule.makes,
    Rule.guard, and_assoc]

/-- **Collapse is admitted** exactly when both rules are present at different occurrences, the made
occurrence is fresh and carries the equation, the rule matches, `s = c[l]`, and `s` strictly
encompasses `l`: `c ≠ □`. -/
theorem collapse_admits_iff (o oRule made : O) (s t l r : GroundTerm sig) (c : Ctx sig) :
    (guarded (syntactic _) label).Admits (s := C) (collapseMove o oRule made s t l r c).firing ↔
      (o ∈ C.present ∧ label o = .rule s t) ∧ (oRule ∈ C.present ∧ label oRule = .rule l r) ∧ o ≠ oRule ∧
        (made ∉ C.present ∧ label made = .eqn s(c.fill r, t)) ∧ Plain C ∧ s = c.fill l ∧ c ≠ .hole := by
  rw [Move.admits_iff]
  simp [collapseMove, Move.takePairs, Move.readPairs, Move.makePairs, Rule.takes, Rule.reads, Rule.makes,
    Rule.guard, and_assoc]

end Rules

/-! ## Runs are derivations -/

section Runs

variable [Preorder (GroundTerm sig)] [DecidableEq O] (label : O → Item sig)

/-- **A run of completion moves**: each configuration is the previous one or the result of an
admitted move. -/
def IsRun (C : ℕ → Configuration (Item sig) O) : Prop :=
  ∀ i, C (i + 1) = C i ∨ ∃ m : Move sig O, (guarded (syntactic _) label).Admits (s := C i) m.firing ∧
    C (i + 1) = m.firing.firing.result label (C i)

/-- **Runs of admitted moves are derivations** on the items present. -/
theorem IsRun.derivation {C : ℕ → Configuration (Item sig) O} (run : IsRun label C) :
    Derivation fun i => clauses label (C i) where
  step i := by
    rcases run i with same | ⟨m, admitted, next⟩
    · exact Or.inl (by rw [same])
    · refine Or.inr ⟨m.rule, ?_⟩
      rw [next]
      exact Move.transition label admitted

end Runs

/-! ## Independence -/

/-- **Two moves are apart**: neither takes an occurrence the other uses, and they make different
occurrences. -/
def Apart (m₁ m₂ : Move sig O) : Prop :=
  (∀ p ∈ m₁.takePairs, ∀ q ∈ m₂.takePairs ++ m₂.readPairs, p.1 ≠ q.1) ∧
  (∀ p ∈ m₂.takePairs, ∀ q ∈ m₁.takePairs ++ m₁.readPairs, p.1 ≠ q.1) ∧
  (∀ p ∈ m₁.makePairs, ∀ q ∈ m₂.makePairs, p.1 ≠ q.1)

theorem Apart.symm {m₁ m₂ : Move sig O} (apart : Apart m₁ m₂) : Apart m₂ m₁ :=
  ⟨apart.2.1, apart.1, fun p inP q inQ same => apart.2.2 q inQ p inP same.symm⟩

section Independence

variable [Preorder (GroundTerm sig)] [DecidableEq O] (label : O → Item sig)

/-- After an admitted move, a move apart from it that was admitted is still admitted. -/
theorem Move.admits_after {C : Configuration (Item sig) O} {m₁ m₂ : Move sig O} (apart : Apart m₁ m₂)
    (first : (guarded (syntactic _) label).Admits (s := C) m₁.firing)
    (second : (guarded (syntactic _) label).Admits (s := C) m₂.firing) :
    (guarded (syntactic _) label).Admits (s := m₁.firing.firing.result label C) m₂.firing := by
  obtain ⟨present, apartTR, fresh, -, guard⟩ := (Move.admits_iff label C m₂).mp second
  obtain ⟨-, -, fresh₁, -, -⟩ := (Move.admits_iff label C m₁).mp first
  refine (Move.admits_iff label _ m₂).mpr ⟨fun p member => ⟨?_, (present p member).2⟩, apartTR,
    fun p member => ⟨?_, (fresh p member).2⟩, Move.plain label first, guard⟩
  · rw [Move.present_result]
    refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨(present p member).1, fun taken => ?_⟩)
    obtain ⟨q, inQ, same⟩ := List.mem_map.mp (List.mem_toFinset.mp taken)
    exact apart.1 q inQ p member same
  · rw [Move.present_result]
    intro inAfter
    rcases Finset.mem_union.mp inAfter with kept | made
    · exact (fresh p member).1 (Finset.mem_sdiff.mp kept).1
    · obtain ⟨q, inQ, same⟩ := List.mem_map.mp (List.mem_toFinset.mp made)
      exact apart.2.2 q inQ p member same

/-- **Moves apart are independent**: each is admitted after the other. -/
theorem Move.independent {C : Configuration (Item sig) O} {m₁ m₂ : Move sig O} (apart : Apart m₁ m₂)
    (first : (guarded (syntactic _) label).Admits (s := C) m₁.firing)
    (second : (guarded (syntactic _) label).Admits (s := C) m₂.firing) :
    (guardedTransport (syntactic _) label).Independent C m₁.firing m₂.firing :=
  (guarded_independent_iff (syntactic _) label).mpr
    ⟨first, second, Move.admits_after label apart first second,
      Move.admits_after label apart.symm second first⟩

/-- **The two orders of moves apart are trace-equivalent runs.** -/
theorem Move.traceEquiv {C : Configuration (Item sig) O} {m₁ m₂ : Move sig O} (apart : Apart m₁ m₂)
    (first : (guarded (syntactic _) label).Admits (s := C) m₁.firing)
    (second : (guarded (syntactic _) label).Admits (s := C) m₂.firing) :
    ∃ r r' : (guarded (syntactic _) label).Run C,
      r.word.map Sigma.snd = [m₁.firing, m₂.firing] ∧ r'.word.map Sigma.snd = [m₂.firing, m₁.firing] ∧
      (guardedTransport (syntactic _) label).TraceEquiv C r r' := by
  obtain ⟨one, two, afterOne, afterTwo, close, swap⟩ := (Move.independent label apart first second).swap
  exact ⟨_, _, rfl, rfl, EqvGen.rel _ _ (Or.inl (swap (.nil _)))⟩

/-- **A move that takes a premise of another makes the two dependent**: after it, the other is
refused. -/
theorem Move.takes_premise_dependent {C : Configuration (Item sig) O} {m₁ m₂ : Move sig O}
    (takes : m₁.rule.takes ≠ []) (premise : m₁.taken ∈ (m₂.takePairs ++ m₂.readPairs).map Prod.fst)
    (first : (guarded (syntactic _) label).Admits (s := C) m₁.firing) :
    ¬ (guarded (syntactic _) label).Admits (s := m₁.firing.firing.result label C) m₂.firing ∧
      ¬ (guardedTransport (syntactic _) label).Independent C m₁.firing m₂.firing := by
  have refused : ¬ (guarded (syntactic _) label).Admits (s := m₁.firing.firing.result label C) m₂.firing := by
    intro admitted
    obtain ⟨present, -⟩ := (Move.admits_iff label _ m₂).mp admitted
    obtain ⟨q, inQ, same⟩ := List.mem_map.mp premise
    have stillThere := (present q inQ).1
    rw [Move.present_result] at stillThere
    obtain ⟨x, one⟩ : ∃ x, m₁.rule.takes = [x] := by
      rcases m₁.rule.takes_cases with none | one
      · exact absurd none takes
      · exact one
    obtain ⟨-, -, fresh, -, -⟩ := (Move.admits_iff label C m₁).mp first
    obtain ⟨present₁, -⟩ := (Move.admits_iff label C m₁).mp first
    have pair : (m₁.taken, x) ∈ m₁.takePairs := Move.mem_takePairs.mpr ⟨rfl, by rw [one]; exact List.mem_singleton_self x⟩
    rcases Finset.mem_union.mp stillThere with kept | made
    · exact (Finset.mem_sdiff.mp kept).2 (List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, pair, same.symm⟩))
    · obtain ⟨p, inP, same'⟩ := List.mem_map.mp (List.mem_toFinset.mp made)
      exact (fresh p inP).1 (by rw [same', same]; exact (present₁ _ (List.mem_append_left _ pair)).1)
  exact ⟨refused, fun independent =>
    refused ((guarded_independent_iff (syntactic _) label).mp independent).2.2.1⟩

/-- **A Collapse that takes a rule a Deduce reads makes the two dependent.** -/
theorem collapse_deduce_dependent {C : Configuration (Item sig) O} {o oRule made o₂ made' : O}
    {s t l r l₂ r₂ : GroundTerm sig} {c d : Ctx sig}
    (first : (guarded (syntactic _) label).Admits (s := C) (collapseMove o oRule made s t l r c).firing) :
    ¬ (guardedTransport (syntactic _) label).Independent C (collapseMove o oRule made s t l r c).firing
      (deduceMove o o₂ made' s t l₂ r₂ d).firing :=
  (Move.takes_premise_dependent label (by simp [collapseMove, Rule.takes])
    (by simp [deduceMove, Move.takePairs, Move.readPairs, collapseMove, Rule.takes, Rule.reads]) first).2

end Independence

#print axioms Move.admits_iff
#print axioms Move.transition
#print axioms Move.theory_iff
#print axioms Move.decreasing
#print axioms Move.takes_redundant
#print axioms deduce_admits_iff
#print axioms orient_admits_iff
#print axioms delete_admits_iff
#print axioms simplify_admits_iff
#print axioms compose_admits_iff
#print axioms collapse_admits_iff
#print axioms IsRun.derivation
#print axioms Move.admits_after
#print axioms Move.independent
#print axioms Move.traceEquiv
#print axioms Move.takes_premise_dependent
#print axioms collapse_deduce_dependent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Completion
