import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.BudgetedConversion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SearchOutcome

/-!
# Budgets as outcomes: the laws of a budgeted decision procedure

A question that a computation answers only within a budget gets three outcomes at every budget `k`:
**yes**, **no**, and **checked up to `k`** (the budget ran out). The outcomes are the three verdicts of the
budgeted conversion check (`NativeTypesOnTheStep.Computing.Budgeted.Verdict`: `equal`, `different`,
`undecided`), read here as yes, no and exhausted.

**A budgeted decision procedure** (`Procedure`) carries three laws as fields:
1. yes and no are sound at every budget (`equal_sound`, `different_sound`);
2. raising the budget only resolves: a decided verdict is the verdict of every larger budget (`resolves`); a
   yes and a no never meet, at any two budgets (`never_flips`);
3. exhausted is exactly the record that the computation ran out within its budget (`undecided_iff`, with the
   procedure's own `ranOut`), so it says nothing about the instance.

Law 4, "every instance that has an answer is answered at some budget", is not a field: it holds on a class,
stated with its hypothesis (`AnsweredOn`), and there exact from some budget on (`answered_exact`).

**Exhausted is never read as no or as empty.** Its existence readout is `suspended`, its answers are `unknown`, the
bottom of the information order, never `refuted` (`undecided_reads`); only a no reads refuted (`readout_refuted`).
That it is never read as missing by the step is `Budgets.OnTheStep`. The answers of a procedure grow in the information order as the budget grows
(`answers_mono`). Reading exhausted as a no, or as a yes, breaks that order on every instance that is later
answered the other way (`no_reading_breaks`, `yes_reading_breaks`).

**From partial deciders, by taking the first answer** (`Decider`, `Decider.procedure`). A family of deciders
indexed by a budget, each answering soundly or not at all, becomes a procedure: at budget `k` the verdict is the
first answer found at a budget up to `k` (`firstUpTo`). The laws hold by construction, and law 4 holds exactly on
the instances some budget answers (`Decider.answered_iff`). An instance without any possible answer is
exhausted at every budget (`Decider.undecided_of_empty`). **On the answered instances the budget can be dropped**:
the search for the least budget that answers (`Decider.search`, by `Nat.find`) takes no budget, agrees with every
budget at which the procedure is decided (`Decider.verdict_eq_search`), and every smaller budget is exhausted
(`Decider.verdict_below_least`). Off them, no budget answers, and exhausted is the only honest outcome.

**The conversion check is an instance** (`conversion`): law 3 is `check_undecided_iff`; law 4 holds on pairs
whose two terms both reach an answer of the normalizer (`conversion_answered`, from `check_eventually`).
**Without that hypothesis law 4 is false**, for every normalizer: `Ω = (λ x. x x) (λ x. x x)` is convertible with
itself, its only reduct is itself, so no normalizer answers it, and the pair is exhausted at every budget
(`omega_undecided`). With the declared addition's normalizer, a normal pair outside its first-order fragment is
exhausted at every budget too (`lam_undecided`, `conversion_not_answered_everywhere`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre.Budgets

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ConversionCoherence (ChurchRosser StepStar)
open NativeTypesOnTheStep.Computing

/-! ## The procedure and its laws -/

section Procedure

variable {Q : Type} (P : Q → Prop)

/-- **A budgeted decision procedure** for a question `P`: at every budget, yes (`equal`), no (`different`), or
exhausted (`undecided`), with laws 1 to 3. -/
structure Procedure where
  /-- The verdict at a budget. -/
  verdict : Nat → Q → Budgeted.Verdict
  /-- The procedure's own record that its computation ran out within a budget. -/
  ranOut : Nat → Q → Prop
  /-- Law 1: a yes is sound. -/
  equal_sound : ∀ {k : Nat} {q : Q}, verdict k q = .equal → P q
  /-- Law 1: a no is sound. -/
  different_sound : ∀ {k : Nat} {q : Q}, verdict k q = .different → ¬ P q
  /-- Law 2: raising the budget only resolves. -/
  resolves : ∀ {k k' : Nat} {q : Q}, k ≤ k' → verdict k q ≠ .undecided → verdict k' q = verdict k q
  /-- Law 3: exhausted is exactly the record that the computation ran out. -/
  undecided_iff : ∀ {k : Nat} {q : Q}, verdict k q = .undecided ↔ ranOut k q

variable {P}

/-- **Law 4 on a class**: every instance of the class is answered at some budget. -/
def Procedure.AnsweredOn (D : Procedure P) (C : Q → Prop) : Prop :=
  ∀ q, C q → ∃ k, D.verdict k q ≠ .undecided

namespace Procedure

variable (D : Procedure P)

/-- **Never flips**: a yes at one budget and a no at another never meet. -/
theorem never_flips {k k' : Nat} {q : Q} (yes : D.verdict k q = .equal) : D.verdict k' q ≠ .different :=
  fun no => D.different_sound no (D.equal_sound yes)

/-- **A decided verdict is exact.** -/
theorem exact_of_decided {k : Nat} {q : Q} (decided : D.verdict k q ≠ .undecided) :
    D.verdict k q = .equal ↔ P q := by
  constructor
  · exact D.equal_sound
  · intro holds
    cases h : D.verdict k q with
    | equal => rfl
    | different => exact absurd holds (D.different_sound h)
    | undecided => exact absurd h decided

/-- Once decided, decided at every larger budget. -/
theorem decided_mono {k k' : Nat} {q : Q} (le : k ≤ k') (decided : D.verdict k q ≠ .undecided) :
    D.verdict k' q ≠ .undecided := by
  rw [D.resolves le decided]
  exact decided

/-- Exhausted at a budget, exhausted at every smaller one. -/
theorem undecided_anti {k k' : Nat} {q : Q} (le : k ≤ k') (undecided : D.verdict k' q = .undecided) :
    D.verdict k q = .undecided := by
  by_contra decided
  exact D.decided_mono le decided undecided

/-- **Law 4 gives exact answers**: on the class, from some budget on, the verdict is decided and decides `P`. -/
theorem answered_exact {C : Q → Prop} (answered : D.AnsweredOn C) {q : Q} (inside : C q) :
    ∃ k, ∀ k', k ≤ k' → D.verdict k' q ≠ .undecided ∧ (D.verdict k' q = .equal ↔ P q) := by
  obtain ⟨k, decided⟩ := answered q inside
  exact ⟨k, fun k' le => ⟨D.decided_mono le decided, D.exact_of_decided (D.decided_mono le decided)⟩⟩

end Procedure

end Procedure

/-! ## Readouts: exhausted is never no, empty or missing -/

/-- **The existence readout** of a verdict. -/
def readout : Budgeted.Verdict → Search.Outcome.Verdict
  | .equal => .commit
  | .different => .refuted
  | .undecided => .suspended

/-- **The answers of a verdict**, as a search outcome: one answer, finished; none, finished; none, cut off. -/
def answers : Budgeted.Verdict → Search.Outcome Unit
  | .equal => Search.Outcome.pure ()
  | .different => Search.Outcome.refuted
  | .undecided => Search.Outcome.unknown

/-- The existence readout is the readout of the answers. -/
theorem answers_verdict (v : Budgeted.Verdict) : (answers v).verdict = readout v := by
  cases v with
  | equal => exact (Search.Outcome.verdict_eq_commit_iff _).mpr (Multiset.singleton_ne_zero ())
  | different => exact (Search.Outcome.verdict_eq_refuted_iff _).mpr rfl
  | undecided => exact (Search.Outcome.verdict_eq_suspended_iff _).mpr rfl

theorem answers_equal_ne_refuted : answers .equal ≠ Search.Outcome.refuted := by
  intro same
  have count := congrArg (fun o : Search.Outcome Unit => Multiset.card o.answers) same
  simp [answers, Search.Outcome.refuted] at count

namespace Procedure

variable {Q : Type} {P : Q → Prop} (D : Procedure P)

/-- **Law 3, read out**: an exhausted verdict reads `suspended`, its answers are `unknown` (cut off, the bottom of
the information order), and never `refuted`. -/
theorem undecided_reads {k : Nat} {q : Q} (undecided : D.verdict k q = .undecided) :
    readout (D.verdict k q) = .suspended ∧ answers (D.verdict k q) = Search.Outcome.unknown ∧
      answers (D.verdict k q) ≠ Search.Outcome.refuted := by
  rw [undecided]
  exact ⟨rfl, rfl, Search.Outcome.unknown_ne_refuted⟩

/-- **Only a no reads refuted.** -/
theorem readout_refuted {k : Nat} {q : Q} (refuted : readout (D.verdict k q) = .refuted) : ¬ P q := by
  cases h : D.verdict k q with
  | equal => rw [h] at refuted; exact absurd refuted (by decide)
  | different => exact D.different_sound h
  | undecided => rw [h] at refuted; exact absurd refuted (by decide)

/-- **Only a yes reads commit.** -/
theorem readout_commit {k : Nat} {q : Q} (commit : readout (D.verdict k q) = .commit) : P q := by
  cases h : D.verdict k q with
  | equal => exact D.equal_sound h
  | different => rw [h] at commit; exact absurd commit (by decide)
  | undecided => rw [h] at commit; exact absurd commit (by decide)

/-- **The answers grow in the information order** as the budget grows. -/
theorem answers_mono {k k' : Nat} {q : Q} (le : k ≤ k') : answers (D.verdict k q) ≤ answers (D.verdict k' q) := by
  by_cases decided : D.verdict k q = .undecided
  · rw [decided]
    exact bot_le
  · simp only [D.resolves le decided, le_refl]

/-- **Reading exhausted as a no breaks the information order** on an instance answered yes later: the refuted
outcome lies below no commit. -/
theorem no_reading_breaks {k' : Nat} {q : Q} (yes : D.verdict k' q = .equal) :
    ¬ (Search.Outcome.refuted : Search.Outcome Unit) ≤ answers (D.verdict k' q) := by
  rw [yes, Search.Outcome.refuted_le_iff]
  exact answers_equal_ne_refuted

/-- **Reading exhausted as a yes breaks it too**, on an instance answered no later. -/
theorem yes_reading_breaks {k' : Nat} {q : Q} (no : D.verdict k' q = .different) :
    ¬ (Search.Outcome.pure () : Search.Outcome Unit) ≤ answers (D.verdict k' q) := by
  rw [no]
  intro below
  exact answers_equal_ne_refuted (Search.Outcome.eq_of_finished_le rfl below).symm

end Procedure

/-! ## From partial deciders: the first answer up to the budget -/

section Cumulative

variable {Q : Type} {A : Q → Type}

/-- **The first answer found at a budget up to `k`.** -/
def firstUpTo (attempt : Nat → (q : Q) → Option (A q)) (q : Q) : Nat → Option (A q)
  | 0 => attempt 0 q
  | k + 1 =>
      match firstUpTo attempt q k with
      | some a => some a
      | none => attempt (k + 1) q

variable (attempt : Nat → (q : Q) → Option (A q)) (q : Q)

theorem firstUpTo_succ_of_some {k : Nat} {a : A q} (found : firstUpTo attempt q k = some a) :
    firstUpTo attempt q (k + 1) = some a := by
  simp only [firstUpTo, found]

theorem firstUpTo_succ_of_none {k : Nat} (missing : firstUpTo attempt q k = none) :
    firstUpTo attempt q (k + 1) = attempt (k + 1) q := by
  simp only [firstUpTo, missing]

/-- **A first answer stays the first answer** at every larger budget. -/
theorem firstUpTo_mono {k : Nat} {a : A q} (found : firstUpTo attempt q k = some a) {k' : Nat} (le : k ≤ k') :
    firstUpTo attempt q k' = some a := by
  induction le with
  | refl => exact found
  | step _ ih => exact firstUpTo_succ_of_some attempt q ih

/-- **No first answer up to `k`** exactly when no budget up to `k` answers. -/
theorem firstUpTo_eq_none_iff (k : Nat) :
    firstUpTo attempt q k = none ↔ ∀ j, j ≤ k → attempt j q = none := by
  induction k with
  | zero =>
      constructor
      · intro missing j le
        rw [Nat.le_zero.mp le]
        exact missing
      · intro missing
        exact missing 0 le_rfl
  | succ k ih =>
      cases first : firstUpTo attempt q k with
      | some a =>
          rw [firstUpTo_succ_of_some attempt q first]
          constructor
          · intro h
            cases h
          · intro missing
            have none' : firstUpTo attempt q k = none := ih.mpr fun j le => missing j (by omega)
            rw [first] at none'
            cases none'
      | none =>
          rw [firstUpTo_succ_of_none attempt q first]
          constructor
          · intro last j le
            by_cases eq : j = k + 1
            · rw [eq]
              exact last
            · exact ih.mp first j (by omega)
          · intro missing
            exact missing (k + 1) le_rfl

/-- A first answer is an answer of some budget up to `k`. -/
theorem firstUpTo_spec (k : Nat) {a : A q} (found : firstUpTo attempt q k = some a) :
    ∃ j, j ≤ k ∧ attempt j q = some a := by
  induction k generalizing a with
  | zero => exact ⟨0, le_rfl, found⟩
  | succ k ih =>
      cases first : firstUpTo attempt q k with
      | some b =>
          rw [firstUpTo_succ_of_some attempt q first] at found
          obtain ⟨j, le, h⟩ := ih first
          exact ⟨j, by omega, by rw [h, found]⟩
      | none =>
          rw [firstUpTo_succ_of_none attempt q first] at found
          exact ⟨k + 1, le_rfl, found⟩

end Cumulative

section Decider

variable {Q : Type} (P : Q → Prop)

/-- **A budget-indexed decider**: at each budget an answer or nothing; each answer is a yes or a no, soundly. -/
structure Decider where
  /-- What an answer carries (a certificate). -/
  Answer : Q → Type
  /-- The attempt at one budget. -/
  attempt : Nat → (q : Q) → Option (Answer q)
  /-- Whether an answer says yes. -/
  sign : {q : Q} → Answer q → Bool
  yes : ∀ {q : Q} (a : Answer q), sign a = true → P q
  no : ∀ {q : Q} (a : Answer q), sign a = false → ¬ P q

namespace Decider

variable {P} (D : Decider P)

/-- The verdict of an answer, or of none. -/
def verdictOf {q : Q} : Option (D.Answer q) → Budgeted.Verdict
  | none => .undecided
  | some a => if D.sign a then .equal else .different

/-- **The verdict at budget `k`**: the first answer found at a budget up to `k`. -/
def verdict (k : Nat) (q : Q) : Budgeted.Verdict :=
  D.verdictOf (firstUpTo D.attempt q k)

theorem verdictOf_some_ne {q : Q} (a : D.Answer q) : D.verdictOf (some a) ≠ .undecided := by
  cases s : D.sign a <;> simp [verdictOf, s]

theorem verdict_equal {k : Nat} {q : Q} (h : D.verdict k q = .equal) : P q := by
  unfold verdict at h
  cases found : firstUpTo D.attempt q k with
  | none =>
      rw [found] at h
      simp [verdictOf] at h
  | some a =>
      rw [found] at h
      cases s : D.sign a with
      | true => exact D.yes a s
      | false => simp [verdictOf, s] at h

theorem verdict_different {k : Nat} {q : Q} (h : D.verdict k q = .different) : ¬ P q := by
  unfold verdict at h
  cases found : firstUpTo D.attempt q k with
  | none =>
      rw [found] at h
      simp [verdictOf] at h
  | some a =>
      rw [found] at h
      cases s : D.sign a with
      | true => simp [verdictOf, s] at h
      | false => exact D.no a s

theorem verdict_undecided_iff {k : Nat} {q : Q} :
    D.verdict k q = .undecided ↔ ∀ j, j ≤ k → D.attempt j q = none := by
  refine Iff.trans ?_ (firstUpTo_eq_none_iff D.attempt q k)
  unfold verdict
  cases found : firstUpTo D.attempt q k with
  | none => simp [verdictOf]
  | some a =>
      constructor
      · intro h
        exact absurd h (D.verdictOf_some_ne a)
      · intro h
        cases h

theorem verdict_resolves {k k' : Nat} {q : Q} (le : k ≤ k') (decided : D.verdict k q ≠ .undecided) :
    D.verdict k' q = D.verdict k q := by
  unfold verdict at decided ⊢
  cases found : firstUpTo D.attempt q k with
  | none =>
      rw [found] at decided
      exact absurd rfl decided
  | some a => rw [firstUpTo_mono D.attempt q found le]

/-- **The procedure of a decider**: the first answer up to the budget. -/
def procedure : Procedure P where
  verdict := D.verdict
  ranOut k q := ∀ j, j ≤ k → D.attempt j q = none
  equal_sound := D.verdict_equal
  different_sound := D.verdict_different
  resolves := D.verdict_resolves
  undecided_iff := D.verdict_undecided_iff

/-- **Law 4, exactly**: an instance is answered at some budget exactly when some budget's attempt answers it. -/
theorem answered_iff {q : Q} :
    (∃ k, D.procedure.verdict k q ≠ .undecided) ↔ ∃ k a, D.attempt k q = some a := by
  constructor
  · rintro ⟨k, decided⟩
    by_contra none'
    apply decided
    refine D.verdict_undecided_iff.mpr fun j _ => ?_
    cases h : D.attempt j q with
    | none => rfl
    | some a => exact absurd ⟨j, a, h⟩ none'
  · rintro ⟨k, a, found⟩
    refine ⟨k, fun undecided => ?_⟩
    have missing := (D.verdict_undecided_iff.mp undecided) k le_rfl
    rw [missing] at found
    cases found

/-- **Law 4 on the class of answered instances.** -/
theorem answeredOn : D.procedure.AnsweredOn fun q => ∃ k a, D.attempt k q = some a :=
  fun _ answered => D.answered_iff.mpr answered

/-- **Exhausted at `k`** when no attempt up to `k` answers. -/
theorem undecided_of_none {k : Nat} {q : Q} (before : ∀ j, j ≤ k → D.attempt j q = none) :
    D.procedure.verdict k q = .undecided :=
  D.verdict_undecided_iff.mpr before

/-- **An instance with no possible answer is exhausted at every budget.** -/
theorem undecided_of_empty {q : Q} (empty : D.Answer q → False) (k : Nat) :
    D.procedure.verdict k q = .undecided :=
  D.verdict_undecided_iff.mpr fun j _ => by
    cases h : D.attempt j q with
    | none => rfl
    | some a => exact (empty a).elim

/-- **Exhausted at `k`, answered at `k + 1`**: no attempt up to `k` answers and the next one does. -/
theorem verdict_first {k : Nat} {q : Q} (before : ∀ j, j ≤ k → D.attempt j q = none) {a : D.Answer q}
    (found : D.attempt (k + 1) q = some a) :
    D.procedure.verdict k q = .undecided ∧ D.procedure.verdict (k + 1) q = D.verdictOf (some a) := by
  refine ⟨D.verdict_undecided_iff.mpr before, ?_⟩
  show D.verdictOf (firstUpTo D.attempt q (k + 1)) = _
  rw [firstUpTo_succ_of_none D.attempt q ((firstUpTo_eq_none_iff D.attempt q k).mpr before), found]

/-! ### The limit of the procedure: a search with no budget, on the answered instances -/

theorem answered_isSome {q : Q} (answered : ∃ k a, D.attempt k q = some a) :
    ∃ k, (D.attempt k q).isSome = true := by
  obtain ⟨k, a, found⟩ := answered
  exact ⟨k, by rw [found]; rfl⟩

/-- **The least budget that answers.** -/
def leastAnswering {q : Q} (answered : ∃ k a, D.attempt k q = some a) : Nat :=
  Nat.find (D.answered_isSome answered)

/-- **The search with no budget**: the answer of the least budget that answers. -/
def search {q : Q} (answered : ∃ k a, D.attempt k q = some a) : D.Answer q :=
  (D.attempt (D.leastAnswering answered) q).get (Nat.find_spec (D.answered_isSome answered))

theorem attempt_least {q : Q} (answered : ∃ k a, D.attempt k q = some a) :
    D.attempt (D.leastAnswering answered) q = some (D.search answered) :=
  (Option.some_get _).symm

theorem none_below {q : Q} (answered : ∃ k a, D.attempt k q = some a) {j : Nat}
    (below : j < D.leastAnswering answered) : D.attempt j q = none := by
  have unanswered := Nat.find_min (D.answered_isSome answered) below
  cases h : D.attempt j q with
  | none => rfl
  | some a => exact (unanswered (by rw [h]; rfl)).elim

theorem firstUpTo_least {q : Q} (answered : ∃ k a, D.attempt k q = some a) :
    firstUpTo D.attempt q (D.leastAnswering answered) = some (D.search answered) := by
  have least := D.attempt_least answered
  cases hm : D.leastAnswering answered with
  | zero =>
      rw [hm] at least
      exact least
  | succ m =>
      have before : firstUpTo D.attempt q m = none :=
        (firstUpTo_eq_none_iff D.attempt q m).mpr fun j le => D.none_below answered (by omega)
      rw [firstUpTo_succ_of_none D.attempt q before]
      rw [hm] at least
      exact least

/-- **The search agrees with every budget that answers**: wherever the procedure is decided, its verdict is the
search's. -/
theorem verdict_eq_search {q : Q} (answered : ∃ k a, D.attempt k q = some a) {k : Nat}
    (decided : D.procedure.verdict k q ≠ .undecided) :
    D.procedure.verdict k q = D.verdictOf (some (D.search answered)) := by
  have le : D.leastAnswering answered ≤ k := by
    by_contra lt
    apply decided
    exact D.verdict_undecided_iff.mpr fun j le => D.none_below answered (by omega)
  show D.verdictOf (firstUpTo D.attempt q k) = _
  rw [firstUpTo_mono D.attempt q (D.firstUpTo_least answered) le]

/-- **Exhausted below the least budget that answers.** -/
theorem verdict_below_least {q : Q} (answered : ∃ k a, D.attempt k q = some a) {k : Nat}
    (below : k < D.leastAnswering answered) : D.procedure.verdict k q = .undecided :=
  D.undecided_of_none fun j le => D.none_below answered (by omega)

/-- **A decider that only says yes never says no.** -/
theorem verdict_ne_different {q : Q} (always : ∀ a : D.Answer q, D.sign a = true) (k : Nat) :
    D.procedure.verdict k q ≠ .different := by
  show D.verdictOf (firstUpTo D.attempt q k) ≠ .different
  cases firstUpTo D.attempt q k with
  | none => simp [verdictOf]
  | some a => simp [verdictOf, always a]

end Decider

end Decider

/-! ## The conversion check is an instance -/

section Conversion

variable {Head : Type} [DecidableEq Head] {R : Rules Head}

/-- **The budgeted conversion check as a budgeted decision procedure**, on a Church–Rosser package. -/
def conversion (N : Budgeted.Normalizer R) (church : ChurchRosser R) (n : Nat) :
    Procedure (fun pair : Tm Head n × Tm Head n => Conv R.headEq pair.1 pair.2 R.computation) where
  verdict k pair := Budgeted.check N k pair.1 pair.2
  ranOut k pair := N.run k pair.1 = none ∨ N.run k pair.2 = none
  equal_sound h := Budgeted.check_equal N h
  different_sound h := Budgeted.check_different N church h
  resolves le h := Budgeted.check_mono N le h
  undecided_iff := Budgeted.check_undecided_iff N

/-- The pairs on which the check answers: both terms reach an answer of the normalizer at some budget. -/
def Normalizes (N : Budgeted.Normalizer R) {n : Nat} (pair : Tm Head n × Tm Head n) : Prop :=
  (∃ k a, N.run k pair.1 = some a) ∧ ∃ k b, N.run k pair.2 = some b

/-- **Law 4 for the conversion check**, on the pairs both of whose terms the normalizer answers. -/
theorem conversion_answered (N : Budgeted.Normalizer R) (church : ChurchRosser R) (n : Nat) :
    (conversion N church n).AnsweredOn (Normalizes N) := by
  rintro pair ⟨⟨k₁, a, ha⟩, ⟨k₂, b, hb⟩⟩
  obtain ⟨k, decided, _⟩ := Budgeted.check_eventually N church ha hb
  exact ⟨k, decided⟩

end Conversion

/-! ## Law 4 without its hypothesis is false -/

section Controls

open NativeTypesOnTheStep.VectorAppend (vrules)
open NativeTypesOnTheStep.DeclaredConfluence (add_churchRosser)

/-- **A normal pair the declared addition's normalizer never answers**: `λ x. x` is outside its first-order
fragment, so the pair is exhausted at every budget, though convertible. -/
theorem lam_undecided (k : Nat) :
    (conversion Budgeted.addNormalizer add_churchRosser 0).verdict k
        ((.lam (.var 0) : Tower.Tm 0), (.lam (.var 0) : Tower.Tm 0)) = .undecided ∧
      Conv vrules.headEq (.lam (.var 0) : Tower.Tm 0) (.lam (.var 0)) vrules.computation := by
  refine ⟨?_, Relation.EqvGen.refl _⟩
  show Budgeted.check Budgeted.addNormalizer k (.lam (.var 0) : Tower.Tm 0) (.lam (.var 0)) = .undecided
  exact (Budgeted.check_undecided_iff Budgeted.addNormalizer).mpr (Or.inl rfl)

/-- **So the check of the declared addition is not answered on every pair.** -/
theorem conversion_not_answered_everywhere :
    ¬ ∀ pair : Tower.Tm 0 × Tower.Tm 0,
      ∃ k, (conversion Budgeted.addNormalizer add_churchRosser 0).verdict k pair ≠ .undecided := by
  intro answered
  obtain ⟨k, decided⟩ := answered ((.lam (.var 0) : Tower.Tm 0), (.lam (.var 0) : Tower.Tm 0))
  exact decided (lam_undecided k).1

/-- `ω = λ x. x x`. -/
abbrev selfApply : Tower.Tm 0 := .lam (.app (.var 0) (.var 0))

/-- No step leaves a variable. -/
theorem var_stuck {t : Tower.Tm 1} : ¬ StepCore vrules.computation vrules.headEq (.var 0 : Tower.Tm 1) t := by
  intro step
  cases step with
  | root h => rcases h with h | h <;> cases h

/-- No step leaves `x x`. -/
theorem selfApp_stuck {t : Tower.Tm 1} :
    ¬ StepCore vrules.computation vrules.headEq (.app (.var 0) (.var 0) : Tower.Tm 1) t := by
  intro step
  cases step with
  | root h => rcases h with h | h <;> cases h
  | congAppFun inner => exact var_stuck inner
  | congAppArg inner => exact var_stuck inner

/-- No step leaves `ω`. -/
theorem selfApply_stuck {t : Tower.Tm 0} :
    ¬ StepCore vrules.computation vrules.headEq (.lam (.app (.var 0) (.var 0)) : Tower.Tm 0) t := by
  intro step
  cases step with
  | root h => rcases h with h | h <;> cases h
  | congLam inner => exact selfApp_stuck inner

/-- **The only step from `Ω = ω ω` is to `Ω`.** -/
theorem omega_step {t : Tower.Tm 0}
    (step : StepCore vrules.computation vrules.headEq
      (.app (.lam (.app (.var 0) (.var 0))) (.lam (.app (.var 0) (.var 0))) : Tower.Tm 0) t) :
    t = .app (.lam (.app (.var 0) (.var 0))) (.lam (.app (.var 0) (.var 0))) := by
  cases step with
  | betaPi body a => rfl
  | root h => rcases h with h | h <;> cases h
  | congAppFun inner => exact absurd inner selfApply_stuck
  | congAppArg inner => exact absurd inner selfApply_stuck

/-- Every computation from `Ω` stays at `Ω`. -/
theorem omega_reaches {t : Tower.Tm 0} (steps : StepStar vrules (.app selfApply selfApply) t) :
    t = .app selfApply selfApply := by
  induction steps with
  | refl => rfl
  | tail _ step ih =>
      subst ih
      exact omega_step step

/-- `Ω` is not normal: it steps to itself. -/
theorem omega_not_normal : ¬ ConstructorSystem.Normal vrules (.app selfApply selfApply : Tower.Tm 0) :=
  fun normal => normal (StepCore.betaPi (.app (.var 0) (.var 0)) selfApply)

/-- **No normalizer ever answers `Ω`**: an answer would be a normal form reached from it. -/
theorem omega_unanswered (N : Budgeted.Normalizer vrules) (k : Nat) : N.run k (.app selfApply selfApply) = none := by
  cases h : N.run k (.app selfApply selfApply) with
  | none => rfl
  | some v =>
      obtain ⟨steps, normal⟩ := N.sound h
      have same := omega_reaches steps
      subst same
      exact (omega_not_normal @normal).elim

/-- **Law 4 is false without its hypothesis, for every normalizer**: `Ω` is convertible with itself, and the pair
is exhausted at every budget. -/
theorem omega_undecided (N : Budgeted.Normalizer vrules) (k : Nat) :
    Conv vrules.headEq (.app selfApply selfApply : Tower.Tm 0) (.app selfApply selfApply) vrules.computation ∧
      (conversion N add_churchRosser 0).verdict k (.app selfApply selfApply, .app selfApply selfApply) =
        .undecided :=
  ⟨Relation.EqvGen.refl _, (Budgeted.check_undecided_iff N).mpr (Or.inl (omega_unanswered N k))⟩

/-- The statement is not vacuous: the declared addition's normalizer is one. -/
theorem omega_undecided_addition (k : Nat) :
    (conversion Budgeted.addNormalizer add_churchRosser 0).verdict k
      (.app selfApply selfApply, .app selfApply selfApply) = .undecided :=
  (omega_undecided Budgeted.addNormalizer k).2

end Controls

end TreeFibre.Budgets

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

section Audit
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Budgets
#print axioms Procedure.never_flips
#print axioms Procedure.exact_of_decided
#print axioms Procedure.answered_exact
#print axioms Procedure.undecided_reads
#print axioms Procedure.readout_refuted
#print axioms Procedure.answers_mono
#print axioms Procedure.no_reading_breaks
#print axioms Procedure.yes_reading_breaks
#print axioms firstUpTo_eq_none_iff
#print axioms Decider.procedure
#print axioms Decider.answered_iff
#print axioms Decider.undecided_of_empty
#print axioms Decider.verdict_first
#print axioms Decider.search
#print axioms Decider.verdict_eq_search
#print axioms Decider.verdict_below_least
#print axioms conversion
#print axioms conversion_answered
#print axioms lam_undecided
#print axioms conversion_not_answered_everywhere
#print axioms omega_unanswered
#print axioms omega_undecided
#print axioms omega_undecided_addition
end Audit
