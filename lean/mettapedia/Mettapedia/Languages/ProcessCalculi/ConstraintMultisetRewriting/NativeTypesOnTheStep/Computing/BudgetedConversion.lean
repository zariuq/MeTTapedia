import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.HostTables

/-!
# Conversion with a budget: equal, different, or not decided within budget `k`

Without a termination proof, a conversion check may still run, with a budget. It has three outcomes
(`Verdict`): **equal**, **different**, and **not decided within budget `k`**. Running out of budget is
its own outcome, never "different".

A `Normalizer` runs a package's computation with fuel: what it returns within budget `k` is a normal
form reached by computation, and more fuel never changes a returned answer.

* **Sound in all three outcomes**: "equal" means convertible (`check_equal`); on a Church–Rosser package
  "different" means not convertible (`check_different`); "not decided" holds exactly when the budget ran
  out on one side (`check_undecided_iff`), so it asserts nothing about the terms.
* **Monotone in the budget**: a decided verdict stays the same under every larger budget
  (`check_mono`).
* **Complete in the limit** on terms the normalizer finishes: some budget decides them (`check_eventually`).

**Instance.** For the step's declared addition on first-order terms (`addNormalizer`): `add 2 1` and
`3` are equal at budget 5 (`check_two_one`); `add 1 0` and `2` are different (`check_one_zero`); at
budget 0 the first pair is not decided (`check_budget_zero`), and every larger budget decides it the same
way. Terms outside the first-order fragment are not decided by this normalizer at any budget, which is
again the third outcome, not a refusal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Budgeted

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ConversionCoherence (ChurchRosser StepStar)

/-! ## The checker -/

section Generic

variable {Head : Type} [DecidableEq Head]

/-- **A fuelled normalizer**: an answer within budget `k` is a normal form reached by computation, and
more fuel keeps it. -/
structure Normalizer (R : Rules Head) where
  run : Nat → ∀ {n : Nat}, Tm Head n → Option (Tm Head n)
  sound : ∀ {k n : Nat} {t v : Tm Head n}, run k t = some v →
    StepStar R t v ∧ ConstructorSystem.Normal R v
  mono : ∀ {k n : Nat} {t v : Tm Head n}, run k t = some v → run (k + 1) t = some v

/-- The three outcomes of a budgeted check. -/
inductive Verdict where
  | equal
  | different
  | undecided
  deriving DecidableEq, Repr

variable {R : Rules Head}

/-- **The budgeted conversion check.** -/
def check (N : Normalizer R) (k : Nat) {n : Nat} (t u : Tm Head n) : Verdict :=
  match N.run k t with
  | none => .undecided
  | some a =>
      match N.run k u with
      | none => .undecided
      | some b => if a = b then .equal else .different

theorem check_some (N : Normalizer R) {k n : Nat} {t u a b : Tm Head n} (ht : N.run k t = some a)
    (hu : N.run k u = some b) : check N k t u = if a = b then .equal else .different := by
  unfold check
  simp only [ht, hu]

/-- **"Equal" is sound**: the two terms are convertible. -/
theorem check_equal (N : Normalizer R) {k n : Nat} {t u : Tm Head n} (verdict : check N k t u = .equal) :
    Conv R.headEq t u R.computation := by
  cases ht : N.run k t with
  | none => simp [check, ht] at verdict
  | some a =>
      cases hu : N.run k u with
      | none => simp [check, ht, hu] at verdict
      | some b =>
          rw [check_some N ht hu] at verdict
          by_cases same : a = b
          · subst same
            exact .trans _ _ _ (conv_of_stepStar (N.sound ht).1) (.symm _ _ (conv_of_stepStar (N.sound hu).1))
          · simp [same] at verdict

/-- **"Different" is sound on a Church–Rosser package**: the two terms are not convertible. -/
theorem check_different (N : Normalizer R) (church : ChurchRosser R) {k n : Nat} {t u : Tm Head n}
    (verdict : check N k t u = .different) : ¬ Conv R.headEq t u R.computation := by
  intro conversion
  cases ht : N.run k t with
  | none => simp [check, ht] at verdict
  | some a =>
      cases hu : N.run k u with
      | none => simp [check, ht, hu] at verdict
      | some b =>
          rw [check_some N ht hu] at verdict
          have answerA : Answer R t a := N.sound ht
          have answerB : Answer R u b := N.sound hu
          have toB : Conv R.headEq t b R.computation :=
            .trans _ _ _ conversion (conv_of_stepStar answerB.1)
          have same : a = b := answer_unique church answerA ((answer_iff church).mpr ⟨toB, answerB.2⟩)
          simp [same] at verdict

/-- **"Not decided" is exactly a budget outcome**: the budget ran out on one side. -/
theorem check_undecided_iff (N : Normalizer R) {k n : Nat} {t u : Tm Head n} :
    check N k t u = .undecided ↔ N.run k t = none ∨ N.run k u = none := by
  cases ht : N.run k t with
  | none => simp [check, ht]
  | some a =>
      cases hu : N.run k u with
      | none => simp [check, ht, hu]
      | some b =>
          rw [check_some N ht hu]
          by_cases same : a = b <;> simp [same]

omit [DecidableEq Head] in
theorem run_mono_le (N : Normalizer R) {k k' n : Nat} {t v : Tm Head n} (le : k ≤ k')
    (answer : N.run k t = some v) : N.run k' t = some v := by
  induction le with
  | refl => exact answer
  | step _ ih => exact N.mono ih

/-- **Monotone in the budget**: a decided verdict is the verdict of every larger budget. -/
theorem check_mono (N : Normalizer R) {k k' n : Nat} {t u : Tm Head n} (le : k ≤ k')
    (decided : check N k t u ≠ .undecided) : check N k' t u = check N k t u := by
  cases ht : N.run k t with
  | none => simp [check, ht] at decided
  | some a =>
      cases hu : N.run k u with
      | none => simp [check, ht, hu] at decided
      | some b => rw [check_some N ht hu, check_some N (run_mono_le N le ht) (run_mono_le N le hu)]

/-- **Complete in the limit**: on terms the normalizer finishes, some budget decides, and a decided
verdict is exact on a Church–Rosser package. -/
theorem check_eventually (N : Normalizer R) (church : ChurchRosser R) {n : Nat} {t u : Tm Head n}
    {a b : Tm Head n} {k₁ k₂ : Nat} (ht : N.run k₁ t = some a) (hu : N.run k₂ u = some b) :
    ∃ k, check N k t u ≠ .undecided ∧
      (check N k t u = .equal ↔ Conv R.headEq t u R.computation) := by
  refine ⟨max k₁ k₂, ?_, ?_⟩
  · rw [check_some N (run_mono_le N (Nat.le_max_left _ _) ht) (run_mono_le N (Nat.le_max_right _ _) hu)]
    by_cases same : a = b <;> simp [same]
  · constructor
    · exact check_equal N
    · intro conversion
      rw [check_some N (run_mono_le N (Nat.le_max_left _ _) ht) (run_mono_le N (Nat.le_max_right _ _) hu)]
      by_cases same : a = b
      · simp [same]
      · exfalso
        have different : check N (max k₁ k₂) t u = .different := by
          rw [check_some N (run_mono_le N (Nat.le_max_left _ _) ht)
            (run_mono_le N (Nat.le_max_right _ _) hu)]
          simp [same]
        exact check_different N church different conversion

end Generic

/-! ## A normalizer for the declared addition on first-order terms -/

section Addition

open ProgrammingOnTheStep.VectorPackage
open NativeTypesOnTheStep.VectorAppend (AddStep vrules)
open NativeTypesOnTheStep.DeclaredConfluence (add_churchRosser)

/-- Terms built from variables and constants by application. -/
def firstOrder {n : Nat} : Tower.Tm n → Bool
  | .var _ => true
  | .const _ => true
  | .app f a => firstOrder f && firstOrder a
  | _ => false

/-- The rows of addition at the root, as a function. -/
def addRoot {n : Nat} : Tower.Tm n → Option (Tower.Tm n)
  | .app (.app (.const c) (.const z)) y =>
      if c = addN ∧ z = zeroN then some y else none
  | .app (.app (.const c) (.app (.const s) a)) y =>
      if c = addN ∧ s = succN then some (.app (.const succN) (.app (.app (.const addN) a) y)) else none
  | _ => none

theorem addRoot_sound {n : Nat} {t t' : Tower.Tm n} (h : addRoot t = some t') : AddStep t t' := by
  unfold addRoot at h
  split at h
  next =>
    split at h
    next names =>
      obtain ⟨rfl, rfl⟩ := names
      cases h
      exact AddStep.zero _
    next => cases h
  next =>
    split at h
    next names =>
      obtain ⟨rfl, rfl⟩ := names
      cases h
      exact AddStep.succ _ _
    next => cases h
  next => cases h

theorem addRoot_complete {n : Nat} {t t' : Tower.Tm n} (step : AddStep t t') : addRoot t = some t' := by
  cases step with
  | zero b => simp [addRoot]
  | succ a b => simp [addRoot]

/-- One step, function part first, then the argument, then the root. -/
def step1 {n : Nat} : Tower.Tm n → Option (Tower.Tm n)
  | .app f a =>
      match step1 f with
      | some f' => some (.app f' a)
      | none =>
          match step1 a with
          | some a' => some (.app f a')
          | none => addRoot (.app f a)
  | _ => none

theorem step1_sound {n : Nat} : ∀ {t t' : Tower.Tm n}, step1 t = some t' →
    StepCore vrules.computation vrules.headEq t t'
  | .app f a, t', h => by
      unfold step1 at h
      cases hf : step1 f with
      | some f' =>
          simp only [hf] at h
          cases h
          exact .congAppFun (step1_sound hf)
      | none =>
          cases ha : step1 a with
          | some a' =>
              simp only [hf, ha] at h
              cases h
              exact .congAppArg (step1_sound ha)
          | none =>
              simp only [hf, ha] at h
              exact .root (declare_step (addRoot_sound h))
  | .var _, _, h => by simp [step1] at h
  | .const _, _, h => by simp [step1] at h
  | .head _, _, h => by simp [step1] at h
  | .pi _ _, _, h => by simp [step1] at h
  | .sigma _ _, _, h => by simp [step1] at h
  | .id _ _ _, _, h => by simp [step1] at h
  | .lam _, _, h => by simp [step1] at h
  | .pair _ _, _, h => by simp [step1] at h
  | .fst _, _, h => by simp [step1] at h
  | .snd _, _, h => by simp [step1] at h
  | .refl _, _, h => by simp [step1] at h

/-- On first-order terms, no step left means normal. -/
theorem step1_none {n : Nat} : ∀ {t : Tower.Tm n}, firstOrder t = true → step1 t = none →
    ConstructorSystem.Normal vrules t
  | .var _, _, _ => fun step => by
      cases step with
      | root h => rcases h with h | h <;> cases h
  | .const _, _, _ => fun step => by
      cases step with
      | root h => rcases h with h | h <;> cases h
  | .app f a, fo, h => by
      simp only [firstOrder, Bool.and_eq_true] at fo
      unfold step1 at h
      cases hf : step1 f with
      | some f' => simp only [hf] at h; cases h
      | none =>
          cases ha : step1 a with
          | some a' => simp only [hf, ha] at h; cases h
          | none =>
              simp only [hf, ha] at h
              have normalF : ConstructorSystem.Normal vrules f := step1_none fo.1 hf
              have normalA : ConstructorSystem.Normal vrules a := step1_none fo.2 ha
              intro step
              cases step with
              | root root =>
                  rcases root with root | root
                  · cases root
                  · rw [addRoot_complete root] at h
                    cases h
              | betaPi body _ => simp [firstOrder] at fo
              | congAppFun inner => exact normalF inner
              | congAppArg inner => exact normalA inner
  | .head _, fo, _ => by simp [firstOrder] at fo
  | .pi _ _, fo, _ => by simp [firstOrder] at fo
  | .sigma _ _, fo, _ => by simp [firstOrder] at fo
  | .id _ _ _, fo, _ => by simp [firstOrder] at fo
  | .lam _, fo, _ => by simp [firstOrder] at fo
  | .pair _ _, fo, _ => by simp [firstOrder] at fo
  | .fst _, fo, _ => by simp [firstOrder] at fo
  | .snd _, fo, _ => by simp [firstOrder] at fo
  | .refl _, fo, _ => by simp [firstOrder] at fo

/-- Steps keep terms first-order. -/
theorem step1_firstOrder {n : Nat} : ∀ {t t' : Tower.Tm n}, firstOrder t = true → step1 t = some t' →
    firstOrder t' = true
  | .app f a, t', fo, h => by
      simp only [firstOrder, Bool.and_eq_true] at fo
      unfold step1 at h
      cases hf : step1 f with
      | some f' =>
          simp only [hf] at h
          cases h
          simp [firstOrder, step1_firstOrder fo.1 hf, fo.2]
      | none =>
          cases ha : step1 a with
          | some a' =>
              simp only [hf, ha] at h
              cases h
              simp [firstOrder, fo.1, step1_firstOrder fo.2 ha]
          | none =>
              simp only [hf, ha] at h
              have root := addRoot_sound h
              cases root with
              | zero b => exact fo.2
              | succ a' b =>
                  have firstA : firstOrder a' = true := by simpa [firstOrder] using fo.1
                  simp [firstOrder, firstA, fo.2]
  | .var _, _, _, h => by simp [step1] at h
  | .const _, _, _, h => by simp [step1] at h
  | .head _, _, fo, _ => by simp [firstOrder] at fo
  | .pi _ _, _, fo, _ => by simp [firstOrder] at fo
  | .sigma _ _, _, fo, _ => by simp [firstOrder] at fo
  | .id _ _ _, _, fo, _ => by simp [firstOrder] at fo
  | .lam _, _, fo, _ => by simp [firstOrder] at fo
  | .pair _ _, _, fo, _ => by simp [firstOrder] at fo
  | .fst _, _, fo, _ => by simp [firstOrder] at fo
  | .snd _, _, fo, _ => by simp [firstOrder] at fo
  | .refl _, _, fo, _ => by simp [firstOrder] at fo

/-- Normalize with fuel. -/
def normalizeFuel {n : Nat} : Nat → Tower.Tm n → Option (Tower.Tm n)
  | 0, t =>
      match step1 t with
      | none => some t
      | some _ => none
  | k + 1, t =>
      match step1 t with
      | none => some t
      | some t' => normalizeFuel k t'

theorem normalizeFuel_sound {n : Nat} : ∀ (k : Nat) {t v : Tower.Tm n}, firstOrder t = true →
    normalizeFuel k t = some v → StepStar vrules t v ∧ ConstructorSystem.Normal vrules v
  | 0, t, v, fo, h => by
      cases hs : step1 t with
      | none =>
          simp only [normalizeFuel, hs, Option.some.injEq] at h
          subst h
          exact ⟨.refl, step1_none fo hs⟩
      | some _ => simp [normalizeFuel, hs] at h
  | k + 1, t, v, fo, h => by
      cases hs : step1 t with
      | none =>
          simp only [normalizeFuel, hs, Option.some.injEq] at h
          subst h
          exact ⟨.refl, step1_none fo hs⟩
      | some t' =>
          simp only [normalizeFuel, hs] at h
          obtain ⟨steps, normal⟩ := normalizeFuel_sound k (step1_firstOrder fo hs) h
          exact ⟨.head (step1_sound hs) steps, normal⟩

theorem normalizeFuel_mono {n : Nat} : ∀ (k : Nat) {t v : Tower.Tm n},
    normalizeFuel k t = some v → normalizeFuel (k + 1) t = some v
  | 0, t, v, h => by
      cases hs : step1 t with
      | none =>
          simp only [normalizeFuel, hs] at h ⊢
          exact h
      | some _ => simp [normalizeFuel, hs] at h
  | k + 1, t, v, h => by
      cases hs : step1 t with
      | none =>
          simp only [normalizeFuel, hs] at h ⊢
          exact h
      | some t' =>
          simp only [normalizeFuel, hs] at h ⊢
          exact normalizeFuel_mono k h

/-- **A normalizer for the declared addition**: first-order terms only; other terms are never decided. -/
def addNormalizer : Normalizer vrules where
  run := fun k {_n} t => if firstOrder t then normalizeFuel k t else none
  sound := by
    intro k n t v h
    by_cases fo : firstOrder t = true
    · simp only [fo, if_true] at h
      exact normalizeFuel_sound k fo h
    · simp [fo] at h
  mono := by
    intro k n t v h
    by_cases fo : firstOrder t = true
    · simp only [fo, if_true] at h ⊢
      exact normalizeFuel_mono k h
    · simp [fo] at h

/-- **`add 2 1` and `3` are equal at budget 5**, so convertible. -/
theorem check_two_one :
    check addNormalizer 5 (.app (.app (.const addN) (numeral 2)) (numeral 1) : Tower.Tm 0) (numeral 3) =
      .equal := by
  decide

theorem two_one_convertible :
    Conv vrules.headEq (.app (.app (.const addN) (numeral 2)) (numeral 1) : Tower.Tm 0) (numeral 3)
      vrules.computation :=
  check_equal addNormalizer check_two_one

/-- **`add 1 0` and `2` are different**, so not convertible. -/
theorem check_one_zero :
    check addNormalizer 5 (.app (.app (.const addN) (numeral 1)) (numeral 0) : Tower.Tm 0) (numeral 2) =
      .different := by
  decide

theorem one_zero_not_two :
    ¬ Conv vrules.headEq (.app (.app (.const addN) (numeral 1)) (numeral 0) : Tower.Tm 0) (numeral 2)
      vrules.computation :=
  check_different addNormalizer add_churchRosser check_one_zero

/-- **At budget 0 the first pair is not decided**, and every budget from 5 on decides it as equal. -/
theorem check_budget_zero :
    check addNormalizer 0 (.app (.app (.const addN) (numeral 2)) (numeral 1) : Tower.Tm 0) (numeral 3) =
        .undecided ∧
      ∀ k, 5 ≤ k →
        check addNormalizer k (.app (.app (.const addN) (numeral 2)) (numeral 1) : Tower.Tm 0) (numeral 3) =
          .equal := by
  refine ⟨by decide, fun k le => ?_⟩
  rw [check_mono addNormalizer le (by rw [check_two_one]; decide)]
  exact check_two_one

/-- **With termination discharged by structural recursion, conversion between ground calls is
decided**: both calls answer a numeral, and the call are convertible exactly when the numerals are
equal. -/
theorem ground_conv_decided {t u : Tower.Tm 0} (groundT : Ground t) (groundU : Ground u) :
    Conv vrules.headEq t u vrules.computation ∨ ¬ Conv vrules.headEq t u vrules.computation := by
  obtain ⟨a, answerA⟩ := ground_answer groundT
  obtain ⟨b, answerB⟩ := ground_answer groundU
  by_cases same : a = b
  · subst same
    exact .inl (.trans _ _ _ (conv_of_stepStar answerA.1) (.symm _ _ (conv_of_stepStar answerB.1)))
  · refine .inr fun conversion => same ?_
    have toB : Conv vrules.headEq t (numeral b) vrules.computation :=
      .trans _ _ _ conversion (conv_of_stepStar answerB.1)
    have equal : (numeral a : Tower.Tm 0) = numeral b :=
      answer_unique add_churchRosser answerA ((answer_iff add_churchRosser).mpr ⟨toB, answerB.2⟩)
    exact HostTables.numeral_injective equal

end Addition

end NativeTypesOnTheStep.Computing.Budgeted

#print axioms NativeTypesOnTheStep.Computing.Budgeted.check_some
#print axioms NativeTypesOnTheStep.Computing.Budgeted.check_equal
#print axioms NativeTypesOnTheStep.Computing.Budgeted.check_different
#print axioms NativeTypesOnTheStep.Computing.Budgeted.check_undecided_iff
#print axioms NativeTypesOnTheStep.Computing.Budgeted.run_mono_le
#print axioms NativeTypesOnTheStep.Computing.Budgeted.check_mono
#print axioms NativeTypesOnTheStep.Computing.Budgeted.check_eventually
#print axioms NativeTypesOnTheStep.Computing.Budgeted.addRoot_sound
#print axioms NativeTypesOnTheStep.Computing.Budgeted.addRoot_complete
#print axioms NativeTypesOnTheStep.Computing.Budgeted.step1_sound
#print axioms NativeTypesOnTheStep.Computing.Budgeted.step1_none
#print axioms NativeTypesOnTheStep.Computing.Budgeted.step1_firstOrder
#print axioms NativeTypesOnTheStep.Computing.Budgeted.normalizeFuel_sound
#print axioms NativeTypesOnTheStep.Computing.Budgeted.normalizeFuel_mono
#print axioms NativeTypesOnTheStep.Computing.Budgeted.addNormalizer
#print axioms NativeTypesOnTheStep.Computing.Budgeted.check_two_one
#print axioms NativeTypesOnTheStep.Computing.Budgeted.two_one_convertible
#print axioms NativeTypesOnTheStep.Computing.Budgeted.check_one_zero
#print axioms NativeTypesOnTheStep.Computing.Budgeted.one_zero_not_two
#print axioms NativeTypesOnTheStep.Computing.Budgeted.check_budget_zero
#print axioms NativeTypesOnTheStep.Computing.Budgeted.ground_conv_decided

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
