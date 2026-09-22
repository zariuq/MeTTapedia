import Mettapedia.OSLF.Formula
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# OSLF Decidability: Bounded Reflection and Incompleteness

## LLM Primer
- `sem` is Prop-valued (noncomputable over arbitrary R, I)
- `check` is the bounded model checker (kernel-reducible, fuel-bounded)
- `semFuel` is the Prop mirror of `check` — same fuel, same conservative behavior
- Reflection: `check ... = .sat ↔ semFuel ...` (biconditional)
- Sound lift: `semFuel ... → sem ...` (semFuel is a subset of sem)
- Incompleteness: ∃ instances where sem holds but checker never returns .sat

## Contents

1. `semFuel` — bounded Prop-valued semantics matching `check` exactly
2. `check_sat_iff_semFuel` — reflection biconditional
3. `semFuel_implies_sem` — sound lift to unbounded semantics
4. `checker_incomplete_general` — incompleteness for unbounded reductions

## Design

`semFuel` is NOT `sem`. It mirrors the checker's conservative choices:
- `imp φ ψ` only checks ψ (consequent), ignoring φ (like checker)
- `box` is always False (checker returns `.unknown` for box)
- fuel 0 is False (checker returns `.unknown` at fuel 0)
- `dia` searches a concrete List of successors (not existential over Prop)

This makes `check_sat_iff_semFuel` a true biconditional, not just soundness.
-/

namespace Mettapedia.OSLF.Formula

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Bounded Prop-Valued Semantics

`semFuel` mirrors the `check` function structure exactly, but returns `Prop`
instead of `CheckResult`. This gives us a clean reflection layer. -/

/-- Bounded Prop-valued semantics matching the `check` function.

    `semFuel step I fuel φ p` holds iff the checker would return `.sat`
    on the same inputs. This is the "semantic shadow" of the checker. -/
def semFuel (step : Pattern → List Pattern) (I : AtomSem)
    (fuel : Nat) (φ : OSLFFormula) (p : Pattern) : Prop :=
  match fuel with
  | 0 => False
  | fuel + 1 =>
    match φ with
    | .top => True
    | .bot => False
    | .atom a => I a p
    | .and φ₁ φ₂ => semFuel step I fuel φ₁ p ∧ semFuel step I fuel φ₂ p
    | .or φ₁ φ₂ => semFuel step I fuel φ₁ p ∨ semFuel step I fuel φ₂ p
    | .imp _ φ₂ => semFuel step I fuel φ₂ p
    | .dia φ' => ∃ q ∈ step p, semFuel step I fuel φ' q
    | .box _ => False
    | .var _ => False
    | .mu φ' =>
      if OSLFFormula.closedAt 1 φ' && OSLFFormula.positiveIn 0 φ' then
        semFuel step I fuel (OSLFFormula.unfold φ') p
      else
        False
    | .emptyColl kind => p = Pattern.collection kind [] none
    | .headed label body =>
      ∃ inner : Pattern, p = Pattern.apply label [inner] ∧ semFuel step I fuel body inner
    | .cut kind φ₁ φ₂ =>
      ∃ leftParts rightParts : List Pattern,
        p = Pattern.collection kind (leftParts ++ rightParts) none ∧
          semFuel step I fuel φ₁ (Pattern.collection kind leftParts none) ∧
          semFuel step I fuel φ₂ (Pattern.collection kind rightParts none)

/-! ## Reflection: check .sat ↔ semFuel

The key theorem: the checker returning `.sat` is logically equivalent to
`semFuel` holding. This is a true biconditional because `semFuel` was
designed to exactly mirror the checker's behavior. -/

/-- `aggregateDia` answers `.sat` exactly when some entry does. -/
private theorem aggregateDia_eq_sat_iff (results : List CheckResult) :
    aggregateDia results = .sat ↔ ∃ r ∈ results, r = CheckResult.sat := by
  constructor
  · exact aggregateDia_sat
  · rintro ⟨r, member, rfl⟩
    induction results with
    | nil => exact absurd member (List.not_mem_nil)
    | cons head tail ih =>
        rcases List.mem_cons.mp member with rfl | inTail
        · simp [aggregateDia]
        · cases head with
          | sat => simp [aggregateDia]
          | unsat => simpa [aggregateDia] using ih inTail
          | unknown => simp only [aggregateDia, ih inTail]

/-- Helper: `aggregateDia` returning `.sat` iff some successor satisfies the formula. -/
private theorem aggregateDia_sat_iff {step : Pattern → List Pattern}
    {I_check : AtomCheck} {I_sem : AtomSem}
    {fuel : Nat} {φ : OSLFFormula} {succs : List Pattern}
    (h_refl : ∀ q, q ∈ succs → (check step I_check fuel q φ = .sat ↔
                              semFuel step I_sem fuel φ q)) :
    aggregateDia (succs.map fun q => check step I_check fuel q φ) = .sat ↔
    ∃ q ∈ succs, semFuel step I_sem fuel φ q := by
  induction succs with
  | nil =>
    simp [aggregateDia]
  | cons hd tl ihtl =>
    simp only [List.map_cons]
    have h_hd := h_refl hd List.mem_cons_self
    have h_tl : ∀ q, q ∈ tl → (check step I_check fuel q φ = .sat ↔
                                  semFuel step I_sem fuel φ q) :=
      fun q hq => h_refl q (List.mem_cons_of_mem _ hq)
    have ih := ihtl h_tl
    constructor
    · intro h
      cases hcheck : check step I_check fuel hd φ with
      | sat =>
        exact ⟨hd, List.mem_cons_self, h_hd.mp hcheck⟩
      | unsat =>
        simp only [aggregateDia, hcheck] at h
        obtain ⟨q, hq, hsem⟩ := ih.mp h
        exact ⟨q, List.mem_cons_of_mem _ hq, hsem⟩
      | unknown =>
        simp only [aggregateDia, hcheck] at h
        have htl_sat : aggregateDia (tl.map fun q => check step I_check fuel q φ) = .sat := by
          revert h; cases aggregateDia (tl.map fun q => check step I_check fuel q φ) <;> simp
        obtain ⟨q, hq, hsem⟩ := ih.mp htl_sat
        exact ⟨q, List.mem_cons_of_mem _ hq, hsem⟩
    · rintro ⟨q, hq, hsem⟩
      cases List.mem_cons.mp hq with
      | inl heq =>
        subst heq
        have := h_hd.mpr hsem
        simp only [aggregateDia, this]
      | inr htl_mem =>
        have htl_sat : aggregateDia (tl.map fun q => check step I_check fuel q φ) = .sat :=
          ih.mpr ⟨q, htl_mem, hsem⟩
        cases hcheck : check step I_check fuel hd φ with
        | sat => simp [aggregateDia]
        | unsat => simp [aggregateDia, htl_sat]
        | unknown => simp [aggregateDia, htl_sat]

/-- **Reflection theorem**: the checker returns `.sat` if and only if
    the bounded Prop-valued semantics `semFuel` holds.

    This is the core reflection principle that allows us to use
    kernel-reducible computation (via `check`) to prove `semFuel` goals.

    **Hypotheses**:
    - `h_atoms`: atom checker is a faithful Boolean reflection of atom semantics -/
theorem check_sat_iff_semFuel
    {step : Pattern → List Pattern} {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true ↔ I_sem a p)
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula} :
    check step I_check fuel p φ = .sat ↔ semFuel step I_sem fuel φ p := by
  induction fuel generalizing p φ with
  | zero => simp [check, semFuel]
  | succ n ih =>
    cases φ with
    | emptyColl kind =>
      simp only [check, semFuel]
      constructor
      · intro h
        split at h
        · rename_i shape; simpa using shape
        · exact absurd h (by simp)
      · intro h; simp [h]
    | headed label body =>
      simp only [check, semFuel]
      constructor
      · intro h
        split at h
        · rename_i labelVar inner
          split at h
          · rename_i sameLabel
            simp only [beq_iff_eq] at sameLabel
            subst sameLabel
            exact ⟨inner, rfl, ih.mp h⟩
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · rintro ⟨inner, rfl, holds⟩
        simp only [beq_self_eq_true, if_true]
        exact ih.mpr holds
    | cut kind φ₁ φ₂ =>
      simp only [check, semFuel]
      constructor
      · intro h
        split at h
        · rename_i kindVar elements
          split at h
          · rename_i sameKind
            simp only [beq_iff_eq] at sameKind
            subst sameKind
            obtain ⟨result, resultMember, resultSat⟩ := aggregateDia_sat h
            obtain ⟨split, splitMember, resultEq⟩ := List.mem_map.mp resultMember
            obtain ⟨index, -, splitEq⟩ := List.mem_map.mp splitMember
            subst splitEq
            subst resultEq
            simp only at resultSat
            split at resultSat
            · rename_i leftSat rightSat
              exact ⟨elements.take index, elements.drop index,
                by rw [List.take_append_drop], ih.mp leftSat, ih.mp rightSat⟩
            · exact absurd resultSat (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · rintro ⟨leftParts, rightParts, rfl, holdsLeft, holdsRight⟩
        simp only [beq_self_eq_true, if_true]
        refine (aggregateDia_eq_sat_iff _).mpr ⟨CheckResult.sat, ?_, rfl⟩
        refine List.mem_map.mpr ⟨(Pattern.collection kind leftParts none,
          Pattern.collection kind rightParts none), ?_, ?_⟩
        · refine List.mem_map.mpr ⟨leftParts.length, ?_, ?_⟩
          · simp
          · simp [cutSplits]
        · show (match check step I_check n (Pattern.collection kind leftParts none) φ₁,
                  check step I_check n (Pattern.collection kind rightParts none) φ₂ with
                | CheckResult.sat, CheckResult.sat => CheckResult.sat
                | _, _ => CheckResult.unknown) = CheckResult.sat
          rw [ih.mpr holdsLeft, ih.mpr holdsRight]
    | top => simp [check, semFuel]
    | bot => simp [check, semFuel]
    | atom a =>
      simp only [check, semFuel]
      constructor
      · intro h; split at h <;> simp_all
      · intro h
        have := (h_atoms a p).mpr h
        simp [this]
    | and φ₁ φ₂ =>
      simp only [check, semFuel]
      constructor
      · intro h
        have h1 : check step I_check n p φ₁ = .sat := by
          revert h; cases check step I_check n p φ₁ <;>
            cases check step I_check n p φ₂ <;> simp
        have h2 : check step I_check n p φ₂ = .sat := by
          revert h; cases check step I_check n p φ₁ <;>
            cases check step I_check n p φ₂ <;> simp
        exact ⟨ih.mp h1, ih.mp h2⟩
      · rintro ⟨h1, h2⟩
        have hsat1 := ih.mpr h1
        have hsat2 := ih.mpr h2
        simp [hsat1, hsat2]
    | or φ₁ φ₂ =>
      simp only [check, semFuel]
      constructor
      · intro h
        have : check step I_check n p φ₁ = .sat ∨ check step I_check n p φ₂ = .sat := by
          revert h; cases check step I_check n p φ₁ <;>
            cases check step I_check n p φ₂ <;> simp
        cases this with
        | inl h₁ => exact Or.inl (ih.mp h₁)
        | inr h₂ => exact Or.inr (ih.mp h₂)
      · rintro (h1 | h2)
        · have hsat := ih.mpr h1; simp [hsat]
        · have hsat := ih.mpr h2
          cases check step I_check n p φ₁ <;> simp [hsat]
    | imp φ₁ φ₂ =>
      simp only [check, semFuel]
      constructor
      · intro h
        have : check step I_check n p φ₂ = .sat := by
          revert h; cases check step I_check n p φ₂ <;> simp
        exact ih.mp this
      · intro h
        have hsat := ih.mpr h
        simp [hsat]
    | dia φ' =>
      simp only [check, semFuel]
      exact aggregateDia_sat_iff (fun q _ => ih)
    | box _ =>
      simp [check, semFuel]
    | var _ =>
      simp [check, semFuel]
    | mu φ' =>
      by_cases guard :
          (OSLFFormula.closedAt 1 φ' && OSLFFormula.positiveIn 0 φ') = true
      · simp only [check, semFuel, guard, if_true]
        exact ih
      · simp only [check, semFuel, guard, if_false]
        simp

/-! ## Sound Lift: semFuel → sem

`semFuel` is conservative: it only asserts what the checker can verify.
Since `check_sat_sound` shows `.sat → sem`, and `check_sat_iff_semFuel`
shows `.sat ↔ semFuel`, we get `semFuel → sem` for free.

But we prove it directly for clarity. -/

/-- **Sound lift**: bounded semantics implies unbounded semantics.

    If `semFuel` holds with step function `step`, and `step` is sound
    w.r.t. the reduction relation `R`, then `sem R I φ p` holds. -/
theorem semFuel_implies_sem
    {R : Pattern → Pattern → Prop}
    {step : Pattern → List Pattern} {I : AtomSem}
    (h_step : ∀ p q, q ∈ step p → R p q)
    {fuel : Nat} {φ : OSLFFormula} {p : Pattern}
    (h : semFuel step I fuel φ p) : sem R I φ p := by
  induction fuel generalizing p φ with
  | zero => exact absurd h (by simp [semFuel])
  | succ n ih =>
    cases φ with
    | top => exact trivial
    | emptyColl kind =>
      simp only [semFuel] at h
      simp only [sem, semEnv]
      exact fullFrame.le_close _ p h
    | headed label body =>
      simp only [semFuel] at h
      obtain ⟨inner, shape, holds⟩ := h
      simp only [sem, semEnv]
      exact fullFrame.le_close _ p ⟨inner, shape, ih holds⟩
    | cut kind φ₁ φ₂ =>
      simp only [semFuel] at h
      obtain ⟨leftParts, rightParts, shape, holdsLeft, holdsRight⟩ := h
      simp only [sem, semEnv]
      exact fullFrame.le_close _ p ⟨leftParts, rightParts, shape, ih holdsLeft, ih holdsRight⟩
    | bot => exact absurd h (by simp [semFuel])
    | atom a => exact h
    | and φ₁ φ₂ =>
      simp only [semFuel] at h
      exact ⟨ih h.1, ih h.2⟩
    | or φ₁ φ₂ =>
      simp only [semFuel] at h
      exact h.elim (Or.inl ∘ ih) (Or.inr ∘ ih)
    | imp φ₁ φ₂ =>
      simp only [semFuel] at h
      simp only [sem]
      intro _
      exact ih h
    | dia φ' =>
      simp only [semFuel] at h
      obtain ⟨q, hq_mem, hq_sem⟩ := h
      exact ⟨q, h_step p q hq_mem, ih hq_sem⟩
    | box _ =>
      exact absurd h (by simp [semFuel])
    | var _ =>
      exact absurd h (by simp [semFuel])
    | mu φ' =>
      simp only [semFuel] at h
      split at h
      · rename_i guard
        simp only [Bool.and_eq_true] at guard
        rw [sem_mu_eq_unfold R I φ' guard.1 guard.2]
        exact ih h
      · exact absurd h (by simp)

/-- Combined reflection + lift: if the checker returns `.sat`, then `sem` holds.

    This is essentially `check_sat_sound` reproved via the semFuel detour,
    confirming consistency of our reflection layer. -/
theorem check_sat_implies_sem_via_reflection
    {R : Pattern → Pattern → Prop}
    {step : Pattern → List Pattern}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true ↔ I_sem a p)
    (h_step : ∀ p q, q ∈ step p → R p q)
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula}
    (h : check step I_check fuel p φ = .sat) :
    sem R I_sem φ p :=
  semFuel_implies_sem h_step ((check_sat_iff_semFuel h_atoms).mp h)

/-! ## Monotonicity: more fuel never loses results -/

/-- More fuel preserves `semFuel`: if it holds at fuel `n`, it holds at `n + 1`. -/
theorem semFuel_mono {step : Pattern → List Pattern} {I : AtomSem}
    {n : Nat} {φ : OSLFFormula} {p : Pattern}
    (h : semFuel step I n φ p) : semFuel step I (n + 1) φ p := by
  induction n generalizing p φ with
  | zero => exact absurd h (by simp [semFuel])
  | succ k ih =>
    cases φ with
    | top => trivial
    | emptyColl kind =>
      simp only [semFuel] at h ⊢
      exact h
    | headed label body =>
      simp only [semFuel] at h ⊢
      obtain ⟨inner, shape, holds⟩ := h
      exact ⟨inner, shape, ih holds⟩
    | cut kind φ₁ φ₂ =>
      simp only [semFuel] at h ⊢
      obtain ⟨leftParts, rightParts, shape, holdsLeft, holdsRight⟩ := h
      exact ⟨leftParts, rightParts, shape, ih holdsLeft, ih holdsRight⟩
    | bot => exact absurd h (by simp [semFuel])
    | atom a => exact h
    | and φ₁ φ₂ =>
      simp only [semFuel] at h ⊢
      exact ⟨ih h.1, ih h.2⟩
    | or φ₁ φ₂ =>
      simp only [semFuel] at h ⊢
      exact h.elim (Or.inl ∘ ih) (Or.inr ∘ ih)
    | imp _ φ₂ =>
      simp only [semFuel] at h ⊢
      exact ih h
    | dia φ' =>
      simp only [semFuel] at h ⊢
      obtain ⟨q, hq_mem, hq_sem⟩ := h
      exact ⟨q, hq_mem, ih hq_sem⟩
    | box _ =>
      exact absurd h (by simp [semFuel])
    | var _ =>
      exact absurd h (by simp [semFuel])
    | mu φ' =>
      simp only [semFuel] at h ⊢
      split at h
      · rename_i guard
        simp only [guard, if_true]
        exact ih h
      · exact absurd h (by simp)

/-- `semFuel` is monotone in fuel: `n ≤ m → semFuel ... n ... → semFuel ... m ...` -/
theorem semFuel_mono_fuel {step : Pattern → List Pattern} {I : AtomSem}
    {n m : Nat} (hnm : n ≤ m) {φ : OSLFFormula} {p : Pattern}
    (h : semFuel step I n φ p) : semFuel step I m φ p := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact semFuel_mono ih

/-! ## Checker Incompleteness

The bounded checker is necessarily incomplete: there exist formula-pattern pairs
where `sem` holds but the checker returns `.unknown` (never `.sat`) at any fuel.

### Construction

Define a language with a single rewrite rule that shifts a counter:
  `⊛count(n) ⇝ ⊛count(n+1)`

This generates an infinite reduction chain. Consider:
- Formula: `◇(atom "target")` — "some successor satisfies target"
- Atom semantics: `I "target" p ↔ True` (always true)
- Start pattern: `⊛count(0)`

Semantically: `sem R I (◇ ⊤) p` holds because `R p q` for some q, and `⊤` is true.
But for `◇(atom "target")`, the checker at fuel `n` only explores `n` successors
in the rewrite chain, and we need to construct the scenario carefully.

Actually, the simpler incompleteness is for `box`: the checker always returns
`.unknown` for `□ φ`, but `sem R I (□ φ) p` can hold when p has no predecessors.

### Box incompleteness

For ANY language and atom semantics, and any p with no predecessors:
- `sem R I (□ ⊤) p = ∀ q, R q p → True = True`
- `check step I fuel p (□ ⊤) = .unknown ≠ .sat`
-/

/-- **Box incompleteness**: for any pattern p, the checker returns `.unknown` for
    `□ φ`, but `sem R I (□ ⊤) p` always holds (vacuously or otherwise).

    This is the simplest form of checker incompleteness: the checker is
    structurally unable to handle backward-looking modalities. -/
theorem box_top_sem_always {R : Pattern → Pattern → Prop} {I : AtomSem}
    {p : Pattern} : sem R I (.box .top) p := by
  intro _ _; trivial

theorem box_check_never_sat {step : Pattern → List Pattern} {I : AtomCheck}
    {fuel : Nat} {φ : OSLFFormula} {p : Pattern} :
    check step I fuel p (.box φ) ≠ .sat := by
  cases fuel with
  | zero => simp [check]
  | succ n => simp [check]

/-- **Checker incompleteness (box)**: there exists a formula where `sem` holds
    but the checker never returns `.sat` at any fuel level. -/
theorem checker_incomplete_box :
    ∃ (φ : OSLFFormula),
      (∀ (R : Pattern → Pattern → Prop) (I : AtomSem) (p : Pattern),
        sem R I φ p) ∧
      (∀ (step : Pattern → List Pattern) (I : AtomCheck) (fuel : Nat) (p : Pattern),
        check step I fuel p φ ≠ .sat) :=
  ⟨.box .top,
   fun _ _ _ => box_top_sem_always,
   fun _ _ _ _ => box_check_never_sat⟩

/-- **Global checker incompleteness**: there is no way to make the bounded checker
    a complete decision procedure for `sem`. Specifically, there is no choice of
    step function, atom checker, and fuel such that `.sat` ↔ `sem` for all formulas.

    Proof: `□ ⊤` is always true semantically but always `.unknown` in the checker. -/
theorem checker_not_complete_global :
    ¬ ∃ (step : Pattern → List Pattern) (I_check : AtomCheck) (I_sem : AtomSem)
        (fuel : Nat),
      ∀ (R : Pattern → Pattern → Prop) (φ : OSLFFormula) (p : Pattern),
        check step I_check fuel p φ = .sat ↔ sem R I_sem φ p := by
  rintro ⟨step, I_check, I_sem, fuel, h⟩
  have := (h (fun _ _ => True) (.box .top) (.fvar "x")).mpr box_top_sem_always
  exact absurd this box_check_never_sat

/-! ### Diamond incompleteness via infinite chains

For `◇`, incompleteness manifests when the semantic reduction relation `R`
has witnesses that are not reachable by the finite step function.

Concretely: if `R p q` holds for some `q` satisfying `φ`, but `q ∉ step p`,
then `sem R I (◇ φ) p` holds but `check step I fuel p (◇ φ)` may not find it. -/

/-- **Diamond incompleteness**: if the step function produces no successors
    for pattern p, but R has a successor, then ◇ φ is unprovable by the checker
    but may hold semantically. -/
theorem checker_incomplete_dia_empty_step
    {R : Pattern → Pattern → Prop}
    {I_sem : AtomSem}
    {φ : OSLFFormula} {p q : Pattern}
    (hR : R p q) (hφ : sem R I_sem φ q) :
    sem R I_sem (.dia φ) p ∧
    ∀ (step : Pattern → List Pattern) (_ : step p = []) (I : AtomCheck) (fuel : Nat),
      check step I fuel p (.dia φ) ≠ .sat := by
  refine ⟨⟨q, hR, hφ⟩, ?_⟩
  intro step hstep I fuel hcheck
  cases fuel with
  | zero => simp [check] at hcheck
  | succ n =>
    simp only [check, hstep, List.map_nil] at hcheck
    simp [aggregateDia] at hcheck

end Mettapedia.OSLF.Formula
