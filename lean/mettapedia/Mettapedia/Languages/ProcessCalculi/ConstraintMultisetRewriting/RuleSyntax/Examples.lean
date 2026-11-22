import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderEq

/-!
# Every feature of the rule fires: positive and negative examples

One program over first-order atoms (numerals as constants and variables, no function symbols), at the
one-frame action with the identity extension. Its rules:

* `consume` takes a token `1` and makes a `2` (a take and a make);
* `answer` reads any row `x` and tells `x = 5` (a read and a tell);
* `guardAt n` reads any row `x` and guards `x = n` (an equation guard);
* `absentNine` asks the absence of `9` (an absence query).

Admitted firings: `consume_admitted` (with its result, `consume_result_present`,
`consume_result_label`), `answer_admitted`, `guardFive_admitted`, `absent_admitted_when_bound`.

* **A tell that binds a caller unknown** (`answer_binds_caller`): the request row is labelled by the
  caller's unknown `x`; the rule's own `x` is opened fresh as `x₁`, read against the row (two-way: both
  sides are unknowns) and told to be `5`. Every solution of the result's knowledge sends the caller's
  `x` to `5`.
* **Freshness is needed** (`capture_not_fresh`, `capture_refused`): opening the rule's `x` as the
  caller's `x` itself is not fresh, and the firing is refused.
* **A guard that fails** (`guardSix_refused`): with the caller's `x` bound to `5`, the guard `x₁ = 6`
  fails at the solutions of the firing's own information, which equate `x₁` with the row.
* **Absence reads through solutions** (`absent_admitted_when_bound`, `absent_refused_when_open`): the
  same row labelled `x` passes the absence of `9` when the knowledge binds `x` to `5`, and fails it
  when nothing binds `x`, since a solution may send `x` to `9`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-! ## Rules whose terms are fixed are opened freshly by any opening -/

section Ground

universe uT uS uO

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S) {O : Type uO} {P : Program (Terms T)}

/-- **A rule whose terms every substitution fixes is opened freshly by any opening.** -/
theorem fresh_of_ground (s : State (Terms T) O) (g : Firing O (ext A) P s.frame)
    (ground : ∀ t ∈ g.rule.terms, ∀ σ : S, A.apply σ t = t) : g.Fresh (frames A) s := by
  intro b θ h
  refine ⟨θ, fun t _ => ?_, fun t member => ?_⟩
  · show A.E (A.apply θ (A.apply A.identity t)) (A.apply θ t)
    rw [A.apply_identity]
    exact A.equivalence.refl _
  · show A.E (A.apply θ (A.apply g.opening t)) (A.apply h t)
    rw [ground t member g.opening, ground t member θ, ground t member h]
    exact A.equivalence.refl _

end Ground

/-! ## The program -/

/-- Terms at the one frame. -/
abbrev Tm := Terms (Term atoms)

/-- The frame action. -/
abbrev X := frames action

/-- The identity extension. -/
abbrev E := ext action

/-- The unknown `x`. -/
def x : Term atoms := .var 0

/-- The constant `n`. -/
def c (n : ℕ) : Term atoms := .const n

/-- Take a token `1`, make a `2`. -/
def consume : Rule Tm := ⟨PUnit.unit, ⟨[c 1], [], [], [], [c 2]⟩, []⟩

/-- Read any row `x`, tell `x = 5`. -/
def answer : Rule Tm := ⟨PUnit.unit, ⟨[], [x], [(x, c 5)], [], []⟩, []⟩

/-- Read any row `x`, guard `x = n`. -/
def guardAt (n : ℕ) : Rule Tm := ⟨PUnit.unit, ⟨[], [x], [], [.equal x (c n)], []⟩, []⟩

/-- Ask the absence of `9`. -/
def absentNine : Rule Tm := ⟨PUnit.unit, ⟨[], [], [], [.predicate .none (c 9)], []⟩, []⟩

/-- **The program.** -/
def demo : Program Tm := {consume, answer, guardAt 5, guardAt 6, absentNine}

/-- The opening that renames each unknown `n` to `n + 1`. -/
def shift : Subst atoms := fun v => Term.var (v + 1)

/-- The solution that sends every unknown to `n`. -/
def everywhere (n : ℕ) : Subst atoms := fun _ => c n

/-- A token `1` at identity `0`. -/
def tokenState : State Tm ℕ := ⟨PUnit.unit, [], {0}, fun _ => c 1⟩

/-- A request row at identity `0`, labelled by the caller's unknown `x`, which nothing binds. -/
def openRequest : State Tm ℕ := ⟨PUnit.unit, [], {0}, fun _ => x⟩

/-- The same request row, with the caller's unknown bound to `5`. -/
def boundRequest : State Tm ℕ := ⟨PUnit.unit, [(x, c 5)], {0}, fun _ => x⟩

/-! ## A take and a make -/

/-- Take the token, make identity `1`. -/
def consumeFiring : Firing ℕ E demo PUnit.unit :=
  ⟨consume, Or.inl rfl, PUnit.unit, Subst.id atoms, ⟨[0], [], [1]⟩, []⟩

theorem consume_information :
    consumeFiring.information X tokenState = [(c 1, c 1)] := rfl

theorem consume_admitted : (step X ℕ E demo).Admits (s := tokenState) consumeFiring := by
  refine (admits_iff consumeFiring).mpr ⟨?_, ⟨List.nodup_singleton 0, List.nodup_singleton 1, rfl, rfl,
    rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · apply fresh_of_ground action tokenState consumeFiring
    intro t member σ
    simp only [consumeFiring, consume, Rule.terms, List.map_nil, List.flatMap_nil, List.nil_append,
      List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [consumeFiring, tokenState, Selection.commit]
  · rw [consume_information]
    exact ⟨PUnit.unit, Subst.id atoms, fun e member => by
      obtain rfl := List.mem_singleton.mp member
      rfl⟩
  · intro check member
    simp [consumeFiring, consume, Firing.opened, RuleInstance.map] at member
  · intro q member
    simp [consumeFiring, consume, Firing.collectOpened] at member

theorem consume_result_present : (consumeFiring.result X tokenState).present = {1} := by
  simp [Firing.result, consumeFiring, tokenState, fire, Selection.commit]

theorem consume_result_label : (consumeFiring.result X tokenState).label 1 = c 2 := rfl

/-! ## A read and a tell that binds the caller's unknown -/

/-- Read the request row with the rule's `x` opened as `x₁`. -/
def answerFiring : Firing ℕ E demo PUnit.unit :=
  ⟨answer, Or.inr (Or.inl rfl), PUnit.unit, shift, ⟨[], [0], []⟩, []⟩

theorem answer_information :
    answerFiring.information X openRequest = [(.var 1, x), (.var 1, c 5)] := rfl

/-- **The rule's `x` is opened apart from the caller's `x`.** -/
theorem answer_fresh : answerFiring.Fresh X openRequest := by
  intro b g h
  refine ⟨fun v => if v = 1 then h 0 else g v, ?_, ?_⟩
  · rintro t (member | member | ⟨o, -, rfl⟩)
    · simp [openRequest] at member
    · simp [openRequest] at member
    · rfl
  · intro t member
    simp only [answerFiring, answer, Rule.terms, List.map_cons, List.map_nil, List.flatMap_nil,
      List.nil_append, List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl

theorem answer_admitted : (step X ℕ E demo).Admits (s := openRequest) answerFiring := by
  refine (admits_iff answerFiring).mpr ⟨answer_fresh, ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl,
    rfl⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [answerFiring, openRequest, Selection.commit]
  · rw [answer_information]
    refine ⟨PUnit.unit, everywhere 5, fun e member => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · intro check member
    simp [answerFiring, answer, Firing.opened, RuleInstance.map] at member
  · intro q member
    simp [answerFiring, answer, Firing.collectOpened] at member

/-- **The tell binds the caller's unknown**: every solution of the result's knowledge sends the
caller's `x` to `5`. -/
theorem answer_binds_caller (σ : Subst atoms)
    (solved : action.Models σ (answerFiring.result X openRequest).knowledge) : σ 0 = c 5 := by
  have known : (answerFiring.result X openRequest).knowledge = [(.var 1, x), (.var 1, c 5)] :=
    answer_information
  rw [known] at solved
  have read : σ 1 = σ 0 := solved (.var 1, x) List.mem_cons_self
  have told : σ 1 = c 5 := solved (.var 1, c 5) (List.mem_cons_of_mem _ List.mem_cons_self)
  exact read.symm.trans told

/-- Opening the rule's `x` as the caller's `x` itself. -/
def captureFiring : Firing ℕ E demo PUnit.unit :=
  ⟨answer, Or.inr (Or.inl rfl), PUnit.unit, Subst.id atoms, ⟨[], [0], []⟩, []⟩

/-- **Capturing the caller's unknown is not fresh.** -/
theorem capture_not_fresh : ¬ captureFiring.Fresh X openRequest := by
  intro fresh
  obtain ⟨u, state, rule⟩ := fresh PUnit.unit (fun _ => c 0) (fun _ => c 1)
  have seen : u 0 = c 0 := state x (Or.inr (Or.inr ⟨0, Finset.mem_singleton_self 0, rfl⟩))
  have opened : u 0 = c 1 := rule x (by simp [captureFiring, answer, Rule.terms])
  exact absurd (seen.symm.trans opened) (by simp [c])

theorem capture_refused : ¬ (step X ℕ E demo).Admits (s := openRequest) captureFiring :=
  fun admitted => capture_not_fresh ((admits_iff captureFiring).mp admitted).1

/-! ## A guard that holds and a guard that fails -/

/-- Read the request row and guard `x₁ = n`. -/
def guardFiring (n : ℕ) (member : guardAt n ∈ demo) : Firing ℕ E demo PUnit.unit :=
  ⟨guardAt n, member, PUnit.unit, shift, ⟨[], [0], []⟩, []⟩

theorem guard_information (n : ℕ) (member : guardAt n ∈ demo) :
    (guardFiring n member).information X boundRequest = [(x, c 5), (.var 1, x)] := rfl

theorem guard_fresh (n : ℕ) (member : guardAt n ∈ demo) :
    (guardFiring n member).Fresh X boundRequest := by
  intro b g h
  refine ⟨fun v => if v = 1 then h 0 else g v, ?_, ?_⟩
  · rintro t (inside | inside | ⟨o, -, rfl⟩)
    · simp only [boundRequest, List.map_cons, List.map_nil, List.mem_singleton] at inside
      subst inside
      rfl
    · simp only [boundRequest, List.map_cons, List.map_nil, List.mem_singleton] at inside
      subst inside
      rfl
    · rfl
  · intro t inside
    simp only [guardFiring, guardAt, Rule.terms, checkTerms, List.map_nil, List.flatMap_cons,
      List.flatMap_nil, List.nil_append, List.append_nil, List.cons_append, List.mem_cons,
      List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl <;> rfl

theorem guard_solvable (n : ℕ) (member : guardAt n ∈ demo) :
    X.Solvable ((guardFiring n member).information X boundRequest) := by
  rw [guard_information]
  refine ⟨PUnit.unit, everywhere 5, fun e inside => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl <;> rfl

/-- Every solution of the guard firing's information sends `x₁` to `5`. -/
theorem guard_solution (n : ℕ) (member : guardAt n ∈ demo) {σ : Subst atoms}
    (solved : X.Models (a := PUnit.unit) (b := PUnit.unit) σ
      ((guardFiring n member).information X boundRequest)) : σ 1 = c 5 := by
  rw [guard_information] at solved
  have bound : σ 0 = c 5 := solved (x, c 5) List.mem_cons_self
  have read : σ 1 = σ 0 := solved (.var 1, x) (List.mem_cons_of_mem _ List.mem_cons_self)
  exact read.trans bound

theorem guardFive_admitted :
    (step X ℕ E demo).Admits (s := boundRequest) (guardFiring 5 (Or.inr (Or.inr (Or.inl rfl)))) := by
  refine (admits_iff _).mpr ⟨guard_fresh 5 _, ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩,
    ?_, guard_solvable 5 _, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [guardFiring, boundRequest, Selection.commit]
  · intro check inside b σ solved
    simp only [guardFiring, guardAt, Firing.opened, RuleInstance.map, List.map_cons, List.map_nil,
      Check.map, List.mem_singleton] at inside
    subst inside
    exact guard_solution 5 _ solved
  · intro q inside
    simp [guardFiring, guardAt, Firing.collectOpened] at inside

/-- **A guard that fails**: the solutions equate `x₁` with the row, which the knowledge binds to `5`,
so the guard `x₁ = 6` fails there. -/
theorem guardSix_refused :
    ¬ (step X ℕ E demo).Admits (s := boundRequest)
      (guardFiring 6 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) := by
  intro admitted
  obtain ⟨-, -, -, -, checks, -⟩ := (admits_iff _).mp admitted
  have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) (everywhere 5)
      ((guardFiring 6 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).information X boundRequest) := by
    intro e inside
    have known : (guardFiring 6 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).information X boundRequest =
        [(x, c 5), (.var 1, x)] := rfl
    rw [known] at inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> rfl
  have holds := checks (.equal (.var 1) (c 6)) (List.mem_singleton_self _) PUnit.unit _ solved
  have five : (Term.const (5 : ℕ) : Term atoms) = Term.const (6 : ℕ) := holds
  exact absurd (Term.const.inj five) (by decide)

/-! ## Absence that holds and absence that fails -/

/-- Ask the absence of `9`. -/
def absentFiring : Firing ℕ E demo PUnit.unit :=
  ⟨absentNine, Or.inr (Or.inr (Or.inr (Or.inr rfl))), PUnit.unit, Subst.id atoms, ⟨[], [], []⟩, []⟩

theorem absent_fresh (s : State Tm ℕ) : Firing.Fresh X s absentFiring := by
  apply fresh_of_ground action s absentFiring
  intro t member σ
  simp only [absentFiring, absentNine, Rule.terms, checkTerms, List.map_nil, List.flatMap_cons,
    List.flatMap_nil, List.nil_append, List.append_nil, List.mem_singleton] at member
  subst member
  rfl

/-- **Absence holds when the knowledge binds the row away from the pattern.** -/
theorem absent_admitted_when_bound : (step X ℕ E demo).Admits (s := boundRequest) absentFiring := by
  refine (admits_iff absentFiring).mpr ⟨absent_fresh boundRequest,
    ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [absentFiring, boundRequest, Selection.commit]
  · refine ⟨PUnit.unit, everywhere 5, fun e inside => ?_⟩
    have known : absentFiring.information X boundRequest = [(x, c 5)] := rfl
    rw [known, List.mem_singleton] at inside
    subst inside
    rfl
  · intro check inside b σ solved
    have known : absentFiring.information X boundRequest = [(x, c 5)] := rfl
    rw [known] at solved
    have bound : σ 0 = c 5 := solved (x, c 5) List.mem_cons_self
    simp only [absentFiring, absentNine, Firing.opened, RuleInstance.map, List.map_cons,
      List.map_nil, Check.map, List.mem_singleton] at inside
    subst inside
    intro o _ equated
    have nine : (c 9 : Term atoms) = σ 0 := equated
    rw [bound] at nine
    exact absurd (Term.const.inj nine) (by decide)
  · intro q inside
    simp [absentFiring, absentNine, Firing.collectOpened] at inside

/-- **Absence fails when nothing binds the row**: a solution may send `x` to `9`. -/
theorem absent_refused_when_open : ¬ (step X ℕ E demo).Admits (s := openRequest) absentFiring := by
  intro admitted
  obtain ⟨-, -, -, -, checks, -⟩ := (admits_iff absentFiring).mp admitted
  have known : absentFiring.information X openRequest = [] := rfl
  have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) (everywhere 9)
      (absentFiring.information X openRequest) := by
    rw [known]
    intro e inside
    cases inside
  have holds := checks (.predicate .none (c 9)) (List.mem_singleton_self _) PUnit.unit _ solved
  exact holds 0 (Finset.mem_singleton_self 0) rfl

#print axioms fresh_of_ground
#print axioms consume_admitted
#print axioms consume_result_present
#print axioms answer_admitted
#print axioms answer_binds_caller
#print axioms capture_not_fresh
#print axioms capture_refused
#print axioms guardFive_admitted
#print axioms guardSix_refused
#print axioms absent_admitted_when_bound
#print axioms absent_refused_when_open

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples
