import Mettapedia.Languages.MeTTa.PeTTa.PatternReadByCells

/-!
# A call selects exactly the admissible equations, on values with no unknowns

A call of an authored function meets its values with each candidate equation's argument
patterns (`Unifying.selections`, by `Unifying.unifyArguments`), each equation renamed apart
for its own use. `PatternReadByCells` says what one pattern means. This module says what
the selection means.

* **The arguments hold** (`ArgumentsHold`): the list of argument patterns and the list of
  values, spelled, are equal. That is each pattern holding of its value, and as many
  patterns as values (`argumentsHold_iff`). The argument list itself is never read through
  the list view.
* **An equation is admissible** for a call when some valuation solves the caller's bindings
  and makes each argument pattern hold of its value (`Admissible`).
* **The theorem** (`call_selects_exactly_the_admissible`): for a selection the machine
  completed, with the caller's bindings in solved form and values with no unknowns, the
  equation at a position is selected exactly when it is admissible, and the bindings its
  body goes on with mean exactly the valuations that solve the caller's bindings and make
  its patterns hold. Nothing else is selected
  (`call_goes_on_only_with_admissible_equations`).

Values with unknowns are outside these theorems: there the pattern unifier reads a list
constructor against an unknown as data (`an_unknown_value_is_read_otherwise`).

Controls: the equation `(= (first-of (cons $h $t)) $h)` is selected by the list `(p q)`
and not by the symbol `foo`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ListView

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation (presentation)
open Mettapedia.Languages.MeTTa.PeTTa.Unifying
  (Unified unifyPattern unifyLists unifyArguments selections rename Control Idempotent
    unifyPattern_refines unifyLists_refines unifyArguments_decides)
open Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics (Equation)

/-! ## The arguments of a call -/

/-- Argument patterns hold of a call's values under a valuation: the two lists, spelled,
are equal. -/
def ArgumentsHold (ρ : Valuation) (patterns values : List Atom) : Prop :=
  EquationHolds (fun name => spell (ρ name))
    (readPattern.readEach patterns, spell.spellItems values)

/-- The arguments hold exactly when there are as many patterns as values and each pattern
holds of its value. -/
theorem argumentsHold_iff (ρ : Valuation) :
    ∀ patterns values : List Atom,
      ArgumentsHold ρ patterns values ↔ List.Forall₂ (PatternHolds ρ) patterns values
  | [], [] => by simp [ArgumentsHold, EquationHolds]
  | [], value :: values => by simp [ArgumentsHold, EquationHolds]
  | pattern :: patterns, [] => by simp [ArgumentsHold, EquationHolds]
  | pattern :: patterns, value :: values => by
      unfold ArgumentsHold
      rw [readEach_cons, spellItems_cons, cell_equation_iff, List.forall₂_cons]
      exact and_congr Iff.rfl (argumentsHold_iff ρ patterns values)

/-- What the argument unifier answers, on values with no unknowns. -/
theorem unifyArguments_agrees {bindings : Subst} {patterns values : List Atom}
    (valid : Idempotent bindings) (ground : Ground (.expression values)) :
    (∀ bound, unifyArguments bindings patterns values = .ok bound →
      ∀ ρ : Valuation, ρ ∈ SolutionsOf EquationHolds (presentation bound) ↔
        ρ ∈ SolutionsOf EquationHolds (presentation bindings) ∧
          ArgumentsHold ρ patterns values) ∧
    (unifyArguments bindings patterns values = .clash →
      ∀ ρ : Valuation, ρ ∈ SolutionsOf EquationHolds (presentation bindings) →
        ¬ ArgumentsHold ρ patterns values) :=
  lists_agree (pattern_unifier_agrees _) patterns values bindings valid ground

/-- Some valuation solves the caller's bindings and makes each argument pattern hold of its
value. -/
def Admissible (bindings : Subst) (patterns values : List Atom) : Prop :=
  ∃ ρ : Valuation, ρ ∈ SolutionsOf EquationHolds (presentation bindings) ∧
    List.Forall₂ (PatternHolds ρ) patterns values

/-- Bindings the argument unifier answers mean the valuations that solve the caller's
bindings and make each pattern hold of its value. -/
theorem unifyArguments_means {bindings bound : Subst} {patterns values : List Atom}
    (valid : Idempotent bindings) (ground : Ground (.expression values))
    (unified : unifyArguments bindings patterns values = .ok bound) :
    SolutionsOf EquationHolds (presentation bound) =
      SolutionsOf EquationHolds (presentation bindings) ∩
        {ρ | List.Forall₂ (PatternHolds ρ) patterns values} := by
  ext ρ
  rw [(unifyArguments_agrees valid ground).1 bound unified ρ, argumentsHold_iff]
  rfl

/-- The argument unifier answers bindings exactly when the equation is admissible. -/
theorem unifyArguments_accepts_iff {bindings : Subst} {patterns values : List Atom}
    (valid : Idempotent bindings) (ground : Ground (.expression values)) :
    (∃ bound, unifyArguments bindings patterns values = .ok bound) ↔
      Admissible bindings patterns values := by
  constructor
  · rintro ⟨bound, unified⟩
    have boundValid := (unifyLists_refines _ (unifyPattern_refines _) patterns values
      bindings bound valid unified).1
    have model := environment_solves ⟨bound, boundValid⟩
    rw [unifyArguments_means valid ground unified] at model
    exact ⟨_, model.1, model.2⟩
  · rintro ⟨ρ, model, holds⟩
    cases result : unifyArguments bindings patterns values with
    | ok bound => exact ⟨bound, rfl⟩
    | clash =>
        exact absurd ((argumentsHold_iff ρ patterns values).mpr holds)
          ((unifyArguments_agrees valid ground).2 result ρ model)
    | exhausted =>
        exact absurd result (unifyArguments_decides bindings patterns values valid)

/-! ## The selection of a call -/

/-- A selection that completed decided every candidate: at each position the argument
unifier either succeeded, and that equation's body under its unifier is among the controls,
or clashed. -/
theorem selections_row (bindings : Subst) (values : List Atom) :
    ∀ (use : Nat) (equations : List Equation) (controls : List Control),
      selections bindings values use equations = some controls →
      ∀ (index : Nat) (equation : Equation), equations[index]? = some equation →
        (∃ bound, unifyArguments bindings
            (equation.arguments.map (rename (use + index))) values = .ok bound ∧
          Control.evaluate bound (rename (use + index) equation.body) ∈ controls) ∨
        unifyArguments bindings
          (equation.arguments.map (rename (use + index))) values = .clash
  | _, [], _, _, index, equation, at_ => by simp at at_
  | use, candidate :: rest, controls, selected, index, equation, at_ => by
      cases later : selections bindings values (use + 1) rest with
      | none => simp [selections, later] at selected
      | some others =>
          have inherited := selections_row bindings values (use + 1) rest others later
          cases matched : unifyArguments bindings
              (candidate.arguments.map (rename use)) values with
          | exhausted => simp [selections, later, matched] at selected
          | ok bound =>
              simp [selections, later, matched] at selected
              subst selected
              cases index with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at at_
                  subst at_
                  exact Or.inl ⟨bound, by simpa using matched, List.mem_cons_self ..⟩
              | succ next =>
                  simp only [List.getElem?_cons_succ] at at_
                  have shifted : use + (next + 1) = use + 1 + next := by omega
                  rw [shifted]
                  rcases inherited next equation at_ with ⟨found, unified, member⟩ | clashed
                  · exact Or.inl ⟨found, unified, List.mem_cons_of_mem _ member⟩
                  · exact Or.inr clashed
          | clash =>
              simp [selections, later, matched] at selected
              subst selected
              cases index with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at at_
                  subst at_
                  exact Or.inr (by simpa using matched)
              | succ next =>
                  simp only [List.getElem?_cons_succ] at at_
                  have shifted : use + (next + 1) = use + 1 + next := by omega
                  rw [shifted]
                  exact inherited next equation at_

/-- Every control of a completed selection is the body of a candidate under the unifier of
its argument patterns with the values. -/
theorem selections_sound (bindings : Subst) (values : List Atom) :
    ∀ (use : Nat) (equations : List Equation) (controls : List Control),
      selections bindings values use equations = some controls →
      ∀ control ∈ controls, ∃ (index : Nat) (equation : Equation) (bound : Subst),
        equations[index]? = some equation ∧
          unifyArguments bindings
            (equation.arguments.map (rename (use + index))) values = .ok bound ∧
          control = .evaluate bound (rename (use + index) equation.body)
  | _, [], controls, selected, control, member => by
      simp only [selections, Option.some.injEq] at selected
      subst selected
      cases member
  | use, candidate :: rest, controls, selected, control, member => by
      cases later : selections bindings values (use + 1) rest with
      | none => simp [selections, later] at selected
      | some others =>
          have inherited := selections_sound bindings values (use + 1) rest others later
          have fromRest : control ∈ others →
              ∃ (index : Nat) (equation : Equation) (bound : Subst),
                (candidate :: rest)[index]? = some equation ∧
                  unifyArguments bindings
                    (equation.arguments.map (rename (use + index))) values = .ok bound ∧
                  control = .evaluate bound (rename (use + index) equation.body) := by
            intro inOthers
            obtain ⟨index, equation, bound, at_, unified, same⟩ := inherited control inOthers
            have shifted : use + (index + 1) = use + 1 + index := by omega
            exact ⟨index + 1, equation, bound, by simpa using at_, by rw [shifted]; exact unified,
              by rw [shifted]; exact same⟩
          cases matched : unifyArguments bindings
              (candidate.arguments.map (rename use)) values with
          | exhausted => simp [selections, later, matched] at selected
          | ok bound =>
              simp [selections, later, matched] at selected
              subst selected
              rcases List.mem_cons.mp member with here | inOthers
              · exact ⟨0, candidate, bound, by simp, by simpa using matched, by simpa using here⟩
              · exact fromRest inOthers
          | clash =>
              simp [selections, later, matched] at selected
              subst selected
              exact fromRest member

/-- **A call selects exactly the admissible equations.** For a selection the machine
completed, with the caller's bindings in solved form and values with no unknowns: the
candidate at a position is selected exactly when it is admissible, and the bindings its
body goes on with mean the valuations that solve the caller's bindings and make each of its
argument patterns hold of its value. -/
theorem call_selects_exactly_the_admissible {bindings : Subst} {values : List Atom}
    (valid : Idempotent bindings) (ground : Ground (.expression values))
    {use : Nat} {equations : List Equation} {controls : List Control}
    (selected : selections bindings values use equations = some controls)
    {index : Nat} {equation : Equation} (at_ : equations[index]? = some equation) :
    (∃ bound, Control.evaluate bound (rename (use + index) equation.body) ∈ controls ∧
        unifyArguments bindings
          (equation.arguments.map (rename (use + index))) values = .ok bound ∧
        SolutionsOf EquationHolds (presentation bound) =
          SolutionsOf EquationHolds (presentation bindings) ∩
            {ρ | List.Forall₂ (PatternHolds ρ)
              (equation.arguments.map (rename (use + index))) values}) ↔
      Admissible bindings (equation.arguments.map (rename (use + index))) values := by
  constructor
  · rintro ⟨bound, _, unified, _⟩
    exact (unifyArguments_accepts_iff valid ground).mp ⟨bound, unified⟩
  · intro admissible
    obtain ⟨found, accepted⟩ := (unifyArguments_accepts_iff valid ground).mpr admissible
    rcases selections_row bindings values use equations controls selected index equation at_
      with ⟨bound, unified, member⟩ | clashed
    · exact ⟨bound, member, unified, unifyArguments_means valid ground unified⟩
    · rw [accepted] at clashed
      cases clashed

/-- A call goes on only with admissible equations: every control of a completed selection
is the body of a candidate that is admissible, under bindings that mean the valuations
making its patterns hold. -/
theorem call_goes_on_only_with_admissible_equations {bindings : Subst} {values : List Atom}
    (valid : Idempotent bindings) (ground : Ground (.expression values))
    {use : Nat} {equations : List Equation} {controls : List Control}
    (selected : selections bindings values use equations = some controls)
    {control : Control} (member : control ∈ controls) :
    ∃ (index : Nat) (equation : Equation) (bound : Subst),
      equations[index]? = some equation ∧
        control = .evaluate bound (rename (use + index) equation.body) ∧
        Admissible bindings (equation.arguments.map (rename (use + index))) values ∧
        SolutionsOf EquationHolds (presentation bound) =
          SolutionsOf EquationHolds (presentation bindings) ∩
            {ρ | List.Forall₂ (PatternHolds ρ)
              (equation.arguments.map (rename (use + index))) values} := by
  obtain ⟨index, equation, bound, at_, unified, same⟩ :=
    selections_sound bindings values use equations controls selected control member
  exact ⟨index, equation, bound, at_, same,
    (unifyArguments_accepts_iff valid ground).mp ⟨bound, unified⟩,
    unifyArguments_means valid ground unified⟩

/-! ## Controls -/

/-- The equation `(= (first-of (cons $h $t)) $h)`. -/
def firstOf : Equation :=
  ⟨"first-of", [.expression [.symbol "cons", .var "h", .var "t"]], .var "h"⟩

/-- Positive: the list `(p q)` selects the equation. -/
theorem a_list_selects_the_equation :
    (selections [] [.expression [.symbol "p", .symbol "q"]] 0 [firstOf]).map List.length =
      some 1 := by
  decide +kernel

/-- Negative: the symbol `foo` does not. -/
theorem a_symbol_selects_no_equation :
    (selections [] [.symbol "foo"] 0 [firstOf]).map List.length = some 0 := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.ListView
