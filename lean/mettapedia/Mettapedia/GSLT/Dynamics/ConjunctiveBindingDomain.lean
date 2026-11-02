import Mettapedia.GSLT.Dynamics.ConjunctiveBindingJoin

/-!
# Finite-domain and variable-coverage obligations for binding joins

Source-style binding does not invent values for unused variables. A complete
variable schedule is therefore justified only when every query variable is
already captured or occurs in a factor. The finite domain must also contain
captured values and every retained row coordinate. These are input properties,
not a test obtained by first enumerating the answers.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ConjunctiveBindingDomain

open ConjunctiveRegionProvenance GenericJoinRegions ConjunctiveRowMatching ConjunctiveBindingJoin

variable {n : Nat} {Value Id : Type} [DecidableEq Value]

def InDomain (domain : Finset Value) (environment : Environment n Value) : Prop :=
  ∀ name value, environment name = some value → value ∈ domain

def RowsInDomain (domain : Finset Value) (factors : List (Factor (Fin n) Value Id)) : Prop :=
  ∀ factor ∈ factors, ∀ row ∈ factor.rows, ∀ column, row.2 column ∈ domain

def Covered (before : Environment n Value) (factors : List (Factor (Fin n) Value Id)) : Prop :=
  ∀ name, (before name).isSome ∨ ∃ factor ∈ factors, ∃ column, factor.pattern column = .variable name

def inputDomain (before : Environment n Value) (factors : List (Factor (Fin n) Value Id)) : Finset Value :=
  ((List.finRange n).filterMap before ++
    factors.flatMap (fun factor => factor.rows.flatMap (fun row => List.ofFn row.2))).toFinset

theorem inputDomain_captures (before : Environment n Value) (factors : List (Factor (Fin n) Value Id)) :
    InDomain (inputDomain before factors) before := by
  intro name value found
  apply List.mem_toFinset.mpr
  apply List.mem_append_left
  exact List.mem_filterMap.mpr ⟨name, by simp, found⟩

theorem inputDomain_rows (before : Environment n Value) (factors : List (Factor (Fin n) Value Id)) :
    RowsInDomain (inputDomain before factors) factors := by
  intro factor present row stored column
  apply List.mem_toFinset.mpr
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨factor, present, List.mem_flatMap.mpr ⟨row, stored, List.mem_ofFn.mpr ⟨column, rfl⟩⟩⟩

def coveredCheck (before : Environment n Value) (factors : List (Factor (Fin n) Value Id)) : Bool :=
  (List.finRange n).all fun name => (before name).isSome || factors.any fun factor =>
    (List.ofFn factor.pattern).any (fun cell => decide (cell = .variable name))

theorem coveredCheck_iff (before : Environment n Value) (factors : List (Factor (Fin n) Value Id)) :
    coveredCheck before factors = true ↔ Covered before factors := by
  simp only [coveredCheck, Covered, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq, List.mem_ofFn]
  constructor
  · intro checked name
    rcases checked name with captured | ⟨factor, present, cell, ⟨column, equal⟩, named⟩
    · exact Or.inl captured
    · exact Or.inr ⟨factor, present, column, equal.trans named⟩
  · intro covered name
    rcases covered name with captured | ⟨factor, present, column, named⟩
    · exact Or.inl captured
    · exact Or.inr ⟨factor, present, factor.pattern column, ⟨column, rfl⟩, named⟩

theorem bindCell_domain (domain : Finset Value) {before after : Environment n Value}
    (initial : InDomain domain before) {cell : Cell (Fin n) Value} {value : Value}
    (inside : value ∈ domain) (matched : bindCell before cell value = some after) : InDomain domain after := by
  cases cell with
  | constant expected =>
      simp only [bindCell] at matched
      split at matched
      · cases matched; exact initial
      · cases matched
  | «variable» slot =>
      cases old : before slot with
      | none =>
          simp only [bindCell, old] at matched
          cases matched
          intro name actual found
          by_cases same : name = slot
          · subst name
            have equal : value = actual := by simpa using found
            exact equal ▸ inside
          · apply initial name actual
            simpa [Function.update_of_ne same] using found
      | some previous =>
          simp only [bindCell, old] at matched
          split at matched
          · cases matched; exact initial
          · cases matched

theorem bindValues_domain (domain : Finset Value) {before after : Environment n Value}
    (initial : InDomain domain before) {cells : List (Cell (Fin n) Value)} {values : List Value}
    (inside : ∀ value ∈ values, value ∈ domain) (matched : bindValues before cells values = some after) : InDomain domain after := by
  induction cells generalizing before values with
  | nil =>
      cases values with
      | nil => cases matched; exact initial
      | cons => cases matched
  | cons cell cells ih =>
      cases values with
      | nil => cases matched
      | cons value values =>
          obtain ⟨middle, first, later⟩ := Option.bind_eq_some_iff.mp matched
          exact ih (bindCell_domain domain initial (inside value (by simp)) first)
            (fun item member => inside item (List.mem_cons_of_mem _ member)) later

theorem bindFactor_domain (domain : Finset Value) {before after : Environment n Value}
    (initial : InDomain domain before) (factor : Factor (Fin n) Value Id) (row : Id × (Fin factor.arity → Value))
    (inside : ∀ column, row.2 column ∈ domain) (matched : bindFactor before factor row = some after) : InDomain domain after := by
  apply bindValues_domain domain initial _ matched
  intro value member
  obtain ⟨column, rfl⟩ := List.mem_ofFn.mp member
  exact inside column

theorem bindFactor_holds {before after : Environment n Value} (factor : Factor (Fin n) Value Id)
    (row : Id × (Fin factor.arity → Value)) (matched : bindFactor before factor row = some after) :
    ∀ column, holds after (factor.pattern column) (row.2 column) := by
  have all := (bindValues_sound matched).2
  intro column
  have selected := all.get (i := column.val) (by simpa only [List.length_ofFn] using column.isLt)
    (by simpa only [List.length_ofFn] using column.isLt)
  simpa only [List.get_ofFn, Fin.cast_mk, Fin.eta] using selected

theorem run_extends (before : Environment n Value) (factors : List (Factor (Fin n) Value Id))
    (answer : Environment n Value × List Id) (member : answer ∈ ConjunctiveBindingJoin.run before factors) :
    Extends before answer.1 := by
  induction factors generalizing before answer with
  | nil =>
      have same : answer = (before, []) := List.mem_singleton.mp member
      subst answer
      exact Extends.refl _
  | cons factor factors ih =>
      obtain ⟨row, _, choices⟩ := List.mem_flatMap.mp member
      obtain ⟨middle, matched, later⟩ := List.mem_flatMap.mp choices
      obtain ⟨result, inRest, rfl⟩ := List.mem_map.mp later
      exact (bindValues_sound (Option.mem_toList.mp matched)).1.trans (ih middle result inRest)

theorem run_domain (domain : Finset Value) (before : Environment n Value) (factors : List (Factor (Fin n) Value Id))
    (initial : InDomain domain before) (rows : RowsInDomain domain factors)
    (answer : Environment n Value × List Id) (member : answer ∈ ConjunctiveBindingJoin.run before factors) :
    InDomain domain answer.1 := by
  induction factors generalizing before answer with
  | nil =>
      have same : answer = (before, []) := List.mem_singleton.mp member
      subst answer
      exact initial
  | cons factor factors ih =>
      obtain ⟨row, stored, choices⟩ := List.mem_flatMap.mp member
      obtain ⟨middle, matched, later⟩ := List.mem_flatMap.mp choices
      obtain ⟨result, inRest, rfl⟩ := List.mem_map.mp later
      exact ih middle
        (bindFactor_domain domain initial factor row (rows factor (by simp) row stored) (Option.mem_toList.mp matched))
        (fun entry present => rows entry (List.mem_cons_of_mem _ present)) result inRest

theorem run_holds (before : Environment n Value) (factors : List (Factor (Fin n) Value Id))
    (answer : Environment n Value × List Id) (member : answer ∈ ConjunctiveBindingJoin.run before factors) :
    ∀ factor ∈ factors, ∃ row ∈ factor.rows, ∀ column, holds answer.1 (factor.pattern column) (row.2 column) := by
  induction factors generalizing before answer with
  | nil => simp
  | cons factor factors ih =>
      obtain ⟨row, stored, choices⟩ := List.mem_flatMap.mp member
      obtain ⟨middle, matched, later⟩ := List.mem_flatMap.mp choices
      obtain ⟨result, inRest, rfl⟩ := List.mem_map.mp later
      have atHead := bindFactor_holds factor row (Option.mem_toList.mp matched)
      have extension := run_extends middle factors result inRest
      intro target present
      rcases List.mem_cons.mp present with same | inTail
      · subst target
        exact ⟨row, stored, fun column => holds_extends extension _ _ (atHead column)⟩
      · exact ih middle result inRest target inTail

theorem covered_results_total (before : Environment n Value) (factors : List (Factor (Fin n) Value Id))
    (covered : Covered before factors) (answer : Environment n Value × List Id)
    (member : answer ∈ ConjunctiveBindingJoin.run before factors) : ∀ name, ∃ value, answer.1 name = some value := by
  intro name
  rcases covered name with captured | ⟨factor, present, column, named⟩
  · obtain ⟨value, found⟩ := Option.isSome_iff_exists.mp captured
    exact ⟨value, run_extends before factors answer member name value found⟩
  · obtain ⟨row, _, held⟩ := run_holds before factors answer member factor present
    refine ⟨row.2 column, ?_⟩
    simpa only [named, holds] using held column

omit [DecidableEq Value] in
theorem holds_compatible {before : Environment n Value} {cell : Cell (Fin n) Value} {value : Value}
    (held : holds before cell value) : compatible before cell value := by
  cases cell with
  | constant => exact held.symm
  | «variable» name =>
      change before name = some value at held
      simp [compatible, held]

theorem run_feasible (before : Environment n Value) (factors : List (Factor (Fin n) Value Id))
    (answer : Environment n Value × List Id) (member : answer ∈ ConjunctiveBindingJoin.run before factors) :
    feasible answer.1 factors := by
  intro factor present
  obtain ⟨row, stored, held⟩ := run_holds before factors answer member factor present
  exact ⟨row, stored, fun column => holds_compatible (held column)⟩

theorem source_binding_is_reference_key {OrderedValue : Type} [LinearOrder OrderedValue]
    (domain : Finset OrderedValue) (before : Environment n OrderedValue)
    (factors : List (Factor (Fin n) OrderedValue Id)) (initial : InDomain domain before)
    (rows : RowsInDomain domain factors) (covered : Covered before factors)
    (answer : Environment n OrderedValue × List Id) (member : answer ∈ ConjunctiveBindingJoin.run before factors) :
    answer.1 ∈ GenericJoinRegions.reference domain factors (List.finRange n) before := by
  apply reference_complete domain factors _ before answer.1 (run_extends before factors answer member)
    (run_feasible before factors answer member)
  · intro name _
    obtain ⟨value, found⟩ := covered_results_total before factors covered answer member name
    exact ⟨value, run_domain domain before factors initial rows answer member name value found, found⟩
  · intro name outside
    simp at outside

namespace Controls

theorem used_variable_is_covered :
    Covered (fun _ => none) [ConjunctiveBindingJoin.Controls.duplicate] := by
  intro name
  refine Or.inr ⟨ConjunctiveBindingJoin.Controls.duplicate, by simp, ⟨0, by decide⟩, ?_⟩
  change Cell.variable (0 : Fin 1) = Cell.variable name
  exact congrArg Cell.variable (Subsingleton.elim _ _)

theorem unused_unbound_variable_is_not_covered :
    ¬ Covered (Id := Nat) (fun (_ : Fin 1) => (none : Option Nat)) [] := by
  intro covered
  simpa using covered 0

theorem captured_value_requires_domain_membership :
    ¬ InDomain ({1, 2} : Finset Nat) (fun (_ : Fin 1) => some 7) := by
  intro inside
  simpa using inside 0 7 rfl

end Controls

end Mettapedia.GSLT.Dynamics.ConjunctiveBindingDomain
