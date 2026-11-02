import Mettapedia.GSLT.Dynamics.GenericJoinRegions

/-!
# Binding rows in the conjunctive-query IR

The matcher uses the existing cells and partial environments. A new variable
is bound once; every later occurrence tests that binding. Its soundness and
completion laws relate sequential row binding to satisfaction under a common
extension. This supplies the row-wise source bridge for variable-at-a-time
joins without treating repeated unbound coordinates as independent holes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ConjunctiveRowMatching

open ConjunctiveRegionProvenance GenericJoinRegions

variable {n : Nat} {Value : Type} [DecidableEq Value]

def holds (environment : Environment n Value) : Cell (Fin n) Value → Value → Prop
  | .constant expected, actual => expected = actual
  | .variable name, actual => environment name = some actual

omit [DecidableEq Value] in
theorem holds_extends {before after : Environment n Value} (extension : Extends before after)
    (cell : Cell (Fin n) Value) (value : Value) (held : holds before cell value) : holds after cell value := by
  cases cell with
  | constant => exact held
  | «variable» name => exact extension name value held

def bindCell (environment : Environment n Value) : Cell (Fin n) Value → Value → Option (Environment n Value)
  | .constant expected, actual => if expected = actual then some environment else none
  | .variable name, actual => match environment name with
      | none => some (Function.update environment name (some actual))
      | some expected => if expected = actual then some environment else none

theorem bindCell_sound {before after : Environment n Value} {cell : Cell (Fin n) Value} {value : Value}
    (bound : bindCell before cell value = some after) : Extends before after ∧ holds after cell value := by
  cases cell with
  | constant expected =>
      simp only [bindCell] at bound
      split at bound
      next equal => cases bound; exact ⟨Extends.refl _, equal⟩
      next => cases bound
  | «variable» name =>
      cases old : before name with
      | none =>
          simp only [bindCell, old] at bound
          cases bound
          constructor
          · intro other previous found
            by_cases same : other = name
            · subst other; rw [old] at found; cases found
            · simpa [Function.update_of_ne same] using found
          · simp [holds]
      | some previous =>
          simp only [bindCell, old] at bound
          split at bound
          next equal => cases bound; exact ⟨Extends.refl _, by simpa [holds, equal] using old⟩
          next => cases bound

theorem bindCell_complete {before target : Environment n Value} (extension : Extends before target)
    (cell : Cell (Fin n) Value) (value : Value) (held : holds target cell value) :
    ∃ after, bindCell before cell value = some after ∧ Extends after target := by
  cases cell with
  | constant expected => exact ⟨before, if_pos held, extension⟩
  | «variable» name =>
      cases old : before name with
      | none =>
          refine ⟨Function.update before name (some value), by simp [bindCell, old], ?_⟩
          intro other actual found
          by_cases same : other = name
          · subst other
            have equal : value = actual := by simpa using found
            simpa [holds, equal] using held
          · apply extension other actual
            simpa [Function.update_of_ne same] using found
      | some actual =>
          have equal : actual = value := Option.some.inj ((extension name actual old).symm.trans held)
          exact ⟨before, by simp [bindCell, old, equal], extension⟩

def bindValues (environment : Environment n Value) : List (Cell (Fin n) Value) → List Value → Option (Environment n Value)
  | [], [] => some environment
  | cell :: cells, value :: values => (bindCell environment cell value).bind fun next => bindValues next cells values
  | _, _ => none

theorem bindValues_sound {before after : Environment n Value} {cells : List (Cell (Fin n) Value)} {values : List Value}
    (bound : bindValues before cells values = some after) :
    Extends before after ∧ List.Forall₂ (holds after) cells values := by
  induction cells generalizing before values with
  | nil =>
      cases values with
      | nil => cases bound; exact ⟨Extends.refl _, .nil⟩
      | cons => cases bound
  | cons cell cells ih =>
      cases values with
      | nil => cases bound
      | cons value values =>
          obtain ⟨middle, first, later⟩ := Option.bind_eq_some_iff.mp bound
          obtain ⟨extendsFirst, holdsFirst⟩ := bindCell_sound first
          obtain ⟨extendsRest, holdsRest⟩ := ih later
          exact ⟨extendsFirst.trans extendsRest, .cons (holds_extends extendsRest cell value holdsFirst) holdsRest⟩

theorem bindValues_complete {before target : Environment n Value} (extension : Extends before target)
    {cells : List (Cell (Fin n) Value)} {values : List Value} (held : List.Forall₂ (holds target) cells values) :
    ∃ after, bindValues before cells values = some after ∧ Extends after target := by
  induction held generalizing before with
  | nil => exact ⟨before, rfl, extension⟩
  | @cons cell value cells values first later ih =>
      obtain ⟨middle, matched, grows⟩ := bindCell_complete extension cell value first
      obtain ⟨after, continued, extendsTarget⟩ := ih grows
      exact ⟨after, by simp only [bindValues, matched, Option.bind_some, continued], extendsTarget⟩

theorem bindValues_extension_iff (before target : Environment n Value)
    (cells : List (Cell (Fin n) Value)) (values : List Value) :
    (∃ after, bindValues before cells values = some after ∧ Extends after target) ↔
      Extends before target ∧ List.Forall₂ (holds target) cells values := by
  constructor
  · rintro ⟨after, matched, extendsTarget⟩
    obtain ⟨extension, matchedCells⟩ := bindValues_sound matched
    refine ⟨extension.trans extendsTarget, matchedCells.imp ?_⟩
    intro cell value held
    exact holds_extends extendsTarget cell value held
  · rintro ⟨extension, held⟩
    exact bindValues_complete extension held

theorem bindValues_full (assignment : Fin n → Value) (cells : List (Cell (Fin n) Value)) (values : List Value) :
    bindValues (fun name => some (assignment name)) cells values =
      if List.Forall₂ (fun cell value => cell.eval assignment = value) cells values then
        some (fun name => some (assignment name)) else none := by
  induction cells generalizing values with
  | nil => cases values <;> simp [bindValues]
  | cons cell cells ih =>
      cases values with
      | nil => simp [bindValues]
      | cons value values =>
          have one : bindCell (fun name => some (assignment name)) cell value =
              if cell.eval assignment = value then some (fun name => some (assignment name)) else none := by
            cases cell <;> rfl
          simp only [bindValues, one, List.forall₂_cons]
          by_cases equal : cell.eval assignment = value
          · simp only [equal, ↓reduceIte, Option.bind_some, true_and, ih]
          · simp [equal]

def bindFactor {Id : Type} (environment : Environment n Value) (factor : Factor (Fin n) Value Id)
    (row : Id × (Fin factor.arity → Value)) : Option (Environment n Value) :=
  bindValues environment (List.ofFn factor.pattern) (List.ofFn row.2)

theorem bindFactor_full {Id : Type} (assignment : Fin n → Value) (factor : Factor (Fin n) Value Id)
    (row : Id × (Fin factor.arity → Value)) :
    bindFactor (fun name => some (assignment name)) factor row =
      if factor.acceptsRow assignment row then some (fun name => some (assignment name)) else none := by
  have columns (arity : Nat) (pattern : Fin arity → Cell (Fin n) Value) (values : Fin arity → Value) :
      List.Forall₂ (fun cell value => cell.eval assignment = value) (List.ofFn pattern) (List.ofFn values) ↔
        ∀ i, (pattern i).eval assignment = values i := by
    induction arity with
    | zero => simp
    | succ arity ih => simp only [List.ofFn_succ, List.forall₂_cons, ih, Fin.forall_fin_succ]
  have agreed : List.Forall₂ (fun cell value => cell.eval assignment = value)
      (List.ofFn factor.pattern) (List.ofFn row.2) ↔
        ∀ i, row.2 i = (factor.pattern i).eval assignment :=
    (columns factor.arity factor.pattern row.2).trans (forall_congr' fun _ => eq_comm)
  simp only [bindFactor, bindValues_full, agreed, Factor.acceptsRow, decide_eq_true_eq]

namespace Controls

theorem repeated_unbound_variable_checks_its_first_value :
    bindValues (fun (_ : Fin 1) => none) [.variable 0, .variable 0] ([1, 2] : List Nat) = none := by decide +kernel

theorem repeated_equal_value_binds_once :
    (bindValues (fun (_ : Fin 1) => none) [.variable 0, .variable 0] ([1, 1] : List Nat)).map (fun env => env 0) =
      some (some 1) := by decide +kernel

theorem captured_value_is_not_overwritten :
    bindCell (fun (_ : Fin 1) => some 7) (.variable 0) (8 : Nat) = none := by decide +kernel

theorem different_variables_are_independent_slots :
    (bindValues (fun (_ : Fin 2) => none) [.variable 0, .variable 1] ([1, 2] : List Nat)).map
      (fun env => (env 0, env 1)) = some (some 1, some 2) := by decide +kernel

end Controls

end Mettapedia.GSLT.Dynamics.ConjunctiveRowMatching
