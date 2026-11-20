import Mettapedia.Languages.MeTTa.PeTTa.CellReadingIsTheReference

/-!
# The pattern unifier by cells, for every value

`PatternReadByCells` shows that the model's pattern unifier means the cell reading when
the value has no unknowns, and that it does not when the value is an unknown: there it
binds the unknown to the three-item expression `(cons first rest)`. Both hosts bind the
unknown to a cell instead, so that a second view of it gives the same parts and the list
closes when the parts become known.

This module gives the unifier that does that, and its laws for every value.

* **A pattern told of a value** is one equation (`patternEquation`): the pattern as read,
  with `(cons first rest)` a cell, equal to the value spelled cell by cell.
* **The unifier** (`patternReading`) is the model's own unifier on that equation. It is a
  lawful reading: the frame it reaches means exactly the valuations that solve what was
  told (`byCells_means`), and it accepts exactly when such a valuation exists
  (`byCells_accepts_iff`). No hypothesis on the value is left.
* **Unknowns range over cell terms.** A valuation here may give an unknown a cell whose
  rest is no list. On a value with no unknowns that freedom changes nothing: a pattern
  that some valuation satisfies is satisfied by a valuation of MeTTa's own terms
  (`ground_value_needs_no_improper_cell`).
* **On values with no unknowns the two unifiers agree**: one accepts when the other does
  (`byCells_accepts_iff_the_model_accepts`), and the model's bindings mean the valuations
  whose spelling the cell frame allows (`model_bindings_spell_the_cell_frame`).
* **A call's arguments** are told one after another (`tellArguments`); a candidate equation
  is selected exactly when a valuation solves the caller's frame and its argument patterns
  (`arguments_accept_iff`), for every value.

Controls, each measured on both hosts with `cons-atom`: an unknown becomes a cell; a list
opens; a cell whose rest is no list opens; a symbol and the empty list are refused; a
second view of an unknown gives the same parts; the list closes when its parts are known.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ListView

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst atomFreeVars)
open Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation
open Mettapedia.Languages.MeTTa.PeTTa.Unifying

/-! ## A lawful reading from any frame -/

/-- From any frame, a lawful reading accepts a list of facts exactly when some valuation
the frame allows solves them. -/
theorem Reading.tellAll_accepts_iff {Fact : Type} {Holds : Valuation → Fact → Prop}
    (R : Reading Holds) (frame : R.Frame) (told : List Fact) :
    (R.tellAll frame told).isSome ↔ (R.Denotes frame ∩ SolutionsOf Holds told).Nonempty := by
  constructor
  · intro accepted
    obtain ⟨next, reached⟩ := Option.isSome_iff_exists.mp accepted
    rw [← R.tellAll_some told frame next reached]
    exact R.frame_satisfiable next
  · intro satisfiable
    cases reached : R.tellAll frame told with
    | some next => rfl
    | none =>
        rw [R.tellAll_none told frame reached] at satisfiable
        exact absurd satisfiable Set.not_nonempty_empty

/-! ## A pattern told of a value -/

/-- A pattern told of a value: the pattern as read, equal to the value as spelled. -/
def patternEquation (told : Atom × Atom) : Atom × Atom := (readPattern told.1, spell told.2)

/-- The pattern holds of the value under a valuation of the unknowns by cell terms. -/
def CellPatternHolds (σ : Valuation) (told : Atom × Atom) : Prop :=
  EquationHolds σ (patternEquation told)

/-- The pattern unifier by cells: the model's unifier on the equation as spelled. -/
def patternReading : Reading CellPatternHolds := unifierReading.along patternEquation

/-- A pattern holding under a valuation of MeTTa's terms is the cell statement under the
spelling of that valuation. -/
theorem patternHolds_iff_cells (ρ : Valuation) (pattern value : Atom) :
    PatternHolds ρ pattern value ↔
      CellPatternHolds (fun name => spell (ρ name)) (pattern, value) :=
  Iff.rfl

/-- The frame the unifier reaches means the valuations its frame allowed that solve what
was told. Every value is covered. -/
theorem byCells_means {frame next : patternReading.Frame} {told : List (Atom × Atom)}
    (reached : patternReading.tellAll frame told = some next) :
    patternReading.Denotes next =
      patternReading.Denotes frame ∩ SolutionsOf CellPatternHolds told :=
  patternReading.tellAll_some told frame next reached

/-- The unifier accepts exactly when some valuation its frame allows solves what is told.
Every value is covered. -/
theorem byCells_accepts_iff (frame : patternReading.Frame) (told : List (Atom × Atom)) :
    (patternReading.tellAll frame told).isSome ↔
      (patternReading.Denotes frame ∩ SolutionsOf CellPatternHolds told).Nonempty :=
  patternReading.tellAll_accepts_iff frame told

/-! ## A value with no unknowns needs no improper cell -/

/-- A value with no unknowns, spelled, is its own instance. -/
theorem instantiate_spell_of_ground (σ : Valuation) :
    ∀ value : Atom, Ground value → instantiate σ (spell value) = spell value
  | .var name, ground => absurd ground (not_ground_var name)
  | .symbol name, _ => by simp
  | .grounded held, _ => by simp [spell, instantiate]
  | .expression [], _ => by simp
  | .expression (first :: rest), ground => by
      have parts := ground_head_tail ground
      have one := instantiate_spell_of_ground σ first parts.1
      have others := instantiate_spell_of_ground σ (.expression rest) parts.2
      have markStays : instantiate σ mark = mark := by simp [mark]
      rw [spell_expression] at others
      rw [spell_expression, spellItems_cons, instantiate_expression, instantiateList_cons,
        instantiateList_cons, instantiateList_cons, instantiateList_nil, markStays, one, others]
termination_by value => sizeOf value
decreasing_by
  all_goals first
    | (simp_wf; done)
    | (simp_wf; omega)

/-- A term kept when it spells a term of MeTTa, and the empty list otherwise. -/
noncomputable def mend (term : Atom) : Atom :=
  open Classical in if ∃ source, spell source = term then term else .expression []

theorem mend_spell (source : Atom) : mend (spell source) = spell source := by
  unfold mend
  exact if_pos ⟨source, rfl⟩

theorem mend_is_a_spelling (term : Atom) : ∃ source, spell source = mend term := by
  unfold mend
  by_cases spelled : ∃ source, spell source = term
  · rw [if_pos spelled]
    exact spelled
  · rw [if_neg spelled]
    exact ⟨.expression [], by simp⟩

/-- A spelled value that is a cell is a list with a first item. -/
theorem cell_of_spell {value first rest : Atom}
    (same : .expression [mark, first, rest] = spell value) :
    ∃ head tail, value = .expression (head :: tail) ∧ spell head = first ∧
      spell (.expression tail) = rest := by
  cases value with
  | var name => simp at same
  | symbol name => simp at same
  | grounded held => simp [spell] at same
  | expression items =>
      cases items with
      | nil => simp at same
      | cons head tail =>
          rw [spell_expression, spellItems_cons] at same
          injection same with same
          injection same with _ same
          injection same with one same
          injection same with others _
          exact ⟨head, tail, rfl, one.symm, by rw [spell_expression]; exact others.symm⟩

/-- An instance of a cell that spells a value: the parts spell the value's parts. -/
theorem cell_instance {σ : Valuation} {first rest value : Atom}
    (holds : instantiate σ (.expression [mark, first, rest]) = spell value) :
    ∃ head tail, value = .expression (head :: tail) ∧ instantiate σ first = spell head ∧
      instantiate σ rest = spell (.expression tail) := by
  have markStays : instantiate σ mark = mark := by simp [mark]
  rw [instantiate_expression, instantiateList_cons, instantiateList_cons, instantiateList_cons,
    instantiateList_nil, markStays] at holds
  obtain ⟨head, tail, shape, one, others⟩ := cell_of_spell holds
  exact ⟨head, tail, shape, one.symm, others.symm⟩

/-- A cell whose parts instantiate to the spellings of a list's parts instantiates to the
spelling of the list. -/
theorem cell_instance_of_parts {σ : Valuation} {first rest head : Atom} {tail : List Atom}
    (one : instantiate σ first = spell head)
    (others : instantiate σ rest = spell (.expression tail)) :
    instantiate σ (.expression [mark, first, rest]) = spell (.expression (head :: tail)) := by
  have markStays : instantiate σ mark = mark := by simp [mark]
  rw [spell_expression] at others
  rw [instantiate_expression, instantiateList_cons, instantiateList_cons, instantiateList_cons,
    instantiateList_nil, markStays, one, others, spell_expression, spellItems_cons]

/-- A pattern whose instance is the spelling of a value keeps that instance when each
unknown's value is mended. -/
theorem mended_solves (σ : Valuation) :
    ∀ (pattern value : Atom), instantiate σ (readPattern pattern) = spell value →
      instantiate (fun name => mend (σ name)) (readPattern pattern) = spell value
  | .var name, value, holds => by
      rw [readPattern_var, instantiate_var] at holds ⊢
      rw [holds, mend_spell]
  | .symbol name, value, holds => by simpa using holds
  | .grounded held, value, holds => by simpa [readPattern, instantiate] using holds
  | .expression items, value, holds => by
      rcases view_or_not items with ⟨first, rest, shape⟩ | notView
      · rw [shape, readPattern_view] at holds ⊢
        obtain ⟨head, tail, isList, one, others⟩ := cell_instance holds
        have oneMended := mended_solves σ first head one
        have othersMended := mended_solves σ rest (.expression tail) others
        rw [isList]
        exact cell_instance_of_parts oneMended othersMended
      · have each : ∀ item ∈ items, ∀ part : Atom,
            instantiate σ (readPattern item) = spell part →
              instantiate (fun name => mend (σ name)) (readPattern item) = spell part :=
          fun item member part same => mended_solves σ item part same
        rw [readPattern_list notView] at holds ⊢
        clear notView
        induction items generalizing value with
        | nil => simpa using holds
        | cons head tail ih =>
            rw [readEach_cons] at holds ⊢
            obtain ⟨part, parts, isList, one, others⟩ := cell_instance holds
            rw [isList]
            exact cell_instance_of_parts (each head List.mem_cons_self part one)
              (ih (.expression parts) others
                fun item member => each item (List.mem_cons_of_mem _ member))
termination_by pattern => sizeOf pattern
decreasing_by
  all_goals first
    | (simp_wf; subst shape; simp; omega)
    | (simp_wf; have smaller := List.sizeOf_lt_of_mem member; omega)

/-- On a value with no unknowns, a pattern that some valuation by cell terms satisfies is
satisfied by a valuation of MeTTa's own terms: a cell whose rest is no list is never
needed. -/
theorem ground_value_needs_no_improper_cell {σ : Valuation} {pattern value : Atom}
    (ground : Ground value) (holds : CellPatternHolds σ (pattern, value)) :
    ∃ ρ : Valuation, PatternHolds ρ pattern value := by
  have asSpelled : instantiate σ (readPattern pattern) = spell value := by
    have same : instantiate σ (readPattern pattern) = instantiate σ (spell value) := holds
    rw [same, instantiate_spell_of_ground σ value ground]
  have mended := mended_solves σ pattern value asSpelled
  choose source spells using fun name => mend_is_a_spelling (σ name)
  refine ⟨source, ?_⟩
  have sameValuation : (fun name => spell (source name)) = fun name => mend (σ name) :=
    funext spells
  show instantiate (fun name => spell (source name)) (readPattern pattern) =
    instantiate (fun name => spell (source name)) (spell value)
  rw [sameValuation, mended, instantiate_spell_of_ground _ value ground]

/-! ## Agreement with the model's pattern unifier on values with no unknowns -/

theorem presentation_nil_solutions :
    SolutionsOf EquationHolds (presentation ([] : Subst)) = Set.univ := by
  simp [presentation, solutionsOf_nil]

/-- With nothing bound yet and a value with no unknowns, the unifier by cells accepts a
pattern exactly when the model's pattern unifier does. -/
theorem byCells_accepts_iff_the_model_accepts {pattern value : Atom} (ground : Ground value) :
    (patternReading.tellAll patternReading.empty [(pattern, value)]).isSome ↔
      ∃ bound, unifyAsPattern [] pattern value = .ok bound := by
  rw [patternReading.accepts_iff_satisfiable,
    unifyAsPattern_accepts_iff idempotent_nil ground, presentation_nil_solutions,
    Set.univ_inter]
  constructor
  · rintro ⟨σ, holds⟩
    have one : CellPatternHolds σ (pattern, value) := holds (pattern, value) (by simp)
    obtain ⟨ρ, holdsOfTerms⟩ := ground_value_needs_no_improper_cell ground one
    exact ⟨ρ, holdsOfTerms⟩
  · rintro ⟨ρ, holds⟩
    refine ⟨fun name => spell (ρ name), ?_⟩
    intro told member
    simp only [List.mem_singleton] at member
    subst member
    exact holds

/-- With nothing bound yet and a value with no unknowns, the model's bindings mean the
valuations of MeTTa's terms whose spelling the cell frame allows. -/
theorem model_bindings_spell_the_cell_frame {pattern value : Atom} {bound : Subst}
    {next : patternReading.Frame} (ground : Ground value)
    (unified : unifyAsPattern [] pattern value = .ok bound)
    (reached : patternReading.tellAll patternReading.empty [(pattern, value)] = some next)
    (ρ : Valuation) :
    ρ ∈ SolutionsOf EquationHolds (presentation bound) ↔
      (fun name => spell (ρ name)) ∈ patternReading.Denotes next := by
  rw [unifyAsPattern_means idempotent_nil ground unified, presentation_nil_solutions,
    Set.univ_inter, patternReading.denotes_the_solutions reached]
  constructor
  · intro holds told member
    simp only [List.mem_singleton] at member
    subst member
    exact holds
  · intro holds
    exact holds (pattern, value) (by simp)

/-! ## The arguments of a call -/

/-- A call's values told of a candidate equation's argument patterns, one after another;
refused when there are not as many patterns as values. -/
def tellArguments (frame : patternReading.Frame) (patterns values : List Atom) :
    Option patternReading.Frame :=
  if patterns.length = values.length then
    patternReading.tellAll frame (patterns.zip values)
  else none

/-- The candidate is selected exactly when there are as many patterns as values and some
valuation the caller's frame allows makes each pattern hold of its value. Every value is
covered. -/
theorem arguments_accept_iff (frame : patternReading.Frame) (patterns values : List Atom) :
    (tellArguments frame patterns values).isSome ↔
      patterns.length = values.length ∧
        (patternReading.Denotes frame ∩
          SolutionsOf CellPatternHolds (patterns.zip values)).Nonempty := by
  unfold tellArguments
  by_cases same : patterns.length = values.length
  · rw [if_pos same, byCells_accepts_iff]
    exact ⟨fun solvable => ⟨same, solvable⟩, fun both => both.2⟩
  · rw [if_neg same]
    simp [same]

/-- The frame a selected candidate's body goes on with means the valuations the caller's
frame allowed that make each pattern hold of its value. -/
theorem arguments_mean {frame next : patternReading.Frame} {patterns values : List Atom}
    (selected : tellArguments frame patterns values = some next) :
    patternReading.Denotes next =
      patternReading.Denotes frame ∩ SolutionsOf CellPatternHolds (patterns.zip values) := by
  unfold tellArguments at selected
  by_cases same : patterns.length = values.length
  · rw [if_pos same] at selected
    exact byCells_means selected
  · rw [if_neg same] at selected
    cases selected

/-! ## Controls, each measured on both hosts -/

/-- Telling patterns of values is telling the unifier their equations. -/
theorem tellAll_along (told : List (Atom × Atom)) :
    ∀ frame : patternReading.Frame,
      patternReading.tellAll frame told =
        unifierReading.tellAll frame (told.map patternEquation) := by
  induction told with
  | nil => intro frame; rfl
  | cons first rest ih =>
      intro frame
      show (unifierReading.tell frame (patternEquation first)).bind
          (fun next => patternReading.tellAll next rest) = _
      simp only [List.map_cons, Reading.tellAll]
      congr 1
      funext next
      exact ih next

/-- The bindings a list of equations reaches, when the unifier accepts it. -/
def reachedOf (equations : List (Atom × Atom)) : Option Subst :=
  (unifierReading.tellAll unifierReading.empty equations).map (·.1)

/-- The bindings a list of told patterns reaches, when it is accepted. -/
def reached (told : List (Atom × Atom)) : Option Subst :=
  (patternReading.tellAll patternReading.empty told).map (·.1)

theorem reached_eq (told : List (Atom × Atom)) :
    reached told = reachedOf (told.map patternEquation) := by
  unfold reached reachedOf
  rw [tellAll_along]
  rfl

/-- The view `(cons $h $t)`. -/
def viewOf (first rest : String) : Atom :=
  .expression [.symbol "cons", .var first, .var rest]

/-- Positive: the view of an unknown binds the unknown to a cell. -/
theorem an_unknown_becomes_a_cell :
    reached [(viewOf "h" "t", .var "l")] =
      some [("l", .expression [mark, .var "h", .var "t"])] := by
  rw [reached_eq]
  simp only [List.map_cons, List.map_nil, patternEquation, viewOf, readPattern_view,
    readPattern_var, spell_var]
  decide +kernel

/-- Positive: the view opens a list. -/
theorem a_list_opens :
    (reached [(viewOf "h" "t", .expression [.symbol "p", .symbol "q", .symbol "r"])]).map
        (fun bindings => (resolve bindings (.var "h"), resolve bindings (.var "t"))) =
      some (.symbol "p", spell (.expression [.symbol "q", .symbol "r"])) := by
  rw [reached_eq]
  simp only [List.map_cons, List.map_nil, patternEquation, viewOf, readPattern_view,
    readPattern_var]
  decide +kernel

/-- Positive: a cell whose rest is no list opens into its two parts. -/
theorem a_cell_with_any_rest_opens :
    (reached [(.expression [.symbol "cons", .symbol "p", .symbol "q"], .var "v"),
        (viewOf "h" "t", .var "v")]).map
        (fun bindings => (resolve bindings (.var "h"), resolve bindings (.var "t"))) =
      some (.symbol "p", .symbol "q") := by
  rw [reached_eq]
  simp only [List.map_cons, List.map_nil, patternEquation, viewOf, readPattern_view,
    readPattern_var, readPattern_symbol, spell_var]
  decide +kernel

/-- Negative: a symbol has no view. -/
theorem a_symbol_is_refused : reached [(viewOf "h" "t", .symbol "foo")] = none := by
  rw [reached_eq]
  simp only [List.map_cons, List.map_nil, patternEquation, viewOf, readPattern_view,
    readPattern_var]
  decide +kernel

/-- Negative: the empty list has no view. -/
theorem the_empty_list_is_refused : reached [(viewOf "h" "t", .expression [])] = none := by
  rw [reached_eq]
  simp only [List.map_cons, List.map_nil, patternEquation, viewOf, readPattern_view,
    readPattern_var]
  decide +kernel

/-- Positive: a second view of an unknown gives the same parts. -/
theorem a_second_view_gives_the_same_parts :
    (reached [(viewOf "h" "t", .var "l"), (viewOf "a" "b", .var "l")]).map
        (fun bindings => (resolve bindings (.var "a"), resolve bindings (.var "b"))) =
      some (.var "h", .var "t") := by
  rw [reached_eq]
  simp only [List.map_cons, List.map_nil, patternEquation, viewOf, readPattern_view,
    readPattern_var, spell_var]
  decide +kernel

/-- Positive: the list closes when its parts are known. -/
theorem the_list_closes_when_its_parts_are_known :
    (reached [(viewOf "h" "t", .var "l"), (.var "h", .symbol "p"),
        (.var "t", .expression [.symbol "q", .symbol "r"])]).map
        (fun bindings => resolve bindings (.var "l")) =
      some (spell (.expression [.symbol "p", .symbol "q", .symbol "r"])) := by
  rw [reached_eq]
  simp only [List.map_cons, List.map_nil, patternEquation, viewOf, readPattern_view,
    readPattern_var, spell_var]
  decide +kernel

/-- Negative: two views of one unknown with different first items are refused. -/
theorem two_views_with_different_first_items_are_refused :
    reached [(.expression [.symbol "cons", .symbol "p", .var "t"], .var "l"),
        (.expression [.symbol "cons", .symbol "q", .var "u"], .var "l")] = none := by
  rw [reached_eq]
  simp only [List.map_cons, List.map_nil, patternEquation, readPattern_view,
    readPattern_var, readPattern_symbol, spell_var]
  decide +kernel

/-- Positive: a call's two arguments, the first an unknown. -/
theorem arguments_with_an_unknown_are_accepted :
    (tellArguments patternReading.empty [viewOf "h" "t", .var "y"]
        [.var "l", .symbol "p"]).isSome = true := by
  unfold tellArguments
  rw [if_pos (by decide), tellAll_along]
  simp only [List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil,
    patternEquation, viewOf, readPattern_view, readPattern_var, spell_var]
  decide +kernel

/-- Negative: two patterns do not meet one value. -/
theorem arguments_of_another_number_are_refused :
    (tellArguments patternReading.empty [viewOf "h" "t", .var "y"] [.var "l"]).isSome = false := by
  unfold tellArguments
  rw [if_neg (by decide)]
  rfl

end Mettapedia.Languages.MeTTa.PeTTa.ListView
