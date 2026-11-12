import Mettapedia.Languages.MeTTa.PeTTa.UnifierReadsEquations

/-!
# A list view is an equation once every list is spelled cell by cell

`ListViewMeaning` states what a list view means and what a lawful reading is.
`UnifierReadsEquations` shows the model's unifier is a lawful reading of equations. This
module constructs lawful readings of views and equations together, from that unifier.

* **Spelling.** `spell` writes every list cell by cell: the empty list stays `()`, and a
  list with first item `a` and others `l` becomes the three-item expression of a mark,
  `a` spelled, and `l` spelled. The mark is `(())`, an expression no spelled term equals,
  so no unknown can stand for it (`spell_ne_mark`). Spelling loses nothing
  (`spell_injective`) and commutes with giving unknowns their values (`spell_instantiate`).
* **A view is an equation.** Under spelling, "`list` is a list with first item `first` and
  others `rest`" is the equation `list = (mark first rest)`, and an equation between terms
  is the equation between their spellings (`told_holds_iff_spelled`). No fact about `rest`
  being a list has to be kept: the equation implies it.
* **Which solutions are lists.** The unifier solves the spelled equations over all values,
  and some of those are not the spelling of anything: a cell whose rest is a symbol, the
  improper list. A term is `Spelled` when it is the spelling of a term
  (`spelled_iff_spelling`).
* **Two readings, one check apart.**
  - `cellReading`: the unifier on the spelled facts, with every value allowed. It is lawful
    for the meaning in which a cell is a value whatever its rest is. This is the reading by
    terms with cells.
  - `listReading`: the same, and a frame is kept only if it `closes`: with every unknown
    still free taken as the empty list, each bound value is spelled. It is lawful for the
    meaning of `ListViewMeaning`, in which the values are MeTTa's terms
    (`lists_accept_iff_solvable`).
* **The difference between them is exactly the improper list.** Whatever the list reading
  accepts, the cell reading accepts (`cells_accept_what_lists_accept`). The facts "`x` is a
  list with first item `a` and others `b`" and "`b` is the symbol `foo`" are accepted by the
  cell reading and refused by the list reading (`cells_accept_an_improper_list`,
  `lists_refuse_an_improper_list`); among MeTTa's terms they have no solution
  (`improper_list_has_no_solution`).

* **The spelling is needed.** Between terms as they are written, where an expression has
  a known number of items, no list of equations says what a view says
  (`view_is_not_a_list_of_equations`).

Controls of the list reading. Accepted: a view of an unknown; two views of one unknown; a
view and then the list; data headed by the symbol `cons`, whose first item is then `cons`.
Refused: a view of a symbol; a view of the empty list; a list that is its own rest; two
views of one unknown with different first items; an improper list.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ListView

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation
  (environment presentation read_environment environment_models_presentation)
open Mettapedia.Languages.MeTTa.PeTTa.Unifying (Idempotent resolve)

/-! ## A reading of facts given as other facts -/

/-- A reading of facts, used for facts of another kind that are translated to them. -/
def Reading.along {Fact Source : Type} {Holds : Valuation → Fact → Prop} (R : Reading Holds)
    (translate : Source → Fact) : Reading (fun ρ source => Holds ρ (translate source)) where
  Frame := R.Frame
  empty := R.empty
  Denotes := R.Denotes
  tell frame source := R.tell frame (translate source)
  empty_denotes := R.empty_denotes
  frame_satisfiable := R.frame_satisfiable
  told := fun told => R.told told
  refused := fun refused => R.refused refused

/-! ## Spelling a list cell by cell -/

/-- The mark at the head of a cell: `(())`. -/
def mark : Atom := .expression [.expression []]

/-- A term with every list spelled cell by cell. -/
def spell : Atom → Atom
  | .var name => .var name
  | .symbol name => .symbol name
  | .grounded value => .grounded value
  | .expression items => spellItems items
where
  /-- The list of these items, spelled. -/
  spellItems : List Atom → Atom
    | [] => .expression []
    | first :: rest => .expression [mark, spell first, spellItems rest]

@[simp] theorem spell_var (name : String) : spell (.var name) = .var name := by
  simp [spell]

@[simp] theorem spell_symbol (name : String) : spell (.symbol name) = .symbol name := by
  simp [spell]

@[simp] theorem spell_expression (items : List Atom) :
    spell (.expression items) = spell.spellItems items := by
  simp [spell]

@[simp] theorem spellItems_nil : spell.spellItems [] = .expression [] := by
  simp [spell.spellItems]

@[simp] theorem spellItems_cons (first : Atom) (rest : List Atom) :
    spell.spellItems (first :: rest) =
      .expression [mark, spell first, spell.spellItems rest] := by
  simp [spell.spellItems]

/-- A term that is the spelling of a term. -/
inductive Spelled : Atom → Prop where
  | var (name : String) : Spelled (.var name)
  | symbol (name : String) : Spelled (.symbol name)
  | grounded (value : _) : Spelled (.grounded value)
  | nil : Spelled (.expression [])
  | cell {first : Atom} {rest : List Atom} :
      Spelled first → Spelled (.expression rest) →
        Spelled (.expression [mark, first, .expression rest])

/-- The spelling of a list is an expression. -/
theorem spellItems_is_expression (items : List Atom) :
    ∃ cells, spell.spellItems items = .expression cells := by
  cases items with
  | nil => exact ⟨[], spellItems_nil⟩
  | cons first rest => exact ⟨_, spellItems_cons first rest⟩

theorem spelled_spell : ∀ term : Atom, Spelled (spell term)
  | .var name => by simpa using Spelled.var name
  | .symbol name => by simpa using Spelled.symbol name
  | .grounded value => by simpa [spell] using Spelled.grounded value
  | .expression items => by
      rw [spell_expression]
      exact spelled_spellItems items
where
  /-- The same for a list. -/
  spelled_spellItems : ∀ items : List Atom, Spelled (spell.spellItems items)
    | [] => by simpa using Spelled.nil
    | first :: rest => by
        obtain ⟨cells, shape⟩ := spellItems_is_expression rest
        have others := spelled_spellItems rest
        rw [spellItems_cons, shape]
        rw [shape] at others
        exact Spelled.cell (spelled_spell first) others

/-- A spelled term is the spelling of a term. -/
theorem spelling_of_spelled {term : Atom} (spelled : Spelled term) :
    ∃ source, spell source = term := by
  induction spelled with
  | var name => exact ⟨.var name, spell_var name⟩
  | symbol name => exact ⟨.symbol name, spell_symbol name⟩
  | grounded value => exact ⟨.grounded value, by simp [spell]⟩
  | nil => exact ⟨.expression [], by simp⟩
  | @cell first rest _ _ firstSource restSource =>
      obtain ⟨head, headIs⟩ := firstSource
      obtain ⟨tail, tailIs⟩ := restSource
      cases tail with
      | var name => simp at tailIs
      | symbol name => simp at tailIs
      | grounded value => simp [spell] at tailIs
      | expression items =>
          refine ⟨.expression (head :: items), ?_⟩
          rw [spell_expression] at tailIs
          rw [spell_expression, spellItems_cons, headIs, tailIs]

theorem spelled_iff_spelling (term : Atom) : Spelled term ↔ ∃ source, spell source = term :=
  ⟨spelling_of_spelled, fun ⟨source, same⟩ => same ▸ spelled_spell source⟩

/-- What a spelled expression is: the empty list, or a cell of a spelled first item and a
spelled list. -/
theorem spelled_expression {items : List Atom} (spelled : Spelled (.expression items)) :
    items = [] ∨ ∃ first rest, items = [mark, first, .expression rest] ∧ Spelled first ∧
      Spelled (.expression rest) := by
  cases spelled with
  | nil => exact .inl rfl
  | cell spelledFirst spelledRest => exact .inr ⟨_, _, rfl, spelledFirst, spelledRest⟩

/-- No spelled term is the mark. -/
theorem spelled_ne_mark {term : Atom} (spelled : Spelled term) : term ≠ mark := by
  intro same
  rw [same, mark] at spelled
  rcases spelled_expression spelled with empty | ⟨first, rest, shape, _, _⟩
  · simp at empty
  · simp at shape

theorem spell_ne_mark (term : Atom) : spell term ≠ mark :=
  spelled_ne_mark (spelled_spell term)

/-- Spelling loses nothing. -/
theorem spell_injective : ∀ left right : Atom, spell left = spell right → left = right
  | .var name, right, same => by
      cases right with
      | var other => simpa using same
      | symbol other => simp at same
      | grounded value => simp [spell] at same
      | expression items =>
          obtain ⟨cells, shape⟩ := spellItems_is_expression items
          simp [shape] at same
  | .symbol name, right, same => by
      cases right with
      | var other => simp at same
      | symbol other => simpa using same
      | grounded value => simp [spell] at same
      | expression items =>
          obtain ⟨cells, shape⟩ := spellItems_is_expression items
          simp [shape] at same
  | .grounded value, right, same => by
      cases right with
      | var other => simp [spell] at same
      | symbol other => simp [spell] at same
      | grounded other => simpa [spell] using same
      | expression items =>
          obtain ⟨cells, shape⟩ := spellItems_is_expression items
          simp [spell, shape] at same
  | .expression items, right, same => by
      cases right with
      | var other =>
          obtain ⟨cells, shape⟩ := spellItems_is_expression items
          simp [shape] at same
      | symbol other =>
          obtain ⟨cells, shape⟩ := spellItems_is_expression items
          simp [shape] at same
      | grounded value =>
          obtain ⟨cells, shape⟩ := spellItems_is_expression items
          simp [spell, shape] at same
      | expression others =>
          rw [spell_expression, spell_expression] at same
          rw [spellItems_injective items others same]
where
  /-- The same for a list. -/
  spellItems_injective :
      ∀ left right : List Atom, spell.spellItems left = spell.spellItems right → left = right
    | [], right, same => by
        cases right with
        | nil => rfl
        | cons first rest => simp at same
    | first :: rest, right, same => by
        cases right with
        | nil => simp at same
        | cons other others =>
            simp only [spellItems_cons, Atom.expression.injEq, List.cons.injEq, true_and,
              and_true] at same
            rw [spell_injective first other same.1, spellItems_injective rest others same.2]

/-- Spelling commutes with giving the unknowns their values. -/
theorem spell_instantiate (ρ : Valuation) :
    ∀ term : Atom,
      spell (instantiate ρ term) = instantiate (fun name => spell (ρ name)) (spell term)
  | .var name => by simp
  | .symbol name => by simp
  | .grounded value => by simp [instantiate, spell]
  | .expression items => by
      rw [instantiate_expression, spell_expression, spell_expression,
        spellItems_instantiate ρ items]
where
  /-- The same for a list. -/
  spellItems_instantiate (ρ : Valuation) :
      ∀ items : List Atom,
        spell.spellItems (instantiate.instantiateList ρ items) =
          instantiate (fun name => spell (ρ name)) (spell.spellItems items)
    | [] => by simp
    | first :: rest => by
        rw [instantiateList_cons, spellItems_cons, spellItems_cons, spell_instantiate ρ first,
          spellItems_instantiate ρ rest]
        simp [mark]

/-! ## A told fact is an equation between spelled terms -/

/-- The equation a told fact is, once lists are spelled. -/
def spellFact : Told → Atom × Atom
  | .view list first rest => (.var list, .expression [mark, .var first, .var rest])
  | .equal left right => (spell left, spell right)

/-- A told fact holds under a valuation exactly when its equation holds under the spelled
valuation. -/
theorem told_holds_iff_spelled (ρ : Valuation) (fact : Told) :
    fact.Holds ρ ↔ EquationHolds (fun name => spell (ρ name)) (spellFact fact) := by
  cases fact with
  | equal left right =>
      show instantiate ρ left = instantiate ρ right ↔
        instantiate _ (spell left) = instantiate _ (spell right)
      rw [← spell_instantiate, ← spell_instantiate]
      exact ⟨fun same => by rw [same], spell_injective _ _⟩
  | view list first rest =>
      show (∃ items, ρ rest = .expression items ∧ ρ list = .expression (ρ first :: items)) ↔
        instantiate _ (.var list) = instantiate _ (.expression [mark, .var first, .var rest])
      simp only [instantiate_var, instantiate_expression, instantiateList_cons,
        instantiateList_nil]
      have markStays : instantiate (fun name => spell (ρ name)) mark = mark := by simp [mark]
      rw [markStays]
      constructor
      · rintro ⟨items, restIs, listIs⟩
        rw [listIs, restIs, spell_expression, spell_expression, spellItems_cons]
      · intro same
        cases listIs : ρ list with
        | var name => simp [listIs] at same
        | symbol name => simp [listIs] at same
        | grounded value => simp [listIs, spell] at same
        | expression items =>
            cases items with
            | nil => simp [listIs] at same
            | cons head tail =>
                rw [listIs, spell_expression, spellItems_cons] at same
                simp only [Atom.expression.injEq, List.cons.injEq, true_and, and_true] at same
                refine ⟨tail, ?_, ?_⟩
                · exact (spell_injective _ _ (by rw [spell_expression]; exact same.2)).symm
                · rw [spell_injective _ _ same.1]

/-! ## The reading by terms with cells -/

/-- A told fact in the meaning where a cell is a value whatever its rest is. -/
def CellHolds (σ : Valuation) (fact : Told) : Prop := EquationHolds σ (spellFact fact)

/-- The unifier on the spelled facts, every value allowed. It is lawful for `CellHolds`. -/
def cellReading : Reading CellHolds := unifierReading.along spellFact

theorem cells_accept_iff_solvable (told : List Told) :
    (cellReading.tellAll cellReading.empty told).isSome ↔
      (SolutionsOf CellHolds told).Nonempty :=
  cellReading.accepts_iff_satisfiable told

/-! ## Which frames have a solution among MeTTa's terms -/

/-- Every unknown taken as the empty list. -/
def allNil : Valuation := fun _ => .expression []

/-- Giving the unknowns values, and then the unknowns of those values, is giving the
composed values. -/
theorem instantiate_instantiate (τ σ : Valuation) :
    ∀ term : Atom,
      instantiate τ (instantiate σ term) = instantiate (fun name => instantiate τ (σ name)) term
  | .var name => by simp
  | .symbol name => by simp
  | .grounded value => by simp [instantiate]
  | .expression items => by
      rw [instantiate_expression, instantiate_expression, instantiate_expression,
        instantiateList_instantiateList τ σ items]
where
  /-- The same for a list. -/
  instantiateList_instantiateList (τ σ : Valuation) :
      ∀ items : List Atom,
        instantiate.instantiateList τ (instantiate.instantiateList σ items) =
          instantiate.instantiateList (fun name => instantiate τ (σ name)) items
    | [] => by simp
    | first :: rest => by
        rw [instantiateList_cons, instantiateList_cons, instantiateList_cons,
          instantiate_instantiate τ σ first, instantiateList_instantiateList τ σ rest]

/-- A solution stays a solution when its values' own unknowns are given values. -/
theorem equationHolds_instance {σ : Valuation} {equation : Atom × Atom} (τ : Valuation)
    (holds : EquationHolds σ equation) :
    EquationHolds (fun name => instantiate τ (σ name)) equation := by
  unfold EquationHolds at holds ⊢
  rw [← instantiate_instantiate, ← instantiate_instantiate, holds]

theorem three_of_instantiateList {ρ : Valuation} {items : List Atom} {one two three : Atom}
    (shape : instantiate.instantiateList ρ items = [one, two, three]) :
    ∃ head item tail, items = [head, item, tail] ∧ instantiate ρ head = one ∧
      instantiate ρ item = two ∧ instantiate ρ tail = three := by
  match items, shape with
  | [], shape => simp at shape
  | [_], shape => simp at shape
  | [_, _], shape => simp at shape
  | [head, item, tail], shape =>
      simp only [instantiateList_cons, instantiateList_nil, List.cons.injEq, and_true] at shape
      exact ⟨head, item, tail, rfl, shape.1, shape.2.1, shape.2.2⟩
  | _ :: _ :: _ :: _ :: _, shape => simp at shape

/-- A term that is the mark under spelled values is the mark when every unknown is taken as
the empty list. -/
theorem mark_under_allNil {σ : Valuation} (spelledValues : ∀ name, Spelled (σ name))
    {head : Atom} (isMark : instantiate σ head = mark) : instantiate allNil head = mark := by
  cases head with
  | var name =>
      rw [instantiate_var] at isMark
      exact absurd isMark (spelled_ne_mark (spelledValues name))
  | symbol name => simp [mark] at isMark
  | grounded value => simp [instantiate, mark] at isMark
  | expression items =>
      rw [instantiate_expression, mark] at isMark
      match items, isMark with
      | [], isMark => simp at isMark
      | _ :: _ :: _, isMark => simp at isMark
      | [inner], isMark =>
          simp only [instantiateList_cons, instantiateList_nil, Atom.expression.injEq,
            List.cons.injEq, and_true] at isMark
          cases inner with
          | var name => simp [allNil, mark]
          | symbol name => simp at isMark
          | grounded value => simp [instantiate] at isMark
          | expression deeper =>
              cases deeper with
              | nil => simp [mark]
              | cons first rest => simp at isMark

/-- If a term is spelled under some spelled values of its unknowns, it is spelled with
every unknown taken as the empty list. -/
theorem spelled_under_allNil (σ : Valuation) (spelledValues : ∀ name, Spelled (σ name)) :
    ∀ term : Atom, Spelled (instantiate σ term) → Spelled (instantiate allNil term)
  | .var name, _ => by simpa [allNil] using Spelled.nil
  | .symbol name, _ => by simpa using Spelled.symbol name
  | .grounded value, _ => by simpa [instantiate] using Spelled.grounded value
  | .expression items, spelled => by
      rw [instantiate_expression] at spelled ⊢
      rcases spelled_expression spelled with empty | ⟨first, rest, shape, spelledFirst, spelledRest⟩
      · cases items with
        | nil => simpa using Spelled.nil
        | cons _ _ => simp at empty
      · obtain ⟨head, item, tail, itemsAre, headIs, itemIs, tailIs⟩ :=
          three_of_instantiateList shape
        have closedItem := spelled_under_allNil σ spelledValues item (itemIs ▸ spelledFirst)
        have closedTail := spelled_under_allNil σ spelledValues tail (tailIs ▸ spelledRest)
        have closedHead := mark_under_allNil spelledValues headIs
        subst itemsAre
        simp only [instantiateList_cons, instantiateList_nil, closedHead]
        cases tail with
        | var name => simpa [allNil] using Spelled.cell closedItem Spelled.nil
        | symbol name => simp at tailIs
        | grounded value => simp [instantiate] at tailIs
        | expression inner =>
            rw [instantiate_expression] at closedTail ⊢
            exact Spelled.cell closedItem closedTail
termination_by term => sizeOf term
decreasing_by all_goals (simp_wf; subst itemsAre; simp; omega)

/-- Whether a term is spelled, computed. -/
def isSpelled : Atom → Bool
  | .var _ => true
  | .symbol _ => true
  | .grounded _ => true
  | .expression items => isSpelledItems items
where
  /-- Whether these are the items of a spelled expression. -/
  isSpelledItems : List Atom → Bool
    | [] => true
    | [.expression [.expression []], first, .expression rest] =>
        isSpelled first && isSpelledItems rest
    | _ => false

theorem isSpelled_of_spelled {term : Atom} (spelled : Spelled term) : isSpelled term = true := by
  induction spelled with
  | var name => simp [isSpelled]
  | symbol name => simp [isSpelled]
  | grounded value => simp [isSpelled]
  | nil => simp [isSpelled, isSpelled.isSpelledItems]
  | @cell first rest _ _ firstHolds restHolds =>
      simp only [isSpelled] at restHolds
      simp [isSpelled, isSpelled.isSpelledItems, mark, firstHolds, restHolds]

/-- What the computed check says of the items of an expression. -/
theorem isSpelledItems_shape {items : List Atom}
    (holds : isSpelled.isSpelledItems items = true) :
    items = [] ∨ ∃ first rest, items = [mark, first, .expression rest] ∧
      isSpelled first = true ∧ isSpelled.isSpelledItems rest = true := by
  unfold isSpelled.isSpelledItems at holds
  split at holds
  · exact .inl rfl
  · rename_i first rest
    simp only [Bool.and_eq_true] at holds
    exact .inr ⟨first, rest, rfl, holds.1, holds.2⟩
  · cases holds

theorem spelled_of_isSpelled : ∀ term : Atom, isSpelled term = true → Spelled term
  | .var name, _ => .var name
  | .symbol name, _ => .symbol name
  | .grounded value, _ => .grounded value
  | .expression items, holds => by
      rcases isSpelledItems_shape (by simpa [isSpelled] using holds) with
        empty | ⟨first, rest, itemsAre, firstHolds, restHolds⟩
      · rw [empty]
        exact .nil
      · have one := spelled_of_isSpelled first firstHolds
        have others := spelled_of_isSpelled (.expression rest)
          (by simpa [isSpelled] using restHolds)
        rw [itemsAre]
        exact .cell one others
termination_by term => sizeOf term
decreasing_by all_goals (simp_wf; subst itemsAre; simp [mark]; omega)

theorem isSpelled_iff (term : Atom) : isSpelled term = true ↔ Spelled term :=
  ⟨spelled_of_isSpelled term, isSpelled_of_spelled⟩

/-- Bindings close: with every unknown still free taken as the empty list, each bound value
is spelled. -/
def closes (bindings : Subst) : Bool :=
  bindings.all fun binding => isSpelled (instantiate allNil (resolve bindings (.var binding.1)))

theorem key_of_lookup {bindings : Subst} {name : String} {value : Atom}
    (found : Subst.lookup bindings name = some value) :
    ∃ binding ∈ bindings, binding.1 = name := by
  induction bindings with
  | nil => simp [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup] at found
  | cons first rest ih =>
      by_cases same : first.1 = name
      · exact ⟨first, List.mem_cons_self, same⟩
      · have later : Subst.lookup rest name = some value := by
          simpa [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, same] using found
        obtain ⟨binding, present, key⟩ := ih later
        exact ⟨binding, List.mem_cons_of_mem _ present, key⟩

/-- The valuation the bindings themselves give solves them. -/
theorem environment_solves (frame : {bindings : Subst // Idempotent bindings}) :
    valuationOf (environment frame.1) ∈ SolutionsOf EquationHolds (presentation frame.1) := by
  intro pair member
  have solved := environment_models_presentation frame.1 frame.2 pair member
  show instantiate _ pair.1 = instantiate _ pair.2
  rw [instantiate_valuationOf, instantiate_valuationOf]
  exact solved

/-- Bindings that close have a solution whose values are spellings. -/
theorem closes_has_a_list_solution (frame : {bindings : Subst // Idempotent bindings})
    (closed : closes frame.1 = true) :
    ∃ ρ : Valuation,
      (fun name => spell (ρ name)) ∈ SolutionsOf EquationHolds (presentation frame.1) := by
  have spelledAll : ∀ name,
      Spelled (instantiate allNil (valuationOf (environment frame.1) name)) := by
    intro name
    have value : valuationOf (environment frame.1) name = resolve frame.1 (.var name) :=
      read_environment frame.1 (.var name)
    rw [value]
    cases found : Subst.lookup frame.1 name with
    | none =>
        rw [Unifying.resolve_var_free found]
        simpa [allNil] using Spelled.nil
    | some bound =>
        obtain ⟨binding, present, key⟩ := key_of_lookup found
        have checked := List.all_eq_true.mp closed binding present
        rw [key] at checked
        exact spelled_of_isSpelled _ checked
  refine ⟨fun name => Classical.choose (spelling_of_spelled (spelledAll name)), ?_⟩
  have same : (fun name => spell (Classical.choose (spelling_of_spelled (spelledAll name)))) =
      fun name => instantiate allNil (valuationOf (environment frame.1) name) :=
    funext fun name => Classical.choose_spec (spelling_of_spelled (spelledAll name))
  rw [same]
  intro pair member
  exact equationHolds_instance allNil (environment_solves frame pair member)

/-- Bindings with a solution whose values are spellings close. -/
theorem list_solution_closes {bindings : Subst} {ρ : Valuation}
    (solves : (fun name => spell (ρ name)) ∈ SolutionsOf EquationHolds (presentation bindings)) :
    closes bindings = true := by
  apply List.all_eq_true.mpr
  intro binding present
  have holds : EquationHolds (fun name => spell (ρ name))
      (.var binding.1, resolve bindings (.var binding.1)) :=
    solves _ (List.mem_map.mpr ⟨binding, present, rfl⟩)
  have spelled : Spelled (instantiate (fun name => spell (ρ name))
      (resolve bindings (.var binding.1))) := by
    have same : spell (ρ binding.1) =
        instantiate (fun name => spell (ρ name)) (resolve bindings (.var binding.1)) := by
      simpa [EquationHolds] using holds
    rw [← same]
    exact spelled_spell _
  exact isSpelled_of_spelled
    (spelled_under_allNil _ (fun name => spelled_spell (ρ name)) _ spelled)

/-! ## The reading by MeTTa's terms -/

/-- A frame of the list reading: bindings in solved form that close. -/
abbrev ListFrame := {frame : {bindings : Subst // Idempotent bindings} // closes frame.1 = true}

/-- Tell the unifier the spelled fact, and keep the frame only if it closes. -/
def tellSpelled (frame : ListFrame) (fact : Told) : Option ListFrame :=
  match tellEquation frame.1 (spellFact fact) with
  | none => none
  | some next => if closed : closes next.1 = true then some ⟨next, closed⟩ else none

theorem tellSpelled_some {frame next : ListFrame} {fact : Told}
    (told : tellSpelled frame fact = some next) :
    tellEquation frame.1 (spellFact fact) = some next.1 := by
  unfold tellSpelled at told
  split at told
  · cases told
  · split at told
    · simp only [Option.some.injEq] at told
      subst told
      assumption
    · cases told

theorem tellSpelled_none {frame : ListFrame} {fact : Told}
    (refused : tellSpelled frame fact = none) :
    tellEquation frame.1 (spellFact fact) = none ∨
      ∃ next, tellEquation frame.1 (spellFact fact) = some next ∧ closes next.1 = false := by
  unfold tellSpelled at refused
  split at refused
  · left
    assumption
  · rename_i next unified
    split at refused
    · cases refused
    · rename_i unclosed
      exact .inr ⟨next, unified, by simpa using unclosed⟩

/-- The unifier on the spelled facts, a frame kept only if it closes. It is lawful for the
meaning of `ListViewMeaning`, whose values are MeTTa's terms. -/
def listReading : Reading Told.Holds where
  Frame := ListFrame
  empty := ⟨unifierReading.empty, by decide⟩
  Denotes frame := {ρ | (fun name => spell (ρ name)) ∈ unifierReading.Denotes frame.1}
  tell := tellSpelled
  empty_denotes := by
    ext ρ
    simp [unifierReading.empty_denotes]
  frame_satisfiable frame := closes_has_a_list_solution frame.1 frame.2
  told := by
    intro frame fact next told
    have law := unifierReading.told (tellSpelled_some told)
    ext ρ
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, told_holds_iff_spelled]
    rw [law]
    rfl
  refused := by
    intro frame fact refused
    ext ρ
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false,
      told_holds_iff_spelled]
    rintro ⟨inFrame, holds⟩
    rcases tellSpelled_none refused with none | ⟨next, unified, unclosed⟩
    · have law := unifierReading.refused none
      have member : (fun name => spell (ρ name)) ∈
          unifierReading.Denotes frame.1 ∩ {σ | EquationHolds σ (spellFact fact)} :=
        ⟨inFrame, holds⟩
      rw [law] at member
      exact member
    · have law := unifierReading.told unified
      have member : (fun name => spell (ρ name)) ∈ unifierReading.Denotes next := by
        rw [law]
        exact ⟨inFrame, holds⟩
      have closed := list_solution_closes member
      rw [unclosed] at closed
      cases closed

/-- The list reading accepts a list of told facts exactly when they have a solution among
MeTTa's terms. -/
theorem lists_accept_iff_solvable (told : List Told) :
    (listReading.tellAll listReading.empty told).isSome ↔ (Solutions told).Nonempty :=
  listReading.accepts_iff_satisfiable told

/-- The frame the list reading reaches means the solutions of what it was told. -/
theorem list_frame_means_the_solutions {told : List Told} {frame : listReading.Frame}
    (reached : listReading.tellAll listReading.empty told = some frame) :
    listReading.Denotes frame = Solutions told :=
  listReading.denotes_the_solutions reached

/-! ## The two readings compared -/

/-- Whatever the list reading accepts, the cell reading accepts. -/
theorem cells_accept_what_lists_accept (told : List Told)
    (accepted : (listReading.tellAll listReading.empty told).isSome) :
    (cellReading.tellAll cellReading.empty told).isSome := by
  rw [cells_accept_iff_solvable]
  obtain ⟨ρ, solution⟩ := (lists_accept_iff_solvable told).mp accepted
  exact ⟨fun name => spell (ρ name), fun fact member =>
    (told_holds_iff_spelled ρ fact).mp (solution fact member)⟩

/-- "`x` is a list with first item `a` and others `b`", and "`b` is the symbol `foo`". -/
def improperList : List Told := [.view "x" "a" "b", .equal (.var "b") (.symbol "foo")]

/-- The cell reading accepts an improper list. -/
theorem cells_accept_an_improper_list :
    (cellReading.tellAll cellReading.empty improperList).isSome = true := by
  decide +kernel

/-- Negative: the list reading refuses it. -/
theorem lists_refuse_an_improper_list :
    (listReading.tellAll listReading.empty improperList).isSome = false := by
  decide +kernel

/-- Among MeTTa's terms an improper list has no solution. -/
theorem improper_list_has_no_solution : Solutions improperList = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  intro solvable
  have accepted := (lists_accept_iff_solvable improperList).mpr solvable
  rw [lists_refuse_an_improper_list] at accepted
  cases accepted

/-! ## Without spelling, no list of equations says what a view says -/

theorem instantiateList_length (ρ : Valuation) :
    ∀ items : List Atom, (instantiate.instantiateList ρ items).length = items.length
  | [] => by simp
  | first :: rest => by simp [instantiateList_length ρ rest]

/-- `x` is the list of `count + 1` copies of `p`, `a` is `p` and `b` the list of `count`
copies. -/
def copies (count : Nat) : Valuation := fun name =>
  if name = "x" then .expression (List.replicate (count + 1) (.symbol "p"))
  else if name = "b" then .expression (List.replicate count (.symbol "p"))
  else .symbol "p"

/-- Positive: for every length, `copies` is a solution of the view. -/
theorem copies_is_a_view (count : Nat) : copies count ∈ Solutions [.view "x" "a" "b"] := by
  intro fact member
  rw [List.mem_singleton] at member
  subst member
  exact ⟨List.replicate count (.symbol "p"), by simp [copies],
    by simp [copies, List.replicate_succ]⟩

/-- Between terms as they are written, no list of equations has the solutions of a view:
the solutions of equations all give `x` a list of one length, and a view allows every
length. -/
theorem view_is_not_a_list_of_equations :
    ¬ ∃ equations : List (Atom × Atom),
        SolutionsOf EquationHolds equations = Solutions [.view "x" "a" "b"] := by
  rintro ⟨equations, same⟩
  have solvable : (SolutionsOf EquationHolds equations).Nonempty := by
    rw [same]
    exact view_alone_has_a_solution
  obtain ⟨frame, reached⟩ :=
    Option.isSome_iff_exists.mp ((unifier_accepts_iff_solvable equations).mpr solvable)
  have means := unifier_frame_means_the_solutions reached
  have canonical : valuationOf (environment frame.1) ∈ Solutions [.view "x" "a" "b"] := by
    rw [← same, ← means]
    exact environment_solves frame
  obtain ⟨items, _, listIs⟩ :
      (Told.view "x" "a" "b").Holds (valuationOf (environment frame.1)) :=
    canonical _ (List.mem_singleton.mpr rfl)
  have value : valuationOf (environment frame.1) "x" = resolve frame.1 (.var "x") :=
    read_environment frame.1 (.var "x")
  cases found : Subst.lookup frame.1 "x" with
  | none =>
      rw [value, Unifying.resolve_var_free found] at listIs
      cases listIs
  | some bound =>
      obtain ⟨binding, present, key⟩ := key_of_lookup found
      have longer : copies (items.length + 1) ∈
          SolutionsOf EquationHolds (presentation frame.1) := by
        rw [means, same]
        exact copies_is_a_view _
      have holds : EquationHolds (copies (items.length + 1))
          (.var binding.1, resolve frame.1 (.var binding.1)) :=
        longer _ (List.mem_map.mpr ⟨binding, present, rfl⟩)
      rw [key] at holds
      unfold EquationHolds at holds
      rw [← value, listIs] at holds
      have lengths := congrArg
        (fun term : Atom => match term with
          | .expression list => list.length
          | _ => 0) holds
      simp [copies, instantiateList_length] at lengths

/-! ## Controls of the list reading -/

/-- Positive: a view of an unknown. -/
theorem lists_accept_a_view_of_an_unknown :
    (listReading.tellAll listReading.empty [.view "x" "a" "b"]).isSome = true := by
  decide +kernel

/-- Positive: two views of one unknown. -/
theorem lists_accept_two_views_of_one_unknown :
    (listReading.tellAll listReading.empty
      [.view "x" "a" "b", .view "x" "c" "d"]).isSome = true := by
  decide +kernel

/-- Negative: two views of one unknown with different first items. -/
theorem lists_refuse_two_views_with_different_first_items :
    (listReading.tellAll listReading.empty
      [.view "x" "a" "b", .view "x" "c" "d", .equal (.var "a") (.symbol "p"),
        .equal (.var "c") (.symbol "q")]).isSome = false := by
  decide +kernel

/-- Positive: a view, then the list `(p q r)`, then its parts `p` and `(q r)`. -/
theorem lists_accept_a_view_and_then_the_list :
    (listReading.tellAll listReading.empty
      [.view "x" "a" "b",
        .equal (.var "x") (.expression [.symbol "p", .symbol "q", .symbol "r"]),
        .equal (.var "a") (.symbol "p"),
        .equal (.var "b") (.expression [.symbol "q", .symbol "r"])]).isSome = true := by
  decide +kernel

/-- Negative: the same view and list, and other items than `(q r)`. -/
theorem lists_refuse_other_items_than_the_list_has :
    (listReading.tellAll listReading.empty
      [.view "x" "a" "b",
        .equal (.var "x") (.expression [.symbol "p", .symbol "q", .symbol "r"]),
        .equal (.var "b") (.expression [.symbol "q"])]).isSome = false := by
  decide +kernel

/-- Positive: the parts first, then the list they make. -/
theorem lists_accept_the_parts_and_then_the_list :
    (listReading.tellAll listReading.empty
      [.view "x" "a" "b", .equal (.var "a") (.symbol "p"),
        .equal (.var "b") (.expression [.symbol "q", .symbol "r"]),
        .equal (.var "x") (.expression [.symbol "p", .symbol "q", .symbol "r"])]).isSome =
      true := by
  decide +kernel

/-- Positive: data headed by the symbol `cons` is a list whose first item is `cons`. -/
theorem lists_read_data_headed_by_cons_as_a_list :
    (listReading.tellAll listReading.empty
      [.equal (.var "x") (.expression [.symbol "cons", .symbol "p", .symbol "q"]),
        .view "x" "a" "b", .equal (.var "a") (.symbol "cons"),
        .equal (.var "b") (.expression [.symbol "p", .symbol "q"])]).isSome = true := by
  decide +kernel

/-- Negative: its first item is not `p`. -/
theorem lists_do_not_read_data_headed_by_cons_as_a_cell :
    (listReading.tellAll listReading.empty
      [.equal (.var "x") (.expression [.symbol "cons", .symbol "p", .symbol "q"]),
        .view "x" "a" "b", .equal (.var "a") (.symbol "p")]).isSome = false := by
  decide +kernel

/-- Negative: a view of a symbol. -/
theorem lists_refuse_a_view_of_a_symbol :
    (listReading.tellAll listReading.empty
      [.equal (.var "x") (.symbol "foo"), .view "x" "a" "b"]).isSome = false := by
  decide +kernel

/-- Negative: a view of the empty list. -/
theorem lists_refuse_a_view_of_the_empty_list :
    (listReading.tellAll listReading.empty
      [.equal (.var "x") (.expression []), .view "x" "a" "b"]).isSome = false := by
  decide +kernel

/-- Negative: a list that is its own rest. -/
theorem lists_refuse_a_list_that_is_its_own_rest :
    (listReading.tellAll listReading.empty [.view "x" "a" "x"]).isSome = false := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.ListView
