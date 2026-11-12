import Mettapedia.Languages.MeTTa.PeTTa.UnifyingViewOfUnknown
import Mathlib.Data.Set.Basic

/-!
# What a list pattern against an unknown means, and which readings of it are lawful

PeTTa's pattern `(cons first rest)` says of the value it meets: it is a list, `first` is
its first item and `rest` is the list of the others. When the value is not known yet, an
evaluator has to keep what was said. There are several ways to keep it, and this module
is where they are compared. It states the meaning once, without choosing a way:

* A **valuation** gives every unknown a value. What can be told is a view of an unknown as
  a list, or an equation between two terms (`Told`). A told fact holds or fails under a
  valuation; a list of told facts means the set of valuations under which all of them hold,
  its **solutions** (`Solutions`).
* The laws follow from the meaning alone: two views of one unknown have the same first
  item and the same others (`view_twice`); a view followed by the values of its parts gives
  the list (`view_then_known`), and a known list followed by a view gives the parts
  (`known_then_view`), whichever comes first; data whose first item is the symbol `cons` is
  a list like any other (`data_headed_by_cons_is_a_list`).
* A **lawful reading** (`Reading`) keeps what was told in frames of its own choosing, and is
  held to three things: a told fact narrows the frame's valuations to exactly those under
  which the fact holds, a fact is refused only when no valuation is left, and no frame is
  empty of valuations. Any two lawful readings accept the same lists of facts and mean the
  same solutions by them (`lawful_readings_agree`). The theorem says that much and no more:
  what a machine shows of a frame (a binding, a reply that waits), in what order, and with
  what effects, is not decided by it and needs laws of its own.

Readings that are not lawful, each with the fact that shows it:

* **The unknown bound to the expression `(cons first rest)`**, a three-item list. This is
  what `Unifying.unifyPattern` does (`model_binds_the_unknown_to_an_expression`). That
  binding, read as the equation it is, and the view have no solution in common
  (`model_answer_has_none_of_the_solutions`).
* **Data headed by `cons` read as a list cell.** It would repair the first reading, and
  it confuses data with structure (`data_headed_by_cons_is_not_a_cell`).
* **No answer until the value is known.** A view of an unknown has solutions
  (`view_alone_has_a_solution`), so a lawful reading accepts it
  (`Reading.accepts_a_view_of_an_unknown`).

A fourth reading comes from MeTTa's rule that what cannot be evaluated is left as it is
written. Taken on closed terms alone, it makes `cons` a total operation: the list when its
second argument is a list, the expression `(cons first rest)` otherwise (`consOrLeft`). On
lists it is the list view (`consOrLeft_of_a_list`). But it is not injective
(`consOrLeft_is_not_injective`): the data `(cons p q)` is at once the list with first item
`cons` and others `(p q)`, and the application of `cons` to `p` and `q` left as written.
So under this reading a view does not determine its parts. Both hosts avoid that by keeping
the application left as written apart from the data of the same shape, and print the two
alike. A lawful form of this reading therefore needs the two kept apart in the terms
themselves, as computation and data are.

Existence is shown in `ListViewByCells` (`listReading`): the model's unifier on terms whose
lists are spelled cell by cell, a frame kept only if it has a solution among MeTTa's terms.
A second construction, the told views kept beside bindings between terms as they are
written, is not built; by `lawful_readings_agree` it would accept the same facts and mean
the same solutions. Whether two such machines also show the same bindings at the same
times is a separate question (`Machines/OperatorChoice/ConstraintObservationControls`).

Negative examples of the meaning itself: a symbol and the empty list have no view
(`view_of_a_symbol_has_no_solution`, `view_of_the_empty_list_has_no_solution`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ListView

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa.Unifying (unifyAsPattern atomSize)
open Mettapedia.Languages.MeTTa.PeTTa.Unifying.Controls (listView)

/-! ## The meaning -/

/-- A valuation gives every unknown a value. -/
abbrev Valuation := String → Atom

/-- A term under a valuation: each unknown replaced by its value. -/
def instantiate (ρ : Valuation) : Atom → Atom
  | .var name => ρ name
  | .symbol name => .symbol name
  | .grounded value => .grounded value
  | .expression items => .expression (instantiateList ρ items)
where
  /-- The items of a list under a valuation. -/
  instantiateList (ρ : Valuation) : List Atom → List Atom
    | [] => []
    | first :: rest => instantiate ρ first :: instantiateList ρ rest

@[simp] theorem instantiate_var (ρ : Valuation) (name : String) :
    instantiate ρ (.var name) = ρ name := by
  simp [instantiate]

@[simp] theorem instantiate_symbol (ρ : Valuation) (name : String) :
    instantiate ρ (.symbol name) = .symbol name := by
  simp [instantiate]

@[simp] theorem instantiate_expression (ρ : Valuation) (items : List Atom) :
    instantiate ρ (.expression items) = .expression (instantiate.instantiateList ρ items) := by
  simp [instantiate]

@[simp] theorem instantiateList_nil (ρ : Valuation) : instantiate.instantiateList ρ [] = [] := by
  simp [instantiate.instantiateList]

@[simp] theorem instantiateList_cons (ρ : Valuation) (first : Atom) (rest : List Atom) :
    instantiate.instantiateList ρ (first :: rest) =
      instantiate ρ first :: instantiate.instantiateList ρ rest := by
  simp [instantiate.instantiateList]

/-- What can be told of unknowns. -/
inductive Told where
  /-- `list` is a list, `first` is its first item and `rest` the list of the others. -/
  | view (list first rest : String)
  /-- The two terms are equal. -/
  | equal (left right : Atom)

/-- A told fact under a valuation. -/
def Told.Holds (ρ : Valuation) : Told → Prop
  | .view list first rest =>
      ∃ items, ρ rest = .expression items ∧ ρ list = .expression (ρ first :: items)
  | .equal left right => instantiate ρ left = instantiate ρ right

/-- The valuations under which every fact of a list holds, for facts of any kind. -/
def SolutionsOf {Fact : Type} (Holds : Valuation → Fact → Prop) (facts : List Fact) :
    Set Valuation := {ρ | ∀ fact ∈ facts, Holds ρ fact}

theorem solutionsOf_nil {Fact : Type} (Holds : Valuation → Fact → Prop) :
    SolutionsOf Holds [] = Set.univ := by
  ext ρ
  simp [SolutionsOf]

theorem solutionsOf_cons {Fact : Type} (Holds : Valuation → Fact → Prop) (fact : Fact)
    (facts : List Fact) :
    SolutionsOf Holds (fact :: facts) = {ρ | Holds ρ fact} ∩ SolutionsOf Holds facts := by
  ext ρ
  simp [SolutionsOf]

/-- The valuations under which every told fact holds. -/
def Solutions (told : List Told) : Set Valuation := SolutionsOf Told.Holds told

/-! ## Laws of the meaning -/

/-- Two views of one unknown: the same first item and the same others. -/
theorem view_twice {ρ : Valuation} {list first rest first' rest' : String}
    (solution : ρ ∈ Solutions [.view list first rest, .view list first' rest']) :
    ρ first = ρ first' ∧ ρ rest = ρ rest' := by
  obtain ⟨one, two⟩ :
      (Told.view list first rest).Holds ρ ∧ (Told.view list first' rest').Holds ρ := by
    simpa [Solutions, SolutionsOf] using solution
  obtain ⟨items, restIs, listIs⟩ := one
  obtain ⟨items', restIs', listIs'⟩ := two
  rw [listIs] at listIs'
  simp only [Atom.expression.injEq, List.cons.injEq] at listIs'
  exact ⟨listIs'.1, by rw [restIs, restIs', listIs'.2]⟩

/-- A known list, then a view of it: the parts. -/
theorem known_then_view {ρ : Valuation} {list first rest : String} {head : Atom}
    {tail : List Atom}
    (solution : ρ ∈ Solutions
      [.equal (.var list) (.expression (head :: tail)), .view list first rest]) :
    ρ first = instantiate ρ head ∧ ρ rest = .expression (instantiate.instantiateList ρ tail) := by
  obtain ⟨known, viewed⟩ :
      (Told.equal (.var list) (.expression (head :: tail))).Holds ρ ∧
        (Told.view list first rest).Holds ρ := by
    simpa [Solutions, SolutionsOf] using solution
  obtain ⟨items, restIs, listIs⟩ := viewed
  have known' : ρ list =
      .expression (instantiate ρ head :: instantiate.instantiateList ρ tail) := by
    simpa [Told.Holds] using known
  rw [known'] at listIs
  simp only [Atom.expression.injEq, List.cons.injEq] at listIs
  exact ⟨listIs.1.symm, by rw [restIs, listIs.2]⟩

/-- A view, then the values of its parts: the list. The same facts as in `known_then_view`,
told in the other order, mean the same. -/
theorem view_then_known {ρ : Valuation} {list first rest : String} {head : Atom}
    {tail : List Atom}
    (solution : ρ ∈ Solutions
      [.view list first rest, .equal (.var first) head, .equal (.var rest) (.expression tail)]) :
    ρ list = .expression (instantiate ρ head :: instantiate.instantiateList ρ tail) := by
  obtain ⟨viewed, firstIs, restIs⟩ :
      (Told.view list first rest).Holds ρ ∧ (Told.equal (.var first) head).Holds ρ ∧
        (Told.equal (.var rest) (.expression tail)).Holds ρ := by
    simpa [Solutions, SolutionsOf] using solution
  obtain ⟨items, restExpression, listIs⟩ := viewed
  have firstIs' : ρ first = instantiate ρ head := by simpa [Told.Holds] using firstIs
  have restIs' : ρ rest = .expression (instantiate.instantiateList ρ tail) := by
    simpa [Told.Holds] using restIs
  rw [restIs'] at restExpression
  simp only [Atom.expression.injEq] at restExpression
  rw [listIs, firstIs', ← restExpression]

/-- Data whose first item is the symbol `cons` is a list like any other: its first item is
`cons`. -/
theorem data_headed_by_cons_is_a_list {ρ : Valuation} {list first rest : String}
    {left right : Atom}
    (solution : ρ ∈ Solutions
      [.equal (.var list) (.expression [.symbol "cons", left, right]), .view list first rest]) :
    ρ first = .symbol "cons" ∧ ρ rest = .expression [instantiate ρ left, instantiate ρ right] := by
  simpa using known_then_view solution

/-- Negative: a symbol has no view. -/
theorem view_of_a_symbol_has_no_solution (list first rest name : String) :
    Solutions [.equal (.var list) (.symbol name), .view list first rest] = ∅ := by
  ext ρ
  simp only [Set.mem_empty_iff_false, iff_false]
  intro solution
  obtain ⟨known, viewed⟩ :
      (Told.equal (.var list) (.symbol name)).Holds ρ ∧ (Told.view list first rest).Holds ρ := by
    simpa [Solutions, SolutionsOf] using solution
  obtain ⟨items, -, listIs⟩ := viewed
  have known' : ρ list = .symbol name := by simpa [Told.Holds] using known
  rw [known'] at listIs
  exact absurd listIs (by simp)

/-- Negative: the empty list has no view. -/
theorem view_of_the_empty_list_has_no_solution (list first rest : String) :
    Solutions [.equal (.var list) (.expression []), .view list first rest] = ∅ := by
  ext ρ
  simp only [Set.mem_empty_iff_false, iff_false]
  intro solution
  obtain ⟨known, viewed⟩ :
      (Told.equal (.var list) (.expression [])).Holds ρ ∧ (Told.view list first rest).Holds ρ := by
    simpa [Solutions, SolutionsOf] using solution
  obtain ⟨items, -, listIs⟩ := viewed
  have known' : ρ list = .expression [] := by simpa [Told.Holds] using known
  rw [known'] at listIs
  exact absurd listIs (by simp)

/-- The valuation `$x = (p)`, `$a = p`, every other unknown the empty list. -/
def onePValuation : Valuation := fun name =>
  if name = "x" then .expression [.symbol "p"]
  else if name = "a" then .symbol "p"
  else .expression []

/-- Positive: a view of an unknown has a solution. -/
theorem view_alone_has_a_solution : (Solutions [.view "x" "a" "b"]).Nonempty := by
  refine ⟨onePValuation, ?_⟩
  intro fact member
  simp only [List.mem_singleton] at member
  subst member
  exact ⟨[], by simp [onePValuation], by simp [onePValuation]⟩

/-! ## Lawful readings -/

/-- A reading keeps what was told in frames. It is lawful when a frame means a set of
valuations that is never empty, a told fact narrows that set to exactly the valuations under
which the fact holds, and a fact is refused only when none would be left. The kind of fact
is a parameter: views and equations (`Told.Holds`), or equations alone. -/
structure Reading {Fact : Type} (Holds : Valuation → Fact → Prop) where
  /-- What the reading keeps. -/
  Frame : Type
  /-- Nothing told yet. -/
  empty : Frame
  /-- The valuations a frame leaves possible. -/
  Denotes : Frame → Set Valuation
  /-- Tell a fact: the next frame, or a refusal. -/
  tell : Frame → Fact → Option Frame
  empty_denotes : Denotes empty = Set.univ
  frame_satisfiable : ∀ frame, (Denotes frame).Nonempty
  told : ∀ {frame : Frame} {fact : Fact} {next : Frame}, tell frame fact = some next →
    Denotes next = Denotes frame ∩ {ρ | Holds ρ fact}
  refused : ∀ {frame : Frame} {fact : Fact}, tell frame fact = none →
    Denotes frame ∩ {ρ | Holds ρ fact} = ∅

section Lawful

variable {Fact : Type} {Holds : Valuation → Fact → Prop}

/-- Facts told one after another. -/
def Reading.tellAll (R : Reading Holds) : R.Frame → List Fact → Option R.Frame
  | frame, [] => some frame
  | frame, fact :: rest => (R.tell frame fact).bind fun next => R.tellAll next rest

theorem Reading.tellAll_some (R : Reading Holds) :
    ∀ (told : List Fact) (frame next : R.Frame), R.tellAll frame told = some next →
      R.Denotes next = R.Denotes frame ∩ SolutionsOf Holds told
  | [], frame, next, reached => by
      simp only [Reading.tellAll, Option.some.injEq] at reached
      subst reached
      simp [solutionsOf_nil]
  | fact :: rest, frame, next, reached => by
      simp only [Reading.tellAll] at reached
      cases step : R.tell frame fact with
      | none =>
          rw [step] at reached
          cases reached
      | some middle =>
          rw [step] at reached
          have reached' : R.tellAll middle rest = some next := reached
          rw [R.tellAll_some rest middle next reached', R.told step, solutionsOf_cons,
            Set.inter_assoc]

theorem Reading.tellAll_none (R : Reading Holds) :
    ∀ (told : List Fact) (frame : R.Frame), R.tellAll frame told = none →
      R.Denotes frame ∩ SolutionsOf Holds told = ∅
  | [], frame, reached => by
      simp [Reading.tellAll] at reached
  | fact :: rest, frame, reached => by
      simp only [Reading.tellAll] at reached
      cases step : R.tell frame fact with
      | none =>
          rw [solutionsOf_cons, ← Set.inter_assoc, R.refused step, Set.empty_inter]
      | some middle =>
          rw [step] at reached
          have reached' : R.tellAll middle rest = none := reached
          have none_left := R.tellAll_none rest middle reached'
          rw [R.told step] at none_left
          rw [solutionsOf_cons, ← Set.inter_assoc]
          exact none_left

/-- The frame a lawful reading reaches means the solutions of what was told. -/
theorem Reading.denotes_the_solutions (R : Reading Holds) {told : List Fact} {next : R.Frame}
    (reached : R.tellAll R.empty told = some next) : R.Denotes next = SolutionsOf Holds told := by
  rw [R.tellAll_some told R.empty next reached, R.empty_denotes, Set.univ_inter]

/-- A lawful reading accepts a list of facts exactly when it has a solution. -/
theorem Reading.accepts_iff_satisfiable (R : Reading Holds) (told : List Fact) :
    (R.tellAll R.empty told).isSome ↔ (SolutionsOf Holds told).Nonempty := by
  constructor
  · intro accepted
    obtain ⟨next, reached⟩ := Option.isSome_iff_exists.mp accepted
    rw [← R.denotes_the_solutions reached]
    exact R.frame_satisfiable next
  · intro satisfiable
    cases reached : R.tellAll R.empty told with
    | some next => rfl
    | none =>
        have none_left := R.tellAll_none told R.empty reached
        rw [R.empty_denotes, Set.univ_inter] at none_left
        rw [none_left] at satisfiable
        exact absurd satisfiable Set.not_nonempty_empty

/-- Any two lawful readings accept the same lists of facts and mean the same solutions by
them. -/
theorem lawful_readings_agree (R S : Reading Holds) (told : List Fact) :
    ((R.tellAll R.empty told).isSome ↔ (S.tellAll S.empty told).isSome) ∧
      ∀ {r : R.Frame} {s : S.Frame}, R.tellAll R.empty told = some r →
        S.tellAll S.empty told = some s → R.Denotes r = S.Denotes s := by
  refine ⟨(R.accepts_iff_satisfiable told).trans (S.accepts_iff_satisfiable told).symm, ?_⟩
  intro r s reachedR reachedS
  rw [R.denotes_the_solutions reachedR, S.denotes_the_solutions reachedS]

end Lawful

/-- In a lawful reading two views of one unknown have the same first item and the same
others. -/
theorem Reading.view_twice (R : Reading Told.Holds) {list first rest first' rest' : String}
    {next : R.Frame}
    (reached : R.tellAll R.empty [.view list first rest, .view list first' rest'] = some next)
    {ρ : Valuation} (possible : ρ ∈ R.Denotes next) :
    ρ first = ρ first' ∧ ρ rest = ρ rest' := by
  rw [R.denotes_the_solutions reached] at possible
  exact ListView.view_twice possible

/-- A lawful reading accepts a view of an unknown: answering nothing until the value is
known is not lawful. -/
theorem Reading.accepts_a_view_of_an_unknown (R : Reading Told.Holds) :
    (R.tellAll R.empty [.view "x" "a" "b"]).isSome :=
  (R.accepts_iff_satisfiable _).mpr view_alone_has_a_solution

/-! ## The readings that are not lawful -/

/-- A list of bindings as told facts: each bound unknown equal to the term it is bound to. -/
def bindingsTold (bindings : Subst) : List Told :=
  bindings.map fun binding => .equal (.var binding.1) binding.2

/-- What the model answers when the pattern `(cons $a $b)` meets the unknown `$x`: `$x`
bound to the expression `(cons $a $b)`. -/
theorem model_binds_the_unknown_to_an_expression :
    unifyAsPattern [] (listView "a" "b") (.var "x") =
      .ok [("x", .expression [.symbol "cons", .var "a", .var "b"])] := by
  decide +kernel

/-- The model's answer and the view have no solution in common. A common one would make
`$b` a list that has itself as an item. -/
theorem model_answer_has_none_of_the_solutions :
    Solutions (bindingsTold [("x", .expression [.symbol "cons", .var "a", .var "b"])]) ∩
      Solutions [.view "x" "a" "b"] = ∅ := by
  ext ρ
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨accepted, solution⟩
  have bound : ρ "x" = .expression [.symbol "cons", ρ "a", ρ "b"] := by
    have binding := accepted
      (.equal (.var "x") (.expression [.symbol "cons", .var "a", .var "b"]))
      (by simp [bindingsTold])
    simpa [Told.Holds] using binding
  obtain ⟨items, restIs, listIs⟩ : (Told.view "x" "a" "b").Holds ρ := solution _ (by simp)
  rw [bound] at listIs
  simp only [Atom.expression.injEq, List.cons.injEq] at listIs
  obtain ⟨-, itemsAre⟩ := listIs
  rw [← itemsAre] at restIs
  have sizes := congrArg atomSize restIs
  simp only [atomSize, atomSize.listSize] at sizes
  omega

/-- The valuation `$x = (cons p q)` as data, `$a = cons`, every other unknown `(p q)`. -/
def consDataValuation : Valuation := fun name =>
  if name = "x" then .expression [.symbol "cons", .symbol "p", .symbol "q"]
  else if name = "a" then .symbol "cons"
  else .expression [.symbol "p", .symbol "q"]

/-- Reading data headed by `cons` as a list cell is refuted: of the data `(cons p q)` the
view's first item is `cons`, not `p`. -/
theorem data_headed_by_cons_is_not_a_cell :
    ¬ ∀ (ρ : Valuation) (left right : Atom),
        ρ ∈ Solutions
          [.equal (.var "x") (.expression [.symbol "cons", left, right]), .view "x" "a" "b"] →
        ρ "a" = instantiate ρ left := by
  intro claimed
  have solution : consDataValuation ∈ Solutions
      [.equal (.var "x") (.expression [.symbol "cons", .symbol "p", .symbol "q"]),
        .view "x" "a" "b"] := by
    intro fact member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · simp [Told.Holds, consDataValuation]
    · simp [Told.Holds, consDataValuation]
  have wrong := claimed consDataValuation (.symbol "p") (.symbol "q") solution
  simp [consDataValuation] at wrong

/-! ## `cons` left as written when it cannot be applied -/

/-- `cons` as a total operation on terms: the list when the second argument is a list,
and otherwise the application left as it is written, the three-item expression. -/
def consOrLeft (first rest : Atom) : Atom :=
  match rest with
  | .expression items => .expression (first :: items)
  | other => .expression [.symbol "cons", first, other]

/-- Positive: on a list it is the list with the new first item. -/
theorem consOrLeft_of_a_list (first : Atom) (items : List Atom) :
    consOrLeft first (.expression items) = .expression (first :: items) := rfl

/-- Positive: on a symbol the application is left as written. -/
theorem consOrLeft_of_a_symbol (first : Atom) (name : String) :
    consOrLeft first (.symbol name) = .expression [.symbol "cons", first, .symbol name] := rfl

/-- Negative: it is not injective. The data `(cons p q)` is the list with first item `cons`
and others `(p q)`, and it is also `cons` of `p` and `q` left as written. -/
theorem consOrLeft_is_not_injective :
    consOrLeft (.symbol "cons") (.expression [.symbol "p", .symbol "q"]) =
        consOrLeft (.symbol "p") (.symbol "q") ∧
      (Atom.symbol "cons", Atom.expression [.symbol "p", .symbol "q"]) ≠
        (Atom.symbol "p", Atom.symbol "q") := by
  refine ⟨rfl, ?_⟩
  intro same
  simp at same

end Mettapedia.Languages.MeTTa.PeTTa.ListView
