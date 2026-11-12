import Mettapedia.Languages.MeTTa.PeTTa.ListViewByCells
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingPatternDecides

/-!
# The model's pattern unifier means the cell reading, on values with no unknowns

`Unifying.unifyPattern` is what the model's machine runs when a value meets an equation's
argument pattern, a `let` pattern or a `case` pattern. In those places `(cons first rest)`
is the list constructor. `ListViewByCells` gives the meaning of that constructor by
spelling lists cell by cell. This module joins the two.

* **What a pattern stands for** (`readPattern`): `(cons first rest)` is the cell of `first`
  and `rest`; every other expression is the list of its items; its parts are read the same
  way. A value is data and is spelled as it is written (`spell`). So in a pattern `cons` is
  the constructor and in a value it is a symbol like any other
  (`pattern_reads_cons_as_the_constructor_and_a_value_does_not`).
* **A pattern holds of a value** under a valuation when the term the pattern stands for
  and the spelled value are equal (`PatternHolds`). For the pattern `(cons $first $rest)`
  and an unknown this is the list view of `ListViewMeaning` (`patternHolds_view`).
* **The theorem** (`pattern_unifier_agrees`, `unifyAsPattern_means`,
  `unifyAsPattern_refuses`, `unifyAsPattern_accepts_iff`): on a value with no unknowns and
  bindings in solved form, the pattern unifier answers bindings exactly when the pattern
  holds of the value under some valuation that solves the bindings it was given; the
  bindings it answers mean exactly those valuations; and a clash means there is none.
* **A `let` pattern** is such a pattern, unless it is quoted: `(quote literal)` is the
  term it quotes, met by the term unifier with no list view, whatever the value holds
  (`unifyBinding_of_no_quote`, `unifyBinding_quoted_means`). A `case` row is met by the
  pattern unifier itself.
* **The hypothesis is needed** (`an_unknown_value_is_read_otherwise`): against an unknown
  the pattern unifier binds it to the three-item expression `(cons first rest)`, and no
  valuation that solves that binding makes the pattern hold.

Related modules already in the tree, over other term types: `Machines/Cursor/ListCells`
proves the cell-aware matcher of CeTTa's PeTTa lane against unification of the readings of
its terms; `Logic/Unification/ListSpliceTerms` and `ListSpliceEncoding` encode terms with
proper lists and open spines into first-order terms and preserve unifiers. This module and
`ListViewByCells` state the cell reading for the PeTTa model's own `Atom` and its own
unifier. No map between the three term types is proved here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ListView

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst atomFreeVars)
open Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation
  (presentation successful_models_iff clashed_has_no_source_solution)
open Mettapedia.Languages.MeTTa.PeTTa.Unifying
  (Unified unify unifyTerms unifyPattern unifyAsPattern unifyBinding unifyLists Idempotent
    resolve unifyPattern_refines resolve_of_unbound unifyAsPattern_decides)

/-! ## What a pattern stands for -/

/-- The term a pattern with the list view stands for, its lists spelled by cells. -/
def readPattern : Atom → Atom
  | .var name => .var name
  | .symbol name => .symbol name
  | .grounded value => .grounded value
  | .expression items => readItems items
where
  /-- The items of one expression: the list constructor, or a list of patterns. -/
  readItems : List Atom → Atom
    | [.symbol "cons", first, rest] => .expression [mark, readPattern first, readPattern rest]
    | items => readEach items
  /-- A list of patterns, spelled. -/
  readEach : List Atom → Atom
    | [] => .expression []
    | first :: rest => .expression [mark, readPattern first, readEach rest]

@[simp] theorem readPattern_var (name : String) : readPattern (.var name) = .var name := by
  simp [readPattern]

@[simp] theorem readPattern_symbol (name : String) :
    readPattern (.symbol name) = .symbol name := by
  simp [readPattern]

@[simp] theorem readPattern_view (first rest : Atom) :
    readPattern (.expression [.symbol "cons", first, rest]) =
      .expression [mark, readPattern first, readPattern rest] := by
  simp [readPattern, readPattern.readItems]

@[simp] theorem readEach_nil : readPattern.readEach [] = .expression [] := by
  simp [readPattern.readEach]

@[simp] theorem readEach_cons (first : Atom) (rest : List Atom) :
    readPattern.readEach (first :: rest) =
      .expression [mark, readPattern first, readPattern.readEach rest] := by
  simp [readPattern.readEach]

/-- An expression that is not the list constructor is the list of its items. -/
theorem readPattern_list {items : List Atom}
    (notView : ∀ first rest, items = [.symbol "cons", first, rest] → False) :
    readPattern (.expression items) = readPattern.readEach items := by
  simp only [readPattern]
  unfold readPattern.readItems
  split
  · exact (notView _ _ rfl).elim
  · rfl

/-- An expression pattern stands for an expression. -/
theorem readPattern_expression_is_expression (items : List Atom) :
    ∃ cells, readPattern (.expression items) = .expression cells := by
  simp only [readPattern]
  unfold readPattern.readItems
  split
  · exact ⟨_, rfl⟩
  · cases items with
    | nil => exact ⟨_, readEach_nil⟩
    | cons first rest => exact ⟨_, readEach_cons first rest⟩

/-- A pattern with the list view holds of a value under a valuation: the term the pattern
stands for and the spelled value are equal. -/
def PatternHolds (ρ : Valuation) (pattern value : Atom) : Prop :=
  EquationHolds (fun name => spell (ρ name)) (readPattern pattern, spell value)

/-- Two cells are equal exactly when their first items are and their others are. -/
theorem cell_equation_iff (σ : Valuation) (first rest head tail : Atom) :
    EquationHolds σ (.expression [mark, first, rest], .expression [mark, head, tail]) ↔
      EquationHolds σ (first, head) ∧ EquationHolds σ (rest, tail) := by
  simp [EquationHolds]

/-- The pattern `(cons $first $rest)` against an unknown is the list view. -/
theorem patternHolds_view (ρ : Valuation) (list first rest : String) :
    PatternHolds ρ (.expression [.symbol "cons", .var first, .var rest]) (.var list) ↔
      (Told.view list first rest).Holds ρ := by
  rw [told_holds_iff_spelled]
  unfold PatternHolds EquationHolds
  simp only [readPattern_view, readPattern_var, spell_var, spellFact]
  exact eq_comm

/-- A pattern that is no expression holds of a value exactly when the two are equal. -/
theorem patternHolds_of_plain {pattern : Atom}
    (plain : ∀ items, pattern = .expression items → False) (ρ : Valuation) (value : Atom) :
    PatternHolds ρ pattern value ↔ EquationHolds ρ (pattern, value) := by
  have same : readPattern pattern = spell pattern := by
    cases pattern with
    | var name => simp
    | symbol name => simp
    | grounded held => simp [readPattern, spell]
    | expression items => exact (plain items rfl).elim
  unfold PatternHolds
  rw [same]
  exact (told_holds_iff_spelled ρ (.equal pattern value)).symm

/-- In a pattern `cons` is the list constructor; in a value it is a symbol like any other.
The pattern `(cons $a $b)` holds of the data `(cons p q)` exactly when `$a` is the symbol
`cons` and `$b` is `(p q)`. -/
theorem pattern_reads_cons_as_the_constructor_and_a_value_does_not (ρ : Valuation) :
    PatternHolds ρ (.expression [.symbol "cons", .var "a", .var "b"])
        (.expression [.symbol "cons", .symbol "p", .symbol "q"]) ↔
      ρ "a" = .symbol "cons" ∧ ρ "b" = .expression [.symbol "p", .symbol "q"] := by
  unfold PatternHolds
  rw [readPattern_view, spell_expression, spellItems_cons, cell_equation_iff]
  constructor
  · rintro ⟨one, two⟩
    refine ⟨spell_injective _ _ ?_, spell_injective _ _ ?_⟩
    · simpa [EquationHolds] using one
    · simpa [EquationHolds, mark] using two
  · rintro ⟨one, two⟩
    simp [EquationHolds, one, two, mark]

/-! ## The term unifier's laws, for valuations and any fuel -/

theorem terms_ok_iff (fuel : Nat) {bindings bound : Subst} {left right : Atom}
    (valid : Idempotent bindings) (unified : unifyTerms fuel bindings left right = .ok bound)
    (ρ : Valuation) :
    ρ ∈ SolutionsOf EquationHolds (presentation bound) ↔
      ρ ∈ SolutionsOf EquationHolds (presentation bindings) ∧ EquationHolds ρ (left, right) := by
  have law := successful_models_iff fuel bindings bound left right valid unified (modelOf ρ)
  rw [solves_modelOf, solves_modelOf, read_modelOf, read_modelOf] at law
  exact law

theorem terms_clash (fuel : Nat) {bindings : Subst} {left right : Atom}
    (valid : Idempotent bindings) (clashed : unifyTerms fuel bindings left right = .clash)
    (ρ : Valuation) (model : ρ ∈ SolutionsOf EquationHolds (presentation bindings)) :
    ¬ EquationHolds ρ (left, right) := by
  intro holds
  exact clashed_has_no_source_solution fuel bindings left right valid clashed
    ⟨modelOf ρ, (solves_modelOf ρ _).mpr model, by
      simpa [EquationHolds, read_modelOf] using holds⟩

/-! ## Values with no unknowns -/

/-- A term with no unknowns. -/
def Ground (term : Atom) : Prop := atomFreeVars term = []

theorem resolve_ground {bindings : Subst} {term : Atom} (ground : Ground term) :
    resolve bindings term = term :=
  resolve_of_unbound term (fun name present => by
    rw [ground] at present
    cases present)

theorem ground_head_tail {head : Atom} {tail : List Atom}
    (ground : Ground (.expression (head :: tail))) :
    Ground head ∧ Ground (.expression tail) := by
  unfold Ground at ground ⊢
  simp only [atomFreeVars, atomFreeVars.atomFreeVarsList, List.append_eq_nil_iff] at ground
  exact ⟨ground.1, by simpa [atomFreeVars] using ground.2⟩

theorem not_ground_var (name : String) : ¬ Ground (.var name) := by
  simp [Ground, atomFreeVars]

/-! ## The pattern unifier and the cell reading -/

/-- What is shown of the pattern unifier at one fuel: on a value with no unknowns, bindings
it answers mean the valuations that solve the bindings it was given and make the pattern
hold; a clash means there is no such valuation. -/
def Agrees (fuel : Nat) : Prop :=
  ∀ (bindings : Subst) (pattern value : Atom), Idempotent bindings → Ground value →
    (∀ bound, unifyPattern fuel bindings pattern value = .ok bound →
      ∀ ρ : Valuation, ρ ∈ SolutionsOf EquationHolds (presentation bound) ↔
        ρ ∈ SolutionsOf EquationHolds (presentation bindings) ∧ PatternHolds ρ pattern value) ∧
    (unifyPattern fuel bindings pattern value = .clash →
      ∀ ρ : Valuation, ρ ∈ SolutionsOf EquationHolds (presentation bindings) →
        ¬ PatternHolds ρ pattern value)

/-- The same for two lists met item by item. -/
theorem lists_agree {fuel : Nat} (each : Agrees fuel) :
    ∀ (patterns values : List Atom) (bindings : Subst), Idempotent bindings →
      Ground (.expression values) →
      (∀ bound, unifyLists (unifyPattern fuel) bindings patterns values = .ok bound →
        ∀ ρ : Valuation, ρ ∈ SolutionsOf EquationHolds (presentation bound) ↔
          ρ ∈ SolutionsOf EquationHolds (presentation bindings) ∧
            EquationHolds (fun name => spell (ρ name))
              (readPattern.readEach patterns, spell.spellItems values)) ∧
      (unifyLists (unifyPattern fuel) bindings patterns values = .clash →
        ∀ ρ : Valuation, ρ ∈ SolutionsOf EquationHolds (presentation bindings) →
          ¬ EquationHolds (fun name => spell (ρ name))
            (readPattern.readEach patterns, spell.spellItems values))
  | [], [], bindings, _, _ => by
      refine ⟨fun bound unified ρ => ?_, fun clashed => by simp [unifyLists] at clashed⟩
      simp only [unifyLists, Unified.ok.injEq] at unified
      subst unified
      simp [EquationHolds]
  | [], value :: values, bindings, _, _ => by
      refine ⟨fun bound unified => by simp [unifyLists] at unified, fun _ ρ _ => ?_⟩
      simp [EquationHolds]
  | pattern :: patterns, [], bindings, _, _ => by
      refine ⟨fun bound unified => by simp [unifyLists] at unified, fun _ ρ _ => ?_⟩
      simp [EquationHolds]
  | pattern :: patterns, value :: values, bindings, valid, ground => by
      obtain ⟨groundValue, groundValues⟩ := ground_head_tail ground
      obtain ⟨firstOk, firstClash⟩ := each bindings pattern value valid groundValue
      simp only [unifyLists, readEach_cons, spellItems_cons, cell_equation_iff]
      cases step : unifyPattern fuel bindings pattern value with
      | exhausted =>
          exact ⟨fun bound unified => by simp at unified, fun clashed => by simp at clashed⟩
      | clash =>
          refine ⟨fun bound unified => by simp at unified, fun _ ρ model holds => ?_⟩
          exact firstClash step ρ model holds.1
      | ok middle =>
          have middleValid := (unifyPattern_refines fuel bindings middle pattern value valid step).1
          obtain ⟨restOk, restClash⟩ :=
            lists_agree each patterns values middle middleValid groundValues
          simp only [Unified.ok_andThen]
          refine ⟨fun bound unified ρ => ?_, fun clashed ρ model holds => ?_⟩
          · rw [restOk bound unified ρ, firstOk middle step ρ]
            exact and_assoc
          · exact restClash clashed ρ ((firstOk middle step ρ).mpr ⟨model, holds.1⟩) holds.2

/-- **The pattern unifier means the cell reading** on values with no unknowns, at every
fuel. -/
theorem pattern_unifier_agrees : ∀ fuel : Nat, Agrees fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro bindings pattern value _ _
      exact ⟨fun bound unified => by simp [unifyPattern] at unified,
        fun clashed => by simp [unifyPattern] at clashed⟩
  | succ fuel ih =>
      intro bindings pattern value valid ground
      have same : resolve bindings value = value := resolve_ground ground
      simp only [unifyPattern]
      rw [same]
      split
      · -- the list constructor against a list with a first item
        rename_i first rest head tail
        obtain ⟨groundHead, groundTail⟩ := ground_head_tail ground
        obtain ⟨firstOk, firstClash⟩ := ih bindings first head valid groundHead
        have whole : ∀ ρ : Valuation,
            PatternHolds ρ (.expression [.symbol "cons", first, rest])
                (.expression (head :: tail)) ↔
              PatternHolds ρ first head ∧ PatternHolds ρ rest (.expression tail) := by
          intro ρ
          unfold PatternHolds
          rw [readPattern_view, spell_expression, spellItems_cons, cell_equation_iff,
            spell_expression]
        cases step : unifyPattern fuel bindings first head with
        | exhausted =>
            exact ⟨fun bound unified => by simp at unified, fun clashed => by simp at clashed⟩
        | clash =>
            refine ⟨fun bound unified => by simp at unified, fun _ ρ model holds => ?_⟩
            exact firstClash step ρ model ((whole ρ).mp holds).1
        | ok middle =>
            have middleValid :=
              (unifyPattern_refines fuel bindings middle first head valid step).1
            obtain ⟨restOk, restClash⟩ := ih middle rest (.expression tail) middleValid groundTail
            simp only [Unified.ok_andThen]
            refine ⟨fun bound unified ρ => ?_, fun clashed ρ model holds => ?_⟩
            · rw [restOk bound unified ρ, firstOk middle step ρ, whole ρ]
              exact and_assoc
            · exact restClash clashed ρ
                ((firstOk middle step ρ).mpr ⟨model, ((whole ρ).mp holds).1⟩)
                ((whole ρ).mp holds).2
      · -- the list constructor against an unknown: the value has none
        exact absurd ground (not_ground_var _)
      · -- the list constructor against a symbol, a number or the empty list
        rename_i first rest notList notVar
        refine ⟨fun bound unified => by simp at unified, fun _ ρ _ holds => ?_⟩
        unfold PatternHolds at holds
        rw [readPattern_view] at holds
        cases value with
        | var name => exact notVar name rfl
        | symbol name => simp [EquationHolds] at holds
        | grounded held => simp [EquationHolds, spell, instantiate] at holds
        | expression items =>
            cases items with
            | nil => simp [EquationHolds] at holds
            | cons head tail => exact notList head tail rfl
      · -- two lists, item by item
        rename_i patterns values _ notView
        obtain ⟨listOk, listClash⟩ := lists_agree ih patterns values bindings valid ground
        simp only [PatternHolds, readPattern_list notView, spell_expression]
        exact ⟨listOk, listClash⟩
      · -- a list pattern against an unknown: the value has none
        exact absurd ground (not_ground_var _)
      · -- a list pattern against a symbol or a number
        rename_i items notView _ _ notList notVar
        refine ⟨fun bound unified => by simp at unified, fun _ ρ _ holds => ?_⟩
        obtain ⟨cells, shape⟩ := readPattern_expression_is_expression items
        unfold PatternHolds at holds
        rw [shape] at holds
        cases value with
        | var name => exact notVar name rfl
        | symbol name => simp [EquationHolds] at holds
        | grounded held => simp [EquationHolds, spell, instantiate] at holds
        | expression others => exact notList others rfl
      · -- a pattern that is no expression: the term unifier
        rename_i _ plain _ _ _ _
        refine ⟨fun bound unified ρ => ?_, fun clashed ρ model holds => ?_⟩
        · rw [patternHolds_of_plain plain ρ value]
          exact terms_ok_iff fuel valid unified ρ
        · exact terms_clash fuel valid clashed ρ model
            ((patternHolds_of_plain plain ρ value).mp holds)

/-- Bindings the pattern unifier answers on a value with no unknowns mean the valuations
that solve the bindings it was given and make the pattern hold. -/
theorem unifyAsPattern_means {bindings bound : Subst} {pattern value : Atom}
    (valid : Idempotent bindings) (ground : Ground value)
    (unified : unifyAsPattern bindings pattern value = .ok bound) :
    SolutionsOf EquationHolds (presentation bound) =
      SolutionsOf EquationHolds (presentation bindings) ∩ {ρ | PatternHolds ρ pattern value} := by
  ext ρ
  exact (pattern_unifier_agrees _ bindings pattern value valid ground).1 bound unified ρ

/-- A clash of the pattern unifier on a value with no unknowns: no valuation solves the
bindings and makes the pattern hold. -/
theorem unifyAsPattern_refuses {bindings : Subst} {pattern value : Atom}
    (valid : Idempotent bindings) (ground : Ground value)
    (clashed : unifyAsPattern bindings pattern value = .clash) :
    SolutionsOf EquationHolds (presentation bindings) ∩ {ρ | PatternHolds ρ pattern value} = ∅ := by
  ext ρ
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨model, holds⟩
  exact (pattern_unifier_agrees _ bindings pattern value valid ground).2 clashed ρ model holds

/-- On a value with no unknowns the pattern unifier answers bindings exactly when some
valuation solves the bindings it was given and makes the pattern hold. -/
theorem unifyAsPattern_accepts_iff {bindings : Subst} {pattern value : Atom}
    (valid : Idempotent bindings) (ground : Ground value) :
    (∃ bound, unifyAsPattern bindings pattern value = .ok bound) ↔
      (SolutionsOf EquationHolds (presentation bindings) ∩
        {ρ | PatternHolds ρ pattern value}).Nonempty := by
  constructor
  · rintro ⟨bound, unified⟩
    rw [← unifyAsPattern_means valid ground unified]
    have boundValid :=
      (unifyPattern_refines _ bindings bound pattern value valid unified).1
    exact ⟨_, environment_solves ⟨bound, boundValid⟩⟩
  · intro solvable
    cases result : unifyAsPattern bindings pattern value with
    | ok bound => exact ⟨bound, rfl⟩
    | clash =>
        rw [unifyAsPattern_refuses valid ground result] at solvable
        exact absurd solvable Set.not_nonempty_empty
    | exhausted => exact absurd result (unifyAsPattern_decides bindings pattern value valid)

/-! ## A `let` pattern -/

/-- A `let` pattern that is not quoted is met as a pattern with the list view. -/
theorem unifyBinding_of_no_quote {bindings : Subst} {pattern value : Atom}
    (plain : ∀ literal, pattern = .expression [.symbol "quote", literal] → False) :
    unifyBinding bindings pattern value = unifyAsPattern bindings pattern value := by
  unfold unifyBinding
  split
  · exact (plain _ rfl).elim
  · rfl

/-- A quoted `let` pattern is the term it quotes, with no list view: the bindings answered
mean the valuations that solve the given bindings and make that term equal to the value.
This holds whatever the value holds, unknowns included. -/
theorem unifyBinding_quoted_means {bindings bound : Subst} {literal value : Atom}
    (valid : Idempotent bindings)
    (unified : unifyBinding bindings (.expression [.symbol "quote", literal]) value =
      .ok bound) :
    SolutionsOf EquationHolds (presentation bound) =
      SolutionsOf EquationHolds (presentation bindings) ∩
        {ρ | EquationHolds ρ (literal, value)} := by
  have same : unifyBinding bindings (.expression [.symbol "quote", literal]) value =
      unify bindings literal value := by
    simp [unifyBinding]
  rw [same] at unified
  unfold unify at unified
  ext ρ
  exact terms_ok_iff _ valid unified ρ

/-! ## The hypothesis is needed, and controls -/

/-- Against an unknown the pattern unifier binds it to the three-item expression
`(cons $a $b)`, and no valuation that solves that binding makes the pattern hold. -/
theorem an_unknown_value_is_read_otherwise :
    unifyAsPattern [] (.expression [.symbol "cons", .var "a", .var "b"]) (.var "x") =
        .ok [("x", .expression [.symbol "cons", .var "a", .var "b"])] ∧
      SolutionsOf EquationHolds
          (presentation [("x", .expression [.symbol "cons", .var "a", .var "b"])]) ∩
        {ρ | PatternHolds ρ (.expression [.symbol "cons", .var "a", .var "b"]) (.var "x")} = ∅ := by
  refine ⟨by decide +kernel, ?_⟩
  ext ρ
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
    patternHolds_view]
  rintro ⟨model, viewed⟩
  have common : ρ ∈ Solutions (bindingsTold
      [("x", .expression [.symbol "cons", .var "a", .var "b"])]) ∩
      Solutions [.view "x" "a" "b"] := by
    refine ⟨fun fact member => ?_, fun fact member => ?_⟩
    · simp only [bindingsTold, List.map_cons, List.map_nil, List.mem_singleton] at member
      subst member
      exact model (.var "x", .expression [.symbol "cons", .var "a", .var "b"]) (by decide +kernel)
    · rw [List.mem_singleton] at member
      subst member
      exact viewed
  rw [model_answer_has_none_of_the_solutions] at common
  exact common

/-- Positive: the list `(p q r)` under the pattern `(cons $a $b)`. -/
theorem pattern_takes_a_list_apart :
    unifyAsPattern [] (.expression [.symbol "cons", .var "a", .var "b"])
        (.expression [.symbol "p", .symbol "q", .symbol "r"]) =
      .ok [("b", .expression [.symbol "q", .symbol "r"]), ("a", .symbol "p")] := by
  decide +kernel

/-- Positive: the data `(cons p q)` under the same pattern has first item `cons`. -/
theorem pattern_takes_data_headed_by_cons_apart :
    unifyAsPattern [] (.expression [.symbol "cons", .var "a", .var "b"])
        (.expression [.symbol "cons", .symbol "p", .symbol "q"]) =
      .ok [("b", .expression [.symbol "p", .symbol "q"]), ("a", .symbol "cons")] := by
  decide +kernel

/-- Negative: a symbol and the empty list are refused. -/
theorem pattern_refuses_a_symbol_and_the_empty_list :
    unifyAsPattern [] (.expression [.symbol "cons", .var "a", .var "b"]) (.symbol "foo") =
        .clash ∧
      unifyAsPattern [] (.expression [.symbol "cons", .var "a", .var "b"]) (.expression []) =
        .clash := by
  decide +kernel

/-- A quoted `let` pattern has no list view: `(quote (cons $a $b))` against the data
`(cons p q)` gives `p` and `q`. Without the quote the same pattern gives `cons` and
`(p q)` (`pattern_takes_data_headed_by_cons_apart`). -/
theorem quoted_pattern_reads_cons_as_a_symbol :
    (match unifyBinding []
        (.expression [.symbol "quote", .expression [.symbol "cons", .var "a", .var "b"]])
        (.expression [.symbol "cons", .symbol "p", .symbol "q"]) with
      | .ok bound => (Subst.lookup bound "a", Subst.lookup bound "b")
      | _ => (none, none)) = (some (.symbol "p"), some (.symbol "q")) := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.ListView
