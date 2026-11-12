import Mettapedia.Languages.MeTTa.PeTTa.PatternReadByCells
import Mettapedia.Machines.Cursor.ListCells
import Mathlib.Logic.Equiv.List

/-!
# The model's cell reading is the reference reading of CeTTa's list cells

`Machines/Cursor/ListCells` proves the cell-aware matcher of CeTTa's PeTTa lane against a
reference: every term has a reading as a term of lists (`PT`: atoms, variables, the empty
list, cons), and two terms unify when a substitution of reference terms equates their
readings (`Unifies`). `ListViewByCells` and `PatternReadByCells` give the PeTTa model's
terms a meaning by spelling lists cell by cell inside the model's own term type. This
module shows the two are one meaning.

* **Names.** The model names symbols and unknowns by strings and has grounded values; the
  reference numbers its atoms and variables. A `Naming` gives the numbers. Where the map
  has to reflect equality the naming is `Faithful` (different names, different numbers);
  one such naming is given (`naming`, `naming_faithful`).
* **A spelled term stands for a reference term** (`referenceOf`): the empty list for `()`,
  a cons for a cell, nothing for any other expression. A model value, spelled, stands for
  the list it is (`referenceOf_spell`), and a pattern for the list or cell it stands for
  (`referenceOf_readPattern`). Giving unknowns their values is substitution in the
  reference (`referenceOf_instantiate`), and under a faithful naming a reference term is
  the reading of at most one spelled term (`referenceOf_injective`).
* **The engine's terms.** A model value is CeTTa's flat expression (`embed`), a pattern is
  its expression with a cell where the pattern has the list constructor (`embedPattern`);
  their readings are the same reference terms (`denote_embed`, `denote_embedPattern`).
* **One fact** (`equation_iff_unifies`, `patternHolds_iff_unifies`): a pattern holds of a
  value under a valuation exactly when the reference substitution of that valuation
  unifies the engine's two terms. With `PatternReadByCells`: on a value with no unknowns
  the model's pattern unifier answers exactly when some valuation's reference substitution
  unifies them (`unifyAsPattern_accepts_iff_reference_unifies`).

Controls: the pattern `(cons $a $b)` is the engine's cell of the two variables
(`pattern_embeds_as_a_cell`); the data `(cons p q)` is no cell
(`data_headed_by_cons_embeds_as_no_cell`).

Not shown here: any statement about the engine's matcher itself, which
`Machines/Cursor/ListCells` proves against `Unifies`; and the map to the first-order
encoding of `Logic/Unification/ListSpliceEncoding`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ListView

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Machines.Cursor.ListCells (Tm PT Unifies Agree)
open Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation (presentation)
open Mettapedia.Languages.MeTTa.PeTTa.Unifying (unifyAsPattern)

/-! ## Names -/

/-- Numbers for the model's names: one for each symbol and grounded value, one for each
unknown. -/
structure Naming where
  leaf : String ⊕ GroundedValue → ℕ
  unknown : String → ℕ

/-- Different names have different numbers. -/
def Naming.Faithful (N : Naming) : Prop :=
  Function.Injective N.leaf ∧ Function.Injective N.unknown

/-- A number for a string: the code of the list of its characters' numbers. -/
def stringNumber (text : String) : ℕ := Encodable.encode (text.toList.map Char.toNat)

theorem stringNumber_injective : Function.Injective stringNumber := by
  intro one two same
  have characters : Function.Injective Char.toNat := fun _ _ equal => Char.toNat_inj.mp equal
  exact String.toList_injective
    (List.map_injective_iff.mpr characters (Encodable.encode_injective same))

/-- A grounded value as numbers, each kind apart. -/
def groundedCode : GroundedValue → ℤ ⊕ (ℕ ⊕ (Bool ⊕ (ℕ × ℕ)))
  | .int value => .inl value
  | .string text => .inr (.inl (stringNumber text))
  | .bool flag => .inr (.inr (.inl flag))
  | .custom typeName data => .inr (.inr (.inr (stringNumber typeName, stringNumber data)))

theorem groundedCode_injective : Function.Injective groundedCode := by
  intro one two same
  cases one <;> cases two <;> simp only [groundedCode, Sum.inl.injEq, Sum.inr.injEq,
    Prod.mk.injEq, reduceCtorEq] at same
  · rw [same]
  · rw [stringNumber_injective same]
  · rw [same]
  · rw [stringNumber_injective same.1, stringNumber_injective same.2]

/-- A naming: strings and grounded values by their codes. -/
def naming : Naming where
  leaf name := Encodable.encode (name.map stringNumber groundedCode)
  unknown := stringNumber

/-- The naming is faithful. -/
theorem naming_faithful : naming.Faithful := by
  refine ⟨fun one two same => ?_, stringNumber_injective⟩
  exact Sum.map_injective.mpr ⟨stringNumber_injective, groundedCode_injective⟩
    (Encodable.encode_injective same)

/-! ## The reference term a spelled term stands for -/

/-- The reference term a term spelled by cells stands for. An expression that is neither
`()` nor a cell stands for none. -/
def referenceOf (N : Naming) : Atom → Option PT
  | .var name => some (.var (N.unknown name))
  | .symbol name => some (.atom (N.leaf (.inl name)))
  | .grounded value => some (.atom (N.leaf (.inr value)))
  | .expression items => referenceItems N items
where
  /-- The same for the items of one expression. -/
  referenceItems (N : Naming) : List Atom → Option PT
    | [] => some .nil
    | [.expression [.expression []], first, rest] =>
        Option.map₂ PT.cons (referenceOf N first) (referenceOf N rest)
    | _ => none

@[simp] theorem referenceOf_var (N : Naming) (name : String) :
    referenceOf N (.var name) = some (.var (N.unknown name)) := by
  simp [referenceOf]

@[simp] theorem referenceOf_symbol (N : Naming) (name : String) :
    referenceOf N (.symbol name) = some (.atom (N.leaf (.inl name))) := by
  simp [referenceOf]

@[simp] theorem referenceOf_grounded (N : Naming) (value : GroundedValue) :
    referenceOf N (.grounded value) = some (.atom (N.leaf (.inr value))) := by
  simp [referenceOf]

@[simp] theorem referenceOf_nil (N : Naming) : referenceOf N (.expression []) = some .nil := by
  simp [referenceOf, referenceOf.referenceItems]

@[simp] theorem referenceOf_cell (N : Naming) (first rest : Atom) :
    referenceOf N (.expression [mark, first, rest]) =
      Option.map₂ PT.cons (referenceOf N first) (referenceOf N rest) := by
  simp [referenceOf, referenceOf.referenceItems, mark]

/-- What an expression with a reading is: `()`, or a cell of two terms with readings. -/
theorem referenceOf_expression {N : Naming} {items : List Atom} {p : PT}
    (reads : referenceOf N (.expression items) = some p) :
    (items = [] ∧ p = .nil) ∨ ∃ first rest a b, items = [mark, first, rest] ∧
      referenceOf N first = some a ∧ referenceOf N rest = some b ∧ p = .cons a b := by
  simp only [referenceOf] at reads
  unfold referenceOf.referenceItems at reads
  split at reads
  · simp only [Option.some.injEq] at reads
    exact .inl ⟨rfl, reads.symm⟩
  · rename_i first rest
    obtain ⟨a, b, firstIs, restIs, same⟩ := PT.map₂_cons_eq_some reads
    exact .inr ⟨first, rest, a, b, rfl, firstIs, restIs, same⟩
  · cases reads

/-- The list a model value is, as a reference term. -/
def reference (N : Naming) : Atom → PT
  | .var name => .var (N.unknown name)
  | .symbol name => .atom (N.leaf (.inl name))
  | .grounded value => .atom (N.leaf (.inr value))
  | .expression items => referenceList N items
where
  /-- The list of these items. -/
  referenceList (N : Naming) : List Atom → PT
    | [] => .nil
    | first :: rest => .cons (reference N first) (referenceList N rest)

/-- A model value, spelled, stands for the list it is. -/
theorem referenceOf_spell (N : Naming) :
    ∀ value : Atom, referenceOf N (spell value) = some (reference N value)
  | .var name => by simp [reference]
  | .symbol name => by simp [reference]
  | .grounded held => by simp [spell, reference]
  | .expression items => by
      rw [spell_expression]
      simpa [reference] using referenceOf_spellItems N items
where
  /-- The same for a list. -/
  referenceOf_spellItems (N : Naming) :
      ∀ items : List Atom,
        referenceOf N (spell.spellItems items) = some (reference.referenceList N items)
    | [] => by simp [reference.referenceList]
    | first :: rest => by
        rw [spellItems_cons, referenceOf_cell, referenceOf_spell N first,
          referenceOf_spellItems N rest]
        rfl

/-- The list or cell a pattern stands for, as a reference term. -/
def referencePattern (N : Naming) : Atom → PT
  | .var name => .var (N.unknown name)
  | .symbol name => .atom (N.leaf (.inl name))
  | .grounded value => .atom (N.leaf (.inr value))
  | .expression items => referenceViewed N items
where
  /-- The items of one expression: the list constructor, or a list of patterns. -/
  referenceViewed (N : Naming) : List Atom → PT
    | [.symbol "cons", first, rest] =>
        .cons (referencePattern N first) (referencePattern N rest)
    | items => referenceEach N items
  /-- A list of patterns. -/
  referenceEach (N : Naming) : List Atom → PT
    | [] => .nil
    | first :: rest => .cons (referencePattern N first) (referenceEach N rest)

/-- An expression is the list constructor applied to two terms, or it is not. -/
theorem view_or_not (items : List Atom) :
    (∃ first rest, items = [.symbol "cons", first, rest]) ∨
      ∀ first rest, items = [.symbol "cons", first, rest] → False := by
  by_cases view : ∃ first rest, items = [.symbol "cons", first, rest]
  · exact .inl view
  · exact .inr fun first rest same => view ⟨first, rest, same⟩

theorem referencePattern_view (N : Naming) (first rest : Atom) :
    referencePattern N (.expression [.symbol "cons", first, rest]) =
      .cons (referencePattern N first) (referencePattern N rest) := by
  simp [referencePattern, referencePattern.referenceViewed]

theorem referencePattern_list (N : Naming) {items : List Atom}
    (notView : ∀ first rest, items = [.symbol "cons", first, rest] → False) :
    referencePattern N (.expression items) = referencePattern.referenceEach N items := by
  simp only [referencePattern]
  unfold referencePattern.referenceViewed
  split
  · exact (notView _ _ rfl).elim
  · rfl

/-- A pattern, read, stands for the list or cell it stands for. -/
theorem referenceOf_readPattern (N : Naming) :
    ∀ pattern : Atom, referenceOf N (readPattern pattern) = some (referencePattern N pattern)
  | .var name => by simp [referencePattern]
  | .symbol name => by simp [referencePattern]
  | .grounded held => by simp [readPattern, referencePattern]
  | .expression items => by
      rcases view_or_not items with ⟨first, rest, shape⟩ | notView
      · have one := referenceOf_readPattern N first
        have others := referenceOf_readPattern N rest
        rw [shape, readPattern_view, referenceOf_cell, one, others, referencePattern_view]
        rfl
      · have each : ∀ item ∈ items,
            referenceOf N (readPattern item) = some (referencePattern N item) :=
          fun item member => referenceOf_readPattern N item
        rw [readPattern_list notView, referencePattern_list N notView]
        clear notView
        induction items with
        | nil => simp [referencePattern.referenceEach]
        | cons head tail ih =>
            rw [readEach_cons, referenceOf_cell, each head List.mem_cons_self,
              ih fun item member => each item (List.mem_cons_of_mem _ member)]
            simp [referencePattern.referenceEach]
termination_by pattern => sizeOf pattern
decreasing_by
  all_goals first
    | (simp_wf; subst shape; simp; omega)
    | (simp_wf; have smaller := List.sizeOf_lt_of_mem member; omega)

/-! ## Unknowns and their values -/

/-- Giving the unknowns of a term with a reading their values is substitution in the
reference, when each value has the reading the substitution gives. -/
theorem referenceOf_instantiate (N : Naming) {σ : Valuation} {θ : ℕ → PT}
    (reads : ∀ name, referenceOf N (σ name) = some (θ (N.unknown name))) :
    ∀ (term : Atom) (p : PT), referenceOf N term = some p →
      referenceOf N (instantiate σ term) = some (p.subst θ)
  | .var name, p, read => by
      simp only [referenceOf_var, Option.some.injEq] at read
      subst read
      simpa [PT.subst] using reads name
  | .symbol name, p, read => by
      simp only [referenceOf_symbol, Option.some.injEq] at read
      subst read
      simp [PT.subst]
  | .grounded held, p, read => by
      simp only [referenceOf_grounded, Option.some.injEq] at read
      subst read
      simp [instantiate, PT.subst]
  | .expression items, p, read => by
      rcases referenceOf_expression read with ⟨empty, isNil⟩ |
        ⟨first, rest, a, b, shape, firstIs, restIs, isCons⟩
      · rw [empty, isNil]
        simp [PT.subst]
      · have one := referenceOf_instantiate N reads first a firstIs
        have others := referenceOf_instantiate N reads rest b restIs
        have markStays : instantiate σ mark = mark := by simp [mark]
        rw [shape, isCons, instantiate_expression, instantiateList_cons, instantiateList_cons,
          instantiateList_cons, instantiateList_nil, markStays, referenceOf_cell, one, others]
        rfl
termination_by term => sizeOf term
decreasing_by all_goals (simp_wf; subst shape; simp; omega)

/-- Under a faithful naming, a reference term is the reading of at most one term. -/
theorem referenceOf_injective (N : Naming) (faithful : N.Faithful) :
    ∀ (left right : Atom) (p : PT), referenceOf N left = some p →
      referenceOf N right = some p → left = right
  | .var name, right, p, leftIs, rightIs => by
      simp only [referenceOf_var, Option.some.injEq] at leftIs
      subst leftIs
      cases right with
      | var other =>
          simp only [referenceOf_var, Option.some.injEq, PT.var.injEq] at rightIs
          rw [faithful.2 rightIs]
      | symbol other => simp at rightIs
      | grounded held => simp at rightIs
      | expression items =>
          rcases referenceOf_expression rightIs with ⟨_, isNil⟩ | ⟨_, _, _, _, _, _, _, isCons⟩
          · cases isNil
          · cases isCons
  | .symbol name, right, p, leftIs, rightIs => by
      simp only [referenceOf_symbol, Option.some.injEq] at leftIs
      subst leftIs
      cases right with
      | var other => simp at rightIs
      | symbol other =>
          simp only [referenceOf_symbol, Option.some.injEq, PT.atom.injEq] at rightIs
          have same := faithful.1 rightIs
          simp only [Sum.inl.injEq] at same
          rw [same]
      | grounded held =>
          simp only [referenceOf_grounded, Option.some.injEq, PT.atom.injEq] at rightIs
          exact absurd (faithful.1 rightIs) (by simp)
      | expression items =>
          rcases referenceOf_expression rightIs with ⟨_, isNil⟩ | ⟨_, _, _, _, _, _, _, isCons⟩
          · cases isNil
          · cases isCons
  | .grounded held, right, p, leftIs, rightIs => by
      simp only [referenceOf_grounded, Option.some.injEq] at leftIs
      subst leftIs
      cases right with
      | var other => simp at rightIs
      | symbol other =>
          simp only [referenceOf_symbol, Option.some.injEq, PT.atom.injEq] at rightIs
          exact absurd (faithful.1 rightIs) (by simp)
      | grounded other =>
          simp only [referenceOf_grounded, Option.some.injEq, PT.atom.injEq] at rightIs
          have same := faithful.1 rightIs
          simp only [Sum.inr.injEq] at same
          rw [same]
      | expression items =>
          rcases referenceOf_expression rightIs with ⟨_, isNil⟩ | ⟨_, _, _, _, _, _, _, isCons⟩
          · cases isNil
          · cases isCons
  | .expression items, right, p, leftIs, rightIs => by
      rcases referenceOf_expression leftIs with ⟨empty, isNil⟩ |
        ⟨first, rest, a, b, shape, firstIs, restIs, isCons⟩
      · subst isNil
        cases right with
        | var other => simp at rightIs
        | symbol other => simp at rightIs
        | grounded held => simp at rightIs
        | expression others =>
            rcases referenceOf_expression rightIs with ⟨alsoEmpty, _⟩ |
              ⟨_, _, _, _, _, _, _, isCons⟩
            · rw [empty, alsoEmpty]
            · cases isCons
      · subst isCons
        cases right with
        | var other => simp at rightIs
        | symbol other => simp at rightIs
        | grounded held => simp at rightIs
        | expression others =>
            rcases referenceOf_expression rightIs with ⟨_, isNil⟩ |
              ⟨first', rest', a', b', shape', firstIs', restIs', isCons'⟩
            · cases isNil
            · simp only [PT.cons.injEq] at isCons'
              obtain ⟨sameA, sameB⟩ := isCons'
              subst sameA sameB
              have firstSame := referenceOf_injective N faithful first first' a firstIs firstIs'
              have restSame := referenceOf_injective N faithful rest rest' b restIs restIs'
              rw [shape, shape', firstSame, restSame]
termination_by left => sizeOf left
decreasing_by all_goals (simp_wf; subst shape; simp; omega)

/-! ## The engine's terms -/

/-- A model value as the engine's term: a flat expression. -/
def embed (N : Naming) : Atom → Tm
  | .var name => .var (N.unknown name)
  | .symbol name => .sym (N.leaf (.inl name))
  | .grounded value => .sym (N.leaf (.inr value))
  | .expression items => .expr (embedList N items)
where
  /-- The same for a list. -/
  embedList (N : Naming) : List Atom → List Tm
    | [] => []
    | first :: rest => embed N first :: embedList N rest

/-- A model value is no bare tag. -/
theorem embed_ne_tag (N : Naming) (value : Atom) : embed N value ≠ Tm.tag := by
  cases value <;> simp [embed]

/-- A model value's expression is no cell. -/
theorem embed_expression_is_no_cell (N : Naming) (items : List Atom) :
    ¬ Tm.IsCell (.expr (embed.embedList N items)) := by
  rintro ⟨head, tail, same⟩
  match items, same with
  | [], same => cases same
  | first :: rest, same =>
      simp only [embed.embedList] at same
      injection same with same
      injection same with firstIs _
      exact embed_ne_tag N first firstIs

/-- The engine reads a model value as the list it is. -/
theorem denote_embed (N : Naming) :
    ∀ value : Atom, (embed N value).denote = some (reference N value)
  | .var name => rfl
  | .symbol name => rfl
  | .grounded held => rfl
  | .expression items => by
      simp only [embed]
      rw [Tm.denote_expr (embed_expression_is_no_cell N items)]
      simpa [reference] using denoteList_embedList N items
where
  /-- The same for a list. -/
  denoteList_embedList (N : Naming) :
      ∀ items : List Atom,
        Tm.denoteList (embed.embedList N items) = some (reference.referenceList N items)
    | [] => rfl
    | first :: rest => by
        simp only [embed.embedList]
        rw [Tm.denoteList_cons, denote_embed N first, denoteList_embedList N rest]
        rfl

/-- A pattern as the engine's term: a cell where the pattern has the list constructor. -/
def embedPattern (N : Naming) : Atom → Tm
  | .var name => .var (N.unknown name)
  | .symbol name => .sym (N.leaf (.inl name))
  | .grounded value => .sym (N.leaf (.inr value))
  | .expression items => embedViewed N items
where
  /-- The items of one expression: the list constructor, or a list of patterns. -/
  embedViewed (N : Naming) : List Atom → Tm
    | [.symbol "cons", first, rest] => Tm.cell (embedPattern N first) (embedPattern N rest)
    | items => .expr (embedEach N items)
  /-- A list of patterns. -/
  embedEach (N : Naming) : List Atom → List Tm
    | [] => []
    | first :: rest => embedPattern N first :: embedEach N rest

theorem embedPattern_view (N : Naming) (first rest : Atom) :
    embedPattern N (.expression [.symbol "cons", first, rest]) =
      Tm.cell (embedPattern N first) (embedPattern N rest) := by
  simp [embedPattern, embedPattern.embedViewed]

theorem embedPattern_list (N : Naming) {items : List Atom}
    (notView : ∀ first rest, items = [.symbol "cons", first, rest] → False) :
    embedPattern N (.expression items) = .expr (embedPattern.embedEach N items) := by
  simp only [embedPattern]
  unfold embedPattern.embedViewed
  split
  · exact (notView _ _ rfl).elim
  · rfl

/-- A pattern that is not the list constructor's is no bare tag. -/
theorem embedPattern_ne_tag (N : Naming) (pattern : Atom) : embedPattern N pattern ≠ Tm.tag := by
  cases pattern with
  | var name => simp [embedPattern]
  | symbol name => simp [embedPattern]
  | grounded held => simp [embedPattern]
  | expression items =>
      simp only [embedPattern]
      unfold embedPattern.embedViewed
      split <;> simp [Tm.cell]

/-- A list of patterns is no cell. -/
theorem embedEach_is_no_cell (N : Naming) (items : List Atom) :
    ¬ Tm.IsCell (.expr (embedPattern.embedEach N items)) := by
  rintro ⟨head, tail, same⟩
  cases items with
  | nil => simp [embedPattern.embedEach, Tm.cell] at same
  | cons first rest =>
      simp only [embedPattern.embedEach, Tm.cell, Tm.expr.injEq, List.cons.injEq] at same
      exact embedPattern_ne_tag N first same.1

/-- The engine reads a pattern as the list or cell it stands for. -/
theorem denote_embedPattern (N : Naming) :
    ∀ pattern : Atom, (embedPattern N pattern).denote = some (referencePattern N pattern)
  | .var name => by simp [embedPattern, referencePattern, Tm.denote]
  | .symbol name => by simp [embedPattern, referencePattern, Tm.denote]
  | .grounded held => by simp [embedPattern, referencePattern, Tm.denote]
  | .expression items => by
      rcases view_or_not items with ⟨first, rest, shape⟩ | notView
      · have one := denote_embedPattern N first
        have others := denote_embedPattern N rest
        rw [shape, embedPattern_view, Tm.denote_cell, one, others, referencePattern_view]
        rfl
      · have each : ∀ item ∈ items,
            (embedPattern N item).denote = some (referencePattern N item) :=
          fun item member => denote_embedPattern N item
        rw [embedPattern_list N notView, Tm.denote_expr (embedEach_is_no_cell N items),
          referencePattern_list N notView]
        clear notView
        induction items with
        | nil => simp [embedPattern.embedEach, referencePattern.referenceEach, Tm.denoteList]
        | cons head tail ih =>
            simp only [embedPattern.embedEach]
            rw [Tm.denoteList_cons, each head List.mem_cons_self,
              ih fun item member => each item (List.mem_cons_of_mem _ member)]
            simp [referencePattern.referenceEach]
termination_by pattern => sizeOf pattern
decreasing_by
  all_goals first
    | (simp_wf; subst shape; simp; omega)
    | (simp_wf; have smaller := List.sizeOf_lt_of_mem member; omega)

/-! ## One fact -/

/-- An equation between the term a pattern stands for and a spelled value holds under a
valuation exactly when the reference substitution of that valuation unifies the engine's
two terms. -/
theorem equation_iff_unifies (N : Naming) (faithful : N.Faithful) {σ : Valuation}
    {θ : ℕ → PT} (reads : ∀ name, referenceOf N (σ name) = some (θ (N.unknown name)))
    (pattern value : Atom) :
    EquationHolds σ (readPattern pattern, spell value) ↔
      Unifies θ (embedPattern N pattern) (embed N value) := by
  have patternReads := referenceOf_instantiate N reads _ _ (referenceOf_readPattern N pattern)
  have valueReads := referenceOf_instantiate N reads _ _ (referenceOf_spell N value)
  constructor
  · intro holds
    unfold EquationHolds at holds
    refine ⟨_, _, denote_embedPattern N pattern, denote_embed N value, ?_⟩
    rw [holds] at patternReads
    exact Option.some.inj (patternReads.symm.trans valueReads)
  · rintro ⟨p, q, patternIs, valueIs, same⟩
    rw [denote_embedPattern] at patternIs
    rw [denote_embed] at valueIs
    cases patternIs
    cases valueIs
    rw [same] at patternReads
    exact referenceOf_injective N faithful _ _ _ patternReads valueReads

/-- **A pattern holds of a value exactly when the reference unifies the engine's terms**,
under any reference substitution that gives each unknown the list its value is. -/
theorem patternHolds_iff_unifies (N : Naming) (faithful : N.Faithful) {ρ : Valuation}
    {θ : ℕ → PT} (agrees : ∀ name, θ (N.unknown name) = reference N (ρ name))
    (pattern value : Atom) :
    PatternHolds ρ pattern value ↔ Unifies θ (embedPattern N pattern) (embed N value) :=
  equation_iff_unifies N faithful
    (fun name => by rw [referenceOf_spell, agrees]) pattern value

/-- The reference substitution of a valuation: each numbered unknown gets the list its
value is. -/
noncomputable def referenceValuation (N : Naming) (ρ : Valuation) : ℕ → PT := fun number =>
  open Classical in
  if named : ∃ name, N.unknown name = number then reference N (ρ (Classical.choose named))
  else .var number

theorem referenceValuation_agrees (N : Naming) (faithful : N.Faithful) (ρ : Valuation)
    (name : String) : referenceValuation N ρ (N.unknown name) = reference N (ρ name) := by
  have named : ∃ other, N.unknown other = N.unknown name := ⟨name, rfl⟩
  unfold referenceValuation
  rw [dif_pos named, faithful.2 (Classical.choose_spec named)]

/-- On a value with no unknowns, the model's pattern unifier answers exactly when some
valuation's reference substitution unifies the engine's pattern and value. -/
theorem unifyAsPattern_accepts_iff_reference_unifies (N : Naming) (faithful : N.Faithful)
    {pattern value : Atom} (ground : Ground value) :
    (∃ bound, unifyAsPattern [] pattern value = .ok bound) ↔
      ∃ ρ : Valuation,
        Unifies (referenceValuation N ρ) (embedPattern N pattern) (embed N value) := by
  rw [unifyAsPattern_accepts_iff idempotent_nil ground]
  constructor
  · rintro ⟨ρ, _, holds⟩
    exact ⟨ρ, (patternHolds_iff_unifies N faithful
      (referenceValuation_agrees N faithful ρ) pattern value).mp holds⟩
  · rintro ⟨ρ, unifies⟩
    refine ⟨ρ, ?_, (patternHolds_iff_unifies N faithful
      (referenceValuation_agrees N faithful ρ) pattern value).mpr unifies⟩
    intro pair member
    simp [presentation] at member

/-- The same with the naming given here: no hypothesis on names is left. -/
theorem unifyAsPattern_accepts_iff_the_reference_unifies {pattern value : Atom}
    (ground : Ground value) :
    (∃ bound, unifyAsPattern [] pattern value = .ok bound) ↔
      ∃ ρ : Valuation,
        Unifies (referenceValuation naming ρ) (embedPattern naming pattern)
          (embed naming value) :=
  unifyAsPattern_accepts_iff_reference_unifies naming naming_faithful ground

/-! ## Controls -/

/-- Positive: the pattern `(cons $a $b)` is the engine's cell of the two variables. -/
theorem pattern_embeds_as_a_cell (N : Naming) :
    embedPattern N (.expression [.symbol "cons", .var "a", .var "b"]) =
      Tm.cell (.var (N.unknown "a")) (.var (N.unknown "b")) := by
  simp [embedPattern, embedPattern.embedViewed]

/-- Negative: the data `(cons p q)` is no cell of the engine. -/
theorem data_headed_by_cons_embeds_as_no_cell (N : Naming) :
    ¬ Tm.IsCell (embed N (.expression [.symbol "cons", .symbol "p", .symbol "q"])) :=
  embed_expression_is_no_cell N _

end Mettapedia.Languages.MeTTa.PeTTa.ListView
