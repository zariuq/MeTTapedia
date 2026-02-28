import Mettapedia.Logic.Datalog.Core
import Mathlib.Data.Finset.Image

/-!
# Datalog Substitution and Grounding

A **grounding** maps every variable to a constant, turning a rule into a ground rule.
This is the key operation for the immediate consequence operator T_P.

## Design

- `Grounding τ = τ.vars → τ.constants` — total substitution (all vars get a value).
  For the T_P operator we only need total groundings (range-restricted rules guarantee
  this is sufficient).
- `Grounding.applyTerm`, `applyAtom`, `applyBody`, `applyRule` — functorial action.
- Key lemma: `applyAtom_length` — grounding preserves atom arity.
- `groundBodySatisfied` — a grounded body is satisfied by an interpretation.
-/

namespace Mettapedia.Logic.Datalog

/-! ## Section 1: Groundings -/

/-- A grounding: a total assignment of constants to variables. -/
abbrev Grounding (τ : Signature) := τ.vars → τ.constants

/-- Apply a grounding to a term: constants are preserved, variables are substituted. -/
def Grounding.applyTerm {τ : Signature} (g : Grounding τ) : Term τ → τ.constants
  | .constant c   => c
  | .variableDL v => g v

/-- Apply a grounding to a list of terms. -/
def Grounding.applyTermList {τ : Signature} (g : Grounding τ)
    (ts : List (Term τ)) : List τ.constants :=
  ts.map g.applyTerm

/-- Applying a grounding preserves list length. -/
@[simp]
theorem Grounding.applyTermList_length {τ : Signature} (g : Grounding τ)
    (ts : List (Term τ)) :
    (g.applyTermList ts).length = ts.length := by
  simp [Grounding.applyTermList]

/-! ## Section 2: Grounding atoms -/

/-- Apply a grounding to an atom, yielding a ground atom. -/
def Grounding.applyAtom {τ : Signature} (g : Grounding τ) (a : Atom τ) : GroundAtom τ where
  symbol      := a.symbol
  atom_terms  := g.applyTermList a.atom_terms
  term_length := by simp [a.term_length]

/-- Grounding a ground atom's coercion is the identity. -/
@[simp]
theorem Grounding.applyAtom_toAtom {τ : Signature} (g : Grounding τ)
    (ga : GroundAtom τ) :
    g.applyAtom ga.toAtom = ga := by
  simp only [Grounding.applyAtom, GroundAtom.toAtom, Grounding.applyTermList,
             List.map_map]
  ext
  · rfl
  · simp [Grounding.applyTerm]

/-- Apply a grounding to a list of atoms. -/
def Grounding.applyBody {τ : Signature} (g : Grounding τ)
    (body : List (Atom τ)) : List (GroundAtom τ) :=
  body.map g.applyAtom

/-- The number of body atoms is preserved under grounding. -/
@[simp]
theorem Grounding.applyBody_length {τ : Signature} (g : Grounding τ)
    (body : List (Atom τ)) :
    (g.applyBody body).length = body.length := by
  simp [Grounding.applyBody]

/-! ## Section 3: Grounding rules -/

/-- Apply a grounding to a rule, yielding a ground rule. -/
def Grounding.applyRule {τ : Signature} (g : Grounding τ) (r : Rule τ) : GroundRule τ where
  head := g.applyAtom r.head
  body := g.applyBody r.body

/-! ## Section 4: Satisfaction -/

/-- A grounded body is satisfied by interpretation `I` when every ground atom is in `I`. -/
def groundBodySatisfied {τ : Signature}
    (body : List (GroundAtom τ)) (I : Interpretation τ) : Prop :=
  ∀ a ∈ body, a ∈ I

/-- Satisfaction is monotone: larger interpretations satisfy more bodies. -/
theorem groundBodySatisfied_mono {τ : Signature}
    (body : List (GroundAtom τ)) {I J : Interpretation τ} (hIJ : I ⊆ J)
    (h : groundBodySatisfied body I) : groundBodySatisfied body J := by
  intro a ha
  exact hIJ (h a ha)

/-- For a finite interpretation, satisfaction is decidable when equality is decidable. -/
def finBodySatisfied {τ : Signature} [DecidableEq τ.constants] [DecidableEq τ.relationSymbols]
    (body : List (GroundAtom τ)) (I : FinInterpretation τ) : Bool :=
  body.all (· ∈ I)

theorem finBodySatisfied_iff {τ : Signature} [DecidableEq τ.constants]
    [DecidableEq τ.relationSymbols]
    (body : List (GroundAtom τ)) (I : FinInterpretation τ) :
    finBodySatisfied body I = true ↔ groundBodySatisfied body ↑I := by
  simp [finBodySatisfied, groundBodySatisfied, List.all_eq_true, decide_eq_true_eq]

/-! ## Section 5: Variable collection via grounding -/

/-- The set of constants that a grounding assigns to the variables of an atom. -/
def Grounding.constantsOf {τ : Signature} [DecidableEq τ.constants] [DecidableEq τ.vars]
    (g : Grounding τ) (a : Atom τ) : Finset τ.constants :=
  a.vars.image g

end Mettapedia.Logic.Datalog
