import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic

/-!
# Datalog Core: Signature, Term, Atom, Rule, KnowledgeBase

Foundational syntax for Datalog over an arbitrary signature.

## Design choices

- `Signature` bundles relation symbols and their arities (following CertifyingDatalog).
- `Term τ` is inductive: `constant` or `variableDL` (same names as CertifyingDatalog).
- `Atom τ` carries `atom_terms : List (Term τ)` with an explicit `term_length` proof.
- **Ground atoms**: use `GroundAtom τ` (constants-only list), isomorphic to
  `Atom τ` with `vars τ = ∅`.  A `Coe` makes ground atoms usable as atoms.
- `KnowledgeBase τ` bundles `prog : Program τ` (intensional rules) and
  `db : Database τ` (extensional ground facts).

## References

- Ullman, *Principles of Database and Knowledge-Base Systems*, 1989
- Tantow et al., *Certifying Datalog Reasoning in Lean 4*, 2024
  (CertifyingDatalog repo — patterns reused here under Mettapedia style)
-/

namespace Mettapedia.Logic.Datalog

/-! ## Section 1: Signatures -/

/-- A relational signature: relation symbols and their arities. -/
structure Signature where
  /-- Relation symbols (e.g. `edge`, `ancestor`). -/
  constants       : Type*
  vars            : Type*
  relationSymbols : Type*
  relationArity   : relationSymbols → ℕ

/-! ## Section 2: Terms and Atoms -/

/-- A first-order term over signature `τ`. -/
inductive Term (τ : Signature) : Type* where
  | constant   : τ.constants → Term τ
  | variableDL : τ.vars      → Term τ

instance {τ : Signature} [DecidableEq τ.constants] [DecidableEq τ.vars] :
    DecidableEq (Term τ)
  | .constant c,   .constant c'   => if h : c = c' then isTrue (by rw [h]) else
                                      isFalse (by intro h'; cases h'; exact h rfl)
  | .variableDL v, .variableDL v' => if h : v = v' then isTrue (by rw [h]) else
                                      isFalse (by intro h'; cases h'; exact h rfl)
  | .constant _,   .variableDL _  => isFalse (by intro h; cases h)
  | .variableDL _, .constant _    => isFalse (by intro h; cases h)

/-- The set of variables appearing in a term. -/
def Term.vars {τ : Signature} [DecidableEq τ.vars] : Term τ → Finset τ.vars
  | .constant _   => ∅
  | .variableDL v => {v}

/-- An atom: a relation symbol applied to a list of terms of the right length. -/
@[ext]
structure Atom (τ : Signature) where
  symbol     : τ.relationSymbols
  atom_terms : List (Term τ)
  term_length : atom_terms.length = τ.relationArity symbol

instance {τ : Signature} [DecidableEq τ.constants] [DecidableEq τ.vars]
    [DecidableEq τ.relationSymbols] : DecidableEq (Atom τ)
  | a, b =>
    if hs : a.symbol = b.symbol then
      if ht : a.atom_terms = b.atom_terms then
        isTrue (by ext; exact hs; simp [ht])
      else isFalse (by intro h; cases h; exact ht rfl)
    else isFalse (by intro h; cases h; exact hs rfl)

/-- The set of all variables appearing in an atom. -/
def Atom.vars {τ : Signature} [DecidableEq τ.vars] (a : Atom τ) : Finset τ.vars :=
  a.atom_terms.foldl (fun acc t => acc ∪ t.vars) ∅

/-! ## Section 3: Ground Atoms (variables = Empty) -/

/-- A ground atom: all terms are constants (no variables).
    Represented as a list of constants with the arity proof. -/
@[ext]
structure GroundAtom (τ : Signature) where
  symbol     : τ.relationSymbols
  atom_terms : List τ.constants
  term_length : atom_terms.length = τ.relationArity symbol

instance {τ : Signature} [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] :
    DecidableEq (GroundAtom τ)
  | a, b =>
    if hs : a.symbol = b.symbol then
      if ht : a.atom_terms = b.atom_terms then
        isTrue (by ext; exact hs; simp [ht])
      else isFalse (by intro h; cases h; exact ht rfl)
    else isFalse (by intro h; cases h; exact hs rfl)

/-- Lift a ground atom to a full atom by wrapping constants as `Term.constant`. -/
def GroundAtom.toAtom {τ : Signature} (ga : GroundAtom τ) : Atom τ where
  symbol      := ga.symbol
  atom_terms  := ga.atom_terms.map Term.constant
  term_length := by rw [List.length_map]; exact ga.term_length

instance {τ : Signature} : Coe (GroundAtom τ) (Atom τ) where
  coe := GroundAtom.toAtom

/-- A ground atom's atom has empty variable set. -/
theorem GroundAtom.vars_empty {τ : Signature} [DecidableEq τ.vars] (ga : GroundAtom τ) :
    ga.toAtom.vars = ∅ := by
  simp only [GroundAtom.toAtom, Atom.vars]
  suffices h : ∀ (l : List τ.constants) (acc : Finset τ.vars),
      List.foldl (fun a t => a ∪ Term.vars t) acc (List.map Term.constant l) = acc by
    exact h _ _
  intro l
  induction l with
  | nil => simp
  | cons c rest ih =>
    intro acc
    simp only [List.map_cons, List.foldl_cons]
    rw [show Term.vars (Term.constant c) = (∅ : Finset τ.vars) from rfl]
    have : acc ∪ (∅ : Finset τ.vars) = acc := by show acc ⊔ ⊥ = acc; exact sup_bot_eq acc
    rw [this]
    exact ih acc

/-! ## Section 4: Rules and Programs -/

/-- A Datalog rule: a head atom and a list of body atoms (over the same signature). -/
@[ext]
structure Rule (τ : Signature) where
  head : Atom τ
  body : List (Atom τ)

instance {τ : Signature} [DecidableEq τ.constants] [DecidableEq τ.vars]
    [DecidableEq τ.relationSymbols] : DecidableEq (Rule τ)
  | r, s =>
    if hh : r.head = s.head then
      if hb : r.body = s.body then
        isTrue (Rule.ext hh hb)
      else isFalse (by intro h; cases h; exact hb rfl)
    else isFalse (by intro h; cases h; exact hh rfl)

/-- A Datalog program: a finite list of rules. -/
abbrev Program (τ : Signature) := List (Rule τ)

/-- A ground rule: head and body are all ground atoms. -/
@[ext]
structure GroundRule (τ : Signature) where
  head : GroundAtom τ
  body : List (GroundAtom τ)

/-! ## Section 5: Database and KnowledgeBase -/

/-- An extensional database: a finite set of ground atoms (EDB facts). -/
abbrev Database (τ : Signature) := Finset (GroundAtom τ)

/-- A Datalog knowledge base: intensional rules + extensional ground facts. -/
structure KnowledgeBase (τ : Signature) where
  prog : Program τ
  db   : Database τ

/-! ## Section 6: Interpretations -/

/-- A Herbrand interpretation: a set of ground atoms.
    We use `Set` here for the fixpoint construction (powerset is a complete lattice).
    Finite interpretations use `Finset`, lifted to `Set` via `Finset.toSet`. -/
abbrev Interpretation (τ : Signature) := Set (GroundAtom τ)

/-- A finite Herbrand interpretation. -/
abbrev FinInterpretation (τ : Signature) := Finset (GroundAtom τ)

/-! ## Section 7: Variable collection helpers -/

/-- Variables appearing in a list of atoms. -/
def Atom.varsOfList {τ : Signature} [DecidableEq τ.vars]
    (atoms : List (Atom τ)) : Finset τ.vars :=
  atoms.foldl (fun acc a => acc ∪ a.vars) ∅

/-- A rule is *range-restricted* if every head variable appears in the body.
    This ensures grounding is finite when `τ.constants` is `Fintype`. -/
def Rule.rangeRestricted {τ : Signature} [DecidableEq τ.vars] (r : Rule τ) : Prop :=
  r.head.vars ⊆ Atom.varsOfList r.body

end Mettapedia.Logic.Datalog
