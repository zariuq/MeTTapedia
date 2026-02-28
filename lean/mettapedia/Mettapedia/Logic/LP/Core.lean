import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Logic Programming Kernel: Core Types

First-order logic programming syntax over an arbitrary signature with function symbols.
Generalizes `Mettapedia.Logic.Datalog.Core` by allowing compound terms.

## Design choices

- `LPSignature` extends Datalog's `Signature` with function symbols and their arities.
- `Term σ` uses Fin-indexed arguments for function application (matching Foundation's
  `Semiterm` pattern), enabling clean structural recursion.
- Both finite (Fintype) and infinite Herbrand universes are supported.
- `LPSignature.isFunctionFree` characterizes the Datalog restriction.

## References

- Lloyd, *Foundations of Logic Programming*, 2nd ed., 1987
- van Emden & Kowalski, "Semantics of predicate logic as a programming language", 1976
- Tantow et al., *Certifying Datalog Reasoning in Lean 4*, ITP 2025
-/

namespace Mettapedia.Logic.LP

/-! ## Section 1: Signatures -/

/-- A logic programming signature: relation symbols, function symbols, and their arities. -/
structure LPSignature where
  /-- Domain of constant symbols (0-ary terms). -/
  constants       : Type*
  /-- Domain of variables. -/
  vars            : Type*
  /-- Predicate/relation symbols. -/
  relationSymbols : Type*
  /-- Arity of each relation symbol. -/
  relationArity   : relationSymbols → ℕ
  /-- Function symbols (non-constant). -/
  functionSymbols : Type*
  /-- Arity of each function symbol. -/
  functionArity   : functionSymbols → ℕ

/-- A signature is function-free when it has no function symbols (= Datalog territory). -/
def LPSignature.isFunctionFree (σ : LPSignature) : Prop :=
  IsEmpty σ.functionSymbols

/-! ## Section 2: Terms -/

/-- A first-order term over an LP signature.
    - `var v`: a variable
    - `const c`: a constant (0-ary function)
    - `app f ts`: a function symbol applied to Fin-indexed subterms -/
inductive Term (σ : LPSignature) : Type* where
  | var   : σ.vars → Term σ
  | const : σ.constants → Term σ
  | app   : (f : σ.functionSymbols) → (Fin (σ.functionArity f) → Term σ) → Term σ

/-- Structural size of a term (for well-founded recursion). -/
def Term.size {σ : LPSignature} : Term σ → ℕ
  | .var _    => 1
  | .const _  => 1
  | .app f ts => 1 + ∑ i : Fin (σ.functionArity f), (ts i).size

theorem Term.size_pos {σ : LPSignature} (t : Term σ) : 0 < t.size := by
  cases t with
  | var _ => simp [Term.size]
  | const _ => simp [Term.size]
  | app f ts => simp [Term.size]

theorem Term.size_subterm {σ : LPSignature} {f : σ.functionSymbols}
    {ts : Fin (σ.functionArity f) → Term σ} (i : Fin (σ.functionArity f)) :
    (ts i).size < (Term.app f ts).size := by
  simp only [Term.size]
  have h : (ts i).size ≤ ∑ j : Fin (σ.functionArity f), (ts j).size :=
    Finset.single_le_sum (f := fun j => (ts j).size)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- The set of variables occurring in a term. -/
def Term.freeVars {σ : LPSignature} [DecidableEq σ.vars] : Term σ → Finset σ.vars
  | .var v    => {v}
  | .const _  => ∅
  | .app _ ts => Finset.biUnion Finset.univ (fun i => (ts i).freeVars)

/-- A term is ground if it contains no variables. -/
def Term.isGround {σ : LPSignature} : Term σ → Prop
  | .var _    => False
  | .const _  => True
  | .app _ ts => ∀ i, (ts i).isGround

private theorem biUnion_univ_eq_empty {α : Type*} [Fintype α] {β : Type*} [DecidableEq β]
    {t : α → Finset β} :
    Finset.univ.biUnion t = ∅ ↔ ∀ i, t i = ∅ := by
  constructor
  · intro h i
    exact Finset.subset_empty.mp (h ▸ Finset.subset_biUnion_of_mem t (Finset.mem_univ i))
  · intro h
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩; rw [h i] at hi; simp at hi
    · simp

theorem Term.isGround_iff_freeVars_empty {σ : LPSignature} [DecidableEq σ.vars]
    (t : Term σ) : t.isGround ↔ t.freeVars = ∅ := by
  induction t with
  | var v => simp [isGround, freeVars]
  | const _ => simp [isGround, freeVars]
  | app f ts ih =>
    simp only [isGround, freeVars]
    rw [biUnion_univ_eq_empty]
    exact ⟨fun h i => (ih i).mp (h i), fun h i => (ih i).mpr (h i)⟩

/-! ## Section 3: Atoms -/

/-- An atom: a relation symbol applied to Fin-indexed terms. -/
@[ext]
structure Atom (σ : LPSignature) where
  /-- The predicate symbol. -/
  symbol : σ.relationSymbols
  /-- Arguments, indexed by position. -/
  args   : Fin (σ.relationArity symbol) → Term σ

/-- Variables occurring in an atom. -/
def Atom.freeVars {σ : LPSignature} [DecidableEq σ.vars] (a : Atom σ) : Finset σ.vars :=
  Finset.biUnion Finset.univ (fun i => (a.args i).freeVars)

/-- An atom is ground if all its arguments are ground. -/
def Atom.isGround {σ : LPSignature} (a : Atom σ) : Prop :=
  ∀ i, (a.args i).isGround

/-! ## Section 4: Ground Terms and Ground Atoms -/

/-- A ground term: a term with no variables.
    Uses constants and function symbols only. -/
inductive GroundTerm (σ : LPSignature) : Type* where
  | const : σ.constants → GroundTerm σ
  | app   : (f : σ.functionSymbols) → (Fin (σ.functionArity f) → GroundTerm σ) → GroundTerm σ

/-- Lift a ground term to a general term. -/
def GroundTerm.toTerm {σ : LPSignature} : GroundTerm σ → Term σ
  | .const c  => .const c
  | .app f ts => .app f (fun i => (ts i).toTerm)

instance {σ : LPSignature} : Coe (GroundTerm σ) (Term σ) where
  coe := GroundTerm.toTerm

theorem GroundTerm.toTerm_isGround {σ : LPSignature} (gt : GroundTerm σ) :
    gt.toTerm.isGround := by
  induction gt with
  | const _ => exact trivial
  | app _ _ ih => exact fun i => ih i

/-- A ground atom: a relation symbol applied to ground terms. -/
@[ext]
structure GroundAtom (σ : LPSignature) where
  symbol : σ.relationSymbols
  args   : Fin (σ.relationArity symbol) → GroundTerm σ

/-- Lift a ground atom to a general atom. -/
def GroundAtom.toAtom {σ : LPSignature} (ga : GroundAtom σ) : Atom σ where
  symbol := ga.symbol
  args   := fun i => (ga.args i).toTerm

instance {σ : LPSignature} : Coe (GroundAtom σ) (Atom σ) where
  coe := GroundAtom.toAtom

theorem GroundAtom.toAtom_isGround {σ : LPSignature} (ga : GroundAtom σ) :
    ga.toAtom.isGround :=
  fun i => GroundTerm.toTerm_isGround (ga.args i)

/-! ## Section 5: Clauses and Programs -/

/-- A definite clause: `head :- body₁, body₂, …`
    A fact is a clause with empty body. -/
@[ext]
structure Clause (σ : LPSignature) where
  /-- The head atom. -/
  head : Atom σ
  /-- The body atoms (conjunction). -/
  body : List (Atom σ)

/-- A logic program: a finite list of definite clauses. -/
abbrev Program (σ : LPSignature) := List (Clause σ)

/-- A ground clause: head and body are ground atoms. -/
@[ext]
structure GroundClause (σ : LPSignature) where
  head : GroundAtom σ
  body : List (GroundAtom σ)

/-! ## Section 6: Database and KnowledgeBase -/

/-- An extensional database: a set of ground atoms. -/
abbrev Database (σ : LPSignature) := Set (GroundAtom σ)

/-- A finite extensional database. -/
abbrev FinDatabase (σ : LPSignature) := Finset (GroundAtom σ)

/-- An LP knowledge base: intensional rules + extensional facts. -/
structure KnowledgeBase (σ : LPSignature) where
  prog : Program σ
  db   : Set (GroundAtom σ)

/-- A finite knowledge base (for decidable evaluation). -/
structure FinKnowledgeBase (σ : LPSignature) where
  prog : Program σ
  db   : Finset (GroundAtom σ)

/-- Lift a finite knowledge base to a general one. -/
def FinKnowledgeBase.toKB {σ : LPSignature} (fkb : FinKnowledgeBase σ) : KnowledgeBase σ where
  prog := fkb.prog
  db   := ↑fkb.db

/-! ## Section 7: Interpretations -/

/-- A Herbrand interpretation: a set of ground atoms.
    `Set` gives us a complete lattice for fixpoint constructions. -/
abbrev Interpretation (σ : LPSignature) := Set (GroundAtom σ)

/-- A finite Herbrand interpretation. -/
abbrev FinInterpretation (σ : LPSignature) := Finset (GroundAtom σ)

/-! ## Section 8: Variable helpers -/

/-- Variables appearing in a list of atoms. -/
def Atom.freeVarsOfList {σ : LPSignature} [DecidableEq σ.vars]
    (atoms : List (Atom σ)) : Finset σ.vars :=
  atoms.foldl (fun acc a => acc ∪ a.freeVars) ∅

/-- Variables appearing in a clause. -/
def Clause.freeVars {σ : LPSignature} [DecidableEq σ.vars] (c : Clause σ) : Finset σ.vars :=
  c.head.freeVars ∪ Atom.freeVarsOfList c.body

/-- A clause is *range-restricted* if every head variable appears in the body. -/
def Clause.rangeRestricted {σ : LPSignature} [DecidableEq σ.vars] (c : Clause σ) : Prop :=
  c.head.freeVars ⊆ Atom.freeVarsOfList c.body

end Mettapedia.Logic.LP
