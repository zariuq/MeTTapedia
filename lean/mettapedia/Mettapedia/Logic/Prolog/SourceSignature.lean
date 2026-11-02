import Mettapedia.Logic.Prolog.Syntax

/-!
# Concrete source signature for Prolog text

This module instantiates the canonical `Logic.LP` representation with the
symbols and atomic values needed by a Prolog reader. Predicate and compound
symbols include their arity, matching SWI-Prolog's predicate-indicator and
functor discipline. Atoms and zero-arity compounds such as `f()` remain
distinct, as they are in modern SWI-Prolog.

Variables carry an occurrence identity in addition to their source spelling.
A reader can therefore share repeated named variables while assigning every
anonymous `_` occurrence a distinct identity before the ordinary LP
standardize-apart pass adds an activation scope.
-/

namespace Mettapedia.Logic.Prolog.SourceSignature

/-- Atomic Prolog data retained without passing through a host-language
number or string conversion. IEEE floats are stored by their 64-bit payload
so NaNs and signed zero remain distinguishable. -/
inductive Constant where
  /-- SWI's empty-list constant, distinct from the ordinary atom named `[]`. -/
  | nil
  | atom (name : String)
  | integer (value : Int)
  | floatBits (bits : UInt64)
  | string (value : String)
  /-- Opaque stable identity returned by `asserta/2` and `assertz/2`.
  The source reader has no constructor for this case, so a program cannot
  forge a database occurrence reference from textual syntax. -/
  | clauseReference (reference : Nat)
deriving DecidableEq, Repr

/-- Clause- or query-local source variable identity. -/
structure Variable where
  spelling : String
  occurrence : Nat
deriving DecidableEq, Repr

/-- Prolog predicates are identified by both name and arity. -/
structure PredicateIndicator where
  name : String
  arity : Nat
deriving DecidableEq, Repr

/-- Compound identity includes arity. Arity zero represents explicit `f()`
syntax and remains distinct from the atom `f`. -/
structure CompoundIndicator where
  name : String
  arity : Nat
deriving DecidableEq, Repr

/-- The concrete signature consumed by the source reader and the same LP
runtime used by hand-constructed and verified programs. -/
@[reducible]
def signature : LP.LPSignature where
  constants := Constant
  vars := Variable
  relationSymbols := PredicateIndicator
  relationArity := PredicateIndicator.arity
  functionSymbols := CompoundIndicator
  functionArity := CompoundIndicator.arity

abbrev Term := LP.Term signature
abbrev Atom := LP.Atom signature
abbrev Goal := Prolog.Goal signature
abbrev Clause := Prolog.Clause signature
abbrev Program := Prolog.Program signature

def atom (name : String) : Term := .const (.atom name)
def integer (value : Int) : Term := .const (.integer value)
def floatBits (bits : UInt64) : Term := .const (.floatBits bits)
def string (value : String) : Term := .const (.string value)
def clauseReference (reference : Nat) : Term :=
  .const (.clauseReference reference)
def var (spelling : String) (occurrence : Nat) : Term :=
  .var { spelling, occurrence }

/-- Build a compound whose arity index is exactly its ordered argument-list
length. The empty list constructs explicit zero-arity compound syntax. -/
def compound (name : String) (args : List Term) : Term :=
  .app { name, arity := args.length } args.get

/-- Build one relation atom with arity exactly equal to its ordered argument
list length. Name-equal predicates at different arities remain distinct. -/
def predicate (name : String) (args : List Term) : Atom := {
  symbol := { name, arity := args.length }
  args := args.get
}

def call (name : String) (args : List Term) : Goal :=
  .call (predicate name args)

/-- The source dialect chooses its actual nil constant and cons functor.
This dictionary changes notation without collapsing distinct source atoms. -/
structure ListEncoding where
  nilConstant : Constant
  consName : String
  deriving DecidableEq, Repr

def ListEncoding.nil (encoding : ListEncoding) : Term := .const encoding.nilConstant

def ListEncoding.cons (encoding : ListEncoding) (head tail : Term) : Term :=
  compound encoding.consName [head,tail]

def ListEncoding.list (encoding : ListEncoding) (elements : List Term) (tail : Term := encoding.nil) : Term :=
  elements.foldr encoding.cons tail

def swiLists : ListEncoding := ⟨.nil, "[|]"⟩
def isoLists : ListEncoding := ⟨.atom "[]", "."⟩

/-- The existing source-runtime services use the SWI list representation. -/
def nil : Term := swiLists.nil
def cons (head tail : Term) : Term := swiLists.cons head tail
def list (elements : List Term) (tail : Term := nil) : Term := swiLists.list elements tail

theorem swi_nil_ne_atom : nil ≠ atom "[]" := by intro equal; cases equal

@[simp]
theorem predicate_arity (name : String) (args : List Term) :
    (predicate name args).symbol.arity = args.length := rfl

theorem predicate_same_name_different_arity
    (name : String) (left right : List Term)
    (different : left.length ≠ right.length) :
    (predicate name left).symbol ≠ (predicate name right).symbol := by
  intro equal
  exact different (congrArg PredicateIndicator.arity equal)

theorem anonymous_occurrences_distinct (first second : Nat)
    (different : first ≠ second) :
    ({ spelling := "_", occurrence := first } : Variable) ≠
      { spelling := "_", occurrence := second } := by
  intro equal
  exact different (congrArg Variable.occurrence equal)

theorem atom_ne_zero_arity_compound (name : String) :
    atom name ≠ compound name [] := by
  intro equal
  cases equal

end Mettapedia.Logic.Prolog.SourceSignature
