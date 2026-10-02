import Mettapedia.Languages.VibeITP.Spec.Basic

/-!
# Vibe-ITP specification: kernel term operations and primitive theorems

The kernel's term operations are stated exactly, including the traversal
pruning that decides where word arithmetic is performed, because the reference
kernel refuses an operation whenever one of those word computations would
wrap.  With realistic binder counts no such refusal can occur; the conditions
are nevertheless part of what the checker accepts.

* `shift` moves free bound variables at or above a cutoff.  Terms whose depth
  does not exceed the cutoff are returned unchanged without traversal.
* `substBVars` plugs arguments for the outermost bound variables of a body.
* `instantiate` replaces every application of one free-variable symbol by its
  value, with the application's arguments plugged in.  Subterms without any
  free-variable application are returned unchanged without traversal.

The primitive literal theorems use the kernel's number literals: one byte below
256 and the eight-byte little-endian word otherwise.  Addition and
multiplication wrap modulo `2 ^ 64`; there is no division theorem for a zero
divisor and no ordering theorem unless the first number is smaller.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec

/-! ## Shifting -/

mutual
/-- Shift every free bound variable at or above `cutoff` by `amount`. -/
def shift (sig : Sig) (amount : Nat) : Nat → Term → Option Term
  | cutoff, .bvar b =>
      if amount = 0 ∨ b + 1 ≤ cutoff then some (.bvar b)
      else if b + amount + 1 < wordBound then some (.bvar (b + amount))
      else none
  | _, .lit bytes => some (.lit bytes)
  | cutoff, .app s args =>
      if amount = 0 ∨ depth sig (.app s args) ≤ cutoff then some (.app s args)
      else (shiftArgs sig amount s cutoff 0 args).map (.app s)

/-- Shift the arguments of head `s`; argument `index` lies under the head's
binders at that position, whose cumulative count must remain a word. -/
def shiftArgs (sig : Sig) (amount : Nat) (s : SymId) (cutoff : Nat) :
    Nat → List Term → Option (List Term)
  | _, [] => some []
  | index, a :: as =>
      if cutoff + binderAt sig s index < wordBound then
        match shift sig amount (cutoff + binderAt sig s index) a,
            shiftArgs sig amount s cutoff (index + 1) as with
        | some a', some as' => some (a' :: as')
        | _, _ => none
      else none
end

/-! ## Plugging arguments for bound variables -/

mutual
/-- Plug `args` for the bound variables `offset + numArgs - 1, ..., offset`;
argument `numArgs - 1 - k` replaces variable `offset + k` and is shifted by
the number of binders crossed. -/
def substGo (sig : Sig) (numArgs : Nat) (args : List Term) :
    Nat → Term → Option Term
  | offset, .bvar b =>
      if b + 1 ≤ offset then some (.bvar b)
      else if b - offset < numArgs then
        shift sig offset 0 (args.getD (numArgs - 1 - (b - offset)) (.bvar 0))
      else if b - offset + 1 < wordBound then some (.bvar (b - offset))
      else none
  | _, .lit bytes => some (.lit bytes)
  | offset, .app s as =>
      if depth sig (.app s as) ≤ offset then some (.app s as)
      else (substGoArgs sig numArgs args s offset 0 as).map (.app s)

def substGoArgs (sig : Sig) (numArgs : Nat) (args : List Term) (s : SymId)
    (offset : Nat) : Nat → List Term → Option (List Term)
  | _, [] => some []
  | index, a :: as =>
      if offset + binderAt sig s index < wordBound then
        match substGo sig numArgs args (offset + binderAt sig s index) a,
            substGoArgs sig numArgs args s offset (index + 1) as with
        | some a', some as' => some (a' :: as')
        | _, _ => none
      else none
end

/-- Plug `args` into `body` at binder depth `offset`.  With no arguments the
body is returned unchanged. -/
def substBVars (sig : Sig) (numArgs : Nat) (args : List Term) (body : Term)
    (offset : Nat) : Option Term :=
  if numArgs = 0 then some body else substGo sig numArgs args offset body

/-! ## Instantiating a free variable -/

mutual
/-- Replace the applications of free variable `F` (of arity `arity`) by
`value`, whose bound variables `arity - 1, ..., 0` stand for the arguments. -/
def instGo (sig : Sig) (F : SymId) (arity : Nat) (value : Term) :
    Nat → Term → Option Term
  | _, .bvar b => some (.bvar b)
  | _, .lit bytes => some (.lit bytes)
  | offset, .app s as =>
      if hasFvar sig (.app s as) = false then some (.app s as)
      else
        match instArgs sig F arity value s offset 0 as with
        | none => none
        | some as' =>
            if s = F then
              match shift sig offset arity value with
              | none => none
              | some value' => substBVars sig arity as' value' 0
            else some (.app s as')

def instArgs (sig : Sig) (F : SymId) (arity : Nat) (value : Term) (s : SymId)
    (offset : Nat) : Nat → List Term → Option (List Term)
  | _, [] => some []
  | index, a :: as =>
      if offset + binderAt sig s index < wordBound then
        match instGo sig F arity value (offset + binderAt sig s index) a,
            instArgs sig F arity value s offset (index + 1) as with
        | some a', some as' => some (a' :: as')
        | _, _ => none
      else none
end

/-- The kernel's instantiation rule on a theorem statement: the symbol must
be a free variable, the value may use at most its arity of outer bound
variables, and the result must be closed. -/
def instantiateStatement (sig : Sig) (F : SymId) (value statement : Term) :
    Option Term :=
  match sig F with
  | some info =>
      if info.kind = .fvar ∧ depth sig value ≤ info.arity then
        match instGo sig F info.arity value 0 statement with
        | some result => if depth sig result = 0 then some result else none
        | none => none
      else none
  | none => none

/-! ## Primitive theorems about literals -/

def litIsNatStatement (n : Nat) : Term :=
  .app (.builtin .litIsNat) [.natLit n]

def litLtStatement (a b : Nat) : Term :=
  .app (.builtin .litLt) [.natLit a, .natLit b]

def litAddStatement (a b : Nat) : Term :=
  .eq (.app (.builtin .litAdd) [.natLit a, .natLit b]) (.natLit ((a + b) % wordBound))

def litMulStatement (a b : Nat) : Term :=
  .eq (.app (.builtin .litMul) [.natLit a, .natLit b]) (.natLit ((a * b) % wordBound))

def litDivStatement (a b : Nat) : Term :=
  .eq (.app (.builtin .litDiv) [.natLit a, .natLit b]) (.natLit (a / b))

def litLengthStatement (bytes : List UInt8) : Term :=
  .eq (.app (.builtin .litLength) [.lit bytes]) (.natLit bytes.length)

def litGetStatement (bytes : List UInt8) (index : Nat) : Term :=
  .eq (.app (.builtin .litGet) [.lit bytes, .natLit index])
    (.natLit (bytes.getD index 0).toNat)

/-! ## Definitions -/

mutual
/-- Heads of free-variable applications in preorder. -/
def fvarOccurrences (sig : Sig) : Term → List SymId
  | .bvar _ => []
  | .lit _ => []
  | .app s args =>
      (if isFvarSym sig s then [s] else []) ++ fvarOccurrencesList sig args

def fvarOccurrencesList (sig : Sig) : List Term → List SymId
  | [] => []
  | a :: as => fvarOccurrences sig a ++ fvarOccurrencesList sig as
end

/-- The hint list names, in order, the parameter of every free-variable
occurrence of the definition body.  Surplus hints are permitted, but every
hint must name a parameter. -/
def hintsAdmit (fvars : List SymId) (hints : List Nat)
    (occurrences : List SymId) : Bool :=
  hints.all (· < fvars.length) &&
    decide (occurrences.length ≤ hints.length) &&
    (occurrences.zip hints).all fun pair => fvars[pair.2]? == some pair.1

/-- Arity of an allocated symbol; zero when unknown. -/
def symArity (sig : Sig) (s : SymId) : Nat :=
  match sig s with
  | some info => info.arity
  | none => 0

/-- Admission conditions of a definition by a closed body. -/
def definitionAdmissible (sig : Sig) (fvars : List SymId) (hints : List Nat)
    (value : Term) : Bool :=
  decide (depth sig value = 0) && fvars.all (isFvarSym sig) &&
    hintsAdmit fvars hints (fvarOccurrences sig value)

/-- The defined constant takes one argument per parameter and binds, in that
argument, as many variables as the parameter's arity. -/
def definitionInfo (sig : Sig) (fvars : List SymId) : SymInfo :=
  { kind := .constant, binders := fvars.map (symArity sig) }

/-- A free variable applied to all the bound variables of its own binders. -/
def etaFvar (F : SymId) (arity : Nat) : Term :=
  .app F ((List.range arity).reverse.map Term.bvar)

/-- The defining equation `c(F₁(...), ..., Fₙ(...)) = value`. -/
def definitionStatement (sig : Sig) (c : SymId) (fvars : List SymId)
    (value : Term) : Term :=
  .eq (.app c (fvars.map fun F => etaFvar F (symArity sig F))) value

end Mettapedia.Languages.VibeITP.Spec
