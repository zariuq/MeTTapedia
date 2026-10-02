/-!
# Vibe-ITP specification: words, literals, symbols and terms

This module begins an independent specification of the Vibe-ITP proof kernel
and its binary checker protocol.  It is written from the published binary
format and axiom file, together with the observed behaviour of the reference
kernel on the exported corpus.

The source system is Mirek Olšák's
[Vibe-ITP](https://git.olsak.net/mirek/Vibe-ITP). The reference material for
this specification is `binary_spec.md`, `logic.lg`, and the kernel interfaces
at upstream revision `e671155fea55df629026ed52719e9115ed1d4e1d`.

Vibe-ITP is a second-order logic with a single universe.  A term is a de Bruijn
bound variable, a byte-string literal, or the application of a symbol to
arguments.  A constant symbol binds a fixed number of variables in each of its
arguments; a free variable (a second-order metavariable) has an arity and binds
nothing.  Symbol identity is allocation identity: every symbol creation yields
a symbol distinct from all earlier ones.

The reference kernel computes with unsigned 64-bit words.  Every place where
it refuses an operation because a word computation would wrap is stated here
exactly; these conditions are part of what the checker accepts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec

/-! ## Machine words -/

/-- Exclusive upper bound of the reference kernel's unsigned machine word. -/
def wordBound : Nat := 2 ^ 64

/-- Little-endian expansion of the low `width` bytes of `value`. -/
def leBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | width + 1, value => UInt8.ofNat (value % 256) :: leBytes width (value / 256)

/-- The kernel's number literal: one byte below 256, otherwise the eight-byte
little-endian word.  Arguments are machine words. -/
def natLiteral (value : Nat) : List UInt8 :=
  if value < 256 then [UInt8.ofNat value] else leBytes 8 value

@[simp] theorem leBytes_length (width value : Nat) :
    (leBytes width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [leBytes, ih]

/-! ## Built-in symbols -/

/-- The eleven constant symbols the kernel itself refers to. -/
inductive Builtin where
  | impl
  | eq
  | litIsNat
  | litLt
  | litAdd
  | litMul
  | litDiv
  | litLength
  | litGet
  | isSafeCode
  | executedTo
deriving DecidableEq, Repr

/-- Protocol slot of each built-in constant.  Slots 0 and 1 hold the markers
for bound variables and literals, which are not applicable symbols. -/
def Builtin.slot : Builtin → Nat
  | .impl => 2
  | .eq => 3
  | .litIsNat => 4
  | .litLt => 5
  | .litAdd => 6
  | .litMul => 7
  | .litDiv => 8
  | .litLength => 9
  | .litGet => 10
  | .isSafeCode => 11
  | .executedTo => 12

/-- Arity of each built-in constant.  None of them binds variables. -/
def Builtin.arity : Builtin → Nat
  | .impl => 2
  | .eq => 2
  | .litIsNat => 1
  | .litLt => 2
  | .litAdd => 2
  | .litMul => 2
  | .litDiv => 2
  | .litLength => 1
  | .litGet => 2
  | .isSafeCode => 4
  | .executedTo => 4

/-- All built-in constants, in slot order. -/
def Builtin.all : List Builtin :=
  [.impl, .eq, .litIsNat, .litLt, .litAdd, .litMul, .litDiv, .litLength,
    .litGet, .isSafeCode, .executedTo]

/-- Number of protected symbol slots: the two markers, the eleven kernel
constants, and no further reservations. -/
def protectedSymbolSlots : Nat := 13

/-! ## Symbols -/

/-- Allocation identity of a symbol: a kernel built-in, or the `n`-th symbol
allocated during a checker run. -/
inductive SymId where
  | builtin (b : Builtin)
  | fresh (n : Nat)
deriving DecidableEq, Repr

inductive SymKind where
  | constant
  | fvar
deriving DecidableEq, Repr

/-- Immutable data of an allocated symbol.  The arity is the length of the
binder list; a free variable binds nothing in any argument. -/
structure SymInfo where
  kind : SymKind
  binders : List Nat
deriving DecidableEq, Repr

def SymInfo.arity (info : SymInfo) : Nat := info.binders.length

/-- Symbol information of a free variable of the given arity. -/
def SymInfo.fvarOf (arity : Nat) : SymInfo :=
  { kind := .fvar, binders := List.replicate arity 0 }

def Builtin.info (b : Builtin) : SymInfo :=
  { kind := .constant, binders := List.replicate b.arity 0 }

/-- A signature assigns data to the symbols allocated so far. -/
abbrev Sig := SymId → Option SymInfo

/-- The signature determined by the information of fresh allocations. -/
def sigOf (fresh : Nat → Option SymInfo) : Sig
  | .builtin b => some b.info
  | .fresh n => fresh n

/-- Binder count of argument `index` of symbol `s`; zero when unknown. -/
def binderAt (sig : Sig) (s : SymId) (index : Nat) : Nat :=
  match sig s with
  | some info => info.binders.getD index 0
  | none => 0

def isFvarSym (sig : Sig) (s : SymId) : Bool :=
  match sig s with
  | some info => info.kind == .fvar
  | none => false

/-! ## Terms -/

inductive Term where
  | bvar (index : Nat)
  | lit (bytes : List UInt8)
  | app (head : SymId) (args : List Term)
deriving Repr

mutual
/-- Structural equality; symbols compare by allocation identity. -/
def Term.decEq : (a b : Term) → Decidable (a = b)
  | .bvar i, .bvar j =>
      if h : i = j then isTrue (by subst h; rfl)
      else isFalse (by intro e; cases e; exact h rfl)
  | .lit x, .lit y =>
      if h : x = y then isTrue (by subst h; rfl)
      else isFalse (by intro e; cases e; exact h rfl)
  | .app s xs, .app t ys =>
      if h : s = t then
        match Term.decEqList xs ys with
        | isTrue e => isTrue (by subst h; subst e; rfl)
        | isFalse n => isFalse (by intro e; cases e; exact n rfl)
      else isFalse (by intro e; cases e; exact h rfl)
  | .bvar _, .lit _ => isFalse (by intro e; cases e)
  | .bvar _, .app _ _ => isFalse (by intro e; cases e)
  | .lit _, .bvar _ => isFalse (by intro e; cases e)
  | .lit _, .app _ _ => isFalse (by intro e; cases e)
  | .app _ _, .bvar _ => isFalse (by intro e; cases e)
  | .app _ _, .lit _ => isFalse (by intro e; cases e)

def Term.decEqList : (a b : List Term) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
  | x :: xs, y :: ys =>
      match Term.decEq x y, Term.decEqList xs ys with
      | isTrue e₁, isTrue e₂ => isTrue (by subst e₁; subst e₂; rfl)
      | isFalse n, _ => isFalse (by intro e; cases e; exact n rfl)
      | _, isFalse n => isFalse (by intro e; cases e; exact n rfl)
end

instance : DecidableEq Term := Term.decEq

namespace Term

def impl (a b : Term) : Term := .app (.builtin .impl) [a, b]
def eq (a b : Term) : Term := .app (.builtin .eq) [a, b]
def natLit (value : Nat) : Term := .lit (natLiteral value)

end Term

mutual
/-- Number of enclosing binders needed to close a term (`bvar_depth`). -/
def depth (sig : Sig) : Term → Nat
  | .bvar i => i + 1
  | .lit _ => 0
  | .app s args => depthArgs sig s 0 args

/-- Maximum over the arguments of their depth minus the binders the head
symbol introduces at that argument. -/
def depthArgs (sig : Sig) (s : SymId) : Nat → List Term → Nat
  | _, [] => 0
  | index, a :: as =>
      max (depth sig a - binderAt sig s index) (depthArgs sig s (index + 1) as)
end

mutual
/-- Whether a term contains an application of a free-variable symbol. -/
def hasFvar (sig : Sig) : Term → Bool
  | .bvar _ => false
  | .lit _ => false
  | .app s args => isFvarSym sig s || hasFvarList sig args

def hasFvarList (sig : Sig) : List Term → Bool
  | [] => false
  | a :: as => hasFvar sig a || hasFvarList sig as
end

mutual
/-- Kernel term formation.  A bound variable must have a representable
depth, a literal must have a representable length header, and an application
must use an allocated symbol at its exact arity.  Heads of either kind are
admitted; the markers for bound variables and literals are not symbols. -/
def WellFormed (sig : Sig) : Term → Bool
  | .bvar i => decide (i + 1 < wordBound)
  | .lit bytes => decide (bytes.length + 8 < wordBound)
  | .app s args =>
      match sig s with
      | some info => decide (args.length = info.arity) && WellFormedList sig args
      | none => false

def WellFormedList (sig : Sig) : List Term → Bool
  | [] => true
  | a :: as => WellFormed sig a && WellFormedList sig as
end

/-- A closed term has depth zero; theorem statements are closed. -/
def Closed (sig : Sig) (t : Term) : Prop := depth sig t = 0

instance (sig : Sig) (t : Term) : Decidable (Closed sig t) :=
  inferInstanceAs (Decidable (depth sig t = 0))

end Mettapedia.Languages.VibeITP.Spec
