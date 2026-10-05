import Mettapedia.Languages.MM0.Formats.MMB.Machine
import Mettapedia.Languages.MM0.Kernel.TheoryAdmission

/-!
# MMB declarations as kernel declarations

The tables of an MMB file describe declarations: argument descriptors, return
types and unify streams. This module reads them as kernel declarations.

* An argument descriptor becomes a binder. A regular argument's dependencies
  name bound variables by rank; the binder names them by their position among
  the arguments.
* A unify stream is an expression in polish notation. `UTermSave` reserves a
  slot before its arguments are read and fills it with the finished subterm;
  `URef` reads a filled slot, and a reference to a slot still being read is
  refused, as in the reference importer. `UDummy` introduces the next dummy
  variable, which follows the arguments.
* A theorem's stream gives the conclusion, then each hypothesis after a `UHyp`
  from the last to the first.

Decoding spends fuel on nesting and on siblings; twice the number of commands
is enough.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Formats.MMB.Statements

open Mettapedia.Languages.MM0.Kernel

/-- Context positions of the bound arguments, in rank order. -/
def boundPositions (args : List ExprType) : List Nat :=
  (args.zipIdx.filter (·.1.bound)).map (·.2)

def binder (positions : List Nat) (type : ExprType) : Binder :=
  if type.bound then .bound type.sort
  else .regular type.sort (type.deps.image fun rank => positions.getD rank rank)

/-- The context of a declaration's arguments. -/
def context (args : List ExprType) : Context := args.map (binder (boundPositions args))

/-- Slots of a unify stream and the sorts of the dummies introduced so far. -/
structure Decoding where
  slots : List (Option Preterm)
  dummies : List Nat

mutual

/-- One expression of a unify stream. -/
def decodeExpr (arity : Nat → Option Nat) (arguments : Nat) :
    Nat → Decoding → List UnifyCmd → Option (Preterm × Decoding × List UnifyCmd)
  | 0, _, _ => none
  | fuel + 1, state, .term t :: rest => do
      let count ← arity t
      let (args, state, rest) ← decodeExprs arity arguments fuel count state rest
      pure (Preterm.applyArgs (.term t) args, state, rest)
  | fuel + 1, state, .termSave t :: rest => do
      let count ← arity t
      let slot := state.slots.length
      let (args, state, rest) ←
        decodeExprs arity arguments fuel count { state with slots := state.slots ++ [none] } rest
      let e := Preterm.applyArgs (.term t) args
      pure (e, { state with slots := state.slots.set slot (some e) }, rest)
  | _ + 1, state, .ref index :: rest => do
      let e ← (state.slots[index]?).bind id
      pure (e, state, rest)
  | _ + 1, state, .dummy sort :: rest =>
      let e := Preterm.var (arguments + state.dummies.length)
      some (e, ⟨state.slots ++ [some e], state.dummies ++ [sort]⟩, rest)
  | _ + 1, _, _ => none

/-- A number of consecutive expressions. -/
def decodeExprs (arity : Nat → Option Nat) (arguments : Nat) :
    Nat → Nat → Decoding → List UnifyCmd → Option (List Preterm × Decoding × List UnifyCmd)
  | _, 0, state, cmds => some ([], state, cmds)
  | 0, _ + 1, _, _ => none
  | fuel + 1, count + 1, state, cmds => do
      let (first, state, cmds) ← decodeExpr arity arguments fuel state cmds
      let (rest, state, cmds) ← decodeExprs arity arguments fuel count state cmds
      pure (first :: rest, state, cmds)

end

/-- The arity of each term of a table. -/
def arityOf (terms : List TermEntry) (t : Nat) : Option Nat := (terms[t]?).map (·.args.length)

def initial (arguments : Nat) : Decoding :=
  ⟨(List.range arguments).map fun position => some (Preterm.var position), []⟩

/-- The hypotheses after the conclusion, each after a `UHyp`, read from the
last to the first. -/
def decodeHyps (arity : Nat → Option Nat) (arguments : Nat) :
    Nat → Decoding → List UnifyCmd → Option (List Preterm)
  | _, _, [] => some []
  | 0, _, _ :: _ => none
  | fuel + 1, state, .hyp :: rest => do
      let (hypothesis, state, rest) ← decodeExpr arity arguments fuel state rest
      let earlier ← decodeHyps arity arguments fuel state rest
      pure (earlier ++ [hypothesis])
  | _ + 1, _, _ :: _ => none

/-- **A theorem table entry as a kernel theorem declaration.** -/
def theoremDecl (terms : List TermEntry) (entry : ThmEntry) : Option TheoremDecl := do
  let fuel := 2 * entry.unify.length + 2
  let arguments := entry.args.length
  let (conclusion, state, rest) ←
    decodeExpr (arityOf terms) arguments fuel (initial arguments) entry.unify
  if state.dummies ≠ [] then none else
  let hypotheses ← decodeHyps (arityOf terms) arguments fuel state rest
  pure ⟨context entry.args, hypotheses, conclusion⟩

/-- **A term table entry as a kernel term declaration**, with the body of a
definition. -/
def termDecl (terms : List TermEntry) (entry : TermEntry) :
    Option (TermDecl × Option Definition.Body) := do
  let positions := boundPositions entry.args
  let declaration : TermDecl :=
    ⟨context entry.args, entry.sort, entry.ret.deps.image fun rank => positions.getD rank rank⟩
  match entry.value with
  | none => pure (declaration, none)
  | some value =>
      let arguments := entry.args.length
      let (expression, state, rest) ←
        decodeExpr (arityOf terms) arguments (2 * value.length + 2) (initial arguments) value
      if rest ≠ [] then none else
      pure (declaration, some ⟨state.dummies, expression⟩)

end Mettapedia.Languages.MM0.Formats.MMB.Statements
