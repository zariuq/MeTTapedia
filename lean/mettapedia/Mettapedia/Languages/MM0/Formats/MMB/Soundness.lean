import Mettapedia.Languages.MM0.Formats.MMB.Statements
import Mettapedia.Languages.MM0.Kernel.ProofChecking

/-!
# Soundness of the MMB machine: expressions

An allocated expression decodes to a kernel preterm: a variable to the
variable at its context position, an application of a term to the curried
application of the term to its decoded arguments. Arguments are allocated
before the application that uses them, so decoding follows strictly smaller
positions; a store violating this decodes to nothing.

A bound variable's rank names it among the bound binders of the statement's
context, which lists the arguments and then the dummies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Formats.MMB.Soundness

open Mettapedia.Languages.MM0.Kernel

/-- Decode the expression at a position of the store. -/
def decode (store : List Alloc) (position : Nat) : Option Preterm :=
  match h : store[position]? with
  | none => none
  | some alloc =>
      match alloc.node with
      | .var index => some (.var index)
      | .app t args =>
          if earlier : ∀ a ∈ args, a < position then
            (args.attach.mapM fun (arg : {a // a ∈ args}) =>
              have : arg.1 < position := earlier arg.1 arg.2
              decode store arg.1).map (Preterm.applyArgs (.term t))
          else none
termination_by position

/-- Context positions of the bound binders, in rank order. -/
def rankPositions (context : Context) : List Nat :=
  (context.zipIdx.filter fun (binder, _) => match binder with
    | .bound _ => true
    | .regular _ _ => false).map (·.2)

/-- The dependencies of a type, by context position. -/
def positionsOf (context : Context) (deps : Finset Nat) : Finset Nat :=
  deps.image fun rank => (rankPositions context).getD rank rank

end Mettapedia.Languages.MM0.Formats.MMB.Soundness
