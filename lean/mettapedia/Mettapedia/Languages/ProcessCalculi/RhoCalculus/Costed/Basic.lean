import Mathlib.Data.Multiset.Basic

/-!
# Concrete cost-accounted rho syntax

This module gives a direct syntax for the cost profile implemented by the
CeTTa rho reducer.  Spatial signatures are finite multisets: multiplication is
commutative, multiplicity is retained, and no inverse operation is present.
Temporal tokens remain ordered stacks.

The syntax deliberately excludes evaluator payloads.  It models the concrete
rho cost profile before any future combination with Rhometa evaluation.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed

universe u

/-- A normalized product of ground signing authorities. -/
abbrev CostSig (Ground : Type u) := Multiset Ground

namespace CostSig

/-- Public runtime signatures contain at least one ground authority. -/
def RuntimeValid {Ground : Type u} (sig : CostSig Ground) : Prop :=
  sig ≠ 0

end CostSig

mutual
  /-- Names are variables, quoted cost terms, or signature-valued channels. -/
  inductive CostName (Ground : Type u) : Type u where
    | bvar : Nat → CostName Ground
    | quote : CostTerm Ground → CostName Ground
    | signature : CostSig Ground → CostName Ground
    deriving DecidableEq

  /-- Rho introductions whose communicated payloads and continuations are cost terms.

  Dequotation is deliberately not a constructor of this sort.  The cost
  endofunctor re-sorts continuation positions to `CostTerm`, so `drop` belongs
  to the wrapped-term sort below. -/
  inductive CostProc (Ground : Type u) : Type u where
    | nil : CostProc Ground
    | par : CostProc Ground → CostProc Ground → CostProc Ground
    | send : CostName Ground → CostTerm Ground → CostProc Ground
    | recv : CostName Ground → CostTerm Ground → CostProc Ground
    deriving DecidableEq

  /-- Wrapped continuations, their structural composition, reflection, and
  nominally located temporal purses. -/
  inductive CostTerm (Ground : Type u) : Type u where
    | nil : CostTerm Ground
    | signed : CostProc Ground → CostSig Ground → CostTerm Ground
    | par : CostTerm Ground → CostTerm Ground → CostTerm Ground
    | drop : CostName Ground → CostTerm Ground
    | purse : CostName Ground → CostStack Ground → CostTerm Ground
    deriving DecidableEq

  /-- A temporal purse: the head signature is spent before the tail is exposed. -/
  inductive CostStack (Ground : Type u) : Type u where
    | empty : CostStack Ground
    | cons : CostSig Ground → CostStack Ground → CostStack Ground
    deriving DecidableEq
end

/-! ## Runtime-supported fragment -/

mutual
  /-- The name forms accepted by the current concrete cost-profile validator. -/
  def CostName.RuntimeSupported {Ground : Type u} : CostName Ground → Prop
    | .bvar _ => True
    | .quote term => term.RuntimeSupported
    | .signature sig => sig.RuntimeValid

  /-- The process forms accepted by the current concrete cost-profile validator. -/
  def CostProc.RuntimeSupported {Ground : Type u} : CostProc Ground → Prop
    | .nil => True
    | .par left right => left.RuntimeSupported ∧ right.RuntimeSupported
    | .send channel payload => channel.RuntimeSupported ∧ payload.RuntimeSupported
    | .recv channel body => channel.RuntimeSupported ∧ body.RuntimeSupported

  /-- The cost terms accepted by the current concrete cost-profile validator. -/
  def CostTerm.RuntimeSupported {Ground : Type u} : CostTerm Ground → Prop
    | .nil => True
    | .signed proc sig => proc.RuntimeSupported ∧ sig.RuntimeValid
    | .par left right => left.RuntimeSupported ∧ right.RuntimeSupported
    | .drop name => name.RuntimeSupported
    | .purse surface stack => surface.RuntimeSupported ∧ stack.RuntimeSupported

  /-- The temporal stacks accepted by the current concrete cost-profile validator. -/
  def CostStack.RuntimeSupported {Ground : Type u} : CostStack Ground → Prop
    | .empty => True
    | .cons sig rest => sig.RuntimeValid ∧ rest.RuntimeSupported
end

/-! ## Locally nameless COMM substitution -/

mutual
  /-- Lift free indices before inserting a communicated term under binders. -/
  def CostName.lift {Ground : Type u} (amount cutoff : Nat) :
      CostName Ground → CostName Ground
    | .bvar index =>
        if cutoff ≤ index then .bvar (index + amount) else .bvar index
    | .quote term => .quote term
    | .signature sig => .signature sig

  /-- Lift free indices through process structure. -/
  def CostProc.lift {Ground : Type u} (amount cutoff : Nat) :
      CostProc Ground → CostProc Ground
    | .nil => .nil
    | .par left right => .par (left.lift amount cutoff) (right.lift amount cutoff)
    | .send channel payload =>
        .send (channel.lift amount cutoff) (payload.lift amount cutoff)
    | .recv channel body =>
        .recv (channel.lift amount cutoff) (body.lift amount (cutoff + 1))

  /-- Lift free indices through wrapped terms. -/
  def CostTerm.lift {Ground : Type u} (amount cutoff : Nat) :
      CostTerm Ground → CostTerm Ground
    | .nil => .nil
    | .signed proc sig => .signed (proc.lift amount cutoff) sig
    | .par left right => .par (left.lift amount cutoff) (right.lift amount cutoff)
    | .drop name => .drop (name.lift amount cutoff)
    | .purse surface stack => .purse (surface.lift amount cutoff) stack
end

mutual
  /-- Substitute a communicated term for one bound name.

  Existing quotations are opaque.  A matched name becomes a quotation of the
  communicated term, shifted to remain capture-avoiding under nested inputs.
  -/
  def CostName.substitute {Ground : Type u} (replacement : CostTerm Ground)
      (depth : Nat) : CostName Ground → CostName Ground
    | .bvar index =>
        if index = depth then
          .quote (replacement.lift depth 0)
        else if depth < index then
          .bvar (index - 1)
        else
          .bvar index
    | .quote term => .quote term
    | .signature sig => .signature sig

  /-- Capture-avoiding substitution through rho processes. -/
  def CostProc.substitute {Ground : Type u} (replacement : CostTerm Ground)
      (depth : Nat) : CostProc Ground → CostProc Ground
    | .nil => .nil
    | .par left right =>
        .par
          (CostProc.substitute (replacement := replacement) (depth := depth) left)
          (CostProc.substitute (replacement := replacement) (depth := depth) right)
    | .send channel payload =>
        .send
          (CostName.substitute (replacement := replacement) (depth := depth) channel)
          (CostTerm.substitute (replacement := replacement) (depth := depth) payload)
    | .recv channel body =>
        .recv
          (CostName.substitute (replacement := replacement) (depth := depth) channel)
          (CostTerm.substitute (replacement := replacement) (depth := depth + 1) body)

  /-- Capture-avoiding substitution through wrapped cost terms.

  Only a `drop` whose variable is replaced by this substitution unwraps the
  communicated term.  A literal `drop (quote term)` remains inert; there is no
  free or eager dequotation rule. -/
  def CostTerm.substitute {Ground : Type u} (replacement : CostTerm Ground)
      (depth : Nat) : CostTerm Ground → CostTerm Ground
    | .nil => .nil
    | .signed proc sig =>
        .signed (CostProc.substitute (replacement := replacement) (depth := depth) proc) sig
    | .par left right =>
        .par
          (CostTerm.substitute (replacement := replacement) (depth := depth) left)
          (CostTerm.substitute (replacement := replacement) (depth := depth) right)
    | .drop (.bvar index) =>
        if index = depth then
          replacement.lift depth 0
        else if depth < index then
          .drop (.bvar (index - 1))
        else
          .drop (.bvar index)
    | .drop name => .drop name
    | .purse surface stack =>
        .purse
          (CostName.substitute (replacement := replacement) (depth := depth) surface)
          stack
end

/-- The contractum used by COMM: open the input body with the output payload. -/
def CostTerm.commSubst {Ground : Type u} (body payload : CostTerm Ground) :
    CostTerm Ground :=
  CostTerm.substitute (replacement := payload) (depth := 0) body

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
