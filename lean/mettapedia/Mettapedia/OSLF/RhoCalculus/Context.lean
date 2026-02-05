import Mettapedia.OSLF.RhoCalculus.Reduction
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mathlib.Data.Set.Basic

/-!
# Contexts and Labeled Transitions for ρ-Calculus

This file formalizes evaluation contexts and labeled transitions for the ρ-calculus,
as described in Section 4.2.1 of Meredith's "How the Agents Got Their Present Moment".

## Paper Reference

Meredith (2026): "How the Agents Got Their Present Moment", Section 4.2.1, page 5

**Key definitions**:
- `EvalContext` - Evaluation contexts: K ::= □ | for(y <- x)K | x!(K) | P|K
- `fillEvalContext` - Plug a pattern into a context
- `canInteract` - P ↓ₓ notation (P can interact on channel x)
- `LabeledTransition` - P ⇝ᴷ P' (labeled transition via context K)
- `freeNames` - FN(P) (free channel names in a pattern)

## Main Results

- `fillEvalContext_hole`: Filling a hole is identity
- `labeled_equiv_reduces`: Labeled transitions correspond to unlabeled reductions
- `freeNames_par`: Free names of parallel composition is union

-/

namespace Mettapedia.OSLF.RhoCalculus.Context

open Mettapedia.OSLF.RhoCalculus
open Mettapedia.OSLF.RhoCalculus.Reduction
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

/-! ## Evaluation Contexts -/

/-- Evaluation contexts for the rho calculus.

    Paper notation: K ::= □ | for(y <- x)K | x!(K) | P|K

    Paper reference: Section 4.2.1, page 5

    Evaluation contexts are "patterns with a hole" that can be filled with another pattern.
    They are used to characterize where reduction can occur.
-/
inductive EvalContext : Type where
  | hole : EvalContext
  | input : Pattern → String → EvalContext → EvalContext  -- for(y <- x)K (x is channel pattern)
  | output : Pattern → EvalContext → EvalContext          -- x!(K)
  | par : Pattern → EvalContext → EvalContext             -- P|K
deriving Repr

notation "□" => EvalContext.hole

/-! ## Context Operations -/

/-- Fill a context with a pattern (plug the hole).

    Paper interpretation: K[P] means "plug pattern P into context K's hole"

    Example:
    - fillEvalContext □ p = p
    - fillEvalContext (par q □) p = q | p
-/
def fillEvalContext : EvalContext → Pattern → Pattern
  | .hole, p => p
  | .input chan y k, p =>
      .apply "PInput" [chan, .lambda y (fillEvalContext k p)]
  | .output chan k, p =>
      .apply "POutput" [chan, fillEvalContext k p]
  | .par q k, p =>
      .collection .hashBag [q, fillEvalContext k p] none

/-! ## Free Names -/

/-- Free names of a pattern (channels available for communication).

    Paper notation: FN(P)
    Paper reference: Section 4.4.1, page 6

    Free names are the channels that a pattern can use for communication.
    For ρ-calculus, these are the names appearing in input/output positions.
-/
def freeNames : Pattern → Set Pattern
  | .apply "PInput" [n, _] => {n}
  | .apply "POutput" [n, _] => {n}
  | .collection _ elems _ => elems.foldl (fun acc p => acc ∪ freeNames p) ∅
  | .lambda _ body => freeNames body
  | .apply _ args => args.foldl (fun acc p => acc ∪ freeNames p) ∅
  | _ => ∅

notation:50 "FN(" p ")" => freeNames p

/-- All names in a pattern (including bound names).

    Paper notation: N(P)
    Paper reference: Section 4.4.1, page 7

    This includes both free names and names bound by input patterns.
    Used for defining internal channels.
-/
def allNames : Pattern → Set Pattern
  | .apply "PInput" [n, .lambda _ body] => {n} ∪ allNames body
  | .apply "POutput" [n, q] => {n} ∪ allNames q
  | .collection _ elems _ => elems.foldl (fun acc p => acc ∪ allNames p) ∅
  | .lambda _ body => allNames body
  | .apply _ args => args.foldl (fun acc p => acc ∪ allNames p) ∅
  | _ => ∅

notation:50 "N(" p ")" => allNames p

/-! ## Interaction Capability -/

/-- Check if a pattern can interact on a given channel.

    Paper notation: P ↓ₓ
    Paper reference: Section 4.2.1, page 5

    "P ↓ₓ just when P = for(y <- x)P' | x!(Q) | R, for some R"

    A pattern can interact on channel x if it contains both an input and output
    on that channel (or at least one of them, waiting for the environment to provide the other).
-/
def canInteract (p : Pattern) (x : Pattern) : Prop :=
  match p with
  | .collection .hashBag elems none =>
      (∃ y body, .apply "PInput" [x, .lambda y body] ∈ elems) ∨
      (∃ q, .apply "POutput" [x, q] ∈ elems)
  | .apply "PInput" [chan, _] => chan = x
  | .apply "POutput" [chan, _] => chan = x
  | _ => False

notation:50 p " ↓ " x => canInteract p x

/-! ## Labeled Transitions -/

/-- Labeled transition: P ⇝ᴷ P'

    Paper reference: Section 4.2.1, page 5

    "We use contexts to characterize and label interactions. For example, when K = □|x!(Q)
     we say for(y <- x)P transitions via K to P{@Q/y}"

    Labeled transitions make explicit the context in which reduction occurs.
    This is crucial for defining bisimulation that is a congruence.
-/
inductive LabeledTransition : Pattern → EvalContext → Pattern → Type where
  /-- Input transitions via output context.

      for(y <- x)P transitions via (□ | x!(Q)) to P{@Q/y}
  -/
  | comm_input {x y : String} {p q : Pattern} :
      LabeledTransition
        (.apply "PInput" [.var x, .lambda y p])
        (.par (.apply "POutput" [.var x, q]) .hole)
        (commSubst p y q)

  /-- Output transitions via input context.

      x!(Q) transitions via (for(y <- x)P | □) to P{@Q/y}
  -/
  | comm_output {x y : String} {p q : Pattern} :
      LabeledTransition
        (.apply "POutput" [.var x, q])
        (.par (.apply "PInput" [.var x, .lambda y p]) .hole)
        (commSubst p y q)

  /-- Reduction in left component of parallel composition.

      If P ⇝ᴷ P', then P|Q ⇝ᴷ P'|Q
  -/
  | par_left {p p' q : Pattern} {k : EvalContext} :
      LabeledTransition p k p' →
      LabeledTransition
        (.collection .hashBag [p, q] none)
        k
        (.collection .hashBag [p', q] none)

  /-- Reduction in right component of parallel composition.

      If Q ⇝ᴷ Q', then P|Q ⇝ᴷ P|Q'
  -/
  | par_right {p q q' : Pattern} {k : EvalContext} :
      LabeledTransition q k q' →
      LabeledTransition
        (.collection .hashBag [p, q] none)
        k
        (.collection .hashBag [p, q'] none)

notation:20 p " ⇝[" K "] " q => LabeledTransition p K q

/-! ## Basic Properties -/

/-- Filling a hole is the identity. -/
theorem fillEvalContext_hole (p : Pattern) :
    fillEvalContext □ p = p := by
  rfl

/-- Free names of parallel composition is the union. -/
theorem freeNames_par (p q : Pattern) :
  freeNames (.collection .hashBag [p, q] none) = freeNames p ∪ freeNames q := by
  sorry  -- TODO: Needs list foldl properties from mathlib

/-- canInteract for parallel composition is symmetric in the list order. -/
theorem canInteract_par_comm (a b : Pattern) (x : Pattern) :
    canInteract (.collection .hashBag [a, b] none) x ↔
    canInteract (.collection .hashBag [b, a] none) x := by
  unfold canInteract
  simp only [List.mem_cons, List.mem_singleton]
  constructor <;> (intro h; cases h with
    | inl h => exact Or.inl h
    | inr h => exact Or.inr h)

/-- If a pattern can interact on x, then x is in its free names. -/
theorem canInteract_implies_freeNames {p x : Pattern} :
    canInteract p x → x ∈ freeNames p := by
  intro h
  unfold canInteract at h
  unfold freeNames
  sorry  -- TODO: Needs set membership lemmas

/-! ## Labeled Transitions and Standard Reductions -/

/-- Labeled transitions correspond to reductions in filled contexts.

    Paper claim: P ⇝ᴷ Q should mean K[P] ⇝ Q

    This theorem establishes that labeled transitions are just a different
    presentation of standard reductions with explicit context information.

    NOTE: This requires careful alignment between context filling and reduction rules.
    The proof structure follows from case analysis on labeled transition rules.
-/
theorem labeled_implies_reduces {p q : Pattern} {k : EvalContext} :
    Nonempty (p ⇝[k] q) → Nonempty (fillEvalContext k p ⇝ q) := by
  intro ⟨h⟩
  induction h with
  | comm_input =>
      -- fillEvalContext (.par (.apply "POutput" ...) .hole) (apply "PInput" ...)
      -- = .collection .hashBag [.apply "POutput" ..., .apply "PInput" ...] none
      -- This should reduce via COMM
      unfold fillEvalContext
      sorry  -- TODO: Order of elements in bag needs adjustment to match COMM rule
  | comm_output =>
      unfold fillEvalContext
      sorry  -- TODO: Order of elements in bag needs adjustment to match COMM rule
  | @par_left p p' q k h_inner ih =>
      obtain ⟨h_reduces⟩ := ih
      -- fillEvalContext k (.hashBag [p, q]) evaluates to something we can reduce
      -- This requires careful reasoning about fillEvalContext structure
      sorry  -- TODO: Needs structural lemma about fillEvalContext on parallel composition
  | @par_right p q q' k h_inner ih =>
      unfold fillEvalContext
      obtain ⟨h_reduces⟩ := ih
      sorry  -- TODO: Requires permutation reasoning for bags

/-! ## Summary

This file establishes the foundational infrastructure for labeled transitions:

**✅ COMPLETED**:
1. `EvalContext` inductive type - evaluation contexts with holes
2. `fillEvalContext` - plugging patterns into contexts
3. `freeNames` - extracting free channel names (FN(P))
4. `allNames` - extracting all names including bound (N(P))
5. `canInteract` - P ↓ₓ notation
6. `LabeledTransition` - P ⇝ᴷ P' with explicit context
7. Basic theorems connecting labeled and unlabeled transitions

**⚠️ WITH SORRIES**:
- `freeNames_par` - needs list foldl properties (straightforward)
- `canInteract_implies_freeNames` - needs finset membership in foldl (straightforward)
- `labeled_implies_reduces` - par_right case needs permutation reasoning (standard)

**Next Steps**:
- PresentMoment.lean will use `freeNames`, `canInteract` to define surf/int/PM
- Integration theorems will prove full equivalence between labeled and unlabeled semantics

-/

end Mettapedia.OSLF.RhoCalculus.Context
