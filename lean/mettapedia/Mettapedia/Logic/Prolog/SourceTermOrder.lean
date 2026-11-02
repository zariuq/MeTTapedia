import Mettapedia.Logic.Prolog.SourceSignature
import Mettapedia.Logic.LP.RuntimeQuery

/-!
# Standard order and stable sorting of source-runtime terms

This file implements the finite graph fragment of SWI-Prolog V10.1.9's
standard term order directly over the canonical `Logic.LP` heap.  It follows
`src/pl-prims.c` (`compareStandard`, `compare_primitives`, and
`compare_functors`) and the stable natural-sort contract in `src/pl-list.c`.

The implementation does not read a heap term back into a second syntax tree.
It dereferences existing roots, compares variables by allocation address,
compares atomic values in SWI order, and descends through the existing
compound edges.  Non-identical rational cycles fail explicitly when the
heap-sized comparison budget is exhausted; no finite order is fabricated for
that still-open fragment.
-/

namespace Mettapedia.Logic.Prolog.SourceTermOrder

open Mettapedia.Logic
open LP.RuntimeTerm
open SourceSignature

abbrev Sigma := SourceSignature.signature

/-- Failures local to finite standard-order inspection.  They are converted
to typed query errors only at the source-runtime service boundary. -/
inductive Error where
  | memory (error : MemoryError)
  | comparisonBudgetExhausted
  | unsupportedClauseReference
  | invalidSortKey
deriving Repr, DecidableEq

private def compareNat (left right : Nat) : Ordering :=
  if left < right then .lt else if right < left then .gt else .eq

private def compareInt (left right : Int) : Ordering :=
  if left < right then .lt else if right < left then .gt else .eq

private def compareString (left right : String) : Ordering :=
  compare left right

private def reverseOrdering : Ordering → Ordering
  | .lt => .gt
  | .eq => .eq
  | .gt => .lt

private def signBit (bits : UInt64) : Bool :=
  (bits &&& 0x8000000000000000) != 0

private def exponentBits (bits : UInt64) : Nat :=
  ((bits >>> 52) &&& 0x7ff).toNat

private def fractionBits (bits : UInt64) : Nat :=
  (bits &&& 0x000fffffffffffff).toNat

private def isNaNBits (bits : UInt64) : Bool :=
  exponentBits bits == 0x7ff && fractionBits bits != 0

private def isInfinityBits (bits : UInt64) : Bool :=
  exponentBits bits == 0x7ff && fractionBits bits == 0

/-- Exact rational value of one finite IEEE-754 binary64 payload. -/
private def finiteFloatRat (bits : UInt64) : Rat :=
  let exponent := exponentBits bits
  let fraction := fractionBits bits
  let effectiveExponent := if exponent = 0 then 1 else exponent
  let significand := if exponent = 0 then fraction else 2 ^ 52 + fraction
  let signed : Int :=
    if signBit bits then -(Int.ofNat significand) else Int.ofNat significand
  if 1075 ≤ effectiveExponent then
    Rat.ofInt (signed * Int.ofNat (2 ^ (effectiveExponent - 1075)))
  else
    Rat.ofInt signed / Rat.ofInt (Int.ofNat (2 ^ (1075 - effectiveExponent)))

/-- SWI orders NaNs by the finite payload obtained by replacing the all-ones
exponent with the bias exponent (`NaN_value` in `src/pl-write.c`). -/
private def nanPayloadRat (bits : UInt64) : Rat :=
  let normalized :=
    (bits &&& UInt64.ofNat 0x800fffffffffffff) |||
      (UInt64.ofNat 0x3ff <<< 52)
  finiteFloatRat normalized

private def compareRat (left right : Rat) : Ordering :=
  if left < right then .lt else if right < left then .gt else .eq

/-- Exact SWI-style comparison of two stored binary64 payloads, including
NaN payloads and the distinction between negative and positive zero. -/
def compareFloatBits (left right : UInt64) : Ordering :=
  if left = right then .eq
  else if isNaNBits left then
    if isNaNBits right then
      compareRat (nanPayloadRat left) (nanPayloadRat right)
    else .lt
  else if isNaNBits right then .gt
  else if isInfinityBits left then
    if isInfinityBits right then
      if signBit left then .lt else .gt
    else if signBit left then .lt else .gt
  else if isInfinityBits right then
    if signBit right then .gt else .lt
  else
    match compareRat (finiteFloatRat left) (finiteFloatRat right) with
    | .eq => if signBit left then .lt else .gt
    | order => order

/-- Mixed integer/float comparison follows SWI's non-ISO numeric standard
order.  Equal numeric values still order the float before the integer. -/
private def compareFloatInt (floatBits : UInt64) (integer : Int) : Ordering :=
  if isNaNBits floatBits then .lt
  else if isInfinityBits floatBits then
    if signBit floatBits then .lt else .gt
  else
    match compareRat (finiteFloatRat floatBits) (Rat.ofInt integer) with
    | .eq => .lt
    | order => order

private def rootCell (heap : Heap Sigma.scoped) (address : Addr) :
    Except Error (Addr × Cell Sigma.scoped) :=
  match heap.deref address with
  | .error error => .error (.memory error)
  | .ok (.variableCycle cycle) =>
      .error (.memory (.variableReferenceCycle cycle))
  | .ok (.root root) =>
      match heap[root]? with
      | some cell => .ok (root, cell)
      | none => .error (.memory (.invalidAddress root))

private def compareConstants : Constant → Constant → Except Error Ordering
  | .nil, .nil => .ok .eq
  | .nil, .atom _ => .ok .lt
  | .atom _, .nil => .ok .gt
  | .nil, .integer _ | .nil, .floatBits _ | .nil, .string _ => .ok .gt
  | .integer _, .nil | .floatBits _, .nil | .string _, .nil => .ok .lt
  | .integer left, .integer right => .ok (compareInt left right)
  | .floatBits left, .floatBits right => .ok (compareFloatBits left right)
  | .floatBits left, .integer right => .ok (compareFloatInt left right)
  | .integer left, .floatBits right =>
      .ok (reverseOrdering (compareFloatInt right left))
  | .integer _, .string _ | .floatBits _, .string _ => .ok .lt
  | .string _, .integer _ | .string _, .floatBits _ => .ok .gt
  | .integer _, .atom _ | .floatBits _, .atom _ => .ok .lt
  | .atom _, .integer _ | .atom _, .floatBits _ => .ok .gt
  | .string left, .string right => .ok (compareString left right)
  | .string _, .atom _ => .ok .lt
  | .atom _, .string _ => .ok .gt
  | .atom left, .atom right => .ok (compareString left right)
  | .clauseReference _, _ | _, .clauseReference _ =>
      .error .unsupportedClauseReference

/-- Heap-sized finite standard-order comparison.  Equal roots return without
descending, so self-comparison of rational trees is supported.  Distinct
cycles remain an explicit partial boundary. -/
def compareAtAux : Nat → Heap Sigma.scoped → Addr → Addr →
    Except Error Ordering
  | 0, _, _, _ => .error .comparisonBudgetExhausted
  | fuel + 1, heap, left, right => do
      let (leftRoot, leftCell) ← rootCell heap left
      let (rightRoot, rightCell) ← rootCell heap right
      if leftRoot = rightRoot then return .eq
      match leftCell, rightCell with
      | .var _ none, .var _ none => return compareNat leftRoot rightRoot
      | .var _ none, _ => return .lt
      | _, .var _ none => return .gt
      | .var _ (some _), _ | _, .var _ (some _) =>
          return ← .error (.memory .illFormedHeap)
      | .const leftConstant, .const rightConstant =>
          compareConstants leftConstant rightConstant
      | .const _, .app _ _ => return .lt
      | .app _ _, .const _ => return .gt
      | .app leftSymbol leftArgs, .app rightSymbol rightArgs =>
          match compareNat leftSymbol.arity rightSymbol.arity with
          | .lt => return .lt
          | .gt => return .gt
          | .eq =>
              match compareString leftSymbol.name rightSymbol.name with
              | .lt => return .lt
              | .gt => return .gt
              | .eq =>
                  let rec compareArgs : List Addr → List Addr →
                      Except Error Ordering
                    | [], [] => .ok .eq
                    | left :: leftTail, right :: rightTail => do
                        match ← compareAtAux fuel heap left right with
                        | .eq => compareArgs leftTail rightTail
                        | order => return order
                    | _, _ => .error (.memory .illFormedHeap)
                  compareArgs leftArgs.toList rightArgs.toList

/-- Public comparison uses one more step than the number of heap cells, which
is complete for finite acyclic paths and detects unsupported distinct cycles. -/
def compareAt (heap : Heap Sigma.scoped) (left right : Addr) :
    Except Error Ordering :=
  compareAtAux (heap.size + 1) heap left right

/-- Key selection supported by SWI's sorting predicates. -/
inductive Key where
  | whole
  | positions (indices : List Nat)
  | pair
deriving Repr, DecidableEq

inductive Direction where
  | ascending
  | descending
deriving Repr, DecidableEq

structure Spec where
  key : Key
  direction : Direction
  removeDuplicates : Bool
deriving Repr, DecidableEq

private def keyAtPositions (heap : Heap Sigma.scoped) :
    List Nat → Addr → Except Error Addr
  | [], address => rootCell heap address |>.map Prod.fst
  | index :: indices, address => do
      if index = 0 then return ← .error .invalidSortKey
      let (_, cell) ← rootCell heap address
      match cell with
      | .app _ arguments =>
          match arguments[index - 1]? with
          | some next => keyAtPositions heap indices next
          | none => .error .invalidSortKey
      | _ => .error .invalidSortKey

private def keyAt (heap : Heap Sigma.scoped) (key : Key) (address : Addr) :
    Except Error Addr := do
  match key with
  | .whole => return (← rootCell heap address).1
  | .positions indices => keyAtPositions heap indices address
  | .pair =>
      let (_, cell) ← rootCell heap address
      match cell with
      | .app symbol arguments =>
          if symbol.name = "-" && symbol.arity = 2 then
            match arguments[0]? with
            | some root => return (← rootCell heap root).1
            | none => .error .invalidSortKey
          else .error .invalidSortKey
      | _ => .error .invalidSortKey

private structure Item where
  term : Addr
  key : Addr

private def prepareItems (heap : Heap Sigma.scoped) (key : Key) :
    List Addr → Except Error (List Item)
  | [] => .ok []
  | term :: tail => do
      let keyRoot ← keyAt heap key term
      let rest ← prepareItems heap key tail
      return { term, key := keyRoot } :: rest

private def compareItems (heap : Heap Sigma.scoped) (direction : Direction)
    (left right : Item) : Except Error Ordering := do
  let result ← compareAt heap left.key right.key
  return match direction with
    | .ascending => result
    | .descending => reverseOrdering result

/-- Stable insertion into an already-sorted list.  Equal keys place the
earlier source item first. -/
private def insertItem (compareItem : Item → Item → Except Error Ordering)
    (item : Item) : List Item → Except Error (List Item)
  | [] => .ok [item]
  | head :: tail => do
      match ← compareItem item head with
      | .lt | .eq => return item :: head :: tail
      | .gt => return head :: (← insertItem compareItem item tail)

private def stableSortItems
    (compareItem : Item → Item → Except Error Ordering) :
    List Item → Except Error (List Item)
  | [] => .ok []
  | head :: tail => do
      let sorted ← stableSortItems compareItem tail
      insertItem compareItem head sorted

private def removeAdjacentDuplicates
    (compareItem : Item → Item → Except Error Ordering) :
    List Item → Except Error (List Item)
  | [] => .ok []
  | [item] => .ok [item]
  | first :: second :: tail => do
      match ← compareItem first second with
      | .eq => removeAdjacentDuplicates compareItem (first :: tail)
      | _ => return first :: (← removeAdjacentDuplicates compareItem (second :: tail))
termination_by items => items.length

/-- Stable sorting over existing term roots.  The result contains only input
roots; allocation of the result list spine remains the shared engine's job. -/
def sortAddresses (heap : Heap Sigma.scoped) (spec : Spec)
    (addresses : List Addr) : Except Error (List Addr) := do
  let items ← prepareItems heap spec.key addresses
  let compareItem := compareItems heap spec.direction
  let sorted ← stableSortItems compareItem items
  let final ←
    if spec.removeDuplicates then removeAdjacentDuplicates compareItem sorted
    else .ok sorted
  return final.map Item.term

end Mettapedia.Logic.Prolog.SourceTermOrder
