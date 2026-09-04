import Mettapedia.GSLT.LanguageDef.CompiledPlanOpenActivationViewCompilation

/-!
# Coalgebraic structural traversal of first-order terms

This module isolates the representation-neutral part of constructor-guided
term traversal.  A term representation supplies one observable polynomial
layer.  The fuelled worklist consumes equal rigid leaves, decomposes equal
applications in authored child order, rejects rigid disagreement, and stops
at variables rather than assigning them an accidental meaning.

The central theorem states naturality under every coalgebra morphism.  A
representation may therefore expose children lazily, eagerly, from an index,
or through another lawful carrier: repeated structural traversal commutes with
the representation map, including completion, mismatch, blocked-variable, and
fuel-exhaustion observations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TermObservationCoalgebra

open CompiledPlanOpenActivationViewCompilation

universe uValue uNext uResult

variable {Value : Type uValue} {Child : Type uValue}
  {Next : Type uNext} {Result : Type uResult}

/-! ## The polynomial observation functor -/

/-- One observable layer of an open first-order term. -/
inductive TermLayer (Child : Type uValue) where
  | symbol (name : List UInt8)
  | variable (name : LogicVariable)
  | string (value : List UInt8)
  | integer (value : Int64)
  | application (head : List UInt8) (children : List Child)
  deriving DecidableEq, Repr

namespace TermLayer

def map (function : Child -> Next) : TermLayer Child -> TermLayer Next
  | .symbol name => .symbol name
  | .variable name => .variable name
  | .string value => .string value
  | .integer value => .integer value
  | .application head children => .application head (children.map function)

@[simp] theorem map_id (layer : TermLayer Child) :
    layer.map id = layer := by
  cases layer <;> simp [map]

@[simp] theorem map_comp
    (first : Child -> Next) (second : Next -> Result)
    (layer : TermLayer Child) :
    (layer.map first).map second = layer.map (second ∘ first) := by
  cases layer <;> simp [map, Function.comp_def]

end TermLayer

/-! ## Ordered equation worklists -/

abbrev Equation (Value : Type uValue) := Value × Value

def mapEquation (function : Child -> Next) : Equation Child -> Equation Next
  | (left, right) => (function left, function right)

def mapEquations (function : Child -> Next) :
    List (Equation Child) -> List (Equation Next) :=
  List.map (mapEquation function)

@[simp] theorem mapEquations_cons
    (function : Child -> Next) (left right : Child)
    (rest : List (Equation Child)) :
    mapEquations function ((left, right) :: rest) =
      (function left, function right) :: mapEquations function rest := by
  rfl

@[simp] theorem mapEquations_append
    (function : Child -> Next)
    (left right : List (Equation Child)) :
    mapEquations function (left ++ right) =
      mapEquations function left ++ mapEquations function right := by
  simp [mapEquations]

@[simp] theorem mapEquations_id (work : List (Equation Child)) :
    mapEquations id work = work := by
  induction work with
  | nil => rfl
  | cons equation rest inductionHypothesis =>
      rcases equation with ⟨left, right⟩
      change (left, right) :: mapEquations id rest = (left, right) :: rest
      rw [inductionHypothesis]

@[simp] theorem mapEquations_comp
    (first : Child -> Next) (second : Next -> Result)
    (work : List (Equation Child)) :
    mapEquations second (mapEquations first work) =
      mapEquations (second ∘ first) work := by
  induction work with
  | nil => rfl
  | cons equation rest =>
      rcases equation with ⟨left, right⟩
      simp [mapEquations, mapEquation, Function.comp_def, *]

theorem mapEquations_zipWith
    (function : Child -> Next) (left right : List Child) :
    mapEquations function (List.zipWith Prod.mk left right) =
      List.zipWith Prod.mk (left.map function) (right.map function) := by
  induction left generalizing right with
  | nil => rfl
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil => rfl
      | cons rightHead rightTail =>
          simp only [List.zipWith, mapEquations, List.map_cons, mapEquation]
          exact congrArg ((function leftHead, function rightHead) :: ·)
            (inductionHypothesis rightTail)

/-! ## Observer-complete traversal results -/

/-- Every externally relevant stopping mode of structural traversal.  A
blocked result retains the exact current equation because variable binding is
the next semantic action; exhaustion retains the complete residual worklist. -/
inductive TraversalResult (Value : Type uValue) where
  | complete
  | mismatch
  | blocked (work : List (Equation Value))
  | exhausted (work : List (Equation Value))
  deriving DecidableEq, Repr

namespace TraversalResult

def map (function : Child -> Next) :
    TraversalResult Child -> TraversalResult Next
  | .complete => .complete
  | .mismatch => .mismatch
  | .blocked work => .blocked (mapEquations function work)
  | .exhausted work => .exhausted (mapEquations function work)

@[simp] theorem map_ite
    (function : Child -> Next) (condition : Prop)
    [Decidable condition]
    (left right : TraversalResult Child) :
    (if condition then left else right).map function =
      if condition then left.map function else right.map function := by
  by_cases holds : condition <;> simp [holds]

@[simp] theorem map_id (result : TraversalResult Child) :
    result.map id = result := by
  cases result <;> simp [map]

@[simp] theorem map_comp
    (first : Child -> Next) (second : Next -> Result)
    (result : TraversalResult Child) :
    (result.map first).map second = result.map (second ∘ first) := by
  cases result <;> simp [map]

end TraversalResult

/-! ## Fuelled structural execution -/

/-- Traverse rigid structure through a one-layer observer.  Fuel counts
equations inspected.  Variables are an explicit suspension boundary: this
operation neither binds them nor treats their printed names as identity.

Equal application children are prepended in authored order.  Thus a stack
realization may push them in reverse order, but its logical worklist remains
the list below. -/
def run
    (observe : Value -> TermLayer Value) :
    Nat -> List (Equation Value) -> TraversalResult Value
  | _, [] => .complete
  | 0, work => .exhausted work
  | fuel + 1, ((left, right) :: rest) =>
      match observe left, observe right with
      | .variable _, _ => .blocked ((left, right) :: rest)
      | _, .variable _ => .blocked ((left, right) :: rest)
      | .symbol leftName, .symbol rightName =>
          if leftName = rightName then run observe fuel rest else .mismatch
      | .string leftValue, .string rightValue =>
          if leftValue = rightValue then run observe fuel rest else .mismatch
      | .integer leftValue, .integer rightValue =>
          if leftValue = rightValue then run observe fuel rest else .mismatch
      | .application leftHead leftChildren,
          .application rightHead rightChildren =>
          if leftHead = rightHead &&
              leftChildren.length = rightChildren.length then
            run observe fuel
              (List.zipWith Prod.mk leftChildren rightChildren ++ rest)
          else
            .mismatch
      | _, _ => .mismatch

/-- A map between carriers is a coalgebra morphism when observing before the
map is exactly observing after it. -/
def Commutes
    (source : Child -> TermLayer Child)
    (target : Next -> TermLayer Next)
    (function : Child -> Next) : Prop :=
  forall value, (source value).map function = target (function value)

/-- The complete fuelled worklist is natural under every coalgebra morphism.
This is stronger than one-step decomposition: it transports every residual
worklist and every stopping observation after arbitrarily many rigid steps. -/
theorem run_natural
    (source : Child -> TermLayer Child)
    (target : Next -> TermLayer Next)
    (function : Child -> Next)
    (commutes : Commutes source target function)
    (fuel : Nat) (work : List (Equation Child)) :
    (run source fuel work).map function =
      run target fuel (mapEquations function work) := by
  induction fuel generalizing work with
  | zero =>
      cases work <;> rfl
  | succ fuel inductionHypothesis =>
      cases work with
      | nil => rfl
      | cons equation rest =>
          rcases equation with ⟨left, right⟩
          have leftCommutes := commutes left
          have rightCommutes := commutes right
          simp only [mapEquations_cons]
          simp only [run]
          rw [← leftCommutes, ← rightCommutes]
          cases sourceLeft : source left <;>
            cases sourceRight : source right <;>
            simp only [TermLayer.map]
          all_goals try simp only [List.length_map]
          all_goals try rfl
          all_goals rw [TraversalResult.map_ite]
          all_goals
            split
            · rw [inductionHypothesis]
              try simp only [mapEquations_append,
                mapEquations_zipWith]
            · rfl

/-! ## Positive and negative controls -/

namespace Canaries

private inductive Tree where
  | symbol (name : UInt8)
  | variable (name : LogicVariable)
  | application (head : UInt8) (children : List Tree)
  deriving Repr

private def outTree : Tree -> TermLayer Tree
  | .symbol name => .symbol [name]
  | .variable name => .variable name
  | .application head children => .application [head] children

private def nestedLeft : Tree :=
  .application 1 [.application 2 [.symbol 3], .symbol 4]

private def nestedRight : Tree :=
  .application 1 [.application 2 [.symbol 3], .symbol 4]

/-- A nested rigid equality completes without an eager reconstruction API. -/
example : run outTree 5 [(nestedLeft, nestedRight)] = .complete := by
  rfl

/-- A deep rigid disagreement is detected after ordered decomposition. -/
example :
    run outTree 5
      [(nestedLeft,
        .application 1 [.application 2 [.symbol 9], .symbol 4])] =
      .mismatch := by
  rfl

/-- A variable remains a semantic suspension, even against itself. -/
example :
    let treeVar := Tree.variable { generation := 7, slot := 3 }
    run outTree 1 [(treeVar, treeVar)] =
      .blocked [(treeVar, treeVar)] := by
  rfl

/-- Fuel exhaustion retains the exact uninspected equation. -/
example :
    run outTree 1 [(nestedLeft, nestedRight)] =
      .exhausted
        [(.application 2 [.symbol 3], .application 2 [.symbol 3]),
         (.symbol 4, .symbol 4)] := by
  rfl

/-- Mismatched rigid constructors cannot be confused by equal arity. -/
example :
    run outTree 1
      [(.application 1 [.symbol 3],
        .application 2 [.symbol 3])] = .mismatch := by
  rfl

/-- Representation maps preserve the full residual observation, not merely a
Boolean success result. -/
example :
    (run outTree 1 [(nestedLeft, nestedRight)]).map id =
      run outTree 1 (mapEquations id [(nestedLeft, nestedRight)]) := by
  exact run_natural outTree outTree id
    (fun value => by simp) 1 [(nestedLeft, nestedRight)]

end Canaries

#print axioms TermLayer.map_id
#print axioms TermLayer.map_comp
#print axioms mapEquations_comp
#print axioms TraversalResult.map_comp
#print axioms run_natural

end Mettapedia.GSLT.LanguageDef.TermObservationCoalgebra
