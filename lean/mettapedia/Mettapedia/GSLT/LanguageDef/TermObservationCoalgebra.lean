import Mettapedia.GSLT.LanguageDef.TermObservationCoalgebra.Structural
import Mettapedia.GSLT.LanguageDef.CompiledPlanOpenActivationViewCompilation

/-!
# Plan term layers as structural observations

This adapter retains the constructor, string, and integer tags of the
admitted plan carrier for clients that inspect them. It supplies those tags
to the representation-independent traversal as a single disjoint rigid-key
type; neither the traversal nor its naturality law depends on this carrier.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TermObservationCoalgebra

open CompiledPlanOpenActivationViewCompilation

universe uValue uNext uResult

variable {Value : Type uValue} {Child : Type uValue}
  {Next : Type uNext} {Result : Type uResult}

/-! ## Plan observations -/

/-- One observable layer of an admitted open plan term. -/
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

/-- A plan leaf's sort tag is part of the rigid equality key. -/
def TermLayer.asStructural :
    TermLayer Child → Layer LogicVariable (List UInt8) OpenConstant Child
  | .symbol name => .leaf (.symbol name)
  | .string value => .leaf (.string value)
  | .integer value => .leaf (.integer value)
  | .variable name => .variable name
  | .application head children => .application head children

@[simp] theorem TermLayer.asStructural_map (layer : TermLayer Child) (f : Child → Next) :
    (layer.map f).asStructural = layer.asStructural.map f := by
  cases layer <;> rfl

def run (observe : Value → TermLayer Value) :
    Nat → List (Equation Value) → TraversalResult Value :=
  runStructural (TermLayer.asStructural ∘ observe)

/-- The plan view inherits the generic coalgebraic traversal theorem. -/
def Commutes (source : Child → TermLayer Child) (target : Next → TermLayer Next)
    (f : Child → Next) : Prop :=
  ∀ value, (source value).map f = target (f value)

theorem run_natural (source : Child → TermLayer Child) (target : Next → TermLayer Next)
    (f : Child → Next) (commutes : Commutes source target f)
    (fuel : Nat) (work : List (Equation Child)) :
    (run source fuel work).map f = run target fuel (mapEquations f work) := by
  apply runStructural_natural
  intro value
  change (source value).asStructural.map f = (target (f value)).asStructural
  rw [← TermLayer.asStructural_map, commutes value]

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

/-- Supplying the same bytes is not permission to merge two leaf sorts. -/
theorem distinct_leaf_tags_remain_distinct :
    run (fun b : Bool => if b then .symbol [42] else .string [42])
      1 [(true, false)] = .mismatch := rfl

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
#print axioms TermLayer.asStructural_map
#print axioms run_natural
#print axioms Canaries.distinct_leaf_tags_remain_distinct

end Mettapedia.GSLT.LanguageDef.TermObservationCoalgebra
