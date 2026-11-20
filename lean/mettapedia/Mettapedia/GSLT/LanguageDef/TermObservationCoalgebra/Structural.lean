import Mathlib.Data.List.Basic

/-!
# Structural traversal over an observed term layer

A term representation exposes variables, rigid leaves, and applications with
ordered children. The traversal needs equality of rigid leaf and head keys;
it never compares or binds variables. It preserves an exact residual
worklist when it stops. There is no term-storage or machine-word carrier in
this interface.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TermObservationCoalgebra

universe uVar uHead uLeaf uValue uNext uResult uVar' uHead' uLeaf'

variable {Var : Type uVar} {Head : Type uHead} {Leaf : Type uLeaf}
  {Value : Type uValue} {Child : Type uValue} {Next : Type uNext} {Result : Type uResult}

/-- The polynomial layer seen by rigid structural traversal. Rigid leaves
carry their whole observation key, including any source-level sort tag. -/
inductive Layer (Var : Type uVar) (Head : Type uHead) (Leaf : Type uLeaf)
    (Child : Type uValue) where
  | variable (name : Var)
  | leaf (value : Leaf)
  | application (head : Head) (children : List Child)
  deriving DecidableEq, Repr

namespace Layer

def map (f : Child → Next) : Layer Var Head Leaf Child → Layer Var Head Leaf Next
  | .variable name => .variable name
  | .leaf value => .leaf value
  | .application head children => .application head (children.map f)

@[simp] theorem map_id (layer : Layer Var Head Leaf Child) : layer.map id = layer := by
  cases layer <;> simp [map]

@[simp] theorem map_comp (f : Child → Next) (g : Next → Result)
    (layer : Layer Var Head Leaf Child) :
    (layer.map f).map g = layer.map (g ∘ f) := by
  cases layer <;> simp [map, Function.comp_def]

def relabel {Var' : Type uVar'} {Head' : Type uHead'} {Leaf' : Type uLeaf'}
    (varKey : Var → Var') (headKey : Head → Head') (leafKey : Leaf → Leaf') :
    Layer Var Head Leaf Child → Layer Var' Head' Leaf' Child
  | .variable name => .variable (varKey name)
  | .leaf value => .leaf (leafKey value)
  | .application head children => .application (headKey head) children

end Layer

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

/-- A rigid traversal inspects at most the stated number of equations.
Applications expose their child equations in the given order. Variables
suspend before either branch could bind one or confuse its identity. -/
def runStructural [DecidableEq Head] [DecidableEq Leaf]
    (observe : Value → Layer Var Head Leaf Value) :
    Nat → List (Equation Value) → TraversalResult Value
  | _, [] => .complete
  | 0, work => .exhausted work
  | fuel + 1, ((left, right) :: rest) =>
      match observe left, observe right with
      | .variable _, _ => .blocked ((left, right) :: rest)
      | _, .variable _ => .blocked ((left, right) :: rest)
      | .leaf a, .leaf b =>
          if a = b then runStructural observe fuel rest else .mismatch
      | .application a xs, .application b ys =>
          if a = b && xs.length = ys.length then
            runStructural observe fuel (List.zipWith Prod.mk xs ys ++ rest)
          else
            .mismatch
      | _, _ => .mismatch

/-- A coalgebra morphism transports the entire residual observation. -/
theorem runStructural_natural [DecidableEq Head] [DecidableEq Leaf]
    (source : Child → Layer Var Head Leaf Child)
    (target : Next → Layer Var Head Leaf Next) (f : Child → Next)
    (commutes : ∀ value, (source value).map f = target (f value))
    (fuel : Nat) (work : List (Equation Child)) :
    (runStructural source fuel work).map f =
      runStructural target fuel (mapEquations f work) := by
  induction fuel generalizing work with
  | zero => cases work <;> rfl
  | succ fuel ih =>
      cases work with
      | nil => rfl
      | cons pair rest =>
          rcases pair with ⟨left, right⟩
          simp only [mapEquations_cons, runStructural, ← commutes]
          cases source left <;> cases source right <;> simp only [Layer.map, List.length_map]
          all_goals try rfl
          all_goals rw [TraversalResult.map_ite]
          all_goals
            split
            · rw [ih]
              try simp only [mapEquations_append, mapEquations_zipWith]
            · rfl

/-- Rigid keys can be stored in any vocabulary that reflects equality.
Variable labels can even be erased for this observer: it stops at them
and returns the unchanged equation. The law is not a unification licence. -/
theorem runStructural_relabel [DecidableEq Head] [DecidableEq Leaf]
    {Var' : Type uVar'} {Head' : Type uHead'} {Leaf' : Type uLeaf'}
    [DecidableEq Head'] [DecidableEq Leaf']
    (observe : Value → Layer Var Head Leaf Value)
    (varKey : Var → Var') (headKey : Head → Head') (leafKey : Leaf → Leaf')
    (headFaithful : Function.Injective headKey) (leafFaithful : Function.Injective leafKey)
    (fuel : Nat) (work : List (Equation Value)) :
    runStructural (fun value => (observe value).relabel varKey headKey leafKey) fuel work =
      runStructural observe fuel work := by
  induction fuel generalizing work with
  | zero => cases work <;> rfl
  | succ fuel ih =>
      cases work with
      | nil => rfl
      | cons pair rest =>
          rcases pair with ⟨left, right⟩
          cases hleft : observe left <;> cases hright : observe right <;>
            simp only [runStructural, hleft, hright, Layer.relabel,
              headFaithful.eq_iff, leafFaithful.eq_iff]
          all_goals split <;> first | rfl | exact ih _

/-- One equation already detects every way a rigid-key encoding can merge
distinctions. Preserving all these observations is equivalent to the two
injectivity conditions that license arbitrary traversals. -/
theorem oneEquation_relabel_iff [DecidableEq Head] [DecidableEq Leaf]
    {Var' : Type uVar'} {Head' : Type uHead'} {Leaf' : Type uLeaf'}
    [DecidableEq Head'] [DecidableEq Leaf']
    (varKey : Var → Var') (headKey : Head → Head') (leafKey : Leaf → Leaf') :
    (∀ observe : Bool → Layer Var Head Leaf Bool,
      runStructural (fun value => (observe value).relabel varKey headKey leafKey) 1 [(false, true)] =
        runStructural observe 1 [(false, true)]) ↔
      Function.Injective headKey ∧ Function.Injective leafKey := by
  constructor
  · intro agrees
    constructor
    · intro a b coded
      by_contra different
      have observed := agrees (fun choose => .application (if choose then b else a) [])
      simp [runStructural, Layer.relabel, coded, different] at observed
    · intro a b coded
      by_contra different
      have observed := agrees (fun choose => .leaf (if choose then b else a))
      simp [runStructural, Layer.relabel, coded, different] at observed
  · rintro ⟨headFaithful, leafFaithful⟩ observe
    exact runStructural_relabel observe varKey headKey leafKey headFaithful leafFaithful
      1 [(false, true)]

namespace Controls

private def largeLeaves : Bool → Layer Empty Unit Int Bool
  | false => .leaf 0
  | true => .leaf (2 ^ 80)

theorem intact_leaf_keys_preserve_mismatch :
    runStructural (fun value => (largeLeaves value).relabel (fun _ => ()) id
      (fun n => (n, true))) 1 [(false, true)] = .mismatch := by
  rw [runStructural_relabel largeLeaves (fun _ => ()) id (fun n => (n, true))
    Function.injective_id (fun _ _ h => congrArg Prod.fst h)]
  rfl

/-- Dropping rigid key distinctions can invent equality. The two leaves
are mathematical integers, not values of a particular machine carrier. -/
theorem merged_leaf_keys_invent_success :
    runStructural largeLeaves 1 [(false, true)] = .mismatch ∧
      runStructural (fun value => (largeLeaves value).relabel (fun _ => ()) id
        (fun _ => ())) 1 [(false, true)] = .complete :=
  ⟨rfl, rfl⟩

end Controls

#print axioms Layer.map_id
#print axioms Layer.map_comp
#print axioms mapEquations_comp
#print axioms TraversalResult.map_comp
#print axioms runStructural_natural
#print axioms runStructural_relabel
#print axioms oneEquation_relabel_iff
#print axioms Controls.intact_leaf_keys_preserve_mismatch
#print axioms Controls.merged_leaf_keys_invent_success

end Mettapedia.GSLT.LanguageDef.TermObservationCoalgebra
