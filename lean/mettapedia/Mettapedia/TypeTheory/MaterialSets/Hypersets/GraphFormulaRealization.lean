import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphSetRealization
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic

/-!
# Type-valued first-order graph interpretation

The ordinary first-order membership syntax is interpreted by actual
matching and membership data. Conjunction, disjunction and quantifiers
are dependent types; an existential realizer includes its graph witness.
Every formula transports along the graph-equality realizers of its free
variables. This transport is defined by recursion on the whole formula,
including contravariance of implication and both unbounded quantifiers.

Graph equality and membership are in `Type u`. The full first-order
interpretation is in `Type (u+1)`, since graph witnesses range over all
original-bound presentations. This is not a conversion of erased
existential propositions into witness data.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphFormulaRealization

open GraphSetRealization

universe u

abbrev Formula := ContextualMaterialLogic.Formula
abbrev Environment (count : Nat) := Fin count → Graph.{u}

def extend {count : Nat} (value : Graph.{u}) (environment : Environment.{u} count) :
    Environment.{u} (count+1) := Fin.cases value environment

/-- Atomic matching data is raised for a uniform full first-order carrier. -/
def realize {count : Nat} : Formula count → Environment.{u} count → Type (u+1)
  | .bottom, _ => PEmpty
  | .equal first second, environment => ULift.{u+1} (Equal (environment first) (environment second))
  | .member child parent, environment => ULift.{u+1} (Member (environment child) (environment parent))
  | .both left right, environment => realize left environment × realize right environment
  | .either left right, environment => realize left environment ⊕ realize right environment
  | .imply left right, environment => realize left environment → realize right environment
  | .all body, environment => (value : Graph.{u}) → realize body (extend value environment)
  | .exist body, environment => Σ value : Graph.{u}, realize body (extend value environment)

def extendEquality {count : Nat} {first second : Environment.{u} count}
    (same : ∀ index, Equal (first index) (second index)) (value : Graph.{u}) :
    ∀ index, Equal (extend value first index) (extend value second index) :=
  Fin.cases (Equal.refl value) same

/-- Formula invariance computes witnesses for the entire first-order syntax. -/
def transport {count : Nat} (formula : Formula count) (first second : Environment.{u} count)
    (same : ∀ index, Equal (first index) (second index)) :
    realize formula first → realize formula second :=
  match formula with
  | .bottom => PEmpty.elim
  | .equal left right => fun proof =>
      ⟨(same left).symm.trans (proof.down.trans (same right))⟩
  | .member child parent => fun proof =>
      ⟨Member.transport (same child) (same parent) proof.down⟩
  | .both left right => fun proof =>
      ⟨transport left first second same proof.1, transport right first second same proof.2⟩
  | .either left right => fun proof =>
      match proof with
      | .inl value => .inl (transport left first second same value)
      | .inr value => .inr (transport right first second same value)
  | .imply left right => fun proof argument =>
      transport right first second same
        (proof (transport left second first (fun index => (same index).symm) argument))
  | .all body => fun proof value =>
      transport body (extend value first) (extend value second) (extendEquality same value) (proof value)
  | .exist body => fun proof =>
      ⟨proof.1, transport body (extend proof.1 first) (extend proof.1 second)
        (extendEquality same proof.1) proof.2⟩

theorem extend_substitution {count other : Nat} (indices : Fin count → Fin other)
    (value : Graph.{u}) (environment : Environment.{u} other) :
    extend value environment ∘ ContextualMaterialLogic.liftVariables indices =
      extend value (environment ∘ indices) := by
  funext index
  refine Fin.cases ?_ (fun index => ?_) index
  · rfl
  · rfl

/-- Variable substitution agrees with interpretation for every formula. -/
theorem realize_substitution {count other : Nat} (indices : Fin count → Fin other)
    (formula : Formula count) (environment : Environment.{u} other) :
    realize (ContextualMaterialLogic.substitute indices formula) environment =
      realize formula (environment ∘ indices) := by
  induction formula generalizing other with
  | bottom => rfl
  | equal _ _ => rfl
  | member _ _ => rfl
  | both left right leftInduction rightInduction =>
    exact congrArg₂ Prod (leftInduction indices environment) (rightInduction indices environment)
  | either left right leftInduction rightInduction =>
    exact congrArg₂ Sum (leftInduction indices environment) (rightInduction indices environment)
  | imply left right leftInduction rightInduction =>
    exact congrArg₂ (fun source target => source → target)
      (leftInduction indices environment) (rightInduction indices environment)
  | all body induction =>
    change ((value : Graph.{u}) → realize (ContextualMaterialLogic.substitute
      (ContextualMaterialLogic.liftVariables indices) body) (extend value environment)) = _
    have same : (fun value : Graph.{u} => realize (ContextualMaterialLogic.substitute
        (ContextualMaterialLogic.liftVariables indices) body) (extend value environment)) =
        (fun value : Graph.{u} => realize body (extend value (environment ∘ indices))) := by
      funext value
      rw [induction, extend_substitution]
    exact congrArg (fun family : Graph.{u} → Type (u+1) => (value : Graph.{u}) → family value) same
  | exist body induction =>
    change (Σ value : Graph.{u}, realize (ContextualMaterialLogic.substitute
      (ContextualMaterialLogic.liftVariables indices) body) (extend value environment)) = _
    have same : (fun value : Graph.{u} => realize (ContextualMaterialLogic.substitute
        (ContextualMaterialLogic.liftVariables indices) body) (extend value environment)) =
        (fun value : Graph.{u} => realize body (extend value (environment ∘ indices))) := by
      funext value
      rw [induction, extend_substitution]
    exact congrArg (fun family : Graph.{u} → Type (u+1) => Σ value : Graph.{u}, family value) same

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphFormulaRealization
