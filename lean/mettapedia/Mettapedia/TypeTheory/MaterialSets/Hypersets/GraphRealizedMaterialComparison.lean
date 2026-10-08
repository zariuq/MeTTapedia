import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphFormulaRealization
import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedIdentityBoundary
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialCoalgebra

/-!
# Positive formula realization and actual material truth

The existing first-order formula syntax has two distinct interpretations:
graph realizers retain matching and existential evidence, whereas material
forcing records propositions about quotient values. Constructed realizers
preserve every positive formula, including unbounded universal and
existential quantification. Quotient induction into propositions handles
the universal case without choosing graph representatives.

The comparison uses the actual constant material membership coalgebra over
an arbitrary context category. It commutes with variable substitution and
retains all futures of that forcing interpretation. It does not interpret
the separately constructed varying contextual set model. Implication
and negation are outside the positive preservation theorem: converting a
material premise into matching or witness data needs a separate argument.
The matching-transport control refutes faithful evidence recovery.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedMaterialComparison

open _root_.CategoryTheory
open GraphSetRealization ContextualMaterialLogic

universe u
variable {D : Type u} [Category.{u} D]

/-- The actual constant bare membership model, retaining every context. -/
def materialModel : Model (ContextualMaterialCoalgebra.ambient (D := D)) where
  member := fun (_ : D) (child parent : HSet.{u}) => child ∈ parent
  member_transport := by
    intro point target arrow child parent available
    exact available

def observeEnvironment {count : Nat}
    (environment : GraphFormulaRealization.Environment.{u} count) (point : D) :
    Environment (ContextualMaterialCoalgebra.ambient (D := D)) count point :=
  fun index => HSet.mk (environment index)

theorem observe_extend {count : Nat}
    (environment : GraphFormulaRealization.Environment.{u} count)
    (value : Graph.{u}) (point : D) :
    observeEnvironment (GraphFormulaRealization.extend value environment) point =
      extend ContextualMaterialCoalgebra.ambient (observeEnvironment environment point) (HSet.mk value) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

theorem observe_transport {count : Nat} {point target : D} (arrow : point ⟶ target)
    (environment : GraphFormulaRealization.Environment.{u} count) :
    ContextualMaterialLogic.transport ContextualMaterialCoalgebra.ambient arrow
        (observeEnvironment environment point) =
      observeEnvironment environment target := rfl

theorem observe_substitute {count other : Nat} (indices : Fin count → Fin other)
    (environment : GraphFormulaRealization.Environment.{u} other) (point : D) :
    observeEnvironment (fun index => environment (indices index)) point =
      fun index => observeEnvironment environment point (indices index) := rfl

/-- Positive syntax retains conjunction, disjunction and both unbounded
quantifiers. It imposes no finiteness hypothesis on graph presentations. -/
inductive Positive : {count : Nat} → Formula count → Prop where
  | bottom {count : Nat} : Positive (.bottom : Formula count)
  | equal {count : Nat} (first second : Fin count) : Positive (.equal first second)
  | member {count : Nat} (child parent : Fin count) : Positive (.member child parent)
  | both {count : Nat} {left right : Formula count} :
      Positive left → Positive right → Positive (.both left right)
  | either {count : Nat} {left right : Formula count} :
      Positive left → Positive right → Positive (.either left right)
  | all {count : Nat} {body : Formula (count + 1)} : Positive body → Positive (.all body)
  | exist {count : Nat} {body : Formula (count + 1)} : Positive body → Positive (.exist body)

/-- Every positive realization is sound in the existing material forcing
semantics. Universal witnesses are handled by proposition-valued quotient
induction, rather than an inverse of the presentation readout. -/
theorem positive_sound {count : Nat} {formula : Formula count}
    (positive : Positive formula)
    (environment : GraphFormulaRealization.Environment.{u} count)
    (proof : GraphFormulaRealization.realize formula environment) (point : D) :
    force ContextualMaterialCoalgebra.ambient materialModel formula point
      (observeEnvironment environment point) := by
  induction positive generalizing point with
  | bottom => exact proof.elim
  | equal first second => exact GraphRealizedIdentityBoundary.materialEquality proof.down
  | member child parent => exact GraphRealizedIdentityBoundary.materialMembership proof.down
  | both _ _ leftIH rightIH =>
    exact ⟨leftIH environment proof.1 point, rightIH environment proof.2 point⟩
  | either _ _ leftIH rightIH =>
    exact proof.elim (fun witness => Or.inl (leftIH environment witness point))
      (fun witness => Or.inr (rightIH environment witness point))
  | @all count body _ bodyIH =>
    intro target arrow value
    change force ContextualMaterialCoalgebra.ambient materialModel body target
      (extend ContextualMaterialCoalgebra.ambient (observeEnvironment environment target) value)
    induction value using HSet.ind with
    | mk graph =>
      rw [← observe_extend environment graph target]
      exact bodyIH (GraphFormulaRealization.extend graph environment) (proof graph) target
  | exist _ bodyIH =>
    refine ⟨HSet.mk proof.1, ?_⟩
    rw [← observe_extend environment proof.1 point]
    exact bodyIH (GraphFormulaRealization.extend proof.1 environment) proof.2 point

theorem positive_substitute {count other : Nat} {formula : Formula count}
    (positive : Positive formula) (indices : Fin count → Fin other) :
    Positive (substitute indices formula) := by
  induction positive generalizing other with
  | bottom => exact .bottom
  | equal first second => exact .equal _ _
  | member child parent => exact .member _ _
  | both _ _ leftIH rightIH => exact .both (leftIH indices) (rightIH indices)
  | either _ _ leftIH rightIH => exact .either (leftIH indices) (rightIH indices)
  | all _ bodyIH => exact .all (bodyIH (liftVariables indices))
  | exist _ bodyIH => exact .exist (bodyIH (liftVariables indices))

/-- Independently interpreted variable substitution gives the same positive
material conclusion, including substitution under both binders. -/
theorem positive_substitution_sound {count other : Nat} {formula : Formula count}
    (positive : Positive formula) (indices : Fin count → Fin other)
    (environment : GraphFormulaRealization.Environment.{u} other)
    (proof : GraphFormulaRealization.realize (substitute indices formula) environment)
    (point : D) :
    force ContextualMaterialCoalgebra.ambient materialModel formula point
      (fun index => observeEnvironment environment point (indices index)) :=
  (force_substitute materialModel indices formula point (observeEnvironment environment point)).mp
    (positive_sound (positive_substitute positive indices) environment proof point)

namespace Controls

/-- Sound atomic preservation does not recover matching evidence or its
dependent action on an occurrence. -/
theorem sound_equality_without_faithful_transport :
    HSet.mk GraphRealizedIdentityBoundary.Controls.cyclic.{u} =
        HSet.mk GraphRealizedIdentityBoundary.Controls.cyclic ∧
      ¬ ∃ read : (HSet.mk GraphRealizedIdentityBoundary.Controls.cyclic =
          HSet.mk GraphRealizedIdentityBoundary.Controls.cyclic) → Bool,
        ∀ proof : Equal GraphRealizedIdentityBoundary.Controls.cyclic
            GraphRealizedIdentityBoundary.Controls.cyclic,
          read (GraphRealizedIdentityBoundary.materialEquality proof) =
            GraphRealizedIdentityBoundary.Controls.response proof :=
  ⟨GraphRealizedIdentityBoundary.materialEquality GraphRealizedIdentityBoundary.Controls.opposite,
    GraphRealizedIdentityBoundary.Controls.response_no_material_descent⟩

end Controls

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedMaterialComparison
