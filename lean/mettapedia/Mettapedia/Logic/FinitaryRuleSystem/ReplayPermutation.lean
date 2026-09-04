import Mathlib.Data.List.FinRange
import Mathlib.Logic.Relation
import Mettapedia.Logic.FinitaryRuleSystem.Tree

/-!
# Premise permutations and replay invariance

A finite derivation tree records its premises in an ordered tuple.  Reordering
that tuple is clerical only for rule interfaces whose Boolean rule test is
invariant under the same permutation.  This module keeps that qualification
explicit, defines recursively nested permutation plans, and proves that exact
replay factors through their equivalence closure.

The construction preserves arity, multiplicity, witnesses, conclusions, and
node count.  It does not license exchange for order-sensitive rules and does
not identify sharing graphs with duplicated trees.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.FinitaryRuleSystem

open scoped BigOperators

universe u v

variable {J : Type u} {W : Type v}

/-- Boolean universal aggregation depends only on the premise multiset. -/
theorem boolAll_eq_of_perm {α : Type*} {left right : List α}
    (permutation : left.Perm right) (predicate : α → Bool) :
    left.all predicate = right.all predicate := by
  by_cases everyLeft : ∀ value ∈ left, predicate value = true
  · rw [List.all_eq_true.mpr everyLeft, List.all_eq_true.mpr]
    intro value member
    exact everyLeft value (permutation.mem_iff.mpr member)
  · have notEveryRight : ¬∀ value ∈ right, predicate value = true := by
      intro everyRight
      exact everyLeft fun value member =>
        everyRight value (permutation.mem_iff.mp member)
    cases leftAll : left.all predicate with
    | false =>
        cases rightAll : right.all predicate with
        | false => rfl
        | true => exact absurd (List.all_eq_true.mp rightAll) notEveryRight
    | true => exact absurd (List.all_eq_true.mp leftAll) everyLeft

/-- A rule interface is premise-permutation invariant when its Boolean root
test depends on the finite premise tuple only up to permutation.  Witnesses and
the conclusion remain fixed. -/
def PremisePermutationInvariant {rules : List J → J → Prop}
    (interface : Mettapedia.Logic.RuleWitness.{u, v} rules) : Prop :=
  ∀ (witness : interface.W) (conclusion : J) (arity : Nat)
    (premises : Fin arity → J) (permutation : Equiv.Perm (Fin arity)),
    interface.isInstance witness
        (List.ofFn (premises ∘ permutation)) conclusion =
      interface.isInstance witness (List.ofFn premises) conclusion

namespace Derivation

/-- A recursively nested plan that permutes the children at each rule node.
The recursive plan at output position `i` belongs to the original child at
position `permutation i`. -/
inductive PremisePermutationPlan :
    (certificate : Mettapedia.Logic.Derivation J W) → Type (max u v) where
  | node {conclusion : J} {witness : W} {arity : Nat}
      {children : Fin arity → Mettapedia.Logic.Derivation J W}
      (permutation : Equiv.Perm (Fin arity))
      (childPlans : (i : Fin arity) →
        PremisePermutationPlan (children (permutation i))) :
      PremisePermutationPlan (.node conclusion witness arity children)

namespace PremisePermutationPlan

/-- Apply a nested premise-permutation plan. -/
def reorder : {certificate : Mettapedia.Logic.Derivation J W} →
    PremisePermutationPlan certificate →
      Mettapedia.Logic.Derivation J W
  | .node conclusion witness arity _children,
      .node _permutation childPlans =>
    .node conclusion witness arity (fun i => reorder (childPlans i))

/-- The plan that leaves every premise position unchanged. -/
def identity : (certificate : Mettapedia.Logic.Derivation J W) →
    PremisePermutationPlan certificate
  | .node _conclusion _witness _arity children =>
    .node (Equiv.refl _) (fun i => identity (children i))

@[simp] theorem reorder_identity
    (certificate : Mettapedia.Logic.Derivation J W) :
    reorder (identity certificate) = certificate := by
  induction certificate with
  | node conclusion witness arity children ih =>
      simp only [identity, reorder]
      congr 1
      funext i
      exact ih i

@[simp] theorem reorder_concl
    {certificate : Mettapedia.Logic.Derivation J W}
    (plan : PremisePermutationPlan certificate) :
    (reorder plan).concl = certificate.concl := by
  cases plan
  rfl

/-- Premise permutation changes no physical rule-node count. -/
theorem reorder_nodeCount
    {certificate : Mettapedia.Logic.Derivation J W}
    (plan : PremisePermutationPlan certificate) :
    (reorder plan).nodeCount = certificate.nodeCount := by
  induction plan with
  | @node conclusion witness arity children permutation childPlans ih =>
      simp only [reorder, Mettapedia.Logic.Derivation.nodeCount_node, ih]
      rw [Equiv.sum_comp permutation
        (fun i => (children i).nodeCount)]

/-- A nested premise permutation preserves exact replay whenever the rule
interface itself is invariant under premise permutation. -/
theorem reorder_valid
    {rules : List J → J → Prop}
    (interface : Mettapedia.Logic.RuleWitness.{u, v} rules)
    (invariant : PremisePermutationInvariant interface)
    {certificate : Mettapedia.Logic.Derivation J interface.W}
    (plan : PremisePermutationPlan certificate) :
    (reorder plan).valid interface = certificate.valid interface := by
  induction plan with
  | @node conclusion witness arity children permutation childPlans ih =>
      let originalPremises : Fin arity → J :=
        fun i => (children i).concl
      have conclusionsPointwise :
          (fun i : Fin arity => (reorder (childPlans i)).concl) =
            originalPremises ∘ permutation := by
        funext i
        exact reorder_concl (childPlans i)
      have rootCheck :
          interface.isInstance witness
              (List.ofFn fun i : Fin arity =>
                (reorder (childPlans i)).concl) conclusion =
            interface.isInstance witness
              (List.ofFn fun i : Fin arity => (children i).concl)
              conclusion := by
        rw [conclusionsPointwise]
        exact invariant witness conclusion arity originalPremises permutation
      have validityPointwise :
          (fun i : Fin arity => (reorder (childPlans i)).valid interface) =
            (fun i => (children i).valid interface) ∘ permutation := by
        funext i
        exact ih i
      have validityPermutation :
          (List.ofFn fun i : Fin arity =>
              (reorder (childPlans i)).valid interface).Perm
            (List.ofFn fun i : Fin arity =>
              (children i).valid interface) := by
        rw [validityPointwise]
        exact Equiv.Perm.ofFn_comp_perm permutation _
      simp only [reorder, Mettapedia.Logic.Derivation.valid]
      rw [rootCheck, boolAll_eq_of_perm validityPermutation id]

/-- One structural premise-permutation step. -/
def PermutationStep
    (left right : Mettapedia.Logic.Derivation J W) : Prop :=
  ∃ plan : PremisePermutationPlan left, reorder plan = right

/-- Equivalence generated by recursively nested premise permutations. -/
def PermutationEquivalent
    (left right : Mettapedia.Logic.Derivation J W) : Prop :=
  Relation.EqvGen PermutationStep left right

theorem PermutationEquivalent.concl_eq
    {left right : Mettapedia.Logic.Derivation J W}
    (equivalent : PermutationEquivalent left right) :
    left.concl = right.concl := by
  induction equivalent with
  | rel left right step =>
      obtain ⟨plan, rfl⟩ := step
      exact (reorder_concl plan).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ firstIH secondIH => exact firstIH.trans secondIH

theorem PermutationEquivalent.nodeCount_eq
    {left right : Mettapedia.Logic.Derivation J W}
    (equivalent : PermutationEquivalent left right) :
    left.nodeCount = right.nodeCount := by
  induction equivalent with
  | rel left right step =>
      obtain ⟨plan, rfl⟩ := step
      exact (reorder_nodeCount plan).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ firstIH secondIH => exact firstIH.trans secondIH

/-- Exact replay validity factors through the premise-permutation quotient. -/
theorem PermutationEquivalent.valid_eq
    {rules : List J → J → Prop}
    (interface : Mettapedia.Logic.RuleWitness.{u, v} rules)
    (invariant : PremisePermutationInvariant interface)
    {left right : Mettapedia.Logic.Derivation J interface.W}
    (equivalent : PermutationEquivalent left right) :
    left.valid interface = right.valid interface := by
  induction equivalent with
  | rel left right step =>
      obtain ⟨plan, rfl⟩ := step
      exact (reorder_valid interface invariant plan).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ firstIH secondIH => exact firstIH.trans secondIH

end PremisePermutationPlan

end Derivation

end Mettapedia.Logic.FinitaryRuleSystem
