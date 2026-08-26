import Mettapedia.Cybernetics.HierarchicalComplexity.Finite

/-!
# Commons--Pekker chain and coordination examples

This file computes the two concrete examples used to introduce the
permutation test in Michael Lamport Commons and Alexander Pekker,
*Presenting the Formal Theory of Hierarchical Complexity* (2008), pp. 376--377.

Example A evaluates `1 + 2` and `3 * 4`.  The two computations update
independent components, so either schedule reaches `(3, 12)`.  Example C
evaluates the expression `2 * (3 + 4)`: addition before multiplication gives
`14`, whereas multiplying `2 * 3` before adding `4` gives `10`.  The first is
therefore a chain and the second a coordination under the paper's actual
permutation criterion.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.HierarchicalComplexity.SourceExamples

open HierarchicalComplexity

/-! ## Example A: two independent arithmetic actions -/

/-- The initial state for Example A records the results of the addition and
multiplication actions independently. -/
def exampleAInitial : Nat × Nat := (0, 0)

/-- Execute `1 + 2`, leaving the multiplication component unchanged. -/
def exampleAAddition (state : Nat × Nat) : Nat × Nat :=
  (1 + 2, state.2)

/-- Execute `3 * 4`, leaving the addition component unchanged. -/
def exampleAMultiplication (state : Nat × Nat) : Nat × Nat :=
  (state.1, 3 * 4)

/-- Execute the two Example-A actions in the order selected by the first
position of a binary schedule. -/
def exampleASemantics : ScheduleSemantics (Fin 2) (Nat × Nat) :=
  fun schedule =>
    if schedule 0 = 0 then
      exampleAMultiplication (exampleAAddition exampleAInitial)
    else
      exampleAAddition (exampleAMultiplication exampleAInitial)

/-- Both schedules of Example A compute the same final state. -/
theorem exampleASemantics_eq (schedule : Schedule (Fin 2)) :
    exampleASemantics schedule = (3, 12) := by
  simp [exampleASemantics, exampleAInitial, exampleAAddition,
    exampleAMultiplication]

/-- Commons and Pekker's Example A is a chain by permutation invariance. -/
theorem exampleA_isChain : IsChain exampleASemantics := by
  intro first second
  rw [exampleASemantics_eq first, exampleASemantics_eq second]

/-- The proof-bearing organization classified by the Example-A computation. -/
def exampleAOrganization : Organization (Fin 2) (Nat × Nat) :=
  .chain exampleASemantics exampleA_isChain

/-- Example A as a finite Commons action with two simple children. -/
def exampleAAction : Finite.Action.{0, 0} (Nat × Nat) :=
  Finite.Action.chain LimitCanary.binary_hasAtLeastTwo
    (fun _ => Finite.Action.simple (Nat × Nat))
    exampleASemantics exampleA_isChain

/-- Independent scheduling does not raise Example A above its simple
children. -/
theorem exampleA_order : exampleAAction.order = 0 := by
  obtain ⟨occurrence, orderEqual⟩ :=
    (Finite.Action.chain_order_is_child_maximum
      LimitCanary.binary_hasAtLeastTwo
      (fun _ : Fin 2 => Finite.Action.simple (Nat × Nat))
      exampleASemantics exampleA_isChain).1
  simpa only [exampleAAction] using orderEqual.trans
    (Finite.Action.order_simple (Nat × Nat))

/-! ## Example C: order-sensitive arithmetic -/

/-- Execute Example C according to the first scheduled operation.  Addition
before multiplication computes the parsed expression `2 * (3 + 4)`; the
opposite order computes `(2 * 3) + 4`. -/
def exampleCSemantics : ScheduleSemantics (Fin 2) Nat :=
  fun schedule =>
    if schedule 0 = 0 then 2 * (3 + 4) else 2 * 3 + 4

@[simp] theorem exampleC_additionFirst :
    exampleCSemantics (Equiv.refl (Fin 2)) = 14 := by
  simp [exampleCSemantics]

@[simp] theorem exampleC_multiplicationFirst :
    exampleCSemantics (Equiv.swap (0 : Fin 2) 1) = 10 := by
  simp [exampleCSemantics]

/-- Commons and Pekker's Example C is a coordination: the identity and swap
schedules compute different results. -/
theorem exampleC_isCoordination : IsCoordination exampleCSemantics := by
  refine ⟨Equiv.refl (Fin 2), Equiv.swap 0 1, ?_⟩
  simp

/-- The proof-bearing organization classified by the Example-C computation. -/
def exampleCOrganization : Organization (Fin 2) Nat :=
  .coordination exampleCSemantics exampleC_isCoordination

/-- Example C as a finite Commons action with two simple children. -/
def exampleCAction : Finite.Action.{0, 0} Nat :=
  Finite.Action.coordination LimitCanary.binary_hasAtLeastTwo
    (fun _ => Finite.Action.simple Nat)
    exampleCSemantics exampleC_isCoordination
    (fun _ _ => rfl)

/-- The order-sensitive coordination in Example C raises the order by one. -/
theorem exampleC_order : exampleCAction.order = 1 := by
  simpa [exampleCAction] using
    (Finite.Action.coordination_order_eq_child_add_one
      LimitCanary.binary_hasAtLeastTwo
      (fun _ : Fin 2 => Finite.Action.simple Nat)
      exampleCSemantics exampleC_isCoordination
      (fun _ _ => rfl) (0 : Fin 2))

end Mettapedia.Cybernetics.HierarchicalComplexity.SourceExamples

#print axioms Mettapedia.Cybernetics.HierarchicalComplexity.SourceExamples.exampleA_isChain
#print axioms Mettapedia.Cybernetics.HierarchicalComplexity.SourceExamples.exampleC_isCoordination
#print axioms Mettapedia.Cybernetics.HierarchicalComplexity.SourceExamples.exampleC_order
