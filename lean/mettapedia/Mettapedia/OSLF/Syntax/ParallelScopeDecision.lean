import Mettapedia.Algebra.SupportSeparatedDecision
import Mettapedia.OSLF.Syntax.ParallelScopeGradeZero
import Mettapedia.OSLF.Syntax.EquationalQuotient
import Mathlib.Tactic.FinCases

/-!
# Actual quotient membership for separated parallel scopes

The authored AC1 equation quotient is bijective with complete channel
inventories. A canonical representative and an independently given raw scope
predicate earn the inventory membership test when the predicate respects
the authored equations. Composite scope membership is defined by actual
quotient components. The one-pass inventory decision is proved equivalent
to that existential definition; it is not used to define membership.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ParallelFragment

open Mettapedia.Algebra.SupportSeparatedDecomposition

abbrev ParallelClass := TermQ ac1 [] PSrt.proc

def classOf (term : Term psig [] PSrt.proc) : ParallelClass := Quotient.mk _ term

/-- Complete occurrences descend through the actual authored equations. -/
def inventoryQ : ParallelClass → Multiset (Fin 3) :=
  Quotient.lift nameInventory (fun _ _ equation => nameInventory_equation equation)

def representInventory (inventory : Multiset (Fin 3)) : Term psig [] PSrt.proc :=
  rep (inventory.count 0) (inventory.count 1) (inventory.count 2)

theorem representInventory_count (inventory : Multiset (Fin 3)) (name : Fin 3) :
    countOut name (representInventory inventory) = inventory.count name := by
  fin_cases name <;> simp [representInventory, countOut_rep]

theorem nameInventory_represent (inventory : Multiset (Fin 3)) :
    nameInventory (representInventory inventory) = inventory := by
  apply Multiset.ext.mpr
  intro name
  rw [nameInventory_count, representInventory_count]

/-- Both inverse equations are earned from the independent count invariant
and actual structural-equation completeness. -/
def inventoryEquiv : ParallelClass ≃ Multiset (Fin 3) where
  toFun := inventoryQ
  invFun inventory := classOf (representInventory inventory)
  left_inv value := by
    refine Quotient.inductionOn value ?_
    intro term
    exact Quotient.sound (equation_iff_nameInventory.mpr
      (nameInventory_represent (nameInventory term)))
  right_inv := nameInventory_represent

theorem inventoryQ_injective : Function.Injective inventoryQ := inventoryEquiv.injective

/-- Equation invariance is the condition needed by a raw scope predicate. -/
def ScopeInvariant (scope : Term psig [] PSrt.proc → Prop) : Prop :=
  ∀ first second, EqClosure ac1 first second → (scope first ↔ scope second)

def scopeQ (scope : Term psig [] PSrt.proc → Prop) (invariant : ScopeInvariant scope) :
    ParallelClass → Prop :=
  Quotient.lift scope (fun first second equation => propext (invariant first second equation))

theorem representative_scope_iff_inventory
    {scope : Term psig [] PSrt.proc → Prop} (invariant : ScopeInvariant scope)
    (inventory : Multiset (Fin 3)) :
    scope (representInventory inventory) ↔ inventoryScope scope inventory := by
  constructor
  · intro admitted
    exact ⟨representInventory inventory, admitted, nameInventory_represent inventory⟩
  · rintro ⟨term, admitted, same⟩
    have related : EqClosure ac1 term (representInventory inventory) :=
      equation_iff_nameInventory.mpr (same.trans (nameInventory_represent inventory).symm)
    exact (invariant _ _ related).mp admitted

theorem scopeQ_iff_inventory
    {scope : Term psig [] PSrt.proc → Prop} (invariant : ScopeInvariant scope)
    (value : ParallelClass) :
    scopeQ scope invariant value ↔ inventoryScope scope (inventoryQ value) := by
  refine Quotient.inductionOn value ?_
  intro term
  constructor
  · intro admitted
    exact ⟨term, admitted, rfl⟩
  · rintro ⟨other, admitted, same⟩
    exact (invariant _ _ (equation_iff_nameInventory.mpr same)).mp admitted

/-- Parallel composition descends from the independently authored congruence. -/
def parallelQ : ParallelClass → ParallelClass → ParallelClass :=
  Quotient.map₂ parT (fun _ _ first _ _ second => parCong first second)

theorem inventoryQ_parallel (first second : ParallelClass) :
    inventoryQ (parallelQ first second) = inventoryQ first + inventoryQ second := by
  refine Quotient.inductionOn₂ first second ?_
  intro first second
  exact nameInventory_par first second

/-- Composite membership is independently defined by actual admitted
equation-class components and their actual parallel composition. -/
def CompositeScopeQ (left right : Term psig [] PSrt.proc → Prop)
    (leftInvariant : ScopeInvariant left) (rightInvariant : ScopeInvariant right)
    (value : ParallelClass) : Prop :=
  ∃ first second : ParallelClass,
    scopeQ left leftInvariant first ∧ scopeQ right rightInvariant second ∧
      parallelQ first second = value

theorem compositeScopeQ_iff_inventory
    {left right : Term psig [] PSrt.proc → Prop}
    (leftInvariant : ScopeInvariant left) (rightInvariant : ScopeInvariant right)
    (value : ParallelClass) :
    CompositeScopeQ left right leftInvariant rightInvariant value ↔
      Composite (inventoryScope left) (inventoryScope right) (inventoryQ value) := by
  constructor
  · rintro ⟨first, second, admittedFirst, admittedSecond, whole⟩
    refine ⟨inventoryQ first, inventoryQ second,
      (scopeQ_iff_inventory leftInvariant first).mp admittedFirst,
      (scopeQ_iff_inventory rightInvariant second).mp admittedSecond, ?_⟩
    exact (inventoryQ_parallel first second).symm.trans (congrArg inventoryQ whole)
  · rintro ⟨first, second, admittedFirst, admittedSecond, whole⟩
    let firstClass := inventoryEquiv.symm first
    let secondClass := inventoryEquiv.symm second
    have firstRead : inventoryQ firstClass = first := inventoryEquiv.apply_symm_apply first
    have secondRead : inventoryQ secondClass = second := inventoryEquiv.apply_symm_apply second
    refine ⟨firstClass, secondClass,
      (scopeQ_iff_inventory leftInvariant firstClass).mpr ?_,
      (scopeQ_iff_inventory rightInvariant secondClass).mpr ?_, ?_⟩
    · rw [firstRead]
      exact admittedFirst
    · rw [secondRead]
      exact admittedSecond
    · apply inventoryQ_injective
      rw [inventoryQ_parallel, firstRead, secondRead]
      exact whole

/-- Whole-scope grade-zero separation also determines the two actual
equation classes in any supplied composite decomposition. -/
theorem quotient_halves_unique
    {left right : Term psig [] PSrt.proc → Prop}
    (leftInvariant : ScopeInvariant left) (rightInvariant : ScopeInvariant right)
    (separated : ScopeGradeZero left right)
    {first second first' second' : ParallelClass}
    (admittedFirst : scopeQ left leftInvariant first)
    (admittedSecond : scopeQ right rightInvariant second)
    (admittedFirst' : scopeQ left leftInvariant first')
    (admittedSecond' : scopeQ right rightInvariant second')
    (same : parallelQ first second = parallelQ first' second') :
    first = first' ∧ second = second' := by
  have total := congrArg inventoryQ same
  rw [inventoryQ_parallel, inventoryQ_parallel] at total
  obtain ⟨firstRead, secondRead⟩ := split_unique
    ((scopeGradeZero_iff_inventory left right).mp separated)
    ((scopeQ_iff_inventory leftInvariant first).mp admittedFirst)
    ((scopeQ_iff_inventory rightInvariant second).mp admittedSecond)
    ((scopeQ_iff_inventory leftInvariant first').mp admittedFirst')
    ((scopeQ_iff_inventory rightInvariant second').mp admittedSecond') total
  exact ⟨inventoryQ_injective firstRead, inventoryQ_injective secondRead⟩

/-- A raw decidable scope is tested at the independently constructed
canonical representative. -/
def scopeTest (scope : Term psig [] PSrt.proc → Prop) [DecidablePred scope]
    (inventory : Multiset (Fin 3)) : Bool :=
  decide (scope (representInventory inventory))

theorem scopeTest_iff {scope : Term psig [] PSrt.proc → Prop} [DecidablePred scope]
    (invariant : ScopeInvariant scope) (inventory : Multiset (Fin 3)) :
    scopeTest scope inventory = true ↔ inventoryScope scope inventory := by
  rw [scopeTest, decide_eq_true_eq]
  exact representative_scope_iff_inventory invariant inventory

/-- One computed split followed by the two independently decidable scopes. -/
def decideCompositeQ (classify : Fin 3 → Bool)
    (left right : Term psig [] PSrt.proc → Prop)
    [DecidablePred left] [DecidablePred right] (value : ParallelClass) : Bool :=
  decideComposite classify (scopeTest left) (scopeTest right) (inventoryQ value)

theorem decideCompositeQ_iff {classify : Fin 3 → Bool}
    {left right : Term psig [] PSrt.proc → Prop}
    [DecidablePred left] [DecidablePred right]
    (leftInvariant : ScopeInvariant left) (rightInvariant : ScopeInvariant right)
    (leftSupported : LeftSupported classify (inventoryScope left))
    (rightSupported : RightSupported classify (inventoryScope right))
    (value : ParallelClass) :
    decideCompositeQ classify left right value = true ↔
      CompositeScopeQ left right leftInvariant rightInvariant value := by
  exact (decideComposite_iff leftSupported rightSupported (scopeTest left) (scopeTest right)
    (scopeTest_iff leftInvariant) (scopeTest_iff rightInvariant) (inventoryQ value)).trans
      (compositeScopeQ_iff_inventory leftInvariant rightInvariant value).symm

/-- The classifier-query account is invariant on actual equation classes. -/
theorem quotient_split_queries (classify : Fin 3 → Bool) (value : ParallelClass) :
    (partitionInventory classify (inventoryQ value)).queries = (inventoryQ value).card :=
  (partitionInventory_readout classify (inventoryQ value)).2.2

end Mettapedia.OSLF.Binding.ParallelFragment
