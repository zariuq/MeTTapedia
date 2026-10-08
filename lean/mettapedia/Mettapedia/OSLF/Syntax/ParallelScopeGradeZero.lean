import Mettapedia.Algebra.SupportSeparatedDecomposition
import Mettapedia.OSLF.Syntax.UniqueDecompositionRepaired

/-!
# Name-based grade-zero separation in the parallel presentation

The authored parallel presentation carries three channel names. Its complete
name inventory is computed from its syntax, preserving repeated occurrences.
The independent output-count invariant identifies this inventory with the
actual AC1 quotient. Grade-zero separation of entire scope extensions earns
uniqueness of both components without choosing a partition of all channels.

The inert disjoint-scope counterexample has shared channel support. Thus it
does not discharge the source's grade-zero hypothesis. These results concern
the declared parallel presentation; binding and reflective name equations
require their own support comparison.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ParallelFragment

open Mettapedia.Algebra.SupportSeparatedDecomposition

/-- The name carried by the outer authored operation, if any. -/
def operationInventory {sort : PSrt} : POp sort → Multiset (Fin 3)
  | .out name => {name}
  | .nul => 0
  | .par => 0

mutual
  /-- Complete channel inventory computed independently from the syntax. -/
  def nameInventory : {Γ : Ctx psig} → {sort : PSrt} →
      Term psig Γ sort → Multiset (Fin 3)
    | _, _, .var _ => 0
    | _, _, .op operation arguments =>
      operationInventory operation + argumentInventory arguments

  def argumentInventory : {arguments : List (List PSrt × PSrt)} →
      {Γ : Ctx psig} → Args psig arguments Γ → Multiset (Fin 3)
    | _, _, .nil => 0
    | _, _, .cons first rest => nameInventory first + argumentInventory rest
end

mutual
  theorem nameInventory_count (name : Fin 3) : ∀ {Γ : Ctx psig} {sort : PSrt}
      (term : Term psig Γ sort), (nameInventory term).count name = countOut name term
    | _, _, .var _ => rfl
    | _, _, .op operation arguments => by
      rw [nameInventory, Multiset.count_add, argumentInventory_count]
      cases operation <;> simp [operationInventory, headCount, countOut,
        Multiset.count_singleton]

  theorem argumentInventory_count (name : Fin 3) :
      ∀ {arguments : List (List PSrt × PSrt)} {Γ : Ctx psig}
      (values : Args psig arguments Γ),
      (argumentInventory values).count name = countOutArgs name values
    | _, _, .nil => rfl
    | _, _, .cons first rest => by
      rw [argumentInventory, Multiset.count_add, nameInventory_count,
        argumentInventory_count, countOutArgs]
end

theorem nameInventory_par (first second : Term psig [] PSrt.proc) :
    nameInventory (parT first second) = nameInventory first + nameInventory second := by
  simp only [parT, nameInventory, operationInventory, argumentInventory, Multiset.add_zero,
    Multiset.zero_add]

theorem nameInventory_equation {first second : Term psig [] PSrt.proc}
    (equation : EqClosure ac1 first second) :
    nameInventory first = nameInventory second := by
  apply Multiset.ext.mpr
  intro name
  rw [nameInventory_count, nameInventory_count]
  exact countOut_invariant name equation

/-- The complete inventory identifies exactly the actual equation classes. -/
theorem equation_iff_nameInventory {first second : Term psig [] PSrt.proc} :
    EqClosure ac1 first second ↔ nameInventory first = nameInventory second := by
  constructor
  · exact nameInventory_equation
  · intro same
    apply eq_of_countOut_eq
    intro name
    simpa only [nameInventory_count] using congrArg (Multiset.count name) same

/-- Name support of a process in this declared syntax. -/
def freeNames (term : Term psig [] PSrt.proc) : Set (Fin 3) :=
  {name | name ∈ nameInventory term}

theorem freeNames_iff_count (term : Term psig [] PSrt.proc) (name : Fin 3) :
    name ∈ freeNames term ↔ 0 < countOut name term := by
  change name ∈ nameInventory term ↔ 0 < countOut name term
  rw [← nameInventory_count name term, Multiset.count_pos]

/-- The literal support condition ranges over the whole scope extensions. -/
def ScopeGradeZero (left right : Term psig [] PSrt.proc → Prop) : Prop :=
  ∀ first second, left first → right second →
    Disjoint (freeNames first) (freeNames second)

/-- Inventory images retain the existence of their actual authored origins. -/
def inventoryScope (scope : Term psig [] PSrt.proc → Prop) : Multiset (Fin 3) → Prop :=
  fun inventory => ∃ term, scope term ∧ nameInventory term = inventory

theorem scopeGradeZero_iff_inventory (left right : Term psig [] PSrt.proc → Prop) :
    ScopeGradeZero left right ↔ GradeZero (inventoryScope left) (inventoryScope right) := by
  constructor
  · intro separated first second admittedFirst admittedSecond name memberFirst memberSecond
    obtain ⟨p, admittedP, rfl⟩ := admittedFirst
    obtain ⟨q, admittedQ, rfl⟩ := admittedSecond
    exact Set.disjoint_left.mp (separated p q admittedP admittedQ) memberFirst memberSecond
  · intro separated first second admittedFirst admittedSecond
    apply Set.disjoint_left.mpr
    intro name memberFirst memberSecond
    exact separated _ _ ⟨first, admittedFirst, rfl⟩ ⟨second, admittedSecond, rfl⟩
      name memberFirst memberSecond

/-- The shared-name grade-zero hypothesis earns the source split conclusion
for this independently presented free parallel syntax. -/
theorem unique_decomposition_of_scopeGradeZero
    {left right : Term psig [] PSrt.proc → Prop} (separated : ScopeGradeZero left right)
    {p q p' q' : Term psig [] PSrt.proc}
    (admittedP : left p) (admittedQ : right q)
    (admittedP' : left p') (admittedQ' : right q')
    (same : EqClosure ac1 (parT p q) (parT p' q')) :
    EqClosure ac1 p p' ∧ EqClosure ac1 q q' := by
  have inventoryEquation := nameInventory_equation same
  rw [nameInventory_par, nameInventory_par] at inventoryEquation
  obtain ⟨first, second⟩ := split_unique
    ((scopeGradeZero_iff_inventory left right).mp separated)
    ⟨p, admittedP, rfl⟩ ⟨q, admittedQ, rfl⟩
    ⟨p', admittedP', rfl⟩ ⟨q', admittedQ', rfl⟩ inventoryEquation
  exact ⟨equation_iff_nameInventory.mpr first, equation_iff_nameInventory.mpr second⟩

/-- The actual counterexample has disjoint predicate extensions and no
reductions, while sharing a name across admitted scope members. -/
theorem disjoint_inert_scopes_not_gradeZero : ¬ ScopeGradeZero phi psi := by
  intro separated
  have zeroMember : (0 : Fin 3) ∈ freeNames (u 0) := by
    rw [freeNames_iff_count]
    simp [u, countOut, countOutArgs, headCount]
  have sameName : (0 : Fin 3) ∈ freeNames (parT (u 0) (u 2)) := by
    rw [freeNames_iff_count, countOut_par]
    simp [u, countOut, countOutArgs, headCount]
  have rightAdmitted : psi (parT (u 0) (u 2)) := by
    simp [psi, countOut_par, u, countOut, countOutArgs, headCount]
  exact Set.disjoint_left.mp (separated _ _ split_left.1 rightAdmitted) zeroMember sameName

end Mettapedia.OSLF.Binding.ParallelFragment
