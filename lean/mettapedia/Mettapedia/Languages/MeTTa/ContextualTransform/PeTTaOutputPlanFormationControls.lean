import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanProgramFormation
import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanFormationDepth
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaOutputPlanControls

/-!
# Formation controls for retained source and ordered code

The positive quotation rule is independent of payload callability. Negative
controls remove a directive, remove a clause, swap distinct interfaces or
replace the retained source. Each mutation violates an actual formation law,
not merely an implementation-specific output snapshot.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaOutputPlanFormationControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open OutputPlan

theorem quotation_has_formation (context : Context) (payload : Atom) :
    ExpressionRel context (hold payload) (Plan.value payload) := by
  let entry := Supply.start [hold payload]
  have normalizedValue : normalized ⟨entry,Plan.value payload⟩ = Plan.value payload := by
    simp only [normalized,Supply.plan,Supply.normalize,entry,Supply.start,Plan.value]
    congr 1
    exact Unifying.resolve_of_unbound _ (by intro name present; rfl)
  rw [← normalizedValue]
  apply ExpressionRel.formed
  change Layer context _ entry (classify (hold payload)) ⟨entry,Plan.value payload⟩
  change Layer context _ entry (.quoted payload) ⟨entry,Plan.value payload⟩
  exact .quoted entry payload

theorem erasing_nonempty_directives_invalid {source : SpaceSemantics.Program} {policy : BranchPolicy}
    (target : Program) (nonempty : source.initializers ≠ []) :
    ¬ProgramRel source policy {target with queries := []} := by
  intro invalid
  have count := program_directive_count invalid
  have empty : source.initializers = [] := List.length_eq_zero_iff.mp count.symm
  exact nonempty empty

theorem removing_a_clause_invalid {source : SpaceSemantics.Program} {policy : BranchPolicy} {target : Program}
    (original : ProgramRel source policy target) (nonempty : target.code ≠ []) :
    ¬ProgramRel source policy {target with code := target.code.tail} := by
  intro invalid
  have before := program_equation_count original
  have after := program_equation_count invalid
  have positive : 0 < target.code.length := List.length_pos_iff.mpr nonempty
  simp only [List.length_tail] at after
  omega

theorem swapped_distinct_interfaces_invalid {source : SpaceSemantics.Program} {policy : BranchPolicy}
    {target : Program} (original : ProgramRel source policy target)
    (first second : SpaceSemantics.Equation) (rest : List SpaceSemantics.Equation)
    (code : target.code = first :: second :: rest) (different : first.head ≠ second.head) :
    ¬ProgramRel source policy {target with code := second :: first :: rest} := by
  intro invalid
  have before := program_interface_order original
  have after := program_interface_order invalid
  rw [code] at before
  have same := before.symm.trans after
  simp only [List.map_cons,List.cons.injEq,Option.some.injEq] at same
  exact different same.1

theorem replacing_source_invalid {source : SpaceSemantics.Program} {policy : BranchPolicy}
    (target : Program) (other : SpaceSemantics.Program) (different : other ≠ source) :
    ¬ProgramRel source policy {target with source := other} := by
  intro invalid
  exact different (program_retains_source invalid)

theorem unsupported_has_no_formation (context : Context) (depth : Nat) (supply : Supply)
    (expression : Atom) (result : Result) (unsupported : classify expression = .unsupported) :
    ¬FormationAt context depth supply expression result := by
  cases depth with
  | zero => exact False.elim
  | succ depth =>
      intro rule
      change Layer context (FormationAt context depth) supply (classify expression) result at rule
      rw [unsupported] at rule
      cases rule

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaOutputPlanFormationControls
