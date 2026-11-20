import Mettapedia.Logic.LP.DirectionalMatching
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.TermRewriting

/-!
# Executable root-schema evaluation using the existing first-order matcher

The input is a finite table of actual left/right patterns and a ground row.
Each schema is matched by `DirectionalMatching.matchMany`; its right side is
then instantiated using the computed substitution. No source-machine case
analysis is used by the evaluator.

For range-restricted schemas, membership in the computed successor list is
exactly `Machines.RootStep`. This is a statement about possible results;
duplicate table entries can repeat a result in the list. Actual native
firings are connected by the existing root-rule correspondence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table

open Mettapedia.Logic.LP
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic
open RuleSyntax.Machines (unknowns mem_unknowns vars_of_mem_unknowns RootStep rootRules
  ReadsBag firing_of_rootStep rootStep_of_firing)

abbrev Schema := Tm × Tm

/-- Ground any variables outside the matched support. Range restriction
ensures those choices cannot affect a licensed right side. -/
def groundAssignment (substitution : Subst rowSig) (name : Nat) : Expr :=
  inst (fun _ => .sym 0) (substitution name)

theorem inst_groundAssignment (substitution : Subst rowSig) : ∀ term : Tm,
    inst (groundAssignment substitution) term = inst (fun _ => .sym 0) (substitution.applyTerm term)
  | .var _ => rfl
  | .const (.sym _) => rfl
  | .const (.name _) => rfl
  | .app .app terms => by
      change Expr.app (inst (groundAssignment substitution) (terms head))
        (inst (groundAssignment substitution) (terms tail)) =
        Expr.app (inst (fun _ => .sym 0) (substitution.applyTerm (terms head)))
          (inst (fun _ => .sym 0) (substitution.applyTerm (terms tail)))
      rw [inst_groundAssignment substitution (terms head), inst_groundAssignment substitution (terms tail)]
  | .app .code terms => by
      change Expr.code (inst (groundAssignment substitution) (terms body)) =
        Expr.code (inst (fun _ => .sym 0) (substitution.applyTerm (terms body)))
      rw [inst_groundAssignment substitution (terms body)]

def applySchema (schema : Schema) (row : Expr) : Option Expr :=
  (DirectionalMatching.matchMany [(schema.1, toTerm row)]).map
    (fun substitution => inst (groundAssignment substitution) schema.2)

private theorem matched_ground {pattern : Tm} {row : Expr} {substitution : Subst rowSig}
    (accepted : DirectionalMatching.matchMany [(pattern, toTerm row)] = some substitution) :
    inst (groundAssignment substitution) pattern = row := by
  have matching := (DirectionalMatching.matchMany_sound _ substitution accepted).2
    (pattern, toTerm row) (List.mem_singleton_self _)
  rw [inst_groundAssignment, matching, inst_toTerm]

theorem applySchema_sound {schema : Schema} {row result : Expr}
    (accepted : applySchema schema row = some result) :
    ∃ assignment : Nat → Expr, inst assignment schema.1 = row ∧ inst assignment schema.2 = result := by
  obtain ⟨substitution, matched, output⟩ := Option.map_eq_some_iff.mp accepted
  exact ⟨groundAssignment substitution, matched_ground matched, output⟩

private theorem match_exists (pattern : Tm) (row : Expr) (assignment : Nat → Expr)
    (matched : inst assignment pattern = row) :
    ∃ substitution, DirectionalMatching.matchMany [(pattern, toTerm row)] = some substitution := by
  apply DirectionalMatching.matchMany_complete _ (lift assignment)
  · intro name member
    have occurs : name ∈ (toTerm row).freeVars := by
      simpa only [DirectionalMatching.subjectVars, Finset.union_empty] using member
    exact False.elim (vars_toTerm row name occurs)
  · intro pair member
    have same := List.mem_singleton.mp member
    subst pair
    show (lift assignment).applyTerm pattern = toTerm row
    rw [applyTerm_lift, matched]

theorem applySchema_complete {schema : Schema}
    (closed : ∀ name ∈ unknowns schema.2, name ∈ unknowns schema.1)
    (assignment : Nat → Expr) {row : Expr} (matched : inst assignment schema.1 = row) :
    applySchema schema row = some (inst assignment schema.2) := by
  obtain ⟨substitution, accepted⟩ := match_exists schema.1 row assignment matched
  have first := matched_ground accepted
  have output : inst (groundAssignment substitution) schema.2 = inst assignment schema.2 := by
    apply inst_congr
    intro name used
    exact agree_of_inst_eq schema.1 (first.trans matched.symm) name
      (vars_of_mem_unknowns schema.1 (closed name (mem_unknowns schema.2 used)))
  simp only [applySchema, accepted, Option.map_some, output]

/-- A failed match excludes that schema, rather than refuting a program
whose other schemas may still apply. -/
theorem applySchema_none_iff (schema : Schema) (row : Expr) :
    applySchema schema row = none ↔ ¬ ∃ assignment : Nat → Expr, inst assignment schema.1 = row := by
  constructor
  · rintro refused ⟨assignment, matched⟩
    obtain ⟨substitution, accepted⟩ := match_exists schema.1 row assignment matched
    simp [applySchema, accepted] at refused
  · intro impossible
    cases result : applySchema schema row with
    | none => rfl
    | some output =>
        obtain ⟨assignment, matched, _⟩ := applySchema_sound result
        exact False.elim (impossible ⟨assignment, matched⟩)

def successors (schemas : List Schema) (row : Expr) : List Expr :=
  schemas.filterMap (fun schema => applySchema schema row)

theorem mem_successors_iff (schemas : List Schema)
    (closed : ∀ schema ∈ schemas, ∀ name ∈ unknowns schema.2, name ∈ unknowns schema.1)
    (row result : Expr) : result ∈ successors schemas row ↔ RootStep schemas row result := by
  constructor
  · intro member
    obtain ⟨schema, present, accepted⟩ := List.mem_filterMap.mp member
    obtain ⟨assignment, matched, output⟩ := applySchema_sound accepted
    exact ⟨schema, present, assignment, matched, output⟩
  · rintro ⟨schema, present, assignment, matched, output⟩
    apply List.mem_filterMap.mpr
    refine ⟨schema, present, ?_⟩
    rw [← output]
    exact applySchema_complete (closed schema present) assignment matched

theorem successors_empty_iff (schemas : List Schema)
    (closed : ∀ schema ∈ schemas, ∀ name ∈ unknowns schema.2, name ∈ unknowns schema.1)
    (row : Expr) : successors schemas row = [] ↔ ¬ ∃ result, RootStep schemas row result := by
  rw [List.eq_nil_iff_forall_not_mem]
  constructor
  · rintro empty ⟨result, stepped⟩
    exact empty result ((mem_successors_iff schemas closed row result).mpr stepped)
  · intro noStep result member
    exact noStep ⟨result, (mem_successors_iff schemas closed row result).mp member⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.applySchema_sound
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.applySchema_complete
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.Table.mem_successors_iff
