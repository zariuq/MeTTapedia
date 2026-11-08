import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalCheckRegions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CheckStability
import Mettapedia.Logic.LP.TermEquality

/-!
# Executable certain-check admission for the first-order profile

The existing total occurs-checked unifier decides compatibility with each
candidate occurrence. Equality, absence and exact counts are accepted exactly
when the equation store is consistent and the check holds in every model.
Counts concern physical identities, without an independence assumption.

A false result denies this certain-check admission. It may represent a
pending guard, rather than a proof that the guard is false in every model.
This profile does not restrict other term theories or unification fragments.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderChecks

open Mettapedia.Logic.LP

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  {O : Type} [DecidableEq O]

abbrev A := FirstOrder.action signature

def compatible (problem : EquationStore (Term signature)) (left right : Term signature) : Bool :=
  (unifyTotal (problem ++ [(left, right)])).isSome

theorem compatible_iff (problem : EquationStore (Term signature)) (left right : Term signature) :
    compatible problem left right = true ↔ A.Consistent (problem ++ [(left, right)]) := by
  rw [compatible, Option.isSome_iff_exists]
  exact FirstOrder.accepted_iff_consistent _

def possible (problem : EquationStore (Term signature)) (label : O → Term signature)
    (world : Finset O) (pattern : Term signature) : Finset O :=
  world.filter fun occurrence => compatible problem pattern (label occurrence) = true

def certain (answer : Subst signature) (label : O → Term signature)
    (world : Finset O) (pattern : Term signature) : Finset O :=
  world.filter fun occurrence => answer.applyTerm pattern = answer.applyTerm (label occurrence)

omit [DecidableEq O] in
theorem possible_eq (problem : EquationStore (Term signature)) (label : O → Term signature)
    (world : Finset O) (pattern : Term signature) :
    possible problem label world pattern = PrincipalCheckRegions.possibleRegion A problem label world pattern := by
  classical
  ext occurrence
  simp only [possible, PrincipalCheckRegions.possibleRegion, Finset.mem_filter, compatible_iff]

omit [DecidableEq O] in
theorem certain_eq (answer : Subst signature) (label : O → Term signature)
    (world : Finset O) (pattern : Term signature) :
    certain answer label world pattern = Check.matches A answer label world pattern := by
  classical
  ext occurrence
  simp only [certain, Check.matches, Finset.mem_filter, FirstOrder.action]

def acceptsCertainCheck (problem : EquationStore (Term signature)) (label : O → Term signature)
    (world : Finset O) (check : Check (Term signature)) : Bool :=
  match unifyTotal problem with
  | none => false
  | some answer => match check with
    | .equal left right => decide (answer.applyTerm left = answer.applyTerm right)
    | .absent pattern => decide (possible problem label world pattern = ∅)
    | .count pattern number => decide ((certain answer label world pattern).card = number ∧
        possible problem label world pattern = certain answer label world pattern)

theorem accepts_iff (problem : EquationStore (Term signature)) (label : O → Term signature)
    (world : Finset O) (check : Check (Term signature)) :
    acceptsCertainCheck problem label world check = true ↔
      A.Consistent problem ∧ A.Entails problem (fun assignment => check.Holds A assignment label world) := by
  cases computed : unifyTotal problem with
  | none =>
      have inconsistent := (FirstOrder.refused_iff_inconsistent problem).mp computed
      simp only [acceptsCertainCheck, computed, Bool.false_eq_true, false_iff]
      exact fun admitted => inconsistent admitted.1
  | some answer =>
      have principal := FirstOrder.accepted_principal problem answer computed
      have consistent : A.Consistent problem := ⟨answer, principal.sound⟩
      simp only [acceptsCertainCheck, computed, consistent, true_and]
      cases check with
      | equal left right =>
          rw [decide_eq_true_eq]
          have interface := SubstitutionAction.Principal.on A principal [left, right]
          exact (PrincipalCheckRegions.equal_iff_principal_answer A interface left right
            (by simp) (by simp)).symm
      | absent pattern =>
          rw [decide_eq_true_eq, possible_eq]
          exact (PrincipalCheckRegions.absent_iff_possible_empty A problem label world pattern).symm
      | count pattern number =>
          rw [decide_eq_true_eq, possible_eq, certain_eq]
          have interface := SubstitutionAction.Principal.on A principal (pattern :: world.toList.map label)
          exact (PrincipalCheckRegions.count_iff_regions A interface label world pattern number
            List.mem_cons_self (fun occurrence member =>
              List.mem_cons_of_mem _ (List.mem_map.mpr ⟨occurrence, Finset.mem_toList.mpr member, rfl⟩))).symm

omit [DecidableEq O] in
/-- The existing complete first-order solver constructs a candidate scan
covering every matching occurrence in every permitted solution. -/
theorem possible_covers (problem : EquationStore (Term signature)) (label : O → Term signature)
    (world : Finset O) (pattern : Term signature) :
    Check.CoversMatches A problem label (possible problem label world pattern) world pattern := by
  intro assignment model occurrence present same
  apply Finset.mem_filter.mpr
  refine ⟨present, (compatible_iff problem pattern (label occurrence)).mpr ?_⟩
  refine ⟨assignment, (A.models_append _ _ _).mpr ⟨model, ?_⟩⟩
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  exact same

/-- A covered restriction preserves the actual executable absence verdict,
including its consistency check. Partial unqualified scans get no such law. -/
theorem absent_accepts_iff_of_covered (problem : EquationStore (Term signature))
    (label : O → Term signature) (visible world : Finset O) (pattern : Term signature)
    (included : visible ⊆ world)
    (covered : Check.CoversMatches A problem label visible world pattern) :
    acceptsCertainCheck problem label visible (.absent pattern) = true ↔
      acceptsCertainCheck problem label world (.absent pattern) = true := by
  rw [accepts_iff, accepts_iff, Check.entails_absent_iff_of_covered A included covered]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderChecks
