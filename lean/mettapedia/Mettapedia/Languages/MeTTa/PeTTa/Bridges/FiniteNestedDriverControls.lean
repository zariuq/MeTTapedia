import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryDriver
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryControls

/-! Source driver, sufficient allowance and exact-dispatch controls. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryDriver.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval SpaceSemantics NamedSpaces
open FlatQueryDomainInvariant FiniteNestedQueryCompletion
open FiniteNestedQuerySource.Controls (names queries head domain caller before after finalState
  bindings_valid entrance_valid no_head_constants second_round_preserves_domain rows)

def driver : String := "close-domain"
def expression : Atom := body queries head driver "out" "payload" "fresh"
def equation : Equation := ⟨driver, [.var "out"], expression⟩
def program : Program := {equations := [equation], declarations := []}
def certificate : Certificate program queries head driver "out" "payload" "fresh" .self :=
  (prepare program queries head driver "out" "payload" "fresh" .self).get (by decide +kernel)

theorem driver_is_extracted : (prepare program queries head driver "out" "payload" "fresh" .self).isSome = true := by
  decide +kernel

theorem static_coverage : Covered queries caller := (coveredCheck_iff queries caller).mp (by decide +kernel)
theorem data_head : DataHead head := by unfold DataHead; decide +kernel

theorem three_phase_trace :
    FiniteNestedQueryIteration.iterate queries head .self caller 3 before = some (finalState, [3, 3, 0]) := by
  kernel_reflexivity

theorem two_phases_are_not_completion :
    FiniteNestedQueryIteration.iterate queries head .self caller 2 before = none := by kernel_reflexivity

theorem no_allowance_is_not_a_zero_result :
    FiniteNestedQueryIteration.iterate queries head .self caller 0 before = none := rfl

theorem catalogue_bound_completes :
    ∃ result counts, FiniteNestedQueryIteration.iterate queries head .self caller
      (domain.card ^ head.2.cells.length + 1) before = some (result, counts) :=
  FiniteNestedQueryIteration.catalogue_allowance domain queries head data_head no_head_constants .self caller before before.core
    bindings_valid entrance_valid static_coverage rfl

theorem actual_recursive_source_returns_true :
    PureReturns program caller before (call driver "out") finalState (Effects.boolean true) :=
  certificate.calls caller before finalState rfl
    (body_returns certificate domain no_head_constants bindings_valid 3 before finalState [3, 3, 0] entrance_valid three_phase_trace)

theorem source_terminates_and_is_saturated :
    ∃ result counts,
      FiniteNestedQueryIteration.iterate queries head .self caller
        (domain.card ^ head.2.cells.length + 1) before = some (result, counts) ∧
      PureReturns program caller before (call driver "out") result (Effects.boolean true) ∧
      FreshNestedQuerySource.SaturatedAt result .self head.1 (queries.map Query.leg) caller :=
  terminates certificate domain data_head no_head_constants bindings_valid static_coverage before before.core entrance_valid rfl

theorem exact_count_balance :
    ∃ rows, finalState.read .self = some rows ∧
      FiniteNestedQueryRank.rank domain head rows + ([3, 3, 0] : List Nat).sum =
        FiniteNestedQueryRank.rank domain head before.core :=
  FiniteNestedQueryIteration.balance domain queries head no_head_constants .self caller 3 before finalState before.core [3, 3, 0]
    bindings_valid entrance_valid rfl three_phase_trace

def unmatched : Equation := ⟨driver, [.grounded (.int 7)], .symbol "unreachable"⟩
def withUnmatched : Program := {program with equations := [unmatched, equation]}

theorem unmatched_equation_is_ignored_by_actual_dispatch :
    (prepare withUnmatched queries head driver "out" "payload" "fresh" .self).isSome = true := by decide +kernel

def unmatchedCertificate : Certificate withUnmatched queries head driver "out" "payload" "fresh" .self :=
  (prepare withUnmatched queries head driver "out" "payload" "fresh" .self).get (by decide +kernel)

theorem unmatched_equation_preserves_source_execution :
    PureReturns withUnmatched caller before (call driver "out") finalState (Effects.boolean true) :=
  unmatchedCertificate.calls caller before finalState rfl
    (body_returns unmatchedCertificate domain no_head_constants bindings_valid 3 before finalState [3, 3, 0] entrance_valid three_phase_trace)

def productive : Equation := ⟨driver, [.var "out"], Effects.boolean false⟩
def withProductive : Program := {program with equations := [equation, productive]}

theorem extra_productive_equation_refuses :
    (prepare withProductive queries head driver "out" "payload" "fresh" .self).isNone = true := by decide +kernel

def wrongBody : Program := {program with equations := [⟨driver, [.var "out"], Effects.boolean true⟩]}

theorem same_spelling_does_not_certify_a_driver :
    (prepare wrongBody queries head driver "out" "payload" "fresh" .self).isNone = true := by decide +kernel

def renamed : Program :=
  {equations := [⟨"iterate-renamed", [.var "destination"],
    body queries head "iterate-renamed" "destination" "local-row" "delta"⟩], declarations := []}

theorem renamed_source_is_admitted :
    (prepare renamed queries head "iterate-renamed" "destination" "local-row" "delta" .self).isSome = true := by decide +kernel

theorem occupied_progress_name_refuses :
    (prepare program queries head driver "out" "payload" "out" .self).isNone = true := by decide +kernel

theorem query_capture_cannot_be_the_temporary :
    (prepare program queries head driver "out" "x" "fresh" .self).isNone = true := by decide +kernel

def reflectedProgram : Program :=
  {equations := [equation, unmatched], declarations := [], facts := rows,
    layout := [.fact, .fact, .fact, .equation, .equation]}

def reflectedBefore : Effects.State := Store.new (loadedAtoms reflectedProgram) []

def reflectedCertificate : Certificate reflectedProgram queries head driver "out" "payload" "fresh" .self :=
  (prepare reflectedProgram queries head driver "out" "payload" "fresh" .self).get (by decide +kernel)

theorem reflected_equations_remain_in_the_input_space :
    reflectedBefore.core = rows ++ [equation.toAtom, unmatched.toAtom] := rfl

theorem reflected_input_is_domain_admitted : ViewsInDomain domain queries reflectedBefore :=
  (validateViews_iff domain queries reflectedBefore).mp (by decide +kernel)

theorem actual_loaded_source_terminates :
    ∃ result counts,
      FiniteNestedQueryIteration.iterate queries head .self caller
        (domain.card ^ head.2.cells.length + 1) reflectedBefore = some (result, counts) ∧
      PureReturns reflectedProgram caller reflectedBefore (call driver "out") result (Effects.boolean true) ∧
      FreshNestedQuerySource.SaturatedAt result .self head.1 (queries.map Query.leg) caller :=
  terminates reflectedCertificate domain data_head no_head_constants bindings_valid static_coverage reflectedBefore
    reflectedBefore.core reflected_input_is_domain_admitted rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryDriver.Controls
