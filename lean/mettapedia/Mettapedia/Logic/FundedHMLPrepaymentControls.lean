import Mettapedia.Logic.FundedHMLPrepayment
import Mettapedia.Logic.HMLStackControls

/-!
# Independent prepaid judgments, interrupted prefixes and rejected programs

Direct rule trees admit a variable/negation program and a duplicate-sensitive
gather with a retained stack suffix. Actual prefix transport keeps the original
remaining instruction judgment. An interrupted funded prefix is quiet but can
advance; its underfunded counterpart retains calculation evidence without
prepayment. Malformed programs have no admission even with an ample purse.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalMuCalculus.StackInspection.PrepaymentControls

open Inspection Funded Controls
open Mettapedia.GSLT.Causality.OccurrenceHistory

def direct : PrepaidProgram environment [.variable 0 true, .negate] [] [false] 2 :=
  .instruction (.readVariable 0 true [])
    (.instruction (.negate true []) (.finish [false] 0))

def gathered : PrepaidProgram environment [.literal true, .literal false, .gatherAll 2]
    [true] [false, true] 3 :=
  .instruction (.literal true [true])
    (.instruction (.literal false [true, true])
      (.instruction (.gatherAll [false, true] [true]) (.finish [false, true] 0)))

theorem independent_rule_tree_reads_actual_variable :
    execute environment [.variable 0 true, .negate] [] = some [false] := direct.computed environment

theorem full_gather_and_suffix_retained :
    execute environment [.literal true, .literal false, .gatherAll 2] [true] = some [false, true] :=
  gathered.computed environment

theorem composition_of_separate_paid_blocks :
    Nonempty (PrepaidProgram environment [.literal true, .negate] [true] [false, true] 2) := by
  let first : PrepaidProgram environment [.literal true] [true] [true, true] 1 :=
    .instruction (.literal true [true]) (.finish [true, true] 0)
  let second : PrepaidProgram environment [.negate] [true, true] [false, true] 1 :=
    .instruction (.negate true [true]) (.finish [false, true] 0)
  exact ⟨first.append environment second⟩

def initial : Configuration Bool 1 := ⟨[.variable 0 true, .negate], [], 2, 0⟩
def interrupted : Configuration Bool 1 := ⟨[.negate], [true], 1, 1⟩
def finished : Configuration Bool 1 := ⟨[], [false], 0, 2⟩

def firstTick : Tick environment (.variable 0 true) initial interrupted := ⟨rfl, rfl, rfl, rfl⟩
def lastTick : Tick environment .negate interrupted finished := ⟨rfl, rfl, rfl, rfl⟩

def firstPath : Path environment initial interrupted :=
  .cons ⟨.variable 0 true, firstTick⟩ (.refl (P := presentation environment) interrupted)

def lastPath : Path environment interrupted finished :=
  .cons ⟨.negate, lastTick⟩ (.refl (P := presentation environment) finished)

def current : Prepayment environment interrupted [false] := transportPrepayment environment firstPath direct

theorem original_suffix_judgment_retained :
    current = PrepaidProgram.instruction (.negate true []) (.finish [false] 0) := rfl

theorem supplied_prepayment_composes :
    transportPrepayment environment (OccurrencePath.append firstPath lastPath) direct =
      transportPrepayment environment lastPath current :=
  transportPrepayment_composition environment firstPath lastPath direct

theorem interrupted_quiet_but_not_maximal :
    publicAnswer interrupted = none ∧ ¬ Maximal environment interrupted := by
  refine ⟨by decide, ?_⟩
  intro maximal
  exact maximal finished ⟨⟨.negate, lastTick⟩⟩

theorem completed_maximal : Maximal environment finished := by
  rintro target ⟨⟨opcode, event⟩⟩
  have pending := event.pending
  change [] = opcode :: target.pending at pending
  cases pending

theorem every_independently_supplied_maximal_prefix (target : Configuration Bool 1)
    (path : Path environment initial target) (maximal : Maximal environment target) :
    target.pending = [] ∧ target.stack = [false] ∧ target.spent = 2 := by
  simpa only [initial, List.length_cons, List.length_nil, Nat.zero_add] using
    every_maximal_prepaid_prefix_finishes environment [false] direct path maximal

theorem completed_actual_instruction_account :
    (instructionAccount environment).onPath (OccurrencePath.append firstPath lastPath) = 2 := by decide

theorem insufficient_purse_rejected :
    ¬ Nonempty (PrepaidProgram environment [.variable 0 true, .negate] [] [false] 1) := by
  rintro ⟨accepted⟩
  have funded := accepted.funding environment
  change (2 : Nat) ≤ 1 at funded
  omega

theorem residual_calculation_does_not_supply_prepayment :
    Nonempty (ResidualEvidence environment intermediate.endpoint) ∧
      ¬ Nonempty (Prepayment environment intermediate.endpoint [false]) := by
  refine ⟨⟨⟨[false], residual_evidence_at_incomplete_endpoint⟩⟩, ?_⟩
  rintro ⟨accepted⟩
  have funded := accepted.funding environment
  change (1 : Nat) ≤ 0 at funded
  omega

theorem malformed_program_has_no_admission (output : List Bool) :
    ¬ Nonempty (PrepaidProgram environment [.negate] [] output 25) := by
  rintro ⟨accepted⟩
  have computed := accepted.computed environment
  simp only [execute, Instruction.execute, Option.bind_none] at computed
  cases computed

theorem one_value_cannot_fund_a_two_occurrence_gather (output : List Bool) :
    ¬ Nonempty (PrepaidProgram environment [.gatherAll 2] [true] output 1) := by
  rintro ⟨accepted⟩
  have computed := accepted.computed environment
  have rejected : execute environment [.gatherAll 2] [true] = none := by decide
  rw [rejected] at computed
  cases computed

theorem source_formula_prepayment_boundary :
    Nonempty (PrepaidProgram environment (compile quiescent compound rfl true)
      [false] [false, false] 6) ∧
      ¬ Nonempty (PrepaidProgram environment (compile quiescent compound rfl true)
        [false] [false, false] 5) := by
  have computation := compound_instruction_readout.2.1
  have price : (compile quiescent compound rfl true).length = 6 := by decide
  constructor
  · exact ⟨PrepaidProgram.reconstruct environment _ _ _ _ computation (price ▸ le_rfl)⟩
  · rintro ⟨accepted⟩
    have funded := accepted.funding environment
    rw [price] at funded
    omega

end Mettapedia.Logic.ModalMuCalculus.StackInspection.PrepaymentControls
