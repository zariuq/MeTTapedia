import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameWorklist
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameControls

/-!
# Executed flexible-pair controls for shared and disjoint parameter scopes

Disjoint scopes share a closed fresh helper. A nonempty overlap retains
exactly its corresponding formal positions, including reordered spines.
Repeated arguments admit distinct original answers; the fresh interface
does not falsely assert unique recovery of either original body.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameFlexPairControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualFrameWorklist

abbrev base := ContextualFrame.Controls.signature
local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)
def declaration (identity : Bool) : MetaArity base := if identity then ([()], ()) else ([(), ()], ())
abbrev extended := signature base declaration

def first {Γ : Ctx base} (left right : Term extended Γ ()) : Term extended Γ () :=
  .op (.inr (.mk false)) (.cons left (.cons right .nil))
def second {Γ : Ctx base} (argument : Term extended Γ ()) : Term extended Γ () :=
  .op (.inr (.mk true)) (.cons argument .nil)
def constant {Γ : Ctx base} : Term extended Γ () := .op (.inl .constant) .nil

def disjointLeft : Term extended [(), (), ()] () := first (.var .zero) (.var (.succ .zero))
def disjointRight : Term extended [(), (), ()] () := second (.var (.succ (.succ .zero)))
def disjoint : Problem declaration := [(observe disjointLeft, observe disjointRight)]
def overlapLeft : Term extended [(), (), ()] () := first (.var (.succ (.succ .zero))) (.var .zero)
def overlapRight : Term extended [(), (), ()] () := second (.var .zero)
def overlap : Problem declaration := [(observe overlapLeft, observe overlapRight)]
def repeatedLeft : Term extended [()] () := first (.var .zero) (.var .zero)
def repeatedRight : Term extended [()] () := second (.var .zero)
def repeated : Problem declaration := [(observe repeatedLeft, observe repeatedRight)]

def constantModel : Assignment declaration declaration
  | false => constant
  | true => constant

theorem constantModel_models_disjoint : Models constantModel disjoint := by
  apply (models_observed_iff constantModel _ _).mpr
  rfl

theorem constantModel_models_overlap : Models constantModel overlap := by
  apply (models_observed_iff constantModel _ _).mpr
  rfl

def pendingCount {problem : Problem declaration} : Result problem → Option Nat
  | .refuted _ => none
  | .residual update => some update.remaining.length

def rootArity {Next : Type} (next : Next → MetaArity base) :
    {Γ : Ctx base} → Term (signature base next) Γ () → Option Nat
  | _, .op (.inr (.mk identity)) _ => some (next identity).1.length
  | _, _ => none

def originalArity {problem : Problem declaration} (result : Result problem) (identity : Bool) : Option Nat :=
  match result with
  | .refuted _ => none
  | .residual update => rootArity update.declaration (update.answer identity)

def argumentIndices {Next : Type} (next : Next → MetaArity base) :
    {arities : List (MetaArity base)} → {Γ : Ctx base} →
      Args (signature base next) arities Γ → List (Option Nat)
  | _, _, .nil => []
  | _, _, .cons (.var position) rest => some (CommonABT.index position) :: argumentIndices next rest
  | _, _, .cons (.op _ _) rest => none :: argumentIndices next rest

def rootArguments {Next : Type} (next : Next → MetaArity base) :
    {Γ : Ctx base} → Term (signature base next) Γ () → List (Option Nat)
  | _, .op (.inr _) arguments => argumentIndices next arguments
  | _, _ => []

def originalArguments {problem : Problem declaration} (result : Result problem) (identity : Bool) : List (Option Nat) :=
  match result with
  | .refuted _ => []
  | .residual update => rootArguments update.declaration (update.answer identity)

theorem neither_side_can_first_recover_the_disjoint_dependency :
    (ContextualBindingWorklist.tryEquation (observe disjointLeft, observe disjointRight)).isSome = false := by
  decide +kernel

theorem disjoint_parameter_scopes_finish_with_a_fresh_interface :
    pendingCount (run 1 declaration disjoint) = some 0 := by
  rw [run_eq_local_on_model 1 disjoint declaration constantModel constantModel_models_disjoint]
  decide +kernel

theorem both_original_images_use_a_closed_helper :
    originalArity (run 1 declaration disjoint) false = some 0 ∧
    originalArity (run 1 declaration disjoint) true = some 0 := by
  rw [run_eq_local_on_model 1 disjoint declaration constantModel constantModel_models_disjoint]
  constructor <;> decide +kernel

theorem a_nonempty_overlap_keeps_one_parameter :
    originalArity (run 1 declaration overlap) false = some 1 := by
  rw [run_eq_local_on_model 1 overlap declaration constantModel constantModel_models_overlap]
  decide +kernel

theorem the_reordered_first_spine_keeps_its_second_formal_position :
    originalArguments (run 1 declaration overlap) false = [some 1] := by
  rw [run_eq_local_on_model 1 overlap declaration constantModel constantModel_models_overlap]
  decide +kernel

theorem the_second_spine_uses_its_own_corresponding_position :
    originalArguments (run 1 declaration overlap) true = [some 0] := by
  rw [run_eq_local_on_model 1 overlap declaration constantModel constantModel_models_overlap]
  decide +kernel

def firstSolution : Assignment declaration declaration
  | false => .var .zero
  | true => .var .zero
def secondSolution : Assignment declaration declaration
  | false => .var (.succ .zero)
  | true => .var .zero

theorem repeated_arguments_have_a_first_actual_solution : Models firstSolution repeated := by
  apply (models_observed_iff firstSolution repeatedLeft repeatedRight).mpr
  rfl

theorem repeated_arguments_have_a_different_actual_solution : Models secondSolution repeated := by
  apply (models_observed_iff secondSolution repeatedLeft repeatedRight).mpr
  rfl

theorem those_original_bodies_are_distinct : firstSolution false ≠ secondSolution false := by
  intro same
  cases same

theorem solving_the_repeated_equation_does_not_claim_unique_recovery :
    pendingCount (run 1 declaration repeated) = some 0 := by
  decide +kernel

theorem the_computed_flexible_pair_answer_satisfies_the_original_problem :
    ∃ update, run 1 declaration disjoint = .residual update ∧ update.remaining = [] ∧
      Models update.answer disjoint := by
  have count := disjoint_parameter_scopes_finish_with_a_fresh_interface
  generalize computed : run 1 declaration disjoint = result at count
  cases result with
  | refuted proof => cases count
  | residual update =>
      have empty : update.remaining = [] := by simpa using (Option.some.inj count)
      exact ⟨update, rfl, empty, update.completed empty⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameFlexPairControls
