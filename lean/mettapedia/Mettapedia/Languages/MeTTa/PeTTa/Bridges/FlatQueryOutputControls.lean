import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryOutputDomain
import Mettapedia.Tools.KernelReflexivity

/-! Output-domain controls keep finite head support distinct from ordered
producer multiplicity and include constants introduced only by the head. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryOutputDomain.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.GSLT.Dynamics ConjunctiveBindingDomain
open FlatQueryRowCodec FlatQueryConjunctionCompilation
open FlatQueryConjunctionCompilation.Controls (names patterns)

def rows : List Atom := [
  .expression [.symbol "r", .grounded (.int 0), .grounded (.int 1)],
  .expression [.symbol "r", .grounded (.int 0), .grounded (.int 1)],
  .expression [.symbol "s", .grounded (.int 1), .grounded (.int 2)],
  .expression [.symbol "s", .grounded (.int 1), .grounded (.int 2)]]

def legs : List (Leg integers names rows) := (compile integers names rows patterns).get (by decide +kernel)

def headSource : Atom := .expression [.symbol "out", .var "x", .var "z", .grounded (.int 9)]
def head : Head integers names := ⟨headSource, ⟨"out", by decide,
  [.variable ⟨0, by decide⟩, .variable ⟨2, by decide⟩, .constant 9], rfl⟩⟩
def environment : Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation.DenseEnvironment names Int := fun _ => none
def heads := [head]
def domain : Finset Int := derivedDomain environment legs heads
def headShapes : Finset (String × Nat) := derivedShapes heads
def payload : Atom := .expression [.symbol "out", .grounded (.int 0), .grounded (.int 2), .grounded (.int 9)]
def answer : Subst × List Nat := ([("z", .grounded (.int 2)), ("y", .grounded (.int 1)), ("x", .grounded (.int 0))], [0, 2])

theorem derived_domain_includes_head_only_constant : domain = {0, 1, 2, 9} := by decide +kernel
theorem actual_head_shape : headShapes = {("out", 3)} := by decide +kernel
theorem source_answer_present : answer ∈ sourceRun rows [] (legs.map Leg.source) := by decide +kernel
theorem actual_head_extracted : compileHead integers names headSource = some head := by kernel_reflexivity
theorem query_variables_covered : Covered environment (factors legs) :=
  (coveredCheck_iff _ _).mp (by decide +kernel)
theorem initial_bindings_represented : Represents integers names environment [] := by intro slot; rfl

theorem actual_payload_bounded : payload ∈ catalogue integers domain headShapes := by
  exact (checkRow_iff integers domain headShapes payload).mp (by decide +kernel)

theorem ignoring_head_constant_is_unsound :
    payload ∉ catalogue integers (inputDomain environment (factors legs)) headShapes := by
  rw [← checkRow_iff]
  decide +kernel

theorem four_witnesses_one_output_value :
    (sourceRun rows [] patterns).map (fun found => applySubst found.1 headSource) = List.replicate 4 payload := by
  decide +kernel

theorem catalogue_is_an_enclosure_not_the_answer_set :
    (catalogue integers domain headShapes).card = 64 ∧
      ((sourceRun rows [] patterns).map (fun found => applySubst found.1 headSource)).toFinset.card = 1 := by
  constructor
  · rw [catalogue_card, derived_domain_includes_head_only_constant, actual_head_shape]
    norm_num
  · decide +kernel

theorem no_default_for_unbound_output :
    ConjunctiveOutputDomain.instantiate (fun _ : Fin 1 => (none : Option Int)) [.variable 0] = none := rfl

theorem undeclared_output_variable_refuses :
    (compileHead integers names (.expression [.symbol "out", .var "unbound"])).isNone = true := by decide +kernel

theorem nullary_output_survives_empty_value_domain :
    ConjunctiveOutputDomain.catalogue (∅ : Finset Int) ({("done", 0)} : Finset (String × Nat)) = {("done", [])} := by
  decide +kernel

def before : Effects.State := NamedSpaces.Store.new rows []
def after : Effects.State := NamedSpaces.Store.new (rows ++ [payload]) []

theorem inserted : FreshInsertionSource.update before .self (applySubst answer.1 head.1) = some (after, true) := by
  rw [show applySubst answer.1 head.1 = payload from by decide +kernel]
  have reading : before.read .self = some rows := rfl
  have missing : payload ∉ rows := by decide +kernel
  have written : Effects.insert before .self payload = some after := rfl
  simp [FreshInsertionSource.update, reading, missing, written]

theorem source_derived_rank_decreases :
    FreshInsertionRank.remaining (catalogue integers domain headShapes) after.core + 1 =
      FreshInsertionRank.remaining (catalogue integers domain headShapes) before.core :=
  source_fresh_entry_decreases legs heads head List.mem_cons_self environment [] initial_bindings_represented
    query_variables_covered answer source_answer_present .self before after before.core after.core rfl rfl inserted

theorem unrelated_input_rows_do_not_consume_head_budget :
    FreshInsertionRank.remaining (catalogue integers domain headShapes) before.core = 64 := by
  have rejected : before.core.all (fun atom => !checkRow integers domain headShapes atom) = true := by decide +kernel
  have disjoint : Disjoint (catalogue integers domain headShapes) before.core.toFinset := by
    apply Finset.disjoint_right.mpr
    intro atom stored member
    have no := List.all_eq_true.mp rejected atom (List.mem_toFinset.mp stored)
    have yes := (checkRow_iff integers domain headShapes atom).mpr member
    simp only [yes, Bool.not_true, Bool.false_eq_true] at no
  unfold FreshInsertionRank.remaining
  rw [Finset.sdiff_eq_self_of_disjoint disjoint]
  exact catalogue_is_an_enclosure_not_the_answer_set.1

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryOutputDomain.Controls
