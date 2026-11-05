import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQuerySource
import Mettapedia.Tools.KernelReflexivity

/-! Matching writes preserve a finite domain without preserving old query
answers. Current-state nested reads and data-only refusal are explicit. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQuerySource.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
open Mettapedia.GSLT.Dynamics ConjunctiveRegionProvenance
open FlatQueryRowCodec FlatQueryDomainInvariant
open Eval SpaceSemantics NamedSpaces EffectfulQuerySource

def names : Inventory String := ⟨["x", "u", "v"], by decide⟩
def number (value : Int) : Atom := .grounded (.int value)
def app (head : String) (fields : List Atom) : Atom := .expression (.symbol head :: fields)
def stepPattern : Atom := app "step" [.var "x"]
def pairPattern : Atom := app "p" [.var "u", .var "v"]
def stepQuery : Query integers names := ⟨.self, stepPattern, ⟨"step", by decide, [.variable ⟨0, by decide⟩], rfl⟩, by decide⟩
def pairQuery : Query integers names := ⟨.self, pairPattern, ⟨"p", by decide,
  [.variable ⟨1, by decide⟩, .variable ⟨2, by decide⟩], rfl⟩, by decide⟩
def queries := [stepQuery, pairQuery]
def head : FlatQueryOutputDomain.Head integers names := ⟨app "p" [.var "x", .var "u"],
  ⟨"p", by decide, [.variable ⟨0, by decide⟩, .variable ⟨1, by decide⟩], rfl⟩⟩
def domain : Finset Int := {0, 1, 2}
def pair (first second : Int) : Atom := app "p" [number first, number second]
def rows : List Atom := [app "step" [number 1], app "step" [number 2], pair 0 0]
def before : Effects.State := Store.new rows []
def after : Effects.State := Store.new (rows ++ [pair 1 0, pair 2 0, pair 2 1]) []
def finalState : Effects.State := Store.new (rows ++ [pair 1 0, pair 2 0, pair 2 1, pair 1 1, pair 1 2, pair 2 2]) []
def caller : Subst := [("out", .symbol "&self")]
def program : Program := {equations := [], declarations := []}

theorem bindings_valid : BindingsInDomain integers names domain caller :=
  (validateBindings_iff integers names domain caller).mp (by decide +kernel)

theorem entrance_valid : ViewsInDomain domain queries before :=
  (validateViews_iff domain queries before).mp (by decide +kernel)

theorem no_head_constants (value : Int) : Cell.constant value ∈ head.2.cells → value ∈ domain := by
  simp [head]

theorem first_round_finds_three_fresh_rows : run queries head .self caller before =
    some (after, List.replicate 3 (Effects.boolean true)) := by kernel_reflexivity

theorem first_round_preserves_domain : ViewsInDomain domain queries after :=
  run_preserves domain queries queries (fun _ member => member) head no_head_constants .self caller before after _
    bindings_valid entrance_valid first_round_finds_three_fresh_rows

theorem second_round_finds_three_more : run queries head .self caller after =
    some (finalState, List.replicate 3 (Effects.boolean true)) := by kernel_reflexivity

theorem second_round_preserves_domain : ViewsInDomain domain queries finalState :=
  run_preserves domain queries queries (fun _ member => member) head no_head_constants .self caller after finalState _
    bindings_valid first_round_preserves_domain second_round_finds_three_more

theorem third_round_is_quiet : run queries head .self caller finalState = some (finalState, []) := by kernel_reflexivity

theorem source_first_round_returns_three : Returns program caller before
    (NestedQuerySource.source (queries.map Query.leg) (FreshQueryMaterialization.bodySource "out" "payload" head.1))
    after (List.replicate 3 (Effects.boolean true)) :=
  source_returns domain queries head no_head_constants program "out" "payload" .self caller before after _
    bindings_valid entrance_valid (by decide) (by decide +kernel) ⟨rfl, rfl⟩ first_round_finds_three_fresh_rows

theorem source_second_round_returns_three : Returns program caller after
    (NestedQuerySource.source (queries.map Query.leg) (FreshQueryMaterialization.bodySource "out" "payload" head.1))
    finalState (List.replicate 3 (Effects.boolean true)) :=
  source_returns domain queries head no_head_constants program "out" "payload" .self caller after finalState _
    bindings_valid first_round_preserves_domain (by decide) (by decide +kernel) ⟨rfl, rfl⟩ second_round_finds_three_more

theorem source_third_round_has_no_fresh_answers : Returns program caller finalState
    (NestedQuerySource.source (queries.map Query.leg) (FreshQueryMaterialization.bodySource "out" "payload" head.1))
    finalState [] :=
  source_returns domain queries head no_head_constants program "out" "payload" .self caller finalState finalState []
    bindings_valid second_round_preserves_domain (by decide) (by decide +kernel) ⟨rfl, rfl⟩ third_round_is_quiet

theorem final_state_is_saturated_for_the_schema :
    FreshNestedQuerySource.SaturatedAt finalState .self head.1 (queries.map Query.leg) caller :=
  (quiet_is_saturated domain queries head no_head_constants .self caller finalState finalState
    bindings_valid second_round_preserves_domain third_round_is_quiet).2

theorem domain_preservation_is_not_query_view_preservation :
    (choices caller pairPattern before.core).length = 1 ∧
      (choices caller pairPattern after.core).length = 4 := by decide +kernel

theorem outside_value_rejects_current_read :
    validateViews domain queries (Store.new (rows ++ [pair 3 0]) []) = false := by decide +kernel

theorem relevant_open_row_rejects_current_read :
    validateViews domain queries (Store.new (rows ++ [app "p" [.var "open", number 0]]) []) = false := by decide +kernel

theorem unrelated_open_row_is_not_a_domain_value :
    validateViews domain queries (Store.new (rows ++ [app "unrelated" [.var "open"]]) []) = true := by decide +kernel

theorem out_of_domain_capture_refuses :
    validateBindings integers names domain (("x", number 3) :: caller) = false := by decide +kernel

theorem unsupported_capture_is_not_an_unbound_slot :
    validateBindings integers names domain (("x", Effects.boolean true) :: caller) = false := by decide +kernel

theorem unbound_output_refuses : emit head .self caller before = none := by kernel_reflexivity

def declaration : FlatQueryOutputDomain.Head integers names := ⟨app ":" [number 1, number 2],
  ⟨":", by decide, [.constant 1, .constant 2], rfl⟩⟩

theorem declaration_write_refuses : emit declaration .self caller before = none := by kernel_reflexivity

theorem active_query_is_not_compiled :
    (compileQuery integers names .self (.expression [.symbol ",", .var "x", .var "u"])).isNone = true := by decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQuerySource.Controls
