import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanNames
import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanGate
import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanPolicy
import Lean.Elab.Tactic.Cbv

/-!
# Exposed results and the source branch-alias counterexample

The source fixtures distinguish literal-output native rejection and SWI's
compile-time branch aliases. In particular, an inert binding is not uniformly
erasable in that frontend. Corrected dialects require their own stated policy.
These finite controls do not assert whole compiler or native correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaOutputPlanControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open OutputPlan (call)

def plain : SpaceSemantics.Equation :=
  ⟨"plain-choice",[.var "x",.var "y"],call "superpose" [.expression [.var "x",.var "y"]]⟩
def wrapped : SpaceSemantics.Equation :=
  ⟨"wrapped-choice",[.var "x",.var "y"],call "superpose" [.expression
    [call "let" [.var "unused1",Effects.boolean true,.var "x"],
     call "let" [.var "unused2",Effects.boolean true,.var "y"]]]⟩
def source : SpaceSemantics.Program :=
  {equations := [plain,wrapped],declarations := [],layout := [.equation,.equation]}

def outputs (program : SpaceSemantics.Program) (expression : Atom)
    (policy : OutputPlan.BranchPolicy := .swiAliases) : Option (List Atom) := do
  let compiled ← OutputPlan.compileProgram {program with initializers := [expression]} policy
  match compiled.queries with
  | [query] =>
      match Streaming.run program 1500
          (Streaming.enter {state := Effects.loaded program,privateCode := compiled.code} query) with
      | .complete reached => some (Streaming.values reached)
      | _ => none
  | _ => none

theorem branch_builder_can_alias_formal_inputs_during_compilation :
    (OutputPlan.compileProgram source).map (fun compiled =>
      compiled.code.map fun equation =>
        (equation.arguments.length,equation.arguments[0]? == equation.arguments[1]?)) =
        some [(3,false),(3,true)] := by decide +kernel

theorem pure_branches_keep_distinct_input_answers :
    outputs source (call "collapse" [call "plain-choice" [.symbol "a",.symbol "b"]]) =
      some [.expression [.symbol "a",.symbol "b"]] := by decide +kernel

theorem inert_wrapped_branches_can_reject_distinct_inputs :
    outputs source (call "collapse" [call "wrapped-choice" [.symbol "a",.symbol "b"]]) =
      some [.expression []] := by decide +kernel

theorem source_inert_branch_wrapping_is_observable :
    outputs source (call "collapse" [call "plain-choice" [.symbol "a",.symbol "b"]]) ≠
      outputs source (call "collapse" [call "wrapped-choice" [.symbol "a",.symbol "b"]]) := by
  rw [pure_branches_keep_distinct_input_answers,inert_wrapped_branches_can_reject_distinct_inputs]
  decide

def plainSharing : Atom := call "collapse" [call "let" [.var "result",
  call "superpose" [.expression [.var "x",.var "y"]],call "==" [.var "x",.var "y"]]]
def wrappedSharing : Atom := call "collapse" [call "let" [.var "result",
  call "superpose" [.expression
    [call "let" [.var "unused3",Effects.boolean true,.var "x"],
     call "let" [.var "unused4",Effects.boolean true,.var "y"]]],
  call "==" [.var "x",.var "y"]]]
def emptySource : SpaceSemantics.Program := {equations := [],declarations := []}

theorem source_wrapper_changes_joint_variable_observation :
    outputs emptySource plainSharing = some [.expression [Effects.boolean false,Effects.boolean false]] ∧
      outputs emptySource wrappedSharing = some [.expression [Effects.boolean true,Effects.boolean true]] := by
  constructor <;> decide +kernel

theorem runtime_constraints_preserve_this_inert_wrapper :
    outputs emptySource plainSharing .runtimeConstraints =
        some [.expression [Effects.boolean false,Effects.boolean false]] ∧
      outputs emptySource wrappedSharing .runtimeConstraints =
        some [.expression [Effects.boolean false,Effects.boolean false]] := by
  constructor <;> decide +kernel

def nativeRejected : Atom := call "collapse"
  [call "let" [Effects.boolean false,call "add-atom" [.symbol "&self",call "event" [.symbol "forbidden"]],
    .symbol "chosen"]]

def nativeObservation : Option (List Atom × Nat) := do
  let program : SpaceSemantics.Program := {equations := [],declarations := [],initializers := [nativeRejected]}
  let compiled ← OutputPlan.compileProgram program
  match compiled.queries with
  | [query] =>
      match Streaming.run program 1500
          (Streaming.enter {state := Effects.loaded program,privateCode := compiled.code} query) with
      | .complete reached =>
          some (Streaming.values reached,reached.world.state.core.count (call "event" [.symbol "forbidden"]))
      | _ => none
  | _ => none

theorem literal_true_native_head_rejects_before_its_write :
    nativeObservation = some ([.expression []],0) := by decide +kernel

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaOutputPlanControls
