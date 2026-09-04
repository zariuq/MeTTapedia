import Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion

/-!
# Transfer canary for ordered decision/rule fusion

This example is independent of the PeTTa call guard.  A constructor switch
selects an ordered pair of rules, while a separate partial compiler assigns
each occurrence a first-order plan.  The fused program retains both the
decision structure and those plans.

The positive controls show exact source/fused execution and authored order.
The negative controls show that a missing plan makes compilation fail closed
and that the semantic theorem cannot be applied to a plan interpreter with an
extra result.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusionCanary

namespace Fusion

export Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion
  (CompiledRule Program Branches compile? evalAll_eq_of_compile?)

end Fusion

namespace OPM

export Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation
  (Pattern Subject ConstructorKey DecisionTree DecisionBranches)

end OPM

namespace WPM

export Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixWildcardColumnCompilation
  (DecisionProgram DecisionBranches)

end WPM

private def sourceTree : OPM.DecisionTree String Nat :=
  .switch
    (.cons
      { head := "Pair", arity := 2 }
      (.tryRule 0 [.wildcard, .wildcard]
        (.tryRule 1 [.wildcard, .wildcard] .failure))
      .nil)
    .failure

private def compileRule? : Nat → Option String
  | 0 => some "take-left"
  | 1 => some "take-right"
  | _ => none

private def fusedProgram : Fusion.Program String Nat String :=
  .switch
    (.cons
      { head := "Pair", arity := 2 }
      (.tryRule ⟨0, "take-left"⟩ [.wildcard, .wildcard]
        (.tryRule ⟨1, "take-right"⟩ [.wildcard, .wildcard] .failure))
      .nil)
    .failure

private def runSource : Nat → List String
  | 0 => ["left"]
  | 1 => ["right"]
  | _ => []

private def runPlan (compiled : Fusion.CompiledRule Nat String) : List String :=
  match compiled.plan with
  | "take-left" => ["left"]
  | "take-right" => ["right"]
  | _ => []

private def subject : List (OPM.Subject String) :=
  [.node "Pair" [.node "Leaf" [], .node "Leaf" []]]

/-- The residual program is produced from the source tree and partial rule
compiler, rather than being used as its own input specification. -/
theorem compilation_exact :
    Fusion.compile? compileRule? sourceTree = some fusedProgram := by
  rfl

private theorem plan_exact (occurrence : Nat) (plan : String)
    (compiled : compileRule? occurrence = some plan) :
    runPlan ⟨occurrence, plan⟩ = runSource occurrence := by
  cases occurrence with
  | zero =>
      simp [compileRule?] at compiled
      subst plan
      rfl
  | succ occurrence =>
      cases occurrence with
      | zero =>
          simp [compileRule?] at compiled
          subst plan
          rfl
      | succ occurrence => simp [compileRule?] at compiled

/-- Generic fusion preserves the independently defined source execution. -/
theorem execution_exact :
    fusedProgram.evalAll runPlan subject = sourceTree.evalAll runSource subject := by
  exact Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.evalAll_eq_of_compile?
    compileRule? runSource runPlan plan_exact sourceTree fusedProgram
      compilation_exact subject

/-- Both successful occurrences remain visible in authored order. -/
theorem ordered_results :
    fusedProgram.evalAll runPlan subject = ["left", "right"] := by
  decide +kernel

private def incompleteCompiler : Nat → Option String
  | 0 => some "take-left"
  | _ => none

/-- A reachable occurrence without a compiled plan rejects the whole
artifact; it cannot silently become a runtime callback. -/
theorem missing_plan_rejected :
    Fusion.compile? incompleteCompiler sourceTree = none := by
  decide +kernel

private def inventingRunPlan
    (compiled : Fusion.CompiledRule Nat String) : List String :=
  runPlan compiled ++ ["invented"]

/-- The semantic premise is load-bearing: an interpreter that adds behavior
does not agree with the source decision semantics. -/
theorem invented_result_detected :
    fusedProgram.evalAll inventingRunPlan subject ≠
      sourceTree.evalAll runSource subject := by
  decide +kernel

private def wildcardTree : WPM.DecisionProgram String Nat :=
  .drop (.switch
    (.cons
      { head := "Pair", arity := 2 }
      (.tryRule 0 [.wildcard, .wildcard]
        (.tryRule 1 [.wildcard, .wildcard] .failure))
      .nil)
    .failure)

private def wildcardFusedProgram : Fusion.Program String Nat String :=
  .drop fusedProgram

private def wildcardSubject : List (OPM.Subject String) :=
  [.node "Ignored" [], .node "Pair" [.node "Leaf" [], .node "Leaf" []]]

/-- Projection nodes survive fusion as explicit residual structure. -/
theorem wildcard_compilation_exact :
    Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.compileWildcard?
      compileRule? wildcardTree = some wildcardFusedProgram := by
  rfl

/-- Fusing after common-wildcard elimination preserves the same independent
source execution. -/
theorem wildcard_execution_exact :
    wildcardFusedProgram.evalAll runPlan wildcardSubject =
      wildcardTree.evalAll runSource wildcardSubject := by
  exact
    Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.evalAll_eq_of_compileWildcard?
      compileRule? runSource runPlan plan_exact wildcardTree
        wildcardFusedProgram wildcard_compilation_exact wildcardSubject

/-- A missing plan still rejects compilation after projection nodes have
been introduced. -/
theorem wildcard_missing_plan_rejected :
    Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.compileWildcard?
      incompleteCompiler wildcardTree = none := by
  decide +kernel

#print axioms execution_exact
#print axioms ordered_results
#print axioms missing_plan_rejected
#print axioms invented_result_detected
#print axioms wildcard_execution_exact
#print axioms wildcard_missing_plan_rejected

end Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusionCanary
