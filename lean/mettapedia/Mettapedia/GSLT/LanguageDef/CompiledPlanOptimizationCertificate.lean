import Mettapedia.GSLT.LanguageDef.CompiledPlanOptimizationPipeline

/-!
# Composed certificates for compiled-plan optimizations

The compiled-plan loader performs one transient structural admission pass and
then retains only the products needed by execution.  This module models that
boundary directly.  Dense finite support and immutable-subterm caching are
derived from the same locally admitted rule, their observations are proved
together, and support evidence is then erased before runtime without changing
the executable head or body observation.

The construction is vocabulary independent.  A rule contributes only its
typed plan, finite slot inventory, and the result of the local recognizer.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanOptimizationCertificate

open Mettapedia.GSLT
open CompiledPlanAdmission
open CompiledPlanLowering
open CompiledPlanTermSemantics
open CompiledPlanFiniteSupportCompilation
open CompiledPlanOptimizationPipeline
open FiniteSupportBitVecCompilation

/-- Source accepted by the same local recognizer that guards physical plan
lowering. -/
structure AdmittedRule where
  source : TypedRule
  accepted : source.locallySupported = true

/-- The admission-stage product.  Packed support is checked transiently;
`analysis` is the persistent execution product. -/
structure CheckedRuleArtifact where
  width : Nat
  packedSupport : PackedSupport (slotInventory width)
  analysis : RuleAnalysis

/-- Complete observation before certificate erasure. -/
@[ext] structure CheckedRuleObservation where
  support : Nat -> Bool
  head : Substitution -> Option GroundTerm
  body : Substitution -> List (Option GroundTerm)

/-- Execution observes instantiated rule terms but not already-checked support
evidence. -/
@[ext] structure RuntimeRuleObservation where
  head : Substitution -> Option GroundTerm
  body : Substitution -> List (Option GroundTerm)

def compileCheckedRule (admitted : AdmittedRule) : CheckedRuleArtifact :=
  let rule := admitted.source
  let width := rule.variableCount.toNat
  { width
    packedSupport := encode (slotInventory width) (ruleUsedVariables rule)
    analysis := analyzeRule rule }

def observeAdmittedRule (admitted : AdmittedRule) :
    CheckedRuleObservation :=
  { support := fun slot => (ruleUsedVariables admitted.source).contains slot
    head := fun substitution =>
      instantiateTerm substitution admitted.source.head
    body := fun substitution =>
      admitted.source.body.map (instantiateTerm substitution) }

def observeCheckedRule (artifact : CheckedRuleArtifact) :
    CheckedRuleObservation :=
  { support := decodeMember (slotInventory artifact.width)
      artifact.packedSupport
    head := fun substitution =>
      CompiledPlanGroundCacheCompilation.executeTerm substitution
        artifact.analysis.cachedHead
    body := fun substitution =>
      artifact.analysis.cachedBody.map
        (CompiledPlanGroundCacheCompilation.executeTerm substitution) }

def observeRuntimeRule (analysis : RuleAnalysis) : RuntimeRuleObservation :=
  { head := fun substitution =>
      CompiledPlanGroundCacheCompilation.executeTerm substitution
        analysis.cachedHead
    body := fun substitution =>
      analysis.cachedBody.map
        (CompiledPlanGroundCacheCompilation.executeTerm substitution) }

def eraseSupport (observation : CheckedRuleObservation) :
    RuntimeRuleObservation :=
  { head := observation.head, body := observation.body }

/-- Local rule admission entails the in-range half consumed by the packed
support compiler. -/
theorem supportAccepted (admitted : AdmittedRule) :
    supported? (slotInventory admitted.source.variableCount.toNat)
      (ruleUsedVariables admitted.source) = true := by
  have packed := packedDenseVariables_of_rule_locallySupported
    admitted.source admitted.accepted
  have combined :
      supported? (slotInventory admitted.source.variableCount.toNat)
          (ruleUsedVariables admitted.source) &&
        packedFull? (slotInventory admitted.source.variableCount.toNat)
          (encode (slotInventory admitted.source.variableCount.toNat)
            (ruleUsedVariables admitted.source)) = true := by
    simpa [packedDenseVariables] using packed
  rw [Bool.and_eq_true] at combined
  exact combined.1

/-- Packed support and cached term execution compose into one exact rule
observation. -/
def checkedRuleRealization :
    SimpleRealization AdmittedRule CheckedRuleArtifact
      CheckedRuleObservation where
  compile := fun _ admitted => compileCheckedRule admitted
  observeSource := fun _ admitted => observeAdmittedRule admitted
  observeArtifact := fun _ artifact => observeCheckedRule artifact
  adequate := by
    intro _ admitted
    apply CheckedRuleObservation.ext
    · funext slot
      exact decodeMember_encode
        (slotInventory admitted.source.variableCount.toNat)
        (ruleUsedVariables admitted.source) (supportAccepted admitted) slot
    · funext substitution
      exact CompiledPlanGroundCacheCompilation.executeTerm_compileTerm
        admitted.source.head substitution
    · funext substitution
      simpa [compileCheckedRule, observeCheckedRule, observeAdmittedRule]
        using analyzeRule_cachedBody_exact admitted.source substitution

/-- Forgetting support changes only the named observation, not compilation. -/
def checkedExecutionRealization :
    SimpleRealization AdmittedRule CheckedRuleArtifact
      RuntimeRuleObservation :=
  checkedRuleRealization.mapObservation (fun _ => eraseSupport)

/-- The physical runtime retains the analysis and discards the transient
packed-support witness after admission. -/
def runtimeRuleRealization :
    SimpleRealization AdmittedRule RuleAnalysis RuntimeRuleObservation :=
  checkedExecutionRealization.stage
    (fun _ artifact => artifact.analysis)
    (fun _ analysis => observeRuntimeRule analysis)
    (by intro _ artifact; rfl)

@[simp] theorem runtimeRuleRealization_compile
    (admitted : AdmittedRule) :
    runtimeRuleRealization.compile () admitted = analyzeRule admitted.source :=
  rfl

/-- Evidence erasure preserves the complete executable rule observation. -/
theorem runtimeRuleExecution_exact (admitted : AdmittedRule) :
    observeRuntimeRule (runtimeRuleRealization.compile () admitted) =
      eraseSupport (observeAdmittedRule admitted) :=
  runtimeRuleRealization.observe_compile () admitted

/-! ## Program-level attachment -/

/-- A successful emitted pipeline artifact together with the exact equation
that admits it.  The producer is not trusted merely for constructing this
value: consumers replay `compile?` or validate the corresponding physical
packet. -/
structure AdmittedProgram where
  source : TypedProgram
  artifact : Artifact
  accepted : CompiledPlanOptimizationPipeline.compile? source = some artifact

def admitProgram? (source : TypedProgram) : Option AdmittedProgram :=
  match accepted : CompiledPlanOptimizationPipeline.compile? source with
  | none => none
  | some artifact => some { source, artifact, accepted }

theorem admitProgram?_isSome (source : TypedProgram) :
    (admitProgram? source).isSome =
      (CompiledPlanOptimizationPipeline.compile? source).isSome := by
  unfold admitProgram?
  split <;> simp_all

/-- Every source rule named by an admitted emitted artifact supplies the local
certificate needed by the composed rule realization. -/
def AdmittedProgram.admittedRule (program : AdmittedProgram)
    (rule : TypedRule) (member : rule ∈ program.source) : AdmittedRule :=
  { source := rule
    accepted := by
      have programSupported :=
        (CompiledPlanOptimizationPipeline.compile?_success
          program.source program.artifact program.accepted).1
      have rulesSupported :
          program.source.all TypedRule.locallySupported = true := by
        simp [TypedProgram.locallySupported] at programSupported
        aesop
      exact (List.all_eq_true.mp rulesSupported) rule member }

/-- Rule-local support checking, ground caching, and evidence erasure therefore
compose for every occurrence in an admitted emitted program. -/
theorem admittedProgram_ruleExecution_exact
    (program : AdmittedProgram) (rule : TypedRule)
    (member : rule ∈ program.source) :
    observeRuntimeRule
        (runtimeRuleRealization.compile ()
          (program.admittedRule rule member)) =
      eraseSupport
        (observeAdmittedRule (program.admittedRule rule member)) :=
  runtimeRuleExecution_exact (program.admittedRule rule member)

/-! ## Independent witnesses and rejection boundary -/

private def parserRule : TypedRule :=
  { name := [1]
    head := .application [2]
      (.cons (.variable 0) (.cons (.string [3]) .nil))
    body := [.application [4] (.cons (.variable 0) .nil)]
    variableCount := 1 }

private def proofRule : TypedRule :=
  { name := [5]
    head := .application [6]
      (.cons (.variable 1) (.cons (.variable 0) .nil))
    body := [.application [7] (.cons (.variable 1) .nil)]
    variableCount := 2 }

private def invalidRule : TypedRule :=
  { name := [8]
    head := .application [9] (.cons (.variable 1) .nil)
    body := []
    variableCount := 1 }

/-- Parser-like and proof-like rules independently enter the same composed
admission and execution path. -/
example : (admitProgram? [parserRule, proofRule]).isSome = true := by
  have supported :
      TypedProgram.locallySupported [parserRule, proofRule] = true := by
    decide
  obtain ⟨artifact, compiled⟩ :=
    CompiledPlanOptimizationPipeline.compile?_complete
      [parserRule, proofRule] supported
  rw [admitProgram?_isSome, compiled]
  rfl

/-- A slot outside the declared local inventory is rejected before any
optimization product is retained. -/
example : (admitProgram? [invalidRule]).isSome = false := by
  have unsupported :
      TypedProgram.locallySupported [invalidRule] = false := by
    decide
  have rejected :
      CompiledPlanOptimizationPipeline.compile? [invalidRule] = none := by
    simp [CompiledPlanOptimizationPipeline.compile?, unsupported]
  rw [admitProgram?_isSome, rejected]
  rfl

end Mettapedia.GSLT.LanguageDef.CompiledPlanOptimizationCertificate
