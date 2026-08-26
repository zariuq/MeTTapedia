import Mettapedia.Logic.WorldModel.FeatureContainmentConstruction

/-!
# Compiling feature-containment wrappers

The executable containment construction first lives in a wrapper algorithm.
This file states and proves the exact obligation for returning that result to
a chosen reference algorithm: a compiler must preserve every execution and
bound the increase in program length by one uniform additive overhead.

Compilation transports the wrapper's budgeted feature implication back to the
reference algorithm, adding precisely the compiler overhead.  It still does
not turn additive-slack featurehood into strict featurehood.  A separate
compression-margin premise is both visible and necessary.
-/

namespace Mettapedia.Logic.WorldModel.FeatureContainmentCompilation

open KolmogorovComplexity
open Mettapedia.Logic.WorldModel.Algorithmic
open Mettapedia.Logic.WorldModel.FeatureContainment
open Mettapedia.Logic.WorldModel.FeatureContainmentConstruction

/-- A proof-relevant compiler between conditional algorithms.  The compiled
program preserves every source execution under the same condition, and its
length grows by at most `overhead`. -/
structure ConditionalAlgorithmCompiler
    (source target : ConditionalAlgorithm) where
  compile : BinString → BinString
  overhead : Nat
  preserves : ∀ {program condition output : BinString},
    output ∈ source program condition →
      output ∈ target (compile program) condition
  length_le : ∀ program, (compile program).length ≤ program.length + overhead

namespace ConditionalAlgorithmCompiler

/-- Identity compilation is the zero-overhead positive control. -/
def refl (U : ConditionalAlgorithm) : ConditionalAlgorithmCompiler U U where
  compile := id
  overhead := 0
  preserves := by
    intro program condition output h
    exact h
  length_le := by simp

/-- Compose two compiler passes; execution preservation and length overheads
compose additively. -/
def trans
    {first second third : ConditionalAlgorithm}
    (firstCompiler : ConditionalAlgorithmCompiler first second)
    (secondCompiler : ConditionalAlgorithmCompiler second third) :
    ConditionalAlgorithmCompiler first third where
  compile := secondCompiler.compile ∘ firstCompiler.compile
  overhead := firstCompiler.overhead + secondCompiler.overhead
  preserves := fun h => secondCompiler.preserves (firstCompiler.preserves h)
  length_le := by
    intro program
    have hFirst := firstCompiler.length_le program
    have hSecond := secondCompiler.length_le (firstCompiler.compile program)
    dsimp
    omega

@[simp] theorem refl_compile (U : ConditionalAlgorithm) (program : BinString) :
    (refl U).compile program = program := rfl

@[simp] theorem refl_overhead (U : ConditionalAlgorithm) :
    (refl U).overhead = 0 := rfl

end ConditionalAlgorithmCompiler

/-- Compile both executable programs carried by a residual certificate.  The
residual data itself is unchanged. -/
def compileResidualCertificate
    {source target : ConditionalAlgorithm}
    (compiler : ConditionalAlgorithmCompiler source target)
    (certificate : ResidualCertificate) : ResidualCertificate where
  descriptiveProgram := compiler.compile certificate.descriptiveProgram
  residual := certificate.residual

/-- A slack realization survives compilation.  Only the compiled feature
program contributes to the compression inequality, so exactly one compiler
overhead is added to the slack. -/
theorem compile_slackRealization
    {sourceAlgorithm targetAlgorithm : ConditionalAlgorithm}
    (compiler : ConditionalAlgorithmCompiler sourceAlgorithm targetAlgorithm)
    {slack : Nat} {feature source : BinString}
    {certificate : ResidualCertificate}
    (realizes :
      (slackFeatureSemantics sourceAlgorithm slack).realizes
        feature certificate source) :
    (slackFeatureSemantics targetAlgorithm
      (slack + compiler.overhead)).realizes
        (compiler.compile feature)
        (compileResidualCertificate compiler certificate) source := by
  rcases realizes with ⟨extracts, reconstructs, compresses⟩
  refine ⟨compiler.preserves extracts, compiler.preserves reconstructs, ?_⟩
  have hLength := compiler.length_le feature
  simp only [compileResidualCertificate]
  omega

theorem compile_slackFeatureOf
    {sourceAlgorithm targetAlgorithm : ConditionalAlgorithm}
    (compiler : ConditionalAlgorithmCompiler sourceAlgorithm targetAlgorithm)
    {slack : Nat} {feature source : BinString}
    (featureOf : SlackFeatureOf sourceAlgorithm slack feature source) :
    SlackFeatureOf targetAlgorithm (slack + compiler.overhead)
      (compiler.compile feature) source := by
  obtain ⟨certificate, realizes⟩ := featureOf
  exact ⟨compileResidualCertificate compiler certificate,
    compile_slackRealization compiler realizes⟩

/-- Compile the consequent side of a cross-algorithm implication.  The
premise remains in the reference algorithm; the consequent returns there with
the compiler overhead added pointwise to its budget. -/
theorem compile_crossAlgorithmFeatureImplicationWithBudget
    {premiseAlgorithm consequentAlgorithm : ConditionalAlgorithm}
    (compiler : ConditionalAlgorithmCompiler consequentAlgorithm premiseAlgorithm)
    {budget : BinString → Nat} {premise consequent : BinString}
    (implication : CrossAlgorithmFeatureImplicationWithBudget
      premiseAlgorithm consequentAlgorithm budget premise consequent) :
    FeatureImplicationWithBudget premiseAlgorithm
      (fun source => budget source + compiler.overhead)
      premise (compiler.compile consequent) := by
  intro certificate source realizesPremise
  exact compile_slackFeatureOf compiler
    (implication certificate source realizesPremise)

/-! ## Exact strictness boundary -/

/-- For a fixed certificate, strict realization is exactly slack realization
plus the original strict length inequality.  The additive execution theorem
supplies the first conjunct; a margin argument must supply the second. -/
theorem strictRealization_iff_slackRealization_and_strictLength
    {U : ConditionalAlgorithm} {slack : Nat}
    {feature source : BinString} {certificate : ResidualCertificate} :
    (strictFeatureSemantics U).realizes feature certificate source ↔
      (slackFeatureSemantics U slack).realizes feature certificate source ∧
        feature.length + certificate.residual.length < source.length := by
  constructor
  · intro realizes
    rcases realizes with ⟨extracts, reconstructs, compresses⟩
    exact ⟨⟨extracts, reconstructs, by omega⟩, compresses⟩
  · rintro ⟨realizes, strictLength⟩
    exact ⟨realizes.1, realizes.2.1, strictLength⟩

/-- The declared additive budget is dominated by a witnessed compression gap
for every executable certificate of `feature` at `source`. -/
def BudgetDominatedByCompressionGap
    (U : ConditionalAlgorithm) (budget : BinString → Nat)
    (feature source : BinString) : Prop :=
  ∀ certificate : ResidualCertificate,
    certificate.residual ∈ U certificate.descriptiveProgram source →
    source ∈ U feature certificate.residual →
    feature.length + certificate.residual.length + budget source < source.length

/-- A budgeted family implication becomes strict when a separately proved
compression gap dominates its budget on every premise instance. -/
theorem featureImplicationWithBudget_to_strict_of_margin
    {U : ConditionalAlgorithm} {budget : BinString → Nat}
    {premise consequent : BinString}
    (implication : FeatureImplicationWithBudget U budget premise consequent)
    (margin : ∀ certificate source,
      (strictFeatureSemantics U).realizes premise certificate source →
        BudgetDominatedByCompressionGap U budget consequent source) :
    StrictFeatureImplication U premise consequent := by
  intro premiseCertificate source realizesPremise
  obtain ⟨consequentCertificate, realizesConsequent⟩ :=
    implication premiseCertificate source realizesPremise
  refine ⟨consequentCertificate, realizesConsequent.1,
    realizesConsequent.2.1, ?_⟩
  have hMargin := margin premiseCertificate source realizesPremise
    consequentCertificate realizesConsequent.1 realizesConsequent.2.1
  omega

/-! ## The corrected containment construction after compilation -/

/-- Compile the corrected wrapper construction back into the reference
algorithm.  This closes the operational embedding obligation while retaining
the exact coding and compiler overheads. -/
theorem compiled_containmentWrapper_implication_of_coreDescriptionBound
    {U : ConditionalAlgorithm}
    (compiler : ConditionalAlgorithmCompiler (containmentWrapperAlgorithm U) U)
    {complexityIndex coreSlack : Nat}
    {baseFeature reconstructionProgram premiseFeature : BinString}
    (reconstructsPremise :
      premiseFeature ∈ U reconstructionProgram
        (pairCondition baseFeature (binaryBits complexityIndex)))
    (coreBound :
      baseFeature.length + reconstructionProgram.length ≤
        premiseFeature.length + coreSlack) :
    FeatureImplicationWithBudget U
      (fun _ =>
        coreSlack + containmentInnerOverhead complexityIndex +
          containmentOuterOverhead complexityIndex reconstructionProgram +
          compiler.overhead)
      premiseFeature
      (compiler.compile (containmentGenerator baseFeature)) := by
  have hWrapper := containmentWrapper_implication_of_coreDescriptionBound
    reconstructsPremise coreBound
  have hCompiled :=
    compile_crossAlgorithmFeatureImplicationWithBudget compiler hWrapper
  simpa [Nat.add_assoc] using hCompiled

/-- Strict compiled containment requires, and here explicitly consumes, a
compression margin dominating every coding and compiler overhead. -/
theorem compiled_containmentWrapper_strictImplication_of_margin
    {U : ConditionalAlgorithm}
    (compiler : ConditionalAlgorithmCompiler (containmentWrapperAlgorithm U) U)
    {complexityIndex coreSlack : Nat}
    {baseFeature reconstructionProgram premiseFeature : BinString}
    (reconstructsPremise :
      premiseFeature ∈ U reconstructionProgram
        (pairCondition baseFeature (binaryBits complexityIndex)))
    (coreBound :
      baseFeature.length + reconstructionProgram.length ≤
        premiseFeature.length + coreSlack)
    (margin : ∀ certificate source,
      (strictFeatureSemantics U).realizes premiseFeature certificate source →
        BudgetDominatedByCompressionGap U
          (fun _ =>
            coreSlack + containmentInnerOverhead complexityIndex +
              containmentOuterOverhead complexityIndex reconstructionProgram +
              compiler.overhead)
          (compiler.compile (containmentGenerator baseFeature)) source) :
    StrictFeatureImplication U premiseFeature
      (compiler.compile (containmentGenerator baseFeature)) := by
  exact featureImplicationWithBudget_to_strict_of_margin
    (compiled_containmentWrapper_implication_of_coreDescriptionBound
      compiler reconstructsPremise coreBound) margin

/-! The negative control is
`FeatureContainment.no_uniform_oneBitBudget_to_strictFeatureImplication`:
without the separate margin premise, even a witnessed nonvacuous one-bit
budget cannot be promoted uniformly to strict implication. -/

#print axioms ConditionalAlgorithmCompiler.trans
#print axioms compile_crossAlgorithmFeatureImplicationWithBudget
#print axioms strictRealization_iff_slackRealization_and_strictLength
#print axioms featureImplicationWithBudget_to_strict_of_margin
#print axioms compiled_containmentWrapper_implication_of_coreDescriptionBound
#print axioms compiled_containmentWrapper_strictImplication_of_margin
#print axioms no_uniform_oneBitBudget_to_strictFeatureImplication

end Mettapedia.Logic.WorldModel.FeatureContainmentCompilation
