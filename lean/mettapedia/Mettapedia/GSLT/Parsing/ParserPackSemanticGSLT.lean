import Mettapedia.GSLT.Core.ProofRelevantJudgment
import Mettapedia.GSLT.LanguageDef.TwoNTTCoherence
import Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence

/-!
# ParserPack compilation as an exact GSLT translation

The scannerless source plan and its compiled ParserPack plan already have
independently defined, proof-relevant derivation judgments.  This module makes
their semantic status explicit: each judgment generates a proof-relevant GSLT,
and exact plan agreement induces an exact translation between those GSLTs.

The `CompiledParserPackPlan` remains implementation data used to define the
target step relation.  It is not a semantic pipeline node in its own right.
The public endpoints are the source and target GSLTs, their proof-relevant
step fibres, and the generated OSLF native-type readouts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ParserPackSemanticGSLT

open Mettapedia.GSLT
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.GSLT.ProofRelevantJudgment
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.TwoNTTCoherence
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open Mettapedia.GSLT.Parsing.PresentationExprSemantics

/-! ## The two semantic endpoints -/

/-- The independently authored scannerless root judgment. -/
def sourceJudgment
    (literalScalars? : String -> Option (List Nat))
    (profile : ParserProfileLayer) (rules : List CompiledRule) :
    Judgment (List Nat) CST where
  Evidence := SourcePlanRootDerives literalScalars? profile rules

/-- The root judgment executed by one concrete ParserPack plan. -/
def parserPackJudgment (profile : ParserProfileLayer)
    (plan : CompiledParserPackPlan) : Judgment (List Nat) CST where
  Evidence := ParserPackRootDerives profile plan

/-- Source parsing as a proof-relevant GSLT. -/
def sourceSystem
    (literalScalars? : String -> Option (List Nat))
    (profile : ParserProfileLayer) (rules : List CompiledRule) :
    ProofRelevantGSLT :=
  (sourceJudgment literalScalars? profile rules).system

/-- ParserPack execution as a proof-relevant GSLT. -/
def parserPackSystem (profile : ParserProfileLayer)
    (plan : CompiledParserPackPlan) : ProofRelevantGSLT :=
  (parserPackJudgment profile plan).system

/-- The source operational GSLT obtained by erasing only receipt identity. -/
abbrev sourceGSLT
    (literalScalars? : String -> Option (List Nat))
    (profile : ParserProfileLayer) (rules : List CompiledRule) : GSLT :=
  (sourceJudgment literalScalars? profile rules).theory

/-- The target operational GSLT obtained by erasing only receipt identity. -/
abbrev parserPackGSLT (profile : ParserProfileLayer)
    (plan : CompiledParserPackPlan) : GSLT :=
  (parserPackJudgment profile plan).theory

/-! ## Compilation preserves and reflects the whole proof fibre -/

/-- Exact ParserPack agreement is an exact equivalence of the source and
target root-derivation judgments, not merely equality of accepted trees. -/
def compilerExactEquivalence
    {literalScalars? : String -> Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan) :
    ExactEquivalence
      (sourceJudgment literalScalars? profile rules)
      (parserPackJudgment profile plan) where
  evidenceEquiv input tree :=
    sourcePlanRootDerivationEquiv (input := input) agreement tree

/-- The compiler's semantic arrow retains every derivation occurrence and
reflects every target occurrence. -/
def compilerExactTranslation
    {literalScalars? : String -> Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan) :
    ProofRelevant.ExactTranslation
      (sourceSystem literalScalars? profile rules)
      (parserPackSystem profile plan) :=
  (compilerExactEquivalence agreement).exactTranslation

/-- The ordinary GSLT/OSLF view is the equation-class semantic cover obtained
by erasing proof occurrences from the exact translation. -/
def compilerSemanticCover
    {literalScalars? : String -> Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan) :
    SemanticCoveredTranslation
      (sourceGSLT literalScalars? profile rules)
      (parserPackGSLT profile plan) :=
  (compilerExactEquivalence agreement).semanticCover

/-- Successful execution of the actual plan compiler supplies the exact
proof-relevant GSLT translation. -/
def compilerExactTranslationOfCompilation
    {literalScalars? : String -> Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan}
    (compiled :
      compileParserPackPlan? literalScalars? profile rules = some plan) :
    ProofRelevant.ExactTranslation
      (sourceSystem literalScalars? profile rules)
      (parserPackSystem profile plan) :=
  compilerExactTranslation
    (ParserPackPlanAgreement.of_compilation compiled)

/-! ## The public semantic compilation object -/

/-- A ParserPack compilation exposes only its target proof-relevant GSLT and
the exact compiler arrow from the source GSLT.  The host plan used to build
that target is existentially hidden by this package; the associated native
type theories are derived from the two endpoints rather than stored as an
independent intermediate representation. -/
structure SemanticCompilation
    (literalScalars? : String -> Option (List Nat))
    (profile : ParserProfileLayer) (rules : List CompiledRule) where
  target : ProofRelevantGSLT
  compiler : ProofRelevant.ExactTranslation
    (sourceSystem literalScalars? profile rules) target

namespace SemanticCompilation

/-- The source endpoint of a semantic parser compilation. -/
abbrev source
    {literalScalars? : String -> Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    (_compilation : SemanticCompilation literalScalars? profile rules) :
    ProofRelevantGSLT :=
  sourceSystem literalScalars? profile rules

/-- Erasing occurrences from the source endpoint retains its GSLT. -/
abbrev sourceTheory
    {literalScalars? : String -> Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    (_compilation : SemanticCompilation literalScalars? profile rules) : GSLT :=
  (sourceSystem literalScalars? profile rules).theory

/-- Erasing occurrences from the compiled endpoint retains its GSLT. -/
abbrev targetTheory
    {literalScalars? : String -> Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    (compilation : SemanticCompilation literalScalars? profile rules) : GSLT :=
  compilation.target.theory

/-- The public GSLT arrow of a semantic parser compilation. -/
def semanticCompiler
    {literalScalars? : String -> Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    (compilation : SemanticCompilation literalScalars? profile rules) :
    SemanticCoveredTranslation compilation.sourceTheory
      compilation.targetTheory :=
  SemanticCoveredTranslation.ofCoveredTranslation
    compilation.compiler.toTranslation.toCovered

/-- The source native type theory is generated from the source GSLT. -/
def sourceNTT
    {literalScalars? : String -> Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    (compilation : SemanticCompilation literalScalars? profile rules) :
    GeneratedNTT :=
  generateNTT compilation.sourceTheory

/-- The target native type theory is generated from the target GSLT. -/
def targetNTT
    {literalScalars? : String -> Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    (compilation : SemanticCompilation literalScalars? profile rules) :
    GeneratedNTT :=
  generateNTT compilation.targetTheory

end SemanticCompilation

/-- Successful host compilation is immediately sealed as a semantic
GSLT-to-GSLT compilation.  No plan or table type appears in the result. -/
def compileSemantic?
    (literalScalars? : String -> Option (List Nat))
    (profile : ParserProfileLayer) (rules : List CompiledRule) :
    Option (SemanticCompilation literalScalars? profile rules) :=
  match compiled : compileParserPackPlan? literalScalars? profile rules with
  | none => none
  | some plan =>
      some {
        target := parserPackSystem profile plan
        compiler := compilerExactTranslationOfCompilation compiled }

/-- The source and ParserPack steps agree on every query/answer pair. -/
theorem compiler_step_iff
    {literalScalars? : String -> Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan)
    (source target :
      ProofRelevantJudgment.Term
        (sourceJudgment literalScalars? profile rules)) :
    (sourceGSLT literalScalars? profile rules).Step source target <->
      (parserPackGSLT profile plan).Step
        (source.rebase (parserPackJudgment profile plan))
        (target.rebase (parserPackJudgment profile plan)) :=
  (compilerExactEquivalence agreement).step_iff source target

/-- A compiled plan with exact agreement cannot invent a root parse. -/
theorem no_spurious_parserPack_root
    {literalScalars? : String -> Option (List Nat)}
    {profile : ParserProfileLayer} {rules : List CompiledRule}
    {plan : CompiledParserPackPlan} {input : List Nat} {tree : CST}
    (agreement :
      ParserPackPlanAgreement literalScalars? profile rules plan) :
    Not (Nonempty (ParserPackRootDerives profile plan input tree) /\
      Not (Nonempty
        (SourcePlanRootDerives literalScalars? profile rules input tree))) := by
  rintro ⟨⟨targetEvidence⟩, sourceMissing⟩
  apply sourceMissing
  exact ⟨(sourcePlanRootDerivationEquiv agreement tree).symm targetEvidence⟩

/-! ## Generated native-type readouts -/

/-- OSLF generates the source plan's native-type readout from its GSLT. -/
def sourceGeneratedNTT
    (literalScalars? : String -> Option (List Nat))
    (profile : ParserProfileLayer) (rules : List CompiledRule) :
    GeneratedNTT :=
  generateNTT (sourceGSLT literalScalars? profile rules)

/-- OSLF generates the ParserPack machine's native-type readout from its
target GSLT, rather than from the host plan record. -/
def parserPackGeneratedNTT (profile : ParserProfileLayer)
    (plan : CompiledParserPackPlan) : GeneratedNTT :=
  generateNTT (parserPackGSLT profile plan)

/-! ## Positive and negative controls -/

namespace Canary

def profile : ParserProfileLayer := {
  name := "ParserPackSemanticCanary"
  startSort := "Scalar"
  classes := [
    { name := "letter-a"
      kind := .points [65] }
  ]
  states := [
    { resultSort := "Scalar"
      className := "letter-a"
      ruleLabel := "lex-a" }
  ]
}

def literalScalars? : String -> Option (List Nat) := fun _ => none

def plan : CompiledParserPackPlan := {
  lexical := compileLexicalPack profile
  structural := []
}

def agreement :
    ParserPackPlanAgreement literalScalars? profile [] plan := by
  refine ⟨rfl, ?_⟩
  rfl

/-- The canary's host plan is sealed behind the public semantic compiler
package. -/
def semanticCompilation : SemanticCompilation literalScalars? profile [] where
  target := parserPackSystem profile plan
  compiler := compilerExactTranslation agreement

/-- Positive control: running the host compiler produces a sealed semantic
compilation package. -/
theorem semantic_compilation_succeeds :
    (compileSemantic? literalScalars? profile []).isSome = true := by
  rfl

def tree : CST :=
  .node "lex-a" 0 1 [.terminal [65] 0 1]

def sourceEvidence :
    SourcePlanRootDerives literalScalars? profile [] [65] tree := by
  refine SourcePlanDerivesAt.lexical 0 (by simp [profile]) rfl rfl ?_
  exact ⟨RecognizesAtUsing.classMember rfl (by
    simp [ParserProfileLayer.ClassEvidence,
      ParserProfileLayer.classAccepts?, ParserProfileLayer.class?, profile,
      LexicalClassKind.accepts, isUnicodeScalar]), rfl⟩

def targetEvidence :
    ParserPackRootDerives profile plan [65] tree :=
  (sourcePlanRootDerivationEquiv agreement tree) sourceEvidence

/-- Positive control: a real lexical source receipt maps to an executable
ParserPack GSLT step. -/
theorem compiled_step :
    (parserPackGSLT profile plan).Step
      (.query [65]) (.answer [65] tree) :=
  ⟨.accepted targetEvidence⟩

/-- Positive control: the packaged compiler arrow maps the source step to the
same target step without exposing the host plan as a pipeline node. -/
theorem semantic_compiler_maps_step :
    semanticCompilation.targetTheory.Step
      (semanticCompilation.semanticCompiler.mapTerm (.query [65]))
      (semanticCompilation.semanticCompiler.mapTerm (.answer [65] tree)) :=
  semanticCompilation.semanticCompiler.mapStep
    ⟨.accepted sourceEvidence⟩

/-- Mutating the target start sort prevents construction of the semantic
compiler arrow; exact agreement fails before any backend is trusted. -/
def mutatedPlan : CompiledParserPackPlan := {
  lexical := {
    profileName := plan.lexical.profileName
    startSort := "Invented"
    classes := plan.lexical.classes
    productions := plan.lexical.productions }
  structural := plan.structural
}

theorem mutated_plan_has_no_agreement :
    Not (ParserPackPlanAgreement literalScalars? profile [] mutatedPlan) := by
  intro falseAgreement
  have startSortEquality := congrArg CompiledLexicalPack.startSort
    falseAgreement.lexical_exact
  simp [mutatedPlan, plan, profile, compileLexicalPack] at startSortEquality

end Canary

#print axioms compiler_step_iff
#print axioms no_spurious_parserPack_root
#print axioms Canary.semantic_compilation_succeeds
#print axioms Canary.compiled_step
#print axioms Canary.semantic_compiler_maps_step
#print axioms Canary.mutated_plan_has_no_agreement

end Mettapedia.GSLT.Parsing.ParserPackSemanticGSLT
