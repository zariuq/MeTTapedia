import Mettapedia.Languages.MeTTa.Prime.NativeProgramGradualGuarantee
import Mettapedia.Languages.MeTTa.Prime.NativeInteractionInterpretation
import Mettapedia.GSLT.LanguageDef.TotalGSLT

/-!
# Source adequacy for planned Prime interaction occurrences

Program preparation preserves the complete authored command stream, but an
interaction computation consumes particular pattern occurrences.  This file
connects those two levels without postulating a whole-program interpreter:

* the patterns selected from a `ProgramPlan` erase to patterns occurring in
  the unchanged source program;
* an exact rho event path between two selected occurrences is an ordinary
  Prime semantic term at those endpoints; and
* erasing that term yields the authorized GSLT rewrite path carried by the
  same events.

The construction is intentionally occurrence-indexed.  Equal-looking source
patterns in different declarations remain different `ProgramOccurrence`
values because their retained `PlannedPattern` locations differ.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeProgramSourceAdequacy

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.Languages.MeTTa.StagedReflective
open Mettapedia.Languages.MeTTa.Prime.NativeInteraction
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionInterpretation
open Mettapedia.Languages.MeTTa.Prime.NativeProgramElaboration
open Mettapedia.Languages.MeTTa.Prime.PrimeMotivationProgramPackages
open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

abbrev SourcePattern :=
  Mettapedia.Languages.MeTTa.Prime.NativeTypedQuotation.RuntimePattern

/-! ## Supported authored programs as ordinary GSLTs -/

/-- A proof that one planned program belongs to the supported equation-only
source subset and compiles to this exact five-field language.  The equality
is parser-derived evidence; callers cannot supply an unrelated language. -/
structure CompiledProgram (package : ProgramPlan) where
  language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef
  compiled : sourceLanguage? package.source = some language

namespace CompiledProgram

/-- Program planning cannot change the source compilation result. -/
theorem compiled_after_plan_erasure {package : ProgramPlan}
    (compiled : CompiledProgram package) :
    sourceLanguage? (eraseRows package.planned) = some compiled.language := by
  rw [package.erases]
  exact compiled.compiled

/-- The existing `LanguageDef` semantics of the exact parser-derived rewrite
core. -/
def theory {package : ProgramPlan} (compiled : CompiledProgram package) : GSLT :=
  languageGSLT compiled.language
    (ReductionRespectsEquations.of_equation_free
      (sourceLanguage?_equations_empty compiled.compiled))

/-- Source semantics for the supported program is the established
premise-aware, contextual `LanguageDef` reduction relation. -/
def SourceStep {package : ProgramPlan} (compiled : CompiledProgram package)
    (source target : SourcePattern) : Prop :=
  langReducesUsing RelationEnv.empty compiled.language source target

/-- Ordinary GSLT execution is exactly the source reduction generated from
the quoted declarations. -/
theorem theory_step_iff_source {package : ProgramPlan}
    (compiled : CompiledProgram package) (source target : SourcePattern) :
    compiled.theory.Step source target ↔ compiled.SourceStep source target :=
  languageGSLT_step _ _ _ _

/-- The complete DFA package is accepted by the equation-only source
compiler. -/
def dfaPeTTa : CompiledProgram (prepareProgram rawPolicy dfa.petta) where
  language := dfa.pettaLanguage
  compiled := dfa.pettaCompiles

/-- The HE version compiles to the same `LanguageDef`, not merely the same
equation multiset. -/
def dfaHE : CompiledProgram (prepareProgram rawPolicy dfa.he) where
  language := dfa.pettaLanguage
  compiled := dfa.heCompilesToSameLanguage

theorem dfa_source_compilations_equal :
    sourceLanguage? dfa.petta = sourceLanguage? dfa.he := by
  rw [dfa.pettaCompiles, dfa.heCompilesToSameLanguage]

private def dfaQ0ZeroRule : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule where
  name := "SOURCE_RULE_0"
  typeContext := []
  premises := []
  left := metta% petta "(dfa-step q0 zero)"
  right := metta% petta "q1"

/-- A concrete transition from the quoted complete DFA is an actual source
reduction in the generated `LanguageDef`, not only an interface-level
equivalence.  The witness names the first parser-derived rule and passes
through the generic matching, premise, substitution, and contextual-step
machinery. -/
theorem dfa_q0_zero_source_step : dfaPeTTa.SourceStep
    (metta% petta "(dfa-step q0 zero)") (metta% petta "q1") := by
  apply Mettapedia.OSLF.MeTTaIL.ContextualStep.step_of_rule
      (rule := dfaQ0ZeroRule) (initialBindings := []) (finalBindings := [])
  · simp [dfaQ0ZeroRule, dfaPeTTa, dfa, sourceLanguage?,
      sourceLanguageFrom, rewriteDeclarations?, rewriteRulesFrom,
      semanticDeclarations]
    decide
  · simp [dfaQ0ZeroRule,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule,
      Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
      Mettapedia.OSLF.MeTTaIL.Match.matchArgs,
      Mettapedia.OSLF.MeTTaIL.Match.mergeBindings]
  · exact .nil
  · simp [dfaQ0ZeroRule, applyPremisesWithEnv]
  · simp [dfaQ0ZeroRule,
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule,
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings]

end CompiledProgram

/-! ## Occurrences in unchanged source programs -/

/-- Source-level pattern projection, matching `commandPatterns` after
planning evidence is erased. -/
def sourceCommandPatterns : SourceCommand → List SourcePattern
  | .empty | .setFuel _ | .newSpace _ => []
  | .eval term | .fact term => [term]
  | .defineEq left right | .defineType left right |
      .import left right | .addAtom left right | .removeAtom left right =>
      [left, right]
  | .defineRule left right premises => left :: right :: premises
  | .relationFact _ arguments | .builtinFact _ arguments |
      .directive _ arguments => arguments

/-- All pattern occurrences in a quoted program, in declaration and child
order. -/
def sourcePatterns (source : SourceProgram) : List SourcePattern :=
  source.flatMap fun row => sourceCommandPatterns row.2

theorem commandPatterns_erase (command : PlannedCommand) :
    (commandPatterns command).map PlannedPattern.erase =
      sourceCommandPatterns (eraseCommand command) := by
  cases command <;> rfl

/-- Planning evidence neither drops nor invents a source pattern occurrence.
The equality is positional, so duplicates are retained. -/
theorem plannedPatterns_erase (package : ProgramPlan) :
    (plannedPatterns package).map PlannedPattern.erase =
      sourcePatterns package.source := by
  unfold plannedPatterns sourcePatterns
  rw [← package.erases]
  unfold eraseRows
  induction package.planned with
  | nil => rfl
  | cons row rows inductionHypothesis =>
      rcases row with ⟨line, command⟩
      simp only [List.flatMap_cons, List.map_append, List.map_cons]
      rw [commandPatterns_erase, inductionHypothesis]

/-- One exact planned occurrence, retaining its declaration/child location
and proof that it belongs to this program package. -/
structure ProgramOccurrence (package : ProgramPlan) where
  planned : PlannedPattern
  member : planned ∈ plannedPatterns package

namespace ProgramOccurrence

def pattern {package : ProgramPlan} (occurrence : ProgramOccurrence package) :
    SourcePattern :=
  occurrence.planned.erase

/-- The selected occurrence is present in the unchanged authored source.
This is the source half of the adequacy boundary. -/
theorem pattern_mem_source {package : ProgramPlan}
    (occurrence : ProgramOccurrence package) :
    occurrence.pattern ∈ sourcePatterns package.source := by
  rw [← plannedPatterns_erase package]
  exact List.mem_map.mpr ⟨occurrence.planned, occurrence.member, rfl⟩

/-- Every source occurrence has the canonical conservative rho endpoint as
a closed native runtime-pattern term. -/
def endpoint {package : ProgramPlan} (occurrence : ProgramOccurrence package) :
    rhoInterpretation.Endpoint
      (.pattern occurrence.pattern : StagedReflectiveTm 0 0) :=
  rhoPatternEndpoint occurrence.pattern

end ProgramOccurrence

/-! ## Exact paths from source occurrences into Prime -/

/-- An occurrence-preserving interaction between two occurrences selected
from complete program packages.  The packages may be the same or distinct;
the path itself supplies all transition authority. -/
structure ProgramInteraction {sourcePackage targetPackage : ProgramPlan}
    (source : ProgramOccurrence sourcePackage)
    (target : ProgramOccurrence targetPackage) where
  path : EventPath rhoOccurrencePresentation source.pattern target.pattern

namespace ProgramInteraction

variable {sourcePackage targetPackage : ProgramPlan}
variable {source : ProgramOccurrence sourcePackage}
variable {target : ProgramOccurrence targetPackage}

/-- Internalize the exact event path as a Prime semantic term.  Endpoint
admissions are derived from the authored occurrences rather than supplied by
an unrelated caller. -/
def toPrime (interaction : ProgramInteraction source target) :
    familiesCwF.Tm PrimeContext
      (rhoInterpretation.computationTy rhoOccurrencePresentation
        (.pattern source.pattern) (.pattern target.pattern)) :=
  fun _ => ⟨source.endpoint, target.endpoint, interaction.path⟩

/-- Ordinary GSLT execution obtained by forgetting event identity. -/
def erase (interaction : ProgramInteraction source target) :
    rhoOccurrenceTheory.RewritePath source.pattern target.pattern :=
  interaction.path.erase

/-- The Prime term contains the same occurrence-specific event path supplied
by the source-indexed interaction. -/
@[simp] theorem toPrime_path (interaction : ProgramInteraction source target)
    (context : PrimeContext) :
    (interaction.toPrime context).2.2 = interaction.path :=
  rfl

/-- Erasing the path contained in the Prime term yields exactly the ordinary
authorized GSLT execution, with no new transition authority. -/
@[simp] theorem toPrime_erases (interaction : ProgramInteraction source target)
    (context : PrimeContext) :
    (interaction.toPrime context).2.2.erase = interaction.erase :=
  rfl

/-- Every selected occurrence admits the zero-event return computation. -/
def returnAt {package : ProgramPlan} (occurrence : ProgramOccurrence package) :
    ProgramInteraction occurrence occurrence where
  path := .nil (presentation := rhoOccurrencePresentation) occurrence.pattern

@[simp] theorem returnAt_erases_nil {package : ProgramPlan}
    (occurrence : ProgramOccurrence package) :
    (returnAt occurrence).erase =
      GSLT.RewritePath.nil (S := rhoOccurrenceTheory) occurrence.pattern :=
  rfl

end ProgramInteraction

/-! ## Positive and negative controls -/

def authoredRequestProgram : SourceProgram :=
  metta_program% petta "!(request ticket-7 (payload datum))"

def authoredRequestPackage : ProgramPlan :=
  prepareProgram rawPolicy authoredRequestProgram

def authoredRequestOccurrence : ProgramOccurrence authoredRequestPackage where
  planned := preparePattern rawPolicy ⟨0, 1, 0⟩
    (metta% petta "(request ticket-7 (payload datum))")
  member := by
    simp [authoredRequestPackage, authoredRequestProgram, plannedPatterns,
      commandPatterns, prepareProgram, prepareRows, prepareRowsFrom,
      prepareCommand, preparePattern, rawPolicy, ProgramCommand.mapIdx]

/-- Positive: a pattern from actual authored program text reaches the native
interaction fibre, and the return computation erases to the raw empty path. -/
theorem authored_request_return_source_adequate :
    authoredRequestOccurrence.pattern ∈
        sourcePatterns authoredRequestPackage.source ∧
      (ProgramInteraction.returnAt authoredRequestOccurrence).erase =
        GSLT.RewritePath.nil (S := rhoOccurrenceTheory)
          authoredRequestOccurrence.pattern := by
  exact ⟨authoredRequestOccurrence.pattern_mem_source,
    ProgramInteraction.returnAt_erases_nil authoredRequestOccurrence⟩

/-- Negative: dependent function types remain outside the rho endpoint
interpretation even though authored runtime-pattern occurrences are admitted.
Program quotation does not collapse Prime's static constructors into rho. -/
theorem dependent_function_remains_outside_source_interaction
    (domain : StagedReflectiveTm 0 0) (body : StagedReflectiveTm 0 1) :
    rhoInterpretation.lower? (.pi domain body) = none :=
  rfl

#print axioms plannedPatterns_erase
#print axioms CompiledProgram.compiled_after_plan_erasure
#print axioms CompiledProgram.theory_step_iff_source
#print axioms CompiledProgram.dfa_source_compilations_equal
#print axioms CompiledProgram.dfa_q0_zero_source_step
#print axioms ProgramOccurrence.pattern_mem_source
#print axioms ProgramInteraction.toPrime_erases
#print axioms authored_request_return_source_adequate
#print axioms dependent_function_remains_outside_source_interaction

end Mettapedia.Languages.MeTTa.Prime.NativeProgramSourceAdequacy
