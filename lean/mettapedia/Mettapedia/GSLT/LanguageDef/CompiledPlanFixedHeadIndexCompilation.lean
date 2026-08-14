import Mettapedia.GSLT.LanguageDef.CompiledPlanLoweringCompleteness
import Mettapedia.GSLT.LanguageDef.FiniteRuleIndexCompilation

/-!
# Fixed-head indexing for compiled plans

Every locally supported compiled-plan rule has an application at its head.
Consequently its outer byte string and immediate arity form a total, finite
dispatch key.  This module derives that fact from the same recognizer that
licenses `CGP1` lowering and instantiates the generic finite rule-index
refinement with it.

The generated index preserves source order and multiplicity inside every
bucket.  Querying a bucket is therefore exactly the source full scan, while
the runtime need not inspect unrelated rule heads.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanFixedHeadIndexCompilation

open CompiledPlanAdmission
open CompiledPlanLowering
open FiniteRuleIndexCompilation

/-- Number of immediate arguments in the typed compiled-plan carrier. -/
def termsLength : Terms -> Nat
  | .nil => 0
  | .cons _ tail => termsLength tail + 1

/-- Generated relation-and-arity key for an application term. -/
structure OuterKey where
  head : List UInt8
  arity : Nat
  deriving DecidableEq, Repr

/-- Partial outer-key projection.  Unsupported head shapes fail closed. -/
def termOuterKey? : Term -> Option OuterKey
  | .application head arguments =>
      some { head, arity := termsLength arguments }
  | _ => none

/-- Rule key consumed by the generic finite-index compiler. -/
def ruleOuterKey? (rule : TypedRule) : Option OuterKey :=
  termOuterKey? rule.head

/-- Local rule support proves that the generated outer key exists. -/
theorem ruleOuterKey?_isSome_of_locallySupported
    (rule : TypedRule) (supported : rule.locallySupported = true) :
    (ruleOuterKey? rule).isSome = true := by
  have headApplication : rule.head.isApplication = true := by
    simp [TypedRule.locallySupported] at supported
    aesop
  cases headShape : rule.head with
  | symbol name => simp [Term.isApplication, headShape] at headApplication
  | «variable» slot => simp [Term.isApplication, headShape] at headApplication
  | «string» value => simp [Term.isApplication, headShape] at headApplication
  | integer value => simp [Term.isApplication, headShape] at headApplication
  | application head arguments =>
      simp [ruleOuterKey?, termOuterKey?, headShape]

/-- The complete local program recognizer admits every rule to the fixed-head
index.  No catch-all bucket is introduced. -/
theorem ruleIndex_supported_of_locallySupported
    (source : TypedProgram) (supported : source.locallySupported = true) :
    FiniteRuleIndexCompilation.supported? ruleOuterKey? source = true := by
  have rulesSupported : source.all TypedRule.locallySupported = true := by
    simp [TypedProgram.locallySupported] at supported
    aesop
  rw [FiniteRuleIndexCompilation.supported?, List.all_eq_true]
  intro rule member
  exact ruleOuterKey?_isSome_of_locallySupported rule
    ((List.all_eq_true.mp rulesSupported) rule member)

/-- Fixed-head index compilation is complete for every locally supported
typed program. -/
theorem compileIndex_complete_of_locallySupported
    (source : TypedProgram) (supported : source.locallySupported = true) :
    ∃ index,
      FiniteRuleIndexCompilation.compile? ruleOuterKey? source = some index := by
  have recognized := ruleIndex_supported_of_locallySupported source supported
  have compiledSome :
      (FiniteRuleIndexCompilation.compile? ruleOuterKey? source).isSome =
        true := by
    rwa [FiniteRuleIndexCompilation.compile?_isSome_eq_supported?]
  cases compiled : FiniteRuleIndexCompilation.compile? ruleOuterKey? source with
  | none => simp [compiled] at compiledSome
  | some index => exact ⟨index, rfl⟩

/-- A single local certificate simultaneously yields the admitted physical
wire packet and the exact fixed-head index.  This is the composition seam
implemented by the generic C loader. -/
theorem compileBytes?_and_index_complete
    (source : TypedProgram) (supported : source.locallySupported = true) :
    ∃ bytes index,
      compileBytes? source = some bytes ∧
        FiniteRuleIndexCompilation.compile? ruleOuterKey? source =
          some index := by
  obtain ⟨index, indexCompiled⟩ :=
    compileIndex_complete_of_locallySupported source supported
  exact ⟨CompiledPlanWireFormat.encodeProgram (compile source), index,
    CompiledPlanLowering.compileBytes?_complete source supported,
    indexCompiled⟩

/-- Looking up the generated head-and-arity bucket is exactly an ordered
source scan for that key. -/
theorem lookup_compiledIndex_eq_sourceCandidates
    (source : TypedProgram)
    (index : BucketIndex OuterKey TypedRule)
    (accepted :
      FiniteRuleIndexCompilation.compile? ruleOuterKey? source = some index)
    (query : OuterKey) :
    lookup query index = sourceCandidates ruleOuterKey? source query :=
  lookup_compile?_eq_sourceCandidates
    ruleOuterKey? source index accepted query

/-! ## Independent shape and rejection canaries -/

private def unaryRule (name head : UInt8) : TypedRule :=
  { name := [name]
    head := .application [head] (.cons (.variable 0) .nil)
    body := []
    variableCount := 1 }

private def binaryRule (name head : UInt8) : TypedRule :=
  { name := [name]
    head := .application [head]
      (.cons (.variable 0) (.cons (.variable 1) .nil))
    body := []
    variableCount := 2 }

/-- Two relation-shaped rules retain their source order in one bucket. -/
example :
    sourceCandidates ruleOuterKey?
        [unaryRule 1 10, unaryRule 2 20, unaryRule 3 10]
        { head := [10], arity := 1 } =
      [unaryRule 1 10, unaryRule 3 10] := by
  decide

/-- A distinct binary rule-machine shape uses the same key projection. -/
example :
    (FiniteRuleIndexCompilation.compile? ruleOuterKey?
      [binaryRule 4 30, unaryRule 5 30]).isSome = true := by
  decide

/-- A non-application head is rejected rather than assigned a fallback key. -/
example :
    (FiniteRuleIndexCompilation.compile? ruleOuterKey?
      [{ name := [6]
         head := .symbol [40]
         body := []
         variableCount := 0 }]).isSome = false := by
  decide

end Mettapedia.GSLT.LanguageDef.CompiledPlanFixedHeadIndexCompilation
