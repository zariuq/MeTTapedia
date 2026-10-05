import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRhoControls
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ChannelTest

/-!
# Quoted implementation code is outside the public-channel observer contract

The actual unary compiler emits different allocation code for two pi
processes related by the unused-restriction equation. A rho observer can use
their quoted emitted code as communication subjects: the allocation quote
answers this test and the inaction quote cannot answer it under any actual
equation-saturated firing. This is a boundary for observing compiler code,
not a claim about unrestricted lambda contextual equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoQuotedCompilerObserverControls

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open HeaderInversion HeaderExecution CanonicalMatch CanonicalStepperCompleteness
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEncodingTyping

def quoteCode (code : Code 0) : Pattern := .apply "NQuote" [code.term]

theorem quote_typed (code : Code 0) :
    NameWellSorted rhoReflectivePresentation rhoAtomicNameContext [] (quoteCode code) :=
  .quote code.typed

theorem quote_safe (code : Code 0) : binderSafeAt "NQuote" 0 (quoteCode code) = true := by
  simpa [quoteCode, binderSafeAt, binderSafeListAt] using code.safe

def allocationQuote : Pattern := quoteCode (Code.reserve (Code.zero 1))
def inactionQuote : Pattern := quoteCode (Code.zero 0)

/-- An equation-invariant constructor count separates the two literal
compiler outputs, independently of execution or a normalization bound. -/
theorem compiler_quotes_distinct :
    rhoCanonicalEquivalent allocationQuote inactionQuote = false := by
  apply Bool.eq_false_iff.mpr
  intro equal
  have structural := (rhoCanonicalEquivalent_eq_true_iff
    (PureBoundary.rhoNameWellSorted_hashSetFree (quote_typed (Code.reserve (Code.zero 1))))
    (PureBoundary.rhoNameWellSorted_hashSetFree (quote_typed (Code.zero 0)))).mp equal
  have impossible := Reduction.ioCount_SC structural
  change Reduction.ioCount allocationQuote = Reduction.ioCount inactionQuote at impossible
  simp [allocationQuote, inactionQuote, quoteCode, Code.reserve, Code.par,
    Code.sendName, Code.emit, Code.datum, Code.listen, Code.zero,
    NameValue.payload, NameValue.term, Reserved.label,
    Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedServers.parallel,
    Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedServers.send,
    Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedServers.receive,
    Reduction.ioCount] at impossible

def testHeaders (code : Code 0) : List Header :=
  ChannelTest.headers allocationQuote (quoteCode code) (Code.zero 1).term (Code.zero 0).term

theorem test_typed (code : Code 0) :
    ∀ header ∈ testHeaders code, header.Typed rhoAtomicNameContext := by
  intro header member
  simp [testHeaders, ChannelTest.headers] at member
  rcases member with rfl | rfl
  · exact ⟨quote_typed _, (Code.zero 1).typed⟩
  · exact ⟨quote_typed _, (Code.zero 0).typed⟩

theorem test_safe (code : Code 0) : ∀ header ∈ testHeaders code, header.Safe := by
  intro header member
  simp [testHeaders, ChannelTest.headers] at member
  rcases member with rfl | rfl
  · exact ⟨quote_safe _, (Code.zero 1).safe⟩
  · exact ⟨quote_safe _, (Code.zero 0).safe⟩

def testProcess (code : Code 0) : ParameterizedRewriteSystem.Process rhoAtomicNameContext :=
  headerProcess (testHeaders code) (test_typed code) (test_safe code)

/-- The positive test receipt is an authored COMM using this quote itself. -/
theorem allocation_quote_answers :
    ∃ after, (ParameterizedRewriteSystem.theory rhoAtomicNameContext).Step
      (testProcess (Code.reserve (Code.zero 1))) after := by
  apply (ChannelTest.enabled_iff allocationQuote allocationQuote _ _
    (test_typed _) (test_safe _)).mpr
  exact (rhoCanonicalEquivalent_iff _ _).mpr rfl

/-- No alternate structural redex can make the different emitted quote
answer the same listener. The endpoint quantifier is unrestricted. -/
theorem inaction_quote_cannot_answer :
    ∀ after, ¬ (ParameterizedRewriteSystem.theory rhoAtomicNameContext).Step
      (testProcess (Code.zero 0)) after := by
  apply ChannelTest.no_step_of_distinct allocationQuote inactionQuote _ _
    (test_typed _) (test_safe _)
  rw [compiler_quotes_distinct]
  decide

/-- The actual source equation and compiler outputs coexist with a
genuine operational test that distinguishes their quoted implementations. -/
theorem unused_scope_quoted_observer_boundary :
    StructuralEq (nu (nil : Proc [Srt.nm])) (nil : Proc []) ∧
      RhoUnaryCompiler.compile NamePassingRhoControls.emptyWorld
        (nu (nil : Proc [Srt.nm])) = some (Code.reserve (Code.zero 1)) ∧
      RhoUnaryCompiler.compile NamePassingRhoControls.emptyWorld
        (nil : Proc []) = some (Code.zero 0) ∧
      (∃ after, (ParameterizedRewriteSystem.theory rhoAtomicNameContext).Step
        (testProcess (Code.reserve (Code.zero 1))) after) ∧
      (∀ after, ¬ (ParameterizedRewriteSystem.theory rhoAtomicNameContext).Step
        (testProcess (Code.zero 0)) after) :=
  ⟨NamePassingRhoControls.source_unused_scope_is_inaction,
    NamePassingRhoControls.unused_scope_compiles, NamePassingRhoControls.inaction_compiles,
    allocation_quote_answers, inaction_quote_cannot_answer⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoQuotedCompilerObserverControls
