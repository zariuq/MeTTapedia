import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-!
# Canonical repeated-binding checks for pure rho

The generic MeTTaIL matcher is syntactic by default.  Rho COMM binds the
channel metavariable twice, however, and the pure calculus identifies names
whose quoted processes are structurally congruent.  This module supplies the
rho specialization of the generic equivalence-parameterized matcher.

This is not an engine profile and does not change generic execution.  Selecting
the comparator from authored language data is a separate integration step.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-! ## Agreement of the derived and theorem-oriented canonicalizers -/

private theorem charListCode_agreement (characters : List Char) :
    PatternCode.charListCode characters = Canonical.charListCode characters := by
  induction characters with
  | nil => rfl
  | cons character characters inductionHypothesis =>
      simp [PatternCode.charListCode, Canonical.charListCode, inductionHypothesis]

private theorem stringCode_agreement (value : String) :
    PatternCode.stringCode value = Canonical.stringCode value := by
  exact charListCode_agreement value.toList

private theorem stringListCode_agreement (values : List String) :
    PatternCode.stringListCode values = Canonical.stringListCode values := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp [PatternCode.stringListCode, Canonical.stringListCode,
        stringCode_agreement, inductionHypothesis]

private theorem optionStringCode_agreement (value : Option String) :
    PatternCode.optionStringCode value = Canonical.optionStringCode value := by
  cases value <;>
    simp [PatternCode.optionStringCode, Canonical.optionStringCode, stringCode_agreement]

private theorem collectionCode_agreement (collectionType : CollType) :
    PatternCode.collectionCode collectionType = Canonical.collectionCode collectionType := by
  cases collectionType <;> rfl

mutual
  private theorem patternCode_agreement (pattern : Pattern) :
      PatternCode.patternCode pattern = Canonical.patternCode pattern := by
    cases pattern with
    | bvar index => rfl
    | fvar name =>
        simp [PatternCode.patternCode, Canonical.patternCode, stringCode_agreement]
    | apply constructor arguments =>
        simp [PatternCode.patternCode, Canonical.patternCode, stringCode_agreement,
          patternListCode_agreement arguments]
    | lambda binderName body =>
        simp [PatternCode.patternCode, Canonical.patternCode,
          optionStringCode_agreement, patternCode_agreement body]
    | multiLambda arity binderNames body =>
        simp [PatternCode.patternCode, Canonical.patternCode,
          stringListCode_agreement, patternCode_agreement body]
    | subst body replacement =>
        simp [PatternCode.patternCode, Canonical.patternCode,
          patternCode_agreement body, patternCode_agreement replacement]
    | collection collectionType elements rest =>
        simp [PatternCode.patternCode, Canonical.patternCode,
          collectionCode_agreement, patternListCode_agreement elements,
          optionStringCode_agreement]
  termination_by sizeOf pattern
  decreasing_by
    all_goals simp_wf
    all_goals omega

  private theorem patternListCode_agreement (patterns : List Pattern) :
      PatternCode.patternListCode patterns = Canonical.patternListCode patterns := by
    cases patterns with
    | nil => rfl
    | cons pattern patterns =>
        simp [PatternCode.patternListCode, Canonical.patternListCode,
          patternCode_agreement pattern, patternListCode_agreement patterns]
  termination_by sizeOf patterns
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

private theorem sortPatterns_agreement (patterns : List Pattern) :
    PatternCode.sortPatterns patterns = Canonical.sortPatterns patterns := by
  simp [PatternCode.sortPatterns, Canonical.sortPatterns, patternCode_agreement]

private theorem parallelSplice_agreement (pattern : Pattern) :
    ReflectiveCanonical.parallelSplice rhoReflectivePresentation pattern =
      Canonical.bagSplice pattern := by
  cases pattern with
  | bvar index => rfl
  | fvar name => rfl
  | apply constructor arguments => rfl
  | lambda binderName body => rfl
  | multiLambda arity binderNames body => rfl
  | subst body replacement => rfl
  | collection collectionType elements rest =>
      cases collectionType <;> cases rest <;>
        simp [ReflectiveCanonical.parallelSplice, Canonical.bagSplice,
          rhoReflectivePresentation]

private theorem normalizeParallelElements_agreement (patterns : List Pattern) :
    ReflectiveCanonical.normalizeParallelElements rhoReflectivePresentation patterns =
      Canonical.normalizeBagElements patterns := by
  unfold ReflectiveCanonical.normalizeParallelElements Canonical.normalizeBagElements
  simp only [rhoReflectivePresentation]
  rw [show patterns.flatMap
        (ReflectiveCanonical.parallelSplice
          { name := "RhoCommSubstitution", rewriteRule := "Comm",
            processSort := "Proc", nameSort := "Name",
            quoteConstructor := "NQuote", dropConstructor := "PDrop",
            inputConstructor := "PInput", outputConstructor := "POutput",
            parallelCollection := .hashBag,
            parallelUnitConstructor := "PZero",
            quoteDropEquation := "QuoteDrop" }) =
      patterns.flatMap Canonical.bagSplice by
        apply List.flatMap_congr
        intro pattern membership
        exact parallelSplice_agreement pattern]
  exact sortPatterns_agreement _

private theorem collapseParallel_agreement (patterns : List Pattern) :
    ReflectiveCanonical.collapseParallel rhoReflectivePresentation patterns =
      Canonical.collapseBag patterns := by
  cases patterns with
  | nil => rfl
  | cons pattern patterns =>
      cases patterns with
      | nil => rfl
      | cons second remainder => rfl

private theorem finishQuote_agreement (pattern : Pattern) :
    ReflectiveSubstitution.finishNormalizeReflectiveApply
        rhoReflectivePresentation "NQuote" [pattern] =
      Canonical.normalizeQuote pattern := by
  cases pattern with
  | bvar index => rfl
  | fvar name => rfl
  | apply constructor arguments =>
      by_cases drop : constructor = "PDrop"
      · subst constructor
        cases arguments with
        | nil => rfl
        | cons name rest =>
            cases rest with
            | nil => rfl
            | cons second remainder => rfl
      · cases arguments with
        | nil =>
            simp [ReflectiveSubstitution.finishNormalizeReflectiveApply,
              Canonical.normalizeQuote, rhoReflectivePresentation]
        | cons argument rest =>
            cases rest with
            | nil =>
                simp [ReflectiveSubstitution.finishNormalizeReflectiveApply,
                  Canonical.normalizeQuote, rhoReflectivePresentation, drop]
            | cons second remainder =>
                simp [ReflectiveSubstitution.finishNormalizeReflectiveApply,
                  Canonical.normalizeQuote, rhoReflectivePresentation]
  | lambda binderName body => rfl
  | multiLambda arity binderNames body => rfl
  | subst body replacement => rfl
  | collection collectionType elements rest => rfl

private theorem canonicalizeList_agreement_of_pointwise
    (patterns : List Pattern)
    (pointwise : ∀ pattern ∈ patterns,
      ReflectiveCanonical.canonicalize rhoReflectivePresentation pattern =
        Canonical.canonicalize pattern) :
    ReflectiveCanonical.canonicalizeList rhoReflectivePresentation patterns =
      Canonical.canonicalizeList patterns := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp only [ReflectiveCanonical.canonicalizeList, Canonical.canonicalizeList]
      rw [pointwise pattern (by simp)]
      rw [inductionHypothesis (fun member membership =>
        pointwise member (by simp [membership]))]

/-- The canonicalizer compiled from the authored rho declaration agrees on
every shared `Pattern` with the independently verified pure-rho canonicalizer. -/
theorem derivedCanonicalize_eq (pattern : Pattern) :
    ReflectiveCanonical.canonicalize rhoReflectivePresentation pattern =
      Canonical.canonicalize pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly constructor arguments inductionHypothesis =>
      have argumentsAgreement :=
        canonicalizeList_agreement_of_pointwise arguments inductionHypothesis
      by_cases quoteShape :
          constructor = "NQuote" ∧ ∃ argument, arguments = [argument]
      · obtain ⟨rfl, argument, rfl⟩ := quoteShape
        simp only [ReflectiveCanonical.canonicalize]
        rw [argumentsAgreement]
        change ReflectiveSubstitution.finishNormalizeReflectiveApply
            rhoReflectivePresentation "NQuote" [Canonical.canonicalize argument] =
          Canonical.normalizeQuote (Canonical.canonicalize argument)
        exact finishQuote_agreement _
      · rw [Canonical.canonicalize_apply_general constructor arguments quoteShape]
        simp only [ReflectiveCanonical.canonicalize]
        rw [argumentsAgreement]
        by_cases quoteConstructor : constructor = "NQuote"
        · subst constructor
          cases arguments with
          | nil => rfl
          | cons argument tail =>
              cases tail with
              | nil => exact False.elim (quoteShape ⟨rfl, argument, rfl⟩)
              | cons second remainder =>
                  simp [ReflectiveSubstitution.finishNormalizeReflectiveApply,
                    rhoReflectivePresentation, Canonical.canonicalizeList]
        · simp [ReflectiveSubstitution.finishNormalizeReflectiveApply,
            rhoReflectivePresentation, quoteConstructor]
  | hlambda binderName body inductionHypothesis =>
      change Pattern.lambda binderName
          (ReflectiveCanonical.canonicalize rhoReflectivePresentation body) =
        Pattern.lambda binderName (Canonical.canonicalize body)
      rw [inductionHypothesis]
  | hmultiLambda arity binderNames body inductionHypothesis =>
      change Pattern.multiLambda arity binderNames
          (ReflectiveCanonical.canonicalize rhoReflectivePresentation body) =
        Pattern.multiLambda arity binderNames (Canonical.canonicalize body)
      rw [inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      change Pattern.subst
          (ReflectiveCanonical.canonicalize rhoReflectivePresentation body)
          (ReflectiveCanonical.canonicalize rhoReflectivePresentation replacement) =
        Pattern.subst (Canonical.canonicalize body)
          (Canonical.canonicalize replacement)
      rw [bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      have elementsAgreement :=
        canonicalizeList_agreement_of_pointwise elements inductionHypothesis
      by_cases parallelShape : collectionType = .hashBag ∧ rest = none
      · obtain ⟨rfl, rfl⟩ := parallelShape
        change ReflectiveCanonical.collapseParallel rhoReflectivePresentation
            (ReflectiveCanonical.normalizeParallelElements rhoReflectivePresentation
              (ReflectiveCanonical.canonicalizeList rhoReflectivePresentation elements)) =
          Canonical.collapseBag
            (Canonical.normalizeBagElements (Canonical.canonicalizeList elements))
        rw [elementsAgreement, normalizeParallelElements_agreement,
          collapseParallel_agreement]
      · rw [Canonical.canonicalize_collection_general collectionType elements rest parallelShape]
        cases rest with
        | none =>
            have notBag : collectionType ≠ .hashBag := by
              intro equality
              exact parallelShape ⟨equality, rfl⟩
            have derivedShape :
                ReflectiveCanonical.canonicalize rhoReflectivePresentation
                    (.collection collectionType elements none) =
                  .collection collectionType
                    (ReflectiveCanonical.canonicalizeList
                      rhoReflectivePresentation elements) none := by
              simp [ReflectiveCanonical.canonicalize, rhoReflectivePresentation,
                notBag]
            rw [derivedShape, elementsAgreement]
        | some restName =>
            simp [ReflectiveCanonical.canonicalize, elementsAgreement]

theorem derivedCanonicalizeList_eq (patterns : List Pattern) :
    ReflectiveCanonical.canonicalizeList rhoReflectivePresentation patterns =
      Canonical.canonicalizeList patterns := by
  apply canonicalizeList_agreement_of_pointwise
  intro pattern membership
  exact derivedCanonicalize_eq pattern

/-- Boolean equality compiled from the authored pure-rho presentation. -/
def rhoCanonicalEquivalent (left right : Pattern) : Bool :=
  ReflectiveCanonical.canonicalEquivalent rhoReflectivePresentation left right

/-- On the pure fragment, the executable comparator recognizes exactly the
paper's structural congruence. -/
theorem rhoCanonicalEquivalent_eq_true_iff {left right : Pattern}
    (leftFree : Canonical.HashSetFree left)
    (rightFree : Canonical.HashSetFree right) :
    rhoCanonicalEquivalent left right = true ↔ StructuralCongruence left right := by
  rw [rhoCanonicalEquivalent, ReflectiveCanonical.canonicalEquivalent_eq_true_iff,
    derivedCanonicalize_eq, derivedCanonicalize_eq]
  exact (Canonical.structuralCongruence_iff_canonicalize_eq leftFree rightFree).symm

/-! ## Executable COMM-channel boundary examples -/

private def canonicalChannel : Pattern :=
  .apply "NQuote" [.apply "PZero" []]

private def unitExpandedChannel : Pattern :=
  .apply "NQuote"
    [.collection .hashBag [.apply "PZero" [], .apply "PZero" []] none]

private def distinctChannel : Pattern :=
  .apply "NQuote"
    [.apply "POutput" [canonicalChannel, .apply "PZero" []]]

private def commCandidate (outputChannel : Pattern) : Pattern :=
  .collection .hashBag
    [.apply "PInput" [unitExpandedChannel, .lambda none (.bvar 0)],
      .apply "POutput" [outputChannel, .apply "PZero" []]]
    none

-- Raw syntax rejects two presentations of the same rho channel.
#guard (matchPattern rhoCommRewrite.left (commCandidate canonicalChannel)).isEmpty

-- Canonical repeated-binding equality admits the structurally congruent
-- channel presentations.
#guard !(matchPatternWith rhoCanonicalEquivalent rhoCommRewrite.left
  (commCandidate canonicalChannel)).isEmpty

-- Canonical equality still rejects genuinely distinct channels.
#guard (matchPatternWith rhoCanonicalEquivalent rhoCommRewrite.left
  (commCandidate distinctChannel)).isEmpty

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch
