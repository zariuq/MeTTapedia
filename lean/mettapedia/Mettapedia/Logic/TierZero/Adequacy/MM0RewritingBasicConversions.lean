import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingConversionJudgments

/-!
# Basic MM0 conversion rules as guarded rewriting steps

Reflexivity, symmetry, transitivity and transport of a proved statement use
ordinary request/take/read/make rules. Their logical justification comes from
the independent MM0 judgments. In particular, transitivity matches its shared
middle expression, and transport retains both the conversion and the proof.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open MM0ContextualSupport

inductive BasicConversion where
  | reflexivity | symmetry | transitivity | transport
  deriving DecidableEq

def BasicConversion.arity : BasicConversion → Nat
  | .reflexivity => 1
  | .symmetry | .transport => 2
  | .transitivity => 3

def BasicConversion.premises (width sort : Nat) : BasicConversion → List Pat
  | .reflexivity => []
  | .symmetry => [conversionPattern width sort (.var 0) (.var 1)]
  | .transitivity => [conversionPattern width sort (.var 0) (.var 1),
      conversionPattern width sort (.var 1) (.var 2)]
  | .transport => [conversionPattern width sort (.var 0) (.var 1), proofPattern width (.var 0)]

def BasicConversion.conclusion (width sort : Nat) : BasicConversion → Pat
  | .reflexivity => conversionPattern width sort (.var 0) (.var 0)
  | .symmetry => conversionPattern width sort (.var 1) (.var 0)
  | .transitivity => conversionPattern width sort (.var 0) (.var 2)
  | .transport => proofPattern width (.var 1)

def BasicConversion.rule (kind : BasicConversion) (signature : TermSignature) (target : Context)
    (sort : Nat) (name : String) : Rule Nat Tm Pat :=
  argumentRule signature target (regularFormals kind.arity sort) name
    (kind.premises target.length sort) (kind.conclusion target.length sort)

theorem BasicConversion.premises_bounded (kind : BasicConversion) (width sort : Nat) :
    ∀ pattern ∈ kind.premises width sort, ∀ index ∈ pattern.vars, index < kind.arity := by
  cases kind with
  | reflexivity => simp [premises]
  | symmetry =>
      intro pattern member
      have same : pattern = conversionPattern width sort (.var 0) (.var 1) := by simpa [premises] using member
      subst pattern
      exact conversionPattern_bounded _ _ _ _ _ (by simp [Preterm.VarsBelow, arity]) (by simp [Preterm.VarsBelow, arity])
  | transitivity =>
      intro pattern member
      rcases (show pattern = conversionPattern width sort (.var 0) (.var 1) ∨
          pattern = conversionPattern width sort (.var 1) (.var 2) from by simpa [premises] using member) with rfl | rfl
      · exact conversionPattern_bounded _ _ _ _ _ (by simp [Preterm.VarsBelow, arity]) (by simp [Preterm.VarsBelow, arity])
      · exact conversionPattern_bounded _ _ _ _ _ (by simp [Preterm.VarsBelow, arity]) (by simp [Preterm.VarsBelow, arity])
  | transport =>
      intro pattern member
      rcases (show pattern = conversionPattern width sort (.var 0) (.var 1) ∨
          pattern = proofPattern width (.var 0) from by simpa [premises] using member) with rfl | rfl
      · exact conversionPattern_bounded _ _ _ _ _ (by simp [Preterm.VarsBelow, arity]) (by simp [Preterm.VarsBelow, arity])
      · exact judgmentPattern_vars_below _ _ _ _ (by simp [Preterm.VarsBelow, arity])

theorem BasicConversion.conclusion_bounded (kind : BasicConversion) (width sort : Nat) :
    ∀ index ∈ (kind.conclusion width sort).vars, index < kind.arity := by
  cases kind with
  | reflexivity => exact conversionPattern_bounded _ _ _ _ _ (by simp [Preterm.VarsBelow, arity]) (by simp [Preterm.VarsBelow, arity])
  | symmetry => exact conversionPattern_bounded _ _ _ _ _ (by simp [Preterm.VarsBelow, arity]) (by simp [Preterm.VarsBelow, arity])
  | transitivity => exact conversionPattern_bounded _ _ _ _ _ (by simp [Preterm.VarsBelow, arity]) (by simp [Preterm.VarsBelow, arity])
  | transport => exact judgmentPattern_vars_below _ _ _ _ (by simp [Preterm.VarsBelow, arity])

theorem BasicConversion.local_sound (kind : BasicConversion)
    {signature : TermSignature} {definitions : Definition.Signature} {theorems : TheoremSignature}
    {target : Context} {hypotheses : List Preterm} (sort : Nat)
    (arguments : List Preterm) (selected : List Tm) (result : Tm)
    (admitted : Substitution.Admissible signature (regularFormals kind.arity sort) target arguments)
    (scopedArguments : ∀ argument ∈ arguments, Term.supportedAt target.length (encode target argument) = true)
    (matched : List.Forall₂ (ContextualPatterns.layer.Solves (expressionAssignment target arguments))
      (kind.premises target.length sort) selected)
    (valid : ∀ value ∈ selected, ValidValue signature definitions theorems target hypotheses value)
    (output : (kind.conclusion target.length sort).inst (expressionAssignment target arguments) = some result) :
    ValidValue signature definitions theorems target hypotheses result := by
  obtain ⟨count, typed⟩ := (regular_admissible_iff _ _ _ _ _).mp admitted
  cases kind with
  | reflexivity =>
      obtain ⟨expression, rfl⟩ := List.length_eq_one_iff.mp count
      have produced := conversionPattern_instantiated target [expression] scopedArguments sort
        (Preterm.Substitutes.var (index := 0) rfl) (Preterm.Substitutes.var (index := 0) rfl)
      have same : conversionValue target sort expression expression = result := Option.some.inj (produced.symm.trans output)
      subst result
      exact valid_conversion (.refl (typed expression (by simp)))
  | symmetry =>
      obtain ⟨left, right, rfl⟩ := List.length_eq_two.mp count
      cases matched with
      | cons first tail =>
        cases tail
        rename_i value
        have same := (matches_conversionPattern_iff target [left, right] scopedArguments sort
          (Preterm.Substitutes.var (index := 0) rfl) (Preterm.Substitutes.var (index := 1) rfl) value).mp first
        subst value
        have converted := (valid _ (by simp)).2 sort left right rfl
        have produced := conversionPattern_instantiated target [left, right] scopedArguments sort
          (Preterm.Substitutes.var (index := 1) rfl) (Preterm.Substitutes.var (index := 0) rfl)
        have resultSame : conversionValue target sort right left = result := Option.some.inj (produced.symm.trans output)
        subst result
        exact valid_conversion (.symm converted)
  | transitivity =>
      obtain ⟨left, middle, right, rfl⟩ := List.length_eq_three.mp count
      cases matched with
      | cons first tail =>
        cases tail with
        | cons second rest =>
          cases rest
          rename_i firstValue secondValue
          have sameFirst := (matches_conversionPattern_iff target [left, middle, right] scopedArguments sort
            (Preterm.Substitutes.var (index := 0) rfl) (Preterm.Substitutes.var (index := 1) rfl) firstValue).mp first
          have sameSecond := (matches_conversionPattern_iff target [left, middle, right] scopedArguments sort
            (Preterm.Substitutes.var (index := 1) rfl) (Preterm.Substitutes.var (index := 2) rfl) secondValue).mp second
          subst firstValue secondValue
          have firstConversion := (valid _ (by simp)).2 sort left middle rfl
          have secondConversion := (valid _ (by simp)).2 sort middle right rfl
          have produced := conversionPattern_instantiated target [left, middle, right] scopedArguments sort
            (Preterm.Substitutes.var (index := 0) rfl) (Preterm.Substitutes.var (index := 2) rfl)
          have same : conversionValue target sort left right = result := Option.some.inj (produced.symm.trans output)
          subst result
          exact valid_conversion (.trans firstConversion secondConversion)
  | transport =>
      obtain ⟨left, right, rfl⟩ := List.length_eq_two.mp count
      cases matched with
      | cons first tail =>
        cases tail with
        | cons second rest =>
          cases rest
          rename_i conversion proof
          have sameConversion := (matches_conversionPattern_iff target [left, right] scopedArguments sort
            (Preterm.Substitutes.var (index := 0) rfl) (Preterm.Substitutes.var (index := 1) rfl) conversion).mp first
          have sameProof : proofValue target left = proof := by
            have applied := (ContextualPatterns.solves_iff _ _ _).mp second
            rw [proofPattern_instantiation target [left, right] scopedArguments] at applied
            exact Option.some.inj applied
          subst conversion proof
          have converted := (valid _ (by simp)).2 sort left right rfl
          have derived := (valid _ (by simp)).1 left rfl
          have produced : (proofPattern target.length (.var 1)).inst (expressionAssignment target [left, right]) =
              some (proofValue target right) := by
            rw [proofPattern_instantiation target [left, right] scopedArguments]
            rfl
          have same : proofValue target right = result := Option.some.inj (produced.symm.trans output)
          subst result
          exact valid_proof (.conversion converted derived)

theorem BasicConversion.preserves (kind : BasicConversion)
    {sorts : SortSignature} {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {target : Context} {hypotheses : List Preterm}
    (formed : Context.WellFormed sorts target) (sort : Nat) (name : String)
    {before after : Multiset Tm}
    (valid : ∀ value ∈ before, ValidValue signature definitions theorems target hypotheses value)
    (step : Step ContextualPatterns.layer (kind.rule signature target sort name) before after) :
    ∀ value ∈ after, ValidValue signature definitions theorems target hypotheses value := by
  apply argumentRule_preserves formed name _ _
    (by simpa [regularFormals] using kind.premises_bounded target.length sort)
    (by simpa [regularFormals] using kind.conclusion_bounded target.length sort)
    _ (kind.local_sound sort) valid step

theorem BasicConversion.input (kind : BasicConversion) (signature : TermSignature) (target : Context)
    (sort : Nat) (name : String) : ContextualPatterns.RuleInput (kind.rule signature target sort name) := by
  have every (tag : String) (expressions : List Preterm) :
      (judgmentPattern target.length tag expressions).inputCheck = true :=
    (ContextualPatterns.Pattern.inputCheck_iff _).mpr (judgmentPattern_input _ _ _)
  apply (ContextualPatterns.ruleInputCheck_iff _).mp
  cases kind <;> simp [ContextualPatterns.ruleInputCheck, rule, argumentRule, requestRule,
    premises, theoremRequest, conversionPattern, proofPattern, every]

theorem reflexivity_step {sorts : SortSignature} {signature : TermSignature} {target : Context}
    (formed : Context.WellFormed sorts target) (name : String) {sort : Nat} {expression : Preterm}
    (typed : Preterm.HasType signature target expression [] sort) (state : Multiset Tm) :
    Step ContextualPatterns.layer (BasicConversion.reflexivity.rule signature target sort name)
      ({requestValue name [encode target expression]} + state)
      (state + {conversionValue target sort expression expression}) := by
  have admitted : Substitution.Admissible signature (regularFormals 1 sort) target [expression] :=
    (regular_admissible_iff _ _ _ _ _).mpr ⟨rfl, by simpa using typed⟩
  have scopedArguments := admitted_arguments_supported formed admitted
  apply argumentRule_complete formed name [] _ admitted [] _ state .nil (by simp)
  exact conversionPattern_instantiated target [expression] scopedArguments sort
    (.var (index := 0) rfl) (.var (index := 0) rfl)

theorem symmetry_step {sorts : SortSignature} {signature : TermSignature} {definitions : Definition.Signature}
    {target : Context} (formed : Context.WellFormed sorts target) (name : String)
    {sort : Nat} {left right : Preterm} (converted : Converts signature definitions target left right sort)
    (state : Multiset Tm) (present : conversionValue target sort left right ∈ state) :
    Step ContextualPatterns.layer (BasicConversion.symmetry.rule signature target sort name)
      ({requestValue name [encode target left, encode target right]} + state)
      (state + {conversionValue target sort right left}) := by
  have admitted : Substitution.Admissible signature (regularFormals 2 sort) target [left, right] :=
    (regular_admissible_iff _ _ _ _ _).mpr ⟨rfl, by simpa using converted.typed⟩
  have scopedArguments := admitted_arguments_supported formed admitted
  apply argumentRule_complete formed name _ _ admitted [conversionValue target sort left right] _ state
  · exact .cons ((matches_conversionPattern_iff target [left, right] scopedArguments sort
      (.var (index := 0) rfl) (.var (index := 1) rfl) _).mpr rfl) .nil
  · simpa using present
  · exact conversionPattern_instantiated target [left, right] scopedArguments sort
      (.var (index := 1) rfl) (.var (index := 0) rfl)

theorem transitivity_step {sorts : SortSignature} {signature : TermSignature} {definitions : Definition.Signature}
    {target : Context} (formed : Context.WellFormed sorts target) (name : String)
    {sort : Nat} {left middle right : Preterm}
    (first : Converts signature definitions target left middle sort)
    (second : Converts signature definitions target middle right sort)
    (state : Multiset Tm) (firstPresent : conversionValue target sort left middle ∈ state)
    (secondPresent : conversionValue target sort middle right ∈ state) :
    Step ContextualPatterns.layer (BasicConversion.transitivity.rule signature target sort name)
      ({requestValue name [encode target left, encode target middle, encode target right]} + state)
      (state + {conversionValue target sort left right}) := by
  have admitted : Substitution.Admissible signature (regularFormals 3 sort) target [left, middle, right] :=
    (regular_admissible_iff _ _ _ _ _).mpr ⟨rfl, by
      simpa using And.intro first.typed.1 (And.intro first.typed.2 second.typed.2)⟩
  have scopedArguments := admitted_arguments_supported formed admitted
  apply argumentRule_complete formed name _ _ admitted
    [conversionValue target sort left middle, conversionValue target sort middle right] _ state
  · exact .cons ((matches_conversionPattern_iff target [left, middle, right] scopedArguments sort
      (.var (index := 0) rfl) (.var (index := 1) rfl) _).mpr rfl)
      (.cons ((matches_conversionPattern_iff target [left, middle, right] scopedArguments sort
        (.var (index := 1) rfl) (.var (index := 2) rfl) _).mpr rfl) .nil)
  · simpa using And.intro firstPresent secondPresent
  · exact conversionPattern_instantiated target [left, middle, right] scopedArguments sort
      (.var (index := 0) rfl) (.var (index := 2) rfl)

theorem transport_step {sorts : SortSignature} {signature : TermSignature} {definitions : Definition.Signature}
    {target : Context} (formed : Context.WellFormed sorts target) (name : String)
    {sort : Nat} {left right : Preterm} (converted : Converts signature definitions target left right sort)
    (state : Multiset Tm) (conversionPresent : conversionValue target sort left right ∈ state)
    (proofPresent : proofValue target left ∈ state) :
    Step ContextualPatterns.layer (BasicConversion.transport.rule signature target sort name)
      ({requestValue name [encode target left, encode target right]} + state)
      (state + {proofValue target right}) := by
  have admitted : Substitution.Admissible signature (regularFormals 2 sort) target [left, right] :=
    (regular_admissible_iff _ _ _ _ _).mpr ⟨rfl, by simpa using converted.typed⟩
  have scopedArguments := admitted_arguments_supported formed admitted
  apply argumentRule_complete formed name _ _ admitted
    [conversionValue target sort left right, proofValue target left] _ state
  · apply List.Forall₂.cons
      ((matches_conversionPattern_iff target [left, right] scopedArguments sort
        (.var (index := 0) rfl) (.var (index := 1) rfl) _).mpr rfl)
    apply List.Forall₂.cons _ .nil
    apply (ContextualPatterns.solves_iff _ _ _).mpr
    rw [proofPattern_instantiation target [left, right] scopedArguments]
    rfl
  · simpa using And.intro conversionPresent proofPresent
  · change (proofPattern target.length (.var 1)).inst _ = _
    rw [proofPattern_instantiation target [left, right] scopedArguments]
    rfl

end Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting
