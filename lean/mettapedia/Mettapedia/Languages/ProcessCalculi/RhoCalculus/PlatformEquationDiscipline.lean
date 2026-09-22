import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformEquations
import Mettapedia.GSLT.LanguageDef.SortedEquationInstance
import Mettapedia.GSLT.LanguageDef.WellSortedFillInversion
import Mettapedia.OSLF.Framework.SortedEquationFrame
import Mettapedia.OSLF.Framework.SourceGenerator

/-!
# What the generated equation theory does with an equation's type context

An authored equation carries a type context: `quoteDropEquation` declares its
schema variable to be a *name*, which is what makes reflection a statement about
names coding processes.  The instance relation that generates the equation
theory does not read that context.  It matches the equation's side against the
term with the ordinary pattern matcher, so a schema variable declared to be a
name is instantiated by any pattern at all.

The consequence is recorded here rather than described, because it decides what
the frame of a generated logic can contain.  On the platform presentation the
terminated process -- which the presentation declares to be a process, and which
no rule declares to be a name -- is equated with the name that quotes its drop.
So no predicate that tells a quote from a non-quote is equation-invariant, and
therefore no such predicate is a predicate of the generated logic.

This is why the negative half of a scope statement is proved in the ambient
powerset in this tree and not in the equation frame.  It is not a missing lemma:
the statement the lemma would have is false while instances are unsorted.

The repair this points at is a sort-disciplined instance relation -- one that
requires each binding to be sorted at the type the equation's own context
declares for it.  That is a change to the equation layer rather than to any
presentation, and it is not made here; what is made here is the evidence that it
is needed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformEquationDiscipline

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation

variable (arities : List Nat)

/-- The terminated process. -/
def stop : Pattern := .apply stopDeclaration.label []

/-- The name that quotes its drop. -/
def quotedDropOfStop : Pattern := .apply quoteLabel [.apply dropLabel [stop]]

/-- **The equation's schema variable is declared to be a name.** -/
theorem quoteDropEquation_declares_a_name :
    quoteDropEquation.typeContext = [("N", TypeExpr.name)] := rfl

/-- **And the matcher instantiates it by the terminated process anyway**, which
the presentation declares to be a process.  Kernel-checked. -/
theorem matcher_instantiates_name_by_a_process :
    matchPattern quoteDropEquation.right stop = [[("N", stop)]] := by
  decide +kernel

/-- **So the theory equates the two.**  One step, at the root, by the reverse
direction of the presentation's own reflection equation. -/
theorem stop_equated_with_quotedDropOfStop (base : BasePremiseEvaluator) :
    EquationEquiv base (rhoPlatform arities) stop quotedDropOfStop :=
  Relation.EqvGen.rel _ _
    (EquationContextStep.inContext .hole
      (Or.inl ⟨0, EquationInstanceAt.reverse
        (equation := quoteDropEquation) (initialBindings := [("N", stop)])
        (finalBindings := [("N", stop)])
        (List.Mem.head _)
        (by decide +kernel)
        (PremisesAt.nil _)
        (by decide +kernel)⟩))

/-- **And the identification is not special to the terminated process.**  The
reverse direction of the equation matches a bare schema variable, so *every*
pattern whatsoever is equated with the name that quotes its drop. -/
theorem every_pattern_equated_with_its_quote (base : BasePremiseEvaluator)
    (term : Pattern) :
    EquationEquiv base (rhoPlatform arities) term
      (.apply quoteLabel [.apply dropLabel [term]]) :=
  Relation.EqvGen.rel _ _
    (EquationContextStep.inContext .hole
      (Or.inl ⟨0, EquationInstanceAt.reverse
        (equation := quoteDropEquation) (initialBindings := [("N", term)])
        (finalBindings := [("N", term)])
        (List.Mem.head _)
        (by simp [quoteDropEquation, matchPattern])
        (PremisesAt.nil _)
        (by simp [quoteDropEquation, applyBindings, quoteLabel, dropLabel])⟩))

/-- **So "is a quote up to the equations" holds of everything** in the
permissive theory of this presentation.  A statement of that form is therefore
without content here, and the tree's generated-logic bound on the source's scope
generator is one such statement: true, and saying nothing, until the instances
read their type contexts. -/
theorem permissive_quote_predicate_is_trivial (relEnv : RelationEnv)
    (term : Pattern) :
    ∃ inner, (langGSLTUsing relEnv (rhoPlatform arities)).Equiv term
      (.apply quoteLabel [inner]) :=
  ⟨.apply dropLabel [term],
    every_pattern_equated_with_its_quote arities (engineBasePremises relEnv) term⟩

/-- The terminated process is a process of the presentation. -/
theorem stop_is_a_process :
    HasSort (rhoPlatform arities) FreeTypeContext.empty [] stop "Proc" :=
  HasType.constructor (by simp [rhoPlatform])
    (by rintro ⟨_, _, _, shape⟩; simp [stopDeclaration] at shape) .nil

/-- **No predicate separating quotes from non-quotes is invariant**, and
therefore none is a predicate of the generated logic.  This is the obstruction,
stated as an impossibility rather than left as an open obligation. -/
theorem no_quote_separating_invariant (relEnv : RelationEnv) :
    ¬ ∃ predicate : Pattern → Prop,
        EquationInvariant (langGSLTUsing relEnv (rhoPlatform arities)) predicate ∧
          predicate stop ∧
          ∀ inner : Pattern, ¬ predicate (.apply quoteLabel [inner]) := by
  rintro ⟨predicate, invariant, holdsAtStop, refutesQuotes⟩
  exact refutesQuotes (.apply dropLabel [stop])
    ((invariant (stop_equated_with_quotedDropOfStop arities
      (engineBasePremises relEnv))).mp holdsAtStop)

/-- **Positive**: the theory does contain the identification the presentation
intended, at a name that really is one. -/
theorem quote_of_drop_of_a_name (base : BasePremiseEvaluator) (process : Pattern) :
    EquationEquiv base (rhoPlatform arities)
      (.apply quoteLabel [.apply dropLabel [.apply quoteLabel [process]]])
      (.apply quoteLabel [process]) :=
  Relation.EqvGen.rel _ _
    (EquationContextStep.inContext .hole
      (Or.inl ⟨0, EquationInstanceAt.forward
        (equation := quoteDropEquation)
        (initialBindings := [("N", .apply quoteLabel [process])])
        (finalBindings := [("N", .apply quoteLabel [process])])
        (List.Mem.head _)
        (by simp [quoteDropEquation, quoteLabel, dropLabel, matchPattern,
          matchArgs, mergeBindings])
        (PremisesAt.nil _)
        (by simp [applyBindings, quoteDropEquation])⟩))

/-! ## The disciplined theory keeps the two sorts apart

`SortedEquationInstance` supplies the instance relation that reads the
equation's type context.  Here is what that buys on this presentation: the
predicate the permissive theory cannot have -- "is headed by the quote" -- is an
invariant of the disciplined one, and the identification above is therefore
absent from it.  The argument is the presentation's own grammar and nothing
else: no rule declares a quote to be a process, and the only rule declaring a
name is the quote. -/

open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- The presentation, at the arity the specimens use. -/
abbrev platform : LanguageDef := rhoPlatform [2]

/-- "Is headed by the quote former." -/
def QuoteHeaded (term : Pattern) : Prop := ∃ inner, term = .apply quoteLabel [inner]

theorem stop_not_quoteHeaded : ¬ QuoteHeaded stop := by
  rintro ⟨inner, shape⟩
  simp [stop, stopDeclaration, quoteLabel] at shape

theorem quotedDropOfStop_quoteHeaded : QuoteHeaded quotedDropOfStop :=
  ⟨.apply dropLabel [stop], rfl⟩

/-- **No rule declares a quote to be a process**, so a process is never headed
by the quote — in any typing context. -/
theorem process_not_quoteHeaded {free : FreeTypeContext} {bound : List TypeExpr}
    {term : Pattern} (quoted : QuoteHeaded term)
    (typed : HasType platform free bound term (.base "Proc")) : False := by
  obtain ⟨inner, rfl⟩ := quoted
  obtain ⟨rule, member, labelEq, -, typeEq, -⟩ := hasType_apply_inversion typed
  have categoryEq : rule.category = "Proc" := by
    injection typeEq with categoryEq
    exact categoryEq.symm
  have noSuchRule : ∀ candidate ∈ platform.terms,
      ¬ (candidate.label = quoteLabel ∧ candidate.category = "Proc") := by
    decide +kernel
  exact noSuchRule rule member ⟨labelEq.symm, categoryEq⟩

/-- **Only the quote declares a name**, so a term of the name sort — an object
pattern, sorted at the empty context — is headed by the quote. -/
theorem name_is_quoteHeaded {term : Pattern}
    (object : isObjectPattern term = true)
    (typed : HasType platform FreeTypeContext.empty [] term (.base "Name")) :
    QuoteHeaded term := by
  cases term with
  | bvar index => cases typed with | bvar bound => simp at bound
  | fvar name => cases typed with | fvar free => simp [FreeTypeContext.empty] at free
  | lambda _ _ => cases typed
  | multiLambda _ _ _ => cases typed
  | subst _ _ => simp [isObjectPattern] at object
  | apply label arguments =>
      obtain ⟨rule, member, labelEq, -, typeEq, argumentsTyped⟩ :=
        hasType_apply_inversion typed
      have categoryEq : rule.category = "Name" := by
        injection typeEq with categoryEq
        exact categoryEq.symm
      have onlyQuote : ∀ candidate ∈ platform.terms,
          candidate.category = "Name" →
            candidate.label = quoteLabel ∧ candidate.params.length = 1 := by
        decide +kernel
      obtain ⟨quoteLabelEq, oneParameter⟩ := onlyQuote rule member categoryEq
      have lengthEq : arguments.length = 1 := by
        rw [ArgumentsHaveTypes.length_eq argumentsTyped, oneParameter]
      match arguments, lengthEq with
      | [argument], _ => exact ⟨argument, by rw [labelEq, quoteLabelEq]⟩
  | collection collectionType elements rest =>
      rcases hasType_collection_inversion typed with
        ⟨elementType, typeEq, -⟩ | ⟨rule, parameterName, elementType, member,
          parameterShape, typeEq, -⟩
      · exact absurd typeEq (by simp)
      · have categoryEq : rule.category = "Name" := by
          injection typeEq with categoryEq
          exact categoryEq.symm
        have noCollectionName : ∀ candidate ∈ platform.terms,
            candidate.category = "Name" → candidate.params.all
              (fun parameter => match parameter with
                | .simple _ (.collection _ _) => false
                | _ => true) = true := by
          decide +kernel
        have := noCollectionName rule member categoryEq
        rw [parameterShape] at this
        simp at this

/-- **A presentation-derived law never crosses the quote**: both of its sides
are compositions, unit constants or processes, and none of those is a quote. -/
theorem derived_not_quoteHeaded {source target : Pattern}
    (derived : DerivedInstance platform source target) :
    ¬ QuoteHeaded source ∧ ¬ QuoteHeaded target := by
  cases derived with
  | bagPerm _ _ _ =>
      exact ⟨by rintro ⟨_, shape⟩; exact Pattern.noConfusion shape,
        by rintro ⟨_, shape⟩; exact Pattern.noConfusion shape⟩
  | setPerm _ _ _ =>
      exact ⟨by rintro ⟨_, shape⟩; exact Pattern.noConfusion shape,
        by rintro ⟨_, shape⟩; exact Pattern.noConfusion shape⟩
  | setDedup _ _ =>
      exact ⟨by rintro ⟨_, shape⟩; exact Pattern.noConfusion shape,
        by rintro ⟨_, shape⟩; exact Pattern.noConfusion shape⟩
  | flatten _ _ _ =>
      exact ⟨by rintro ⟨_, shape⟩; exact Pattern.noConfusion shape,
        by rintro ⟨_, shape⟩; exact Pattern.noConfusion shape⟩
  | unitElim _ _ _ =>
      exact ⟨by rintro ⟨_, shape⟩; exact Pattern.noConfusion shape,
        by rintro ⟨_, shape⟩; exact Pattern.noConfusion shape⟩
  | emptyUnit algebraRule unitEq _ =>
      refine ⟨by rintro ⟨_, shape⟩; exact Pattern.noConfusion shape, ?_⟩
      rintro ⟨_, shape⟩
      simp at shape
  | @singleton rule kind algebra element algebraRule _ sorted =>
      refine ⟨by rintro ⟨_, shape⟩; exact Pattern.noConfusion shape, ?_⟩
      intro quoted
      obtain ⟨free, bound, typed⟩ := sorted
      rcases hasType_collection_inversion typed with
        ⟨elementType, typeEq, -⟩ | ⟨carrier, parameterName, elementType, member,
          parameterShape, -, elementsTyped⟩
      · exact absurd typeEq (by simp)
      · have elementProc : elementType = .base "Proc" := by
          have onlyPar : ∀ candidate ∈ platform.terms,
              candidate.params.all (fun parameter =>
                match parameter with
                | .simple _ (.collection _ elementType') =>
                    elementType' == TypeExpr.base "Proc"
                | _ => true) = true := by
            decide +kernel
          have scanned := onlyPar carrier member
          rw [parameterShape] at scanned
          simpa using scanned
        cases elementsTyped with
        | cons elementTyped _ =>
            rw [elementProc] at elementTyped
            exact process_not_quoteHeaded quoted elementTyped

/-- **A disciplined authored instance never crosses it either**: both of its
sides are quotes, because the equation's own type context says its variable is a
name and the only name-former is the quote. -/
theorem sortedInstance_quoteHeaded_iff (base : BasePremiseEvaluator)
    {source target : Pattern}
    (sorted : SortedEquationInstance base platform source target) :
    QuoteHeaded source ↔ QuoteHeaded target := by
  obtain ⟨fuel, instance'⟩ := sorted
  cases instance' with
  | forward member matched premises sortedBindings applied =>
      rename_i equation initialBindings finalBindings
      have memList : equation ∈ platform.equations := member
      have equationEq : equation = quoteDropEquation := by
        simpa [rhoPlatform] using memList
      subst equationEq
      obtain ⟨object, typed⟩ :=
        sortedBindings "N" TypeExpr.name (by simp [quoteDropEquation])
      have sourceQuoted : QuoteHeaded source := by
        cases source with
        | apply label arguments =>
            simp only [quoteDropEquation, matchPattern] at matched
            split at matched
            · rename_i condition
              simp only [Bool.and_eq_true, beq_iff_eq] at condition
              match arguments, condition with
              | [argument], ⟨labelEq, _⟩ => exact ⟨argument, by rw [labelEq]⟩
            · simp at matched
        | bvar _ => simp [quoteDropEquation, matchPattern] at matched
        | fvar _ => simp [quoteDropEquation, matchPattern] at matched
        | lambda _ _ => simp [quoteDropEquation, matchPattern] at matched
        | multiLambda _ _ _ => simp [quoteDropEquation, matchPattern] at matched
        | subst _ _ => simp [quoteDropEquation, matchPattern] at matched
        | collection _ _ _ => simp [quoteDropEquation, matchPattern] at matched
      have targetQuoted : QuoteHeaded target := by
        rw [← applied]
        exact name_is_quoteHeaded object typed
      exact iff_of_true sourceQuoted targetQuoted
  | reverse member matched premises sortedBindings applied =>
      rename_i equation initialBindings finalBindings
      have memList : equation ∈ platform.equations := member
      have equationEq : equation = quoteDropEquation := by
        simpa [rhoPlatform] using memList
      subst equationEq
      have bindingsEq : initialBindings = [("N", source)] := by
        simpa [quoteDropEquation, matchPattern] using matched
      have finalEq : finalBindings = initialBindings := by
        cases premises with
        | nil _ => rfl
      obtain ⟨object, typed⟩ :=
        sortedBindings "N" TypeExpr.name (by simp [quoteDropEquation])
      rw [finalEq, bindingsEq] at object typed
      simp only [applyBindings, List.find?] at object typed
      have sourceQuoted : QuoteHeaded source := name_is_quoteHeaded object typed
      have targetQuoted : QuoteHeaded target := by
        refine ⟨.apply dropLabel [source], ?_⟩
        rw [← applied, finalEq, bindingsEq]
        simp [quoteDropEquation, applyBindings, quoteLabel, dropLabel]
      exact iff_of_true sourceQuoted targetQuoted

/-- **So the quote is an invariant of the disciplined theory.** -/
theorem quoteHeaded_respects (base : BasePremiseEvaluator)
    (context : OneHoleContext) (redex contractum : Pattern)
    (generator : SortedEquationGenerator base platform redex contractum) :
    QuoteHeaded (context.fill redex) ↔ QuoteHeaded (context.fill contractum) := by
  by_cases isHole : context = .hole
  · subst isHole
    simp only [QuoteHeaded, OneHoleContext.fill_hole]
    rcases generator with sorted | derived
    · exact sortedInstance_quoteHeaded_iff base sorted
    · obtain ⟨sourceNot, targetNot⟩ := derived_not_quoteHeaded derived
      exact iff_of_false sourceNot targetNot
  · exact headedBy_fill_congr quoteLabel context redex contractum isHole

/-- **And the identification the permissive theory makes is absent from the
disciplined one.**  The terminated process is not equated with the name that
quotes its drop once instances read the equation's own type context.  Compare
`stop_equated_with_quotedDropOfStop`: same presentation, same equation, and the
discipline is the whole difference. -/
theorem stop_not_sortedEquated (base : BasePremiseEvaluator) :
    ¬ SortedEquationEquiv base platform stop quotedDropOfStop := by
  intro equivalent
  exact stop_not_quoteHeaded
    ((sortedEquationEquiv_invariant (quoteHeaded_respects base) equivalent).mpr
      quotedDropOfStop_quoteHeaded)

/-- **And the frame of a disciplined generated logic can carry what the
permissive one cannot**: "is headed by the quote" is respected by the whole
disciplined theory. -/
theorem quoteHeaded_sortedEquationInvariant (base : BasePremiseEvaluator)
    {left right : Pattern}
    (equivalent : SortedEquationEquiv base platform left right) :
    QuoteHeaded left ↔ QuoteHeaded right :=
  sortedEquationEquiv_invariant (quoteHeaded_respects base) equivalent

/-! ## And the frame of the disciplined logic carries it

The two statements above are about the equation theories.  Here is the same
separation one layer up, where it decides what a formula can say: the predicate
is a member of the frame the disciplined generated logic selects, and is not a
member of the frame the permissive one selects. -/

open Mettapedia.OSLF.Framework.SortedEquationFrame
open Mettapedia.OSLF.Formula

/-- **It is a predicate of the disciplined generated logic.** -/
theorem quoteHeaded_mem_sortedFrame (relEnv : RelationEnv) :
    (sortedEquationFrameUsing relEnv platform).Mem QuoteHeaded :=
  fun _ _ equivalent =>
    quoteHeaded_sortedEquationInvariant (engineBasePremises relEnv) equivalent

/-- **And it is not a predicate of the permissive one.**  The frame is the thing
that changed; the presentation, the equation and the formula language are the
same. -/
theorem quoteHeaded_not_mem_frame (relEnv : RelationEnv) :
    ¬ (equationFrameUsing relEnv platform).Mem QuoteHeaded := by
  intro member
  refine no_quote_separating_invariant [2] relEnv
    ⟨fun term => ¬ QuoteHeaded term, ?_, stop_not_quoteHeaded, ?_⟩
  · exact fun _ _ equivalent => not_congr (member equivalent)
  · intro inner refutes
    exact refutes ⟨inner, rfl⟩

/-- **The separation, in one statement.** -/
theorem frames_separate (relEnv : RelationEnv) :
    (sortedEquationFrameUsing relEnv platform).Mem QuoteHeaded ∧
      ¬ (equationFrameUsing relEnv platform).Mem QuoteHeaded :=
  ⟨quoteHeaded_mem_sortedFrame relEnv, quoteHeaded_not_mem_frame relEnv⟩

/-! ## And a scope statement that was empty becomes a statement

`SourceGenerator.sourceScope_is_quote_setoid` says everything the source's scope
contains is a quote up to the frame's own equivalence.  Read at the permissive
theory of this presentation that says nothing, because every term whatsoever is
such a quote.  Read at the disciplined one it is a genuine bound, and it refutes
membership -- which is the negative this tree has been proving in the ambient
powerset for want of anywhere better to put it. -/

open Mettapedia.OSLF.Framework.SourceGenerator

/-- **The terminated process is not in the disciplined reading of the source's
scope**, whatever the two part predicates are.  Everything in the scope is
disciplined-equivalent to a quote, the disciplined theory keeps quotes apart
from processes, and the terminated process is a process. -/
theorem stop_not_in_sortedScope (relEnv : RelationEnv)
    (I : SortedEquationAtomSemUsing relEnv platform)
    (leftAtom rightAtom : String) :
    ¬ langSortedSemUsing relEnv platform I
        (sourceScope quoteLabel dropLabel leftAtom rightAtom) stop := by
  intro holds
  obtain ⟨inner, equivalent⟩ :=
    sourceScope_is_quote_setoid (langSortedGSLTUsing relEnv platform).equations
      (langSortedSemanticReducesUsing relEnv platform) (fun atom => (I atom).1)
      quoteLabel dropLabel leftAtom rightAtom holds
  exact stop_not_quoteHeaded
    ((quoteHeaded_sortedEquationInvariant (engineBasePremises relEnv) equivalent).mpr
      ⟨inner, rfl⟩)

/-- **And the same argument is unavailable in the permissive reading**, because
the bound it rests on holds of everything there. -/
theorem permissive_bound_refutes_nothing (relEnv : RelationEnv) (term : Pattern) :
    ∃ inner, (langGSLTUsing relEnv platform).Equiv term (.apply quoteLabel [inner]) :=
  permissive_quote_predicate_is_trivial [2] relEnv term

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformEquationDiscipline
