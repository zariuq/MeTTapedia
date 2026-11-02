import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingSpines
import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingConversionJudgments
import Mettapedia.Logic.TierZero.Adequacy.MM0ContextualDummies

/-!
# MM0 definition unfolding through a guarded rewriting template

The request supplies parameter images followed by fresh dummy images. Native
support masks validate freshness; ordinary data checks validate argument sorts
and the result sort. The conclusion itself is instantiated by the common
contextual graft. No conversion proof object is interpreted.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open MM0ContextualSupport

def dummyImages : List Preterm → Option (List Nat)
  | [] => some []
  | .var index :: rest => (dummyImages rest).map (index :: ·)
  | _ => none

theorem dummyImages_iff (values : List Preterm) (images : List Nat) :
    dummyImages values = some images ↔ values = images.map Preterm.var := by
  induction values generalizing images with
  | nil => cases images <;> simp [dummyImages]
  | cons value values ih =>
      cases value with
      | var index =>
          cases images with
          | nil => simp [dummyImages]
          | cons image images =>
              cases result : dummyImages values <;> simp [dummyImages, result, ← ih]
      | term symbol => cases images <;> simp [dummyImages]
      | app function argument => cases images <;> simp [dummyImages]

def unfoldingCheck (signature : TermSignature) (target : Context) (declaration : TermDecl)
    (body : Definition.Body) (values : List Preterm) : Bool :=
  let arguments := values.take declaration.arguments.length
  match dummyImages (values.drop declaration.arguments.length), body.expression.substitute (Substitution.ofList values) with
  | some images, some result =>
      Substitution.checkArguments signature target arguments declaration.arguments &&
        checkDummiesNative [] target arguments body.dummies images &&
        decide (Preterm.infer signature target result = some ([], declaration.resultSort))
  | _, _ => false

theorem unfoldingCheck_iff (signature : TermSignature) (target : Context) (declaration : TermDecl)
    (body : Definition.Body) (values : List Preterm) :
    unfoldingCheck signature target declaration body values = true ↔
      ∃ arguments images result,
        values = arguments ++ images.map Preterm.var ∧ arguments.length = declaration.arguments.length ∧
        List.Forall₂ (Preterm.FitsBinder signature target) arguments declaration.arguments ∧
        Definition.FreshDummies target arguments body.dummies images ∧
        Preterm.Substitutes (Substitution.ofList values) body.expression result ∧
        Preterm.HasType signature target result [] declaration.resultSort := by
  constructor
  · intro checked
    cases found : dummyImages (values.drop declaration.arguments.length) with
    | none => simp [unfoldingCheck, found] at checked
    | some images =>
      cases instantiated : body.expression.substitute (Substitution.ofList values) with
      | none => simp [unfoldingCheck, instantiated] at checked
      | some result =>
        have facts : Substitution.checkArguments signature target (values.take declaration.arguments.length) declaration.arguments = true ∧
            checkDummiesNative [] target (values.take declaration.arguments.length) body.dummies images = true ∧
            Preterm.infer signature target result = some ([], declaration.resultSort) := by
          simpa [unfoldingCheck, found, instantiated, and_assoc] using checked
        have typed := (Substitution.checkArguments_iff _ _ _ _).mp facts.1
        have supported := fitted_arguments_have_support typed
        refine ⟨values.take declaration.arguments.length, images, result, ?_, typed.length_eq, typed,
          (checkDummiesNative_iff canonical_nil _ _ _ _ supported).mp facts.2.1,
          Preterm.substitute_sound instantiated, Preterm.infer_sound facts.2.2⟩
        rw [← (dummyImages_iff _ _).mp found, List.take_append_drop]
  · rintro ⟨arguments, images, result, valuesSame, count, typed, fresh, substituted, resultTyped⟩
    have takeSame : values.take declaration.arguments.length = arguments := by
      rw [valuesSame, ← count, List.take_left]
    have dropSame : values.drop declaration.arguments.length = images.map Preterm.var := by
      rw [valuesSame, ← count, List.drop_left]
    have supported := fitted_arguments_have_support typed
    have nativeFresh := (checkDummiesNative_iff canonical_nil _ _ _ _ supported).mpr fresh
    have imagesFound : dummyImages (values.drop declaration.arguments.length) = some images :=
      (dummyImages_iff _ _).mpr dropSame
    simp [unfoldingCheck, takeSame, imagesFound, substituted.eval,
      (Substitution.checkArguments_iff _ _ _ _).mpr typed, nativeFresh, resultTyped.eval]

def unfoldingRule (signature : TermSignature) (target : Context) (name : String)
    (symbol : Nat) (declaration : TermDecl) (body : Definition.Body) : Rule Nat Tm Pat :=
  guardedArgumentRule target (declaration.arguments.length + body.dummies.length) name
    (unfoldingCheck signature target declaration body) []
    (conversionPattern target.length declaration.resultSort
      (Preterm.applyArgs (.term symbol) (argumentSpine 0 declaration.arguments.length)) body.expression)

theorem unfoldingRule_preserves {sorts : SortSignature} {signature : TermSignature}
    {definitions : Definition.Signature} {theorems : TheoremSignature} {target : Context}
    {hypotheses : List Preterm} (formed : Context.WellFormed sorts target) (name : String)
    {symbol : Nat} {declaration : TermDecl} {body : Definition.Body}
    (knownTerm : signature symbol = some declaration) (knownBody : definitions symbol = some body)
    (bounded : body.expression.VarsBelow (declaration.arguments.length + body.dummies.length))
    {before after : Multiset Tm}
    (valid : ∀ value ∈ before, ValidValue signature definitions theorems target hypotheses value)
    (step : Step ContextualPatterns.layer (unfoldingRule signature target name symbol declaration body) before after) :
    ∀ value ∈ after, ValidValue signature definitions theorems target hypotheses value := by
  apply guardedArgumentRule_preserves target _ name _ [] _ (by simp)
    (conversionPattern_bounded _ _ _ _ _ (constructorSpine_bounded _ _ _ _ (by omega)) bounded)
    _ _ valid step
  intro values selected result _ checked _ _ output
  obtain ⟨arguments, images, image, valuesSame, count, typed, fresh, substituted, imageTyped⟩ :=
    (unfoldingCheck_iff _ _ _ _ _).mp checked
  have allTyped : List.Forall₂ (Preterm.FitsBinder signature target) values
      (declaration.arguments ++ body.dummies.map Binder.bound) := by
    rw [valuesSame]
    exact fresh.typed_substitution typed
  have scopedArguments := fitted_arguments_supported formed allTyped
  have leftSubstituted : Preterm.Substitutes (Substitution.ofList values)
      (Preterm.applyArgs (.term symbol) (argumentSpine 0 declaration.arguments.length))
      (Preterm.applyArgs (.term symbol) arguments) := by
    rw [valuesSame, ← count]
    exact constructorSpine_substituted symbol [] arguments (images.map Preterm.var)
  have produced := conversionPattern_instantiated target values scopedArguments declaration.resultSort leftSubstituted substituted
  have same : conversionValue target declaration.resultSort (Preterm.applyArgs (.term symbol) arguments) image = result :=
    Option.some.inj (produced.symm.trans output)
  subst result
  apply valid_conversion
  exact Converts.unfold (images := images) knownTerm
    (Definition.Unfolds.intro knownTerm knownBody typed fresh
      (by simpa [Definition.substitutionValues, ← valuesSame] using substituted)) imageTyped

theorem unfoldingRule_complete {sorts : SortSignature} {signature : TermSignature} {target : Context}
    (formed : Context.WellFormed sorts target) (name : String) (symbol : Nat)
    (declaration : TermDecl) (body : Definition.Body) (arguments : List Preterm) (images : List Nat)
    (result : Preterm)
    (typed : List.Forall₂ (Preterm.FitsBinder signature target) arguments declaration.arguments)
    (fresh : Definition.FreshDummies target arguments body.dummies images)
    (substituted : Preterm.Substitutes (Substitution.ofList (arguments ++ images.map Preterm.var)) body.expression result)
    (resultTyped : Preterm.HasType signature target result [] declaration.resultSort) (state : Multiset Tm) :
    Step ContextualPatterns.layer (unfoldingRule signature target name symbol declaration body)
      ({requestValue name ((arguments ++ images.map Preterm.var).map (encode target))} + state)
      (state + {conversionValue target declaration.resultSort (Preterm.applyArgs (.term symbol) arguments) result}) := by
  have count : (arguments ++ images.map Preterm.var).length = declaration.arguments.length + body.dummies.length := by
    simp [typed.length_eq, fresh.length_eq]
  have checked := (unfoldingCheck_iff signature target declaration body _).mpr
    ⟨arguments, images, result, rfl, typed.length_eq, typed, fresh, substituted, resultTyped⟩
  have scopedArguments := fitted_arguments_supported formed (fresh.typed_substitution typed)
  apply guardedArgumentRule_complete target _ name _ [] _ count checked scopedArguments [] _ state .nil (by simp)
  apply conversionPattern_instantiated target _ scopedArguments declaration.resultSort _ substituted
  rw [← typed.length_eq]
  exact constructorSpine_substituted symbol [] arguments (images.map Preterm.var)

/-- Every independent unfolding, at the installed declaration and body, has
an ordinary guarded rewriting realization. Fresh dummy images remain explicit. -/
theorem independent_unfolding_step {sorts : SortSignature} {signature : TermSignature}
    {definitions : Definition.Signature} {target : Context} (formed : Context.WellFormed sorts target)
    (name : String) {symbol : Nat} {declaration : TermDecl} {body : Definition.Body}
    (knownTerm : signature symbol = some declaration) (knownBody : definitions symbol = some body)
    {arguments : List Preterm} {images : List Nat} {result : Preterm}
    (unfolded : Definition.Unfolds signature definitions target symbol arguments images result)
    (resultTyped : Preterm.HasType signature target result [] declaration.resultSort) (state : Multiset Tm) :
    Step ContextualPatterns.layer (unfoldingRule signature target name symbol declaration body)
      ({requestValue name ((arguments ++ images.map Preterm.var).map (encode target))} + state)
      (state + {conversionValue target declaration.resultSort (Preterm.applyArgs (.term symbol) arguments) result}) := by
  cases unfolded with
  | intro termLookup bodyLookup typed fresh substituted =>
      have sameTerm := Option.some.inj (termLookup.symm.trans knownTerm)
      have sameBody := Option.some.inj (bodyLookup.symm.trans knownBody)
      cases sameTerm
      cases sameBody
      exact unfoldingRule_complete formed name symbol declaration body arguments images result typed fresh substituted resultTyped state

theorem unfoldingRule_input (signature : TermSignature) (target : Context) (name : String)
    (symbol : Nat) (declaration : TermDecl) (body : Definition.Body) :
    ContextualPatterns.RuleInput (unfoldingRule signature target name symbol declaration body) := by
  have requestChecked := (ContextualPatterns.Pattern.inputCheck_iff _).mpr
    (judgmentPattern_input target.length (requestTag name) (formals (declaration.arguments.length + body.dummies.length)))
  apply (ContextualPatterns.ruleInputCheck_iff _).mp
  simpa [ContextualPatterns.ruleInputCheck, unfoldingRule, guardedArgumentRule, requestRule, theoremRequest] using
    And.intro requestChecked requestChecked

end Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting
