import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingSpines
import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingConversionJudgments

/-!
# Constructor congruence uses shared conversion reads

Each declared argument contributes one conversion premise at its binder's
sort. The two argument tuples are checked against the actual constructor
binders. This includes the bound-variable restriction, without adding the
independence conditions of theorem substitution.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open MM0ContextualSupport

def congruencePremises (width : Nat) : Nat → Nat → Context → List Pat
  | _, _, [] => []
  | leftIndex, rightIndex, binder :: binders =>
      conversionPattern width binder.sort (.var leftIndex) (.var rightIndex) ::
        congruencePremises width (leftIndex + 1) (rightIndex + 1) binders

def conversionValues (target : Context) : List Preterm → List Preterm → Context → List Tm
  | left :: lefts, right :: rights, binder :: binders =>
      conversionValue target binder.sort left right :: conversionValues target lefts rights binders
  | _, _, _ => []

theorem congruencePremises_bounded (width bound : Nat) (binders : Context) (leftIndex rightIndex : Nat)
    (leftBounded : leftIndex + binders.length ≤ bound) (rightBounded : rightIndex + binders.length ≤ bound) :
    ∀ pattern ∈ congruencePremises width leftIndex rightIndex binders,
      ∀ index ∈ pattern.vars, index < bound := by
  induction binders generalizing leftIndex rightIndex with
  | nil => simp [congruencePremises]
  | cons binder binders ih =>
      intro pattern member
      rcases List.mem_cons.mp member with rfl | member
      · exact conversionPattern_bounded _ _ _ _ _ (by change leftIndex < bound; simp only [List.length_cons] at leftBounded; omega)
          (by change rightIndex < bound; simp only [List.length_cons] at rightBounded; omega)
      · exact ih (leftIndex + 1) (rightIndex + 1) (by simp only [List.length_cons] at leftBounded; omega)
          (by simp only [List.length_cons] at rightBounded; omega) pattern member

theorem conversionArguments_typed {signature : TermSignature} {definitions : Definition.Signature}
    {target : Context} {left right : List Preterm} {binders : Context}
    (converted : ConvertsArgs signature definitions target left right binders) :
    List.Forall₂ (Preterm.FitsBinder signature target) left binders ∧
      List.Forall₂ (Preterm.FitsBinder signature target) right binders := by
  induction binders generalizing left right with
  | nil => cases converted; exact ⟨.nil, .nil⟩
  | cons binder binders ih =>
      cases converted with
      | cons leftFits rightFits _ tail =>
          obtain ⟨leftRest, rightRest⟩ := ih tail
          exact ⟨.cons leftFits leftRest, .cons rightFits rightRest⟩

theorem congruenceReads_sound {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} (target : Context) (hypotheses values : List Preterm)
    (scopedValues : ∀ value ∈ values, Term.supportedAt target.length (encode target value) = true)
    (binders : Context) (leftIndex rightIndex : Nat) (left right : List Preterm) (selected : List Tm)
    (leftTyped : List.Forall₂ (Preterm.FitsBinder signature target) left binders)
    (rightTyped : List.Forall₂ (Preterm.FitsBinder signature target) right binders)
    (leftSlots : List.Forall₂ (Preterm.Substitutes (Substitution.ofList values)) (argumentSpine leftIndex binders.length) left)
    (rightSlots : List.Forall₂ (Preterm.Substitutes (Substitution.ofList values)) (argumentSpine rightIndex binders.length) right)
    (matched : List.Forall₂ (ContextualPatterns.layer.Solves (expressionAssignment target values))
      (congruencePremises target.length leftIndex rightIndex binders) selected)
    (valid : ∀ value ∈ selected, ValidValue signature definitions theorems target hypotheses value) :
    ConvertsArgs signature definitions target left right binders := by
  induction binders generalizing leftIndex rightIndex left right selected with
  | nil => cases leftTyped; cases rightTyped; exact .nil
  | cons binder binders ih =>
      cases leftTyped with
      | cons leftFits leftRest =>
        cases rightTyped with
        | cons rightFits rightRest =>
          simp only [List.length_cons, argumentSpine_cons] at leftSlots rightSlots
          cases leftSlots with
          | cons leftSub leftSubs =>
            cases rightSlots with
            | cons rightSub rightSubs =>
              cases matched with
              | cons head tail =>
                rename_i left lefts right rights value rest
                have same := (matches_conversionPattern_iff target values scopedValues binder.sort leftSub rightSub value).mp head
                have conversion := (valid value (by simp)).2 binder.sort left right same
                exact .cons leftFits rightFits conversion
                  (ih (leftIndex + 1) (rightIndex + 1) lefts rights rest leftRest rightRest leftSubs rightSubs tail
                    (fun term member => valid term (by simp [member])))

theorem congruenceReads_complete {signature : TermSignature} {definitions : Definition.Signature}
    (target : Context) (values : List Preterm)
    (scopedValues : ∀ value ∈ values, Term.supportedAt target.length (encode target value) = true)
    (binders : Context) (leftIndex rightIndex : Nat) (left right : List Preterm)
    (converted : ConvertsArgs signature definitions target left right binders)
    (leftSlots : List.Forall₂ (Preterm.Substitutes (Substitution.ofList values)) (argumentSpine leftIndex binders.length) left)
    (rightSlots : List.Forall₂ (Preterm.Substitutes (Substitution.ofList values)) (argumentSpine rightIndex binders.length) right) :
    List.Forall₂ (ContextualPatterns.layer.Solves (expressionAssignment target values))
      (congruencePremises target.length leftIndex rightIndex binders) (conversionValues target left right binders) := by
  induction binders generalizing leftIndex rightIndex left right with
  | nil => cases converted; exact .nil
  | cons binder binders ih =>
      cases converted with
      | cons leftFits rightFits child tail =>
        simp only [List.length_cons, argumentSpine_cons] at leftSlots rightSlots
        cases leftSlots with
        | cons leftSub leftSubs =>
          cases rightSlots with
          | cons rightSub rightSubs =>
            exact .cons ((matches_conversionPattern_iff target values scopedValues binder.sort leftSub rightSub _).mpr rfl)
              (ih (leftIndex + 1) (rightIndex + 1) _ _ tail leftSubs rightSubs)

def congruenceCheck (signature : TermSignature) (target : Context) (declaration : TermDecl) (values : List Preterm) : Bool :=
  Substitution.checkArguments signature target (values.take declaration.arguments.length) declaration.arguments &&
    Substitution.checkArguments signature target (values.drop declaration.arguments.length) declaration.arguments

theorem congruenceCheck_iff (signature : TermSignature) (target : Context) (declaration : TermDecl) (values : List Preterm) :
    congruenceCheck signature target declaration values = true ↔
      List.Forall₂ (Preterm.FitsBinder signature target) (values.take declaration.arguments.length) declaration.arguments ∧
      List.Forall₂ (Preterm.FitsBinder signature target) (values.drop declaration.arguments.length) declaration.arguments := by
  simp [congruenceCheck, Substitution.checkArguments_iff]

def congruenceRule (signature : TermSignature) (target : Context) (name : String)
    (symbol : Nat) (declaration : TermDecl) : Rule Nat Tm Pat :=
  guardedArgumentRule target (declaration.arguments.length + declaration.arguments.length) name
    (congruenceCheck signature target declaration)
    (congruencePremises target.length 0 declaration.arguments.length declaration.arguments)
    (conversionPattern target.length declaration.resultSort
      (Preterm.applyArgs (.term symbol) (argumentSpine 0 declaration.arguments.length))
      (Preterm.applyArgs (.term symbol) (argumentSpine declaration.arguments.length declaration.arguments.length)))

theorem congruenceRule_preserves {sorts : SortSignature} {signature : TermSignature}
    {definitions : Definition.Signature} {theorems : TheoremSignature} {target : Context}
    {hypotheses : List Preterm} (formed : Context.WellFormed sorts target) (name : String)
    {symbol : Nat} {declaration : TermDecl} (known : signature symbol = some declaration)
    {before after : Multiset Tm}
    (valid : ∀ value ∈ before, ValidValue signature definitions theorems target hypotheses value)
    (step : Step ContextualPatterns.layer (congruenceRule signature target name symbol declaration) before after) :
    ∀ value ∈ after, ValidValue signature definitions theorems target hypotheses value := by
  apply guardedArgumentRule_preserves target _ name _ _ _
    (congruencePremises_bounded _ _ _ _ _ (by omega) (by omega))
    (conversionPattern_bounded _ _ _ _ _ (constructorSpine_bounded _ _ _ _ (by omega))
      (constructorSpine_bounded _ _ _ _ (by omega))) _ _ valid step
  intro values selected result _ checked matched validSelected output
  obtain ⟨leftTyped, rightTyped⟩ := (congruenceCheck_iff _ _ _ _).mp checked
  let left := values.take declaration.arguments.length
  let right := values.drop declaration.arguments.length
  have valuesSame : values = left ++ right := (List.take_append_drop _ _).symm
  have leftCount : left.length = declaration.arguments.length := leftTyped.length_eq
  have rightCount : right.length = declaration.arguments.length := rightTyped.length_eq
  have scopedValues := fitted_arguments_supported formed (List.rel_append leftTyped rightTyped)
  change (∀ argument ∈ left ++ right, Term.supportedAt target.length (encode target argument) = true) at scopedValues
  rw [← valuesSame] at scopedValues
  have leftSlots : List.Forall₂ (Preterm.Substitutes (Substitution.ofList values))
      (argumentSpine 0 declaration.arguments.length) left := by
    rw [valuesSame, ← leftCount]
    exact argumentSpine_substituted [] left right
  have rightSlots : List.Forall₂ (Preterm.Substitutes (Substitution.ofList values))
      (argumentSpine declaration.arguments.length declaration.arguments.length) right := by
    rw [valuesSame]
    simpa [leftCount, rightCount] using argumentSpine_substituted left right []
  have converted := congruenceReads_sound target hypotheses values scopedValues declaration.arguments 0
    declaration.arguments.length left right selected leftTyped rightTyped leftSlots rightSlots matched validSelected
  have produced := conversionPattern_instantiated target values scopedValues declaration.resultSort
    (Preterm.Substitutes.applyArgs _ _ _ _ _ (.term symbol) leftSlots)
    (Preterm.Substitutes.applyArgs _ _ _ _ _ (.term symbol) rightSlots)
  have same : conversionValue target declaration.resultSort (Preterm.applyArgs (.term symbol) left)
      (Preterm.applyArgs (.term symbol) right) = result := Option.some.inj (produced.symm.trans output)
  subst result
  exact valid_conversion (.congruence known converted)

theorem congruenceRule_complete {sorts : SortSignature} {signature : TermSignature}
    {definitions : Definition.Signature} {target : Context} (formed : Context.WellFormed sorts target)
    (name : String) (symbol : Nat) (declaration : TermDecl) (left right : List Preterm)
    (converted : ConvertsArgs signature definitions target left right declaration.arguments)
    (state : Multiset Tm) (present : ∀ value ∈ conversionValues target left right declaration.arguments, value ∈ state) :
    Step ContextualPatterns.layer (congruenceRule signature target name symbol declaration)
      ({requestValue name ((left ++ right).map (encode target))} + state)
      (state + {conversionValue target declaration.resultSort
        (Preterm.applyArgs (.term symbol) left) (Preterm.applyArgs (.term symbol) right)}) := by
  obtain ⟨leftTyped, rightTyped⟩ := conversionArguments_typed converted
  have leftCount := leftTyped.length_eq
  have rightCount := rightTyped.length_eq
  have count : (left ++ right).length = declaration.arguments.length + declaration.arguments.length := by
    simp [leftCount, rightCount]
  have checked : congruenceCheck signature target declaration (left ++ right) = true := by
    apply (congruenceCheck_iff _ _ _ _).mpr
    simpa [← leftCount] using And.intro leftTyped rightTyped
  have scopedValues := fitted_arguments_supported formed (List.rel_append leftTyped rightTyped)
  have leftSlots : List.Forall₂ (Preterm.Substitutes (Substitution.ofList (left ++ right)))
      (argumentSpine 0 declaration.arguments.length) left := by
    rw [← leftCount]
    exact argumentSpine_substituted [] left right
  have rightSlots : List.Forall₂ (Preterm.Substitutes (Substitution.ofList (left ++ right)))
      (argumentSpine declaration.arguments.length declaration.arguments.length) right := by
    simpa [leftCount, rightCount] using argumentSpine_substituted left right []
  apply guardedArgumentRule_complete target _ name _ _ _ count checked scopedValues
    (conversionValues target left right declaration.arguments) _ state
  · exact congruenceReads_complete target (left ++ right) scopedValues declaration.arguments 0
      declaration.arguments.length left right converted leftSlots rightSlots
  · exact present
  · exact conversionPattern_instantiated target (left ++ right) scopedValues declaration.resultSort
      (Preterm.Substitutes.applyArgs _ _ _ _ _ (.term symbol) leftSlots)
      (Preterm.Substitutes.applyArgs _ _ _ _ _ (.term symbol) rightSlots)

theorem congruencePremises_input (width : Nat) (binders : Context) (leftIndex rightIndex : Nat) :
    ∀ pattern ∈ congruencePremises width leftIndex rightIndex binders, pattern.Input := by
  induction binders generalizing leftIndex rightIndex with
  | nil => simp [congruencePremises]
  | cons binder binders ih =>
      intro pattern member
      rcases List.mem_cons.mp member with rfl | member
      · exact judgmentPattern_input _ _ _
      · exact ih _ _ pattern member

theorem congruenceRule_input (signature : TermSignature) (target : Context) (name : String)
    (symbol : Nat) (declaration : TermDecl) :
    ContextualPatterns.RuleInput (congruenceRule signature target name symbol declaration) := by
  constructor
  · intro pattern member
    simp only [congruenceRule, guardedArgumentRule, requestRule, List.singleton_append, List.mem_cons] at member
    rcases member with rfl | member
    · exact judgmentPattern_input _ _ _
    · exact congruencePremises_input _ _ _ _ pattern member
  · intro check member
    simp only [congruenceRule, guardedArgumentRule, requestRule, List.mem_singleton] at member
    subst check
    exact judgmentPattern_input _ _ _

end Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting
