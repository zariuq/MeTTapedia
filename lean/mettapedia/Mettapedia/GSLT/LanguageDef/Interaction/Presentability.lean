import Mettapedia.GSLT.LanguageDef.SemanticCategory

/-!
# Which language definitions admit an interactive presentation

An interactive presentation selects a sort, a contact constructor whose
operands and result all have that sort, and a rewrite whose left side is
headed by that constructor.  This module turns those three requirements into
criteria on the authored declarations alone, so that a language can be shown
to admit a presentation, or to admit none, without inspecting its behaviour.

The negative criteria separate two ways of failing.  A language may author no
rewrite at all, so that nothing can be selected.  Or every rewrite may be
headed by a constructor that brings operands of different sorts together: the
ordered contact is there, and the same-sort requirement is what fails.

The selected rewrite of a presentation may carry a reduction hypothesis.  An
interactive theory asks for more: the selected rewrite is a base rule.  The
difference is not cosmetic, since a theory all of whose rules ask for a
reduction of a subterm has no reduction at all.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open StructuralMorphism

/-- A language definition admits an interactive presentation when some
validated interactive presentation retains exactly that definition. -/
def AdmitsInteractivePresentation (language : LanguageDef) : Prop :=
  ∃ presentation : InteractivePresentation,
    presentation.presentation.language = language

/-- Premise evidence for a list containing a premise that asks for a
reduction contains a reduction at the same depth. -/
theorem exists_stepAt_of_premisesAt
    {base : BasePremiseEvaluator} {lang : LanguageDef} {fuel : Nat} :
    ∀ (premises : List Premise) (initial final : Mettapedia.OSLF.MeTTaIL.Match.Bindings),
      PremisesAt base lang fuel initial premises final →
      ∀ premise ∈ premises, asksReduction premise = true →
        ∃ source target, StepAt base lang fuel source target
  | [], _, _, _, _, membership, _ => by cases membership
  | head :: tail, _, _, evidence, premise, membership, asks => by
      cases evidence with
      | cons first rest =>
          rcases List.mem_cons.mp membership with rfl | inTail
          · cases first with
            | congruence step _ _ => exact ⟨_, _, step⟩
            | scopedRoot _ step _ _ => exact ⟨_, _, step⟩
            | freshness _ => simp [asksReduction] at asks
            | relationQuery _ => simp [asksReduction] at asks
            | forAll _ => simp [asksReduction] at asks
          · exact exists_stepAt_of_premisesAt tail _ _ rest premise inTail asks

/-- A theory all of whose rewrites ask for a reduction of a subterm has no
derivation of any depth: each rule defers to a strictly smaller one. -/
theorem not_stepAt_of_rewrites_ask_reduction
    {base : BasePremiseEvaluator} {lang : LanguageDef}
    (ask : ∀ rule ∈ lang.rewrites, ∃ premise ∈ rule.premises,
      asksReduction premise = true) :
    ∀ (fuel : Nat) (source target : Pattern), ¬ StepAt base lang fuel source target
  | 0, _, _, step => by cases step
  | fuel + 1, _, _, step => by
      cases step with
      | rule ruleMember _ premises _ =>
          obtain ⟨premise, membership, asks⟩ := ask _ ruleMember
          obtain ⟨inner, innerTarget, innerStep⟩ :=
            exists_stepAt_of_premisesAt _ _ _ premises premise membership asks
          exact not_stepAt_of_rewrites_ask_reduction ask fuel inner innerTarget innerStep

/-- A theory with no rule free of such a premise has no reduction. -/
theorem not_step_of_rewrites_ask_reduction
    {base : BasePremiseEvaluator} {lang : LanguageDef}
    (ask : ∀ rule ∈ lang.rewrites, ∃ premise ∈ rule.premises,
      asksReduction premise = true)
    (source target : Pattern) : ¬ Step base lang source target := by
  rintro ⟨fuel, step⟩
  exact not_stepAt_of_rewrites_ask_reduction ask fuel source target step

/-- A theory that reduces at all has a rule none of whose premises asks for a
reduction. -/
theorem exists_rewrite_asking_nothing_of_step
    {base : BasePremiseEvaluator} {lang : LanguageDef} {source target : Pattern}
    (step : Step base lang source target) :
    ∃ rule ∈ lang.rewrites, ∀ premise ∈ rule.premises, asksReduction premise = false := by
  by_contra none
  apply not_step_of_rewrites_ask_reduction (base := base) (lang := lang) _ source target step
  intro rule membership
  by_contra noPremise
  apply none
  refine ⟨rule, membership, ?_⟩
  intro premise premiseMember
  by_contra asks
  exact noPremise ⟨premise, premiseMember, by simpa using asks⟩

namespace InteractivePresentation

/-- The contact constructor has its selected sort as category. -/
theorem contactConstructor_category (presentation : InteractivePresentation) :
    presentation.contactConstructor.1.category =
      presentation.interactingSort.1.name := by
  have represents := presentation.representsContact
  unfold contactRepresentation? at represents
  by_cases category :
      presentation.contactConstructor.1.category =
        presentation.interactingSort.1.name
  · exact category
  · simp [category] at represents

end InteractivePresentation

/-- Any presentation exposes its language as one admitting a presentation. -/
theorem InteractivePresentation.admits (presentation : InteractivePresentation) :
    AdmitsInteractivePresentation presentation.presentation.language :=
  ⟨presentation, rfl⟩

/-- An authored language is interactive when it has an interacting sort, a
same-sort contact on it, and a base rewrite headed by that contact. -/
def IsInteractive (language : LanguageDef) : Prop :=
  ∃ presentation : InteractivePresentation,
    presentation.presentation.language = language ∧ presentation.BaseInteraction

/-- A presentation with a base interaction exhibits its language as
interactive. -/
theorem InteractivePresentation.isInteractive
    (presentation : InteractivePresentation) (base : presentation.BaseInteraction) :
    IsInteractive presentation.presentation.language :=
  ⟨presentation, rfl, base⟩

/-- Every iGSLT carries the base interaction required of its authored language. -/
theorem IGSLT.isInteractive (theory : IGSLT) :
    IsInteractive theory.presentation.presentation.language :=
  theory.presentation.isInteractive theory.baseInteraction

/-- An interactive language admits an interactive presentation. -/
theorem IsInteractive.admits {language : LanguageDef}
    (interactive : IsInteractive language) : AdmitsInteractivePresentation language := by
  obtain ⟨presentation, exact, -⟩ := interactive
  exact ⟨presentation, exact⟩

/-- A language none of whose rewrites is a base rewrite is not interactive,
whatever it selects. -/
theorem not_isInteractive_of_no_baseRewrite {language : LanguageDef}
    (noBase : ∀ rewrite ∈ language.rewrites, ¬ IsBaseRewrite rewrite) :
    ¬ IsInteractive language := by
  rintro ⟨presentation, rfl, base⟩
  exact noBase presentation.interactionRewrite.1 presentation.interactionRewrite.2 base

/-- A language with no rewrite has nothing to select as its interaction rule. -/
theorem not_admitsInteractivePresentation_of_rewrites_eq_nil
    {language : LanguageDef} (noRewrites : language.rewrites = []) :
    ¬ AdmitsInteractivePresentation language := by
  rintro ⟨presentation, rfl⟩
  obtain ⟨rewrite, membership⟩ := presentation.interactionRewrite
  rw [noRewrites] at membership
  cases membership

/-- The exact obstruction: no declared sort, constructor and rewrite satisfy
the same-sort contact requirement and the heading requirement together. -/
theorem not_admitsInteractivePresentation_iff (language : LanguageDef) :
    ¬ AdmitsInteractivePresentation language ↔
      language.validate = [] →
        ∀ sort : TypeDecl, List.Mem sort language.types →
          ∀ constructor : GrammarRule, List.Mem constructor language.terms →
            ∀ rewrite : RewriteRule, List.Mem rewrite language.rewrites →
              ∀ representation,
                contactRepresentation? sort constructor = some representation →
                  ¬ InteractionHeaded representation constructor rewrite.left := by
  constructor
  · intro none valid sort sortMember constructor constructorMember rewrite
      rewriteMember representation represents headed
    exact none
      ⟨{ presentation := ⟨language, valid⟩
         interactingSort := ⟨sort, sortMember⟩
         contactConstructor := ⟨constructor, constructorMember⟩
         interactionRewrite := ⟨rewrite, rewriteMember⟩
         contactRepresentation := representation
         representsContact := represents
         interactionHeaded := headed }, rfl⟩
  · rintro obstruction ⟨presentation, rfl⟩
    exact obstruction presentation.presentation.valid
      presentation.interactingSort.1 presentation.interactingSort.2
      presentation.contactConstructor.1 presentation.contactConstructor.2
      presentation.interactionRewrite.1 presentation.interactionRewrite.2
      presentation.contactRepresentation presentation.representsContact
      presentation.interactionHeaded

/-- No same-sort contact representation is ever read from a constructor
whose category differs from the candidate sort. -/
theorem contactRepresentation?_eq_none_of_category_ne
    {sort : TypeDecl} {constructor : GrammarRule}
    (different : constructor.category ≠ sort.name) :
    contactRepresentation? sort constructor = none := by
  simp [contactRepresentation?, different]

/-- A constructor of two plain operands is a same-sort contact only when both
operand sorts are its own category. -/
theorem contactRepresentation?_binary_eq_none
    {sort : TypeDecl} {constructor : GrammarRule}
    {leftName rightName left right : String}
    (parameters : constructor.params =
      [.simple leftName (.base left), .simple rightName (.base right)])
    (heterogeneous : ¬ (left = constructor.category ∧ right = constructor.category)) :
    contactRepresentation? sort constructor = none := by
  unfold contactRepresentation?
  by_cases category : constructor.category = sort.name
  · have notBoth : ¬ (left = sort.name ∧ right = sort.name) := by
      rw [← category]
      exact heterogeneous
    simp [category, parameters, notBoth]
  · simp [category]

/-- A constructor of one plain operand is never a contact. -/
theorem contactRepresentation?_unary_eq_none
    {sort : TypeDecl} {constructor : GrammarRule} {name operand : String}
    (parameters : constructor.params = [.simple name (.base operand)]) :
    contactRepresentation? sort constructor = none := by
  unfold contactRepresentation?
  by_cases category : constructor.category = sort.name <;> simp [category, parameters]

/-- A constructor with no operand is never a contact. -/
theorem contactRepresentation?_nullary_eq_none
    {sort : TypeDecl} {constructor : GrammarRule}
    (parameters : constructor.params = []) :
    contactRepresentation? sort constructor = none := by
  unfold contactRepresentation?
  by_cases category : constructor.category = sort.name <;> simp [category, parameters]

/-- A constructor with three or more operands is never a contact. -/
theorem contactRepresentation?_eq_none_of_three_le
    {sort : TypeDecl} {constructor : GrammarRule}
    (long : 3 ≤ constructor.params.length) :
    contactRepresentation? sort constructor = none := by
  unfold contactRepresentation?
  rcases parameters : constructor.params with
    _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
  · rw [parameters] at long
    simp at long
  · rw [parameters] at long
    simp at long
  · rw [parameters] at long
    simp at long
  · split <;> simp

/-- A signature none of whose constructors brings operands of its own sort
together admits no interactive presentation, whatever its rules are. -/
theorem not_admitsInteractivePresentation_of_no_contact
    {language : LanguageDef}
    (noContact : ∀ constructor ∈ language.terms, ∀ sort : TypeDecl,
      contactRepresentation? sort constructor = none) :
    ¬ AdmitsInteractivePresentation language := by
  rintro ⟨presentation, rfl⟩
  have absent := noContact presentation.contactConstructor.1
    presentation.contactConstructor.2 presentation.interactingSort.1
  have present := presentation.representsContact
  rw [absent] at present
  cases present

/-- Languages whose every rewrite is headed by an ordinary constructor
application admit an interactive presentation only through a constructor of
that label with a same-sort contact representation.  When every such
constructor fails the same-sort requirement at every sort, none exists. -/
theorem not_admitsInteractivePresentation_of_heads
    {language : LanguageDef}
    (headed : ∀ rewrite ∈ language.rewrites,
      ∃ label arguments, rewrite.left = .apply label arguments ∧
        ∀ constructor ∈ language.terms, constructor.label = label →
          ∀ sort : TypeDecl, contactRepresentation? sort constructor = none) :
    ¬ AdmitsInteractivePresentation language := by
  rintro ⟨presentation, rfl⟩
  obtain ⟨label, arguments, left, noContact⟩ :=
    headed presentation.interactionRewrite.1 presentation.interactionRewrite.2
  have interaction := presentation.interactionHeaded
  rw [left] at interaction
  cases representation : presentation.contactRepresentation with
  | binary =>
      rw [representation] at interaction
      match arguments, interaction with
      | [_, _], sameLabel =>
          have absent := noContact presentation.contactConstructor.1
            presentation.contactConstructor.2 sameLabel.symm
            presentation.interactingSort.1
          have present := presentation.representsContact
          rw [absent] at present
          cases present
  | collection collectionType =>
      rw [representation] at interaction
      exact interaction

end Mettapedia.GSLT.LanguageDef
