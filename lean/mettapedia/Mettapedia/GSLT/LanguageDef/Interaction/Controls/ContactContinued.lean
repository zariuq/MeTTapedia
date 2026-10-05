import Mettapedia.GSLT.LanguageDef.ContinuedCategory
import Mettapedia.GSLT.LanguageDef.CanonicalConstructorSupport
import Mettapedia.GSLT.LanguageDef.Continued.Forget
import Mettapedia.GSLT.LanguageDef.Interaction.Controls.ContactMorphisms

/-!
# The law-free contact theory is continued, and its key-collapsing map does not lift

The law-free contact theory carries the whole structure of a continued
interactive GSLT: its rule is an interaction cut between an input prefix and
an output prefix, equality is a section of its static equivalence, and its
contractum stays sorted when the two continuations are wrapped.

The morphism of iGSLTs that sends the constant `B` to the constant `A` goes
from this theory to itself.  It has no lift to a morphism of continued
theories: a lift would be injective on canonical keys, and `A` and `B` are
two canonical keys with one image.  The forgetful functor is therefore not
full, whether morphisms are taken as defined or up to their underlying
theory map.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.GSLT.LanguageDef.ContinuationRetypingPlan
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-! ## The cut -/

/-- The input prefix constructor. -/
def inputConstructor : DeclaredConstructor barePresentation.presentation :=
  ⟨terms[5], List.getElem_mem (by decide)⟩

/-- The output prefix constructor. -/
def outputConstructor : DeclaredConstructor barePresentation.presentation :=
  ⟨terms[6], List.getElem_mem (by decide)⟩

/-- The program side: an input prefix, its body the continuation. -/
def inputOperand : InteractionOperandProfile barePresentation where
  constructor := inputConstructor
  schemaTerm := .apply "In" [.fvar "x"]
  continuation :=
    { index := 0
      inBounds := by decide
      hasInteractingResult := by rfl }
  continuationPattern := .fvar "x"
  continuationVariable := .plain "x"
  subject := .absent
  form := .introduced (by
      simp [RepresentedBy, UsesBareCollection, inputConstructor, terms])
    (by rfl)

/-- The environment side: an output prefix, its body the continuation. -/
def outputOperand : InteractionOperandProfile barePresentation where
  constructor := outputConstructor
  schemaTerm := .apply "Out" [.fvar "y"]
  continuation :=
    { index := 0
      inBounds := by decide
      hasInteractingResult := by rfl }
  continuationPattern := .fvar "y"
  continuationVariable := .plain "y"
  subject := .absent
  form := .introduced (by
      simp [RepresentedBy, UsesBareCollection, outputConstructor, terms])
    (by rfl)

/-- The contact itself is the ordered core. -/
def bareCoreContact : CoreContactPresentation barePresentation.presentation where
  sort := barePresentation.interactingSort
  constructor := barePresentation.contactConstructor
  representation := .binary
  representsCore := by rfl

/-- The contact rule as an interaction cut. -/
def bareCut : InteractionCutPresentation bare where
  program := inputOperand
  environment := outputOperand
  coreContact := bareCoreContact
  programPlacement := .introduced rfl (by
      intro equality
      have labels := congrArg (fun constructor => constructor.1.label) equality
      change "In" = "Join" at labels
      exact (by decide : ("In" : String) ≠ "Join") labels)
  environmentPlacement := .introduced rfl (by
      intro equality
      have labels := congrArg (fun constructor => constructor.1.label) equality
      change "Out" = "Join" at labels
      exact (by decide : ("Out" : String) ≠ "Join") labels)
  sourceShape :=
    { core := syncRule.left
      coreShape :=
        (CutSourceShape.binary rfl :
          CutSourceShape bareCoreContact inputOperand.schemaTerm outputOperand.schemaTerm
            (.apply bareCoreContact.constructor.1.label
              [inputOperand.schemaTerm, outputOperand.schemaTerm]))
      envelope := .hole
      fillsSource := rfl }
  sourceEnvelopeInSignature := .hole "Proc"
  interactionPremisesEmpty := rfl
  residual := .constructor barePresentation.contactConstructor (by
    change RepresentedBy barePresentation.contactConstructor.1 syncRule.right
    refine ⟨?_, rfl, rfl⟩
    rintro ⟨parameterName, collectionType, elementType, shape⟩
    cases shape)
  subjectsAgree := .structural rfl (by
    intro equation membership
    cases membership)

/-! ## The section -/

/-- With no law, equality is the section on every open fibre. -/
def bareContextualOpenSection :
    ComputableReflectiveFiberContextualSection bare
      (ReflectionExtension.emptyAdmitted (contactWith [])) where
  normalize := id
  equivalent := fun term => Relation.EqvGen.refl term
  complete := by
    intro free bound sort left right equivalent
    apply Subtype.ext
    exact
      (ReflectiveEquationSemantics.equationEquiv_iff_eq_of_no_generators
        (profile := .empty) (base := defaultBasePremises)
        (language := contactWith []) (by rfl) (by decide) left.1 right.1).mp
        (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid_to_equiv
          equivalent)
  preservesFreeVariableSupport := by
    intro free bound sort term name membership
    exact membership
  normalizeRecontextualizeFree := by
    intro sourceFree targetFree bound sort term preserves
    rfl
  preservesReflectiveSupport := by
    intro free bound sort term support available binderImage supported
    exact supported

/-! ## Wrappability -/

/-- The contact is neither of the two introductions. -/
theorem contact_mem_continuationConstructors :
    barePresentation.contactConstructor ∈ continuationConstructors bareCut := by
  apply (mem_continuationConstructors_iff bareCut barePresentation.contactConstructor).2
  constructor
  · intro equality
    have labels := congrArg (fun constructor => constructor.1.label) equality
    exact absurd labels (by decide : ("Join" : String) ≠ "In")
  · intro equality
    have labels := congrArg (fun constructor => constructor.1.label) equality
    exact absurd labels (by decide : ("Join" : String) ≠ "Out")

/-- The contractum is the contact, which is not one of the two
introductions. -/
theorem bareContinuationRetyping : ContinuationRetypingPlan bareCut :=
  ⟨contact_mem_continuationConstructors⟩

theorem bareContextualOpenSection_preservesWrappedConstructorTyping :
    bareContextualOpenSection.PreservesTypedConstructors
      (· ∈ bareContinuationRetyping.wrappedLabels) := by
  apply ComputableReflectiveFiberContextualSection.preservesTypedConstructors_id
    bareContextualOpenSection
  intro free bound sort term
  rfl

/-- The theory has no bare collection constructor. -/
theorem bareBareCollectionConstructorsWrapped :
    ∀ rule ∈ (contactWith []).terms,
      UsesBareCollection rule →
        rule.label ∈ bareContinuationRetyping.wrappedLabels := by
  intro rule membership bare
  change rule ∈ terms at membership
  simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [UsesBareCollection] at bare

@[simp]
theorem bare_costBaseJoin_params :
    (costBaseConstructor bareCut terms[7]).params =
      [.simple "left" (.base (costBaseSortName "Proc")),
        .simple "right" (.base (costBaseSortName "Proc"))] := by
  decide +kernel

@[simp]
theorem bare_costBaseIn_params :
    (costBaseConstructor bareCut terms[5]).params =
      [.simple "body" (.base costWrappedSortName)] := by
  decide +kernel

@[simp]
theorem bare_costBaseOut_params :
    (costBaseConstructor bareCut terms[6]).params =
      [.simple "body" (.base costWrappedSortName)] := by
  decide +kernel

/-- The contact rule's left side stays sorted when the two prefix bodies
are moved to the wrapped fibre. -/
theorem bareContinuationRetyping_redexRetypable :
    bareContinuationRetyping.RedexRetypable := by
  rw [ContinuationRetypingPlan.redexRetypable_def]
  change HasType bareContinuationRetyping.generatedLanguage
    bareContinuationRetyping.generatedFreeContext []
    (.apply (costBaseConstructorName "Join")
      [.apply (costBaseConstructorName "In") [.fvar "x"],
        .apply (costBaseConstructorName "Out") [.fvar "y"]])
    (.base (costBaseSortName "Proc"))
  apply HasType.constructor (rule := costBaseConstructor bareCut terms[7])
  · exact bareContinuationRetyping.costBaseConstructor_mem_generated terms[7]
      (List.getElem_mem (by decide))
  · simp [UsesBareCollection, bare_costBaseJoin_params]
  · rw [bare_costBaseJoin_params]
    apply ArgumentsHaveTypes.cons
    · trivial
    · rfl
    · apply HasType.constructor (rule := costBaseConstructor bareCut terms[5])
      · exact bareContinuationRetyping.costBaseConstructor_mem_generated terms[5]
          (List.getElem_mem (by decide))
      · simp [UsesBareCollection, bare_costBaseIn_params]
      · rw [bare_costBaseIn_params]
        exact .cons trivial rfl (HasType.fvar rfl) .nil
    · apply ArgumentsHaveTypes.cons
      · trivial
      · rfl
      · apply HasType.constructor (rule := costBaseConstructor bareCut terms[6])
        · exact bareContinuationRetyping.costBaseConstructor_mem_generated terms[6]
            (List.getElem_mem (by decide))
        · simp [UsesBareCollection, bare_costBaseOut_params]
        · rw [bare_costBaseOut_params]
          exact .cons trivial rfl (HasType.fvar rfl) .nil
      · exact .nil

/-- The contractum, the contact of the two continuations, has the wrapped
sort. -/
theorem bareContinuationRetyping_wrappable :
    bareContinuationRetyping.Wrappable := by
  rw [ContinuationRetypingPlan.wrappable_def]
  have wrapped : "Join" ∈ bareContinuationRetyping.wrappedLabels := by
    decide +kernel
  have translated :
      bareContinuationRetyping.mapContractum syncRule.right =
        .apply (costWrappedConstructorName "Join") [.fvar "x", .fvar "y"] := by
    simp [syncRule, join, mapContractum_apply, mapContractum_fvar, wrapped]
  change HasType bareContinuationRetyping.generatedLanguage
    bareContinuationRetyping.generatedFreeContext []
    (bareContinuationRetyping.mapContractum syncRule.right) (.base costWrappedSortName)
  rw [translated]
  have typed := HasType.constructor
    (language := bareContinuationRetyping.generatedLanguage)
    (free := bareContinuationRetyping.generatedFreeContext) (bound := [])
    (rule := costWrappedConstructor (theory := bare) terms[7])
    (arguments := [.fvar "x", .fvar "y"])
    (bareContinuationRetyping.costWrappedConstructor_mem_generated
      barePresentation.contactConstructor contact_mem_continuationConstructors)
    (by simp [UsesBareCollection, costWrappedConstructor, terms, mapParameterType,
      costWrappedTypeExpr])
    (by
      change ArgumentsHaveTypes _ _ [] [.fvar "x", .fvar "y"]
        [.simple "left" (.base costWrappedSortName),
          .simple "right" (.base costWrappedSortName)]
      exact .cons trivial rfl (HasType.fvar rfl)
        (.cons trivial rfl (HasType.fvar rfl) .nil))
  exact typed

theorem bareContinuationRetyping_equationsRetypable :
    EquationsRetypable bareContinuationRetyping := by
  intro equation membership
  cases membership

theorem bareContinuationRetyping_reflectivePresentationsRetypable :
    ReflectivePresentationsRetypable bareContinuationRetyping .empty := by
  intro declaration membership
  simp at membership

/-- **The law-free contact theory is a continued interactive GSLT.** -/
def bareContinued : CIGSLT where
  theory := bare
  reflection := ReflectionExtension.emptyAdmitted (contactWith [])
  cut := bareCut
  openCanonical := bareContextualOpenSection
  continuationRetyping := bareContinuationRetyping
  bareCollectionConstructorsWrapped := bareBareCollectionConstructorsWrapped
  openCanonicalPreservesWrappedConstructorTyping :=
    bareContextualOpenSection_preservesWrappedConstructorTyping
  equationsRetypable := bareContinuationRetyping_equationsRetypable
  reflectivePresentationsRetypable :=
    bareContinuationRetyping_reflectivePresentationsRetypable
  sourceEnvelopeStable := .hole "Proc"
  redexRetypable := bareContinuationRetyping_redexRetypable
  wrappable := bareContinuationRetyping_wrappable

/-- Its underlying iGSLT is the law-free contact theory. -/
theorem bareContinued_forget : CIGSLT.forget.obj bareContinued = bare :=
  rfl

end Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact
