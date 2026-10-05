import Mettapedia.Languages.PartrecMachine.UndecidableContinued

/-!
# The interaction cut of the history theory

A continued interactive theory is an interactive theory together with an
ordered cut of its interaction rule, a contractum that is sorted in the
continuation signature derived from that cut, equations that survive the
retyping of continuations, and a contextual section of its static
equivalence.  For the history theory this module supplies every one of these
except the section.

* The interaction rule `Meet(Wait(x), Give(y)) ⟶ Meet(x, y)` is an ordered
  cut.  `Wait` and `Give` are the two introductions, each with one
  continuation; `Meet` is the contact and also the residual constructor; no
  equation mentions the contact, so the two sides agree structurally.
* The continuation signature derived from that cut sorts the retyped redex
  and sorts the contractum at the wrapped sort: the theory is wrappable.
* Every authored equation survives the retyping, in the base fibre and in
  the wrapped fibre.  The equations speak of configurations and of the three
  history constructors that are not prefixes, so neither introduction occurs
  in them.
* No constructor is a bare collection, the cut has no envelope, and no
  admitted reflection profile has a presentation to transport.

`historyContinued` assembles a continued theory over the history theory from
a contextual section that never produces a prefix, so the section is the
only component the history theory can lack.  By the preceding module no
section it carries is effective, and `historyContinued_not_effective` records
that for the assembled theory.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.PartrecMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.GSLT.LanguageDef.ContinuationRetypingPlan

/-! ## The cut -/

/-- The waiting prefix. -/
def waitConstructor : DeclaredConstructor historyValidated :=
  ⟨historyMachine.terms[23], List.getElem_mem (by decide)⟩

/-- The giving prefix. -/
def giveConstructor : DeclaredConstructor historyValidated :=
  ⟨historyMachine.terms[24], List.getElem_mem (by decide)⟩

/-- The waiting side of the interaction: `Wait` introduces it, and the
history under the prefix is its continuation. -/
def historyProgramOperand : InteractionOperandProfile historyPresentation where
  constructor := waitConstructor
  schemaTerm := .apply "Wait" [.fvar "x"]
  continuation :=
    { index := 0
      inBounds := by decide
      hasInteractingResult := by rfl }
  continuationPattern := .fvar "x"
  continuationVariable := .plain "x"
  subject := .absent
  form := .introduced ⟨historyTerms_notBare waitConstructor.2, rfl, rfl⟩ (by rfl)

/-- The giving side of the interaction: `Give` introduces it, and the history
under the prefix is its continuation. -/
def historyEnvironmentOperand : InteractionOperandProfile historyPresentation where
  constructor := giveConstructor
  schemaTerm := .apply "Give" [.fvar "y"]
  continuation :=
    { index := 0
      inBounds := by decide
      hasInteractingResult := by rfl }
  continuationPattern := .fvar "y"
  continuationVariable := .plain "y"
  subject := .absent
  form := .introduced ⟨historyTerms_notBare giveConstructor.2, rfl, rfl⟩ (by rfl)

/-- `Meet` is the ordered core of the interaction. -/
def historyCoreContact : CoreContactPresentation historyValidated where
  sort := historyPresentation.interactingSort
  constructor := historyPresentation.contactConstructor
  representation := .binary
  representsCore := by rfl

/-- No equation mentions the contact. -/
theorem historyContactEquationFree : ContactEquationFree historyPresentation := by
  have checked :
      historyMachine.equations.all (fun equation =>
        decide (("Meet", 2) ∉ equation.left.constructorRefs ∧
          ("Meet", 2) ∉ equation.right.constructorRefs)) = true := by
    decide +kernel
  intro equation membership
  exact of_decide_eq_true (List.all_eq_true.mp checked equation membership)

/-- The interaction rule as an ordered cut: a waiting history and a given one
meet, and both continuations are released into the contact. -/
def historyCut : InteractionCutPresentation historyTheory where
  program := historyProgramOperand
  environment := historyEnvironmentOperand
  coreContact := historyCoreContact
  programPlacement := .introduced rfl (by
    intro equality
    exact (by decide : ("Wait" : String) ≠ "Meet")
      (congrArg (fun constructor => constructor.1.label) equality))
  environmentPlacement := .introduced rfl (by
    intro equality
    exact (by decide : ("Give" : String) ≠ "Meet")
      (congrArg (fun constructor => constructor.1.label) equality))
  sourceShape :=
    { core := meetRule.left
      coreShape := by
        change CutSourceShape historyCoreContact historyProgramOperand.schemaTerm
          historyEnvironmentOperand.schemaTerm meetRule.left
        exact CutSourceShape.binary rfl
      envelope := .hole
      fillsSource := rfl }
  sourceEnvelopeInSignature := .hole "Hist"
  interactionPremisesEmpty := rfl
  residual := .constructor historyPresentation.contactConstructor
    ⟨historyTerms_notBare historyPresentation.contactConstructor.2, rfl, rfl⟩
  subjectsAgree := .structural rfl historyContactEquationFree

/-- The two sides of the cut are the two prefixes, in that order. -/
theorem historyCut_roles :
    historyCut.program.constructor.1.label = "Wait" ∧
      historyCut.environment.constructor.1.label = "Give" :=
  ⟨rfl, rfl⟩

/-- The roles are not interchangeable: the two introductions differ. -/
theorem historyCut_roles_distinct :
    historyCut.program.constructor.1.label ≠ historyCut.environment.constructor.1.label := by
  decide

/-! ## Wrappability -/

/-- The residual of the interaction is the contact itself, which is neither
prefix, so the contractum lies in the hereditary continuation signature. -/
theorem historyRetyping : ContinuationRetypingPlan historyCut where
  residualCovered :=
    (mem_continuationConstructors_iff historyCut historyTheory.presentation.contactConstructor).2
      ⟨fun equality => (by decide : ("Meet" : String) ≠ "Wait")
          (congrArg (fun constructor => constructor.1.label) equality),
        fun equality => (by decide : ("Meet" : String) ≠ "Give")
          (congrArg (fun constructor => constructor.1.label) equality)⟩

/-- The redex stays sorted once the two continuations are moved to the
wrapped fibre. -/
theorem historyRetyping_redexRetypable : historyRetyping.RedexRetypable := by
  rw [ContinuationRetypingPlan.redexRetypable_def]
  exact checkHasType_sound (by decide +kernel)

/-- **The history theory is wrappable**: the contractum of its interaction
rule has the wrapped sort in the continuation signature. -/
theorem historyRetyping_wrappable : historyRetyping.Wrappable := by
  rw [ContinuationRetypingPlan.wrappable_def]
  exact checkHasType_sound (by decide +kernel)

/-- The continuation under a prefix is retyped to the wrapped fibre. -/
theorem wait_continuation_retyped :
    (costBaseConstructor historyCut historyMachine.terms[23]).params =
      [.simple "h" (.base costWrappedSortName)] := by
  decide +kernel

/-- The configuration under `Now` is not a continuation and stays in the base
fibre. -/
theorem now_parameter_not_retyped :
    (costBaseConstructor historyCut historyMachine.terms[19]).params =
      [.simple "c" (.base (costBaseSortName "Cfg"))] := by
  decide +kernel

/-! ## The equations survive the retyping -/

/-- The executable test that one equation survives continuation retyping: it
has no premise, both sides instantiate and match exactly, and both sides are
sorted at histories in the base fibre and in the wrapped fibre. -/
def equationRetypableCheck (equation : Equation) : Bool :=
  equation.premises.isEmpty &&
    schemaInstantiationStable equation.left &&
    schemaInstantiationStable equation.right &&
    Mettapedia.OSLF.MeTTaIL.Match.Pattern.isMatchCorrect equation.left &&
    Mettapedia.OSLF.MeTTaIL.Match.Pattern.isMatchCorrect equation.right &&
    checkHasType historyRetyping.generatedLanguage
      (FreeTypeContext.ofList (costBaseEquation equation).typeContext) []
      (costBaseEquation equation).left (.base (costBaseSortName "Hist")) &&
    checkHasType historyRetyping.generatedLanguage
      (FreeTypeContext.ofList (costBaseEquation equation).typeContext) []
      (costBaseEquation equation).right (.base (costBaseSortName "Hist")) &&
    checkHasType historyRetyping.generatedLanguage
      (FreeTypeContext.ofList (costWrappedEquation historyTheory equation).typeContext) []
      (costWrappedEquation historyTheory equation).left (.base costWrappedSortName) &&
    checkHasType historyRetyping.generatedLanguage
      (FreeTypeContext.ofList (costWrappedEquation historyTheory equation).typeContext) []
      (costWrappedEquation historyTheory equation).right (.base costWrappedSortName)

/-- Every authored equation passes the test. -/
theorem historyEquations_retypableCheck :
    historyMachine.equations.all equationRetypableCheck = true := by
  decide +kernel

/-- **Every equation of the history theory survives continuation retyping**,
in the base fibre and in the wrapped fibre. -/
theorem historyRetyping_equationsRetypable : EquationsRetypable historyRetyping := by
  intro equation membership
  have checked := List.all_eq_true.mp historyEquations_retypableCheck equation membership
  simp only [equationRetypableCheck, Bool.and_eq_true, List.isEmpty_iff] at checked
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨premiseFree, leftStable⟩, rightStable⟩, leftCorrect⟩, rightCorrect⟩,
    baseLeft⟩, baseRight⟩, wrappedLeft⟩, wrappedRight⟩ := checked
  exact
    { premiseFree := premiseFree
      leftInstantiationStable := leftStable
      rightInstantiationStable := rightStable
      leftMatchCorrect := leftCorrect
      rightMatchCorrect := rightCorrect
      baseWellSorted := ⟨_, checkHasType_sound baseLeft, checkHasType_sound baseRight⟩
      wrappedWellSorted :=
        ⟨_, checkHasType_sound wrappedLeft, checkHasType_sound wrappedRight⟩ }

/-! ## The remaining declaration-level conditions -/

/-- No constructor of the history language is a bare collection, so none can
hide a prefix. -/
theorem historyBareCollectionConstructorsWrapped :
    ∀ rule ∈ historyTheory.presentation.presentation.language.terms,
      UsesBareCollection rule → rule.label ∈ historyRetyping.wrappedLabels :=
  fun _ membership bare => absurd bare (historyTerms_notBare membership)

/-- An admitted reflection profile of the history language has no presentation
to transport. -/
theorem historyRetyping_reflectivePresentationsRetypable
    (reflection : AdmittedProfile historyMachine) :
    ReflectivePresentationsRetypable historyRetyping reflection.1 := by
  intro declaration membership
  rw [historyMachine_presentations_eq_nil reflection] at membership
  cases membership

/-! ## Assembly -/

/-- A continued interactive theory over the history theory, from a contextual
section of its static equivalence that never produces a prefix.  Every other
component is the declaration-level data established above. -/
def historyContinued (reflection : AdmittedProfile historyMachine)
    (openCanonical : ComputableReflectiveFiberContextualSection historyTheory reflection)
    (prefixFree :
      openCanonical.PreservesTypedConstructors (· ∈ historyRetyping.wrappedLabels)) :
    CIGSLT where
  theory := historyTheory
  reflection := reflection
  cut := historyCut
  openCanonical := openCanonical
  continuationRetyping := historyRetyping
  bareCollectionConstructorsWrapped := historyBareCollectionConstructorsWrapped
  openCanonicalPreservesWrappedConstructorTyping := prefixFree
  equationsRetypable := historyRetyping_equationsRetypable
  reflectivePresentationsRetypable :=
    historyRetyping_reflectivePresentationsRetypable reflection
  sourceEnvelopeStable := .hole "Hist"
  redexRetypable := historyRetyping_redexRetypable
  wrappable := historyRetyping_wrappable

/-- The assembled theory lies over the history theory. -/
theorem historyContinued_forget (reflection : AdmittedProfile historyMachine)
    (openCanonical : ComputableReflectiveFiberContextualSection historyTheory reflection)
    (prefixFree :
      openCanonical.PreservesTypedConstructors (· ∈ historyRetyping.wrappedLabels)) :
    CIGSLT.forget.obj (historyContinued reflection openCanonical prefixFree) = historyTheory :=
  rfl

/-- Whatever section completes the history theory to a continued theory, no
computable function on codes tracks it. -/
theorem historyContinued_not_effective (reflection : AdmittedProfile historyMachine)
    (openCanonical : ComputableReflectiveFiberContextualSection historyTheory reflection)
    (prefixFree :
      openCanonical.PreservesTypedConstructors (· ∈ historyRetyping.wrappedLabels)) :
    ¬ ∃ track : ℕ → ℕ, Computable track ∧
      ∀ term : (historyContinued reflection openCanonical prefixFree).CanonicalCarrier,
        patternCode
            ((historyContinued reflection openCanonical prefixFree).canonical.normalize term).1 =
          track (patternCode term.1) :=
  no_effective_continued_section _
    (historyContinued_forget reflection openCanonical prefixFree)

end Mettapedia.Languages.PartrecMachine
