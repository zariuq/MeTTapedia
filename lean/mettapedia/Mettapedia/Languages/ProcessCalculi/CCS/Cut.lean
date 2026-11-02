import Mettapedia.Languages.ProcessCalculi.CCS.Interaction
import Mettapedia.GSLT.LanguageDef.Interaction.Migration

/-!
# The interaction cut of CCS, and what it moves

The reaction of CCS is an interaction cut whose operands meet the contact as summands. The program is a process
prefixed by an action, the environment a process prefixed by the complementary action, and the two prefixes carry the
name that must match. Each prefix is one summand of a sum standing in the parallel composition; the cut selects it and
discards the other summands of its sum (`ccs_discards_others`). This is the additive cut: a choice is resolved by the
interaction itself.

The contraction sets both continuations free in the parallel composition where the sums stood. Nothing is substituted,
nothing is relocated and nothing is guarded again: the migration mode is none.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-- Prefixing by an action. -/
def ccsActionConstructor : DeclaredConstructor ccsValidatedLanguageDef :=
  ⟨ccsCalc.terms[4], List.getElem_mem (by simp [ccsCalc])⟩

/-- Prefixing by a co-action. -/
def ccsCoActionConstructor : DeclaredConstructor ccsValidatedLanguageDef :=
  ⟨ccsCalc.terms[5], List.getElem_mem (by simp [ccsCalc])⟩

/-- The sum is a declared choice: a wrapped multiset of guards. -/
theorem ccsSum_isChoice : IsChoice ccsSumConstructor.1 :=
  ⟨rfl, "gs", .base "Guard", rfl⟩

/-- The program side: an action prefix, its name the subject and the prefixed process the continuation. -/
def ccsProgramIntroduction : InteractionOperandProfile ccsInteractivePresentation where
  constructor := ccsActionConstructor
  schemaTerm := .apply "CAct" [.fvar "a", .fvar "p"]
  continuation :=
    { index := 1
      inBounds := by simp [ccsActionConstructor, ccsCalc]
      hasInteractingResult := by rfl }
  continuationPattern := .fvar "p"
  continuationVariable := .plain "p"
  subject := .argument
    { index := 0, inBounds := by simp [ccsActionConstructor, ccsCalc] }
    (.fvar "a") (by rfl)
  form := .introduced (by
      simp [RepresentedBy, UsesBareCollection, ccsActionConstructor, ccsCalc])
    (by rfl)

/-- The environment side: a co-action prefix on the same name. -/
def ccsEnvironmentIntroduction : InteractionOperandProfile ccsInteractivePresentation where
  constructor := ccsCoActionConstructor
  schemaTerm := .apply "CCoAct" [.fvar "a", .fvar "q"]
  continuation :=
    { index := 1
      inBounds := by simp [ccsCoActionConstructor, ccsCalc]
      hasInteractingResult := by rfl }
  continuationPattern := .fvar "q"
  continuationVariable := .plain "q"
  subject := .argument
    { index := 0, inBounds := by simp [ccsCoActionConstructor, ccsCalc] }
    (.fvar "a") (by rfl)
  form := .introduced (by
      simp [RepresentedBy, UsesBareCollection, ccsCoActionConstructor, ccsCalc])
    (by rfl)

/-- The core contact is parallel composition itself. -/
def ccsCoreContact : CoreContactPresentation ccsValidatedLanguageDef where
  sort := ccsInteractivePresentation.interactingSort
  constructor := ccsInteractivePresentation.contactConstructor
  representation := ccsInteractivePresentation.contactRepresentation
  representsCore := by rfl

/-- **The reaction as an interaction cut**, each prefix a summand of a sum. -/
def ccsInteractionCut : InteractionCutPresentation ccsIGSLT where
  program := ccsProgramIntroduction
  environment := ccsEnvironmentIntroduction
  coreContact := ccsCoreContact
  programPlacement := .introduced rfl (by
      intro equality
      have labels := congrArg (fun constructor => constructor.1.label) equality
      change "CAct" = "CPar" at labels
      exact (by decide : ("CAct" : String) ≠ "CPar") labels)
  environmentPlacement := .introduced rfl (by
      intro equality
      have labels := congrArg (fun constructor => constructor.1.label) equality
      change "CCoAct" = "CPar" at labels
      exact (by decide : ("CCoAct" : String) ≠ "CPar") labels)
  sourceShape :=
    { core := ccsReactRewrite.left
      coreShape :=
        (CutSourceShape.collection [] (some "rest") (.summand ccsSumConstructor "m" ccsSum_isChoice)
            (.summand ccsSumConstructor "n" ccsSum_isChoice) rfl :
          CutSourceShape ccsCoreContact
            ccsProgramIntroduction.schemaTerm
            ccsEnvironmentIntroduction.schemaTerm
            (.collection .hashBag
              (.apply "CSum" [.collection .hashBag [ccsProgramIntroduction.schemaTerm] (some "m")] ::
                .apply "CSum" [.collection .hashBag [ccsEnvironmentIntroduction.schemaTerm] (some "n")] :: [])
              (some "rest")))
      envelope := .hole
      fillsSource := rfl }
  sourceEnvelopeInSignature := .hole "Proc"
  interactionPremisesEmpty := rfl
  residual := .constructor ccsParallelConstructor (by
    change RepresentedBy ccsParallelConstructor.1 ccsReactRewrite.right
    exact ⟨"ps", .base "Proc", rfl⟩)
  subjectsAgree := .nominal (.fvar "a") rfl rfl

/-- The two surfaces are one name, matched explicitly: the subject is carried nominally. -/
theorem ccs_subject_nominal :
    ccsInteractionCut.program.subject.pattern = some (.fvar "a") ∧
      ccsInteractionCut.environment.subject.pattern = some (.fvar "a") :=
  ⟨rfl, rfl⟩

/-- **The cut resolves both choices**: the other summands of the two sums occur in its source and not in its
contractum. -/
theorem ccs_discards_others :
    "m" ∈ ccsReactRewrite.left.freeFvarNames ∧ "n" ∈ ccsReactRewrite.left.freeFvarNames ∧
      "m" ∉ ccsReactRewrite.right.freeFvarNames ∧ "n" ∉ ccsReactRewrite.right.freeFvarNames := by
  simp [ccsReactRewrite, Pattern.freeFvarNames]

/-- **The one reduction position of CCS is the body of a restriction.** No position of a prefix is one: a prefix
guards its continuation. -/
theorem ccs_reductionPositions : reductionPositions ccsCalc = [("CNu", 0)] := by
  decide +kernel

/-- **CCS moves nothing.** The contraction is pure release. -/
theorem ccs_migrationMode : ccsInteractionCut.migrationMode = .none := by
  decide +kernel

/-- The environment brings exactly its continuation, and it is not bound into the program's. -/
theorem ccs_not_bindsFromEnvironment : ¬ ccsInteractionCut.BindsFromEnvironment := by
  decide +kernel

/-- Each continuation appears in every instance of the contractum as it was matched: the reduct is the parallel
composition of the two continuations and the rest. -/
theorem ccs_releases (bindings : Bindings) :
    applyBindings bindings ccsReactRewrite.right =
      .collection .hashBag
        ([applyBindings bindings (.fvar "p"), applyBindings bindings (.fvar "q")] ++
          (restResolution bindings .hashBag (some "rest")).1)
        (restResolution bindings .hashBag (some "rest")).2 := by
  have occurrence :
      OneHoleContext.collection .hashBag [] .hole [.fvar "q"] (some "rest") ∈
        zippersAt (.fvar ccsInteractionCut.contractionSchema.programContinuation)
          ccsInteractionCut.contractionSchema.contractum := by
    decide +kernel
  have released := ccsInteractionCut.contractionSchema.program_released_of_mode_ne_binding
    (by rw [show ccsInteractionCut.contractionSchema.mode = .none from ccs_migrationMode]
        decide) bindings occurrence
  exact released

end Mettapedia.Languages.ProcessCalculi.CCS
