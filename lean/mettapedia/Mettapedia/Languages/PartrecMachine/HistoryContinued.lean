import Mettapedia.Languages.PartrecMachine.HistoryCut
import Mettapedia.GSLT.LanguageDef.Continued.NotContinued
import Mettapedia.GSLT.LanguageDef.Continued.Effective

/-!
# The history theory is continued, and never effectively

The three clauses of a continued interactive theory are an interaction cut,
a section of the static equivalence on the interacting fibre, and
wrappability of the contractum.  None of them asks the section to be
computed by anything.

The history theory satisfies the three clauses: it has the cut and the
retyping of the preceding module, and a section is obtained by choosing a
representative of every class.  No section of it is effective, so no
continued presentation of it has an effective section, and the closed section
of any continued theory over it is not effective either.  The lambda
calculus is the positive example: it is effectively continued, with the
identity as its section.

With the same signature and equations, a contact rule whose contractum is
headed by its first operand's constructor has no legacy non-principal
retyping plan. That closure obstruction is independent of the section; it
does not imply failure of a more general continuation decoration.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.PartrecMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.GSLT.LanguageDef.ReflectionExtension

/-! ## The three clauses -/

/-- The history theory with the three clauses of a continued theory: its
cut, a section chosen class by class, and the retyping of its contractum. -/
noncomputable def historyContinuedPresentation : ContinuedPresentation historyTheory where
  cut := historyCut
  canonical := ComputableCanonicalSection.ofChoice historyTheory
  retyping := ContinuationDecorationProfile.ofRetypingPlan historyRetyping
  redexRetypable :=
    (ContinuationDecorationProfile.ofRetypingPlan_redexRetypable_iff _).mpr
      historyRetyping_redexRetypable
  wrappable :=
    (ContinuationDecorationProfile.ofRetypingPlan_wrappable_iff _).mpr historyRetyping_wrappable

/-- **The history theory is continued.** -/
theorem history_isContinued : IsContinued historyTheory :=
  ⟨historyContinuedPresentation⟩

/-- **No continued presentation of the history theory has an effective
section.** -/
theorem history_continuedPresentation_not_effective
    (continued : ContinuedPresentation historyTheory) : ¬ continued.canonical.Effective :=
  historyTheory_no_effective_section continued.canonical

/-- **Continued, and never effectively.**  The history theory satisfies the
three clauses, and whatever data witness them, the section is not tracked by
a computable function on codes. -/
theorem history_continued_never_effectively :
    IsContinued historyTheory ∧
      ∀ continued : ContinuedPresentation historyTheory, ¬ continued.canonical.Effective :=
  ⟨history_isContinued, history_continuedPresentation_not_effective⟩

/-- **The history theory is continued and not effectively continued.**  It is
the theory that separates the two notions. -/
theorem history_not_effectivelyContinued :
    IsContinued historyTheory ∧ ¬ IsEffectivelyContinued historyTheory :=
  ⟨history_isContinued, fun ⟨continued, effective⟩ =>
    history_continuedPresentation_not_effective continued effective⟩

/-! ## Continued theories over the history theory -/

/-- A section of an iGSLT equal to the history theory is not effective. -/
theorem no_effective_section_of_eq (theory : IGSLT) (same : theory = historyTheory)
    (canonical : ComputableCanonicalSection theory) : ¬ canonical.Effective := by
  subst same
  exact historyTheory_no_effective_section canonical

/-- An admitted reflection profile of an iGSLT equal to the history theory
has no presentation. -/
theorem presentations_eq_nil_of_eq (theory : IGSLT) (same : theory = historyTheory)
    (reflection : AdmittedProfile theory.presentation.presentation.language) :
    reflection.1.presentations = [] := by
  subst same
  exact historyMachine_presentations_eq_nil reflection

/-- A continued theory over the history theory authors no reflection, so it
has a closed section. -/
theorem reflectionFree_of_underlying (continued : CIGSLT)
    (underlying : CIGSLT.forget.obj continued = historyTheory) : continued.ReflectionFree :=
  presentations_eq_nil_of_eq continued.theory underlying continued.reflection

/-- **The closed section of a continued theory over the history theory is
not effective.** -/
theorem closedSection_not_effective (continued : CIGSLT)
    (underlying : CIGSLT.forget.obj continued = historyTheory)
    (free : continued.ReflectionFree) : ¬ (continued.closedSection free).Effective :=
  no_effective_section_of_eq continued.theory underlying (continued.closedSection free)

/-! ## The contact rule matters -/

/-- Two finished runs meet and the first remains.  The contractum is headed
by `Flag`, the constructor of the first operand. -/
def absorbRule : RewriteRule where
  name := "Absorb"
  typeContext := [("x", .base "Cfg"), ("y", .base "Cfg")]
  premises := []
  left := meet (flag (.fvar "x")) (flag (.fvar "y"))
  right := flag (.fvar "x")

/-- The history machine with that rule in place of its own: the same sorts,
constructors and equations. -/
def absorbingMachine : LanguageDef :=
  { historyMachine with
    name := "AbsorbingHistoryMachine"
    rewrites := [absorbRule] }

/-- Only the interaction rule differs. -/
theorem absorbingMachine_static :
    absorbingMachine.types = historyMachine.types ∧
      absorbingMachine.terms = historyMachine.terms ∧
      absorbingMachine.equations = historyMachine.equations :=
  ⟨rfl, rfl, rfl⟩

theorem absorbingEquations_ok :
    absorbingMachine.equations.all (LanguageDef.plainEquationOk absorbingMachine) = true := by
  decide +kernel

theorem absorbRule_ok : LanguageDef.plainRewriteOk absorbingMachine absorbRule = true := by
  decide +kernel

/-- The language passes the structural declaration gate. -/
theorem absorbingMachine_validate_eq_nil : absorbingMachine.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorEquationsAndRewrites
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro equation membership
    exact LanguageDef.validateEquation_eq_nil_of_plainEquationOk
      (List.all_eq_true.mp absorbingEquations_ok equation membership)
  · intro rewrite membership
    obtain rfl : rewrite = absorbRule := List.mem_singleton.mp membership
    exact LanguageDef.validateRewrite_eq_nil_of_plainRewriteOk absorbRule_ok

/-- The language passes the ordered binding-flow gate with no relation mode. -/
theorem absorbingMachine_executionAdmissionErrors_eq_nil :
    absorbingMachine.executionAdmissionErrors [] = [] :=
  LanguageDef.executionAdmissionErrors_eq_nil_of_emptyModes absorbingMachine
    absorbingMachine_validate_eq_nil
    (LanguageDef.executionFlowErrors_eq_nil_of_plainFlowOk (by decide +kernel) [])

/-- Histories are the interacting sort and `Meet` the contact, as before; the
interaction is the absorbing rule. -/
def absorbingPresentation : InteractivePresentation where
  presentation := ⟨absorbingMachine, absorbingMachine_validate_eq_nil⟩
  interactingSort := ⟨absorbingMachine.types[5], List.getElem_mem (by decide)⟩
  contactConstructor := ⟨absorbingMachine.terms[22], List.getElem_mem (by decide)⟩
  interactionRewrite := ⟨absorbRule, List.Mem.head _⟩
  contactRepresentation := .binary
  representsContact := by rfl
  interactionHeaded := by rfl

/-- The absorbing theory as an iGSLT. -/
def absorbingTheory : IGSLT where
  presentation := absorbingPresentation
  baseInteraction := isBaseRewrite_of_premises_eq_nil rfl
  executionProfile :=
    { relationModes := []
      admitted :=
        { lang := absorbingMachine
          admitted := absorbingMachine_executionAdmissionErrors_eq_nil }
      exactLanguage := rfl }

/-- Every cut of the absorbing rule names `Flag` as the first introduction,
so no legacy non-principal retyping plan covers its contractum. The failure
does not concern its section or an independent decorated closure. -/
theorem absorbing_legacyRetyping_isEmpty
    (cut : InteractionCutPresentation absorbingTheory) :
    IsEmpty (ContinuationRetypingPlan cut) :=
  isEmpty_retypingPlan_of_contractum_headed_by_program
    (contact := "Meet") (introduction := "Flag") (programArguments := [.fvar "x"])
    (contractumArguments := [.fvar "x"]) (environment := .apply "Flag" [.fvar "y"])
    rfl rfl (by decide) (by decide) cut

end Mettapedia.Languages.PartrecMachine
