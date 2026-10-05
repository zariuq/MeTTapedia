import Mettapedia.GSLT.LanguageDef.Continued.Presentation
import Mettapedia.GSLT.LanguageDef.Continued.NotContinued
import Mettapedia.GSLT.LanguageDef.Continued.Sections
import Mettapedia.GSLT.LanguageDef.Interaction.BaseInteractions
import Mettapedia.GSLT.LanguageDef.Interaction.MigrationInstances
import Mettapedia.GSLT.LanguageDef.Interaction.Surfaces
import Mettapedia.Languages.Calculator.Section
import Mettapedia.Languages.ProcessCalculi.CCS.Continued
import Mettapedia.Languages.ProcessCalculi.CCS.Surface
import Mettapedia.Languages.ProcessCalculi.Ambient.Continued
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction
import Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredSemantics
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Synchronous
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SynchronousDecoration
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
import Mettapedia.Languages.InteractionCategory.Continued
import Mettapedia.Languages.TuringMachine.NotInteractive
import Mettapedia.Languages.Transducers.ForcedReading

/-!
# The instance tables, row by row

Each running example is an authored language, and each entry of the two
tables of instances is a theorem about it: whether it has a contact and a
rule at it, how its surface is carried, what its contraction moves, whether
it has a section, whether its contraction is wrappable, and the verdict.

"Continued" is read as the three clauses state it (`IsContinued`), or as an
object of the category of continued theories where one exists.

The algebraic, effective and restrictive Cost verdicts are kept distinct.

* Synchronous rho's communication decorates a bundle of three payloads.
  Its algebraic section below is selected by choice on its actual quotient;
  effectiveness is not asserted. The old two-slot sorting problem still fails.
* Composition in an interaction category is effectively continued under both
  readings. Visible composition rebuilds a decorated action prefix; excluding
  that prefix gives the restrictive non-principal negative control.
* The calculator is "a theory only" as an equational theory with no rule.
  Read as rewriting, its successor law meets the definition of an interactive
  theory and has an interaction cut.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.InstanceTable

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.BagNormalForm
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-! ## Calculator -/

/-- **Calculator: a theory only.**  No rule to select, hence no contact rule;
its static equivalence has the evaluated numeral as normal form. -/
theorem calculator_row :
    ¬ AdmitsInteractivePresentation Mettapedia.Languages.Calculator.calculator ∧
      (∀ left right : Mettapedia.Languages.Calculator.Expression,
        Mettapedia.Languages.Calculator.expressionSetoid.r left right ↔
          Mettapedia.Languages.Calculator.calculatorSection.normalize left =
            Mettapedia.Languages.Calculator.calculatorSection.normalize right) :=
  ⟨Mettapedia.Languages.Calculator.calculator_not_interactive,
    Mettapedia.Languages.Calculator.calculator_normal_form_only.1⟩

/-- The same arithmetic read as rewriting is interactive, has a cut and
composes interfaces. No legacy non-principal plan covers its successor rule;
this does not exclude an independently chosen decorated closure. -/
theorem calculatorRewriting_row :
    IsInteractive Mettapedia.Languages.Calculator.calculatorRewriting ∧
      Mettapedia.Languages.Calculator.successorCut.migrationMode = .interface ∧
        (∀ cut : InteractionCutPresentation
          Mettapedia.Languages.Calculator.calculatorRewritingIGSLT,
          IsEmpty (ContinuationRetypingPlan cut)) :=
  ⟨Mettapedia.Languages.Calculator.calculatorRewriting_isInteractive,
    Mettapedia.Languages.Calculator.successorCut_migrationMode, successor_legacyRetyping_isEmpty⟩

/-! ## CCS -/

section CCS

open Mettapedia.Languages.ProcessCalculi.CCS

/-- **CCS: continued interactive.**  Contact: parallel composition, a bag
whose laws exchange and regroup its components.  Surfaces: the name on both
prefixes.  Contraction: pure release.  Section: the bag normal form. -/
theorem ccs_row :
    IsInteractive ccsCalc ∧
      (ccsInteractionCut.program.subject.pattern = some (.fvar "a") ∧
        ccsInteractionCut.environment.subject.pattern = some (.fvar "a")) ∧
      ccsInteractionCut.migrationMode = .none ∧
      IsContinued ccsIGSLT :=
  ⟨ccsCalc_isInteractive, ccs_subject_nominal, ccs_migrationMode, ccs_isContinued⟩

/-- The contact of CCS is commutative and associative: the two orders of the
handshake are equal, and so is the handshake regrouped. -/
theorem ccs_contact_laws :
    ccsIGSLT.toGSLT.equations.r handshakeTerm handshakeSwappedTerm ∧
      ccsIGSLT.toGSLT.equations.r handshakeNestedTerm handshakeTerm :=
  ⟨handshake_swaps, handshakeNested_equivalent⟩

end CCS

/-! ## Interaction categories -/

section InteractionCategories

open Mettapedia.Languages.InteractionCategory

/-- **Interaction categories, silent reading: continued interactive.**
Contact: composition, a free binary constructor.  Surfaces: the shared
interface action.  Contraction: the continuations composed again; nothing
moves.  Section: equality. -/
theorem interactionCategory_silent_row :
    IsInteractive (interactionCategory .silent) ∧
      ContactEquationFree (presentation .silent) ∧
      ((cut .silent).program.subject.pattern = some (.fvar "b") ∧
        (cut .silent).environment.subject.pattern = some (.fvar "b")) ∧
      (cut .silent).migrationMode = .none ∧
      IsContinued (theory .silent) :=
  ⟨interactionCategory_isInteractive .silent, contact_equation_free .silent,
    subject_nominal .silent, silent_migrationMode, silent_isContinued⟩

/-- Visible composition is algebraically continued with its rebuilt action
prefix. Excluding that prefix still fails the restrictive sorting problem.
The section's effectiveness is established independently in its instance module. -/
theorem interactionCategory_visible_row :
    IsInteractive (interactionCategory .visible) ∧
      (cut .visible).migrationMode = .interface ∧
      IsContinued (theory .visible) ∧
      ¬ visibleNonPrincipalDecoration.Wrappable :=
  ⟨interactionCategory_isInteractive .visible, visible_migrationMode,
    visible_isContinued, visibleNonPrincipalDecoration_not_wrappable⟩

/-- **A wrappable cut that is not a two-slot plan.**  Visible composition has
a wrappable cut, whose continuation bundle contains the rebuilt action
prefix, and is the theory of no `WrappableIGSLT`: those carry a two-slot
plan. -/
theorem visible_wrappableCut_without_plan :
    Nonempty (WrappableCut (theory .visible)) ∧
      ∀ wrappable : WrappableIGSLT, wrappable.theory ≠ theory .visible :=
  ⟨⟨visibleContinuedPresentation.toWrappableCut⟩,
    visibleComposition_not_wrappableIGSLT⟩

end InteractionCategories

/-! ## Rho and pi, asynchronous -/

section Asynchronous

open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- **Rho, asynchronous: continued interactive.**  It is the underlying
theory of an object of the category of continued theories; its surface is the
name on both sides, and its contraction binds the quoted message into the
input body. -/
theorem rho_row :
    IsInteractive rhoCalc ∧
      (rhoInteractionCut.program.subject.pattern = some (.fvar "n") ∧
        rhoInteractionCut.environment.subject.pattern = some (.fvar "n")) ∧
      rhoInteractionCut.migrationMode = .binding ∧
      CIGSLT.forget.obj rhoCIGSLT = rhoIGSLT :=
  ⟨rhoCalc_isInteractive, rho_subject_nominal, rho_migrationMode, rfl⟩

/-- The static laws of asynchronous pi are those of one bag. -/
theorem pi_bagTheory : BagTheory piCalc piParallelConstructor.1 (some "PiNil") :=
  piBagTheory

/-- The bag normal form is a section of asynchronous pi. -/
def piCanonicalSection : ComputableCanonicalSection piIGSLT :=
  bagCanonicalSection piIGSLT pi_bagTheory

/-- The three clauses for asynchronous pi. -/
def piContinuedPresentation : ContinuedPresentation piIGSLT where
  cut := piInteractionCut
  canonical := piCanonicalSection
  retyping := ContinuationDecorationProfile.ofRetypingPlan piContinuationRetyping
  redexRetypable :=
    (ContinuationDecorationProfile.ofRetypingPlan_redexRetypable_iff _).mpr
      piContinuationRetyping_redexRetypable
  wrappable :=
    (ContinuationDecorationProfile.ofRetypingPlan_wrappable_iff _).mpr
      piContinuationRetyping_wrappable

/-- **Pi, asynchronous: continued interactive.** -/
theorem pi_row :
    IsInteractive piCalc ∧
      piInteractionCut.migrationMode = .binding ∧
      IsContinued piIGSLT :=
  ⟨piCalc_isInteractive, pi_migrationMode, ⟨piContinuedPresentation⟩⟩

end Asynchronous

/-! ## Rho and pi, synchronous -/

section Synchronous

open Mettapedia.Languages.ProcessCalculi.PiCalculus.Synchronous
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous

/-- The static laws of synchronous pi are those of one bag. -/
theorem piSync_bagTheory : BagTheory piSyncCalc piSyncParallelConstructor.1 (some "PiNil") :=
  bagTheory_of_check (by decide +kernel)

/-- The bag normal form is a section of synchronous pi. -/
def piSyncCanonicalSection : ComputableCanonicalSection piSyncIGSLT :=
  bagCanonicalSection piSyncIGSLT piSync_bagTheory

/-- The three clauses for synchronous pi. -/
def piSyncContinuedPresentation : ContinuedPresentation piSyncIGSLT where
  cut := piSyncInteractionCut
  canonical := piSyncCanonicalSection
  retyping := ContinuationDecorationProfile.ofRetypingPlan piSyncContinuationRetyping
  redexRetypable :=
    (ContinuationDecorationProfile.ofRetypingPlan_redexRetypable_iff _).mpr
      piSyncContinuationRetyping_redexRetypable
  wrappable :=
    (ContinuationDecorationProfile.ofRetypingPlan_wrappable_iff _).mpr
      piSyncContinuationRetyping_wrappable

/-- **Pi, synchronous: continued interactive.**  The carried name is bound
into the input body; the process after the output is released. -/
theorem piSync_row :
    IsInteractive piSyncCalc ∧
      piSyncInteractionCut.migrationMode = .binding ∧
      IsContinued piSyncIGSLT :=
  ⟨piSyncCalc_isInteractive, piSync_migrationMode, ⟨piSyncContinuedPresentation⟩⟩

/-- A genuine algebraic section of synchronous rho's ordinary authored
equation quotient. The use of choice supplies no code-tracking theorem. -/
noncomputable def rhoSyncAlgebraicCanonicalSection :
    ComputableCanonicalSection rhoSyncIGSLT :=
  ComputableCanonicalSection.ofChoice rhoSyncIGSLT

/-- The three algebraic clauses for the actual synchronous communication
rule and three-payload decoration. Effectiveness is a separate obligation. -/
noncomputable def rhoSyncAlgebraicContinuedPresentation :
    ContinuedPresentation rhoSyncIGSLT where
  cut := rhoSyncInteractionCut
  canonical := rhoSyncAlgebraicCanonicalSection
  retyping := communicationDecoration
  redexRetypable := communicationDecoration_redexRetypable
  wrappable := communicationDecoration_wrappable

theorem rhoSync_isContinued : IsContinued rhoSyncIGSLT :=
  ⟨rhoSyncAlgebraicContinuedPresentation⟩

/-- Synchronous rho is algebraically continued on its actual ordinary
quotient and decorated payload bundle. The original two-slot problem still
fails; no effective canonical section is asserted by this row. -/
theorem rhoSync_row :
    IsInteractive rhoSyncCalc ∧
      rhoSyncInteractionCut.migrationMode = .binding ∧
      IsContinued rhoSyncIGSLT ∧
      ¬ (ContinuationDecorationProfile.ofRetypingPlan
        rhoSyncContinuationRetyping).Wrappable :=
  ⟨rhoSyncCalc_isInteractive, rhoSync_migrationMode, rhoSync_isContinued,
    decoration_separates_two_slots.2.2⟩

end Synchronous

/-! ## Lambda -/

section Lambda

open Mettapedia.GSLT.LanguageDef.LambdaContinuedInteraction

/-- **Lambda: continued interactive, once the structure is chosen.**
Contact: application, free.  Surface: carried by position.  Contraction:
substitution of the argument.  Section: equality on the locally nameless
carrier, the only one there. -/
theorem lambda_row :
    IsInteractive lambdaInteractivePresentation.presentation.language ∧
      lambdaInteractivePresentation.RigidContact ∧
      (lambdaInteractionCut.program.subject.pattern = none ∧
        lambdaInteractionCut.environment.subject.pattern = none) ∧
      lambdaInteractionCut.migrationMode = .binding ∧
      CIGSLT.forget.obj lambdaCIGSLT = lambdaIGSLT ∧
      IsContinued lambdaIGSLT :=
  ⟨lambdaCalc_isInteractive, lambda_rigidContact, ⟨rfl, rfl⟩, lambda_migrationMode, rfl,
    lambda_isContinued⟩

end Lambda

/-! ## Ambients -/

section Ambients

open Mettapedia.Languages.ProcessCalculi.Ambient.Mobile

/-- **Ambients: continued interactive.**  Contact: parallel composition.
Surfaces: the name of the boundary.  Contraction: the boundary dissolves;
spatial. -/
theorem ambient_row :
    IsInteractive ambientCalc ∧
      (dissolutionCut.program.subject.pattern = some (.fvar "n") ∧
        dissolutionCut.environment.subject.pattern = some (.fvar "n")) ∧
      dissolutionCut.migrationMode = .spatial ∧
      IsContinued ambientIGSLT :=
  ⟨ambientCalc_isInteractive, ambient_subject_nominal, dissolution_migrationMode,
    ambient_isContinued⟩

end Ambients

/-! ## The three machines -/

section Machines

open Mettapedia.Languages.TuringMachine
open Mettapedia.Languages.Transducers

/-- **Turing: a theory only.**  Every table gives a validated theory; the
contact between control and tape is ordered, binary and heterogeneous, and
no constructor of the signature is a same-sort contact. -/
theorem turing_row (machine : Mettapedia.Languages.TuringMachine.Machine) :
    (turingMachine machine).validate = [] ∧
      coreContactRepresentation? (TypeDecl.plain "Config") runConstructor = some .binary ∧
      (∀ sort : TypeDecl, contactRepresentation? sort runConstructor = none) ∧
      ¬ AdmitsInteractivePresentation (turingMachine machine) :=
  ⟨turingMachine_validate_eq_nil machine, run_is_ordered_binary_contact,
    run_is_not_same_sort_contact, turingMachine_not_interactive machine⟩

/-- **Moore and Mealy: theories only.**  The contact between control and
stream is heterogeneous under both disciplines. -/
theorem transducer_row {discipline : Discipline} (machine : Machine discipline) :
    (transducer machine).validate = [] ∧
      coreContactRepresentation? (TypeDecl.plain "Config") feedConstructor = some .binary ∧
      (∀ sort : TypeDecl, contactRepresentation? sort feedConstructor = none) ∧
      ¬ AdmitsInteractivePresentation (transducer machine) :=
  ⟨transducer_validate_eq_nil machine, feed_is_ordered_binary_contact,
    feed_is_not_same_sort_contact, transducer_not_interactive machine⟩

/-- Under a forced reading the Moore machine's emitted value moves nothing and
the Mealy machine's reads the consumed symbol; the next control state reads
it under both. -/
theorem transducer_forced_reading (moore : Machine .moore) (mealy : Machine .mealy) :
    (emissionReading moore).dataMode = .none ∧
      (emissionReading mealy).dataMode = .binding ∧
      (controlReading moore).dataMode = .binding ∧
      (controlReading mealy).dataMode = .binding :=
  ⟨moore_dataMode moore, mealy_dataMode mealy, control_dataMode moore, control_dataMode mealy⟩

end Machines

/-! ## The migration spectrum -/

/-- **The four modes each occur.**  None: CCS and silent composition.
Binding: rho, pi and lambda.  Spatial: ambients.  Interface composition:
visible composition and the successor law. -/
theorem migration_spectrum :
    Mettapedia.Languages.ProcessCalculi.CCS.ccsInteractionCut.migrationMode = .none ∧
      (Mettapedia.Languages.InteractionCategory.cut .silent).migrationMode = .none ∧
      rhoInteractionCut.migrationMode = .binding ∧
      Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction.piInteractionCut.migrationMode =
        .binding ∧
      LambdaContinuedInteraction.lambdaInteractionCut.migrationMode = .binding ∧
      Mettapedia.Languages.ProcessCalculi.Ambient.Mobile.dissolutionCut.migrationMode =
        .spatial ∧
      (Mettapedia.Languages.InteractionCategory.cut .visible).migrationMode = .interface :=
  ⟨Mettapedia.Languages.ProcessCalculi.CCS.ccs_migrationMode,
    Mettapedia.Languages.InteractionCategory.silent_migrationMode, rho_migrationMode,
    Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction.pi_migrationMode,
    lambda_migrationMode,
    Mettapedia.Languages.ProcessCalculi.Ambient.Mobile.dissolution_migrationMode,
    Mettapedia.Languages.InteractionCategory.visible_migrationMode⟩

end Mettapedia.GSLT.LanguageDef.InstanceTable
