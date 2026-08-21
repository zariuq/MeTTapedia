import Mettapedia.Languages.MeTTa.PeTTa.OperationalGSLT
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystem
import Mettapedia.OSLF.Framework.RelationalAnswerTypeSynthesis

/-!
# Operationally derived native typing for PeTTa

OSLF derives behavioral types by applying modalities to observations of the
operational GSLT.  This module carries out that construction for PeTTa's
declarative stateful core.

Two layers are kept explicit:

* `producesBareSymbol` is wholly derived from operational syntax and reduction;
* `producesAuthoredType` lifts the existing authored `MeTTaType` judgment as a
  base observation through the same operational modalities.

The proved comparison is deliberately directional.  Every operational bare
symbol has authored type `Atom`, but authored annotations can assign `Atom` to
non-symbols.  The negative witness shows why a complete derivation of profile
typing requires declarations and profile contracts to be composed into the
source GSLT; a bare rewrite graph cannot reconstruct authored information.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.OperationalNativeTyping

open Mettapedia.GSLT.Dynamics.RelationalAnswerEvaluation
open Mettapedia.Languages.MeTTa.PeTTa.OperationalGSLT
open Mettapedia.OSLF.Framework.RelationalAnswerTypeSynthesis
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Spatial observation selecting nullary applications, PeTTa's symbol
representation. -/
def bareSymbolObservation
    (_initial : EvalState) (_request : Pattern) (_final : EvalState)
    (answer : Pattern) : Prop :=
  ∃ name, answer = .apply name []

/-- OSLF-derived type of requests that can complete and emit a bare symbol. -/
def producesBareSymbol : CoreOperationalTerm → Prop :=
  producesAnswerSatisfying coreSource bareSymbolObservation

/-- Lift the existing authored PeTTa type judgment through the operational
GSLT.  This is a comparison construction, not a claim that the authored
judgment itself was recovered from reduction alone. -/
def authoredTypeObservation (type : Pattern)
    (_initial : EvalState) (_request : Pattern) (final : EvalState)
    (answer : Pattern) : Prop :=
  MeTTaType final.space answer type

/-- Behavioral type of requests that can emit an answer carrying an authored
PeTTa type. -/
def producesAuthoredType (type : Pattern) : CoreOperationalTerm → Prop :=
  producesAnswerSatisfying coreSource (authoredTypeObservation type)

/-- Exact operational meaning of the generated bare-symbol type. -/
theorem producesBareSymbol_request_iff
    (initial : EvalState) (request : Pattern) :
    producesBareSymbol (.request initial request) ↔
      ∃ (final : EvalState) (answers : Answers),
        ∃ occurrence : Fin answers.length,
          CoreDecl initial request final answers ∧
            ∃ name, answers.get occurrence = .apply name [] := by
  simpa [producesBareSymbol, bareSymbolObservation, coreSource] using
    producesAnswerSatisfying_request_iff coreSource bareSymbolObservation
      initial request

/-- Exact operational meaning of a generated authored-type observation. -/
theorem producesAuthoredType_request_iff
    (type : Pattern) (initial : EvalState) (request : Pattern) :
    producesAuthoredType type (.request initial request) ↔
      ∃ (final : EvalState) (answers : Answers),
        ∃ occurrence : Fin answers.length,
          CoreDecl initial request final answers ∧
            MeTTaType final.space (answers.get occurrence) type := by
  simpa [producesAuthoredType, authoredTypeObservation, coreSource] using
    producesAnswerSatisfying_request_iff coreSource
      (authoredTypeObservation type) initial request

/-- The spatial bare-symbol observation refines the authored `Atom` type. -/
theorem bareSymbolObservation_implies_atomType
    (initial : EvalState) (request : Pattern) (final : EvalState)
    (answer : Pattern) :
    bareSymbolObservation initial request final answer →
      authoredTypeObservation atomType initial request final answer := by
  rintro ⟨name, rfl⟩
  exact MeTTaType.symbolIsAtom name

/-- Therefore the operationally derived bare-symbol type is contained in the
behavioral lift of the authored `Atom` judgment. -/
theorem producesBareSymbol_implies_producesAtom :
    ∀ term, producesBareSymbol term → producesAuthoredType atomType term := by
  exact producesAnswerSatisfying_mono coreSource
    bareSymbolObservation_implies_atomType

/-! ## Positive operational witness -/

private def foo : Pattern := .apply "foo" []

/-- Evaluating a bare symbol provides a concrete inhabitant of the generated
native type. -/
theorem groundFoo_producesBareSymbol :
    producesBareSymbol (.request EvalState.empty foo) := by
  rw [producesBareSymbol_request_iff]
  let occurrence : Fin ([foo] : Answers).length := ⟨0, by simp⟩
  exact ⟨EvalState.empty, [foo], occurrence,
    CoreDecl.pure _ _ _ (PureDecl.ground "foo"), ⟨"foo", rfl⟩⟩

/-- The comparison theorem transports the same run into authored `Atom`. -/
theorem groundFoo_producesAuthoredAtom :
    producesAuthoredType atomType (.request EvalState.empty foo) :=
  producesBareSymbol_implies_producesAtom _ groundFoo_producesBareSymbol

/-! ## Negative information: authored declarations are not reduction alone -/

private def appliedFoo : Pattern := .apply "foo" [.apply "x" []]

private def annotatedApplicationState : EvalState :=
  { space :=
      { facts := [typeAnnotationPat appliedFoo atomType]
        rules := [] } }

private def annotatedApplicationSuperpose : Pattern :=
  .apply "superpose" [.collection .vec [appliedFoo] none]

/-- An explicit space declaration may assign `Atom` to a non-symbol. -/
theorem annotatedApplication_has_authoredAtom :
    MeTTaType annotatedApplicationState.space appliedFoo atomType := by
  exact MeTTaType.typeAnnotation _ _ (by simp [annotatedApplicationState])

/-- The annotated non-symbol is genuinely emitted by the operational core. -/
theorem annotatedApplication_producesAuthoredAtom :
    producesAuthoredType atomType
      (.request annotatedApplicationState annotatedApplicationSuperpose) := by
  rw [producesAuthoredType_request_iff]
  let occurrence : Fin ([appliedFoo] : Answers).length := ⟨0, by simp⟩
  exact ⟨annotatedApplicationState, [appliedFoo], occurrence,
    CoreDecl.pure _ _ _ (PureDecl.superpose [appliedFoo]),
    annotatedApplication_has_authoredAtom⟩

/-- A non-nullary application is not a bare-symbol observation. -/
theorem appliedFoo_not_bareSymbol
    (initial : EvalState) (request : Pattern) (final : EvalState) :
    ¬ bareSymbolObservation initial request final appliedFoo := by
  rintro ⟨name, impossible⟩
  simp [appliedFoo] at impossible

/-- Authored `Atom` observations do not refine the operational bare-symbol
type.  This is the concrete obstruction to claiming that a rewrite-only GSLT
determines all authored profile typing. -/
theorem authoredAtom_not_subtype_bareSymbol :
    ¬ (∀ initial request final answer,
      authoredTypeObservation atomType initial request final answer →
        bareSymbolObservation initial request final answer) := by
  intro alleged
  exact appliedFoo_not_bareSymbol annotatedApplicationState
    annotatedApplicationSuperpose annotatedApplicationState
    (alleged annotatedApplicationState annotatedApplicationSuperpose
      annotatedApplicationState appliedFoo annotatedApplication_has_authoredAtom)

end Mettapedia.Languages.MeTTa.PeTTa.OperationalNativeTyping
