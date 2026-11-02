import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateCheckedRealizability
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateFreeInterpreter
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeGuardedRealizabilityControls

/-!
# Checked beta transport over an open predicate guard

An incoming source equality certificate transports an existing application
realizer to its beta endpoint. The arbitrary predicate guard stays attached
to the endpoint. Changing the source type or the context certificate refuses
the request before transport; this example needs no interpreted root rows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeCheckedRealizability.Controls

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies AnnotatedPredicateReading
open NativeGuardedRealizability.Controls

abbrev source : CTm Tower.Head 2 := .app (.lam (.var 1) (.var 0)) (.var 0)
abbrev endpoint : CTm Tower.Head 2 := .var 0
abbrev sourceType : CTm Tower.Head 2 := .var 1

theorem betaEquality : CEqual (Programs.Annotated.church profile) valueContext.source source endpoint sourceType := by
  have familyFormed : CIsType (Programs.Annotated.church profile)
      (.snoc valueContext.source (.var 1)) (.var 2) :=
    ⟨universeHead, by decide +kernel, .var 2⟩
  obtain ⟨level, allowed, productTyped⟩ :=
    CIsType.pi (Programs.Annotated.levelModel profile) family_formed familyFormed
  exact CDerivable.betaPi productTyped allowed (.var 0) variableValue.typed

def equalityCertificate : Programs.Annotated.JudgmentReplay.Certificate profile := by
  annotated_certificate 8000 betaEquality

def rootReader (Γ : HOL.Ctx BaseSort) (left right : CTm Tower.Head Γ.length)
    (_code : SchemaJudgmentCode.Code Tower.Head Γ.length) :
    Option ((carrier : HOL.Ty BaseSort) × FreeInterpreter.Evidence lex roots Γ left right carrier) := none

def received := Interpreter.check? (Programs.Annotated.church profile)
  (Programs.Annotated.JudgmentReplay.decoder profile) FreeInterpreter.operations rootReader
  [number, predicateType] valueContext.source source endpoint sourceType contextCertificate equalityCertificate

theorem source_checked : Programs.Annotated.JudgmentReplay.check profile equalityCertificate
    (.equality valueContext.source source endpoint sourceType) = true := by decide +kernel

theorem received_checked : received.isSome = true := by decide +kernel

def checked := received.get received_checked

def transported := appliedIdentity.rewriteChecked (Programs.Annotated.levelModel profile) checked

theorem endpoint_typed : CTyped (Programs.Annotated.church profile) valueContext.source endpoint sourceType :=
  transported.typed

theorem endpoint_guard_retained : transported.predicate = appliedIdentity.predicate :=
  GuardedRealizer.rewriteChecked_predicate _ _ _

theorem endpoint_code_exact : transported.term = variableValue.term :=
  Reader.term_unique transported.termRead variableValue.termRead

theorem endpoint_guard_exact : transported.predicate = variableValue.predicate :=
  Reader.term_unique transported.typeRead variableValue.typeRead

theorem transported_free : transported.Free :=
  GuardedRealizer.rewriteChecked_free _ appliedIdentity checked application_free checked.evidence.property

def run := Interpreter.checkRealizer? (Programs.Annotated.levelModel profile)
  (Programs.Annotated.JudgmentReplay.decoder profile) FreeInterpreter.operations rootReader
  (Γ := [number, predicateType]) (context := valueContext) (target := endpoint)
  appliedIdentity contextCertificate equalityCertificate

theorem run_accepted : run.isSome = true := by
  apply (Interpreter.checkRealizer?_isSome_iff _ _ _ _ _ _ _).2
  exact received_checked

def changedType := Interpreter.check? (Programs.Annotated.church profile)
  (Programs.Annotated.JudgmentReplay.decoder profile) FreeInterpreter.operations rootReader
  [number, predicateType] valueContext.source source endpoint (.const natName) contextCertificate equalityCertificate

theorem changed_type_refused : changedType.isNone = true := by decide +kernel

def missingContext := Interpreter.checkRealizer? (Programs.Annotated.levelModel profile)
  (Programs.Annotated.JudgmentReplay.decoder profile) FreeInterpreter.operations rootReader
  (Γ := [number, predicateType]) (context := valueContext) (target := endpoint) appliedIdentity
  (.snoc (.snoc .nil nextHead equalityCertificate) universeHead equalityCertificate) equalityCertificate

theorem missing_context_refused : missingContext.isNone = true := by decide +kernel

#print axioms betaEquality
#print axioms received_checked
#print axioms endpoint_typed
#print axioms endpoint_code_exact
#print axioms endpoint_guard_exact
#print axioms transported_free
#print axioms run_accepted
#print axioms changed_type_refused
#print axioms missing_context_refused

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeCheckedRealizability.Controls
