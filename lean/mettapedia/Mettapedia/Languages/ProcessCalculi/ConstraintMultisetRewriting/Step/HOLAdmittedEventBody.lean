import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLAdmissionTypes

/-! # Independent typed body of an event with explicit permission

The prepared-event symbol is an explicit typed parameter. Its loaded identity
is supplied and checked when this body is compared with the source equation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLAdmittedEventBody

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLAdmissionTypes HOLBodySyntax
open StandardTheoryInterpretation.Interpretation

def sourceBody (prepared : Symbol preparedEventType) : HOLBodySyntax.Syntax :=
  lambdas [("preparation", preparationType), ("result", resultType), ("allow", preparationType),
    ("s", stateType), ("f", firingType), ("p", witnessType), ("t", stateType)]
    (conjunction (apps (constant prepared)
      [varTerm "preparation",varTerm "result",varTerm "s",varTerm "f",varTerm "p",varTerm "t"])
      (apps (varTerm "allow") [varTerm "s",varTerm "f",varTerm "p"]))

theorem body_typed (prepared : Symbol preparedEventType) :
    (checkClosed admittedEventType (sourceBody prepared)).isSome = true := by
  simp [checkClosed, sourceBody, lambdas, conjunction, apps, constant, varTerm, signature,
    HOL.NamedElaboration.check, HOL.NamedElaboration.infer, HOL.NamedElaboration.expectType,
    Except.toOption]

def body (prepared : Symbol preparedEventType) : HOL.ClosedTerm Symbol admittedEventType :=
  (checkClosed admittedEventType (sourceBody prepared)).get (body_typed prepared)

universe w

theorem denote_body (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (booleans : HOLLoadedBooleans.Meanings model) (prepared : Symbol preparedEventType)
    (preparation allow : HOL.Ty.denote.{0,w+1} model.Carrier preparationType)
    (result : HOL.Ty.denote.{0,w+1} model.Carrier resultType)
    (s t : HOL.Ty.denote.{0,w+1} model.Carrier stateType)
    (f : HOL.Ty.denote.{0,w+1} model.Carrier firingType)
    (p : HOL.Ty.denote.{0,w+1} model.Carrier witnessType) :
    model.denote (body prepared) (fun index => nomatch index) preparation result allow s f p t =
      ULift.up ((model.constDen prepared preparation result s f p t).down ∧ (allow s f p).down) := by
  simp [body, checkClosed, sourceBody, lambdas, conjunction, apps, constant, varTerm, signature,
    HOL.NamedElaboration.check, HOL.NamedElaboration.infer, HOL.NamedElaboration.expectType]
  dsimp only [Except.toOption, Option.get, HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend]
  rw [booleans.conjunction]
  rfl

#print axioms body_typed
#print axioms denote_body

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLAdmittedEventBody
