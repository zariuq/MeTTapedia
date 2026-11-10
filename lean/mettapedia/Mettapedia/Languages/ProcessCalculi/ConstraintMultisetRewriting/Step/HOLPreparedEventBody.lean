import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLAdmissionTypes

/-! # Independent typed body of a prepared event -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPreparedEventBody

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLAdmissionTypes HOLBodySyntax
open StandardTheoryInterpretation.Interpretation

def sourceBody : HOLBodySyntax.Syntax :=
  lambdas [("preparation", preparationType), ("result", resultType), ("s", stateType),
    ("f", firingType), ("p", witnessType), ("t", stateType)]
    (conjunction (apps (varTerm "preparation") [varTerm "s",varTerm "f",varTerm "p"])
      (.equal (varTerm "t") (apps (varTerm "result") [varTerm "s",varTerm "f",varTerm "p"])))

theorem body_typed : (checkClosed preparedEventType sourceBody).isSome = true := by decide +kernel

def body : HOL.ClosedTerm Symbol preparedEventType := (checkClosed preparedEventType sourceBody).get body_typed

universe w

theorem denote_body (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (full : model.FullDomains) (booleans : HOLLoadedBooleans.Meanings model)
    (preparation : HOL.Ty.denote.{0,w+1} model.Carrier preparationType)
    (result : HOL.Ty.denote.{0,w+1} model.Carrier resultType)
    (s t : HOL.Ty.denote.{0,w+1} model.Carrier stateType)
    (f : HOL.Ty.denote.{0,w+1} model.Carrier firingType)
    (p : HOL.Ty.denote.{0,w+1} model.Carrier witnessType) :
    model.denote body (fun index => nomatch index) preparation result s f p t =
      ULift.up ((preparation s f p).down ∧ t = result s f p) := by
  simp [body, checkClosed, sourceBody, lambdas, conjunction, apps, constant, varTerm, signature,
    HOL.NamedElaboration.check, HOL.NamedElaboration.infer, HOL.NamedElaboration.expectType]
  dsimp only [Except.toOption, Option.get, HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend]
  rw [booleans.conjunction]
  have equalState (x y : HOL.Ty.denote.{0,w+1} model.Carrier stateType) :
      model.Eqv stateType x y ↔ x = y := model.eqv_iff_eq_of_fullDomains full _ _
  simp only [equalState]

#print axioms body_typed
#print axioms denote_body

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPreparedEventBody
