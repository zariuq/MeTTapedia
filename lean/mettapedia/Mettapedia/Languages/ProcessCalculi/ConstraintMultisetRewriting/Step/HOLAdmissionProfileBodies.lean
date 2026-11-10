import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLAdmissionTypes

/-! # Independent typed bodies of the admission-profile constructors

Preparation requires readiness, a solution and the supplied witness relation.
The guard constructor quantifies over solutions. Profile inclusion is required
only on preparations admitted by the first profile.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLAdmissionProfileBodies

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLAdmissionTypes HOLBodySyntax
open StandardTheoryInterpretation.Interpretation

universe w

namespace SolutionPreparation

def sourceBody : HOLBodySyntax.Syntax :=
  lambdas [("ready",readyType),("solution",solutionsType),("witness",preparationType),
    ("s",stateType),("f",firingType),("p",witnessType)]
    (conjunction (apps (varTerm "ready") [varTerm "s",varTerm "f"])
      (conjunction (existsTerm "v" solutionType
        (apps (varTerm "solution") [varTerm "s",varTerm "f",varTerm "v"]))
        (apps (varTerm "witness") [varTerm "s",varTerm "f",varTerm "p"])))

theorem body_typed : (checkClosed solutionPreparationType sourceBody).isSome = true := by decide +kernel
def body : HOL.ClosedTerm Symbol solutionPreparationType := (checkClosed solutionPreparationType sourceBody).get body_typed

theorem denote_body (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (full : model.FullDomains)
    (booleans : HOLLoadedBooleans.Meanings model)
    (ready : HOL.Ty.denote.{0,w+1} model.Carrier readyType)
    (solution : HOL.Ty.denote.{0,w+1} model.Carrier solutionsType)
    (witness : HOL.Ty.denote.{0,w+1} model.Carrier preparationType)
    (s : HOL.Ty.denote.{0,w+1} model.Carrier stateType)
    (f : HOL.Ty.denote.{0,w+1} model.Carrier firingType)
    (p : HOL.Ty.denote.{0,w+1} model.Carrier witnessType) :
    model.denote body (fun index => nomatch index) ready solution witness s f p =
      ULift.up ((ready s f).down ∧ (∃ v, (solution s f v).down) ∧ (witness s f p).down) := by
  simp [body, checkClosed, sourceBody, lambdas, conjunction, existsTerm, apps, constant, varTerm, signature,
    HOL.NamedElaboration.check, HOL.NamedElaboration.infer, HOL.NamedElaboration.expectType]
  dsimp only [Except.toOption, Option.get, HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend]
  have existsValues : model.constDen (Symbols.existential solutionType) =
      (fun predicate => ULift.up (∃ value, model.adm solutionType value ∧ (predicate value).down)) :=
    funext (booleans.existential solutionType)
  have admitted (value : HOL.Ty.denote.{0,w+1} model.Carrier solutionType) : model.adm solutionType value := full _ _
  simp only [existsValues, booleans.conjunction, admitted, true_and]

end SolutionPreparation

namespace Guard

def sourceBody : HOLBodySyntax.Syntax :=
  lambdas [("solution",solutionsType),("holds",holdsType),("s",stateType),("f",firingType),("p",witnessType)]
    (all "v" solutionType (implication (apps (varTerm "solution") [varTerm "s",varTerm "f",varTerm "v"])
      (apps (varTerm "holds") [varTerm "s",varTerm "f",varTerm "p",varTerm "v"])))

theorem body_typed : (checkClosed guardProfileType sourceBody).isSome = true := by decide +kernel
def body : HOL.ClosedTerm Symbol guardProfileType := (checkClosed guardProfileType sourceBody).get body_typed

theorem denote_body (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (full : model.FullDomains)
    (booleans : HOLLoadedBooleans.Meanings model)
    (solution : HOL.Ty.denote.{0,w+1} model.Carrier solutionsType)
    (holds : HOL.Ty.denote.{0,w+1} model.Carrier holdsType)
    (s : HOL.Ty.denote.{0,w+1} model.Carrier stateType)
    (f : HOL.Ty.denote.{0,w+1} model.Carrier firingType)
    (p : HOL.Ty.denote.{0,w+1} model.Carrier witnessType) :
    model.denote body (fun index => nomatch index) solution holds s f p =
      ULift.up (∀ v, (solution s f v).down → (holds s f p v).down) := by
  simp [body, checkClosed, sourceBody, lambdas, all, implication, apps, constant, varTerm, signature,
    HOL.NamedElaboration.check, HOL.NamedElaboration.infer, HOL.NamedElaboration.expectType]
  dsimp only [Except.toOption, Option.get, HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend]
  have allValues : model.constDen (Symbols.universal solutionType) =
      (fun predicate => ULift.up (∀ value, model.adm solutionType value → (predicate value).down)) :=
    funext (booleans.universal solutionType)
  have admitted (value : HOL.Ty.denote.{0,w+1} model.Carrier solutionType) : model.adm solutionType value := full _ _
  simp only [allValues, booleans.implication, admitted, forall_true_left]

end Guard

namespace Inclusion

def sourceBody : HOLBodySyntax.Syntax :=
  lambdas [("preparation",preparationType),("first",preparationType),("second",preparationType)]
    (all "s" stateType (all "f" firingType (all "p" witnessType
      (implication (conjunction (apps (varTerm "preparation") [varTerm "s",varTerm "f",varTerm "p"])
        (apps (varTerm "first") [varTerm "s",varTerm "f",varTerm "p"]))
        (apps (varTerm "second") [varTerm "s",varTerm "f",varTerm "p"])))))

theorem body_typed : (checkClosed inclusionType sourceBody).isSome = true := by decide +kernel
def body : HOL.ClosedTerm Symbol inclusionType := (checkClosed inclusionType sourceBody).get body_typed

theorem denote_body (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (full : model.FullDomains)
    (booleans : HOLLoadedBooleans.Meanings model)
    (preparation first second : HOL.Ty.denote.{0,w+1} model.Carrier preparationType) :
    model.denote body (fun index => nomatch index) preparation first second =
      ULift.up (∀ s f p, (preparation s f p).down → (first s f p).down → (second s f p).down) := by
  simp [body, checkClosed, sourceBody, lambdas, all, implication, conjunction, apps, constant, varTerm, signature,
    HOL.NamedElaboration.check, HOL.NamedElaboration.infer, HOL.NamedElaboration.expectType]
  dsimp only [Except.toOption, Option.get, HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend]
  have allStates : model.constDen (Symbols.universal stateType) =
      (fun predicate => ULift.up (∀ value, model.adm stateType value → (predicate value).down)) :=
    funext (booleans.universal stateType)
  have allFirings : model.constDen (Symbols.universal firingType) =
      (fun predicate => ULift.up (∀ value, model.adm firingType value → (predicate value).down)) :=
    funext (booleans.universal firingType)
  have allWitnesses : model.constDen (Symbols.universal witnessType) =
      (fun predicate => ULift.up (∀ value, model.adm witnessType value → (predicate value).down)) :=
    funext (booleans.universal witnessType)
  have statesAdmitted (value : HOL.Ty.denote.{0,w+1} model.Carrier stateType) : model.adm stateType value := full _ _
  have firingsAdmitted (value : HOL.Ty.denote.{0,w+1} model.Carrier firingType) : model.adm firingType value := full _ _
  have witnessesAdmitted (value : HOL.Ty.denote.{0,w+1} model.Carrier witnessType) : model.adm witnessType value := full _ _
  simp only [allStates, allFirings, allWitnesses, booleans.conjunction, booleans.implication,
    statesAdmitted, firingsAdmitted, witnessesAdmitted, forall_true_left, and_imp]

end Inclusion

#print axioms SolutionPreparation.denote_body
#print axioms Guard.denote_body
#print axioms Inclusion.denote_body

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLAdmissionProfileBodies
