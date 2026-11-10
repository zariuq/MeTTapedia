import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedDisjunction
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLOccurrenceCoding

/-! # Independent typed body of the occurrence update

The update retains an old occurrence exactly when it was not taken, and
includes every made occurrence. Permission and read dependencies are separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLFireBody

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLBodySyntax HOLOccurrenceCoding
open StandardTheoryInterpretation.Interpretation

abbrev predicateType : HOL.Ty AtomicTy := .arr setType (.arr setType (.arr setType setType))

def sourceBody : HOLBodySyntax.Syntax :=
  lambdas [("present", setType), ("taken", setType), ("made", setType), ("occ", occurrenceType)]
    (apps (constant HOLLoadedDisjunction.symbol)
      [conjunction (apps (varTerm "present") [varTerm "occ"])
        (apps (constant Symbols.negation) [apps (varTerm "taken") [varTerm "occ"]]),
       apps (varTerm "made") [varTerm "occ"]])

theorem body_typed : (checkClosed predicateType sourceBody).isSome = true := by decide +kernel

def body : HOL.ClosedTerm Symbol predicateType := (checkClosed predicateType sourceBody).get body_typed

universe w

theorem denote_body (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (full : model.FullDomains)
    (equations : ∀ fact ∈ HOLSemanticDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
      ∃ formula : HOL.ClosedFormula Symbol,
        TranslatesCompositionally []
          ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)
    (present taken made : HOL.Ty.denote.{0,w+1} model.Carrier setType)
    (occ : HOL.Ty.denote.{0,w+1} model.Carrier occurrenceType) :
    model.denote body (fun index => nomatch index) present taken made occ =
      ULift.up (((present occ).down ∧ ¬(taken occ).down) ∨ (made occ).down) := by
  simp [body, checkClosed, sourceBody, lambdas, conjunction, apps, constant, varTerm, signature,
    HOL.NamedElaboration.check, HOL.NamedElaboration.infer, HOL.NamedElaboration.expectType]
  dsimp only [Except.toOption, Option.get, HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend]
  have booleans := HOLLoadedBooleans.meanings_of_cache model equations full
  rw [HOLLoadedDisjunction.operational_meaning model full equations, booleans.conjunction, booleans.negation]
  rfl

#print axioms body_typed
#print axioms denote_body

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLFireBody
