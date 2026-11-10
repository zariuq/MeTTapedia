import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLAdmissionDefinitions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLAdmissionCoding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLOccurrenceCoding

/-! # A shared model domain for frames, effects and indexed events

State, firing and preparation fibres may have independent universe levels
and may be empty. Only raw carriers acquire invalid sentinels. The solution
domain retains a morphism's source and target, supporting guard profiles over
arbitrary future frames.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLAdmissionDomains

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open TypeFamilySemantics

universe uO uT uH uOcc uS uF uP

inductive Slot where
  | objects | terms | morphisms | occurrences | states | firings | witnesses | solutions
  deriving DecidableEq

def parameter : Slot → Name
  | .objects => Name.global "A"
  | .terms => Name.global "T"
  | .morphisms => Name.global "H"
  | .occurrences => Name.global "O"
  | .states => Name.global "S"
  | .firings => Name.global "F"
  | .witnesses => Name.global "P"
  | .solutions => Name.global "V"

variable (Obj : Type uO) (Tm : Obj → Type uT) (Hom : Obj → Obj → Type uH) (O : Type uOcc)
  (State : Type uS) (Firing : State → Type uF) (Preparation : (s : State) → Firing s → Sort uP)

def domains : Slot → Domain.{max uO uT uH uOcc uS uF uP}
  | .objects => ⟨ULift.{(max uO uT uH uOcc uS uF uP)+1} (HOLFrameEncoding.Objects Obj), .up none⟩
  | .terms => ⟨ULift.{(max uO uT uH uOcc uS uF uP)+1} (HOLFrameEncoding.Terms Tm), .up none⟩
  | .morphisms => ⟨ULift.{(max uO uT uH uOcc uS uF uP)+1} (HOLFrameEncoding.Morphisms Hom), .up none⟩
  | .occurrences => ⟨ULift.{(max uO uT uH uOcc uS uF uP)+1} (Option O), .up none⟩
  | .states => ⟨ULift.{(max uO uT uH uOcc uS uF uP)+1} (HOLPreparationEncoding.States State), .up none⟩
  | .firings => ⟨ULift.{(max uO uT uH uOcc uS uF uP)+1} (HOLPreparationEncoding.RawFirings State Firing), .up none⟩
  | .witnesses => ⟨ULift.{(max uO uT uH uOcc uS uF uP)+1} (HOLPreparationEncoding.RawWitnesses State Firing Preparation), .up none⟩
  | .solutions => ⟨ULift.{(max uO uT uH uOcc uS uF uP)+1} (HOLFrameEncoding.Morphisms Hom), .up none⟩

def assignment (prior : Assignment.{max uO uT uH uOcc uS uF uP}) : Assignment.{max uO uT uH uOcc uS uF uP} :=
  fun name => if name = parameter .objects then domains Obj Tm Hom O State Firing Preparation .objects
    else if name = parameter .terms then domains Obj Tm Hom O State Firing Preparation .terms
    else if name = parameter .morphisms then domains Obj Tm Hom O State Firing Preparation .morphisms
    else if name = parameter .occurrences then domains Obj Tm Hom O State Firing Preparation .occurrences
    else if name = parameter .states then domains Obj Tm Hom O State Firing Preparation .states
    else if name = parameter .firings then domains Obj Tm Hom O State Firing Preparation .firings
    else if name = parameter .witnesses then domains Obj Tm Hom O State Firing Preparation .witnesses
    else if name = parameter .solutions then domains Obj Tm Hom O State Firing Preparation .solutions
    else prior name

theorem parameter_domain (prior : Assignment.{max uO uT uH uOcc uS uF uP}) (slot : Slot) :
    assignment Obj Tm Hom O State Firing Preparation prior (parameter slot) = domains Obj Tm Hom O State Firing Preparation slot := by
  cases slot <;> simp [assignment, parameter, Name.global]

theorem evaluated_parameter (other : OperatorFamilies.{max uO uT uH uOcc uS uF uP})
    (prior : Assignment.{max uO uT uH uOcc uS uF uP}) (slot : Slot) :
    evaluate (primitiveFamilies other) (assignment Obj Tm Hom O State Firing Preparation prior) (.var (parameter slot)) =
      domains Obj Tm Hom O State Firing Preparation slot := by
  rw [evaluate_var, parameter_domain]

noncomputable def initial (other : OperatorFamilies.{max uO uT uH uOcc uS uF uP})
    (prior : Assignment.{max uO uT uH uOcc uS uF uP}) :
    HOL.HenkinModel.{0,0,(max uO uT uH uOcc uS uF uP)+1} AtomicTy Symbol :=
  ModelInterpretation.model other (assignment Obj Tm Hom O State Firing Preparation prior)
    (ModelInterpretation.pointedMeanings other (assignment Obj Tm Hom O State Firing Preparation prior))

def parameterCoding (other : OperatorFamilies.{max uO uT uH uOcc uS uF uP})
    (prior : Assignment.{max uO uT uH uOcc uS uF uP}) (slot : Slot) :
    HOL.Ty.denote.{0,(max uO uT uH uOcc uS uF uP)+1}
      (initial Obj Tm Hom O State Firing Preparation other prior).Carrier (Ty.var (parameter slot)).toHOL ≃
      (domains Obj Tm Hom O State Firing Preparation slot).Carrier :=
  (TypeFamilySemantics.holValue other (assignment Obj Tm Hom O State Firing Preparation prior)
    (Ty.var (parameter slot))).symm.trans
      (Equiv.cast (congrArg Domain.Carrier (evaluated_parameter Obj Tm Hom O State Firing Preparation other prior slot)))

def frameCoding (other : OperatorFamilies.{max uO uT uH uOcc uS uF uP})
    (prior : Assignment.{max uO uT uH uOcc uS uF uP}) :
    HOLFrameCoding.Coding (initial Obj Tm Hom O State Firing Preparation other prior) Obj Tm Hom where
  objects := (parameterCoding Obj Tm Hom O State Firing Preparation other prior .objects).trans Equiv.ulift
  terms := (parameterCoding Obj Tm Hom O State Firing Preparation other prior .terms).trans Equiv.ulift
  morphisms := (parameterCoding Obj Tm Hom O State Firing Preparation other prior .morphisms).trans Equiv.ulift

def occurrenceCoding (other : OperatorFamilies.{max uO uT uH uOcc uS uF uP})
    (prior : Assignment.{max uO uT uH uOcc uS uF uP}) :
    HOLOccurrenceCoding.Coding (initial Obj Tm Hom O State Firing Preparation other prior) O :=
  (parameterCoding Obj Tm Hom O State Firing Preparation other prior .occurrences).trans Equiv.ulift

def eventCoding (other : OperatorFamilies.{max uO uT uH uOcc uS uF uP})
    (prior : Assignment.{max uO uT uH uOcc uS uF uP}) :
    HOLAdmissionCoding.Coding (initial Obj Tm Hom O State Firing Preparation other prior) State Firing Preparation where
  states := (parameterCoding Obj Tm Hom O State Firing Preparation other prior .states).trans Equiv.ulift
  firings := (parameterCoding Obj Tm Hom O State Firing Preparation other prior .firings).trans Equiv.ulift
  witnesses := (parameterCoding Obj Tm Hom O State Firing Preparation other prior .witnesses).trans Equiv.ulift

theorem loaded_model_exists (other : OperatorFamilies.{max uO uT uH uOcc uS uF uP})
    (prior : Assignment.{max uO uT uH uOcc uS uF uP}) :
    ∃ actual : HOL.HenkinModel.{0,0,(max uO uT uH uOcc uS uF uP)+1} AtomicTy Symbol,
      actual.Carrier = (initial Obj Tm Hom O State Firing Preparation other prior).Carrier ∧ actual.FullDomains ∧
      ∀ fact ∈ HOLAdmissionDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
        ∃ formula : HOL.ClosedFormula Symbol,
          TranslatesCompositionally []
            ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ actual.models formula := by
  obtain ⟨actual, same, full, equations⟩ := HOLAdmissionDefinitions.defining_equations_have_constructed_model
    (initial Obj Tm Hom O State Firing Preparation other prior)
  exact ⟨actual, same, full (ModelInterpretation.model_fullDomains _ _ _), equations⟩

#print axioms parameter_domain
#print axioms eventCoding
#print axioms loaded_model_exists

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLAdmissionDomains
