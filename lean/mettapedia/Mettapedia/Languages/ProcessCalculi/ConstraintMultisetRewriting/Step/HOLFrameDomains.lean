import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFrameEncoding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLSemanticDefinitions

/-! # The loaded HOL definition history over the indexed frame carriers

The exported A/T/H/O type parameters receive the inhabited raw object, term,
morphism and occurrence domains. Other parameters keep their supplied
interpretation. The admitted definition history constructs a full-domain
model on those same carriers. Its operational specialization is not assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLFrameDomains

open Mettapedia.Logic
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.TypeFamilySemantics
open Mettapedia.Languages.HOLLight

universe uO uT uH uOcc

inductive Slot where
  | objects | terms | morphisms | occurrences
  deriving DecidableEq

def parameter : Slot → Name
  | .objects => Name.global "A"
  | .terms => Name.global "T"
  | .morphisms => Name.global "H"
  | .occurrences => Name.global "O"

variable (Obj : Type uO) (Tm : Obj → Type uT) (Hom : Obj → Obj → Type uH) (O : Type uOcc)

def domains : Slot → Domain.{max uO uT uH uOcc}
  | .objects => ⟨ULift.{(max uO uT uH uOcc)+1} (HOLFrameEncoding.Objects Obj), .up none⟩
  | .terms => ⟨ULift.{(max uO uT uH uOcc)+1} (HOLFrameEncoding.Terms Tm), .up none⟩
  | .morphisms => ⟨ULift.{(max uO uT uH uOcc)+1} (HOLFrameEncoding.Morphisms Hom), .up none⟩
  | .occurrences => ⟨ULift.{(max uO uT uH uOcc)+1} (Option O), .up none⟩

def assignment (prior : Assignment.{max uO uT uH uOcc}) : Assignment.{max uO uT uH uOcc} :=
  fun name => if name = parameter .objects then domains Obj Tm Hom O .objects
    else if name = parameter .terms then domains Obj Tm Hom O .terms
    else if name = parameter .morphisms then domains Obj Tm Hom O .morphisms
    else if name = parameter .occurrences then domains Obj Tm Hom O .occurrences
    else prior name

theorem parameter_domain (prior : Assignment.{max uO uT uH uOcc}) (slot : Slot) :
    assignment Obj Tm Hom O prior (parameter slot) = domains Obj Tm Hom O slot := by
  cases slot <;> simp [assignment, parameter, Name.global]

theorem other_parameter (prior : Assignment.{max uO uT uH uOcc}) (name : Name)
    (different : ∀ slot, name ≠ parameter slot) : assignment Obj Tm Hom O prior name = prior name := by
  simp [assignment, different]

theorem evaluated_parameter (other : OperatorFamilies.{max uO uT uH uOcc})
    (prior : Assignment.{max uO uT uH uOcc}) (slot : Slot) :
    evaluate (primitiveFamilies other) (assignment Obj Tm Hom O prior) (.var (parameter slot)) =
      domains Obj Tm Hom O slot := by
  rw [evaluate_var, parameter_domain]

theorem empty_term_domain_stays_invalid (a : Obj) [IsEmpty (Tm a)]
    (value : (domains Obj Tm Hom O .terms).Carrier) :
    ¬HOLFrameEncoding.terms (some a) value.down :=
  HOLFrameEncoding.empty_fibre_stays_empty a value.down

noncomputable def initial (other : OperatorFamilies.{max uO uT uH uOcc})
    (prior : Assignment.{max uO uT uH uOcc}) :
    HOL.HenkinModel.{0,0,(max uO uT uH uOcc)+1} AtomicTy Symbol :=
  ModelInterpretation.model other (assignment Obj Tm Hom O prior)
    (ModelInterpretation.pointedMeanings other (assignment Obj Tm Hom O prior))

theorem loaded_model_exists (other : OperatorFamilies.{max uO uT uH uOcc})
    (prior : Assignment.{max uO uT uH uOcc}) :
    ∃ finalModel : HOL.HenkinModel.{0,0,(max uO uT uH uOcc)+1} AtomicTy Symbol,
      finalModel.Carrier = (initial Obj Tm Hom O other prior).Carrier ∧
      finalModel.FullDomains ∧
      ∀ fact ∈ HOLSemanticDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
        ∃ formula : HOL.ClosedFormula Symbol,
          TranslatesCompositionally []
            ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧
          finalModel.models formula := by
  obtain ⟨model, same, full, equations⟩ :=
    HOLSemanticDefinitions.defining_equations_have_constructed_model (initial Obj Tm Hom O other prior)
  exact ⟨model, same, full (ModelInterpretation.model_fullDomains _ _ _), equations⟩

#print axioms empty_term_domain_stays_invalid
#print axioms loaded_model_exists

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLFrameDomains
