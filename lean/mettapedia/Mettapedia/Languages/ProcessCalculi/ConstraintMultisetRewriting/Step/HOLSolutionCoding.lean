import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLAdmissionCoding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFrameEncoding

/-! # Solution values retain arbitrary future frame morphisms

The raw solution domain contains all morphisms, including maps that do not
solve the information. The supplied solution predicate checks Models. The
encoding preserves the future frame and morphism without identifying distinct
representatives that happen to have the same action.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLSolutionCoding

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open HOLAdmissionTypes HOLPreparationEncoding

universe w uO uT uH uS uF uP

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

theorem encode_future_injective (a : Obj) :
    Function.Injective (fun future : (b : Obj) × Hom a b => HOLFrameEncoding.encodeHom future.2) := by
  rintro ⟨b, sigma⟩ ⟨c, tau⟩ same
  have targets := congrArg (fun raw : HOLFrameEncoding.Morphisms Hom => raw.map (fun entry => entry.1.2)) same
  have targetEq : b = c := Option.some.inj targets
  subst c
  have mapEq : sigma = tau := HOLFrameEncoding.morphism_identity_retained a b same
  subst tau
  rfl

def answers {a : Obj} (holds : (b : Obj) → Hom a b → Prop) (raw : HOLFrameEncoding.Morphisms Hom) : Prop :=
  ∃ (b : Obj) (sigma : Hom a b), raw = HOLFrameEncoding.encodeHom sigma ∧ holds b sigma

theorem answers_encoded {a b : Obj} (holds : (c : Obj) → Hom a c → Prop) (sigma : Hom a b) :
    answers holds (HOLFrameEncoding.encodeHom sigma) ↔ holds b sigma := by
  constructor
  · rintro ⟨c,tau,same,valid⟩
    have futures : (⟨b,sigma⟩ : (c : Obj) × Hom a c) = ⟨c,tau⟩ := encode_future_injective a same
    cases futures
    exact valid
  · intro valid
    exact ⟨b,sigma,rfl,valid⟩

abbrev Coding (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (Obj : Type uO) (Hom : Obj → Obj → Type uH) :=
  HOL.Ty.denote.{0,w+1} model.Carrier solutionType ≃ HOLFrameEncoding.Morphisms Hom

variable {State : Type uS} {Firing : State → Type uF} {Preparation : (s : State) → Firing s → Sort uP}
  (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (X : Frames Tm Hom)
  (events : HOLAdmissionCoding.Coding model State Firing Preparation) (solutions : Coding model Obj Hom)
  (target : {s : State} → Firing s → Obj)
  (information : {s : State} → (f : Firing s) → EquationStore (Tm (target f)))

def readyValue (ready : (s : State) → Firing s → Prop) : HOL.Ty.denote.{0,w+1} model.Carrier readyType :=
  fun s f => ULift.up (match events.firings f with
    | none => False
    | some ⟨source,candidate⟩ => events.states s = some source ∧ ready source candidate)

def solutionsValue : HOL.Ty.denote.{0,w+1} model.Carrier solutionsType :=
  fun s f v => ULift.up (match events.firings f with
    | none => False
    | some ⟨source,candidate⟩ => events.states s = some source ∧
        answers (fun _ sigma => X.Models sigma (information candidate)) (solutions v))

def holdsValue (holds : (s : State) → (f : Firing s) → Preparation s f → (b : Obj) → Hom (target f) b → Prop) :
    HOL.Ty.denote.{0,w+1} model.Carrier holdsType :=
  fun s f p v => ULift.up (match events.witnesses p with
    | none => False
    | some ⟨⟨source,candidate⟩,prepared⟩ =>
        events.states s = some source ∧ events.firings f = some ⟨source,candidate⟩ ∧
          answers (holds source candidate prepared.down) (solutions v))

theorem ready_at (ready : (s : State) → Firing s → Prop) {s : State} (f : Firing s) :
    (readyValue model events ready (events.states.symm (some s))
      (events.firings.symm (encodeFiring State Firing f))).down ↔ ready s f := by
  simp [readyValue, encodeFiring]

theorem solutions_at {s : State} (f : Firing s) (v : HOL.Ty.denote.{0,w+1} model.Carrier solutionType) :
    (solutionsValue model X events solutions target information (events.states.symm (some s))
      (events.firings.symm (encodeFiring State Firing f)) v).down ↔
      answers (fun _ sigma => X.Models sigma (information f)) (solutions v) := by
  simp [solutionsValue, encodeFiring]

theorem holds_at (holds : (s : State) → (f : Firing s) → Preparation s f → (b : Obj) → Hom (target f) b → Prop)
    {s : State} (f : Firing s) (p : Preparation s f) (v : HOL.Ty.denote.{0,w+1} model.Carrier solutionType) :
    (holdsValue model events solutions target holds (events.states.symm (some s))
      (events.firings.symm (encodeFiring State Firing f))
      (events.witnesses.symm (encodeWitness State Firing Preparation f p)) v).down ↔
      answers (holds s f p) (solutions v) := by
  simp [holdsValue, encodeFiring, encodeWitness]

theorem solvable_at {s : State} (f : Firing s) :
    (∃ v, (solutionsValue model X events solutions target information (events.states.symm (some s))
      (events.firings.symm (encodeFiring State Firing f)) v).down) ↔ X.Solvable (information f) := by
  simp only [solutions_at]
  constructor
  · rintro ⟨v,b,sigma,_,valid⟩
    exact ⟨b,sigma,valid⟩
  · rintro ⟨b,sigma,valid⟩
    exact ⟨solutions.symm (HOLFrameEncoding.encodeHom sigma),b,sigma,solutions.apply_symm_apply _,valid⟩

theorem entails_at (holds : (s : State) → (f : Firing s) → Preparation s f → (b : Obj) → Hom (target f) b → Prop)
    {s : State} (f : Firing s) (p : Preparation s f) :
    (∀ v, (solutionsValue model X events solutions target information (events.states.symm (some s))
        (events.firings.symm (encodeFiring State Firing f)) v).down →
      (holdsValue model events solutions target holds (events.states.symm (some s))
        (events.firings.symm (encodeFiring State Firing f))
        (events.witnesses.symm (encodeWitness State Firing Preparation f p)) v).down) ↔
      X.Entails (information f) (holds s f p) := by
  simp only [solutions_at, holds_at]
  constructor
  · intro guards b sigma solved
    have guarded := guards (solutions.symm (HOLFrameEncoding.encodeHom sigma))
      ⟨b,sigma,solutions.apply_symm_apply _,solved⟩
    rw [solutions.apply_symm_apply] at guarded
    exact (answers_encoded (holds s f p) sigma).mp guarded
  · intro guards v solved
    obtain ⟨b,sigma,same,solves⟩ := solved
    exact ⟨b,sigma,same,guards b sigma solves⟩

def changeModel {first : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol}
    (encoding : Coding first Obj Hom) (second : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (same : second.Carrier = first.Carrier) : Coding second Obj Hom :=
  (Equiv.cast (congrArg (fun carrier => HOL.Ty.denote.{0,w+1} carrier solutionType) same)).trans encoding

#print axioms encode_future_injective
#print axioms solvable_at
#print axioms entails_at

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLSolutionCoding
