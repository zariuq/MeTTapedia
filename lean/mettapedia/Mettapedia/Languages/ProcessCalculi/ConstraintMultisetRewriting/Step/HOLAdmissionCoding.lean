import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLAdmissionTypes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLPreparationEncoding

/-! # Carrier conversions for indexed event packets

The relation checks the source and firing retained by a preparation witness.
Result and permission operations consume that witness without choosing a new
preparation. Invalid raw witnesses cannot pass the relation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLAdmissionCoding

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open HOLAdmissionTypes HOLPreparationEncoding

universe w uS uF uP

structure Coding (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (State : Type uS) (Firing : State → Type uF) (Preparation : (s : State) → Firing s → Sort uP) where
  states : HOL.Ty.denote.{0,w+1} model.Carrier stateType ≃ States State
  firings : HOL.Ty.denote.{0,w+1} model.Carrier firingType ≃ RawFirings State Firing
  witnesses : HOL.Ty.denote.{0,w+1} model.Carrier witnessType ≃ RawWitnesses State Firing Preparation

variable {State : Type uS} {Firing : State → Type uF} {Preparation : (s : State) → Firing s → Sort uP}
  (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (code : Coding model State Firing Preparation)

def preparationValue : HOL.Ty.denote.{0,w+1} model.Carrier preparationType :=
  fun s f p => ULift.up (prepares State Firing Preparation (code.states s) (code.firings f) (code.witnesses p))

def resultValue (next : (s : State) → (f : Firing s) → Preparation s f → State) :
    HOL.Ty.denote.{0,w+1} model.Carrier resultType :=
  fun _ _ p => code.states.symm (result State Firing Preparation next (code.witnesses p))

def permissionValue (allow : (s : State) → (f : Firing s) → Preparation s f → Prop) :
    HOL.Ty.denote.{0,w+1} model.Carrier preparationType :=
  fun _ _ p => ULift.up (permission State Firing Preparation allow (code.witnesses p))

theorem preparation_at_iff {s : State} (f : Firing s)
    (p : HOL.Ty.denote.{0,w+1} model.Carrier witnessType) :
    (preparationValue model code (code.states.symm (some s))
      (code.firings.symm (encodeFiring State Firing f)) p).down ↔
      ∃ witness : Preparation s f, code.witnesses p = encodeWitness State Firing Preparation f witness := by
  simp only [preparationValue, Equiv.apply_symm_apply]
  exact prepares_iff State Firing Preparation f (code.witnesses p)

theorem preparation_exists_iff {s : State} (f : Firing s) :
    (∃ p, (preparationValue model code (code.states.symm (some s))
      (code.firings.symm (encodeFiring State Firing f)) p).down) ↔ Nonempty (Preparation s f) := by
  constructor
  · rintro ⟨p, valid⟩
    obtain ⟨witness,_⟩ := (preparation_at_iff model code f p).mp valid
    exact ⟨witness⟩
  · rintro ⟨witness⟩
    exact ⟨code.witnesses.symm (encodeWitness State Firing Preparation f witness),
      (preparation_at_iff model code f _).mpr ⟨witness, code.witnesses.apply_symm_apply _⟩⟩

theorem result_at (next : (s : State) → (f : Firing s) → Preparation s f → State)
    {s : State} (f : Firing s) (p : Preparation s f) :
    resultValue model code next (code.states.symm (some s)) (code.firings.symm (encodeFiring State Firing f))
      (code.witnesses.symm (encodeWitness State Firing Preparation f p)) = code.states.symm (some (next s f p)) := by
  simp only [resultValue, Equiv.apply_symm_apply, result_encoded]

theorem permission_at (allow : (s : State) → (f : Firing s) → Preparation s f → Prop)
    {s : State} (f : Firing s) (p : Preparation s f) :
    (permissionValue model code allow (code.states.symm (some s)) (code.firings.symm (encodeFiring State Firing f))
      (code.witnesses.symm (encodeWitness State Firing Preparation f p))).down ↔ allow s f p := by
  simp only [permissionValue, Equiv.apply_symm_apply, permission_encoded]

def Coding.changeModel {first : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol}
    (encoding : Coding first State Firing Preparation) (second : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (same : second.Carrier = first.Carrier) : Coding second State Firing Preparation where
  states := (Equiv.cast (congrArg (fun carrier => HOL.Ty.denote.{0,w+1} carrier stateType) same)).trans encoding.states
  firings := (Equiv.cast (congrArg (fun carrier => HOL.Ty.denote.{0,w+1} carrier firingType) same)).trans encoding.firings
  witnesses := (Equiv.cast (congrArg (fun carrier => HOL.Ty.denote.{0,w+1} carrier witnessType) same)).trans encoding.witnesses

#print axioms preparation_at_iff
#print axioms preparation_exists_iff
#print axioms result_at

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLAdmissionCoding
