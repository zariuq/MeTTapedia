import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedSolutionPreparation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedGuardProfile
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLSolutionCoding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLPreparedEffectEncoding

/-! # Solution and guard constructors agree with the indexed contracts

The solution domain contains all raw morphisms; Models selects genuine
solutions. Guard interpretation therefore quantifies over all future
solutions. Readiness, solution existence and the supplied preparation witness
remain separate conditions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLGuardSpecialization

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLAdmissionTypes HOLPreparationEncoding HOLSolutionCoding

universe w uO uT uH uS uF uP

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {State : Type uS} {Firing : State → Type uF} {Preparation : (s : State) → Firing s → Sort uP}
  (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (X : Frames Tm Hom)
  (events : HOLAdmissionCoding.Coding model State Firing Preparation) (solutions : Coding model Obj Hom)
  (target : {s : State} → Firing s → Obj)
  (information : {s : State} → (f : Firing s) → EquationStore (Tm (target f)))
  (full : model.FullDomains)
  (equations : ∀ fact ∈ HOLAdmissionDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)

include full equations in
theorem guard_iff
    (holds : (s : State) → (f : Firing s) → Preparation s f → (b : Obj) → Hom (target f) b → Prop)
    {s : State} (f : Firing s) (p : Preparation s f) :
    (model.constDen HOLLoadedGuardProfile.symbol (solutionsValue model X events solutions target information)
      (holdsValue model events solutions target holds) (events.states.symm (some s))
      (events.firings.symm (encodeFiring State Firing f))
      (events.witnesses.symm (encodeWitness State Firing Preparation f p))).down ↔
      X.Entails (information f) (holds s f p) := by
  have evaluated := HOLLoadedGuardProfile.operational_meaning model full equations
    (solutionsValue model X events solutions target information) (holdsValue model events solutions target holds)
    (events.states.symm (some s)) (events.firings.symm (encodeFiring State Firing f))
    (events.witnesses.symm (encodeWitness State Firing Preparation f p))
  exact (iff_of_eq (congrArg ULift.down evaluated)).trans
    (entails_at model X events solutions target information holds f p)

include full equations in
theorem preparation_iff (ready : (s : State) → Firing s → Prop) {s : State} (f : Firing s)
    (p : HOL.Ty.denote.{0,w+1} model.Carrier witnessType) :
    (model.constDen HOLLoadedSolutionPreparation.symbol (readyValue model events ready)
      (solutionsValue model X events solutions target information) (HOLAdmissionCoding.preparationValue model events)
      (events.states.symm (some s)) (events.firings.symm (encodeFiring State Firing f)) p).down ↔
      ready s f ∧ X.Solvable (information f) ∧
        ∃ witness : Preparation s f, events.witnesses p = encodeWitness State Firing Preparation f witness := by
  have evaluated := HOLLoadedSolutionPreparation.operational_meaning model full equations
    (readyValue model events ready) (solutionsValue model X events solutions target information)
    (HOLAdmissionCoding.preparationValue model events) (events.states.symm (some s))
    (events.firings.symm (encodeFiring State Firing f)) p
  refine (iff_of_eq (congrArg ULift.down evaluated)).trans ?_
  rw [ready_at, solvable_at, HOLAdmissionCoding.preparation_at_iff]

include full equations in
theorem preparation_exists_iff (ready : (s : State) → Firing s → Prop) {s : State} (f : Firing s) :
    (∃ p, (model.constDen HOLLoadedSolutionPreparation.symbol (readyValue model events ready)
      (solutionsValue model X events solutions target information) (HOLAdmissionCoding.preparationValue model events)
      (events.states.symm (some s)) (events.firings.symm (encodeFiring State Firing f)) p).down) ↔
      ready s f ∧ X.Solvable (information f) ∧ Nonempty (Preparation s f) := by
  simp only [preparation_iff model X events solutions target information full equations]
  constructor
  · rintro ⟨p,ready,solvable,witness,_⟩
    exact ⟨ready,solvable,⟨witness⟩⟩
  · rintro ⟨ready,solvable,⟨witness⟩⟩
    exact ⟨events.witnesses.symm (encodeWitness State Firing Preparation f witness),
      ready,solvable,witness,events.witnesses.apply_symm_apply _⟩

universe uOcc

def effectReady {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] (E : EffectCore X O State Firing)
    (s : State) (f : Firing s) : Prop :=
  E.Shapes f ∧ MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : O => ()) (E.present s)
    ((E.selection f).commit (T := Unit))

include full equations in
theorem effect_preparation_iff {O : Type uOcc} [DecidableEq O] (E : EffectCore X O State Firing)
    (code : HOLAdmissionCoding.Coding model State Firing (HOLPreparedEffectEncoding.Witness E))
    {s : State} (f : Firing s) (p : HOL.Ty.denote.{0,w+1} model.Carrier witnessType) :
    (model.constDen HOLLoadedSolutionPreparation.symbol (readyValue model code (effectReady E))
      (solutionsValue model X code solutions E.target E.information) (HOLAdmissionCoding.preparationValue model code)
      (code.states.symm (some s)) (code.firings.symm (encodeFiring State Firing f)) p).down ↔
      (HOLAdmissionCoding.preparationValue model code (code.states.symm (some s))
        (code.firings.symm (encodeFiring State Firing f)) p).down := by
  rw [preparation_iff model X code solutions E.target E.information full equations,
    HOLAdmissionCoding.preparation_at_iff]
  constructor
  · rintro ⟨_,_,witness⟩
    exact witness
  · rintro ⟨witness,same⟩
    exact ⟨⟨witness.1,witness.2.1⟩,witness.2.2,witness,same⟩

include full equations in
theorem effect_guard_iff {O : Type uOcc} [DecidableEq O] (E : EffectCore X O State Firing)
    (code : HOLAdmissionCoding.Coding model State Firing (HOLPreparedEffectEncoding.Witness E))
    (holds : {s : State} → (f : Firing s) → (b : Obj) → Hom (E.target f) b → Prop)
    {s : State} (f : Firing s) (p : E.Prepares f) :
    (model.constDen HOLLoadedGuardProfile.symbol (solutionsValue model X code solutions E.target E.information)
      (holdsValue model code solutions E.target (fun _ f _ => holds f))
      (code.states.symm (some s)) (code.firings.symm (encodeFiring State Firing f))
      (code.witnesses.symm (encodeWitness State Firing (HOLPreparedEffectEncoding.Witness E) f p))).down ↔
      E.guardAdmission holds f p :=
  guard_iff model X code solutions E.target E.information full equations (fun _ f _ => holds f) f p

#print axioms guard_iff
#print axioms preparation_exists_iff
#print axioms effect_guard_iff
#print axioms effect_preparation_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLGuardSpecialization
