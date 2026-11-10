import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLGuardModel
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFramesControls

/-! # Solvability, guard truth and profile-domain controls

The frame has two morphism representatives with the same identity action.
An unsolvable information store makes a false guard vacuously entailed but
still cannot prepare. A representative-sensitive guard sees both maps.
Profile inclusion need not hold outside the preparation domain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLGuardControls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLFramesControls (frame terms maps)
open HOLAdmissionTypes HOLPreparationEncoding HOLSolutionCoding

def target {s : Unit} (_ : Unit) : Unit := s
def bad {s : Unit} (_ : Unit) : EquationStore (terms s) := [((0 : Nat),(1 : Nat))]
def good {s : Unit} (_ : Unit) : EquationStore (terms s) := [((0 : Nat),(0 : Nat))]
def ready (_ _ : Unit) : Prop := ([] : List Nat).Nodup
def forbid (_ _ _ _ : Unit) (_ : Bool) : Prop := False
def preserveZero (_ _ _ b : Unit) (sigma : maps () b) : Prop := frame.act (a := ()) (b := b) sigma (0 : Nat) = (0 : Nat)
def firstRepresentative (_ _ _ _ : Unit) (sigma : Bool) : Prop := sigma = false

theorem bad_unsolvable : ¬frame.Solvable (a := ()) (bad (s := ()) ()) := by
  rintro ⟨b,sigma,solved⟩
  have impossible : (0 : Nat) = 1 := solved ((0 : Nat),(1 : Nat)) (List.mem_singleton_self _)
  omega

theorem good_solvable : frame.Solvable (a := ()) (good (s := ()) ()) := by
  refine ⟨(),false,?_⟩
  intro pair member
  obtain rfl := List.mem_singleton.mp member
  rfl

universe w

abbrev Events (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  HOLAdmissionCoding.Coding model Unit (fun _ => Unit) (fun _ _ => Unit)

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (events : Events model) (solutions : Coding model Unit maps)

def preparation (information : {s : Unit} → Unit → EquationStore (terms s)) : HOL.Ty.denote.{0,w+1} model.Carrier .prop :=
  model.constDen HOLLoadedSolutionPreparation.symbol (readyValue model events ready)
    (solutionsValue model frame events solutions (fun {s} f => @target s f) (fun {s} f => @information s f)) (HOLAdmissionCoding.preparationValue model events)
    (events.states.symm (some ())) (events.firings.symm (encodeFiring Unit (fun _ => Unit) (s := ()) ()))
    (events.witnesses.symm (encodeWitness Unit (fun _ => Unit) (fun _ _ => Unit) (s := ()) () ()))

def guard (information : {s : Unit} → Unit → EquationStore (terms s))
    (holds : Unit → Unit → Unit → Unit → Bool → Prop) : HOL.Ty.denote.{0,w+1} model.Carrier .prop :=
  model.constDen HOLLoadedGuardProfile.symbol (solutionsValue model frame events solutions (fun {s} f => @target s f) (fun {s} f => @information s f))
    (holdsValue model events solutions (fun {s} f => @target s f) holds) (events.states.symm (some ()))
    (events.firings.symm (encodeFiring Unit (fun _ => Unit) (s := ()) ()))
    (events.witnesses.symm (encodeWitness Unit (fun _ => Unit) (fun _ _ => Unit) (s := ()) () ()))

structure Evidence : Prop where
  readyWithSolution : (preparation model events solutions good).down
  noSolutionRefused : ¬(preparation model events solutions bad).down
  vacuousGuard : (guard model events solutions bad forbid).down
  falseGuardRefused : ¬(guard model events solutions good forbid).down
  invariantGuard : (guard model events solutions good preserveZero).down
  representativesRetained : ¬(guard model events solutions good firstRepresentative).down
  inclusionOnPreparations : (model.constDen HOLLoadedProfileInclusion.symbol
    (HOLAdmissionCoding.preparationValue model events) (fun _ _ _ => ULift.up True)
    (HOLAdmissionCoding.preparationValue model events)).down
  notGlobalInclusion : ¬∀ s f p,
    ((fun _ _ _ => ULift.up True : HOL.Ty.denote.{0,w+1} model.Carrier preparationType) s f p).down →
    (HOLAdmissionCoding.preparationValue model events s f p).down

theorem constructed_controls (other : TypeFamilySemantics.OperatorFamilies.{1})
    (prior : TypeFamilySemantics.Assignment.{1}) :
    ∃ (actual : HOL.HenkinModel.{0,0,2} AtomicTy Symbol) (events : Events actual) (solutions : Coding actual Unit maps),
      Evidence actual events solutions := by
  obtain ⟨actual,same,full,equations⟩ := HOLAdmissionDomains.loaded_model_exists Unit terms maps Nat Unit
    (fun _ => Unit) (fun _ _ => Unit) other prior
  let events := (HOLAdmissionDomains.eventCoding Unit terms maps Nat Unit
    (fun _ => Unit) (fun _ _ => Unit) other prior).changeModel actual same
  let solutions := HOLSolutionCoding.changeModel (HOLGuardModel.initialSolutions Unit terms maps Nat Unit
    (fun _ => Unit) (fun _ _ => Unit) other prior) actual same
  have prepareMeaning (information : {s : Unit} → Unit → EquationStore (terms s)) :
      (preparation actual events solutions information).down ↔ ready () () ∧ frame.Solvable (a := ()) (information (s := ()) ()) := by
    have meaning := HOLGuardSpecialization.preparation_iff actual frame events solutions (fun {s} f => @target s f) (fun {s} f => @information s f) full equations
      ready (s := ()) () (events.witnesses.symm (encodeWitness Unit (fun _ => Unit) (fun _ _ => Unit) (s := ()) () ()))
    refine meaning.trans ?_
    simp only [Equiv.apply_symm_apply]
    constructor
    · exact fun h => ⟨h.1,h.2.1⟩
    · exact fun h => ⟨h.1,h.2,(),trivial⟩
  have guardMeaning (information : {s : Unit} → Unit → EquationStore (terms s))
      (holds : Unit → Unit → Unit → Unit → Bool → Prop) :
      (guard actual events solutions information holds).down ↔ frame.Entails (a := ()) (information (s := ()) ()) (holds () () ()) :=
    HOLGuardSpecialization.guard_iff actual frame events solutions (fun {s} f => @target s f) (fun {s} f => @information s f) full equations holds (s := ()) () ()
  refine ⟨actual,events,solutions,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (prepareMeaning good).mpr ⟨List.nodup_nil,good_solvable⟩
  · exact fun prepared => bad_unsolvable ((prepareMeaning bad).mp prepared).2
  · apply (guardMeaning bad forbid).mpr
    intro b sigma solved
    exact bad_unsolvable ⟨b,sigma,solved⟩
  · intro allowed
    obtain ⟨b,sigma,solved⟩ := good_solvable
    exact (guardMeaning good forbid).mp allowed b sigma solved
  · apply (guardMeaning good preserveZero).mpr
    intro b sigma _
    rfl
  · intro allowed
    have solved : frame.Models (a := ()) (b := ()) true (good (s := ()) ()) := by
      intro pair member
      obtain rfl := List.mem_singleton.mp member
      rfl
    have impossible : true = false := (guardMeaning good firstRepresentative).mp allowed () true solved
    cases impossible
  · have meaning := HOLLoadedProfileInclusion.operational_meaning actual full equations
      (HOLAdmissionCoding.preparationValue actual events) (fun _ _ _ => ULift.up True)
      (HOLAdmissionCoding.preparationValue actual events)
    exact (iff_of_eq (congrArg ULift.down meaning)).mpr (fun _ _ _ prepared _ => prepared)
  · intro global
    have impossible := global (events.states.symm (some ()))
      (events.firings.symm (encodeFiring Unit (fun _ => Unit) (s := ()) ())) (events.witnesses.symm none) trivial
    simp only [HOLAdmissionCoding.preparationValue, Equiv.apply_symm_apply, prepares] at impossible

#print axioms bad_unsolvable
#print axioms constructed_controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLGuardControls
