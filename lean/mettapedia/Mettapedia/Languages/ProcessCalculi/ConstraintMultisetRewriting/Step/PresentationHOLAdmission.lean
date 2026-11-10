import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationSourceRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLAdmissionModel

/-! # Authored transform execution and the loaded HOL event predicate

The generic authored root keeps the selected candidate. The concrete scalar
source route uses the existing parse, routing and lowering evidence. Backward
source realization requires the declared policy's canonical coverage; raw
source provenance is retained before the explicit event erasure.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.HOLAdmission

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Engine
open Interface
open HOLAdmissionCoding HOLPreparationEncoding

universe w uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (E : EffectCore X O State Firing) (allow : E.Admission)
  (presentation : Encoding State Firing) (decision : Decisions E allow)
  (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
  (code : Coding model State Firing (HOLPreparedEffectEncoding.Witness E))
  (full : model.FullDomains)
  (equations : ∀ fact ∈ HOLAdmissionDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)

include full equations in
theorem authored_execution_iff {s t : State} (f : Firing s) :
    atState (presentation.state.view (sort := ()) t) ∈ rewriteStepWithPremisesUsing
      (effectQueries E allow presentation decision).relations authoredLanguage
      (request (presentation.state.view (sort := ()) s) (presentation.firing.view (sort := ()) ⟨s,f⟩)) ↔
      ∃ p, (model.constDen HOLLoadedAdmittedEvent.symbol (preparationValue model code)
        (resultValue model code (HOLPreparedEffectEncoding.next E))
        (permissionValue model code (HOLPreparedEffectEncoding.permits E allow))
        (code.states.symm (some s)) (code.firings.symm (encodeFiring State Firing f)) p (code.states.symm (some t))).down := by
  rw [authored_root_execution, execution_iff_prepared]
  constructor
  · rintro ⟨p, permitted, target⟩
    refine ⟨code.witnesses.symm (encodeWitness State Firing (HOLPreparedEffectEncoding.Witness E) f p), ?_⟩
    apply (HOLAdmissionEventSpecialization.admitted_raw_iff model code full equations
      (HOLPreparedEffectEncoding.next E) (HOLPreparedEffectEncoding.permits E allow)
      (some s) (some t) (encodeFiring State Firing f)
      (encodeWitness State Firing (HOLPreparedEffectEncoding.Witness E) f p)).mpr
    exact ⟨prepares_encoded State Firing _ f p, (congrArg some target).symm, permitted⟩
  · rintro ⟨raw, admitted⟩
    have facts := (HOLAdmissionEventSpecialization.admitted_raw_iff model code full equations
      (HOLPreparedEffectEncoding.next E) (HOLPreparedEffectEncoding.permits E allow)
      (some s) (some t) (encodeFiring State Firing f) (code.witnesses raw)).mp
        (by simpa only [Equiv.symm_apply_apply] using admitted)
    obtain ⟨p, same⟩ := (prepares_iff State Firing (HOLPreparedEffectEncoding.Witness E) f (code.witnesses raw)).mp facts.1
    refine ⟨p, ?_, ?_⟩
    · simpa only [same, HOLPreparationEncoding.permission_encoded, HOLPreparedEffectEncoding.permits] using facts.2.2
    · simpa only [same, result_encoded, Option.some.injEq, HOLPreparedEffectEncoding.next] using facts.2.1.symm

#print axioms authored_execution_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.HOLAdmission

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Source.HOLAdmission

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Interface Payloads OccurrenceProfile

universe w

variable (label : Nat → Term) (decision : Decisions (effect label) (admission label))
  (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
  (code : HOLAdmissionCoding.Coding model State (fun _ => Candidate) (HOLPreparedEffectEncoding.Witness (effect label)))
  (full : model.FullDomains)
  (equations : ∀ fact ∈ HOLAdmissionDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)

abbrev Packet (source target : State) := HOLAdmissionEventSpecialization.EventPacket model code
  (HOLPreparedEffectEncoding.next (effect label)) (HOLPreparedEffectEncoding.permits (effect label) (admission label)) source target

include full equations in
def interpret {keep : ParsePolicy} {source target : State} (event : SelectedEvent label decision keep source target) :
    Packet label model code source target :=
  HOLAdmissionEventSpecialization.native_event_equiv model full equations (effect label) code (admission label)
    source target (event.abstract label decision)

include full equations in
theorem interpreted_candidate {keep : ParsePolicy} {source target : State}
    (event : SelectedEvent label decision keep source target) :
    code.firings (interpret label decision model code full equations event).1.1 =
      HOLPreparationEncoding.encodeFiring State (fun _ => Candidate) (s := source) event.candidate :=
  HOLAdmissionEventSpecialization.native_event_firing model full equations (effect label) code (admission label)
    (event.abstract label decision)

include full equations in
theorem source_realization {keep : ParsePolicy} (coverage : CanonicalCoverage label keep)
    {source target : State} (packet : Packet label model code source target) :
    ∃ event : SelectedEvent label decision keep source target,
      interpret label decision model code full equations event = packet := by
  let equivalence := HOLAdmissionEventSpecialization.native_event_equiv model full equations
    (effect label) code (admission label) source target
  obtain ⟨event, agrees, _⟩ := lift_event label decision coverage (equivalence.symm packet)
  refine ⟨event, ?_⟩
  change equivalence (event.abstract label decision) = packet
  rw [agrees, Equiv.apply_symm_apply]

include full equations in
theorem all_parses_realization {source target : State} (packet : Packet label model code source target) :
    ∃ event : SelectedEvent label decision allParses source target,
      interpret label decision model code full equations event = packet :=
  source_realization label decision model code full equations (allParses_coverage label) packet

theorem constructed_source_interpretation
    (other : TypeFamilySemantics.OperatorFamilies.{0}) (prior : TypeFamilySemantics.Assignment.{0}) :
    ∃ (actual : HOL.HenkinModel.{0,0,1} AtomicTy Symbol)
      (events : HOLAdmissionCoding.Coding actual State (fun _ => Candidate) (HOLPreparedEffectEncoding.Witness (effect label)))
      (actualFull : actual.FullDomains)
      (actualEquations : ∀ fact ∈ HOLAdmissionDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
        ∃ formula : HOL.ClosedFormula Symbol,
          TranslatesCompositionally []
            ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ actual.models formula),
      ∀ keep, CanonicalCoverage label keep → ∀ source target,
        Function.Surjective (@interpret label decision actual events actualFull actualEquations keep source target) := by
  obtain ⟨actual,frames,occurrences,events,agreement⟩ := HOLAdmissionModel.constructed_agreement (effect label) other prior
  refine ⟨actual,events,agreement.effects.fullDomains,agreement.definitions,?_⟩
  intro keep coverage source target packet
  exact source_realization label decision actual events agreement.effects.fullDomains agreement.definitions coverage packet

#print axioms interpreted_candidate
#print axioms source_realization
#print axioms all_parses_realization
#print axioms constructed_source_interpretation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Source.HOLAdmission
