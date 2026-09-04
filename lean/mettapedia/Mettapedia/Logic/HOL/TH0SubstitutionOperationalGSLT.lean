import Mettapedia.GSLT.Core.ProofRelevantGSLT
import Mettapedia.Logic.HOL.TH0SyntacticUnifierService

/-!
# TH0 substitution as a proof-relevant operational GSLT

The portable TH0 packet is a representation boundary.  This module gives its
intrinsic simultaneous-substitution algebra an operational interpretation.
At one fixed object type, a state is a typed term together with its context;
an event is an exact typed substitution taking the source term to the target
term.  Event composition is inherited from substitution composition.

The proposition-valued GSLT step remembers only that such an event exists.
The displayed evidence fibre retains which substitution was used.  Two
different substitutions can therefore induce the same semantic step without
becoming equal as evidence.  This is the concrete separation needed by the
mode-theory discussion: proof-relevant operational routes do not by themselves
imply proof-relevant comparisons between translations.

A syntactic unifier is represented operationally by a cospan: its left and
right terms are both sent by the checked substitution to one common target
term.  A future beta-eta-aware unifier may reuse this shape after replacing
literal target equality by a separately justified conversion relation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.TH0SubstitutionOperationalGSLT

open Mettapedia.GSLT
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.TH0SyntacticUnifierService
open Mettapedia.TypeTheory.TH0InterchangeAlgorithmBoundary
open Mettapedia.TypeTheory.TH0SimultaneousSubstitutionService

/-! ## States and proof-relevant substitution events -/

/-- An intrinsically typed term with an existentially packed context.  The
object type remains fixed across substitution. -/
structure State (type : Ty String) where
  context : Ctx String
  term : Term Constant context type

/-- One exact simultaneous-substitution occurrence.  Different substitutions
remain different evidence even when they have the same endpoints. -/
structure Event {type : Ty String} (source target : State type) where
  substitution : Subst Constant source.context target.context
  result : subst substitution source.term = target.term

namespace Event

/-- Identity substitution is the reflexive operational event. -/
def identity {type : Ty String} (state : State type) : Event state state where
  substitution := Subst.id
  result := th0_substitution_identity state.term

/-- Sequential operational events compose by simultaneous-substitution
composition, not by concatenating packet histories. -/
def comp {type : Ty String} {source middle target : State type}
    (first : Event source middle) (second : Event middle target) :
    Event source target where
  substitution := Subst.comp second.substitution first.substitution
  result := by
    rw [← th0_substitution_composition first.substitution
      second.substitution source.term]
    rw [first.result, second.result]

/-- A pointwise-observable difference between substitutions distinguishes the
corresponding event occurrences. -/
theorem ne_of_apply_ne {type : Ty String} {source target : State type}
    (first second : Event source target)
    {variableType : Ty String}
    (termVariable : Var source.context variableType)
    (different : first.substitution termVariable ≠
      second.substitution termVariable) :
    first ≠ second := by
  intro equal
  apply different
  exact congrArg (fun event => event.substitution termVariable) equal

end Event

/-! ## Extensional GSLT and its displayed evidence -/

/-- The extensional operational theory observes existence of a typed
substitution event. -/
def theory (type : Ty String) : GSLT where
  Term := State type
  equations :=
    { r := Eq
      iseqv :=
        { refl := fun _ => rfl
          symm := fun equality => equality.symm
          trans := fun first second => first.trans second } }
  rewrites := fun source target => Nonempty (Event source target)
  rewrites_resp_left := by
    intro source source' target sourceEqual step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step targetEqual
    subst target'
    exact step

/-- The full operational presentation displays exact substitutions above the
proposition-valued step relation. -/
def stepEvidence (type : Ty String) : StepEvidence (theory type) where
  Evidence := Event
  erases_iff := by
    intro source target
    rfl

def system (type : Ty String) : ProofRelevantGSLT where
  theory := theory type
  steps := stepEvidence type

theorem identity_erases_to_step {type : Ty String} (state : State type) :
    (theory type).Step state state :=
  (stepEvidence type).erase (Event.identity state)

theorem composition_erases_to_step
    {type : Ty String} {source middle target : State type}
    (first : Event source middle) (second : Event middle target) :
    (theory type).Step source target :=
  (stepEvidence type).erase (first.comp second)

/-! ## Unification is an operational cospan -/

namespace UnifierOps

variable {problem : Problem}

def leftState (unifier : Unifier problem) : State problem.type.decode :=
  ⟨problem.source, unifier.left⟩

def rightState (unifier : Unifier problem) : State problem.type.decode :=
  ⟨problem.source, unifier.right⟩

def apex (unifier : Unifier problem) : State problem.type.decode :=
  ⟨problem.target,
    subst unifier.substitution.toSubst unifier.left⟩

def leftEvent (unifier : Unifier problem) :
    Event (leftState unifier) (apex unifier) where
  substitution := unifier.substitution.toSubst
  result := rfl

def rightEvent (unifier : Unifier problem) :
    Event (rightState unifier) (apex unifier) where
  substitution := unifier.substitution.toSubst
  result := unifier.equal.symm

theorem both_legs_are_semantic_steps (unifier : Unifier problem) :
    (theory problem.type.decode).Step (leftState unifier) (apex unifier) ∧
      (theory problem.type.decode).Step (rightState unifier) (apex unifier) :=
  ⟨⟨leftEvent unifier⟩, ⟨rightEvent unifier⟩⟩

end UnifierOps

/-- A checked certificate constructs an intrinsic unifier together with its
two operational legs.  Search strategy and packet representation are absent
from the statement. -/
theorem accepted_has_operational_cospan
    {problem : Problem} {certificate : SubstitutionPacket}
    (accepted : check problem certificate = true) :
    ∃ unifier : Unifier problem,
      (theory problem.type.decode).Step
          (UnifierOps.leftState unifier) (UnifierOps.apex unifier) ∧
      (theory problem.type.decode).Step
          (UnifierOps.rightState unifier) (UnifierOps.apex unifier) := by
  obtain ⟨unifier⟩ := check_sound accepted
  exact ⟨unifier, UnifierOps.both_legs_are_semantic_steps unifier⟩

/-! ## Positive and negative controls -/

namespace Canary

open TH0SyntacticUnifierService.Canary

/-- A constant open term: changing its unused variable image does not change
the target term. -/
def constantSource : State individual :=
  ⟨[individual], sourceA⟩

def constantTarget : State individual :=
  ⟨[], closedA⟩

def eventA : Event constantSource constantTarget where
  substitution := substituteA
  result := rfl

def eventB : Event constantSource constantTarget where
  substitution := substituteB
  result := rfl

theorem eventA_ne_eventB : eventA ≠ eventB := by
  apply Event.ne_of_apply_ne eventA eventB
    (Var.vz : Var [individual] individual)
  intro equal
  have packetEqual := congrArg encodeTerm equal
  simp [eventA, eventB, substituteA, substituteB, Subst.single,
    closedA, closedB, constantA, constantB, encodeTerm] at packetEqual

/-- Rich evidence lives above one proposition-valued semantic step. -/
theorem proof_relevant_fibre_over_thin_step :
    (theory individual).Step constantSource constantTarget ∧
      ¬ Subsingleton (Event constantSource constantTarget) := by
  constructor
  · exact ⟨eventA⟩
  · intro subsingleton
    exact eventA_ne_eventB (subsingleton.elim eventA eventB)

/-- The concrete accepted packet from the unifier service has the advertised
operational cospan. -/
theorem accepted_packet_has_cospan :
    ∃ unifier : Unifier baseProblem,
      (theory baseProblem.type.decode).Step
          (UnifierOps.leftState unifier) (UnifierOps.apex unifier) ∧
        (theory baseProblem.type.decode).Step
          (UnifierOps.rightState unifier) (UnifierOps.apex unifier) :=
  accepted_has_operational_cospan certificateA_accepted

end Canary

/-! ## Audited theorem crowns -/

#print axioms Event.ne_of_apply_ne
#print axioms identity_erases_to_step
#print axioms composition_erases_to_step
#print axioms UnifierOps.both_legs_are_semantic_steps
#print axioms accepted_has_operational_cospan
#print axioms Canary.eventA_ne_eventB
#print axioms Canary.proof_relevant_fibre_over_thin_step
#print axioms Canary.accepted_packet_has_cospan

end Mettapedia.Logic.HOL.TH0SubstitutionOperationalGSLT
