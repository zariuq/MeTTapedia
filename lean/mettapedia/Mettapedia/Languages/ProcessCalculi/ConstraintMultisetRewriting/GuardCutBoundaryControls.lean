import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutBindingControls

/-!
# Consistency and the exact boundary of a guard's observation

Current tells belong to its ask problem; current consumption does not belong
to its observation world. An inconsistent problem can entail a guard
vacuously but still cannot supply a source firing or a cut certificate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutBoundaryControls

open Mettapedia.Logic.LP
open LinearConnectionLayout
open GuardedProcessCounterexamples (sig A X a b pTok emptyWorld lab)

def emptySelection : Selection Nat := ⟨[], [], []⟩
def currentTell : RuleInstance (Term sig) := ⟨[], [], [(X, a)], [.equal X a], []⟩

theorem current_tell_can_discharge_its_own_guard :
    emptySelection.Valid A lab currentTell emptyWorld := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl, by decide +kernel,
    ⟨Subst.single 0 a, ?_⟩, ?_⟩
  · intro equation member
    have same : equation = (X, a) := by
      simpa [Selection.problem, Selection.equations, emptySelection, currentTell, emptyWorld] using member
    subst equation
    change (Subst.single 0 a : Subst sig) 0 = a
    exact Subst.single_eq (σ := sig) 0 a
  · intro check member assignment solved
    have same : check = .equal X a := by simpa [currentTell] using member
    subst check
    exact solved (X, a) (by simp [Selection.problem, Selection.equations, emptySelection, currentTell, emptyWorld])

def takingAbsent : RuleInstance (Term sig) := ⟨[pTok], [], [], [.absent pTok], []⟩
def taking : Selection Nat := ⟨[4], [], []⟩
def pWorld : Configuration (Term sig) Nat := ⟨[], {4}⟩

theorem consuming_the_guarded_row_does_not_make_it_absent :
    ¬ taking.Valid A lab takingAbsent pWorld := by
  intro valid
  obtain ⟨assignment, solved⟩ := valid.consistent
  have holds := valid.checks (.absent pTok) (by simp [takingAbsent]) assignment solved
  exact holds 4 (by simp [pWorld]) rfl

def contradictory : RuleInstance (Term sig) := ⟨[], [], [(X, a), (X, b)], [.absent pTok], []⟩
def inconsistentEvents : Fin 1 → Event (Term sig) Nat := fun _ => (contradictory, emptySelection)
def emptyCuts : Fin 1 → Finset (Fin 1) := fun _ => ∅

theorem contradiction_from_tells (assignment : Subst sig)
    (solved : A.Models assignment contradictory.tell) : False := by
  have first := solved (X, a) (by simp [contradictory])
  have second := solved (X, b) (by simp [contradictory])
  have one : assignment 0 = a := first
  have two : assignment 0 = b := second
  exact GuardedProcessCounterexamples.a_ne_b (one.symm.trans two)

theorem inconsistent_ask_is_vacuous :
    GuardedCutSemantics.Asks A lab emptyWorld inconsistentEvents emptyCuts := by
  intro current _check _member assignment solved
  have told := (A.models_append ..).mp solved |>.2
  have same : ConditionalComposite.addedEquations lab
      (inconsistentEvents current).1 (inconsistentEvents current).2 = contradictory.tell := rfl
  rw [same] at told
  exact False.elim (contradiction_from_tells assignment told)

theorem inconsistent_conditions_refused (assignment : Subst sig) :
    ¬ GuardCutSequentialization.Conditions A assignment lab emptyWorld inconsistentEvents := by
  intro conditions
  exact contradiction_from_tells assignment (conditions.connections 0)

theorem inconsistent_source_firing_refused :
    ¬ emptySelection.Valid A lab contradictory emptyWorld := by
  intro valid
  obtain ⟨assignment, solved⟩ := valid.consistent
  have told : A.Models assignment contradictory.tell := by
    simpa [Selection.problem, Selection.equations, emptySelection, emptyWorld] using solved
  exact contradiction_from_tells assignment told

section Empty

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

def noEvents : Fin 0 → Event T O := Fin.elim0
def noEventCuts : Fin 0 → Finset (Fin 0) := Fin.elim0

theorem empty_order_computed :
    GuardCutOrders.order? (noEvents (T := T) (O := O)) noEventCuts = some [] := by rfl

theorem empty_conditions_iff_model (action : SubstitutionAction T S) (assignment : S)
    (labels : O → T) (before : Configuration T O) :
    GuardCutSequentialization.Conditions action assignment labels before noEvents ↔
      action.Models assignment before.equations := by
  constructor
  · exact fun conditions => conditions.incoming
  · intro model
    refine ⟨fun event => Fin.elim0 event, ?_, ?_, ?_, fun event => Fin.elim0 event,
      fun event => Fin.elim0 event, model, fun event => Fin.elim0 event⟩
    · simp [UnorderedOccurrenceConnections.roster]
    · simp [UnorderedOccurrenceConnections.roster]
    · simp [LinearConnectionLayout.made, UnorderedOccurrenceConnections.roster]

end Empty

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutBoundaryControls
