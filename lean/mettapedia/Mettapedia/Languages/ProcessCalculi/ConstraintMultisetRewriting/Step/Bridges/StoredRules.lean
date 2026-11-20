import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Execution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Transitions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Bisimulation

/-!
# Stored rule interpretation composes through actual operational arrows

The existing stored-rule and interpreter steps supply a strong comparison
on the closed fragment. The interpreter remains the actual infinite uniform
family, with rules for all shapes. The representation retains the store and
its solution-dependent tags; neither event multiplicity nor finite
executability follows from this successor correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.StoredRules

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open FragmentsOfTheStep.TransitionMaps RuleSyntax RuleSyntax.RulesAsRows

variable {O : Type*} [DecidableEq O] {F : Set (Rule Tm)} (closed : ClosedFragment F)

include closed

theorem strong : IsBisimulation (StoredSucc (O := O) F) InterpSucc (Represents F) :=
  ⟨fun represented stepped => (bisimulation closed represented).1 _ stepped,
    fun represented stepped => (bisimulation closed represented).2 _ stepped⟩

def correspondence : OperationalCorrespondence
    (Execution.theory (RuleSyntax.step X O Ext (Stored F)).toStep)
    (Execution.theory (RuleSyntax.step X O Ext U).toStep) :=
  Transitions.correspondence (strong (O := O) closed)

def progress : Progress.Certificate (correspondence (O := O) closed).toOperationalReadback :=
  Transitions.progress (strong (O := O) closed)

/-- Composition uses the very same interpreter state as its middle state.
The next comparison must justify its own observation and progress laws. -/
def thenCorrespondence {Target : GSLT}
    (later : OperationalCorrespondence
      (Execution.theory (RuleSyntax.step X O Ext U).toStep) Target) :
    OperationalCorrespondence
      (Execution.theory (RuleSyntax.step X O Ext (Stored F)).toStep) Target :=
  (correspondence closed).comp later

theorem normalization_iff {s u : State Tm O} (represented : Represents F s u) :
    Acc (fun after before => StoredSucc F before after) s ↔
      Acc (fun after before => InterpSucc before after) u :=
  Transitions.normalization_iff (strong closed) represented

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.StoredRules

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.StoredRules.correspondence
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.StoredRules.normalization_iff
