import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationRetainedRuns

/-!
# Composition of executions preserving an entry interpretation

A protected run is an actual dependent run, a model of its returned knowledge,
and equality on the entry store's retained context. The composition proof uses
the fact that transported context terms remain in the intermediate store. It
does not combine models of unrelated singleton executions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationSemantics (hypotheses)

universe uOcc
variable {judgmentTag arrowTag : Nat} {O : Type uOcc} [DecidableEq O] {s : Store O}

theorem run_toLast_append (run : (machine judgmentTag arrowTag O).Run s) :
    ∀ later : (machine judgmentTag arrowTag O).Run run.last,
      (run.append later).toLast = later.toLast.comp run.toLast := by
  induction run with
  | nil initial =>
    intro later
    change later.toLast = later.toLast.comp (Subst.id rowSig)
    exact (Subst.comp_id_right later.toLast).symm
  | cons f admitted rest ih =>
    intro later
    change (rest.append later).toLast.comp f.answer = later.toLast.comp (rest.toLast.comp f.answer)
    rw [ih later]
    exact Subst.comp_assoc later.toLast rest.toLast f.answer

structure ProtectedRun (judgmentTag arrowTag : Nat) (s : Store O) (caller : Subst rowSig) where
  run : (machine judgmentTag arrowTag O).Run s
  source : Subst rowSig
  known : X.Models (a := PUnit.unit) (b := PUnit.unit) source run.last.knowledge
  agrees : ∀ term ∈ context s, source.applyTerm (run.toLast.applyTerm term) = caller.applyTerm term

namespace ProtectedRun

variable {caller : Subst rowSig}

def start (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge) :
    ProtectedRun judgmentTag arrowTag s caller where
  run := .nil s
  source := caller
  known := known
  agrees term _ := by
    change caller.applyTerm ((Subst.id rowSig).applyTerm term) = caller.applyTerm term
    rw [Subst.applyTerm_id]

noncomputable def single (f : Attempt judgmentTag arrowTag O s)
    (admitted : (machine judgmentTag arrowTag O).Admits f) (source : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) source f.result.knowledge)
    (agrees : ∀ term ∈ context s, source.applyTerm (f.answer.applyTerm term) = caller.applyTerm term) :
    ProtectedRun judgmentTag arrowTag s caller where
  run := .cons f admitted (.nil f.result)
  source := source
  known := known
  agrees term inside := by
    change source.applyTerm (((Subst.id rowSig).comp f.answer).applyTerm term) = caller.applyTerm term
    rw [Subst.comp_id_left]
    exact agrees term inside

noncomputable def append (first : ProtectedRun judgmentTag arrowTag s caller)
    (second : ProtectedRun judgmentTag arrowTag first.run.last first.source) :
    ProtectedRun judgmentTag arrowTag s caller where
  run := first.run.append second.run
  source := second.source
  known := by
    rw [Interface.Step.Run.last_append]
    exact second.known
  agrees term inside := by
    rw [run_toLast_append, Subst.applyTerm_comp]
    exact (second.agrees (first.run.toLast.applyTerm term)
      (run_context_transport first.run term inside)).trans (first.agrees term inside)

theorem append_last (first : ProtectedRun judgmentTag arrowTag s caller)
    (second : ProtectedRun judgmentTag arrowTag first.run.last first.source) :
    (first.append second).run.last = second.run.last := Interface.Step.Run.last_append first.run second.run

theorem append_source (first : ProtectedRun judgmentTag arrowTag s caller)
    (second : ProtectedRun judgmentTag arrowTag first.run.last first.source) :
    (first.append second).source = second.source := rfl

theorem preserves_hypotheses (execution : ProtectedRun judgmentTag arrowTag s caller) (value : Tm)
    (assumed : value ∈ hypotheses (s.dataAt X (b := PUnit.unit) (Subst.id rowSig)) caller) :
    value ∈ hypotheses (execution.run.last.dataAt X (b := PUnit.unit) (Subst.id rowSig)) execution.source :=
  run_preserves_hypotheses execution.run caller execution.source execution.agrees value assumed

end ProtectedRun

#print axioms run_toLast_append
#print axioms ProtectedRun.single
#print axioms ProtectedRun.append
#print axioms ProtectedRun.preserves_hypotheses

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
