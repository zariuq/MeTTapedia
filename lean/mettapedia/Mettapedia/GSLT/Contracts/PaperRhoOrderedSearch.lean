import Mettapedia.GSLT.Contracts.PaperRhoAdequacy
import Mettapedia.GSLT.Contracts.RefinedStateExploration
import Mettapedia.GSLT.Contracts.RhoHereditaryLayout

/-!
# State keys for the paper-facing rho transition graph

The paper-facing relation already has EQUIV. This is the exact
step-transport witness required to admit any state-key partition
finer than its process equations. Two serializers can therefore
use different orders while preserving all terminal observations
of congruence classes.

This is a contract for implementations of the paper-facing
transition graph. An engine that implements only one-level syntactic
COMM must separately prove completeness of matching on its chosen
representation. No bounded budget or deterministic scheduler is
claimed invariant here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.PaperRho.OrderedSearch

open Mettapedia.GSLT.Contracts.RefinedStateExploration
open Relation (ReflTransGen)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern rhoReflectivePresentation)
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (canonicalize canonicalizeByDepths)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep (RhoStep)
open PatternBoundary (encodeProcess)

def structuralEquations : Setoid Process :=
  ⟨Congruence, ⟨Congruence.refl, Congruence.symm, Congruence.trans⟩⟩

theorem transports : StepTransport structuralEquations Reduction := by
  intro a b result same step
  exact ⟨result, .equiv (.symm same) step (.refl _), Congruence.refl _⟩

variable {Key OtherKey Answer : Type*}

theorem observes_terminal_classes (coding : Keys Process Key)
    (fine : coding.FinerThan structuralEquations)
    (observe : Quotient structuralEquations → Answer) (source : Process) (answer : Answer) :
    (∃ result, ReflTransGen (coding.step Reduction) (coding.encode source) result ∧
      terminal (coding.step Reduction) result ∧
        observe (Quotient.mk _ (coding.representative result)) = answer) ↔
    (∃ target, ReflTransGen Reduction source target ∧ terminal Reduction target ∧
      observe (Quotient.mk _ target) = answer) := by
  exact terminal_outcomes_iff coding fine transports
    (fun state => observe (Quotient.mk structuralEquations state))
    (fun {_ _} equal => congrArg observe (Quotient.sound (s := structuralEquations) equal))
    source answer

theorem reorder_terminal_classes (first : Keys Process Key) (second : Keys Process OtherKey)
    (fineFirst : first.FinerThan structuralEquations) (fineSecond : second.FinerThan structuralEquations)
    (observe : Quotient structuralEquations → Answer) (source : Process) (answer : Answer) :
    (∃ result, ReflTransGen (first.step Reduction) (first.encode source) result ∧
      terminal (first.step Reduction) result ∧
        observe (Quotient.mk _ (first.representative result)) = answer) ↔
    (∃ result, ReflTransGen (second.step Reduction) (second.encode source) result ∧
      terminal (second.step Reduction) result ∧
        observe (Quotient.mk _ (second.representative result)) = answer) :=
  (observes_terminal_classes first fineFirst observe source answer).trans
    (observes_terminal_classes second fineSecond observe source answer).symm

/-- Closure is not sacrificed when representatives change. -/
theorem representative_keeps_scope (coding : Keys Process Key)
    (fine : coding.FinerThan structuralEquations)
    {source : Process} (closed : ScopedProcess 0 source) :
    ScopedProcess 0 (coding.representative (coding.encode source)) :=
  (Congruence.scoped_iff (coding.representative_equivalent fine source) 0).mpr closed

/-- The authored step at an arbitrarily ordered canonical representative
has exactly the paper-facing successor classes of the closed term.
The raw step actually runs on that ordered term, not on its default
reserialization. -/
theorem keyed_paper_reduction_iff {Rank : Type} [LinearOrder Rank]
    (rank : Nat → Nat → Pattern → Rank) (available scope : Nat)
    {p q : Process} (closed : ScopedProcess 0 p) :
    Reduction p q ↔
      ∃ result,
        RhoStep (canonicalizeByDepths rank rhoReflectivePresentation available scope (encodeProcess p)) result ∧
        canonicalize rhoReflectivePresentation result = canonicalize rhoReflectivePresentation (encodeProcess q) :=
  (Adequacy.reduction_iff_rhoStep closed).trans
    (RhoHereditaryLayout.keyed_successors_iff rank available scope (encodeProcess p)
      (canonicalize rhoReflectivePresentation (encodeProcess q))).symm

namespace LayoutControls

open Separation (base wrapped)

private def aliasRedex : Process :=
  .par (.send wrapped .zero) (.receive base (.drop (.bound 0)))

/-- Even a tie on every rank does not remove the alias COMM. -/
theorem tied_layout_keeps_communication :
    ∃ result,
      RhoStep (canonicalizeByDepths (fun _ _ _ => (0 : Nat)) rhoReflectivePresentation 0 0
        (encodeProcess aliasRedex)) result ∧
      canonicalize rhoReflectivePresentation result = canonicalize rhoReflectivePresentation (encodeProcess .zero) := by
  have sealed : ScopedProcess 0 aliasRedex :=
    .par (.send (.literal (.drop (.literal .zero))) .zero)
      (.receive (.literal .zero) (.drop (.bound (by decide))))
  exact (keyed_paper_reduction_iff (fun _ _ _ => (0 : Nat)) 0 0 sealed).mp
    Controls.alias_communicates.reduction

end LayoutControls

#print axioms transports
#print axioms observes_terminal_classes
#print axioms reorder_terminal_classes
#print axioms representative_keeps_scope
#print axioms keyed_paper_reduction_iff
#print axioms LayoutControls.tied_layout_keeps_communication

end Mettapedia.GSLT.Contracts.PaperRho.OrderedSearch
