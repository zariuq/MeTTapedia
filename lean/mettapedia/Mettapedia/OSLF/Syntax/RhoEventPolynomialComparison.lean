import Mettapedia.OSLF.Syntax.EventGraphNullaryPolynomial
import Mettapedia.OSLF.Syntax.RhoFreePresheafEvents
import Mettapedia.OSLF.Syntax.RhoSourceEventComparison
import Mettapedia.OSLF.Syntax.FreePresheafEventImage

/-!
# Rho COMM and Drop as nullary operational constructors

The actual source-equation rho state presheaf is shared by the COMM-only and
COMM-plus-Drop profiles. The general event-fibre/polynomial equivalence
transports their retained firing objects to nullary rule trees. The Drop
judgment has a tree in the latter profile and none in the former, so the
source equations alone do not derive Drop from COMM.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoEventPolynomialComparison

open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoFreePresheafEvents
open Mettapedia.OSLF.Binding.RhoSourceEventComparison
open Mettapedia.OSLF.Binding.ContextualEquationClassEvents
open Mettapedia.OSLF.Binding.FreePresheafEventExtension
open Mettapedia.OSLF.Binding.EventGraphNullaryPolynomial
open Mettapedia.OSLF.Binding.FreePresheafEventImage.RhoExample

/-- The same equation-class states with only the authored COMM firings. -/
def commEvents : Graph states where
  edge := presentationEventPresheaf rhoSourceComm.toUnpositioned Srt.pr
  source := presentationSourceNatural rhoSourceComm.toUnpositioned Srt.pr
  target := presentationTargetNatural rhoSourceComm.toUnpositioned Srt.pr

/-- The equation-class endpoint pair tested by the source Drop rule. -/
def dropPair : states.obj closedContext × states.obj closedContext :=
  (Quotient.mk _ dropChan, Quotient.mk _ nilP)

/-- A genuine authored Drop firing becomes a nullary constructor tree,
retaining the underlying occurrence in the event fibre. -/
theorem source_drop_tree_exists :
    Nonempty ((rules sourceEvents).Fix () ⟨closedContext, dropPair⟩) := by
  obtain ⟨event, before, after⟩ := source_drop_has_class_event
  exact ⟨eventTree sourceEvents ⟨event, before, after⟩⟩

/-- The COMM-only profile has no constructor tree at the Drop pair. This is
the source-faithful obstruction to reducing Drop to COMM under the current
authored equations. -/
theorem comm_only_has_no_drop_tree :
    ¬ Nonempty ((rules commEvents).Fix () ⟨closedContext, dropPair⟩) := by
  rintro ⟨tree⟩
  let event := treeEvent commEvents tree
  exact source_drop_has_no_comm_event ⟨event.1, event.2⟩

/-- Duplicating the authored COMM rule creates two distinct constructor trees
with exactly the same equation-class endpoints. The endpoint predicate sees
only one pair, while the rule trees retain both occurrences. -/
theorem duplicated_comm_has_distinct_trees :
    ∃ pair :
        (termQPresheaf duplicatedCommunication.eqs Srt.pr).obj closedContext ×
          (termQPresheaf duplicatedCommunication.eqs Srt.pr).obj closedContext,
      ∃ first second :
          (rules duplicatedGraph).Fix () ⟨closedContext, pair⟩,
        first ≠ second := by
  obtain ⟨⟨index, firing⟩, _, _⟩ :=
    ContextualEquationClassEvents.RhoExample.source_order_communication_event
  fin_cases index
  let first : PresentationInstance duplicatedCommunication [] Srt.pr :=
    ⟨⟨0, by decide⟩, firing⟩
  let second : PresentationInstance duplicatedCommunication [] Srt.pr :=
    ⟨⟨1, by decide⟩, firing⟩
  let pair :
      (termQPresheaf duplicatedCommunication.eqs Srt.pr).obj closedContext ×
        (termQPresheaf duplicatedCommunication.eqs Srt.pr).obj closedContext :=
    (Quotient.mk _ first.source, Quotient.mk _ first.target)
  let firstFiber : EndpointFiber duplicatedGraph closedContext pair :=
    ⟨first, rfl, rfl⟩
  let secondFiber : EndpointFiber duplicatedGraph closedContext pair :=
    ⟨second, rfl, rfl⟩
  have distinct : first ≠ second := by
    intro equal
    have indices := congrArg Sigma.fst equal
    have impossible : (0 : Fin 2) = 1 := indices
    cases impossible
  exact ⟨pair, eventTree duplicatedGraph firstFiber,
    eventTree duplicatedGraph secondFiber,
    distinct_trees_of_distinct_events duplicatedGraph firstFiber secondFiber distinct⟩

#print axioms source_drop_tree_exists
#print axioms comm_only_has_no_drop_tree
#print axioms duplicated_comm_has_distinct_trees

end Mettapedia.OSLF.Binding.RhoEventPolynomialComparison
