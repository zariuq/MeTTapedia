import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutFamilies
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardedProcessCounterexamples

/-!
# An aliased shared read keeps one physical guard-world occurrence

One selected row supplies two ordered read ports. A count guard sees one
occupied occurrence, and the original row survives beside the fresh output.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutSharedReadControls

open Mettapedia.Logic.LP
open LinearConnectionLayout
open GuardedProcessCounterexamples (sig A lab pTok qTok)

def before : Configuration (Term sig) Nat := ⟨[], {4}⟩
def reading : Event (Term sig) Nat :=
  (⟨[], [pTok, pTok], [], [.count pTok 1], [qTok]⟩, ⟨[], [4, 4], [5]⟩)
def events : Fin 1 → Event (Term sig) Nat := fun _ => reading
def cuts : Fin 1 → Finset (Fin 1) := fun _ => ∅

theorem conditions : GuardCutSequentialization.Conditions A (Subst.id sig) lab before events := by
  refine ⟨?_, by decide +kernel, by decide +kernel, ?_, ?_, ?_, A.models_nil _, ?_⟩
  · intro event
    fin_cases event
    simp [events, reading, ShapeTest.Holds, ShapeTest.ofSelection, lab]
  · simp [LinearConnectionLayout.made, UnorderedOccurrenceConnections.roster, before,
      events, reading, List.finRange_succ]
  · intro event occurrence port
    have same : occurrence = 4 := by simpa [events, reading] using port
    subst occurrence
    exact Or.inl (by simp [before])
  · intro event
    simp [events, reading]
  · intro event equation member
    simp [ConditionalComposite.addedEquations, Selection.equations, events, reading, lab] at member
    obtain rfl := member
    rfl

theorem computed : GuardCutOrders.order? events cuts = some [0] := by decide +kernel

theorem guard_world : GuardedCutSemantics.cutWorld before events (cuts 0) = {4} := by
  ext occurrence
  simp [GuardedCutSemantics.mem_cutWorld, before, cuts]

theorem asks : GuardedCutSemantics.Asks A lab before events cuts := by
  intro current check member assignment _
  fin_cases current
  have same : check = .count pTok 1 := by simpa [events, reading] using member
  subst check
  change Check.Holds A assignment lab (GuardedCutSemantics.cutWorld before events (cuts 0))
    (.count pTok 1)
  rw [guard_world]
  change (Check.matches A assignment lab {4} pTok).card = 1
  have region : Check.matches A assignment lab {4} pTok = {4} := by
    ext occurrence
    simp only [Check.matches, Finset.mem_filter]
    constructor
    · exact And.left
    · intro member
      refine ⟨member, ?_⟩
      have same : occurrence = 4 := Finset.mem_singleton.mp member
      subst occurrence
      change A.E (A.apply assignment pTok) (A.apply assignment pTok)
      exact A.equivalence.refl _
  rw [region]
  rfl

theorem repeated_read_executes_without_multiplying_rows :
    ConditionalSchedule.Executable A lab before ([0].map events) ∧
      (events 0).2.read = [4, 4] ∧
      (ConditionalSchedule.follow lab before ([0].map events)).present = {4, 5} := by
  have result := conditions.computed_order_executes cuts computed asks
  refine ⟨result.1, rfl, ?_⟩
  rw [result.2.2]
  simp [LinearConnectionLayout.residual, made, taken, UnorderedOccurrenceConnections.roster,
    events, reading, before, List.finRange_succ]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutSharedReadControls
