import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Transitions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Execution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Arrows

/-!
# World firings compose with the actual operational and execution interfaces

The one-world correspondence concerns `Worlds.Fires` at the explicit
`events X O E` instance, with a fixed shared rule set. It reflects every
supplied target prefix into an actual firing run with the same endpoint
and length, and preserves any state readout.
The pair correspondence uses the existing interleaving product. Neither
statement treats fork, publication or merge as a firing, or asserts that
the proposition-valued bag relation retains event multiplicity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open FragmentsOfTheStep.TransitionMaps
open RuleSyntax RuleSyntax.Worlds
open RuleSyntax.Equivalence (System)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} [DecidableEq O]
  (X : Frames Tm Hom) (E : Extensions.{uO, uH, uE} Hom)

def singleton (program shared : Program Tm) (state : State Tm O) : Bag Tm O :=
  ⟨{(⟨program, state⟩ : System Tm O)}, shared⟩

abbrev firings : GSLT := theoryOf (Bag Tm O) (Fires (events X O E))

def singletonTranslation (program shared : Program Tm) :
    OperationalTranslation (Execution.theory (step X O E (program ∪ shared)).toStep)
      (firings (O := O) X E) :=
  Transitions.translation (one_world_bisimulation (X := X) (E := E) (O := O) program shared)

def singletonCorrespondence (program shared : Program Tm) :
    OperationalCorrespondence (Execution.theory (step X O E (program ∪ shared)).toStep)
      (firings (O := O) X E) :=
  Transitions.functionalCorrespondence (one_world_bisimulation (X := X) (E := E) (O := O) program shared)

def singletonProgress (program shared : Program Tm) :
    Progress.Certificate (singletonCorrespondence (O := O) X E program shared).toOperationalReadback :=
  Transitions.progress (graph_isBisimulation_iff.mpr (one_world_bisimulation (X := X) (E := E) (O := O) program shared))

/-- Every concrete firing run has its actual bag path. -/
def singletonRunPath (program shared : Program Tm) {state : State Tm O}
    (run : (step X O E (program ∪ shared)).toStep.Run state) :
    ExecutionPath (firings X E) (singleton program shared state)
      (singleton program shared run.last) :=
  (singletonTranslation X E program shared).mapRoute (Execution.toPath _ run)

theorem singletonRunPath_length (program shared : Program Tm) {state : State Tm O}
    (run : (step X O E (program ∪ shared)).toStep.Run state) :
    (singletonRunPath X E program shared run).length = run.word.length := by
  rw [singletonRunPath, OperationalTranslation.mapRoute_length, Execution.toPath_length]

/-- Every supplied bag firing path from the singleton image lifts to an
actual run. The exact supplied endpoint and number of steps are retained. -/
theorem singletonPathRun (program shared : Program Tm) :
    ∀ {first last : Bag Tm O} (path : ExecutionPath (firings X E) first last)
      (state : State Tm O), singleton program shared state = first →
        ∃ run : (step X O E (program ∪ shared)).toStep.Run state,
          singleton program shared run.last = last ∧ run.word.length = path.length
  | _, _, .refl _, state, same => ⟨.nil state, same, rfl⟩
  | _, _, .cons edge rest, state, same => by
      have taken := edge.down
      rw [← same] at taken
      obtain ⟨next, ⟨firing, admitted, endpoint⟩, there⟩ :=
        (one_world_bisimulation program shared).zag taken
      subst endpoint
      obtain ⟨run, final, length⟩ := singletonPathRun program shared rest _ there
      exact ⟨.cons firing admitted run, final, congrArg (· + 1) length⟩

omit [DecidableEq O] in
theorem singleton_shows (program shared : Program Tm) (state : State Tm O)
    (read : State Tm O → Prop) : Shows read (singleton program shared state) ↔ read state := by
  simp [Shows, singleton]

/-- The readout is arbitrary: knowledge, rows and frame have not been
hidden in an opaque state or replaced by an empty knowledge store. -/
theorem singleton_reachable_iff_run (program shared : Program Tm) (state : State Tm O)
    (read : State Tm O → Prop) :
    (∃ last, (firings X E).MultiStep (singleton program shared state) last ∧ Shows read last) ↔
      ∃ run : (step X O E (program ∪ shared)).toStep.Run state, read run.last := by
  constructor
  · rintro ⟨last, reached, observed⟩
    obtain ⟨path⟩ := (executionPath_nonempty_iff_multiStep (firings X E) _ _).mpr reached
    obtain ⟨run, final, _⟩ := singletonPathRun X E program shared path state rfl
    rw [← final] at observed
    exact ⟨run, (singleton_shows program shared run.last read).mp observed⟩
  · rintro ⟨run, observed⟩
    exact ⟨_, executionPathToMultiStep (singletonRunPath X E program shared run),
      (singleton_shows program shared run.last read).mpr observed⟩

theorem singleton_normalization_iff (program shared : Program Tm) (state : State Tm O) :
    Acc (fun after before => Steps X O E (program ∪ shared) before after) state ↔
      Acc (fun after before => Fires (events X O E) before after) (singleton program shared state) :=
  Transitions.normalization_iff
    (graph_isBisimulation_iff.mpr (one_world_bisimulation program shared)) rfl

/-- The pair object remains the actual GSLT interleaving product. -/
def pairCorrespondence (left right shared : Program Tm) :
    OperationalCorrespondence
      (GSLT.interleavingProduct (Execution.theory (step X O E (left ∪ shared)).toStep)
        (Execution.theory (step X O E (right ∪ shared)).toStep)) (firings (O := O) X E) where
  related pair bag := pairBag left right shared pair = bag
  readStep same moved :=
    (Transitions.functionalCorrespondence (pair_bisimulation (X := X) (E := E) (O := O) left right shared)).readStep same moved
  forward same moved :=
    (Transitions.functionalCorrespondence (pair_bisimulation (X := X) (E := E) (O := O) left right shared)).forward same moved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.singletonPathRun
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.singleton_reachable_iff_run
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.pairCorrespondence
