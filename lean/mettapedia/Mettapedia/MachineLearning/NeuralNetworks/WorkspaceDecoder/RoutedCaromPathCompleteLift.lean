import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromPathCompleteStability

/-!
# Forward lifts of routed path-complete graphs

Ninite and Jungers, *Iterative graph lifting for automatic design of
path-complete stability certificates* (2026), introduce a local forward lift:
a selected phase is split into one copy for each of its outgoing neighbours.
Their Theorems 2 and 3 show respectively that the lift preserves
path-completeness and that every feasible certificate on the original graph
induces one on the lifted graph with the same objective value.

This file isolates the graph-theoretic part for finite routed executions and
connects it to `PathCompleteRegionalLyapunov`.  The certificate transport below
is more general than the quadratic-matrix instance in the source: regions,
centres, and nonlinear transition energies are pulled back along the lift
projection without changing the contraction rate.

The results do not claim that a lift strictly improves a bound, identify which
phase should be split, or solve the source paper's optimization problem.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Function Set

namespace RoutedCarom

universe uPhase uCommand uState

variable {Phase : Type uPhase} {Command : Type uCommand}
  {State : Type uState} [NormedAddCommGroup State]

/-! ## Labeled paths and path-completeness -/

/-- A finite word-labeled path through a routed phase graph. -/
inductive CommandPath (allowed : Phase → Command → Phase → Prop) :
    Phase → List Command → Phase → Prop
  | nil (phase : Phase) : CommandPath allowed phase [] phase
  | cons {source target final command commands} :
      allowed source command target →
      CommandPath allowed target commands final →
      CommandPath allowed source (command :: commands) final

/-- Every nonempty finite command word is realized by some graph path. -/
def GraphPathComplete
    (allowed : Phase → Command → Phase → Prop) : Prop :=
  ∀ commands : List Command, commands ≠ [] →
    ∃ source target, CommandPath allowed source commands target

/-! ## The local forward lift -/

/-- An outgoing neighbour of the selected phase. -/
def ForwardSuccessor
    (allowed : Phase → Command → Phase → Prop) (selected : Phase) :=
  { target : Phase // ∃ command, allowed selected command target }

/-- The selected phase is replaced by one copy for each outgoing neighbour;
all other phases retain one ordinary copy. -/
inductive ForwardLiftNode
    (allowed : Phase → Command → Phase → Prop) (selected : Phase)
  | ordinary : { phase : Phase // phase ≠ selected } →
      ForwardLiftNode allowed selected
  | split : ForwardSuccessor allowed selected →
      ForwardLiftNode allowed selected

/-- Forget which forward-lift copy a phase occupies. -/
def ForwardLiftNode.base
    {allowed : Phase → Command → Phase → Prop} {selected : Phase} :
    ForwardLiftNode allowed selected → Phase
  | .ordinary phase => phase
  | .split _ => selected

/-- The four edge classes of the Ninite--Jungers forward lift.

For a split source, its stored successor determines the only ordinary target
it may enter.  A split copy indexed by the selected phase handles self-loops.
-/
def forwardLiftAllowed
    (allowed : Phase → Command → Phase → Prop) (selected : Phase) :
    ForwardLiftNode allowed selected → Command →
      ForwardLiftNode allowed selected → Prop
  | .ordinary source, command, .ordinary target =>
      allowed source command target
  | .ordinary source, command, .split _ =>
      allowed source command selected
  | .split successor, command, .ordinary target =>
      successor.1 = target.1 ∧ allowed selected command target
  | .split successor, command, .split _ =>
      successor.1 = selected ∧ allowed selected command selected

/-- Every lifted edge projects to an edge of the original graph. -/
theorem forwardLiftAllowed_projects
    {allowed : Phase → Command → Phase → Prop} {selected : Phase}
    {source target : ForwardLiftNode allowed selected} {command : Command}
    (hedge : forwardLiftAllowed allowed selected source command target) :
    allowed source.base command target.base := by
  cases source with
  | ordinary source =>
      cases target <;>
        simpa [forwardLiftAllowed, ForwardLiftNode.base] using hedge
  | split successor =>
      cases target with
      | ordinary target =>
          exact hedge.2
      | split target =>
          exact hedge.2

/-- The lifted copy occupied at the source of an original edge.  A selected
source is represented by the copy indexed by that edge's target. -/
def liftEdgeSource
    [DecidableEq Phase]
    {allowed : Phase → Command → Phase → Prop} {selected source target : Phase}
    {command : Command} (hedge : allowed source command target) :
    ForwardLiftNode allowed selected :=
  if hsource : source = selected then
    .split ⟨target, ⟨command, hsource ▸ hedge⟩⟩
  else
    .ordinary ⟨source, hsource⟩

/-- Consecutive original edges induce one lifted edge between their
source-copy representatives. -/
theorem forwardLiftAllowed_liftEdgeSources
    [DecidableEq Phase]
    {allowed : Phase → Command → Phase → Prop} {selected : Phase}
    {source middle target : Phase} {first second : Command}
    (hfirst : allowed source first middle)
    (hsecond : allowed middle second target) :
    forwardLiftAllowed allowed selected
      (liftEdgeSource (selected := selected) hfirst) first
      (liftEdgeSource (selected := selected) hsecond) := by
  by_cases hsource : source = selected
  · subst source
    by_cases hmiddle : middle = selected
    · subst middle
      simp [liftEdgeSource, forwardLiftAllowed, hfirst]
    · simp [liftEdgeSource, forwardLiftAllowed, hmiddle, hfirst]
  · by_cases hmiddle : middle = selected
    · subst middle
      simp [liftEdgeSource, forwardLiftAllowed, hsource, hfirst]
    · simp [liftEdgeSource, forwardLiftAllowed, hsource, hmiddle, hfirst]

/-- A base path with one lookahead edge lifts to the same path prefix.
Lookahead supplies the outgoing-neighbour index for the final lifted phase. -/
theorem commandPath_forwardLift_prefix
    [DecidableEq Phase]
    {allowed : Phase → Command → Phase → Prop} {selected : Phase}
    {source next final : Phase} {first lookahead : Command}
    (commands : List Command)
    (hfirst : allowed source first next)
    (htail : CommandPath allowed next (commands ++ [lookahead]) final) :
    ∃ liftedFinal,
      CommandPath (forwardLiftAllowed allowed selected)
        (liftEdgeSource (selected := selected) hfirst)
        (first :: commands) liftedFinal := by
  induction commands generalizing source next final first with
  | nil =>
      cases htail with
      | cons hlook hnil =>
          cases hnil
          exact ⟨liftEdgeSource (selected := selected) hlook,
            .cons (forwardLiftAllowed_liftEdgeSources hfirst hlook) (.nil _)⟩
  | cons command commands ih =>
      cases htail with
      | cons hnext hrest =>
          obtain ⟨liftedFinal, hlifted⟩ :=
            ih hnext hrest
          exact ⟨liftedFinal,
            .cons (forwardLiftAllowed_liftEdgeSources hfirst hnext) hlifted⟩

/-- A local forward lift preserves path-completeness.

The proof requests one extra command from the original complete graph.  That
lookahead edge determines which split copy represents the endpoint of the
requested word, avoiding any assumption that every original node has an
outgoing edge.
-/
theorem forwardLift_graphPathComplete
    [DecidableEq Phase] [Nonempty Command]
    {allowed : Phase → Command → Phase → Prop} {selected : Phase}
    (hcomplete : GraphPathComplete allowed) :
    GraphPathComplete (forwardLiftAllowed allowed selected) := by
  intro commands hcommands
  cases commands with
  | nil => exact (hcommands rfl).elim
  | cons first commands =>
      let lookahead : Command := Classical.choice inferInstance
      have hextended : first :: commands ++ [lookahead] ≠ [] := by simp
      obtain ⟨source, final, hpath⟩ :=
        hcomplete (first :: commands ++ [lookahead]) hextended
      cases hpath with
      | cons hfirst htail =>
          obtain ⟨liftedFinal, hlifted⟩ :=
            commandPath_forwardLift_prefix commands hfirst htail
          exact ⟨liftEdgeSource (selected := selected) hfirst,
            liftedFinal, hlifted⟩

/-! ## Pulling regional certificates through the lift -/

/-- Every regional Lyapunov certificate on the base graph induces a
certificate on the forward lift with the same contraction rate. -/
def PathCompleteRegionalLyapunov.forwardLift
    {transition : Command → State → State}
    {center : Phase → State} {region : Phase → Set State}
    {allowed : Phase → Command → Phase → Prop}
    (certificate : PathCompleteRegionalLyapunov transition center region allowed)
    (selected : Phase) :
    PathCompleteRegionalLyapunov transition
      (fun phase : ForwardLiftNode allowed selected => center phase.base)
      (fun phase : ForwardLiftNode allowed selected => region phase.base)
      (forwardLiftAllowed allowed selected) where
  energy := fun phase state => certificate.energy phase.base state
  rate := certificate.rate
  rate_nonneg := certificate.rate_nonneg
  rate_lt_one := certificate.rate_lt_one
  coercivity := fun phase => certificate.coercivity phase.base
  coercivity_pos := fun phase => certificate.coercivity_pos phase.base
  center_mem := fun phase => certificate.center_mem phase.base
  energy_nonneg := fun phase state hstate =>
    certificate.energy_nonneg phase.base state hstate
  energy_controls_distance := fun phase state hstate =>
    certificate.energy_controls_distance phase.base state hstate
  maps_region := by
    intro source target command state hedge hstate
    exact certificate.maps_region command state
      (forwardLiftAllowed_projects hedge) hstate
  contracts := by
    intro source target command state hedge hstate
    exact certificate.contracts command state
      (forwardLiftAllowed_projects hedge) hstate

theorem PathCompleteRegionalLyapunov.forwardLift_rate
    {transition : Command → State → State}
    {center : Phase → State} {region : Phase → Set State}
    {allowed : Phase → Command → Phase → Prop}
    (certificate : PathCompleteRegionalLyapunov transition center region allowed)
    (selected : Phase) :
    (certificate.forwardLift selected).rate = certificate.rate := rfl

/-! ## Positive and negative executable boundaries -/

def completeUnitGraph (_ : Unit) (_ : Bool) (_ : Unit) : Prop := True

theorem completeUnitGraph_pathComplete :
    GraphPathComplete completeUnitGraph := by
  have unitPath : ∀ commands : List Bool,
      CommandPath completeUnitGraph () commands () := by
    intro commands
    induction commands with
    | nil => exact .nil ()
    | cons command commands ih =>
        exact .cons trivial ih
  intro commands _
  exact ⟨(), (), unitPath commands⟩

theorem completeUnitGraph_forwardLift_pathComplete :
    GraphPathComplete (forwardLiftAllowed completeUnitGraph ()) :=
  forwardLift_graphPathComplete completeUnitGraph_pathComplete

/-- A graph missing one command is not path-complete. -/
def falseOnlyUnitGraph (_ : Unit) (command : Bool) (_ : Unit) : Prop :=
  command = false

theorem falseOnlyUnitGraph_not_pathComplete :
    ¬ GraphPathComplete falseOnlyUnitGraph := by
  intro hcomplete
  obtain ⟨source, target, hpath⟩ := hcomplete [true] (by simp)
  cases hpath with
  | cons hedge htail =>
      simp [falseOnlyUnitGraph] at hedge

/-- Forward lifting cannot manufacture an edge carrying a missing command. -/
theorem falseOnlyUnitGraph_forwardLift_not_pathComplete :
    ¬ GraphPathComplete (forwardLiftAllowed falseOnlyUnitGraph ()) := by
  intro hcomplete
  obtain ⟨source, target, hpath⟩ := hcomplete [true] (by simp)
  cases hpath with
  | cons hedge htail =>
      have hprojected := forwardLiftAllowed_projects hedge
      simp [falseOnlyUnitGraph] at hprojected

#print axioms forwardLiftAllowed_projects
#print axioms forwardLiftAllowed_liftEdgeSources
#print axioms commandPath_forwardLift_prefix
#print axioms forwardLift_graphPathComplete
#print axioms PathCompleteRegionalLyapunov.forwardLift
#print axioms completeUnitGraph_forwardLift_pathComplete
#print axioms falseOnlyUnitGraph_not_pathComplete
#print axioms falseOnlyUnitGraph_forwardLift_not_pathComplete

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
