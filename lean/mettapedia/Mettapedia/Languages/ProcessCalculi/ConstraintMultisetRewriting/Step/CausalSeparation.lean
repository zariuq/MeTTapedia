import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CausalNetworksStep
import Mettapedia.GSLT.Causality.DoCalculus.DoRules

/-!
# The network's graph read off the step

On the network program, the step's own dependency between firings is the network's graph.

* **The make–read relation of a history** (`stepGraph`): `u → v` when the firing of `u` in the
  history of `x` makes an atom that the firing of `v` reads. **It is the network's graph**
  (`stepGraph_eq`), for every assignment and every regime.
* **Static independence is non-adjacency** (`history_staticIndependent_iff`): the firings of two
  distinct variables in a history are statically independent on the step
  (`AnnotatedRuns.StaticIndependent`, the independence the step's causal order is built from)
  exactly when neither variable is a parent of the other. The firings of one variable clash
  (`not_independent_same_variable`).

So every premise about the graph is a premise about the step program (`premise_on_step`). For
rule 1 of the do-calculus, the d-separation premise read off the step licenses Grok's conditional
independence in the intervened network (`rule1_on_step`); the premises of rules 2 and 3 are graph
surgeries of the same graph, and `premise_on_step` carries them alike.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CausalSeparation

open AnnotatedRuns (Firing)
open MeTTaCalculus.OccurrenceCommits (Commit)
open CausalNetworks CausalNetworksStep
open Mettapedia.GSLT.Causality.DoCalculus
open Mettapedia.ProbabilityTheory.BayesianNetworks
open MeasureTheory BayesianNetwork DirectedGraph DSeparation

universe uS

variable {V β : Type}
variable [Fintype V] [DecidableEq V]
variable [Fintype β] [DecidableEq β] [MeasurableSpace β]
variable (graph : DirectedGraph V)
variable (acyclic : graph.IsAcyclic)
variable [DecidableRel graph.edges]
variable {R : Type} [Fintype R] [DecidableEq R]
variable {S : Type uS}

local notation "Ev" => Event (β := β) (R := R) graph

omit [Fintype β] [MeasurableSpace β] [Fintype R] [DecidableEq R] [DecidableEq V] [DecidableEq β] in
theorem val_mem_reads_iff (e : Ev) (u : V) (b : β) :
    Atom.val u b ∈ reads graph e ↔ ∃ p : ParentIdx graph e.1, p.1 = u ∧ e.2.1 p = b := by
  constructor
  · intro member
    rcases List.mem_cons.mp member with same | inside
    · cases same
    · obtain ⟨p, _, same⟩ := List.mem_map.mp inside
      exact ⟨p, (Atom.val.inj same).1, (Atom.val.inj same).2⟩
  · rintro ⟨p, rfl, rfl⟩
    exact val_mem_reads e p

omit [Fintype β] [MeasurableSpace β] [Fintype R] [DecidableEq R] [DecidableEq V] [DecidableEq β] in
/-- In a history, the firing of `v` reads the value the firing of `u` makes exactly when `u` is a
parent of `v`. -/
theorem val_mem_history_reads (regime : V → R) (x : V → β) (u v : V) :
    Atom.val u (x u) ∈ reads graph (assignmentEvent graph regime x v) ↔ graph.edges u v := by
  rw [val_mem_reads_iff]
  constructor
  · rintro ⟨p, rfl, -⟩
    exact (mem_parentsFinset_iff graph _ _).1 p.2
  · intro edge
    exact ⟨⟨u, (mem_parentsFinset_iff graph u v).2 edge⟩, rfl, rfl⟩

/-- **The make–read relation of the history of `x`**: `u → v` when the firing of `u` makes an atom
the firing of `v` reads. -/
def stepGraph (regime : V → R) (x : V → β) : DirectedGraph V where
  edges u v := Atom.val u (x u) ∈ reads graph (assignmentEvent graph regime x v)

omit [Fintype β] [MeasurableSpace β] [Fintype R] [DecidableEq R] [DecidableEq V] [DecidableEq β] in
/-- **The step's make–read relation on a history is the network's graph.** -/
theorem stepGraph_eq (regime : V → R) (x : V → β) : stepGraph graph regime x = graph := by
  have edges : (stepGraph graph regime x).edges = graph.edges := by
    funext u v
    exact propext (val_mem_history_reads graph regime x u v)
  show (⟨(stepGraph graph regime x).edges⟩ : DirectedGraph V) = ⟨graph.edges⟩
  rw [edges]

omit [Fintype β] [MeasurableSpace β] [Fintype R] [DecidableEq R] [DecidableEq V] [DecidableEq β] in
/-- **Every premise about the graph is a premise about the step program.** -/
theorem premise_on_step (regime : V → R) (x : V → β) (premise : DirectedGraph V → Prop) :
    premise (stepGraph graph regime x) ↔ premise graph := by
  rw [stepGraph_eq]

omit [Fintype β] [MeasurableSpace β] [Fintype R] in
/-- **The firings of one variable clash**: they take the same pending atom. -/
theorem not_independent_same_variable [Nonempty S] {e e' : Ev} (same : e.1 = e'.1) :
    ¬ AnnotatedRuns.Independent id (firing (S := S) graph e) (firing graph e') := by
  intro independent
  obtain ⟨σ⟩ := ‹Nonempty S›
  apply (independent σ).1.1
  left
  rw [Finset.not_disjoint_iff]
  exact ⟨Atom.pend e.1, by simp [firing], by simp [firing, same]⟩

omit [Fintype β] [MeasurableSpace β] [Fintype R] in
/-- **On a history, static independence of two variables' firings is non-adjacency.** -/
theorem history_staticIndependent_iff [Nonempty S] (regime : V → R) (x : V → β) {u v : V}
    (distinct : u ≠ v) :
    AnnotatedRuns.StaticIndependent id (firing (S := S) graph (assignmentEvent graph regime x u))
        (firing graph (assignmentEvent graph regime x v)) ↔
      ¬ graph.edges u v ∧ ¬ graph.edges v u := by
  have madeU : ∀ σ : S, Atom.val u (x u) ∈
      ((firing (S := S) graph (assignmentEvent graph regime x u)).footprintAt σ).made := by
    intro σ
    simp [firing, assignmentEvent]
  have madeV : ∀ σ : S, Atom.val v (x v) ∈
      ((firing (S := S) graph (assignmentEvent graph regime x v)).footprintAt σ).made := by
    intro σ
    simp [firing, assignmentEvent]
  have usesIff : ∀ (σ : S) (w w' : V) (a : Atom V β R),
      a ∈ ((firing (S := S) graph (assignmentEvent graph regime x w')).footprintAt σ).uses ↔
        a = Atom.pend w' ∨ a ∈ reads graph (assignmentEvent graph regime x w') := by
    intro σ w w' a
    simp [Commit.uses, firing, assignmentEvent]
  constructor
  · rintro ⟨-, -, independent⟩
    obtain ⟨σ⟩ := ‹Nonempty S›
    have trace := independent σ
    refine ⟨fun edge => ?_, fun edge => ?_⟩
    · exact Finset.disjoint_left.mp trace.2.1 (madeU σ)
        ((usesIff σ u v _).mpr (Or.inr ((val_mem_history_reads graph regime x u v).mpr edge)))
    · exact Finset.disjoint_left.mp trace.2.2 (madeV σ)
        ((usesIff σ v u _).mpr (Or.inr ((val_mem_history_reads graph regime x v u).mpr edge)))
  · rintro ⟨noUV, noVU⟩
    have static : ∀ w, (firing (S := S) graph (assignmentEvent graph regime x w)).Static :=
      fun w => ⟨rfl, fun query member => by simp [firing] at member⟩
    refine ⟨static u, static v, fun σ => ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩⟩
    · rintro (taken | made)
      · apply taken
        rw [Finset.disjoint_left]
        intro a inU inV
        simp [firing, assignmentEvent] at inU inV
        rw [inU] at inV
        exact distinct (Atom.pend.inj inV)
      · apply made
        rw [Finset.disjoint_left]
        intro a inU inV
        simp [firing, assignmentEvent] at inU inV
        rw [inU] at inV
        exact distinct (Atom.val.inj inV).1
    · rintro (taken | writes)
      · apply taken
        rw [Finset.disjoint_left]
        intro a inU inV
        simp [firing, assignmentEvent] at inU
        subst inU
        simp [firing, assignmentEvent, reads] at inV
      · obtain ⟨query, member, _⟩ := writes
        simp [firing] at member
    · rintro (taken | writes)
      · apply taken
        rw [Finset.disjoint_left]
        intro a inV inU
        simp [firing, assignmentEvent] at inV
        subst inV
        simp [firing, assignmentEvent, reads] at inU
      · obtain ⟨query, member, _⟩ := writes
        simp [firing] at member
    · rw [Finset.disjoint_left]
      intro a inU inUses
      simp [firing, assignmentEvent] at inU
      subst inU
      rcases (usesIff σ u v _).mp inUses with pending | read
      · cases pending
      · exact noUV ((val_mem_history_reads graph regime x u v).mp read)
    · rw [Finset.disjoint_left]
      intro a inV inUses
      simp [firing, assignmentEvent] at inV
      subst inV
      rcases (usesIff σ v u _).mp inUses with pending | read
      · cases pending
      · exact noVU ((val_mem_history_reads graph regime x v u).mp read)

omit [DecidableEq β] [Fintype R] [DecidableEq R] in
/-- **Rule 1 of the do-calculus, with its d-separation premise read off the step program.** -/
theorem rule1_on_step [Nonempty β] [StandardBorelSpace β] [StandardBorelSpace (V → β)]
    (cpt : (network (β := β) graph acyclic).DiscreteCPT) (treatment : V) (value : β)
    (outcome covariate conditioning : Set V) (hTreat : treatment ∈ conditioning)
    (hOverlap : outcome ∩ covariate ⊆ conditioning) (regime : V → R) (x : V → β)
    (hsep : DSeparatedFull (deleteIncoming (stepGraph graph regime x) {treatment})
      outcome covariate conditioning) :
    CondIndepVertices
      (network (β := β) (deleteIncoming graph {treatment})
        (deleteIncoming_acyclic graph acyclic {treatment}))
      (intervenedCPT graph acyclic cpt treatment value).jointMeasure
      outcome covariate conditioning := by
  rw [stepGraph_eq] at hsep
  exact rule1_condIndep graph acyclic cpt treatment value outcome covariate conditioning hTreat
    hOverlap hsep

#print axioms val_mem_history_reads
#print axioms stepGraph_eq
#print axioms premise_on_step
#print axioms not_independent_same_variable
#print axioms history_staticIndependent_iff
#print axioms rule1_on_step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CausalSeparation

end
