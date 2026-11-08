import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CongruenceTriggers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

/-!
# A context with knowledge breaks open bisimilarity

Equivalence modulo the knowledge asks nothing of a context's knowledge
(`Observation.ModuloEquivalent.tensor_disjoint`): equivalent configurations already have the same
solutions, so the conjunction with the context's knowledge has the same solutions on both sides.
Open bisimilarity does not compare solutions, and a context with knowledge can break it.

* **Ground firings see the knowledge only through its consistency** (`Ground.models_problem`,
  `Ground.valid_iff_consistent`).
* **For a ground program, configurations with the same occurrences and knowledge consistent
  together are open bisimilar**, at any ports (`openBisimilar_of_ground`).
* **Control** (`Triggered.knowledge_not_congruence`): for the triggered race pair over first-order
  terms, `{k, tc}` under the knowledge `x = 1` and `{k, tc}` with no knowledge are open bisimilar,
  hence minimally bisimilar. A context without occurrences and with the knowledge `x = 0` makes the
  first inconsistent and leaves the second consistent: beside it, only the second fires `C`.

So the congruence of the minimal and open steps (`TriggeredProgram.tensor_ports`,
`OpenBisimilar.tensor_ports`) holds for contexts of port atoms without knowledge, and fails both for
atoms outside the ports (`Triggered.nonport_not_congruence`) and for knowledge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race

open AnnotatedRuns (Firing)
open MeTTaCalculus.OccurrenceCommits (Enabled)

universe uT uS uO uL

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {L : Type uL}

/-! ## Ground firings and knowledge -/

section Ground

variable {A : SubstitutionAction T S} {label : O → T} {f : Firing T S O}

omit [DecidableEq O] in
/-- **A reflexive store holds at every solution.** -/
theorem models_of_reflexive {store : EquationStore T} (refl : Reflexive store) (σ : S) :
    A.Models σ store := fun e member => by
  show A.E (A.apply σ e.1) (A.apply σ e.2)
  rw [refl e member]
  exact A.equivalence.refl _

omit [DecidableEq O] in
/-- **The problem of a ground firing has the solutions of the knowledge.** -/
theorem Ground.models_problem (ground : Ground label f) (C : Configuration T O) (σ : S) :
    A.Models σ (f.selection.problem label f.rule C) ↔ A.Models σ C.equations := by
  unfold Selection.problem
  rw [ground.take, ground.read, ground.tell, A.models_append, A.models_append, A.models_append]
  exact ⟨fun solved => solved.1.1.1, fun solved => ⟨⟨⟨solved,
    models_of_reflexive (reflexive_equations label _) σ⟩,
    models_of_reflexive (reflexive_equations label _) σ⟩, models_of_reflexive reflexive_nil σ⟩⟩

variable (A) in
/-- **A ground firing is admitted exactly when the knowledge is consistent and its commit is
enabled.** -/
theorem Ground.valid_iff_consistent (ground : Ground label f) (C : Configuration T O) :
    f.Valid A label C ↔
      A.Consistent C.equations ∧ Enabled label C.present (f.selection.commit (T := T)) := by
  constructor
  · intro valid
    obtain ⟨σ, solved⟩ := valid.firing.consistent
    exact ⟨⟨σ, (ground.models_problem C σ).mp solved⟩, valid.firing.occurrences⟩
  · rintro ⟨⟨σ, solved⟩, enabled⟩
    refine ⟨⟨ground.taken_nodup, ground.made_nodup, ?_, ?_, ground.produce, enabled,
      ⟨σ, (ground.models_problem C σ).mpr solved⟩, ?_⟩, ?_⟩
    · rw [ground.take, List.length_map]
    · rw [ground.read, List.length_map]
    · intro check member
      rw [ground.checks] at member
      simp at member
    · intro query member
      rw [ground.queries] at member
      simp at member

/-- The knowledge after a ground firing is consistent exactly when the knowledge before is. -/
theorem Ground.consistent_result (ground : Ground label f) (C : Configuration T O) :
    A.Consistent (f.result label C).equations ↔ A.Consistent C.equations :=
  ⟨fun ⟨σ, solved⟩ => ⟨σ, (ground.models_problem C σ).mp solved⟩,
    fun ⟨σ, solved⟩ => ⟨σ, (ground.models_problem C σ).mpr solved⟩⟩

end Ground

/-! ## Open bisimilarity of ground programs -/

section GroundPrograms

variable {A : SubstitutionAction T S} {label : O → T} {offers : L → Firing T S O → Prop}
  {ports : O → Prop}

/-- One direction of the open bisimulation of a ground program. -/
theorem ground_step (ground : ∀ ℓ f, offers ℓ f → Ground label f) {X Y : Configuration T O}
    (present : X.present = Y.present) (consistent : A.Consistent X.equations ↔ A.Consistent Y.equations)
    (lab : L ⊕ O) {X' : Configuration T O} (moved : OpenMoves A label offers ports X lab X') :
    ∃ Y', OpenMoves A label offers ports Y lab Y' ∧ X'.present = Y'.present ∧
      (A.Consistent X'.equations ↔ A.Consistent Y'.equations) := by
  rcases lab with ℓ | o
  · obtain ⟨f, offered, valid, rfl⟩ := moved
    have grounded := ground ℓ f offered
    obtain ⟨knows, enabled⟩ := (grounded.valid_iff_consistent A X).mp valid
    refine ⟨f.result label Y, ⟨f, offered, (grounded.valid_iff_consistent A Y).mpr
      ⟨consistent.mp knows, present ▸ enabled⟩, rfl⟩, ?_, ?_⟩
    · show MeTTaCalculus.OccurrenceCommits.fire X.present (f.selection.commit (T := T)) =
        MeTTaCalculus.OccurrenceCommits.fire Y.present (f.selection.commit (T := T))
      rw [present]
    · rw [grounded.consistent_result, grounded.consistent_result]
      exact consistent
  · obtain ⟨port, rfl⟩ := moved
    refine ⟨addAtom Y o, ⟨port, rfl⟩, ?_, consistent⟩
    show insert o X.present = insert o Y.present
    rw [present]

/-- **For a ground program, configurations with the same occurrences and knowledge consistent
together are open bisimilar**, at any ports. -/
theorem openBisimilar_of_ground (ground : ∀ ℓ f, offers ℓ f → Ground label f) {C D : Configuration T O}
    (present : C.present = D.present) (consistent : A.Consistent C.equations ↔ A.Consistent D.equations) :
    OpenBisimilar A label offers ports C D := by
  refine ⟨fun X Y => X.present = Y.present ∧ (A.Consistent X.equations ↔ A.Consistent Y.equations),
    ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, present, consistent⟩
  · rintro X Y ⟨same, knows⟩ lab X' moved
    obtain ⟨Y', moved', same', knows'⟩ := ground_step ground same knows lab moved
    exact ⟨Y', moved', same', knows'⟩
  · rintro X Y ⟨same, knows⟩ lab Y' moved
    obtain ⟨X', moved', same', knows'⟩ := ground_step ground same.symm knows.symm lab moved
    exact ⟨X', moved', same'.symm, knows'.symm⟩

end GroundPrograms

/-! ## Control: knowledge in the context -/

namespace Triggered

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature)

/-- The term type of the control: first-order terms. -/
abbrev Tm := Term signature

/-- The knowledge `x = 1`. -/
def knowsOne : EquationStore Tm := [(.var 0, .const 1)]

/-- The context's knowledge `x = 0`. -/
def knowsZero : EquationStore Tm := [(.var 0, .const 0)]

/-- `{k, tc}` under `x = 1`. -/
def told : Configuration Tm Site := ⟨knowsOne, {.k, .tc}⟩

/-- `{k, tc}` with no knowledge. -/
def untold : Configuration Tm Site := ⟨[], {.k, .tc}⟩

/-- The context: no occurrence, the knowledge `x = 0`. -/
def context : Configuration Tm Site := ⟨knowsZero, ∅⟩

theorem told_consistent : ConstraintMultisetRewriting.Controls.A.Consistent knowsOne :=
  ⟨ConstraintMultisetRewriting.Controls.one, fun e member => by
    rw [List.mem_singleton.mp member]
    rfl⟩

theorem untold_consistent : ConstraintMultisetRewriting.Controls.A.Consistent ([] : EquationStore Tm) :=
  ⟨ConstraintMultisetRewriting.Controls.zero, fun e member => by simp at member⟩

theorem composite_inconsistent :
    ¬ ConstraintMultisetRewriting.Controls.A.Consistent (knowsOne ++ knowsZero) := by
  rintro ⟨σ, solved⟩
  have one : σ.applyTerm (.var 0) = (.const 1 : Tm) := solved (.var 0, .const 1) (by simp [knowsOne])
  have zero : σ.applyTerm (.var 0) = (.const 0 : Tm) := solved (.var 0, .const 0) (by simp [knowsZero])
  exact absurd (Term.const.inj (one.symm.trans zero)) (by decide)

theorem composite_consistent :
    ConstraintMultisetRewriting.Controls.A.Consistent (([] : EquationStore Tm) ++ knowsZero) :=
  ⟨ConstraintMultisetRewriting.Controls.zero, fun e member => by
    rw [List.nil_append, knowsZero, List.mem_singleton] at member
    rw [member]
    rfl⟩

/-- **A context with knowledge breaks open and minimal bisimilarity.** `told` and `untold` are open
bisimilar and minimally bisimilar for the triggered race pair; the context has no occurrence; beside
it they are not open bisimilar. -/
theorem knowledge_not_congruence (τ : Tm) :
    OpenBisimilar ConstraintMultisetRewriting.Controls.A (label τ) (offers τ) trigger told untold ∧
      MinimalBisimilar ConstraintMultisetRewriting.Controls.A (label τ) (offers τ) trigger told untold ∧
      context.present = ∅ ∧
      ¬ OpenBisimilar ConstraintMultisetRewriting.Controls.A (label τ) (offers τ) trigger
        (AnnotatedRuns.tensor told context) (AnnotatedRuns.tensor untold context) := by
  have ground : ∀ ℓ f, offers (S := Subst signature) τ ℓ f → Ground (label τ) f :=
    fun ℓ f member => Triggered.ground τ (ℓ, f) member
  have openly : OpenBisimilar ConstraintMultisetRewriting.Controls.A (label τ) (offers τ) trigger told
      untold :=
    openBisimilar_of_ground ground rfl ⟨fun _ => untold_consistent, fun _ => told_consistent⟩
  refine ⟨openly, (program τ).minimalBisimilar_iff.mpr openly, rfl, fun h => ?_⟩
  let g : Firing Tm (Subst signature) Site := firing τ [.k, .tc] []
  have member : (Act.C, g) ∈ alphabet τ := by simp [g, alphabet]
  have fires : Moves ConstraintMultisetRewriting.Controls.A (label τ) (offers τ)
      (AnnotatedRuns.tensor untold context) Act.C (g.result (label τ) (AnnotatedRuns.tensor untold context)) :=
    ⟨g, member, ((ground _ _ member).valid_iff_consistent _ _).mpr
      ⟨composite_consistent, of_decide_eq_true rfl⟩, rfl⟩
  have flipped : OpenBisimilar ConstraintMultisetRewriting.Controls.A (label τ) (offers τ) trigger
      (AnnotatedRuns.tensor untold context) (AnnotatedRuns.tensor told context) :=
    (openSystem ConstraintMultisetRewriting.Controls.A (label τ) (offers τ) trigger).bisimilar_symm h
  obtain ⟨C', ⟨f, offered, valid, -⟩, -⟩ := flipped.step (lab := .inl Act.C) fires
  exact composite_inconsistent (((ground _ _ offered).valid_iff_consistent _ _).mp valid).1

end Triggered

#print axioms models_of_reflexive
#print axioms Ground.models_problem
#print axioms Ground.valid_iff_consistent
#print axioms Ground.consistent_result
#print axioms ground_step
#print axioms openBisimilar_of_ground
#print axioms Triggered.told_consistent
#print axioms Triggered.composite_inconsistent
#print axioms Triggered.composite_consistent
#print axioms Triggered.knowledge_not_congruence

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race
