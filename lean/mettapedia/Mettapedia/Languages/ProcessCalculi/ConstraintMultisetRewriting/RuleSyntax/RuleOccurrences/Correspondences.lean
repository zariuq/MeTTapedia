import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Program
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.DerivedCongruent
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Congruence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.TransitionMaps
import Mettapedia.GSLT.Core.OperationalReadback

/-!
# Results of this folder as operational correspondences

`GSLT.IndexedOperational.OperationalCorrespondence source target` relates the states of two theories
so that every step of the target, from a related state, is no step or one step of the source, and
every step of the source is a path of the target. A transition relation is a theory with discrete
equations (`TransitionMaps.theoryOf`).

* **`programCorrespondence`** (the step of a program). Source: the step of `P ∪ Q`. Target: the
  candidate with ambient program `P`. A state is related to the candidate state that holds the rules
  of `Q` persistently beside it (`holding`). Each step is one step, both ways. So a property of the
  rows and the knowledge is reached by a run of one exactly when it is reached by a run of the other
  (`program_reachable_iff`, by the general `reachable_iff`).
* **`configCorrespondence`** (configurations and systems). Source: the configurations of
  `Congruence` with their moves. Target: the systems of `RuleSyntax/Equivalence` with their
  reductions. A configuration is related to the system it presents (`Config.system`). Each step is
  one step, both ways (`config_reachable_iff`).
* **`derivedCorrespondence`** (a derived link adds nothing). Source: the program with the derived
  link. Target: the program without it. Two states are related when they are congruent beside the
  program without the link. A firing of the target is answered by one firing of the source; a firing
  of the source by a run of the target, of two firings when it fires the derived link. So the same
  barbs are reachable with the link and without it (`derived_same_barbs`).

Over first-order atoms: `Atoms.chainCorrespondence` and `Atoms.same_barbs_token`; the row `3` is
reached with the derived link in one firing (`Atoms.three_with_derived`), hence without it
(`Atoms.three_without_derived`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences

open Interface (Frames)
open LogicOverTheStep.StepSpan (Succ)
open FragmentsOfTheStep.TransitionMaps (theoryOf)
open _root_.Mettapedia.GSLT.IndexedOperational (OperationalCorrespondence ExecutionPath)

section Paths

universe u

variable {V : Type u} {r : V → V → Prop}

/-- A run of a relation is a path of its theory. -/
theorem path_of_run {x y : V} (run : Relation.ReflTransGen r x y) :
    Nonempty (ExecutionPath (theoryOf V r) x y) := by
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨.refl _⟩
  | head moved _ ih =>
      obtain ⟨rest⟩ := ih
      exact ⟨.cons ⟨moved⟩ rest⟩

end Paths

section Program

universe uO uT uH uE uOcc uR uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} [DecidableEq O] (R : Type uR) [DecidableEq R] {Z : Type uZ}
  (X : Frames Tm Hom) (E : Extensions.{uO, uH, uE} Hom) {P Q : Program Tm}
  {rules : Finset R} {code : R → Rule Tm}

/-- **The step of a program and the candidate, as an operational correspondence**: a state of the
step of `P ∪ Q` is related to the candidate state that holds the rules of `Q` persistently, the
ambient program being `P`. Each step of one is one step of the other. -/
def programCorrespondence (offers : Offers Q rules code) (zone : R → Z) :
    OperationalCorrespondence (theoryOf (State Tm O) (Succ (step X O E (P ∪ Q)).toStep))
      (theoryOf (RState Tm O R (Rule Tm) Z) (Succ (rstep X O R E (ofRules Z) P).toStep)) where
  related s u := u = holding s rules code zone
  readStep := by
    rintro origin current next rfl moved
    obtain ⟨t, same, step⟩ := holding_closed R X E offers zone moved
    exact .inr ⟨t, step, same⟩
  forward := by
    rintro origin after current rfl moved
    have step : Succ (rstep X O R E (ofRules Z) P).toStep (holding origin rules code zone)
        (holding after rules code zone) := (program_eq R X E offers zone origin after).mpr moved
    exact ⟨holding after rules code zone, path_of_run (.single step), rfl⟩

/-- **A property of the rows and the knowledge is reached by the program exactly when it is reached
by the candidate.** -/
theorem program_reachable_iff (offers : Offers Q rules code) (zone : R → Z) (s : State Tm O)
    (φ : State Tm O → Prop) :
    (∃ t : State Tm O,
        (theoryOf (State Tm O) (Succ (step X O E (P ∪ Q)).toStep)).MultiStep s t ∧ φ t) ↔
      ∃ u : RState Tm O R (Rule Tm) Z,
        (theoryOf (RState Tm O R (Rule Tm) Z) (Succ (rstep X O R E (ofRules Z) P).toStep)).MultiStep
          (holding s rules code zone) u ∧ φ u.toState := by
  refine (programCorrespondence R X E (P := P) offers zone).reachable_iff φ
    (fun u : RState Tm O R (Rule Tm) Z => φ u.toState) ?_ rfl
  rintro origin current rfl
  exact Iff.rfl

end Program

section Configurations

universe uO uT uH uE uOcc uR uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} [DecidableEq O] {R : Type uR} [DecidableEq R] {Z : Type uZ}
  (X : Frames Tm Hom) (E : Extensions.{uO, uH, uE} Hom) (code : R → Rule Tm) (zone : R → Z)

/-- **Configurations and the systems they present, as an operational correspondence**: a
configuration is related to the system of its ambient program with the rules it holds; a move of the
configuration is a reduction of the system, and every reduction of the system is a move. -/
def configCorrespondence :
    OperationalCorrespondence (theoryOf (Config Tm O R) (Moves X E code zone))
      (theoryOf (Equivalence.System Tm O) (Equivalence.Reduces X O E)) where
  related κ S := S = κ.system code
  readStep := by
    rintro origin current next rfl moved
    have reduces : Equivalence.Reduces X O E (origin.system code) next := moved
    have same : next.program = (origin.system code).program := reduces.1
    refine .inr ⟨⟨origin.ambient, origin.held, next.state⟩, ?_, (system_of_program same).symm⟩
    refine (moves_iff X E code zone origin _).mpr ⟨rfl, rfl, ?_⟩
    rw [system_of_program same]
    exact reduces
  forward := by
    rintro origin after current rfl moved
    have reduces : Equivalence.Reduces X O E (origin.system code) (after.system code) :=
      ((moves_iff X E code zone origin after).mp moved).2.2
    exact ⟨after.system code, path_of_run (Relation.ReflTransGen.single reduces), rfl⟩

/-- **A property of the rows and the knowledge is reached by the moves of a configuration exactly
when it is reached by the reductions of the system it presents.** -/
theorem config_reachable_iff (κ : Config Tm O R) (φ : State Tm O → Prop) :
    (∃ κ' : Config Tm O R,
        (theoryOf (Config Tm O R) (Moves X E code zone)).MultiStep κ κ' ∧ φ κ'.state) ↔
      ∃ S : Equivalence.System Tm O,
        (theoryOf (Equivalence.System Tm O) (Equivalence.Reduces X O E)).MultiStep
          (κ.system code) S ∧ φ S.state := by
  refine (configCorrespondence X E code zone).reachable_iff
    (fun κ' : Config Tm O R => φ κ'.state) (fun S : Equivalence.System Tm O => φ S.state) ?_ rfl
  rintro origin current rfl
  exact Iff.rfl

end Configurations

#print axioms path_of_run
#print axioms programCorrespondence
#print axioms program_reachable_iff
#print axioms configCorrespondence
#print axioms config_reachable_iff

namespace Derived

open OneFrame (Terms frames ext)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence
  (Congruent MayBarb Pattern candidate_congruent reprogram)

section Link

universe uT uS uO

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S) {O : Type uO} [DecidableEq O]
  [Infinite O]

/-- **A derived link adds nothing, as an operational correspondence**: the program with the derived
link against the program without it, two states being related when they are congruent beside the
program without the link. -/
def derivedCorrespondence {P : Program (Terms T)} {a m b : T}
    (groundA : ∀ σ : S, A.apply σ a = a) (groundM : ∀ σ : S, A.apply σ m = m)
    (groundB : ∀ σ : S, A.apply σ b = b) (first : link a m ∈ P) (second : link m b ∈ P) :
    OperationalCorrespondence
      (theoryOf (State (Terms T) O) (Succ (step (frames A) O (ext A) (P ∪ {link a b})).toStep))
      (theoryOf (State (Terms T) O) (Succ (step (frames A) O (ext A) P).toStep)) where
  related s u := Congruent (frames A) O (ext A) (MayBarb (frames A)) ⟨P, s⟩ ⟨P, u⟩
  readStep := by
    intro origin current next related moved
    have congruent :
        Congruent (frames A) O (ext A) (MayBarb (frames A)) ⟨P, current⟩ ⟨P, origin⟩ :=
      Congruent.symm related
    obtain ⟨W, movedW, relatedW⟩ :=
      candidate_congruent.reduces congruent (S' := ⟨P, next⟩) ⟨rfl, moved⟩
    obtain ⟨Wprogram, Wstate⟩ := W
    obtain ⟨program, g, admitted, same⟩ := movedW
    have sameProgram : Wprogram = P := program
    subst sameProgram
    exact .inr ⟨Wstate, ⟨reprogram g (Or.inl g.member), admitted, same⟩, relatedW.symm⟩
  forward := by
    intro origin after current related moved
    obtain ⟨v, reachedV, relatedV⟩ :=
      step_with_derived A groundA groundM groundB first second moved P
    obtain ⟨W, reachedW, relatedW⟩ := Congruent.reaches related (reaches_of_run A reachedV)
    obtain ⟨program, runW⟩ := run_of_reaches A reachedW
    obtain ⟨Wprogram, Wstate⟩ := W
    have sameProgram : Wprogram = P := program
    subst sameProgram
    exact ⟨Wstate, path_of_run runW, relatedV.trans relatedW⟩

/-- **With the derived link and without it, the same barbs are reachable from every state.** -/
theorem derived_same_barbs {P : Program (Terms T)} {a m b : T}
    (groundA : ∀ σ : S, A.apply σ a = a) (groundM : ∀ σ : S, A.apply σ m = m)
    (groundB : ∀ σ : S, A.apply σ b = b) (first : link a m ∈ P) (second : link m b ∈ P)
    (s : State (Terms T) O) (p : Pattern (Terms T)) :
    (∃ t : State (Terms T) O,
        (theoryOf (State (Terms T) O)
          (Succ (step (frames A) O (ext A) (P ∪ {link a b})).toStep)).MultiStep s t ∧
          MayBarb (frames A) p t) ↔
      ∃ u : State (Terms T) O,
        (theoryOf (State (Terms T) O) (Succ (step (frames A) O (ext A) P).toStep)).MultiStep s u ∧
          MayBarb (frames A) p u := by
  refine (derivedCorrespondence A groundA groundM groundB first second).reachable_iff
    (fun t : State (Terms T) O => MayBarb (frames A) p t)
    (fun u : State (Terms T) O => MayBarb (frames A) p u) ?_ (Congruent.refl _)
  intro origin current related
  have congruent :
      Congruent (frames A) O (ext A) (MayBarb (frames A)) ⟨P, origin⟩ ⟨P, current⟩ := related
  exact ⟨candidate_congruent.barbs congruent p, candidate_congruent.barbs congruent.symm p⟩

end Link

namespace Atoms

open Mettapedia.Logic.LP
open Examples (Tm X E c)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- **The instance**: the chain with the derived link, against the chain. -/
def chainCorrespondence :
    OperationalCorrespondence (theoryOf (State Tm ℕ) (Succ (step X ℕ E withDerived).toStep))
      (theoryOf (State Tm ℕ) (Succ (step X ℕ E chain).toStep)) :=
  derivedCorrespondence action (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (Or.inl rfl)
    (Or.inr rfl)

/-- From the token, the chain with the derived link and the chain reach the same barbs. -/
theorem same_barbs_token (p : Pattern Tm) :
    (∃ t : State Tm ℕ,
        (theoryOf (State Tm ℕ) (Succ (step X ℕ E withDerived).toStep)).MultiStep
          Examples.tokenState t ∧ MayBarb X p t) ↔
      ∃ u : State Tm ℕ,
        (theoryOf (State Tm ℕ) (Succ (step X ℕ E chain).toStep)).MultiStep
          Examples.tokenState u ∧ MayBarb X p u :=
  derived_same_barbs action (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (Or.inl rfl)
    (Or.inr rfl) Examples.tokenState p

/-- **With the derived link, the row `3` is reached in one firing.** -/
theorem three_with_derived :
    ∃ t : State Tm ℕ,
      (theoryOf (State Tm ℕ) (Succ (step X ℕ E withDerived).toStep)).MultiStep
        Examples.tokenState t ∧ MayBarb X ⟨PUnit.unit, c 3⟩ t :=
  ⟨(tokenFiring (P := withDerived) 3 (Or.inr rfl)).result X Examples.tokenState,
    .step ⟨tokenFiring 3 (Or.inr rfl), derived_admitted, rfl⟩ (.refl _),
    1, by decide, PUnit.unit, Subst.id atoms, Subst.id atoms,
    fun e inside => by
      have equation : e ∈ [(c 1, c 1)] := inside
      obtain rfl := List.mem_singleton.mp equation
      rfl,
    rfl⟩

/-- **So the chain reaches the row `3` as well**, in a run that the correspondence gives. -/
theorem three_without_derived :
    ∃ u : State Tm ℕ,
      (theoryOf (State Tm ℕ) (Succ (step X ℕ E chain).toStep)).MultiStep
        Examples.tokenState u ∧ MayBarb X ⟨PUnit.unit, c 3⟩ u :=
  (same_barbs_token _).mp three_with_derived

#print axioms chainCorrespondence
#print axioms same_barbs_token
#print axioms three_with_derived
#print axioms three_without_derived

end Atoms

#print axioms derivedCorrespondence
#print axioms derived_same_barbs

end Derived

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences
