import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationDefinitions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationContinuation

/-!
# Constructor membership with more than one writer

The preservation law is about the actual full-step result: retained rows keep
their predicates and the new row satisfies the declared predicate. Two
different constructor-writing rules use that law in one run. Sole ownership
is unnecessary for this generated class. An extra well-typed writer that
publishes an unevaluated addition breaks the constructor-only class.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.ConstructorWriters

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open NativeTypesOnTheStep.Computing
open NativeTypesOnTheStep.Computing.Definitions (ConTerm)
open TowerVectorsModel (numC zeroC succC addC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg D numType level1)

theorem publication_preserves {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
    (predicate : {n : Nat} → Tm Head n → Prop)
    (configuration : Configuration (S := S))
    (old : ∀ occurrence ∈ configuration.state.present,
      predicate (configuration.state.label occurrence).2.code)
    (output : TotalTerm configuration.state.frame) (generated : predicate output.2.code)
    (target : Nat) (fresh : target ∉ configuration.state.present) :
    ∀ occurrence ∈ (Continuation.fullRun configuration output target fresh).last.present,
      predicate ((Continuation.fullRun configuration output target fresh).last.label occurrence).2.code := by
  intro occurrence present
  dsimp only [Continuation.fullRun, Step.Run.last] at present ⊢
  rw [ComputationResources.result_present] at present
  rcases Finset.mem_union.mp present with retained | made
  · have former := (Finset.mem_sdiff.mp retained).1
    have distinct : occurrence ≠ target := by
      intro same
      exact fresh (same ▸ former)
    have same := ComputationResources.other_label S.levels configuration.state configuration.active
      target occurrence output (Continuation.full_admitted configuration output target fresh) distinct
    rw [same]
    exact old occurrence former
  · obtain rfl := Finset.mem_singleton.mp made
    have same := ComputationResources.result_label S.levels configuration.state configuration.active
      occurrence output (Continuation.full_admitted configuration output occurrence fresh)
    exact (congrArg (fun row : TotalTerm configuration.state.frame => predicate row.2.code) same).mpr generated

abbrev setting := Controls.setting

def initial : Configuration (S := setting) :=
  Configuration.ofTyped (empty pkg) D.zero_typed

def firstRow (Γ : Context pkg) : TotalTerm Γ :=
  ⟨numType Γ, ⟨succC zeroC, D.succ_typed D.zero_typed⟩⟩

def secondRow (Γ : Context pkg) : TotalTerm Γ :=
  ⟨numType Γ, ⟨succC (succC zeroC), D.succ_typed (D.succ_typed D.zero_typed)⟩⟩

theorem first_fresh : 1 ∉ initial.state.present := by decide

def middle : Configuration (S := setting) where
  state := (Continuation.fullRun initial (firstRow initial.state.frame) 1 first_fresh).last
  active := 1
  present := Continuation.fullRun_target initial (firstRow initial.state.frame) 1 first_fresh
  consistent := ComputationResources.result_consistent setting.levels initial.state initial.active 1
    (firstRow initial.state.frame)
    (Continuation.full_admitted initial (firstRow initial.state.frame) 1 first_fresh)

theorem second_fresh : 0 ∉ middle.state.present := by decide

def secondRun := Continuation.fullRun middle (secondRow middle.state.frame) 0 second_fresh

def twoWriters : (step setting.levels Nat).toStep.Run initial.state :=
  .cons (ComputationResources.firing setting.levels initial.state initial.active 1 (firstRow initial.state.frame))
    (Continuation.full_admitted _ _ _ first_fresh) secondRun

theorem initial_generated : ∀ occurrence ∈ initial.state.present,
    ConTerm (initial.state.label occurrence).2.code := fun _ _ => .zero

theorem first_preserves : ∀ occurrence ∈ middle.state.present,
    ConTerm (middle.state.label occurrence).2.code :=
  publication_preserves (@ConTerm) initial initial_generated (firstRow initial.state.frame)
    (.succ .zero) 1 first_fresh

theorem both_preserve : ∀ occurrence ∈ twoWriters.last.present,
    ConTerm (twoWriters.last.label occurrence).2.code :=
  publication_preserves (@ConTerm) middle first_preserves (secondRow middle.state.frame)
    (.succ (.succ .zero)) 0 second_fresh

theorem distinct_rules : firstRow (empty pkg) ≠ secondRow (empty pkg) := by
  intro same
  have codes := congrArg (fun row : TotalTerm (empty pkg) => row.2.code) same
  exact (by decide : (succC zeroC : Tower.Tm 0) ≠ succC (succC zeroC)) codes

theorem two_actual_writer_events : twoWriters.word.length = 2 ∧ twoWriters.last.present = {0} := by
  constructor
  · rfl
  · decide

def extraRow (Γ : Context pkg) : TotalTerm Γ :=
  ⟨numType Γ, ⟨addC zeroC zeroC, TowerVectorsPrograms.add_typed level1 D.zero_typed D.zero_typed⟩⟩

theorem typed_extra_writer_breaks_generatedness :
    ¬ ConTerm (extraRow (empty pkg)).2.code := by
  intro generated
  cases generated

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.ConstructorWriters

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.ConstructorWriters.publication_preserves
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.ConstructorWriters.both_preserve
