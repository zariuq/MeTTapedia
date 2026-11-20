import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerProgressMoves
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerExecutionControls
import Mathlib.Data.Multiset.DershowitzManna

/-!
# All actual scanner schedules terminate on scoped native inputs

Live occurrences retain their own existential work annotations, including
duplicate branches. One source move replaces one labelled occurrence by its
actual live children, each with less work. Dead siblings remain in the source
configuration and cannot take a step. No normality premise or fuel bound is
used for the scanner query.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration Hosting
open NativeTypesOnTheStep.Computing
open NormalChildViews (Child)

universe u

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())
  (supply : Nat → MClosed)

def Labelled {α : Type u} (ranked : Branch (BinderCore.keys built.rules) [] () D.Ty → α → Prop)
    (configuration : Config (BinderCore.keys built.rules) [] () D.Ty) (weights : Multiset α) : Prop := by
  classical
  exact ∃ labels : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty × α),
    labels.map Prod.fst = configuration.branches.filter (fun branch => Solvable branch.store) ∧
    labels.map Prod.snd = weights ∧ ∀ pair ∈ labels, ranked pair.1 pair.2

section Configurations

variable {α : Type u} [Preorder α]
  (ranked : Branch (BinderCore.keys built.rules) [] () D.Ty → α → Prop)
  (decrease : ∀ (world nextWorld : World (BinderCore.keys built.rules) [] ())
    (before : Branch (BinderCore.keys built.rules) [] () D.Ty)
    (children : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty)) (weight : α),
    ranked before weight → NormalScannerReflection.FreshCalls built D world.scope before →
    Move D (NormalProgram.program built D) supply world before nextWorld children →
    ∀ child ∈ children, Solvable child.store → ∃ childWeight, ranked child childWeight ∧ childWeight < weight)
  (spaces : MClosed → Multiset (Row (BinderCore.keys built.rules) [] ()))
  (q : Comp (BinderCore.keys built.rules) [] () D.Ty) {qsite : (BinderCore.keys built.rules).Site}
  (qScoped : q.Scoped [qsite]) (distinct : (qsite :: q.sites).Nodup) (arrow : ArrowComp q)

include decrease qScoped distinct arrow

theorem labelled_step {before after : Config (BinderCore.keys built.rules) [] () D.Ty} {weights : Multiset α}
    (reached : Runs D (NormalProgram.program built D) supply (Config.initial spaces q) before)
    (prepared : Labelled built D ranked before weights)
    (edge : SourceLanguage.Step D (NormalProgram.program built D) supply before after) :
    ∃ nextWeights, Labelled built D ranked after nextWeights ∧
      Multiset.IsDershowitzMannaLT nextWeights weights := by
  classical
  obtain ⟨labels, projection, atWeights, known⟩ := prepared
  cases edge with
  | move world nextWorld branch rest children live moved =>
      have present : branch ∈ labels.map Prod.fst := by
        rw [projection]
        exact Multiset.mem_filter.mpr ⟨Multiset.mem_cons_self _ _, live⟩
      obtain ⟨⟨chosen, weight⟩, member, same⟩ := Multiset.mem_map.mp present
      change chosen = branch at same
      subst chosen
      obtain ⟨otherLabels, split⟩ := Multiset.exists_cons_of_mem member
      have restProjection : otherLabels.map Prod.fst = rest.filter (fun b => Solvable b.store) := by
        have projected := projection
        rw [split, Multiset.map_cons, Multiset.filter_cons_of_pos (p := fun b => Solvable b.store) rest live] at projected
        exact (Multiset.cons_inj_right branch).mp projected
      have scopedBranch := scoping_reachable spaces q (NormalProgramFormation.equations_formed built D)
        qScoped distinct arrow _ reached branch (Multiset.mem_cons_self _ _)
      have progress := decrease world nextWorld branch children weight (known _ member)
        (NormalScannerReflection.fresh_of_scoping built D scopedBranch) moved
      let liveChildren := children.filter (fun b => Solvable b.store)
      have choices : ∀ child ∈ liveChildren, ∃ childWeight, ranked child childWeight ∧ childWeight < weight := by
        intro child included
        obtain ⟨made, alive⟩ := Multiset.mem_filter.mp included
        exact progress child made alive
      let selected : Branch (BinderCore.keys built.rules) [] () D.Ty → α := fun child =>
        if included : child ∈ liveChildren then Classical.choose (choices child included) else weight
      have selected_spec : ∀ child ∈ liveChildren, ranked child (selected child) ∧ selected child < weight := by
        intro child included
        dsimp only [selected]
        rw [dif_pos included]
        exact Classical.choose_spec (choices child included)
      let childLabels := liveChildren.map (fun child => (child, selected child))
      have childProjection : childLabels.map Prod.fst = liveChildren := by
        simp [childLabels]
      refine ⟨(childLabels + otherLabels).map Prod.snd, ⟨childLabels + otherLabels, ?_, rfl, ?_⟩, ?_⟩
      · rw [Multiset.map_add, childProjection, restProjection]
        exact (Multiset.filter_add (fun b => Solvable b.store) children rest).symm
      · intro pair included
        rcases Multiset.mem_add.mp included with made | kept
        · obtain ⟨child, inside, rfl⟩ := Multiset.mem_map.mp made
          exact (selected_spec child inside).1
        · apply known pair
          rw [split]
          exact Multiset.mem_cons_of_mem kept
      · refine ⟨otherLabels.map Prod.snd, childLabels.map Prod.snd, {weight}, by simp, ?_, ?_, ?_⟩
        · rw [Multiset.map_add]
          exact add_comm _ _
        · rw [← atWeights, split, Multiset.map_cons]
          exact (Multiset.singleton_add _ _).symm.trans (add_comm _ _)
        · intro childWeight included
          obtain ⟨pair, pairMember, rfl⟩ := Multiset.mem_map.mp included
          obtain ⟨child, childMember, rfl⟩ := Multiset.mem_map.mp pairMember
          exact ⟨weight, Multiset.mem_singleton_self _, (selected_spec child childMember).2⟩

theorem labelled_normalizes [WellFoundedLT α]
    (configuration : Config (BinderCore.keys built.rules) [] () D.Ty)
    (reached : Runs D (NormalProgram.program built D) supply (Config.initial spaces q) configuration)
    (weights : Multiset α) (prepared : Labelled built D ranked configuration weights) :
    Acc (fun after before => SourceLanguage.Step D (NormalProgram.program built D) supply before after) configuration := by
  have all : ∀ score : Multiset α,
      ∀ current : Config (BinderCore.keys built.rules) [] () D.Ty,
        Runs D (NormalProgram.program built D) supply (Config.initial spaces q) current →
        Labelled built D ranked current score →
        Acc (fun after before => SourceLanguage.Step D (NormalProgram.program built D) supply before after) current := by
    intro score
    have wellFounded : WellFounded (Multiset.IsDershowitzMannaLT : Multiset α → Multiset α → Prop) :=
      Multiset.wellFounded_isDershowitzMannaLT
    refine wellFounded.induction (C := fun score =>
      ∀ current : Config (BinderCore.keys built.rules) [] () D.Ty,
        Runs D (NormalProgram.program built D) supply (Config.initial spaces q) current →
        Labelled built D ranked current score →
        Acc (fun after before => SourceLanguage.Step D (NormalProgram.program built D) supply before after) current)
      score ?_
    intro score smaller current prefixRun ready
    refine .intro current ?_
    intro next edge
    obtain ⟨nextScore, nextReady, less⟩ :=
      labelled_step built D supply ranked decrease spaces q qScoped distinct arrow prefixRun ready edge
    exact smaller nextScore less next (prefixRun.tail edge) nextReady
  exact all weights configuration reached prepared

end Configurations

theorem scanner_normalizes {n : Nat} (term : Tower.Tm n) :
    Acc (fun after before => SourceLanguage.Step D (NormalProgram.program built D) supply before after)
      (Config.initial (fun _ => 0) (NormalScanner.query built (encodeTm term))) := by
  classical
  let ranked := NormalScannerProgressMoves.Ranked built D (⟨n, term⟩ : Child)
  have decrease : ∀ (world nextWorld : World (BinderCore.keys built.rules) [] ())
      (before : Branch (BinderCore.keys built.rules) [] () D.Ty)
      (children : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty)) (weight : Nat),
      ranked before weight → NormalScannerReflection.FreshCalls built D world.scope before →
      Move D (NormalProgram.program built D) supply world before nextWorld children →
      ∀ child ∈ children, Solvable child.store → ∃ childWeight, ranked child childWeight ∧ childWeight < weight := by
    intro world nextWorld before children weight known fresh moved
    obtain ⟨certificate, scored⟩ := known
    exact NormalScannerProgressMoves.move built D supply scored fresh moved
  let q := NormalScanner.query built (Ty := D.Ty) (encodeTm term)
  let current := Config.initial (fun _ => 0) q
  let branch : Branch (BinderCore.keys built.rules) [] () D.Ty := ⟨[], .eval q, [], []⟩
  have branchRanked : ranked branch (NormalScannerProgressRank.scanCost term) := by
    refine ⟨NormalScannerCertificates.initial built D term, ?_⟩
    exact .scan _ ⟨n, term⟩ [] (NormalProbeFreshness.determines_include built [] Hosting.initial_live (encodeTm term)) .done .done
  have prepared : Labelled built D ranked current {NormalScannerProgressRank.scanCost term} := by
    refine ⟨{(branch, NormalScannerProgressRank.scanCost term)}, ?_, ?_, ?_⟩
    · rw [Multiset.map_singleton]
      change {branch} = Multiset.filter (fun b => Solvable b.store) {branch}
      have live : Solvable branch.store := Hosting.initial_live
      rw [Multiset.filter_singleton, if_pos live]
    · simp
    · intro pair member
      rw [Multiset.mem_singleton] at member
      subst pair
      exact branchRanked
  exact labelled_normalizes built D supply ranked decrease (fun _ => 0) q
    (NormalScanner.query_scoped built _) (NormalScanner.query_distinct built _)
    (NormalScanner.query_arrows built _) current .refl _ prepared

theorem identity_scanner_normalizes :
    Acc (fun after before => SourceLanguage.Step D (NormalProgram.program ExecutionControls.built D)
      supply before after)
      (Config.initial (fun _ => 0) (NormalScanner.query ExecutionControls.built (encodeTm NormalScanner.lambdaExample))) :=
  scanner_normalizes ExecutionControls.built D supply NormalScanner.lambdaExample

theorem beta_below_binder_scanner_normalizes :
    Acc (fun after before => SourceLanguage.Step D (NormalProgram.program ExecutionControls.built D)
      supply before after)
      (Config.initial (fun _ => 0) (NormalScanner.query ExecutionControls.built
        (encodeTm NormalScannerExecutionControls.betaBelowBinder))) :=
  scanner_normalizes ExecutionControls.built D supply NormalScannerExecutionControls.betaBelowBinder

theorem beta_below_binder_no_live_finish :
    ¬ ∃ after branch,
      Runs D (NormalProgram.program ExecutionControls.built D) supply
        (Config.initial (fun _ => 0) (NormalScanner.query ExecutionControls.built
          (encodeTm NormalScannerExecutionControls.betaBelowBinder))) after ∧
      branch ∈ after.branches ∧ branch.Finished (D := D) ∧ Solvable branch.store := by
  rintro ⟨after, branch, run, member, finished, live⟩
  exact NormalScannerExecutionControls.beta_below_binder_not_normal
    (NormalScannerReflection.finished_reflects ExecutionControls.built D supply
      NormalScannerExecutionControls.betaBelowBinder run member finished live)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerProgress

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerProgress.scanner_normalizes
