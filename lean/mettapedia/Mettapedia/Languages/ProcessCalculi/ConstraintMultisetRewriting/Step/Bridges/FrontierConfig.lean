import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierMoves

/-!
# Whole plain-source configurations and a native named frontier controller

The target expands a word by all its enabled named native children. Its
transition definition is the generic frontier controller and mentions no
source transition or representation proof. The relation pairs every live
source branch with one target leaf at the source's current global world.

The source scope counter may increase while other leaves remain in place.
Their native representations are transported by `Represents.mono`. Failed
leaves are explicitly retired; finished leaves remain in the answer bag.
This is the plain fragment without mutable shared spaces or evaluation of
held source text. The target's macro expansion is a family of native firings,
not a claim that all those firings form one raw atomic firing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierConfig

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open SourceLanguage Hosting Hosting.Alternatives
open Classical

variable {S : Signature} {Γ : Ctx S} {star : S.Srt}
  {κ : Keys S} {D : Discipline S Γ star} (P : SourceLanguage.Program κ Γ star D.Ty)
  (N : Nodes S Γ star) (q : Comp κ Γ star D.Ty)
  (supply : Nat → Term S Γ star)

abbrev TargetState := Frontier.State (List RuleName)

def ValidRetired (retired : Multiset (List RuleName)) : Prop :=
  (∀ word ∈ retired, ∃ state active, NamedFrom N P q word state active) ∧
    ∀ word ∈ retired, ∀ state active, NamedFrom N P q word state active →
      Terminal N P state ∧ ¬ StateFinished N state active

structure Represents (configuration : Config κ Γ star D.Ty) (frontier : TargetState) : Prop where
  leaves : Multiset.Rel (fun branch word => HostedEvents.Related N P q (configuration.world, branch) word)
    (configuration.branches.filter fun branch => Solvable branch.store) frontier.leaves
  retired : ValidRetired P N q frontier.retired

def source : GSLT := Mettapedia.OSLF.Framework.GSLTTypeSynthesis.equalityGSLT
  (Config κ Γ star D.Ty) (SourceLanguage.Step D P supply)

abbrev target : GSLT := FrontierNames.target P N q

theorem of_tracing {configuration : Config κ Γ star D.Ty}
    {leaves : Multiset (Branch κ Γ star D.Ty × List RuleName)} {retired : Multiset (List RuleName)}
    (tracing : Tracing N P q configuration leaves retired) :
    Represents P N q configuration ⟨leaves.map Prod.snd, retired⟩ := by
  refine ⟨?_, tracing.graveyardReached, tracing.graveyard⟩
  rw [← tracing.branches, Multiset.rel_map]
  apply Multiset.rel_refl_of_refl_on
  intro item member
  have alive : Solvable item.1.store := by
    have mapped := Multiset.mem_map_of_mem Prod.fst member
    rw [tracing.branches] at mapped
    exact (Multiset.mem_filter.mp mapped).2
  exact ⟨tracing.plain item member, alive, tracing.reached item member,
    tracing.uniform item member⟩

theorem initial (spaces : Term S Γ star → Multiset (Row κ Γ star))
    (plainQ : PlainComp q) (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) :
    Represents P N q (Config.initial spaces q) ⟨{[]}, 0⟩ :=
  of_tracing P N q (tracing_initial N spaces q plainQ unopened)

theorem move_not_finished {world nextWorld : World κ Γ star} {branch : Branch κ Γ star D.Ty}
    {branches : Multiset (Branch κ Γ star D.Ty)} (move : Move D P supply world branch nextWorld branches) :
    ¬ branch.Finished (D := D) := by
  rintro ⟨frames, value, focus⟩
  rcases branch with ⟨store, oldFocus, oldFrames, pending⟩
  simp only at frames focus
  subst oldFocus oldFrames
  exact Move.value_still move

theorem retire_valid (plainP : PlainProgram P)
    {world nextWorld : World κ Γ star} {branch : Branch κ Γ star D.Ty}
    {branches : Multiset (Branch κ Γ star D.Ty)} {word : List RuleName} {old : Multiset (List RuleName)}
    (paired : HostedEvents.Related N P q (world, branch) word)
    (previous : ValidRetired P N q old) (move : Move D P supply world branch nextWorld branches) :
    ValidRetired P N q (Frontier.retire (HostedEvents.targetSystem (D := D) N P q) word old) := by
  by_cases empty : Fintype.card ((HostedEvents.targetSystem (D := D) N P q).Choice word) = 0
  · have counts := Fintype.card_congr ((HostedEvents.bisimulation plainP).choices paired)
    have failing := (FrontierMoves.source_empty_iff_fail paired.plain paired.live move).mp (counts.trans empty)
    simp only [Frontier.retire, if_pos empty]
    constructor
    · intro history member
      rcases Multiset.mem_cons.mp member with rfl | older
      · exact paired.reached
      · exact previous.1 history older
    · intro history member state active reached
      rcases Multiset.mem_cons.mp member with rfl | older
      · have represents := paired.uniform state active reached
        refine ⟨fail_still N (supply := supply) plainP represents paired.plain failing, ?_⟩
        intro finished
        exact not_finished_of_fail failing ((Hosting.finished_iff N represents).mpr finished).1
      · exact previous.2 history older state active reached
  · simpa only [Frontier.retire, if_neg empty] using previous

theorem advance (plainP : PlainProgram P)
    {world nextWorld : World κ Γ star} {branch : Branch κ Γ star D.Ty}
    {branches rest : Multiset (Branch κ Γ star D.Ty)}
    {word : List RuleName} {tail retired : Multiset (List RuleName)}
    (paired : HostedEvents.Related N P q (world, branch) word)
    (others : Multiset.Rel (fun other history => HostedEvents.Related N P q (world, other) history)
      (rest.filter fun other => Solvable other.store) tail)
    (previous : ValidRetired P N q retired)
    (move : Move D P supply world branch nextWorld branches) :
    Represents P N q ⟨nextWorld, branches + rest⟩
      ⟨Frontier.children (HostedEvents.targetSystem (D := D) N P q) word + tail,
        Frontier.retire (HostedEvents.targetSystem (D := D) N P q) word retired⟩ := by
  constructor
  · rw [Multiset.filter_add]
    apply (FrontierMoves.target_children N q plainP paired move).add
    exact others.mono (fun other _ history _ represented =>
      FrontierMoves.related_world_mono N q represented (Move.scope_le move))
  · exact retire_valid P N q supply plainP paired previous move

theorem forward (plainP : PlainProgram P) {before after : Config κ Γ star D.Ty} {current : TargetState}
    (represented : Represents P N q before current) (moved : SourceLanguage.Step D P supply before after) :
    ∃ next, (target P N q).Step current next ∧ Represents P N q after next := by
  obtain ⟨world, nextWorld, branch, rest, branches, live, move⟩ := moved
  have pairedLeaves := represented.leaves
  rw [Multiset.filter_cons_of_pos (p := fun branch => Solvable branch.store) rest live] at pairedLeaves
  obtain ⟨word, tail, paired, others, split⟩ := Multiset.rel_cons_left.mp pairedLeaves
  rcases current with ⟨leaves, retired⟩
  change leaves = word ::ₘ tail at split
  subst leaves
  have unfinished : ¬ FinishedClass N P q word := fun finished =>
    move_not_finished P supply move ((HostedEvents.finished_iff paired).mpr finished)
  exact ⟨_, Frontier.Unfold.expand word tail retired unfinished,
    advance P N q supply plainP paired others represented.retired move⟩

theorem backward (plainP : PlainProgram P) {before : Config κ Γ star D.Ty} {current next : TargetState}
    (represented : Represents P N q before current) (moved : (target P N q).Step current next) :
    ∃ after, SourceLanguage.Step D P supply before after ∧ Represents P N q after next := by
  cases moved with
  | expand word tail retired unfinished =>
    obtain ⟨branch, liveRest, paired, others, splitLive⟩ := Multiset.rel_cons_right.mp represented.leaves
    have member : branch ∈ before.branches.filter (fun branch => Solvable branch.store) := by
      rw [splitLive]
      exact Multiset.mem_cons_self _ _
    obtain ⟨inSource, live⟩ := Multiset.mem_filter.mp member
    obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem inSource
    have restEq : rest.filter (fun branch => Solvable branch.store) = liveRest := by
      rw [split, Multiset.filter_cons_of_pos (p := fun branch => Solvable branch.store) rest live] at splitLive
      exact (Multiset.cons_inj_right branch).mp splitLive
    rw [← restEq] at others
    have notFinished : ¬ branch.Finished (D := D) := fun finished =>
      unfinished ((HostedEvents.finished_iff paired).mp finished)
    obtain ⟨nextWorld, branches, move⟩ := plain_moves (supply := supply) before.world paired.plain notFinished
    refine ⟨⟨nextWorld, branches + rest⟩, ?_, advance P N q supply plainP paired others represented.retired move⟩
    exact Step.of_eq split rfl live move

def correspondence (plainP : PlainProgram P) :
    OperationalCorrespondence (source P supply) (target P N q) where
  related := Represents P N q
  readStep represented moved := .inr (backward P N q supply plainP represented moved)
  forward represented moved := by
    obtain ⟨next, step, related⟩ := forward P N q supply plainP represented moved
    exact ⟨next, ⟨.cons ⟨step⟩ (.refl next)⟩, related⟩

theorem answers_eq {configuration : Config κ Γ star D.Ty} {frontier : TargetState}
    (represented : Represents P N q configuration frontier) :
    configuration.answers (D := D) = Frontier.answers (FinishedClass N P q) (classAnswer N P q) frontier := by
  have compared := Frontier.answers_eq
    (R := fun (branch : Branch κ Γ star D.Ty) (word : List RuleName) =>
      HostedEvents.Related N P q (configuration.world, branch) word)
    (leftFinished := fun branch => branch.Finished (D := D))
    (rightFinished := FinishedClass N P q)
    (fun pair => HostedEvents.finished_iff pair)
    (fun (branch : Branch κ Γ star D.Ty) => branch.answer (D := D)) (classAnswer N P q)
    (fun pair finished => (HostedEvents.answer_eq pair finished).symm)
    (show Frontier.Related (fun branch word => HostedEvents.Related N P q (configuration.world, branch) word)
      ⟨configuration.branches.filter (fun branch => Solvable branch.store), 0⟩
      ⟨frontier.leaves, 0⟩ from ⟨represented.leaves, .zero⟩)
  have split : configuration.branches.filter (fun branch => branch.Finished (D := D) ∧ Solvable branch.store) =
      (configuration.branches.filter fun branch => Solvable branch.store).filter (fun branch => branch.Finished (D := D)) := by
    rw [Multiset.filter_filter]
  change Multiset.map _ (configuration.branches.filter _) = _
  rw [split]
  exact compared

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierConfig

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierConfig.forward
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierConfig.backward
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierConfig.correspondence
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierConfig.answers_eq
