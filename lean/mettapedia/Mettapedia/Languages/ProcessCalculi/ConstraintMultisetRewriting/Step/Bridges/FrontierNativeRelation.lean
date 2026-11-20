import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierNative
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierMoves

/-!
# Ghost histories for native frontier leaves

The relation records a named history only as evidence. Native eligibility and
expansion certificates are defined without that history. Every enabled name
of the history class can fire from the supplied native representative, and
every supplied invocation extends its actual history.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives
open Classical

variable {S : Signature} {Γ : Ctx S} {star : S.Srt}
  {κ : Keys S} {D : Discipline S Γ star}
  (N : Nodes S Γ star) (P : SourceLanguage.Program κ Γ star D.Ty) (q : Comp κ Γ star D.Ty)

def Related (word : List RuleName) (leaf : Leaf S) : Prop :=
  (∃ current : HostedEvents.SourceState (κ := κ) (D := D), HostedEvents.Related N P q current word) ∧
    NamedFrom N P q word leaf.state leaf.active

theorem valid_of_related {word : List RuleName} {leaf : Leaf S} (paired : Related N P q word leaf) : Valid leaf := by
  obtain ⟨⟨current, related⟩, history⟩ := paired
  have rep := related.uniform leaf.state leaf.active history
  refine ⟨?_, ?_⟩
  · rw [rep.present]
    exact Finset.mem_insert_self _ _
  · obtain ⟨names, arity, assignment, solved⟩ := related.live
    let frame : Interface.Frames.Frame S := ⟨names, arity⟩
    have branchRead : branchReads N current.2 frame (observe (encBranch N (instantiate assignment) current.2)) :=
      ⟨assignment, solved, rfl⟩
    obtain ⟨native, known, _⟩ := (rep.reads frame _).mpr branchRead
    exact ⟨frame, native, known⟩

theorem enabled_iff (plainP : PlainProgram P) {word : List RuleName} {leaf : Leaf S}
    (paired : Related N P q word leaf) (name : RuleName) :
    HostedEvents.targetEnabled N P q word name ↔ Enabled N P leaf name := by
  obtain ⟨⟨current, related⟩, history⟩ := paired
  constructor
  · intro enabled
    obtain ⟨next, fired⟩ := HostedEvents.enabled_from_every_representative plainP related enabled history
      (freshId_not_mem leaf.state)
    obtain ⟨invocation, _⟩ := invocation_of_fires N P (before := leaf)
      (after := ⟨next, freshId leaf.state⟩) fired
    exact ⟨invocation⟩
  · rintro ⟨invocation⟩
    exact ⟨invocation.after.state, invocation.after.active, .snoc history invocation.fires⟩

theorem invocation_related (plainP : PlainProgram P) {word : List RuleName} {leaf : Leaf S}
    (paired : Related N P q word leaf) {name : RuleName} (invocation : Invocation N P leaf name) :
    Related N P q (word ++ [name]) invocation.after := by
  obtain ⟨⟨current, related⟩, history⟩ := paired
  have enabled : HostedEvents.targetEnabled N P q word name :=
    ⟨invocation.after.state, invocation.after.active, .snoc history invocation.fires⟩
  let choice : (HostedEvents.sourceSystem (D := D) P).Choice current :=
    ⟨name, (HostedEvents.enabled_iff plainP related name).mpr enabled⟩
  exact ⟨⟨_, (HostedEvents.bisimulation plainP).successors related choice⟩,
    .snoc history invocation.fires⟩

theorem finished_iff {word : List RuleName} {leaf : Leaf S} (paired : Related N P q word leaf) :
    FinishedClass N P q word ↔ StateFinished N leaf.state leaf.active := by
  obtain ⟨⟨current, related⟩, history⟩ := paired
  have representation := related.uniform leaf.state leaf.active history
  constructor
  · intro finished
    exact (Hosting.finished_iff N representation).mp ⟨(HostedEvents.finished_iff related).mpr finished, related.live⟩
  · intro finished
    exact (HostedEvents.finished_iff related).mp ((Hosting.finished_iff N representation).mpr finished).1

theorem answer_eq {word : List RuleName} {leaf : Leaf S}
    (paired : Related N P q word leaf) (finished : FinishedClass N P q word) :
    classAnswer N P q word = stateAnswer N leaf.state leaf.active := by
  obtain ⟨⟨current, related⟩, history⟩ := paired
  have sourceFinished := (HostedEvents.finished_iff related).mpr finished
  exact (HostedEvents.answer_eq related sourceFinished).trans
    (Hosting.answer_eq N (related.uniform leaf.state leaf.active history) sourceFinished).symm

def nameEquiv (plainP : PlainProgram P) {word : List RuleName} {leaf : Leaf S}
    (paired : Related N P q word leaf) (chosen : Expansion N P leaf) :
    ((HostedEvents.targetSystem (D := D) N P q).Choice word) ≃ {name // name ∈ chosen.names} :=
  Equiv.subtypeEquivRight (fun name => (enabled_iff N P q plainP paired name).trans (chosen.complete name).symm)

theorem names_card (plainP : PlainProgram P) {word : List RuleName} {leaf : Leaf S}
    (paired : Related N P q word leaf) (chosen : Expansion N P leaf) :
    Fintype.card ((HostedEvents.targetSystem (D := D) N P q).Choice word) = chosen.names.card := by
  simpa using Fintype.card_congr (nameEquiv N P q plainP paired chosen)

theorem children_related (plainP : PlainProgram P) {word : List RuleName} {leaf : Leaf S}
    (paired : Related N P q word leaf) (chosen : Expansion N P leaf) :
    Multiset.Rel (Related N P q)
      (Frontier.children (HostedEvents.targetSystem (D := D) N P q) word) chosen.children := by
  have allNames : (Finset.univ : Finset {name // name ∈ chosen.names}) = chosen.names.attach := by
    ext name
    simp
  unfold Frontier.children Expansion.children
  rw [← allNames, ← Multiset.map_univ_val_equiv (nameEquiv N P q plainP paired chosen), Multiset.map_map]
  apply Multiset.rel_map.mpr
  exact Multiset.rel_refl_of_refl_on fun name _ =>
    invocation_related N P q plainP paired (chosen.invocation name.1 _)

theorem retired_related (plainP : PlainProgram P) {word : List RuleName} {leaf : Leaf S}
    (paired : Related N P q word leaf) (chosen : Expansion N P leaf)
    {historyRetired : Multiset (List RuleName)} {nativeRetired : Multiset (Leaf S)}
    (previous : Multiset.Rel (Related N P q) historyRetired nativeRetired) :
    Multiset.Rel (Related N P q)
      (Frontier.retire (HostedEvents.targetSystem (D := D) N P q) word historyRetired)
      (Expansion.retire N P chosen nativeRetired) := by
  unfold Frontier.retire Expansion.retire
  rw [names_card N P q plainP paired chosen]
  split
  · exact previous.cons paired
  · exact previous

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.valid_of_related
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.enabled_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.children_related
