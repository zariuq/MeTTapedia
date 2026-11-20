import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierNativeCorrespondence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierNativeProbes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Unification

/-!
# Concrete native expansions and incomplete-probe controls

Two closed duplicate equations are represented by two compiler names and one
canonical physical firing. The expansion builder retains two native children.
Omitting the second name violates coverage, even though its rule and result
agree with the first. A pending probe family finds no candidates but does not
certify failure on this actual enabled input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives
open SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting.Answers.Bags (D N P1 P2 q sp supply W0 W1 X final2 eqF fT live_ff matched2 oneC)

abbrev before : Leaf MSig := initialLeaf (D := D) N P2 q

theorem start_represents : Hosting.Represents N P2 0 (initialBranch q) before.state before.active :=
  Hosting.start_represents N P2 q Hosting.Answers.Bags.q_unopened

def physical := canonicalAt before.state (schema N eqF) (schema_mem N P2 List.mem_cons_self) before.active

theorem physical_admitted : physical.Admits (Interface.Frames.contextual MSig) before.state :=
  (schema_admitted_iff N start_represents List.mem_cons_self).mpr live_ff

def first : Invocation (D := D) N P2 before (.eqn 0) where
  firing := physical
  named := rfl
  afterActive := freshId before.state
  taken := rfl
  made := rfl
  admitted := physical_admitted

def second : Invocation (D := D) N P2 before (.eqn 1) where
  firing := physical
  named := rfl
  afterActive := freshId before.state
  taken := rfl
  made := rfl
  admitted := physical_admitted

theorem same_physical_result : first.firing = second.firing ∧ first.after = second.after := ⟨rfl, rfl⟩

theorem initial_related : Related (D := D) N P2 q [] before :=
  ⟨⟨_, HostedEvents.initial (D := D) (N := N) (P := P2) (q := q) sp (by trivial)
      Hosting.Answers.Bags.q_unopened⟩, .nil _ _⟩

theorem enabled_exactly (name : RuleName) : Enabled (D := D) N P2 before name ↔ name = .eqn 0 ∨ name = .eqn 1 := by
  constructor
  · intro enabled
    have historyEnabled := (FrontierNative.enabled_iff (D := D) N P2 q
      Bridges.Controls.HostedEventsAudit.plain_program initial_related name).mpr enabled
    have sourceEnabled := (HostedEvents.enabled_iff Bridges.Controls.HostedEventsAudit.plain_program
      Bridges.Controls.HostedEventsAudit.initial_related name).mpr historyEnabled
    obtain ⟨next, move, _⟩ := sourceEnabled
    rcases next with ⟨nextWorld, nextBranch⟩
    cases move with
    | unmatched _ _ _ _ none =>
        exact False.elim (none eqF List.mem_cons_self live_ff)
    | eqn _ _ _ _ index equation found _ =>
        have bound := FrontierNames.lookup_bound found
        change index < 2 at bound
        have which : index = 0 ∨ index = 1 := by omega
        rcases which with rfl | rfl
        · exact .inl rfl
        · exact .inr rfl
  · rintro (rfl | rfl)
    · exact ⟨first⟩
    · exact ⟨second⟩

/-- The finite probe delivers concrete canonical firing data at the two actual ordinals. -/
def probe (name : RuleName) : ProbeResult (D := D) Nat N P2 before name :=
  if firstName : name = .eqn 0 then .ok (.inl (firstName.symm ▸ first))
  else if secondName : name = .eqn 1 then .ok (.inl (secondName.symm ▸ second))
  else .ok (.inr ⟨fun enabled => (enabled_exactly name).mp enabled |>.elim firstName secondName⟩)

theorem probe_ready : Ready (D := D) N P2 probe := by
  intro name _
  unfold probe
  split
  · rfl
  · split <;> rfl

def completeExpansion : Expansion (D := D) N P2 before := fromProbes (D := D) N P2 probe probe_ready

theorem expansion_names : completeExpansion.names = {.eqn 0, .eqn 1} := by
  ext name
  rw [completeExpansion.complete]
  change Enabled (D := D) N P2 before name ↔ _
  rw [enabled_exactly]
  simp

theorem two_children : completeExpansion.children.card = 2 := by
  rw [completeExpansion.children_card, expansion_names]
  decide

theorem both_are_actual_firings :
    FiresNamed N P2 (.eqn 0) before.state before.active first.after.state first.after.active ∧
      FiresNamed N P2 (.eqn 1) before.state before.active second.after.state second.after.active :=
  ⟨first.fires, second.fires⟩

theorem omitted_duplicate_is_not_coverage :
    ¬ ∃ chosen : Expansion (D := D) N P2 before, chosen.names = {RuleName.eqn 0} := by
  rintro ⟨chosen, onlyOne⟩
  have secondPresent := (chosen.complete (.eqn 1)).mpr (show Enabled (D := D) N P2 before (.eqn 1) from ⟨second⟩)
  rw [onlyOne] at secondPresent
  have impossible := Finset.mem_singleton.mp secondPresent
  cases impossible

def pendingProbe (name : RuleName) : ProbeResult (D := D) Nat N P2 before name := .error 0

theorem pending_probe_not_ready : ¬ Ready (D := D) N P2 pendingProbe :=
  pending_not_ready (D := D) N P2 pendingProbe (name := .ret) (by simp [FrontierNames.names]) rfl

theorem pending_probe_finds_nothing : acceptedNames (D := D) N P2 pendingProbe = ∅ := by
  ext name
  simp [acceptedNames, pendingProbe, ProbeResult.accepted, FrontierNativeCore.ProbeResult.accepted]

theorem empty_probe_is_not_semantic_failure :
    acceptedNames (D := D) N P2 pendingProbe = ∅ ∧ Enabled (D := D) N P2 before (.eqn 0) :=
  ⟨pending_probe_finds_nothing, ⟨first⟩⟩

noncomputable section

theorem whole_duplicate_query_reaches_two_answers :
    ∃ state : State MSig, (theory (D := D) N P2).MultiStep (initialState (D := D) N P2 q) state ∧
      answers N state = {{oneC}, {oneC}} := by
  apply (source_prefixes_iff (D := D) N P2 q sp supply Bridges.Controls.HostedEventsAudit.plain_program
    (by trivial) Hosting.Answers.Bags.q_unopened (fun bag => bag = {{oneC}, {oneC}})).mp
  exact ⟨final2, Hosting.Answers.Bags.p2_runs, Hosting.Answers.Bags.p2_answers⟩

end

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.Controls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.Controls.physical_admitted
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.Controls.two_children
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.Controls.omitted_duplicate_is_not_coverage
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.Controls.empty_probe_is_not_semantic_failure
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.Controls.whole_duplicate_query_reaches_two_answers
