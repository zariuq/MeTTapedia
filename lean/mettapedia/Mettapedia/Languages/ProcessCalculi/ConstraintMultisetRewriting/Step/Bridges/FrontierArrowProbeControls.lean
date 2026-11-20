import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierArrowControls

/-!
# A computable complete probe for an actual sequencing entry

The positive reply carries the canonical bind-start firing itself. All other
names are refuted by reflection on that actual starting row. The generic
finite builder therefore executes a complete expansion without history data
or a source-step admission premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow.ProbeControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit Hosting Hosting.Answers.Bags
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow.Controls

abbrev before : Leaf MSig := initialLeaf (D := D) N P1 rejectedQuery
abbrev afterStart : Branch mkeys [] () MTy :=
  ⟨[], .eval (.ret (sym "one")), [.bindTo [9] (sym "two") (.ret (sym "done"))], []⟩

theorem paired : LeafRep (D := D) N P1 W0 (Hosting.initialBranch rejectedQuery) before :=
  ⟨Hosting.start_represents N P1 rejectedQuery
    (query_unopened (qsite := [3]) (by decide) (by decide) ⟨trivial, trivial⟩),
    trivial, .inl ⟨rejectedQuery, rfl, trivial, trivial⟩⟩

def physical := canonicalAt before.state (bindStartRule N) (bindStartRule_mem N P1) before.active

theorem admitted : physical.Admits (Interface.Frames.contextual MSig) before.state := by
  have simple := canonical_simple (s := before.state) (member := bindStartRule_mem N P1) (a := before.active)
    rfl rfl rfl
  have shapes := canonical_shapes (s := before.state) (member := bindStartRule_mem N P1) (a := before.active)
    rfl rfl rfl rfl
  have present : before.active ∈ before.state.present := by
    rw [paired.1.present]
    exact Finset.mem_insert_self _ _
  refine ⟨shapes, enabled_single present (freshId_not_mem before.state), ?_, entails_of_no_checks rfl rfl⟩
  have live : Solvable afterStart.store := live_nil
  obtain ⟨W, target, assignment, solved⟩ := live
  have reads : branchReads N afterStart ⟨W, target⟩ (observe (encBranch N (instantiate assignment) afterStart)) :=
    ⟨assignment, solved, rfl⟩
  obtain ⟨h, readsB, told, _⟩ := (transfer_bindStart N (b := Hosting.initialBranch rejectedQuery) rfl _).mpr reads
  obtain ⟨g, known, matched⟩ := (paired.1.reads _ _).mpr readsB
  obtain ⟨u, solvedU, _⟩ := simple_amalgamate simple shapes.1 present g h known told matched.symm
  exact ⟨_, u, solvedU⟩

def first : Invocation (D := D) N P1 before .bindStart where
  firing := physical
  named := rfl
  afterActive := freshId before.state
  taken := rfl
  made := rfl
  admitted := admitted

theorem enabled_exactly (name : Name) : Enabled (D := D) N P1 before name ↔ name = .bindStart := by
  constructor
  · rintro ⟨invocation⟩
    have hygiene : Hygienic (Hosting.initialBranch (Ty := MTy) rejectedQuery) := by
      intro K v site p k fs ps same
      cases same
    have arrowP : ArrowProgram P1 := by
      intro equation member
      rw [show P1.equations = [eqF] from rfl, List.mem_singleton] at member
      subst equation
      trivial
    obtain ⟨next, child, moved, _, _⟩ := invocation_reflect (D := D) N P1 arrowP paired hygiene invocation
    change NamedMove P1 W0 ⟨[], .eval (.let_ [9] (sym "two") (.ret (sym "one")) (.ret (sym "done"))), [], []⟩
      name next child at moved
    cases moved
    rfl
  · rintro rfl
    exact ⟨first⟩

def probe (name : Name) : FrontierNativeCore.ProbeResult Nat (catalogue (D := D) N P1) before name :=
  if same : name = .bindStart then .ok (.inl (same ▸ first))
  else .ok (.inr ⟨fun enabled => same ((enabled_exactly name).mp enabled)⟩)

theorem ready : FrontierNativeCore.Ready (catalogue (D := D) N P1) probe := by
  intro name member
  unfold probe
  split <;> rfl

def chosen : Expansion (D := D) N P1 before :=
  FrontierNativeCore.fromProbes (catalogue (D := D) N P1) probe ready

theorem chosen_names : chosen.names = {.bindStart} := by
  ext name
  rw [chosen.complete]
  change Enabled (D := D) N P1 before name ↔ _
  rw [enabled_exactly, Finset.mem_singleton]

theorem one_actual_child : chosen.children.card = 1 := by
  rw [chosen.children_card, chosen_names]
  rfl

theorem actual_selection : first.firing.selection.taken = [1] ∧ first.firing.selection.made = [2] := ⟨rfl, rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow.ProbeControls
