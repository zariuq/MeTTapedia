import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketQueryCuts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketQueryControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.ResidualModels

/-!
# A third tell hides a genuine pair-cut countermodel

The native reader counts the matches of F(1,0), with the original knowledge
F(0,1)=0. A separate writer takes physical occurrence 1 and tells nothing.
A third event tells F(1,0)=0. Constant zero and first projection are actual
source models. The pair retains the projection countermodel, whereas the
three-event cut excludes it by the third tell.

All packet cuts use one family, its original positional indices and its
original use tags. The countermodel also realizes every capture anchor, so
its exclusion cannot be attributed to an uninitialized omitted packet.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.PairCutControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open MeTTaCalculus.OccurrenceCommits (Enabled regionOf mem_regionOf fire)
open ContextualNonprincipalCountControls
open NativePacketQueryControls.Nonprincipal
  (state firing enabled actual_native_admitted sourcePattern reader_checks literal_one_not_seen)
open NativePacketStep (packetAction)
open NativePacketRounds (useTag)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Nat)

private abbrev A := packetAction (S := base) (O := Nat) (Γ := []) (sort := ())
private abbrev target : Frames.Frame base := ⟨Empty,locals⟩
private abbrev projection : Assignment active target.arity := model locals (.var .zero)
private abbrev constantZero : Assignment active target.arity := model locals (literal 0)

/-- The existing writer with only its tell removed. -/
def pureWriter : LiveFiring state where
  rule := ⟨[literal 1],[],[],[],[]⟩
  selection := ⟨[1],[],[]⟩
  outputs := outputs
  patterns := []
  fuel := 0

/-- The removed tell is an independently admitted third event. -/
def thirdTell : LiveFiring state where
  rule := ⟨[],[],[(sourcePattern,literal 0)],[],[]⟩
  selection := ⟨[],[],[]⟩
  outputs := outputs
  patterns := []
  fuel := 0

def members : List (LiveFiring state) := [firing,pureWriter,thirdTell]
def readerIndex : Fin members.length := ⟨0,by decide +kernel⟩
def writerIndex : Fin members.length := ⟨1,by decide +kernel⟩
def tellerIndex : Fin members.length := ⟨2,by decide +kernel⟩

theorem indices_differ : readerIndex ≠ writerIndex := by
  intro same
  have values := congrArg Fin.val same
  change (0 : Nat) = 1 at values
  cases values

noncomputable def query := NativePacketQueryView.countQuery
  (O := Nat) (NativePacketStep.useObject state (useTag readerIndex)) pattern 1

abbrev labels := NativePacketRounds.label members
noncomputable abbrev pairCut := NativePacketQueryCuts.pairProblem members readerIndex writerIndex
noncomputable abbrev fullCut := NativePacketRounds.jointProblem members

theorem pure_writer_information : FamilyInformation.memberInformation pureWriter = information ++
    [(observe (literal (Γ := []) 1),observe (literal (Γ := []) 1))] := by
  with_unfolding_all rfl

theorem third_tell_information : FamilyInformation.memberInformation thirdTell = information ++
    [(observe pattern,observe (literal (Γ := []) 0))] := by
  with_unfolding_all rfl

theorem pure_writer_models {V : Type} {declaration : V → MetaArity base}
    (candidate : Assignment active declaration) (known : ContextualResidual.Models candidate information) :
    ContextualResidual.Models candidate (FamilyInformation.memberInformation pureWriter) := by
  rw [pure_writer_information]
  apply (ContextualResidual.models_append candidate information
    [(observe (literal (Γ := []) 1),observe (literal (Γ := []) 1))]).mpr
  refine ⟨known,?_⟩
  intro equation inside
  obtain rfl := List.mem_singleton.mp inside
  rfl

theorem third_tell_constant_model :
    ContextualResidual.Models constantZero (FamilyInformation.memberInformation thirdTell) := by
  rw [third_tell_information]
  apply (ContextualResidual.models_append constantZero information
    [(observe pattern,observe (literal (Γ := []) 0))]).mpr
  refine ⟨constant_model locals,?_⟩
  intro equation inside
  obtain rfl := List.mem_singleton.mp inside
  rfl

theorem third_tell_forces_zero {V : Type} {declaration : V → MetaArity base}
    (candidate : Assignment active declaration)
    (known : ContextualResidual.Models candidate (FamilyInformation.memberInformation thirdTell)) :
    instantiate candidate pattern = literal 0 := by
  have told := (ContextualResidual.models_append ..).mp (third_tell_information ▸ known) |>.2
  exact observe_injective (told _ List.mem_cons_self)

theorem pure_writer_enabled :
    Enabled (fun _ : Nat => ()) state.state.present (pureWriter.selection.commit (T := Unit)) := by
  decide +kernel

theorem third_tell_enabled :
    Enabled (fun _ : Nat => ()) state.state.present (thirdTell.selection.commit (T := Unit)) := by
  decide +kernel

theorem pure_writer_admitted : pureWriter.toNative.Realized := by
  apply (native_admits_iff pureWriter.toNative).mpr
  refine ⟨⟨by decide,by decide,rfl,rfl,rfl⟩,pure_writer_enabled,
    ⟨target,projection,pure_writer_models projection (projection_model locals)⟩,?_⟩
  intro _ _ _
  constructor
  · intro _ inside
    cases inside
  · intro _ inside
    cases inside

theorem third_tell_admitted : thirdTell.toNative.Realized := by
  apply (native_admits_iff thirdTell.toNative).mpr
  refine ⟨⟨by decide,by decide,rfl,rfl,rfl⟩,third_tell_enabled,
    ⟨target,constantZero,third_tell_constant_model⟩,?_⟩
  intro _ _ _
  constructor
  · intro _ inside
    cases inside
  · intro _ inside
    cases inside

theorem all_admitted (index : Fin members.length) : members[index].toNative.Realized := by
  fin_cases index
  · exact actual_native_admitted
  · exact pure_writer_admitted
  · exact third_tell_admitted

theorem all_shapes (index : Fin members.length) :
    (native (S := base) (O := Nat) (Γ := []) (sort := ())).Shapes members[index].toNative :=
  ((native_admits_iff (S := base) members[index].toNative).mp (all_admitted index)).1

theorem all_enabled (index : Fin members.length) :
    Enabled (fun _ : Nat => ()) state.state.present (members[index].selection.commit (T := Unit)) :=
  ((native_admits_iff members[index].toNative).mp (all_admitted index)).2.1

def projectionData : FamilyInformation.SolutionData state [members[readerIndex],members[writerIndex]] target where
  shared := Assignment.compose projection (ContextualSelectionViews.capturedTarget locals functions)
  member _ := projection
  agrees _ := rfl
  models index := by
    fin_cases index
    · exact projection_model locals
    · exact pure_writer_models projection (projection_model locals)

def constantData : FamilyInformation.SolutionData state members target where
  shared := Assignment.compose constantZero (ContextualSelectionViews.capturedTarget locals functions)
  member _ := constantZero
  agrees _ := rfl
  models index := by
    fin_cases index
    · exact constant_model locals
    · exact pure_writer_models constantZero (constant_model locals)
    · exact third_tell_constant_model

/-- The library pair fitter uses the original positions of the three-event family. -/
noncomputable def pairProjection := NativePacketQueryCuts.pairFit members readerIndex writerIndex
  indices_differ target projectionData

theorem pair_projection_model : A.Models pairProjection pairCut :=
  NativePacketQueryCuts.pairFit_model members readerIndex writerIndex indices_differ
    (all_enabled readerIndex) (all_enabled writerIndex) target projectionData

/-- Extend the same projection to every use packet, including the third.
All capture anchors are satisfied before the third tell is tested. -/
noncomputable def countermodel := NativePacketRounds.patch state members.length
  ⟨(0,target),projectionData.shared⟩ (fun _ => ⟨(0,target),projection⟩)

theorem countermodel_base : countermodel (NativePacketStep.baseObject state 0) =
    ⟨(0,target),projectionData.shared⟩ := NativePacketRounds.patch_base _ _ _ _

theorem countermodel_use (index : Fin members.length) :
    countermodel (NativePacketStep.useObject state (useTag index)) = ⟨(0,target),projection⟩ :=
  NativePacketRounds.patch_use _ _ _ _ index

/-- Completing the third capture does not change the pair's supplied base
or either selected member assignment. -/
theorem countermodel_agrees_pair :
    countermodel (NativePacketStep.baseObject state 0) = pairProjection (NativePacketStep.baseObject state 0) ∧
      countermodel (NativePacketStep.useObject state (useTag readerIndex)) =
        pairProjection (NativePacketStep.useObject state (useTag readerIndex)) ∧
      countermodel (NativePacketStep.useObject state (useTag writerIndex)) =
        pairProjection (NativePacketStep.useObject state (useTag writerIndex)) := by
  refine ⟨countermodel_base.trans ?_,(countermodel_use readerIndex).trans ?_,(countermodel_use writerIndex).trans ?_⟩
  · exact (NativePacketQueryCuts.pairFit_base members readerIndex writerIndex indices_differ target projectionData).symm
  · exact (NativePacketQueryCuts.pairFit_first members readerIndex writerIndex indices_differ target projectionData).symm
  · exact (NativePacketQueryCuts.pairFit_second members readerIndex writerIndex indices_differ target projectionData).symm

theorem countermodel_capture (index : Fin members.length) :
    A.Solves countermodel (NativePacketStep.captureRow state (useTag index),
      ContextPackets.anchor (NativePacketStep.baseObject state 0)) := by
  apply (ContextPackets.capture_solution (source := NativePacketStep.baseObject state 0)
    (target := NativePacketStep.useObject state (useTag index))
    (ContextualSelectionViews.capturedTarget locals functions) _).mpr
  rw [countermodel_base,countermodel_use]
  rfl

theorem countermodel_pair_model : A.Models countermodel pairCut := by
  apply (NativePacketQueryCuts.pair_models_iff members readerIndex writerIndex countermodel).mpr
  constructor
  · apply (NativePacketQueryCuts.member_models_iff members readerIndex (all_enabled readerIndex) countermodel).mpr
    refine ⟨?_,countermodel_capture readerIndex⟩
    rw [countermodel_use]
    exact projection_model locals
  · apply (NativePacketQueryCuts.member_models_iff members writerIndex (all_enabled writerIndex) countermodel).mpr
    refine ⟨?_,countermodel_capture writerIndex⟩
    rw [countermodel_use]
    exact pure_writer_models projection (projection_model locals)

theorem countermodel_region : regionOf labels (NativePacketStep.present state) (query.region countermodel) = {Sum.inl 1} := by
  have actual := NativePacketQueryView.source_region state 0 (useTag readerIndex) pattern countermodel labels
    (NativePacketRounds.label_old members) rfl (countermodel_capture readerIndex)
  rw [countermodel_use] at actual
  change _ = (ContextualConditionalGuards.region locals projection rows before.present pattern).image Sum.inl at actual
  rw [region_at_literal locals projection 1 (.inr rfl) rfl] at actual
  exact actual

theorem full_constant_model : A.Models (NativePacketRounds.fitData constantData) fullCut :=
  NativePacketRounds.fitData_joint constantData (by simp [members]) all_enabled

theorem full_jointly : NativeIterated.Jointly state members :=
  (NativePacketRounds.consistent_iff_jointly members (by simp [members]) all_enabled).mp
    ⟨NativePacketRounds.fitData constantData,full_constant_model⟩

/-- A genuine model of the pair selects precisely the occurrence the writer
takes. The omitted third packet has its capture anchor satisfied as well. -/
theorem pair_not_blind :
    ¬ query.IgnoresWrites A pairCut labels (NativePacketStep.selection pureWriter) := by
  intro ignored
  have member : Sum.inl 1 ∈ regionOf labels (NativePacketStep.present state) (query.region countermodel) := by
    rw [countermodel_region]
    exact Finset.mem_singleton_self _
  have matched := (mem_regionOf.mp member).2
  have refused := ignored countermodel countermodel_pair_model (Sum.inl 1)
    (by simp [NativePacketStep.selection,pureWriter])
  rw [matched] at refused
  cases refused

theorem data_reader_zero {future : Frames.Frame base}
    (data : FamilyInformation.SolutionData state members future) :
    instantiate (data.member readerIndex) pattern = literal 0 := by
  have agree := (data.agrees readerIndex).trans (data.agrees tellerIndex).symm
  calc
    instantiate (data.member readerIndex) pattern =
        instantiate (Assignment.compose (data.member readerIndex)
          (ContextualSelectionViews.capturedTarget locals functions)) (call (literal 1) (literal 0)) :=
      (Assignment.instantiate_compose (data.member readerIndex)
        (ContextualSelectionViews.capturedTarget locals functions) (call (literal 1) (literal 0))).symm
    _ = instantiate (Assignment.compose (data.member tellerIndex)
          (ContextualSelectionViews.capturedTarget locals functions)) (call (literal 1) (literal 0)) :=
      congrArg (fun captured => instantiate captured (call (literal 1) (literal 0))) agree
    _ = instantiate (data.member tellerIndex) pattern :=
      Assignment.instantiate_compose (data.member tellerIndex)
        (ContextualSelectionViews.capturedTarget locals functions) (call (literal 1) (literal 0))
    _ = literal 0 := third_tell_forces_zero (data.member tellerIndex) (data.models tellerIndex)

/-- Every actual full-cut model selects occurrence zero. The quantifier is
over all tagged substitutions and their actual contextual target frames. -/
theorem full_reader_region (substitution : TaggedAssignments.Substitution base)
    (modeled : A.Models substitution fullCut) :
    regionOf labels (NativePacketStep.present state) (query.region substitution) = {Sum.inl 0} := by
  let data := NativePacketRounds.readData members substitution modeled
  have atSource := NativePacketQueryView.family_region members readerIndex pattern substitution modeled
  have atData := NativePacketQueryView.readData_region members readerIndex substitution modeled pattern
  have native : ContextualConditionalGuards.region locals (data.member readerIndex) rows before.present pattern = {0} :=
    region_at_literal _ _ 0 (.inl rfl) (data_reader_zero data)
  exact atSource.trans (congrArg (fun seen : Finset Nat => seen.image (Sum.inl : Nat → NativePacketStep.Ports Nat))
    (atData.symm.trans native))

/-- Testing blindness only at the three-event cut loses the genuine pair
countermodel. This is the same query, labels and writer as `pair_not_blind`. -/
theorem full_blind : query.IgnoresWrites A fullCut labels (NativePacketStep.selection pureWriter) := by
  intro substitution modeled port written
  have only : port = Sum.inl 1 := by
    simpa [NativePacketStep.selection,pureWriter] using written
  subst port
  cases matched : query.region substitution (labels (Sum.inl 1)) with
  | false => rfl
  | true =>
      have inside : Sum.inl 1 ∈ regionOf labels (NativePacketStep.present state) (query.region substitution) :=
        mem_regionOf.mpr ⟨by decide +kernel,matched⟩
      rw [full_reader_region substitution modeled] at inside
      have impossible : (Sum.inl 1 : NativePacketStep.Ports Nat) = Sum.inl 0 := Finset.mem_singleton.mp inside
      cases impossible

theorem projection_refuses_third_tell :
    ¬ ContextualResidual.Models projection (FamilyInformation.memberInformation thirdTell) := by
  intro modeled
  have impossible := third_tell_forces_zero projection modeled
  have distinct : (1 : Nat) = 0 := Sum.inl.inj (Term.op.inj impossible).1
  omega

/-- The countermodel satisfies all capture anchors; the third event's actual
told equation, rather than unused-tag bookkeeping, excludes it. -/
theorem countermodel_not_full : ¬ A.Models countermodel fullCut := by
  intro modeled
  have third := NativePacketRounds.member_models_native members tellerIndex countermodel
    (NativePacketRounds.joint_models_member members tellerIndex countermodel modeled)
  rw [countermodel_use] at third
  exact projection_refuses_third_tell third

def projectionJoint : NativeResidual.Joint state firing.toNative.information pureWriter.toNative.information target where
  left := projection
  right := projection
  left_models := projection_model locals
  right_models := pure_writer_models projection (projection_model locals)
  agree := rfl

theorem projection_matches_one :
    ContextualConditionalRows.Matches locals active projection (instantiate projection pattern) (rows 1) := by
  have member : 1 ∈ ContextualConditionalGuards.region locals projection rows before.present pattern := by
    rw [region_at_literal locals projection 1 (.inr rfl) rfl]
    exact Finset.mem_singleton_self _
  exact ((ContextualConditionalGuards.mem_region locals projection rows before.present pattern 1).mp member).2

/-- The actual native reader and pure writer are not clear at their pair
information, despite joint consistency of the full three-event family. -/
theorem reader_not_clear : ¬ Clear firing pureWriter.selection pureWriter.rule pureWriter.outputs := by
  intro clear
  have ignored := (clear.blindTakes target projectionJoint 1 (List.mem_singleton_self _)).1
  have missing := ignored (.count pattern 1) (by rw [reader_checks]; exact List.mem_singleton_self _)
  exact missing projection_matches_one

theorem pair_not_clears : ¬ NativeIterated.Clears firing pureWriter := fun clear => reader_not_clear clear.1

theorem full_family_not_clear : ¬ NativeIterated.FamilyClear state members := by
  intro clear
  have pairwise : [firing,pureWriter,thirdTell].Pairwise NativeIterated.Clears := clear.pairwise
  exact pair_not_clears ((List.pairwise_cons.mp pairwise).1 pureWriter List.mem_cons_self)

def afterPresent : Finset (NativePacketStep.Ports Nat) :=
  fire (NativePacketStep.present state)
    ((NativePacketStep.selection pureWriter).commit (T := NativePacketStep.Terms base Nat [] ()))

/-- At that same actual pair countermodel, the writer's physical commit
changes the cardinality from one to zero. -/
theorem countermodel_region_after : regionOf labels afterPresent (query.region countermodel) = ∅ := by
  have subset : afterPresent ⊆ NativePacketStep.present state := by decide +kernel
  have gone : (Sum.inl 1 : NativePacketStep.Ports Nat) ∉ afterPresent := by decide +kernel
  apply Finset.eq_empty_of_forall_notMem
  intro port member
  have before : port ∈ regionOf labels (NativePacketStep.present state) (query.region countermodel) :=
    mem_regionOf.mpr ⟨subset (mem_regionOf.mp member).1,(mem_regionOf.mp member).2⟩
  rw [countermodel_region] at before
  have same : port = Sum.inl 1 := Finset.mem_singleton.mp before
  exact gone (same ▸ (mem_regionOf.mp member).1)

theorem countermodel_count_before : query.Holds countermodel labels (NativePacketStep.present state) := by
  change (regionOf labels (NativePacketStep.present state) (query.region countermodel)).card = 1
  rw [countermodel_region]
  rfl

/-- This theorem isolates the physical cardinality refusal. The returned
native frame is treated by the transported-model proof below. -/
theorem countermodel_count_after_refused : ¬ query.Holds countermodel labels afterPresent := by
  change ¬ (regionOf labels afterPresent (query.region countermodel)).card = 1
  rw [countermodel_region_after]
  decide

section ReturnedFrame

variable (execution : ContextualConditionalExecution.Firing state.locals state.state)
  (selectionEq : execution.selection = pureWriter.selection) (ruleEq : execution.rule = pureWriter.rule)

/-- The actual projection model is extended through this actual execution's
returned frame, without choosing a weak terminal frame. -/
def returnedJoint : NativeResidual.Joint state firing.toNative.information
    (NativeResidual.problemOf state execution.selection execution.rule) target where
  left := projection
  right := projection
  left_models := projection_model locals
  right_models := by
    rw [selectionEq,ruleEq]
    exact pure_writer_models projection (projection_model locals)
  agree := rfl

noncomputable def returnedCounter := ResidualModels.amalgam (s := state) execution (returnedJoint execution selectionEq ruleEq)

theorem returned_model : ContextualResidual.Models (returnedCounter execution selectionEq ruleEq)
    (firing.residualAt execution).toNative.information :=
  ResidualModels.models_amalgam (s := state) execution firing (fun _ inside => by cases inside)
    (returnedJoint execution selectionEq ruleEq)

theorem carried_pattern_one :
    instantiate (returnedCounter execution selectionEq ruleEq) (instantiate (NativeResidual.carry execution) pattern) =
      literal 1 := by
  exact (ResidualModels.read_left (s := state) execution (returnedJoint execution selectionEq ruleEq) pattern).trans rfl

theorem returned_pattern_one :
    instantiate (Assignment.compose (returnedCounter execution selectionEq ruleEq) (NativeResidual.carry execution))
      pattern = literal 1 :=
  (Assignment.instantiate_compose (returnedCounter execution selectionEq ruleEq) (NativeResidual.carry execution) pattern).trans
    (carried_pattern_one execution selectionEq ruleEq)

include selectionEq in
theorem returned_present : execution.target.present = {0} := by
  change fire state.state.present (execution.selection.commit (T := Unit)) = {0}
  rw [selectionEq]
  decide +kernel

include selectionEq in
theorem returned_no_made (occurrence : Nat) : occurrence ∉ execution.selection.made := by
  rw [selectionEq]
  simp [pureWriter]

theorem returned_region_empty :
    ContextualConditionalGuards.region
      (ContextualPublication.privateFamily state.locals execution.update.declaration)
      (returnedCounter execution selectionEq ruleEq)
      (ContextualConditionalExecution.guardRows
        (ContextualPublication.privateFamily state.locals execution.update.declaration)
        execution.target.declarations execution.target.rows)
      execution.target.present (instantiate (NativeResidual.carry execution) pattern) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro occurrence inside
  obtain ⟨present,matched⟩ := (ContextualConditionalGuards.mem_region _ _ _ _ _ occurrence).mp inside
  have same : occurrence = 0 := Finset.mem_singleton.mp (returned_present execution selectionEq ▸ present)
  subst occurrence
  rw [carried_pattern_one execution selectionEq ruleEq] at matched
  have original := (NativeResidual.matches_retained (s := state) execution (returnedCounter execution selectionEq ruleEq)
    (returned_no_made execution selectionEq 0) (literal 1)).mp matched
  change ContextualConditionalRows.Matches locals active
    (Assignment.compose (returnedCounter execution selectionEq ruleEq) (NativeResidual.carry execution))
    (literal 1) (rows 0) at original
  have before : 0 ∈ ContextualConditionalGuards.region locals
      (Assignment.compose (returnedCounter execution selectionEq ruleEq) (NativeResidual.carry execution))
      rows before.present pattern :=
    (ContextualConditionalGuards.mem_region (captures := active) locals
      (Assignment.compose (returnedCounter execution selectionEq ruleEq) (NativeResidual.carry execution))
      rows before.present pattern 0).mpr
      ⟨by decide +kernel,(returned_pattern_one execution selectionEq ruleEq).symm ▸ original⟩
  rw [region_at_literal _ _ 1 (.inr rfl) (returned_pattern_one execution selectionEq ruleEq)] at before
  have impossible : (0 : Nat) = 1 := Finset.mem_singleton.mp before
  cases impossible

omit selectionEq ruleEq in
theorem returned_checks : (firing.residualAt execution).toNative.prepared.rule.checks =
    [.count (instantiate (NativeResidual.carry execution) pattern) 1] := by
  have carried := NativeResidual.prepared_rule_carried (s := state) execution firing.selection firing.rule
    (fun occurrence => (state.state.rows occurrence).value)
    (fun occurrence => (execution.target.rows occurrence).value)
  have checks := congrArg RuleInstance.checks carried
  change firing.toNative.prepared.rule.checks.map (Check.map (instantiate (NativeResidual.carry execution))) =
    (firing.residualAt execution).toNative.prepared.rule.checks at checks
  rw [reader_checks] at checks
  exact checks.symm

include selectionEq ruleEq in
/-- The actual returned-frame residual is refused, with a transported model
of its own information whose carried count region is empty. -/
theorem returned_reader_refused : ¬ (firing.residualAt execution).toNative.Realized := by
  intro admitted
  have asked := ((native_admits_iff (S := base) (O := Nat) (Γ := []) (sort := ())
    (firing.residualAt execution).toNative).mp admitted).2.2.2
  have held := (asked (ResidualModels.extended (S := base) (O := Nat) (Γ := []) (sort := ()) (s := state) execution target)
    (returnedCounter execution selectionEq ruleEq)
    (returned_model execution selectionEq ruleEq)).1
      (.count (instantiate (NativeResidual.carry execution) pattern) 1)
      (by rw [returned_checks execution]; exact List.mem_singleton_self _)
  change (ContextualConditionalGuards.region _ _ _ _ _).card = 1 at held
  have impossible : (0 : Nat) = 1 :=
    (congrArg Finset.card (returned_region_empty execution selectionEq ruleEq)).symm.trans held
  cases impossible

end ReturnedFrame

/-- A concrete admitted native take has an actual returned frame at which
the original admitted count reader's real residual is no longer admitted. -/
theorem actual_native_reader_refused_after_writer :
    ¬ (NativeIterated.residualAfter (s := state) (g := pureWriter) pure_writer_admitted firing).toNative.Realized :=
  returned_reader_refused (LiveFiring.execution (s := state) (f := pureWriter) pure_writer_admitted)
    (LiveFiring.execution_data (s := state) (f := pureWriter) pure_writer_admitted).2.1
    (LiveFiring.execution_data (s := state) (f := pureWriter) pure_writer_admitted).1

/-- Individually admitted native events and a genuine full joint model do
not justify replacing pair-cut validation by full-cut validation. -/
theorem third_tell_masks_pair_countermodel :
    firing.toNative.Realized ∧ pureWriter.toNative.Realized ∧ thirdTell.toNative.Realized ∧
      A.Consistent pairCut ∧ A.Consistent fullCut ∧ NativeIterated.Jointly state members ∧
      (¬ query.IgnoresWrites A pairCut labels (NativePacketStep.selection pureWriter)) ∧
      query.IgnoresWrites A fullCut labels (NativePacketStep.selection pureWriter) ∧
      (¬ NativeIterated.FamilyClear state members) ∧
      (¬ (NativeIterated.residualAfter (s := state) (g := pureWriter) pure_writer_admitted firing).toNative.Realized) :=
  ⟨actual_native_admitted,pure_writer_admitted,third_tell_admitted,
    ⟨countermodel,countermodel_pair_model⟩,⟨NativePacketRounds.fitData constantData,full_constant_model⟩,
    full_jointly,pair_not_blind,full_blind,full_family_not_clear,actual_native_reader_refused_after_writer⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.PairCutControls
