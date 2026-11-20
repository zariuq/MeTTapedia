import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketQueryView
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.SchemaControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNonprincipalCountControls

/-!
# Native symbolic row queries and the limits of fixed match sets

The positive count uses the actual nonprincipal contextual information and
its native admission. Two earned models select different physical rows.
The decoder also observes the existing generative schema with its latent
equation. Equality of rigid row packets remains a distinct observation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketQueryControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open MeTTaCalculus.OccurrenceCommits (Enabled regionOf mem_regionOf)
open ContextPackets (Value Environment)
open NativePacketStep (Terms Ports RowCode packetAction)
open NativePacketQueryView

theorem different_physical_packets {S : Signature} {O : Type} {Γ : Ctx S} {sort : S.Srt}
    (substitution : TaggedAssignments.Substitution S) {first second : O} (different : first ≠ second)
    (firstCode secondCode : RowCode S Γ sort) (firstEnvironment secondEnvironment : Environment S) :
    ContextPackets.apply S substitution (Value.row (first,firstCode) firstEnvironment : Terms S O Γ sort) ≠
      ContextPackets.apply S substitution (Value.row (second,secondCode) secondEnvironment) := by
  intro equal
  exact different (congrArg Prod.fst (Value.row.inj equal).1)

namespace Schema

open ContextualSelectionViews.Controls (base locals captures active p a b rawA rawB)

def target : TaggedAssignments.Object base := (0,⟨_,active⟩)

def code : RowCode base [] () :=
  ⟨⟨_,locals⟩,⟨_,captures⟩,SchemaControls.schemaRow⟩

def captured : Assignment captures active :=
  Assignment.compose SchemaControls.schemaModel (ContextualSelectionViews.capturedTarget locals captures)

def packet (physical : Nat) : Terms base Nat [] () :=
  Value.row (physical,code) ⟨⟨_,captures⟩,target,captured⟩

theorem actual_schema_matches_both :
    rowMatches target (p a) (TaggedAssignments.identity base) (packet 7) ∧
      rowMatches target (p b) (TaggedAssignments.identity base) (packet 7) := by
  constructor
  · apply (rowMatches_identity target (p a) (packet 7)).mpr
    exact (matchesAt_row target (p a) 7 code captured).mpr
      SchemaControls.actual_conditional_row_has_both_matches.1
  · apply (rowMatches_identity target (p b) (packet 7)).mpr
    exact (matchesAt_row target (p b) 7 code captured).mpr
      SchemaControls.actual_conditional_row_has_both_matches.2

theorem different_identity_same_schema_matches :
    rowMatches target (p a) (TaggedAssignments.identity base) (packet 8) ∧
      packet 7 ≠ packet 8 := by
  refine ⟨?_,?_⟩
  · apply (rowMatches_identity target (p a) (packet 8)).mpr
    exact (matchesAt_row target (p a) 8 code captured).mpr
      SchemaControls.actual_conditional_row_has_both_matches.1
  · intro equal
    have identities : (7 : Nat) = 8 := congrArg Prod.fst (Value.row.inj equal).1
    omega

theorem latent_equation_retained : code.row.obligations ≠ [] :=
  SchemaControls.latent_conditions_are_not_empty

def impossibleCode : RowCode base [] () :=
  { code with row := ⟨code.row.value,[(observe rawA,observe rawB)]⟩ }

def impossiblePacket : Terms base Nat [] () :=
  Value.row (7,impossibleCode) ⟨⟨_,captures⟩,target,captured⟩

theorem impossible_latent_equation_refused :
    ¬ rowMatches target (p a) (TaggedAssignments.identity base) impossiblePacket := by
  intro matched
  have realized := (matchesAt_row target (p a) 7 impossibleCode captured).mp
    ((rowMatches_identity target (p a) impossiblePacket).mp matched)
  obtain ⟨extension,images,solved,_⟩ := realized
  have observed := solved (observe rawA,observe rawB) (List.mem_singleton_self _)
  change observe (instantiate
    (ContextualGuardMatching.instanceAssignment impossibleCode.locals.arity images extension.assignment captured) rawA) =
    observe (instantiate
      (ContextualGuardMatching.instanceAssignment impossibleCode.locals.arity images extension.assignment captured) rawB) at observed
  have equation := observe_injective observed
  have sizes := congrArg termSize equation
  change 1 = 3 at sizes
  omega

theorem decoded_region_has_both_identities :
    regionOf packet {7,8} (region target (p a) (TaggedAssignments.identity base)) = ({7,8} : Finset Nat) := by
  ext occurrence
  constructor
  · intro member
    exact (mem_regionOf.mp member).1
  · intro member
    apply mem_regionOf.mpr
    refine ⟨member,?_⟩
    apply (region_true_iff target (p a) (TaggedAssignments.identity base) (packet occurrence)).mpr
    apply (rowMatches_identity target (p a) (packet occurrence)).mpr
    exact (matchesAt_row target (p a) occurrence code captured).mpr
      SchemaControls.actual_conditional_row_has_both_matches.1

theorem equality_region_has_one_identity (substitution : TaggedAssignments.Substitution base) :
    Check.matches (packetAction (S := base) (O := Nat) (Γ := []) (sort := ())) substitution
      packet {7,8} (packet 7) = {7} := by
  classical
  ext occurrence
  unfold Check.matches
  rw [Finset.mem_filter]
  change (occurrence ∈ ({7,8} : Finset Nat) ∧
    ContextPackets.apply base substitution (packet 7) = ContextPackets.apply base substitution (packet occurrence)) ↔
      occurrence ∈ ({7} : Finset Nat)
  constructor
  · rintro ⟨_,equal⟩
    exact Finset.mem_singleton.mpr (congrArg Prod.fst (Value.row.inj equal).1).symm
  · intro member
    have same := Finset.mem_singleton.mp member
    subst occurrence
    exact ⟨by decide,rfl⟩

theorem shared_matches_first : ContextualConditionalRows.Matches locals captures captured (p a) SchemaControls.sharedRow := by
  apply (ContextualConditionalRows.ofStored_matches_iff locals captures captured (p a) _).mpr
  apply (ContextualGuardMatching.shared_matches_iff locals captured (p a) _).mpr
  with_unfolding_all rfl

theorem shared_refuses_second :
    ¬ ContextualConditionalRows.Matches locals captures captured (p b) SchemaControls.sharedRow := by
  intro matched
  have same := (ContextualGuardMatching.shared_matches_iff locals captured (p b) _).mp
    ((ContextualConditionalRows.ofStored_matches_iff locals captures captured (p b) _).mp matched)
  have fixed : instantiate captured (p ContextualSelectionViews.Controls.sharedValue) = p a := by
    with_unfolding_all rfl
  rw [fixed] at same
  exact ContextualSelectionViews.Controls.distinct_ground_instances_are_unequal same.symm

universe uV

theorem equivalence_rectangle {V : Type uV} (E : V → V → Prop) (laws : Equivalence E)
    {firstPattern secondPattern firstRow secondRow : V}
    (firstFirst : E firstPattern firstRow) (firstSecond : E firstPattern secondRow)
    (secondFirst : E secondPattern firstRow) : E secondPattern secondRow :=
  laws.trans secondFirst (laws.trans (laws.symm firstFirst) firstSecond)

/-- No equivalence on one encoded value per pattern and per row expresses
these actual schema/shared-row observations at this one model. -/
theorem no_equivalence_pattern_membership {V : Type uV} (E : V → V → Prop) (laws : Equivalence E)
    (encodePattern : Term (signature base active) [] () → V)
    (encodeRow : ContextualConditionalRows.Row locals captures [] () → V)
    (faithful : ∀ pattern row, E (encodePattern pattern) (encodeRow row) ↔
      ContextualConditionalRows.Matches locals captures captured pattern row) : False := by
  have firstFirst := (faithful (p a) SchemaControls.schemaRow).mpr
    SchemaControls.actual_conditional_row_has_both_matches.1
  have firstSecond := (faithful (p a) SchemaControls.sharedRow).mpr shared_matches_first
  have secondFirst := (faithful (p b) SchemaControls.schemaRow).mpr
    SchemaControls.actual_conditional_row_has_both_matches.2
  exact shared_refuses_second ((faithful (p b) SchemaControls.sharedRow).mp
    (equivalence_rectangle E laws firstFirst firstSecond secondFirst))

end Schema

namespace Nonprincipal

open ContextualNonprincipalCountControls

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Nat)

def state : NativeState base Nat [] () := ⟨Empty,inferInstance,locals,before⟩

def firing : LiveFiring state where
  rule := rule
  selection := picked
  outputs := outputs
  patterns := []
  fuel := 0

theorem enabled : Enabled (fun _ : Nat => ()) state.state.present (firing.selection.commit (T := Unit)) :=
  ⟨admitted.taken_present,admitted.read_present,admitted.apart,admitted.fresh,
    fun _ member => by simp [Selection.commit] at member⟩

theorem actual_native_admitted : firing.toNative.Realized := by
  apply (native_admits_iff firing.toNative).mpr
  refine ⟨⟨admitted.take_distinct,admitted.output_distinct,admitted.take_length,
    admitted.read_length,admitted.outputs⟩,enabled,?_,?_⟩
  · obtain ⟨Future,future,candidate,solved⟩ := admitted.solvable
    exact ⟨⟨Future,future⟩,candidate,solved⟩
  · intro target candidate solved
    refine ⟨?_,?_⟩
    · intro check member
      exact admitted.checks check member target.Names target.arity candidate solved
    · intro query member
      cases member

noncomputable def counted (number : Nat) := countQuery (O := Nat) (NativePacketStep.useObject state 1) pattern number

theorem count_one_earned :
    (counted 1).Ask (packetAction (S := base) (O := Nat) (Γ := []) (sort := ()))
      ((NativePacketStep.selection firing).problem (NativePacketStep.label firing 0 1)
        (NativePacketStep.body firing 1) (NativePacketStep.configuration state 0))
      (NativePacketStep.label firing 0 1) (NativePacketStep.present state) :=
  (own_count_ask_iff firing (by decide : (0 : Nat) ≠ 1) enabled pattern 1).mpr count_guard

theorem no_fixed_packet_collect (seen : Finset Nat) :
    ¬ (exactQuery (NativePacketStep.useObject state 1) pattern (seen.image Sum.inl)).Ask
      (packetAction (S := base) (O := Nat) (Γ := []) (sort := ()))
      ((NativePacketStep.selection firing).problem (NativePacketStep.label firing 0 1)
        (NativePacketStep.body firing 1) (NativePacketStep.configuration state 0))
      (NativePacketStep.label firing 0 1) (NativePacketStep.present state) := by
  intro asked
  exact no_fixed_matching_table seen
    ((own_exact_ask_iff firing (by decide : (0 : Nat) ≠ 1) enabled pattern seen).mp asked)

noncomputable def constantFit :=
  NativePacketStep.fit state 0 1 ⟨Empty,locals⟩ (model locals (literal 0))

noncomputable def projectionFit :=
  NativePacketStep.fit state 0 1 ⟨Empty,locals⟩ (model locals (.var .zero))

theorem constant_fit_model :
    (packetAction (S := base) (O := Nat) (Γ := []) (sort := ())).Models constantFit
      ((NativePacketStep.selection firing).problem (NativePacketStep.label firing 0 1)
        (NativePacketStep.body firing 1) (NativePacketStep.configuration state 0)) :=
  NativePacketStep.model_fit firing (by decide : (0 : Nat) ≠ 1) enabled
    ⟨Empty,locals⟩ (model locals (literal 0)) (constant_model locals)

theorem projection_fit_model :
    (packetAction (S := base) (O := Nat) (Γ := []) (sort := ())).Models projectionFit
      ((NativePacketStep.selection firing).problem (NativePacketStep.label firing 0 1)
        (NativePacketStep.body firing 1) (NativePacketStep.configuration state 0)) :=
  NativePacketStep.model_fit firing (by decide : (0 : Nat) ≠ 1) enabled
    ⟨Empty,locals⟩ (model locals (.var .zero)) (projection_model locals)

theorem constant_region :
    regionOf (NativePacketStep.label firing 0 1) (NativePacketStep.present state)
      ((counted 1).region constantFit) = {Sum.inl 0} := by
  have actual := own_region firing 0 1 enabled pattern constantFit constant_fit_model
  dsimp only [constantFit] at actual
  rw [NativePacketStep.fit_use state 0 1 ⟨Empty,locals⟩ (model locals (literal 0))] at actual
  change _ = (ContextualConditionalGuards.region locals (model locals (literal 0))
    rows before.present pattern).image Sum.inl at actual
  rw [region_at_literal locals (model locals (literal 0)) 0 (.inl rfl) rfl] at actual
  exact actual

theorem projection_region :
    regionOf (NativePacketStep.label firing 0 1) (NativePacketStep.present state)
      ((counted 1).region projectionFit) = {Sum.inl 1} := by
  have actual := own_region firing 0 1 enabled pattern projectionFit projection_fit_model
  dsimp only [projectionFit] at actual
  rw [NativePacketStep.fit_use state 0 1 ⟨Empty,locals⟩ (model locals (.var .zero))] at actual
  change _ = (ContextualConditionalGuards.region locals (model locals (.var .zero))
    rows before.present pattern).image Sum.inl at actual
  rw [region_at_literal locals (model locals (.var .zero)) 1 (.inr rfl) rfl] at actual
  exact actual

theorem wrong_count_refused (number : Nat) (different : number ≠ 1) :
    ¬ (counted number).Ask (packetAction (S := base) (O := Nat) (Γ := []) (sort := ()))
      ((NativePacketStep.selection firing).problem (NativePacketStep.label firing 0 1)
        (NativePacketStep.body firing 1) (NativePacketStep.configuration state 0))
      (NativePacketStep.label firing 0 1) (NativePacketStep.present state) := by
  intro asked
  have tested := asked constantFit constant_fit_model
  change (regionOf _ _ ((counted 1).region constantFit)).card = number at tested
  rw [constant_region] at tested
  exact different tested.symm

def sourcePattern : Term (signature base (ContextualActivatedStep.source locals functions)) [] () :=
  instantiate (ContextualSelectionViews.capturedSource locals functions) (call (literal 1) (literal 0))

def writer : LiveFiring state where
  rule := ⟨[literal 1],[],[(sourcePattern,literal 0)],[],[]⟩
  selection := ⟨[1],[],[]⟩
  outputs := outputs
  patterns := []
  fuel := 0

theorem writer_information : FamilyInformation.memberInformation writer = information ++
    [(observe (literal (Γ := []) 1),observe (literal (Γ := []) 1)),
      (observe pattern,observe (literal (Γ := []) 0))] := by
  with_unfolding_all rfl

theorem writer_models : ContextualResidual.Models (model locals (literal 0))
    (FamilyInformation.memberInformation writer) := by
  rw [writer_information]
  apply (ContextualResidual.models_append (model locals (literal 0)) information
    [(observe (literal (Γ := []) 1),observe (literal (Γ := []) 1)),
      (observe pattern,observe (literal (Γ := []) 0))]).mpr
  refine ⟨constant_model locals,?_⟩
  intro equation member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem writer_enabled : Enabled (fun _ : Nat => ()) state.state.present (writer.selection.commit (T := Unit)) := by
  decide +kernel

theorem writer_admitted : writer.toNative.Realized := by
  apply (native_admits_iff writer.toNative).mpr
  refine ⟨⟨by decide,by decide,rfl,rfl,rfl⟩,writer_enabled,
    ⟨⟨Empty,locals⟩,model locals (literal 0),writer_models⟩,?_⟩
  intro target candidate _
  refine ⟨?_,?_⟩
  · intro check member
    cases member
  · intro query member
    cases member

def actualJoint : NativeResidual.Joint state firing.toNative.information writer.toNative.information ⟨Empty,locals⟩ where
  left := model locals (literal 0)
  right := model locals (literal 0)
  left_models := constant_model locals
  right_models := writer_models
  agree := rfl

theorem writer_forces_zero {V : Type} {declaration : V → MetaArity base}
    (candidate : Assignment active declaration)
    (solved : ContextualResidual.Models candidate (FamilyInformation.memberInformation writer)) :
    instantiate candidate pattern = literal 0 := by
  have equation := solved (observe pattern,observe (literal (Γ := []) 0)) (by
    rw [writer_information]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  exact observe_injective equation

theorem joint_pattern_zero {target : Frames.Frame base}
    (joint : NativeResidual.Joint state firing.toNative.information writer.toNative.information target) :
    instantiate joint.left pattern = literal 0 := by
  calc
    instantiate joint.left pattern =
        instantiate (Assignment.compose joint.left (ContextualSelectionViews.capturedTarget locals functions))
          (call (literal 1) (literal 0)) :=
      (Assignment.instantiate_compose joint.left (ContextualSelectionViews.capturedTarget locals functions)
        (call (literal 1) (literal 0))).symm
    _ = instantiate (Assignment.compose joint.right (ContextualSelectionViews.capturedTarget locals functions))
        (call (literal 1) (literal 0)) :=
      congrArg (fun captured => instantiate captured (call (literal 1) (literal 0))) joint.agree
    _ = instantiate joint.right pattern :=
      Assignment.instantiate_compose joint.right (ContextualSelectionViews.capturedTarget locals functions)
        (call (literal 1) (literal 0))
    _ = literal 0 := writer_forces_zero joint.right joint.right_models

theorem literal_one_not_seen {V : Type} (declaration : V → MetaArity base)
    (candidate : Assignment active declaration) (zero : instantiate candidate pattern = literal 0) :
    ¬ ContextualConditionalRows.Matches locals active candidate (instantiate candidate pattern) (rows 1) := by
  intro matched
  have selected := (ContextualConditionalGuards.mem_region locals candidate rows before.present pattern 1).mpr
    ⟨by decide,matched⟩
  rw [region_at_literal declaration candidate 0 (.inl rfl) zero] at selected
  have impossible : (1 : Nat) = 0 := Finset.mem_singleton.mp selected
  omega

theorem reader_checks : firing.toNative.prepared.rule.checks = [.count pattern 1] := by
  with_unfolding_all rfl

theorem reader_clear_writer : Clear firing writer.selection writer.rule writer.outputs where
  takes := by decide
  ports := by decide
  keeps := by decide
  consistent := ⟨⟨Empty,locals⟩,⟨actualJoint⟩⟩
  blindTakes target joint occurrence member := by
    have same : occurrence = 1 := List.mem_singleton.mp member
    subst occurrence
    refine ⟨?_,fun _ impossible => by cases impossible⟩
    intro check member
    rw [reader_checks] at member
    have same := List.mem_singleton.mp member
    subst check
    exact literal_one_not_seen target.arity joint.left (joint_pattern_zero joint)
  blindOutputs _ _ _ impossible := by cases impossible

theorem writer_clear_reader : Clear writer firing.selection firing.rule firing.outputs where
  takes := by decide
  ports := by decide
  keeps := by decide
  consistent := ⟨⟨Empty,locals⟩,⟨actualJoint.swap⟩⟩
  blindTakes _ _ _ impossible := by cases impossible
  blindOutputs _ _ _ _ := by
    refine ⟨?_,?_⟩
    · intro check impossible
      cases impossible
    · intro query impossible
      cases impossible

theorem actual_clear_family : NativeIterated.FamilyClear state [firing,writer] where
  admitted member present := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl
    · exact actual_native_admitted
    · exact writer_admitted
  pairwise := by
    refine List.pairwise_cons.mpr ⟨?_,List.pairwise_singleton _ _⟩
    intro member present
    have same := List.mem_singleton.mp present
    subst member
    exact ⟨reader_clear_writer,writer_clear_reader⟩
  jointly := by
    refine ⟨⟨Empty,locals⟩,Assignment.compose (model locals (literal 0))
      (ContextualSelectionViews.capturedTarget locals functions),?_⟩
    intro member present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl
    · exact ⟨actualJoint.left,actualJoint.left_models,rfl⟩
    · exact ⟨actualJoint.right,actualJoint.right_models,rfl⟩

theorem actual_every_order {order : List (LiveFiring state)} (permutation : order.Perm [firing,writer]) :
    ∃ last, NativeIterated.Sequential state order last :=
  NativeIterated.every_order_admitted actual_clear_family permutation

theorem support_contains_one : 1 ∈ table.seen := by
  have matching : 1 ∈ table.matching predicate ⟨Empty,locals,model locals (.var .zero)⟩ := by
    rw [table_matching locals (model locals (.var .zero)) (projection_model locals),
      region_at_literal locals (model locals (.var .zero)) 1 (.inr rfl) rfl]
    exact Finset.mem_singleton_self _
  exact ((table.mem_matching predicate _ 1).mp matching).choose

theorem table_validation_sees_one :
    (table.query predicate).region ⟨Empty,locals,model locals (literal 0)⟩ (1,rows 1) = true := by
  change (if member : 1 ∈ table.seen then
    predicate ⟨Empty,locals,model locals (literal 0)⟩ 1 (rows 1) ==
      predicate ⟨Empty,locals,model locals (literal 0)⟩ 1 (table.payload 1 member)
    else predicate ⟨Empty,locals,model locals (literal 0)⟩ 1 (rows 1)) = true
  rw [dif_pos support_contains_one]
  change (predicate ⟨Empty,locals,model locals (literal 0)⟩ 1 (rows 1) ==
    predicate ⟨Empty,locals,model locals (literal 0)⟩ 1 (rows 1)) = true
  exact beq_self_eq_true _

theorem table_pair_write_ignorance_fails :
    ¬ (∀ (target : Frames.Frame base)
      (joint : NativeResidual.Joint state firing.toNative.information writer.toNative.information target),
      ∀ occurrence ∈ writer.selection.taken ++ writer.selection.made,
        (table.query predicate).region ⟨target.Names,target.arity,joint.left⟩ (occurrence,rows occurrence) = false) := by
  intro ignored
  have wrong := ignored ⟨Empty,locals⟩ actualJoint 1 (by decide)
  change (table.query predicate).region ⟨Empty,locals,model locals (literal 0)⟩ (1,rows 1) = false at wrong
  rw [table_validation_sees_one] at wrong
  cases wrong

theorem writer_equation_observation_earned :
    (packetAction (S := base) (O := Nat) (Γ := []) (sort := ())).Entails
      ((NativePacketStep.selection writer).problem (NativePacketStep.label writer 0 1)
        (NativePacketStep.body writer 1) (NativePacketStep.configuration state 0))
      (fun substitution => (equationCheck (NativePacketStep.useObject state 1) pattern (literal 0)).Holds
        (packetAction (S := base) (O := Nat) (Γ := []) (sort := ())) substitution
        (NativePacketStep.label writer 0 1) (NativePacketStep.present state)) := by
  apply (own_equation_ask_iff writer (by decide : (0 : Nat) ≠ 1) writer_enabled pattern (literal 0)).mpr
  intro Future future candidate solved
  exact writer_forces_zero candidate solved

end Nonprincipal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketQueryControls
