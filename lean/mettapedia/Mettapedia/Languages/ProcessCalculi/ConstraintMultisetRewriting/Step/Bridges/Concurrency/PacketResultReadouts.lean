import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.PacketResultModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketGuardedRounds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativeWitnessCuts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativeProducedModels

/-!
# Physical closed readings of the actual annotated packet result

The packet result is the existing annotated `follow`, with the family's actual common label map.
Its knowledge is the actual full joint information. The observer decodes the stored conditional row
at a physically present port under a real model of that final information.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.PacketResultReadouts

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open TaggedAssignments (Substitution)
open ContextPackets (Value Environment)
open NativePacketStep (Terms Ports packetAction)
open NativeClosedReadings
open MeTTaCalculus.OccurrenceCommits (fire fireList)

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}

noncomputable def packetFinal {initial : NativeState S O Γ sort} (members : List (LiveFiring initial)) :=
  AnnotatedRuns.follow (NativePacketRounds.label members) (NativePacketStep.configuration initial 0)
    (NativePacketGuardedRounds.image members)

theorem packetFinal_equations {initial : NativeState S O Γ sort} (members : List (LiveFiring initial)) :
    (packetFinal members).equations = NativePacketRounds.jointProblem members :=
  (AnnotatedRuns.follow_equations (NativePacketRounds.label members)
    (NativePacketStep.configuration initial 0) (NativePacketGuardedRounds.image members)).trans
      (NativePacketGuardedRounds.joint_problem members)

def PacketReads {initial : NativeState S O Γ sort} (members : List (LiveFiring initial))
    (occurrence : O) (pattern : ClosedTerm S Γ sort) : Prop :=
  Sum.inl occurrence ∈ (packetFinal members).present ∧
    ∃ substitution : Substitution S,
      (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
        (packetFinal members).equations ∧
      NativePacketQueryView.rowMatches (NativePacketStep.baseObject initial 0)
        (closedAt initial.state.declarations pattern) substitution
        (NativePacketRounds.label members (.inl occurrence))

def physicalWorld (world : Finset O) : Finset (Ports O) :=
  insert (.inr ()) (world.image Sum.inl)

theorem physical_step {initial : NativeState S O Γ sort} (firing : LiveFiring initial) (world : Finset O) :
    fire (physicalWorld world) ((NativePacketStep.selection firing).commit (T := Terms S O Γ sort)) =
      physicalWorld (fire world (firing.selection.commit (T := Unit))) := by
  ext port
  cases port with
  | inl occurrence => simp [physicalWorld, fire, NativePacketStep.selection, Selection.commit, Finset.mem_image]
  | inr token => cases token; simp [physicalWorld, fire, NativePacketStep.selection, Selection.commit, Finset.mem_image]

theorem physical_indices {initial : NativeState S O Γ sort} (members : List (LiveFiring initial))
    (indices : List (Fin members.length)) (world : Finset O) :
    fireList (physicalWorld world)
        (indices.map fun index => (NativePacketGuardedRounds.firing members index).selection.commit (T := Terms S O Γ sort)) =
      physicalWorld (fireList world (indices.map fun index => members[index].selection.commit (T := Unit))) := by
  induction indices generalizing world with
  | nil => rfl
  | cons first rest ih =>
      change fireList
        (fire (physicalWorld world) ((NativePacketStep.selection members[first]).commit (T := Terms S O Γ sort)))
        (rest.map fun index => (NativePacketGuardedRounds.firing members index).selection.commit (T := Terms S O Γ sort)) = _
      rw [physical_step]
      exact ih _

theorem physical_image {initial : NativeState S O Γ sort} (members : List (LiveFiring initial)) :
    fireList (NativePacketStep.present initial)
        (AnnotatedRuns.footprints (NativePacketGuardedRounds.image members)) =
      physicalWorld (fireList initial.state.present (members.map fun firing => firing.selection.commit (T := Unit))) := by
  have enumerates : (List.finRange members.length).map (fun index => members[index]) = members := by
    rw [← List.ofFn_eq_map]
    exact List.ofFn_getElem
  change fireList (physicalWorld initial.state.present)
    (((List.finRange members.length).map (NativePacketGuardedRounds.firing members)).map
      fun firing => firing.selection.commit (T := Terms S O Γ sort)) = _
  rw [List.map_map]
  change fireList (physicalWorld initial.state.present)
    ((List.finRange members.length).map
      fun index => (NativePacketGuardedRounds.firing members index).selection.commit (T := Terms S O Γ sort)) = _
  rw [physical_indices]
  have commits : (List.finRange members.length).map (fun index => members[index].selection.commit (T := Unit)) =
      members.map (fun firing => firing.selection.commit (T := Unit)) := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map fun firing : LiveFiring initial => firing.selection.commit (T := Unit)) enumerates
  exact congrArg physicalWorld (congrArg (fireList initial.state.present) commits)

theorem packetFinal_present {initial last : NativeState S O Γ sort} {members : List (LiveFiring initial)}
    [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (witness : NativeRoundExecution.Witness initial members last) :
    (packetFinal members).present = physicalWorld last.state.present := by
  change (AnnotatedRuns.follow (NativePacketRounds.label members) (NativePacketStep.configuration initial 0)
    (NativePacketGuardedRounds.image members)).present = _
  rw [AnnotatedRuns.follow_present]
  change fireList (NativePacketStep.present initial)
    (AnnotatedRuns.footprints (NativePacketGuardedRounds.image members)) = _
  exact (physical_image members).trans
    (congrArg physicalWorld (NativeConcurrent.sequential_present witness.sequential).symm)

theorem packetFinal_present_inl {initial last : NativeState S O Γ sort} {members : List (LiveFiring initial)}
    [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (witness : NativeRoundExecution.Witness initial members last) (occurrence : O) :
    Sum.inl occurrence ∈ (packetFinal members).present ↔ occurrence ∈ last.state.present := by
  rw [packetFinal_present witness]
  simp [physicalWorld]

omit [DecidableEq O] in
theorem base_old_iff (initial : NativeState S O Γ sort) (substitution : Substitution S)
    (pattern : ClosedTerm S Γ sort) (occurrence : O) :
    NativePacketQueryView.rowMatches (NativePacketStep.baseObject initial 0)
        (closedAt initial.state.declarations pattern) substitution (NativePacketStep.oldRow initial 0 occurrence) ↔
      ContextualConditionalRows.Matches initial.locals initial.state.declarations
        (substitution (NativePacketStep.baseObject initial 0)).2
        (closedAt (substitution (NativePacketStep.baseObject initial 0)).1.2.arity pattern)
        (initial.state.rows occurrence) := by
  unfold NativePacketQueryView.rowMatches
  change NativePacketQueryView.MatchesAt (substitution (NativePacketStep.baseObject initial 0)).1
    (instantiate (substitution (NativePacketStep.baseObject initial 0)).2
      (closedAt initial.state.declarations pattern))
    (Value.row (occurrence,NativePacketStep.oldCode initial occurrence)
      ⟨⟨initial.state.Names,initial.state.declarations⟩,
        (substitution (NativePacketStep.baseObject initial 0)).1,
        Assignment.compose (substitution (NativePacketStep.baseObject initial 0)).2
          (generator initial.state.declarations)⟩) ↔ _
  rw [Assignment.compose_identity_right]
  refine (NativePacketQueryView.matchesAt_row
    (substitution (NativePacketStep.baseObject initial 0)).1
    (instantiate (substitution (NativePacketStep.baseObject initial 0)).2
      (closedAt initial.state.declarations pattern)) occurrence (NativePacketStep.oldCode initial occurrence)
    (substitution (NativePacketStep.baseObject initial 0)).2).trans ?_
  exact Iff.of_eq (congrArg
    (fun term : Term (signature S (substitution (NativePacketStep.baseObject initial 0)).1.2.arity) Γ sort =>
      ContextualConditionalRows.Matches initial.locals initial.state.declarations
        (substitution (NativePacketStep.baseObject initial 0)).2 term (initial.state.rows occurrence))
    (closedAt_natural (source := initial.state.declarations)
      (target := (substitution (NativePacketStep.baseObject initial 0)).1.2.arity)
      (substitution (NativePacketStep.baseObject initial 0)).2 pattern))

omit [DecidableEq O] in
theorem fitData_base_old_iff {initial : NativeState S O Γ sort} {members : List (LiveFiring initial)}
    {target : Frames.Frame S} (data : FamilyInformation.SolutionData initial members target)
    (pattern : ClosedTerm S Γ sort) (occurrence : O) :
    NativePacketQueryView.rowMatches (NativePacketStep.baseObject initial 0)
        (closedAt initial.state.declarations pattern) (NativePacketRounds.fitData data)
        (NativePacketStep.oldRow initial 0 occurrence) ↔
      ContextualConditionalRows.Matches initial.locals initial.state.declarations data.shared
        (closedAt target.arity pattern) (initial.state.rows occurrence) := by
  have actual := base_old_iff initial (NativePacketRounds.fitData data) pattern occurrence
  rw [NativePacketRounds.fitData_base] at actual
  exact actual

theorem base_output_iff {initial : NativeState S O Γ sort} (members : List (LiveFiring initial))
    (writer : Fin members.length) (substitution : Substitution S)
    (model : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
      (NativePacketRounds.jointProblem members)) (pattern : ClosedTerm S Γ sort) (occurrence : O) :
    NativePacketQueryView.rowMatches (NativePacketStep.baseObject initial 0)
        (closedAt initial.state.declarations pattern) substitution
        (NativePacketStep.outputRow members[writer] (NativePacketRounds.useTag writer) occurrence) ↔
      closedAt (substitution (NativePacketStep.baseObject initial 0)).1.2.arity pattern =
        instantiate ((NativePacketRounds.readData members substitution model).member writer)
          (members[writer].outputs occurrence) := by
  have actual := NativePacketQueryView.rowMatches_output_iff members[writer]
    (NativePacketStep.baseObject initial 0) (closedAt initial.state.declarations pattern)
    (NativePacketRounds.useTag writer) substitution (substitution (NativePacketStep.baseObject initial 0)).1
    (substitution (NativePacketStep.baseObject initial 0)).2
    ((NativePacketRounds.readData members substitution model).member writer)
    rfl (NativePacketQueryView.readData_use members writer substitution model) occurrence
  exact actual.trans (Iff.of_eq (congrArg
    (fun term : Term (signature S (substitution (NativePacketStep.baseObject initial 0)).1.2.arity) Γ sort =>
      term = instantiate ((NativePacketRounds.readData members substitution model).member writer)
        (members[writer].outputs occurrence))
    (closedAt_natural (source := initial.state.declarations)
      (target := (substitution (NativePacketStep.baseObject initial 0)).1.2.arity)
      (substitution (NativePacketStep.baseObject initial 0)).2 pattern)))

omit [DecidableEq O] in
theorem fitData_base_output_iff {initial : NativeState S O Γ sort} {members : List (LiveFiring initial)}
    {target : Frames.Frame S} (data : FamilyInformation.SolutionData initial members target)
    (writer : Fin members.length) (pattern : ClosedTerm S Γ sort) (occurrence : O) :
    NativePacketQueryView.rowMatches (NativePacketStep.baseObject initial 0)
        (closedAt initial.state.declarations pattern) (NativePacketRounds.fitData data)
        (NativePacketStep.outputRow members[writer] (NativePacketRounds.useTag writer) occurrence) ↔
      closedAt target.arity pattern = instantiate (data.member writer) (members[writer].outputs occurrence) := by
  have actual := NativePacketQueryView.rowMatches_output_iff members[writer]
    (NativePacketStep.baseObject initial 0) (closedAt initial.state.declarations pattern)
    (NativePacketRounds.useTag writer) (NativePacketRounds.fitData data) (0,target) data.shared
    (data.member writer) (NativePacketRounds.fitData_base data)
    (NativePacketRounds.fitData_use data writer) occurrence
  exact actual.trans (Iff.of_eq (congrArg
    (fun term : Term (signature S target.arity) Γ sort =>
      term = instantiate (data.member writer) (members[writer].outputs occurrence))
    (closedAt_natural (source := initial.state.declarations) (target := target.arity) data.shared pattern)))

section NativeReadings

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

theorem clear_after_prefix {initial last : NativeState S O Γ sort} {front : List (LiveFiring initial)}
    (witness : NativeRoundExecution.Witness initial front last) {remaining : List (LiveFiring initial)}
    (clear : NativeIterated.FamilyClear initial (front ++ remaining)) :
    NativeIterated.FamilyClear last (ResidualPrefixModels.residuals witness remaining) := by
  induction witness with
  | nil => exact clear
  | cons first rest accepted tail ih =>
      apply ih
      have mapped : (rest ++ remaining).map (NativeIterated.residualAfter accepted) =
          rest.map (NativeIterated.residualAfter accepted) ++ remaining.map (NativeIterated.residualAfter accepted) :=
        List.map_append ..
      exact (congrArg
        (fun family : List (LiveFiring (native.result first.toNative accepted)) =>
          NativeIterated.FamilyClear (native.result first.toNative accepted) family) mapped).mp
        (NativeIterated.familyClear_residual clear accepted)

theorem residual_selection_at {initial last : NativeState S O Γ sort} {front : List (LiveFiring initial)}
    (witness : NativeRoundExecution.Witness initial front last) (remaining : List (LiveFiring initial))
    (index : Fin (ResidualPrefixModels.residuals witness remaining).length) :
    (ResidualPrefixModels.residuals witness remaining)[index].selection =
      remaining[(⟨index.val,by simpa only [ResidualPrefixModels.residuals_length] using index.isLt⟩ : Fin remaining.length)].selection := by
  have rightBound : index.val < remaining.length := by
    simpa only [ResidualPrefixModels.residuals_length] using index.isLt
  have point := congrArg (fun values : List (Selection O) => values[index.val]?)
    (NativeWitnessCuts.residuals_selections witness remaining)
  rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using index.isLt),
    List.getElem?_eq_getElem (by simpa only [List.length_map] using rightBound)] at point
  simp only [List.getElem_map] at point
  change (ResidualPrefixModels.residuals witness remaining)[index.val].selection = remaining[index.val].selection
  exact Option.some.inj point

theorem present_cases {initial last : NativeState S O Γ sort} {members : List (LiveFiring initial)}
    (witness : NativeRoundExecution.Witness initial members last) :
    ∀ occurrence ∈ last.state.present, occurrence ∈ initial.state.present ∨
      ∃ index : Fin members.length, occurrence ∈ members[index].selection.made := by
  induction witness with
  | nil => exact fun _ present => Or.inl present
  | @cons initial first rest accepted last tail ih =>
      intro occurrence present
      rcases ih occurrence present with old | ⟨index,made⟩
      · have old' := old
        have actualPresent : (native.result first.toNative accepted).state.present =
            fire initial.state.present (first.selection.commit (T := Unit)) := native.present_result first.toNative accepted
        rw [actualPresent] at old'
        rcases (MeTTaCalculus.OccurrenceCommits.mem_fire.mp old') with kept | made
        · exact Or.inl kept.1
        · exact Or.inr ⟨⟨0,by simp⟩,List.mem_toFinset.mp made⟩
      · let original : Fin rest.length := ⟨index.val,by simpa only [List.length_map] using index.isLt⟩
        refine Or.inr ⟨original.succ,?_⟩
        change occurrence ∈ (rest.map (NativeIterated.residualAfter accepted))[index.val].selection.made at made
        rw [List.getElem_map] at made
        exact made

/-- A supplied original model and a retained conditional-row reading lift through the actual
finite witness. The target extension and returned model are the existing faithful prefix lift. -/
theorem retained_read_of_data {initial last : NativeState S O Γ sort} {members : List (LiveFiring initial)}
    (witness : NativeRoundExecution.Witness initial members last) {target : Frames.Frame S}
    (data : FamilyInformation.SolutionData initial members target)
    (known : ContextualResidual.Models data.shared initial.state.equations)
    (unmade : NativeIterated.Unmade members) (occurrence : O)
    (present : occurrence ∈ last.state.present)
    (notMade : ∀ firing ∈ members, occurrence ∉ firing.selection.made)
    (pattern : ClosedTerm S Γ sort)
    (matched : ContextualConditionalRows.Matches initial.locals initial.state.declarations data.shared
      (closedAt target.arity pattern) (initial.state.rows occurrence)) :
    Reads last occurrence pattern := by
  let expanded := ResidualPrefixModels.castData (List.append_nil members).symm data
  have sameShared : expanded.shared = data.shared :=
    ResidualPrefixModels.castData_shared (List.append_nil members).symm data
  have expandedKnown : ContextualResidual.Models expanded.shared initial.state.equations :=
    (congrArg (fun assignment => ContextualResidual.Models assignment initial.state.equations) sameShared).mpr known
  let lifted := ResidualPrefixModels.lift witness (remaining := []) expanded expandedKnown
    (by simpa only [List.append_nil] using unmade)
  let next : Frames.Frame S := ⟨lifted.extension.Names,lifted.extension.declarations⟩
  have captures : Assignment.compose lifted.data.shared (ResidualPrefixModels.changes witness) =
      Assignment.compose lifted.extension.assignment data.shared :=
    lifted.captures.trans (congrArg (Assignment.compose lifted.extension.assignment) sameShared)
  have after := PacketResultModels.matches_post initial.locals initial.state.declarations
    lifted.extension.assignment data.shared (closedAt target.arity pattern) (initial.state.rows occurrence) matched
  have afterTyped : ContextualConditionalRows.Matches initial.locals initial.state.declarations
      (Assignment.compose lifted.extension.assignment data.shared) (closedAt next.arity pattern)
      (initial.state.rows occurrence) :=
    (congrArg (fun term : Term (signature S next.arity) Γ sort =>
      ContextualConditionalRows.Matches initial.locals initial.state.declarations
        (Assignment.compose lifted.extension.assignment data.shared) term (initial.state.rows occurrence))
      (closedAt_natural lifted.extension.assignment pattern)).mp after
  refine ⟨present,next,lifted.data.shared,lifted.known,?_⟩
  apply (PacketResultModels.witness_matches_retained witness lifted.data.shared occurrence notMade
    (closedAt next.arity pattern)).mpr
  exact (congrArg (fun assignment => ContextualConditionalRows.Matches initial.locals initial.state.declarations
    assignment (closedAt next.arity pattern) (initial.state.rows occurrence)) captures).mpr afterTyped

theorem first_output_read_of_data {initial last : NativeState S O Γ sort}
    (first : LiveFiring initial) (rest : List (LiveFiring initial)) (accepted : first.toNative.Realized)
    (tail : NativeRoundExecution.Witness (native.result first.toNative accepted)
      (rest.map (NativeIterated.residualAfter accepted)) last)
    {target : Frames.Frame S} (data : FamilyInformation.SolutionData initial (first :: rest) target)
    (clear : NativeIterated.FamilyClear initial (first :: rest)) (occurrence : O)
    (made : occurrence ∈ first.selection.made) (present : occurrence ∈ last.state.present)
    (pattern : ClosedTerm S Γ sort)
    (output : closedAt target.arity pattern = instantiate (data.member 0) (first.outputs occurrence)) :
    Reads last occurrence pattern := by
  let execution := LiveFiring.execution accepted
  let right := data.member 0
  let remaining := ResidualPrefixModels.tailData data
  have rightModel : ContextualResidual.Models right
      (NativeResidual.problemOf initial execution.selection execution.rule) := by
    rw [NativeIterated.problemOf_execution accepted]
    exact data.models 0
  have rightAgrees : Assignment.compose right
      (ContextualSelectionViews.capturedTarget initial.locals initial.state.declarations) = remaining.shared := data.agrees 0
  have untouched : ∀ firing ∈ rest, ∀ port ∈ firing.selection.taken ++ firing.selection.read,
      port ∉ execution.selection.made := by
    intro firing member port selected
    rw [(LiveFiring.execution_data accepted).2.1]
    exact (ResidualPrefixModels.unmade_of_clear clear) firing (List.mem_cons_of_mem first member)
      first List.mem_cons_self port selected
  let post := ResidualModels.residualData execution remaining right rightModel rightAgrees untouched
  have known : ContextualResidual.Models post.shared (native.result first.toNative accepted).state.equations :=
    ResidualPrefixModels.publishedModel_known execution right rightModel
  have madeHere : occurrence ∈ execution.selection.made := by
    rwa [(LiveFiring.execution_data accepted).2.1]
  have liveHere : execution.reusable occurrence = false := by
    rw [(LiveFiring.execution_data accepted).2.2.2]
  have produced : closedAt (ResidualModels.extended execution target).arity pattern =
      instantiate (Assignment.compose post.shared (ContextualComputedFreshFrame.includeSource execution.update))
        (execution.outputs occurrence) := by
    calc
      closedAt (ResidualModels.extended execution target).arity pattern
          = instantiate (ResidualModels.inclusion execution target) (closedAt target.arity pattern) :=
            (closedAt_natural (ResidualModels.inclusion execution target) pattern).symm
      _ = instantiate (ResidualModels.inclusion execution target) (instantiate right (first.outputs occurrence)) :=
        congrArg (instantiate (ResidualModels.inclusion execution target)) output
      _ = instantiate (Assignment.compose (ResidualModels.inclusion execution target) right) (first.outputs occurrence) :=
        (Assignment.instantiate_compose _ _ _).symm
      _ = instantiate (Assignment.compose post.shared (ContextualComputedFreshFrame.includeSource execution.update))
          (first.outputs occurrence) := congrArg (fun assignment => instantiate assignment (first.outputs occurrence))
            (ResidualPrefixModels.publishedModel_right execution right).symm
      _ = instantiate (Assignment.compose post.shared (ContextualComputedFreshFrame.includeSource execution.update))
          (execution.outputs occurrence) := congrArg (instantiate
            (Assignment.compose post.shared (ContextualComputedFreshFrame.includeSource execution.update)))
            (congrFun (LiveFiring.execution_data accepted).2.2.1 occurrence).symm
  have matched := (PacketResultModels.state_matches_made execution post.shared madeHere liveHere
    (closedAt (ResidualModels.extended execution target).arity pattern)).mpr produced
  have tailNotMade : ∀ firing ∈ rest.map (NativeIterated.residualAfter accepted), occurrence ∉ firing.selection.made := by
    intro firing member also
    obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
    have apart := ((List.pairwise_cons.mp clear.pairwise).1 original inside).1.ports
    exact Finset.disjoint_left.mp apart (List.mem_toFinset.mpr made) (List.mem_toFinset.mpr also)
  exact retained_read_of_data tail post known
    (ResidualPrefixModels.unmade_of_clear (NativeIterated.familyClear_residual clear accepted))
    occurrence present tailNotMade pattern matched

theorem produced_read_of_data {initial last : NativeState S O Γ sort} {members : List (LiveFiring initial)}
    (witness : NativeRoundExecution.Witness initial members last) {target : Frames.Frame S}
    (data : FamilyInformation.SolutionData initial members target)
    (clear : NativeIterated.FamilyClear initial members) :
    ∀ (occurrence : O), occurrence ∈ last.state.present → ∀ (pattern : ClosedTerm S Γ sort)
      (index : Fin members.length), occurrence ∈ members[index].selection.made →
        closedAt target.arity pattern = instantiate (data.member index) (members[index].outputs occurrence) →
          Reads last occurrence pattern := by
  induction witness generalizing target with
  | nil =>
      intro occurrence present pattern index
      exact index.elim0
  | @cons initial first rest accepted last tail ih =>
      intro occurrence present pattern index
      refine Fin.cases ?_ (fun position => ?_) index
      · intro made output
        exact first_output_read_of_data first rest accepted tail data clear occurrence made present pattern output
      · intro made output
        let execution := LiveFiring.execution accepted
        let right := data.member 0
        let remaining := ResidualPrefixModels.tailData data
        have rightModel : ContextualResidual.Models right
            (NativeResidual.problemOf initial execution.selection execution.rule) := by
          rw [NativeIterated.problemOf_execution accepted]
          exact data.models 0
        have rightAgrees : Assignment.compose right
            (ContextualSelectionViews.capturedTarget initial.locals initial.state.declarations) = remaining.shared := data.agrees 0
        have untouched : ∀ firing ∈ rest, ∀ port ∈ firing.selection.taken ++ firing.selection.read,
            port ∉ execution.selection.made := by
          intro firing member port selected
          rw [(LiveFiring.execution_data accepted).2.1]
          exact (ResidualPrefixModels.unmade_of_clear clear) firing (List.mem_cons_of_mem first member)
            first List.mem_cons_self port selected
        let post := ResidualModels.residualData execution remaining right rightModel rightAgrees untouched
        let nextIndex := PacketResultModels.residualIndex accepted rest position
        have nextMade : occurrence ∈ (rest.map (NativeIterated.residualAfter accepted))[nextIndex].selection.made := by
          change occurrence ∈ (rest.map (NativeIterated.residualAfter accepted))[nextIndex.val].selection.made
          rw [List.getElem_map]
          exact made
        have reads := ResidualModels.read_left execution
          (ResidualModels.familyJoint execution remaining right rightModel rightAgrees position)
          (rest[position].outputs occurrence)
        have transported : instantiate (post.member nextIndex)
            ((rest.map (NativeIterated.residualAfter accepted))[nextIndex].outputs occurrence) =
            instantiate (ResidualModels.inclusion execution target)
              (instantiate (data.member position.succ) (rest[position].outputs occurrence)) := by
          have sameMember : post.member nextIndex = ResidualModels.amalgam execution
              (ResidualModels.familyJoint execution remaining right rightModel rightAgrees position) := by
            change ResidualModels.amalgam execution
              (ResidualModels.familyJoint execution remaining right rightModel rightAgrees
                (⟨nextIndex.val,by simpa only [List.length_map] using nextIndex.isLt⟩ : Fin rest.length)) = _
            exact congrArg (fun original : Fin rest.length => ResidualModels.amalgam execution
              (ResidualModels.familyJoint execution remaining right rightModel rightAgrees original)) (Fin.ext rfl)
          have sameOutput : (rest.map (NativeIterated.residualAfter accepted))[nextIndex].outputs occurrence =
              instantiate (NativeResidual.carry execution) (rest[position].outputs occurrence) := by
            change (rest.map (NativeIterated.residualAfter accepted))[nextIndex.val].outputs occurrence = _
            rw [List.getElem_map]
            rfl
          rw [sameMember,sameOutput]
          exact reads
        have nextOutput : closedAt (ResidualModels.extended execution target).arity pattern =
            instantiate (post.member nextIndex)
              ((rest.map (NativeIterated.residualAfter accepted))[nextIndex].outputs occurrence) :=
          (closedAt_natural (ResidualModels.inclusion execution target) pattern).symm.trans
            ((congrArg (instantiate (ResidualModels.inclusion execution target)) output).trans transported.symm)
        exact ih post (NativeIterated.familyClear_residual clear accepted)
          occurrence present pattern nextIndex nextMade nextOutput

theorem old_not_made {initial : NativeState S O Γ sort} {members : List (LiveFiring initial)}
    (clear : NativeIterated.FamilyClear initial members) {occurrence : O}
    (old : occurrence ∈ initial.state.present) :
    ∀ firing ∈ members, occurrence ∉ firing.selection.made := by
  intro firing member made
  have enabled := ((native_admits_iff firing.toNative).mp (clear.admitted firing member)).2.1
  exact Finset.disjoint_left.mp enabled.fresh (List.mem_toFinset.mpr made) old

theorem label_produced {initial : NativeState S O Γ sort} {members : List (LiveFiring initial)}
    (clear : NativeIterated.FamilyClear initial members) (index : Fin members.length)
    (occurrence : O) (made : occurrence ∈ members[index].selection.made) :
    NativePacketRounds.label members (.inl occurrence) =
      NativePacketStep.outputRow members[index] (NativePacketRounds.useTag index) occurrence := by
  have notOld : occurrence ∉ initial.state.present := by
    intro old
    exact old_not_made clear old members[index] (List.getElem_mem ..) made
  simp only [NativePacketRounds.label,if_neg notOld,NativePacketRounds.owner_of_clear clear index occurrence made]

/-- The actual final packet and returned native state already agree on every surviving original
conditional row. Produced rows are handled separately. -/
theorem retained_result_reads_iff {initial last : NativeState S O Γ sort}
    (members : List (LiveFiring initial)) (nonempty : members ≠ [])
    (clear : NativeIterated.FamilyClear initial members)
    (witness : NativeRoundExecution.Witness initial members last) (occurrence : O)
    (old : occurrence ∈ initial.state.present) (pattern : ClosedTerm S Γ sort) :
    PacketReads members occurrence pattern ↔ Reads last occurrence pattern := by
  have notMade := old_not_made clear old
  have unmade := ResidualPrefixModels.unmade_of_clear clear
  constructor
  · rintro ⟨present,substitution,model,seen⟩
    have fullModel : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
        (NativePacketRounds.jointProblem members) := by rwa [packetFinal_equations] at model
    let data := NativePacketRounds.readData members substitution fullModel
    have known := NativePacketRounds.data_models_knowledge data nonempty
    rw [NativePacketRounds.label_old members occurrence old] at seen
    have matched := (base_old_iff initial substitution pattern occurrence).mp seen
    exact retained_read_of_data witness data known unmade occurrence
      ((packetFinal_present_inl witness occurrence).mp present) notMade pattern matched
  · rintro ⟨present,target,candidate,known,matched⟩
    let recovered := PacketResultModels.recoverFinal witness candidate known unmade
    let data := ResidualPrefixModels.castData (List.append_nil members) recovered.data
    have shared : data.shared = Assignment.compose candidate (ResidualPrefixModels.changes witness) :=
      (ResidualPrefixModels.castData_shared (List.append_nil members) recovered.data).trans
        (recovered.captures.trans (congrArg
          (fun assignment => Assignment.compose assignment (ResidualPrefixModels.changes witness))
          (PacketResultModels.finalPost_shared witness candidate)))
    have before := (PacketResultModels.witness_matches_retained witness candidate occurrence notMade
      (closedAt target.arity pattern)).mp matched
    have sourceMatch : ContextualConditionalRows.Matches initial.locals initial.state.declarations data.shared
        (closedAt target.arity pattern) (initial.state.rows occurrence) :=
      (congrArg (fun assignment => ContextualConditionalRows.Matches initial.locals initial.state.declarations
        assignment (closedAt target.arity pattern) (initial.state.rows occurrence)) shared).mpr before
    have enabled (index : Fin members.length) :=
      ((native_admits_iff members[index].toNative).mp (clear.admitted members[index] (List.getElem_mem ..))).2.1
    refine ⟨(packetFinal_present_inl witness occurrence).mpr present,NativePacketRounds.fitData data,?_,?_⟩
    · rw [packetFinal_equations]
      exact NativePacketRounds.fitData_joint data nonempty enabled
    · rw [NativePacketRounds.label_old members occurrence old]
      exact (fitData_base_old_iff data pattern occurrence).mpr sourceMatch

/-- Every physically present packet reading is a reading of the supplied returned native state.
The producer is recovered from the actual history; the old-row branch retains conditional matching.
-/
theorem packet_reads_native {initial last : NativeState S O Γ sort}
    (members : List (LiveFiring initial)) (nonempty : members ≠ [])
    (clear : NativeIterated.FamilyClear initial members)
    (witness : NativeRoundExecution.Witness initial members last) (occurrence : O)
    (pattern : ClosedTerm S Γ sort) :
    PacketReads members occurrence pattern → Reads last occurrence pattern := by
  intro packet
  have present := (packetFinal_present_inl witness occurrence).mp packet.1
  rcases present_cases witness occurrence present with old | ⟨index,made⟩
  · exact (retained_result_reads_iff members nonempty clear witness occurrence old pattern).mp packet
  · rcases packet with ⟨_,substitution,model,seen⟩
    have fullModel : (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Models substitution
        (NativePacketRounds.jointProblem members) := by rwa [packetFinal_equations] at model
    let data := NativePacketRounds.readData members substitution fullModel
    rw [label_produced clear index occurrence made] at seen
    have output := (base_output_iff members index substitution fullModel pattern occurrence).mp seen
    exact produced_read_of_data witness data clear occurrence present pattern index made output

/-- Exact closed readings of the actual annotated result and the supplied native execution agree.
Both sides require physical presence, a model of their actual final knowledge, and the real stored
row semantics. No equality of history counts or arbitrary native execution reflection is asserted.
-/
theorem packet_result_reads_iff {initial last : NativeState S O Γ sort}
    (members : List (LiveFiring initial)) (nonempty : members ≠ [])
    (clear : NativeIterated.FamilyClear initial members)
    (witness : NativeRoundExecution.Witness initial members last) (occurrence : O)
    (pattern : ClosedTerm S Γ sort) :
    PacketReads members occurrence pattern ↔ Reads last occurrence pattern := by
  constructor
  · exact packet_reads_native members nonempty clear witness occurrence pattern
  · intro returned
    rcases present_cases witness occurrence returned.1 with old | ⟨index,made⟩
    · exact (retained_result_reads_iff members nonempty clear witness occurrence old pattern).mpr returned
    · rcases returned with ⟨present,target,candidate,known,matched⟩
      obtain ⟨data,_,_,output⟩ := NativeProducedModels.produced_model witness clear candidate known
        (closedAt target.arity pattern) occurrence matched index made
      have enabled (position : Fin members.length) :=
        ((native_admits_iff members[position].toNative).mp
          (clear.admitted members[position] (List.getElem_mem ..))).2.1
      refine ⟨(packetFinal_present_inl witness occurrence).mpr present,NativePacketRounds.fitData data,?_,?_⟩
      · rw [packetFinal_equations]
        exact NativePacketRounds.fitData_joint data nonempty enabled
      · rw [label_produced clear index occurrence made]
        exact (fitData_base_output_iff data index pattern occurrence).mpr output

/-- The same result observer reads every supplied ordering of the actual clear family. -/
theorem packet_result_reads_iff_order {initial last : NativeState S O Γ sort}
    (members : List (LiveFiring initial)) (nonempty : members ≠ [])
    (clear : NativeIterated.FamilyClear initial members) {order : List (LiveFiring initial)}
    (permutation : order.Perm members) (witness : NativeRoundExecution.Witness initial order last)
    (occurrence : O) (pattern : ClosedTerm S Γ sort) :
    PacketReads members occurrence pattern ↔ Reads last occurrence pattern := by
  obtain ⟨canonical,canonicalRun,_,_,_⟩ :=
    NativeRoundExecution.every_order_run_of_family clear (List.Perm.refl members)
  have same := NativeIterated.orders_agree members.length members rfl clear permutation
    canonicalRun.sequential witness.sequential
  exact (packet_result_reads_iff members nonempty clear canonicalRun occurrence pattern).trans
    (deadEquiv_reads_iff same occurrence pattern)

/-- Actual guarded admission earns the clear-family premise of the result law. -/
theorem guarded_round_result_reads_iff {initial last : NativeState S O Γ sort}
    (members : List (LiveFiring initial)) (nonempty : members ≠ [])
    (shapes : ∀ index : Fin members.length, native.Shapes members[index].toNative)
    (round : AnnotatedRuns.Round (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (NativePacketRounds.label members) (NativePacketStep.configuration initial 0)
      (NativePacketGuardedRounds.image members))
    {order : List (LiveFiring initial)} (permutation : order.Perm members)
    (witness : NativeRoundExecution.Witness initial order last) (occurrence : O)
    (pattern : ClosedTerm S Γ sort) :
    PacketReads members occurrence pattern ↔ Reads last occurrence pattern :=
  packet_result_reads_iff_order members nonempty
    (NativePacketGuardedRounds.clear_of_round members nonempty shapes round) permutation witness occurrence pattern

end NativeReadings

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.PacketResultReadouts
