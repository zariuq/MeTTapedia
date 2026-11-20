import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketGuardedAdmission

/-!
# Guarded native families at their actual own and pair information

The canonical tagged presentation retains one physical label map for the
whole family. Only the selected members contribute equations at an own or
pair cut. Equation guards remain ordinary checks; the other observations
use the concrete decoded regions, without collecting a fixed seen set.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketGuardedRounds

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open MeTTaCalculus.OccurrenceCommits (Enabled)
open TaggedAssignments (Object Substitution)
open NativePacketStep (Terms Ports packetAction)

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}

noncomputable def firing {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (index : Fin members.length) : AnnotatedRuns.Firing (Terms S O Γ sort) (Substitution S) (Ports O) where
  rule := NativePacketGuardedAdmission.body members[index] (NativePacketRounds.useTag index)
  selection := NativePacketStep.selection members[index]
  queries := NativePacketGuardedAdmission.questions members[index] (NativePacketRounds.useTag index)

noncomputable def image {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :=
  (List.finRange members.length).map (firing members)

theorem firing_problem {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (index : Fin members.length) :
    (firing members index).selection.problem (NativePacketRounds.label members)
        (firing members index).rule (NativePacketStep.configuration s 0) =
      NativePacketQueryCuts.memberProblem members index := rfl

theorem firing_added {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (index : Fin members.length) :
    (firing members index).added (NativePacketRounds.label members) =
      (NativePacketStep.baseFiring members[index] (NativePacketRounds.useTag index)).added
        (NativePacketRounds.label members) := rfl

theorem pair_problem {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) :
    AnnotatedRuns.pairCut (NativePacketRounds.label members) (NativePacketStep.configuration s 0)
        (firing members first) (firing members second) =
      NativePacketQueryCuts.pairProblem members first second := rfl

theorem joint_problem {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :
    AnnotatedRuns.jointProblem (NativePacketRounds.label members) (NativePacketStep.configuration s 0)
        (image members) = NativePacketRounds.jointProblem members := by
  unfold AnnotatedRuns.jointProblem image NativePacketRounds.jointProblem
  rw [NativePacketRounds.image_as_indices]
  simp only [AnnotatedRuns.jointProblem,List.flatMap_map]
  rfl

theorem image_length {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :
    (image members).length = members.length := by simp [image]

theorem ordinary_ignoresWrites {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) :
    ∀ check ∈ (firing members first).rule.checks,
      Check.IgnoresWrites (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
        (NativePacketQueryCuts.pairProblem members first second) (NativePacketRounds.label members)
        (NativePacketStep.selection members[second]) check := by
  intro check inside
  obtain ⟨original,_,compiled⟩ := List.mem_flatMap.mp inside
  cases original with
  | equal left right =>
      simp only [NativePacketGuardedAdmission.ordinary,List.mem_singleton] at compiled
      subst check
      trivial
  | predicate quantifier pattern => cases compiled
  | count pattern number => cases compiled

def pairData {s : NativeState S O Γ sort} {first second : LiveFiring s} {target : Frames.Frame S}
    (joint : NativeResidual.Joint s first.toNative.information second.toNative.information target) :
    FamilyInformation.SolutionData s [first,second] target where
  shared := Assignment.compose joint.left (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)
  member := Fin.cases joint.left (fun _ => joint.right)
  agrees index := by
    fin_cases index
    · rfl
    · exact joint.agree.symm
  models index := by
    fin_cases index
    · exact joint.left_models
    · exact joint.right_models

def dataJoint {s : NativeState S O Γ sort} {first second : LiveFiring s} {target : Frames.Frame S}
    (data : FamilyInformation.SolutionData s [first,second] target) :
    NativeResidual.Joint s first.toNative.information second.toNative.information target where
  left := data.member 0
  right := data.member 1
  left_models := data.models 0
  right_models := data.models 1
  agree := (data.agrees 0).trans (data.agrees 1).symm

/-- Blindness of one concrete decoded pattern at the pair's own models. -/
def PatternBlind {s : NativeState S O Γ sort} (reader writer : LiveFiring s)
    (pattern : Term (signature S s.infoFrame.arity) Γ sort) : Prop :=
  ∀ (target : Frames.Frame S) (joint : NativeResidual.Joint s reader.toNative.information writer.toNative.information target),
    (∀ occurrence ∈ writer.selection.taken,
      ¬ ContextualConditionalRows.Matches s.locals s.infoFrame.arity joint.left (instantiate joint.left pattern)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows occurrence)) ∧
    (∀ occurrence ∈ writer.selection.made,
      instantiate joint.left pattern ≠ instantiate joint.right (writer.outputs occurrence))

def CheckBlind {s : NativeState S O Γ sort} (reader writer : LiveFiring s) :
    Check (Term (signature S s.infoFrame.arity) Γ sort) → Prop
  | .equal _ _ => True
  | .predicate _ pattern | .count pattern _ => PatternBlind reader writer pattern

theorem region_ignored_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) (different : first ≠ second)
    (firstEnabled : Enabled (fun _ : O => ()) s.state.present (members[first].selection.commit (T := Unit)))
    (secondEnabled : Enabled (fun _ : O => ()) s.state.present (members[second].selection.commit (T := Unit)))
    (unique : ∀ occurrence ∈ members[second].selection.made, ∀ other : Fin members.length,
      occurrence ∈ members[other].selection.made → other = second)
    (pattern : Term (signature S s.infoFrame.arity) Γ sort)
    (query : PredicateQueryAdmission.RegionQuery (Terms S O Γ sort) (Substitution S) (Ports O))
    (region : query.region = NativePacketQueryView.region
      (NativePacketStep.useObject s (NativePacketRounds.useTag first)) pattern) :
    query.IgnoresWrites (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
        (NativePacketQueryCuts.pairProblem members first second) (NativePacketRounds.label members)
        (NativePacketStep.selection members[second]) ↔ PatternBlind members[first] members[second] pattern := by
  change (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)).Entails
    (NativePacketQueryCuts.pairProblem members first second)
    (fun substitution => ∀ occurrence ∈ (NativePacketStep.selection members[second]).taken ++
      (NativePacketStep.selection members[second]).made,
      query.region substitution (NativePacketRounds.label members occurrence) = false) ↔ _
  rw [region]
  refine (NativePacketQueryCuts.pair_count_ignoresWrites_iff members first second different
    firstEnabled secondEnabled unique pattern 0).trans ?_
  constructor
  · intro blind target joint
    exact blind target (pairData joint)
  · intro blind target data
    exact blind target (dataJoint data)

theorem observed_ignored_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) (different : first ≠ second)
    (firstEnabled : Enabled (fun _ : O => ()) s.state.present (members[first].selection.commit (T := Unit)))
    (secondEnabled : Enabled (fun _ : O => ()) s.state.present (members[second].selection.commit (T := Unit)))
    (unique : ∀ occurrence ∈ members[second].selection.made, ∀ other : Fin members.length,
      occurrence ∈ members[other].selection.made → other = second)
    (check : Check (Term (signature S s.infoFrame.arity) Γ sort)) :
    (∀ query ∈ NativePacketGuardedAdmission.observed
      (NativePacketStep.useObject s (NativePacketRounds.useTag first)) check,
      query.IgnoresWrites (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
        (NativePacketQueryCuts.pairProblem members first second) (NativePacketRounds.label members)
        (NativePacketStep.selection members[second])) ↔ CheckBlind members[first] members[second] check := by
  cases check with
  | equal left right => simp [NativePacketGuardedAdmission.observed,CheckBlind]
  | predicate quantifier pattern =>
      simp only [NativePacketGuardedAdmission.observed,List.mem_singleton,forall_eq,CheckBlind]
      exact region_ignored_iff members first second different firstEnabled secondEnabled unique pattern _ rfl
  | count pattern number =>
      simp only [NativePacketGuardedAdmission.observed,List.mem_singleton,forall_eq,CheckBlind]
      exact region_ignored_iff members first second different firstEnabled secondEnabled unique pattern _ rfl

theorem questions_ignored_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) (different : first ≠ second)
    (firstEnabled : Enabled (fun _ : O => ()) s.state.present (members[first].selection.commit (T := Unit)))
    (secondEnabled : Enabled (fun _ : O => ()) s.state.present (members[second].selection.commit (T := Unit)))
    (unique : ∀ occurrence ∈ members[second].selection.made, ∀ other : Fin members.length,
      occurrence ∈ members[other].selection.made → other = second) :
    (∀ query ∈ (firing members first).queries,
      query.IgnoresWrites (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
        (NativePacketQueryCuts.pairProblem members first second) (NativePacketRounds.label members)
        (NativePacketStep.selection members[second])) ↔
      (∀ check ∈ (NativePacketGuardedAdmission.prepared members[first]).checks,
        CheckBlind members[first] members[second] check) ∧
      ∀ pattern ∈ members[first].patterns, PatternBlind members[first] members[second] pattern.1 := by
  change (∀ query ∈ NativePacketGuardedAdmission.questions members[first] (NativePacketRounds.useTag first), _) ↔ _
  simp only [NativePacketGuardedAdmission.questions,List.forall_mem_append,List.forall_mem_map]
  apply and_congr
  · constructor
    · intro all check inside
      apply (observed_ignored_iff members first second different firstEnabled secondEnabled unique check).mp
      intro query present
      exact all query (List.mem_flatMap.mpr ⟨check,inside,present⟩)
    · intro all query inside
      obtain ⟨check,present,observed⟩ := List.mem_flatMap.mp inside
      exact ((observed_ignored_iff members first second different firstEnabled secondEnabled unique check).mpr
        (all check present)) query observed
  · exact forall_congr' fun pattern => forall_congr' fun _ =>
      region_ignored_iff members first second different firstEnabled secondEnabled unique pattern.1 _ rfl

theorem blind_of_clear {s : NativeState S O Γ sort} {reader writer : LiveFiring s}
    (clear : Clear reader writer.selection writer.rule writer.outputs) :
    (∀ check ∈ (NativePacketGuardedAdmission.prepared reader).checks, CheckBlind reader writer check) ∧
      ∀ pattern ∈ reader.patterns, PatternBlind reader writer pattern.1 := by
  constructor
  · intro check inside
    cases check with
    | equal left right => trivial
    | predicate quantifier pattern =>
        intro target joint
        exact ⟨fun occurrence taken => (clear.blindTakes target joint occurrence taken).1 _ inside,
          fun occurrence made => (clear.blindOutputs target joint occurrence made).1 _ inside⟩
    | count pattern number =>
        intro target joint
        exact ⟨fun occurrence taken => (clear.blindTakes target joint occurrence taken).1 _ inside,
          fun occurrence made => (clear.blindOutputs target joint occurrence made).1 _ inside⟩
  · intro pattern inside target joint
    exact ⟨fun occurrence taken => (clear.blindTakes target joint occurrence taken).2 _ inside,
      fun occurrence made => (clear.blindOutputs target joint occurrence made).2 _ inside⟩

theorem clear_of_blind {s : NativeState S O Γ sort} (reader writer : LiveFiring s)
    (takes : Disjoint reader.selection.taken.toFinset writer.selection.taken.toFinset)
    (ports : Disjoint reader.selection.made.toFinset writer.selection.made.toFinset)
    (keeps : Disjoint writer.selection.taken.toFinset reader.selection.read.toFinset)
    (joint : ∃ target : Frames.Frame S,
      Nonempty (NativeResidual.Joint s reader.toNative.information writer.toNative.information target))
    (blind : (∀ check ∈ (NativePacketGuardedAdmission.prepared reader).checks, CheckBlind reader writer check) ∧
      ∀ pattern ∈ reader.patterns, PatternBlind reader writer pattern.1) :
    Clear reader writer.selection writer.rule writer.outputs := by
  refine ⟨takes,ports,keeps,joint,?_,?_⟩
  · intro target pair occurrence taken
    refine ⟨?_,fun pattern inside => (blind.2 pattern inside target pair).1 occurrence taken⟩
    intro check inside
    have ignored := blind.1 check inside
    cases check with
    | equal left right => exact not_false
    | predicate quantifier pattern => exact (ignored target pair).1 occurrence taken
    | count pattern number => exact (ignored target pair).1 occurrence taken
  · intro target pair occurrence made
    refine ⟨?_,fun pattern inside => (blind.2 pattern inside target pair).2 occurrence made⟩
    intro check inside
    have ignored := blind.1 check inside
    cases check with
    | equal left right => exact not_false
    | predicate quantifier pattern => exact (ignored target pair).2 occurrence made
    | count pattern number => exact (ignored target pair).2 occurrence made

theorem compatible_iff_clears {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (first second : Fin members.length) (different : first ≠ second)
    (firstEnabled : Enabled (fun _ : O => ()) s.state.present (members[first].selection.commit (T := Unit)))
    (secondEnabled : Enabled (fun _ : O => ()) s.state.present (members[second].selection.commit (T := Unit)))
    (uniqueFirst : ∀ occurrence ∈ members[first].selection.made, ∀ other : Fin members.length,
      occurrence ∈ members[other].selection.made → other = first)
    (uniqueSecond : ∀ occurrence ∈ members[second].selection.made, ∀ other : Fin members.length,
      occurrence ∈ members[other].selection.made → other = second)
    (joint : ∃ target : Frames.Frame S,
      Nonempty (NativeResidual.Joint s members[first].toNative.information members[second].toNative.information target)) :
    AnnotatedRuns.Compatible (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
        (NativePacketRounds.label members) (NativePacketStep.configuration s 0)
        (firing members first) (firing members second) ↔ NativeIterated.Clears members[first] members[second] := by
  constructor
  · rintro ⟨physical,_,_,firstQuestions,secondQuestions⟩
    obtain ⟨takes,ports,keeps,keeps'⟩ :=
      (NativePacketRounds.physical_independent_iff members[first] members[second] _).mp physical
    rw [pair_problem] at firstQuestions secondQuestions
    have firstBlind := (questions_ignored_iff members first second different firstEnabled secondEnabled uniqueSecond).mp firstQuestions
    have secondAt : ∀ query ∈ (firing members second).queries,
        query.IgnoresWrites (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
          (NativePacketQueryCuts.pairProblem members second first) (NativePacketRounds.label members)
          (NativePacketStep.selection members[first]) := by
      intro query inside
      apply AnnotatedRuns.query_ignoresWrites_of_refines _ _
        (AnnotatedRuns.pairCut_refines_swap _ _ _ (firing members first) (firing members second))
        (secondQuestions query inside)
    have secondBlind := (questions_ignored_iff members second first different.symm secondEnabled firstEnabled uniqueFirst).mp secondAt
    obtain ⟨target,⟨pair⟩⟩ := joint
    exact ⟨clear_of_blind _ _ takes ports keeps' ⟨target,⟨pair⟩⟩ firstBlind,
      clear_of_blind _ _ takes.symm ports.symm keeps ⟨target,⟨pair.swap⟩⟩ secondBlind⟩
  · intro clears
    refine ⟨(NativePacketRounds.physical_independent_iff members[first] members[second] _).mpr
      (NativePacketRounds.resources_of_clears clears),?_,?_,?_,?_⟩
    · exact ordinary_ignoresWrites members first second
    · intro check inside
      apply AnnotatedRuns.check_ignoresWrites_of_refines _ _
        (AnnotatedRuns.pairCut_refines_swap _ _ _ (firing members second) (firing members first))
        (ordinary_ignoresWrites members second first check inside)
    · exact (questions_ignored_iff members first second different firstEnabled secondEnabled uniqueSecond).mpr
        (blind_of_clear clears.1)
    · intro query inside
      apply AnnotatedRuns.query_ignoresWrites_of_refines _ _
        (AnnotatedRuns.pairCut_refines_swap _ _ _ (firing members second) (firing members first))
        (((questions_ignored_iff members second first different.symm secondEnabled firstEnabled uniqueFirst).mpr
          (blind_of_clear clears.2)) query inside)

section Admission

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

theorem valid_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (index : Fin members.length) (shapes : native.Shapes members[index].toNative) :
    (firing members index).Valid (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
        (NativePacketRounds.label members) (NativePacketStep.configuration s 0) ↔
      members[index].toNative.Realized ∧
        (NativePacketStep.selection members[index]).made.map (NativePacketRounds.label members) =
          (NativePacketStep.body members[index] (NativePacketRounds.useTag index)).produce :=
  NativePacketGuardedAdmission.regionValid_iff members index shapes

theorem realized_of_round {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (shapes : ∀ index : Fin members.length, native.Shapes members[index].toNative)
    (round : AnnotatedRuns.Round (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (NativePacketRounds.label members) (NativePacketStep.configuration s 0) (image members))
    (index : Fin members.length) : members[index].toNative.Realized :=
  ((valid_iff members index (shapes index)).mp
    (round.valid _ (List.mem_map_of_mem (by simp)))).1

theorem joint_of_round {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (nonempty : members ≠ [])
    (shapes : ∀ index : Fin members.length, native.Shapes members[index].toNative)
    (round : AnnotatedRuns.Round (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (NativePacketRounds.label members) (NativePacketStep.configuration s 0) (image members)) :
    NativeIterated.Jointly s members := by
  have consistent := round.joint
  rw [joint_problem] at consistent
  exact (NativePacketRounds.consistent_iff_jointly members nonempty fun index =>
    ((native_admits_iff members[index].toNative).mp (realized_of_round members shapes round index)).2.1).mp consistent

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem compatible_at {s : NativeState S O Γ sort} {members : List (LiveFiring s)}
    (round : AnnotatedRuns.Round (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (NativePacketRounds.label members) (NativePacketStep.configuration s 0) (image members))
    (first second : Fin members.length) (different : first ≠ second) :
    AnnotatedRuns.Compatible (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (NativePacketRounds.label members) (NativePacketStep.configuration s 0)
      (firing members first) (firing members second) := by
  have pairs := round.compatible
  rw [image,List.pairwise_map] at pairs
  have ordered (left right : Fin members.length) (before : left < right) :
      AnnotatedRuns.Compatible (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
        (NativePacketRounds.label members) (NativePacketStep.configuration s 0)
        (firing members left) (firing members right) := by
    simpa using (List.pairwise_iff_getElem.mp pairs) left.val right.val (by simp) (by simp) before
  rcases lt_or_gt_of_ne different with before | after
  · exact ordered first second before
  · exact (ordered second first after).symm _ _

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem output_unique_of_round {s : NativeState S O Γ sort} {members : List (LiveFiring s)}
    (round : AnnotatedRuns.Round (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (NativePacketRounds.label members) (NativePacketStep.configuration s 0) (image members))
    (index : Fin members.length) (occurrence : O) (made : occurrence ∈ members[index].selection.made)
    (other : Fin members.length) (also : occurrence ∈ members[other].selection.made) : other = index := by
  by_contra different
  have physical := (NativePacketRounds.physical_independent_iff members[other] members[index] _).mp
    (compatible_at round other index different).1
  exact Finset.disjoint_left.mp physical.2.1 (List.mem_toFinset.mpr also) (List.mem_toFinset.mpr made)

theorem clear_of_round {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (nonempty : members ≠ [])
    (shapes : ∀ index : Fin members.length, native.Shapes members[index].toNative)
    (round : AnnotatedRuns.Round (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (NativePacketRounds.label members) (NativePacketStep.configuration s 0) (image members)) :
    NativeIterated.FamilyClear s members := by
  have realized := realized_of_round members shapes round
  have enabled : ∀ index : Fin members.length,
      Enabled (fun _ : O => ()) s.state.present (members[index].selection.commit (T := Unit)) :=
    fun index => ((native_admits_iff members[index].toNative).mp (realized index)).2.1
  have jointly := joint_of_round members nonempty shapes round
  refine ⟨?_,?_,jointly⟩
  · intro member inside
    obtain ⟨index,bound,same⟩ := List.getElem_of_mem inside
    have admitted := realized ⟨index,bound⟩
    change members[index].toNative.Realized at admitted
    rwa [same] at admitted
  · apply List.pairwise_iff_getElem.mpr
    intro first second firstBound secondBound before
    let left : Fin members.length := ⟨first,firstBound⟩
    let right : Fin members.length := ⟨second,secondBound⟩
    have different : left ≠ right := fun same => (ne_of_lt before) (congrArg Fin.val same)
    exact (compatible_iff_clears members left right different (enabled left) (enabled right)
      (output_unique_of_round round left) (output_unique_of_round round right)
      (jointly.joint (List.getElem_mem ..) (List.getElem_mem ..))).mp
        (compatible_at round left right different)

theorem round_of_clear {s : NativeState S O Γ sort} {members : List (LiveFiring s)}
    (nonempty : members ≠ []) (clear : NativeIterated.FamilyClear s members) :
    AnnotatedRuns.Round (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (NativePacketRounds.label members) (NativePacketStep.configuration s 0) (image members) := by
  have realized (index : Fin members.length) := clear.admitted members[index] (List.getElem_mem ..)
  have enabled (index : Fin members.length) := ((native_admits_iff members[index].toNative).mp (realized index)).2.1
  have unique (index : Fin members.length) (occurrence : O) (made : occurrence ∈ members[index].selection.made)
      (other : Fin members.length) (also : occurrence ∈ members[other].selection.made) : other = index := by
    by_contra different
    exact Finset.disjoint_left.mp (NativePacketRounds.clears_at clear other index different).1.ports
      (List.mem_toFinset.mpr also) (List.mem_toFinset.mpr made)
  refine ⟨?_,?_,?_⟩
  · intro event inside
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp inside
    apply (valid_iff members index ((native_admits_iff members[index].toNative).mp (realized index)).1).mpr
    have keeps := NativePacketRounds.keeps_of_clear clear index
    rw [RuleSyntax.StepWeb.Rounds.KeepsLabels,NativePacketRounds.member_opened] at keeps
    exact ⟨realized index,keeps⟩
  · rw [joint_problem]
    exact (NativePacketRounds.consistent_iff_jointly members nonempty enabled).mpr clear.jointly
  · rw [image,List.pairwise_map]
    apply (List.pairwise_lt_finRange members.length).imp
    intro first second before
    have different : first ≠ second := ne_of_lt before
    exact (compatible_iff_clears members first second different (enabled first) (enabled second)
      (unique first) (unique second) (clear.jointly.joint (List.getElem_mem ..) (List.getElem_mem ..))).mpr
        (NativePacketRounds.clears_at clear first second different)

theorem round_iff {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (nonempty : members ≠ [])
    (shapes : ∀ index : Fin members.length, native.Shapes members[index].toNative) :
    AnnotatedRuns.Round (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
        (NativePacketRounds.label members) (NativePacketStep.configuration s 0) (image members) ↔
      NativeIterated.FamilyClear s members :=
  ⟨clear_of_round members nonempty shapes,round_of_clear nonempty⟩

theorem round_iff_concurrent {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (nonempty : members ≠ [])
    (shapes : ∀ index : Fin members.length, native.Shapes members[index].toNative) :
    AnnotatedRuns.Round (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
        (NativePacketRounds.label members) (NativePacketStep.configuration s 0) (image members) ↔
      ∃ last, NativeConcurrent.Concurrent s (members : Multiset (LiveFiring s)) last := by
  rw [round_iff members nonempty shapes]
  constructor
  · exact NativeConcurrent.concurrent_of_clear
  · rintro ⟨_,order,same,clear,_⟩
    exact clear.perm (Multiset.coe_eq_coe.mp same).symm

theorem native_every_order {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (nonempty : members ≠ [])
    (shapes : ∀ index : Fin members.length, native.Shapes members[index].toNative)
    (round : AnnotatedRuns.Round (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (NativePacketRounds.label members) (NativePacketStep.configuration s 0) (image members))
    {order : List (LiveFiring s)} (permutes : order.Perm members) :
    ∃ last, ∃ witness : NativeRoundExecution.Witness s order last,
      witness.toRun.last = last ∧ witness.toRun.word.length = members.length ∧
        witness.toRun.word.map (fun event => event.2.selection) = order.map (fun event => event.selection) :=
  NativeRoundExecution.every_order_run_of_family (clear_of_round members nonempty shapes round) permutes

end Admission

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketGuardedRounds
