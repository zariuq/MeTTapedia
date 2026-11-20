import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketScopedQueries
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketGuardedRounds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.PacketOwnRounds

/-!
# The scoped own bag and the guarded symbolic round

The store is a bag of physical occurrences, the commit is a bag of matches,
each guard is asked after that member's own tells, the program is fixed,
and knowledge is one store. The canonical program earns query freshness
and output ownership. Its own admission is a guarded round precisely with
the additional, actual pair-cut query blindness stated below. Atomic own
bags remain a separate execution choice.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketScopedRounds

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open NativePacketStep (Terms Ports packetAction)
open RuleSyntax RuleSyntax.JointFirings
open RuleSyntax.StepWeb
open RuleSyntax.StepWeb.ObservedBags

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}

noncomputable def plainImage {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :
    List (AnnotatedRuns.Firing (Terms S O Γ sort) (TaggedAssignments.Substitution S) (Ports O)) :=
  (NativePacketGuardedRounds.image members).map fun event => AnnotatedRuns.Firing.ofPlain (S := TaggedAssignments.Substitution S) event.plain

def PairBlind {s : NativeState S O Γ sort} (members : List (LiveFiring s)) : Prop :=
  (NativePacketGuardedRounds.image members).Pairwise fun first second =>
    (∀ query ∈ first.queries,
      query.IgnoresWrites (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
        (AnnotatedRuns.pairCut (NativePacketRounds.label members) (NativePacketStep.configuration s 0) first second)
        (NativePacketRounds.label members) second.selection) ∧
    (∀ query ∈ second.queries,
      query.IgnoresWrites (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
        (AnnotatedRuns.pairCut (NativePacketRounds.label members) (NativePacketStep.configuration s 0) first second)
        (NativePacketRounds.label members) first.selection)

theorem raw_image {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :
    Rounds.image (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
        (NativePacketScopedQueries.memberList members) = plainImage members := by
  unfold Rounds.image NativePacketScopedQueries.memberList plainImage NativePacketGuardedRounds.image
  simp only [List.map_map]
  apply List.map_congr_left
  intro index _
  exact congrArg
    (fun body : RuleInstance (Terms S O Γ sort) =>
      ({ rule := body, queries := [], selection := NativePacketStep.selection members[index] } :
        AnnotatedRuns.Firing (Terms S O Γ sort) (TaggedAssignments.Substitution S) (Ports O)))
    (NativePacketScopedQueries.member_opened members index)

theorem plain_joint_problem {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :
    AnnotatedRuns.jointProblem (NativePacketRounds.label members) (NativePacketStep.configuration s 0)
        (plainImage members) =
      AnnotatedRuns.jointProblem (NativePacketRounds.label members) (NativePacketStep.configuration s 0)
        (NativePacketGuardedRounds.image members) := by
  unfold AnnotatedRuns.jointProblem plainImage
  rw [List.flatMap_map]
  rfl

theorem follow_without_queries (label : Ports O → Terms S O Γ sort)
    (C : Configuration (Terms S O Γ sort) (Ports O))
    (events : List (AnnotatedRuns.Firing (Terms S O Γ sort) (TaggedAssignments.Substitution S) (Ports O))) :
    AnnotatedRuns.follow label C (events.map fun event =>
        AnnotatedRuns.Firing.ofPlain (S := TaggedAssignments.Substitution S) event.plain) =
      AnnotatedRuns.follow label C events := by
  induction events generalizing C with
  | nil => rfl
  | cons event rest ih => exact ih (event.result label C)

theorem plain_round {s : NativeState S O Γ sort} {members : List (LiveFiring s)}
    (round : AnnotatedRuns.Round (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (NativePacketRounds.label members) (NativePacketStep.configuration s 0) (NativePacketGuardedRounds.image members)) :
    AnnotatedRuns.Round (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (NativePacketRounds.label members) (NativePacketStep.configuration s 0) (plainImage members) := by
  refine ⟨?_,?_,?_⟩
  · intro event inside
    obtain ⟨original,member,rfl⟩ := List.mem_map.mp inside
    exact ⟨(round.valid original member).firing,fun _ impossible => by cases impossible⟩
  · rw [plain_joint_problem]
    exact round.joint
  · rw [plainImage,List.pairwise_map]
    exact round.compatible.imp fun compatible =>
      ⟨compatible.1,compatible.2.1,compatible.2.2.1,
        (fun _ impossible => by cases impossible),(fun _ impossible => by cases impossible)⟩

omit [DecidableEq O] in
theorem member_positive {s : NativeState S O Γ sort} (members : List (LiveFiring s)) (index : Fin members.length) :
    Scope.Positive (NativePacketScopedQueries.member members index).rule := by
  refine ⟨?_,rfl⟩
  intro compiled inside
  obtain ⟨check,_,guarded⟩ := List.mem_flatMap.mp inside
  cases check with
  | equal left right =>
      obtain rfl := List.mem_singleton.mp guarded
      exact ⟨_,_,rfl⟩
  | predicate quantifier pattern => cases guarded
  | count pattern number => cases guarded

omit [DecidableEq O] in
theorem selection_eq {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :
    (bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (NativePacketScopedQueries.memberList members)).selection =
        (bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
          (NativePacketRounds.memberList members)).selection := by
  simp only [bagOf,Bag.selection,NativePacketScopedQueries.memberList,NativePacketRounds.memberList,
    List.flatMap_map,NativePacketScopedQueries.member,NativePacketRounds.member]

theorem forget_checks_own {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (own : (bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (NativePacketScopedQueries.memberList members)).AdmitsOwn
        (OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (NativePacketRounds.source members)) :
    (bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (NativePacketRounds.memberList members)).AdmitsOwn
      (OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (NativePacketRounds.source members) := by
  have taken := own.1.2.1
  have made := own.1.2.2.1
  have enabled := own.2.1
  rw [selection_eq] at taken made enabled
  refine ⟨⟨PacketJointFreshness.bag_fresh members,taken,made,?_⟩,enabled,?_,?_⟩
  · intro selected inside
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp inside
    exact own.1.2.2.2 (NativePacketScopedQueries.member members index)
      (List.mem_map.mpr ⟨index,List.mem_finRange index,rfl⟩)
  · have oldInformation :
        (bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (NativePacketRounds.memberList members)).information
            (OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (NativePacketRounds.source members) =
          NativePacketRounds.jointProblem members :=
      Rounds.information_embed (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
        (NativePacketRounds.label members) (NativePacketStep.configuration s 0) (NativePacketRounds.memberList members)
    rw [oldInformation,← NativePacketScopedQueries.joint_information]
    exact own.2.2.1
  · intro selected inside target substitution model
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp inside
    refine ⟨?_,?_⟩
    · intro check guarded
      rw [NativePacketRounds.member_opened] at guarded
      cases guarded
    · intro query impossible
      cases impossible

theorem keeps_of_own {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (own : (bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (NativePacketScopedQueries.memberList members)).AdmitsOwn
        (OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (NativePacketRounds.source members))
    (index : Fin members.length) :
    Rounds.KeepsLabels (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (NativePacketRounds.label members) (NativePacketScopedQueries.member members index) := by
  have keeps := PacketOwnRounds.keeps_of_own members (forget_checks_own members own) index
  rw [Rounds.KeepsLabels,NativePacketRounds.member_opened] at keeps
  rw [Rounds.KeepsLabels,NativePacketScopedQueries.member_opened]
  exact keeps

theorem raw_round_of_scoped {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (admitted : (scopedStep (OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
      (NativePacketScopedQueries.scopedQueries members)).Admits (s := NativePacketRounds.source members)
        (bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (NativePacketScopedQueries.memberList members))) :
    AnnotatedRuns.Round (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (NativePacketRounds.label members) (NativePacketStep.configuration s 0) (plainImage members) := by
  have own := ((NativePacketScopedQueries.scoped_admits_iff_queries members).mp admitted).2.1
  rw [← raw_image]
  apply Rounds.round_image_of_positive _ own
  · intro selected inside
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp inside
    exact keeps_of_own members own index
  · intro selected inside
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp inside
    exact member_positive members index

/-- The actual scoped result is the exact embedded update fold. This does
not assert that the fold is executable without the pair-blindness licence. -/
theorem scoped_result_eq_follow {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (admitted : (scopedStep (OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
      (NativePacketScopedQueries.scopedQueries members)).Admits (s := NativePacketRounds.source members)
        (bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (NativePacketScopedQueries.memberList members))) :
    (scopedStep (OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
      (NativePacketScopedQueries.scopedQueries members)).result
        (bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (NativePacketScopedQueries.memberList members)) admitted =
      OneFrame.embed (NativePacketRounds.label members)
        (AnnotatedRuns.follow (NativePacketRounds.label members) (NativePacketStep.configuration s 0)
          (NativePacketGuardedRounds.image members)) := by
  have own := ((NativePacketScopedQueries.scoped_admits_iff_queries members).mp admitted).2.1
  have result := Rounds.result_embed (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) own.1 own.2.1
    (fun selected inside => by
      obtain ⟨index,_,rfl⟩ := List.mem_map.mp inside
      exact keeps_of_own members own index)
  have images := congrArg (AnnotatedRuns.follow (NativePacketRounds.label members) (NativePacketStep.configuration s 0))
    (raw_image members)
  have followed := images.trans (follow_without_queries (NativePacketRounds.label members)
    (NativePacketStep.configuration s 0) (NativePacketGuardedRounds.image members))
  exact result.trans (congrArg (OneFrame.embed (NativePacketRounds.label members)) followed)

theorem scoped_of_round {s : NativeState S O Γ sort} {members : List (LiveFiring s)} (nonempty : members ≠ [])
    (round : AnnotatedRuns.Round (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (NativePacketRounds.label members) (NativePacketStep.configuration s 0) (NativePacketGuardedRounds.image members)) :
    (scopedStep (OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
      (NativePacketScopedQueries.scopedQueries members)).Admits (s := NativePacketRounds.source members)
        (bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (NativePacketScopedQueries.memberList members)) := by
  have bare := plain_round round
  rw [← raw_image] at bare
  have own := (Rounds.admitsOwn_of_round _ bare (NativePacketScopedQueries.bag_fresh members)
    (fun selected inside => by
      obtain ⟨index,_,rfl⟩ := List.mem_map.mp inside
      rfl)).1
  apply (NativePacketScopedQueries.scoped_admits_iff_queries members).mpr
  refine ⟨?_,own,?_⟩
  · intro empty
    have lengthZero : members.length = 0 := by
      simpa only [NativePacketScopedQueries.memberList,List.length_map,List.length_finRange,List.length_nil]
        using congrArg List.length empty
    exact nonempty (List.length_eq_zero_iff.mp lengthZero)
  · intro index query inside
    have valid := round.valid (NativePacketGuardedRounds.firing members index)
      (List.mem_map.mpr ⟨index,List.mem_finRange index,rfl⟩)
    exact valid.observations query inside

theorem round_iff_scoped_and_blind {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (nonempty : members ≠ []) :
    AnnotatedRuns.Round (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
        (NativePacketRounds.label members) (NativePacketStep.configuration s 0) (NativePacketGuardedRounds.image members) ↔
      (scopedStep (OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
        (NativePacketScopedQueries.scopedQueries members)).Admits (s := NativePacketRounds.source members)
          (bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (NativePacketScopedQueries.memberList members)) ∧
        PairBlind members := by
  constructor
  · intro round
    exact ⟨scoped_of_round nonempty round,
      round.compatible.imp fun compatible => ⟨compatible.2.2.2.1,compatible.2.2.2.2⟩⟩
  · rintro ⟨admitted,blind⟩
    have bare := raw_round_of_scoped members admitted
    have fields := (NativePacketScopedQueries.scoped_admits_iff_queries members).mp admitted
    refine ⟨?_,?_,?_⟩
    · intro event inside
      have valid := bare.valid (AnnotatedRuns.Firing.ofPlain (S := TaggedAssignments.Substitution S) event.plain) (List.mem_map.mpr ⟨event,inside,rfl⟩)
      obtain ⟨index,_,rfl⟩ := List.mem_map.mp inside
      exact ⟨valid.firing,fields.2.2 index⟩
    · rw [← plain_joint_problem]
      exact bare.joint
    · have pairs := List.pairwise_map.mp bare.compatible
      exact (pairs.and blind).imp fun compatible =>
        ⟨compatible.1.1,compatible.1.2.1,compatible.1.2.2.1,compatible.2.1,compatible.2.2⟩

section Native

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

theorem scoped_of_clear {s : NativeState S O Γ sort} {members : List (LiveFiring s)}
    (nonempty : members ≠ []) (clear : NativeIterated.FamilyClear s members) :
    (scopedStep (OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
      (NativePacketScopedQueries.scopedQueries members)).Admits (s := NativePacketRounds.source members)
        (bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (NativePacketScopedQueries.memberList members)) :=
  scoped_of_round nonempty (NativePacketGuardedRounds.round_of_clear nonempty clear)

theorem scoped_and_blind_iff_clear {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (nonempty : members ≠ []) (shapes : ∀ index : Fin members.length, native.Shapes members[index].toNative) :
    ((scopedStep (OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
      (NativePacketScopedQueries.scopedQueries members)).Admits (s := NativePacketRounds.source members)
        (bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (NativePacketScopedQueries.memberList members)) ∧
      PairBlind members) ↔ NativeIterated.FamilyClear s members :=
  (round_iff_scoped_and_blind members nonempty).symm.trans (NativePacketGuardedRounds.round_iff members nonempty shapes)

end Native

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketScopedRounds
