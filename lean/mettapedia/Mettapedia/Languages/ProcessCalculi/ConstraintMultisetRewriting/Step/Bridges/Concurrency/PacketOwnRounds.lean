import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.PacketJointFreshness

/-!
# Own-guard bags, annotated rounds and native packet families

The actual indexed packet bag has jointly fresh openings. Its admitted own
bag also earns the output-label licence from its physical freshness and
distinct made identities; that licence is not an additional hypothesis.
Consequently own admission is exactly the existing annotated round at the
one shared packet state and finite program.

For nonempty families of well-shaped unguarded native firings, this joins
the native family/concurrent execution comparison. It does not include the
guarded query profile or solver-result frame interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.PacketOwnRounds

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open RuleSyntax RuleSyntax.JointFirings
open NativePacketStep (Ports packetAction)
open NativePacketRounds (source label member memberList program image useTag)
open RuleSyntax.StepWeb

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}

omit [DecidableEq O] in
theorem program_finite {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :
    (program members).Finite := by
  have finite := Set.finite_range (fun index : Fin members.length =>
    NativePacketStep.rule members[index] (useTag index))
  exact finite.subset (by
    rintro rule ⟨index, rfl⟩
    exact ⟨index, rfl⟩)

omit [DecidableEq O] in
theorem member_positive {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (index : Fin members.length) : Scope.Positive (member members index).rule := by
  refine ⟨?_, rfl⟩
  intro check inside
  cases inside

omit [DecidableEq O] in
theorem member_collect {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (index : Fin members.length) :
    (member members index).rule.collect.length = (member members index).seen.length := rfl

/-- Jointly distinct made ports give distinct producing owners even if two
positions contain equal native firing values. -/
theorem made_disjoint_of_own {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (own : (bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (memberList members)).AdmitsOwn
        (OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (source members))
    (first second : Fin members.length) (different : first ≠ second) :
    (members[first].selection.made.map (Sum.inl : O → Ports O)).Disjoint
      (members[second].selection.made.map Sum.inl) := by
  have nodup : ((List.finRange members.length).flatMap fun index =>
      members[index].selection.made.map (Sum.inl : O → Ports O)).Nodup := by
    simpa only [bagOf, JointFirings.Bag.selection, memberList, List.flatMap_map,
      member, NativePacketStep.selection] using own.1.2.2.1
  have pairs := (List.nodup_flatMap.mp nodup).2
  have ordered (i j : Fin members.length) (before : i.val < j.val) :
      (members[i].selection.made.map (Sum.inl : O → Ports O)).Disjoint
        (members[j].selection.made.map Sum.inl) := by
    have actual := List.pairwise_iff_getElem.mp pairs i.val j.val
      (by simp) (by simp) before
    simpa using actual
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne different) with before | after
  · exact ordered first second before
  · exact (ordered second first after).symm

theorem owner_of_own {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (own : (bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (memberList members)).AdmitsOwn
        (OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (source members))
    (index : Fin members.length) (occurrence : O) (inside : occurrence ∈ members[index].selection.made) :
    NativePacketRounds.owner members occurrence = some index := by
  apply NativePacketRounds.owner_unique members occurrence index inside
  intro other also
  by_contra different
  exact made_disjoint_of_own members own other index different
    (List.mem_map.mpr ⟨occurrence, also, rfl⟩) (List.mem_map.mpr ⟨occurrence, inside, rfl⟩)

/-- The own-bag's actual formation/enabling laws earn the output-label
licence used by the existing two-presentation theorem. -/
theorem keeps_of_own {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (own : (bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (memberList members)).AdmitsOwn
        (OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (source members))
    (index : Fin members.length) :
    Rounds.KeepsLabels (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (label members) (member members index) := by
  rw [Rounds.KeepsLabels, NativePacketRounds.member_opened]
  change (members[index].selection.made.map Sum.inl).map (label members) =
    members[index].selection.made.map (NativePacketStep.outputRow members[index] (useTag index))
  rw [List.map_map]
  apply List.map_congr_left
  intro occurrence inside
  have listed : member members index ∈ memberList members :=
    List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩
  have made : Sum.inl occurrence ∈
      (bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
        (memberList members)).selection.made := by
    exact List.mem_flatMap.mpr ⟨member members index, listed,
      List.mem_map.mpr ⟨occurrence, inside, rfl⟩⟩
  have notOld : occurrence ∉ s.state.present := by
    intro old
    exact Finset.disjoint_left.mp own.2.1.fresh (List.mem_toFinset.mpr made)
      (by simpa [source, OneFrame.embed, NativePacketStep.configuration, NativePacketStep.present] using old)
  simp only [Function.comp_apply, label, if_neg notOld, owner_of_own members own index occurrence inside]

theorem own_iff_round {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :
    (bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (memberList members)).AdmitsOwn
        (OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (source members) ↔
      AnnotatedRuns.Round (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (label members)
        (NativePacketStep.configuration s 0) (image members) := by
  constructor
  · intro own
    apply Rounds.round_image_of_positive _ own
    · intro selected inside
      obtain ⟨index, _, rfl⟩ := List.mem_map.mp inside
      exact keeps_of_own members own index
    · intro selected inside
      obtain ⟨index, _, rfl⟩ := List.mem_map.mp inside
      exact member_positive members index
  · intro round
    exact (Rounds.admitsOwn_of_round _ round (PacketJointFreshness.bag_fresh members)
      (fun selected inside => by
        obtain ⟨index, _, rfl⟩ := List.mem_map.mp inside
        exact member_collect members index)).1

section Native

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

theorem own_iff_native_family {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (nonempty : members ≠ []) (shapes : ∀ index : Fin members.length, native.Shapes members[index].toNative)
    (noChecks : ∀ index : Fin members.length, members[index].rule.checks = [])
    (noQueries : ∀ index : Fin members.length, members[index].patterns = []) :
    (bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (memberList members)).AdmitsOwn
        (OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (source members) ↔
      NativeIterated.FamilyClear s members :=
  (own_iff_round members).trans (NativePacketRounds.round_iff members nonempty shapes noChecks noQueries)

theorem own_iff_native_concurrent {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (nonempty : members ≠ []) (shapes : ∀ index : Fin members.length, native.Shapes members[index].toNative)
    (noChecks : ∀ index : Fin members.length, members[index].rule.checks = [])
    (noQueries : ∀ index : Fin members.length, members[index].patterns = []) :
    (bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (memberList members)).AdmitsOwn
        (OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (source members) ↔
      ∃ last, NativeConcurrent.Concurrent s (members : Multiset (LiveFiring s)) last :=
  (own_iff_round members).trans
    (NativePacketRounds.round_iff_concurrent members nonempty shapes noChecks noQueries)

theorem native_every_order_of_own {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (nonempty : members ≠ []) (shapes : ∀ index : Fin members.length, native.Shapes members[index].toNative)
    (noChecks : ∀ index : Fin members.length, members[index].rule.checks = [])
    (noQueries : ∀ index : Fin members.length, members[index].patterns = [])
    (own : (bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (memberList members)).AdmitsOwn
        (OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (source members))
    {order : List (LiveFiring s)} (permutes : order.Perm members) :
    ∃ last, ∃ witness : NativeRoundExecution.Witness s order last,
      witness.toRun.last = last ∧ witness.toRun.word.length = members.length ∧
        witness.toRun.word.map (fun event => event.2.selection) = order.map (fun event => event.selection) :=
  NativePacketRounds.native_every_order members nonempty shapes noChecks noQueries
    ((own_iff_round members).mp own) permutes

end Native

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.PacketOwnRounds
