import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketRounds

/-!
# Joint freshness of the actual indexed native packet family

The common source mentions only its base packet. Each indexed member's rule
terms mention that member's distinct use packet. Arbitrary assignments at
those packets, with arbitrary target frames, are assembled by the existing
raw patch construction. No model, admission or consistency assumption is
needed for this freshness statement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.PacketJointFreshness

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open TaggedAssignments (Object Substitution)
open NativePacketStep (Terms Ports packetAction)
open NativePacketRounds (source member memberList useTag patch patch_base patch_use)

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}

/-- Every mentioned term of the actual common source is at its base packet.
The present-label priority makes enabling assumptions unnecessary. -/
theorem source_location {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (term : Terms S O Γ sort) (mentioned : (source members).Mentions term) :
    NativePacketStep.location term = some (NativePacketStep.baseObject s 0) := by
  rcases mentioned with known | known | ⟨port,present,equal⟩
  · obtain ⟨equation,inside,rfl⟩ := List.mem_map.mp known
    exact (NativePacketStep.problem_locations _ _ equation inside).1
  · obtain ⟨equation,inside,rfl⟩ := List.mem_map.mp known
    exact (NativePacketStep.problem_locations _ _ equation inside).2
  · rw [← equal]
    cases port with
    | inl occurrence =>
        have old := (NativePacketStep.mem_present_inl s occurrence).mp present
        change NativePacketStep.location (NativePacketRounds.label members (.inl occurrence)) = _
        rw [NativePacketRounds.label_old members occurrence old]
        rfl
    | inr token => cases token; rfl

omit [DecidableEq O] in
/-- The actual nested realization binders can choose each remaining packet's
assignment independently. Already requested packets retain their full value,
including the chosen target frame. -/
theorem realized_indices {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (incoming : Substitution S) :
    ∀ (indices : List (Fin members.length)), indices.Nodup →
      ∀ requested : Fin members.length → Substitution S,
        RuleSyntax.JointFirings.Realized
          (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) PUnit.unit
          (indices.map (member members)) (fun joint =>
            joint (NativePacketStep.baseObject s 0) = incoming (NativePacketStep.baseObject s 0) ∧
              ∀ index, index ∉ indices →
                joint (NativePacketStep.useObject s (useTag index)) =
                  requested index (NativePacketStep.useObject s (useTag index)))
  | [], _, requested => by
      refine ⟨patch s members.length (incoming (NativePacketStep.baseObject s 0))
        (fun index => requested index (NativePacketStep.useObject s (useTag index))), ?_, ?_⟩
      · exact patch_base _ _ _ _
      · intro index _
        exact patch_use _ _ _ _ index
  | index :: rest, distinct, requested => by
      intro wanted
      have parts := List.nodup_cons.mp distinct
      have later := realized_indices members incoming rest parts.2 (Function.update requested index wanted)
      refine RuleSyntax.JointFirings.Realized.mono
        (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
        (rest.map (member members)) (fun joint data => ?_) later
      refine ⟨⟨data.1, ?_⟩, ?_⟩
      · intro other outside
        have different : other ≠ index := fun equal => outside (List.mem_cons.mpr (Or.inl equal))
        have absent : other ∉ rest := fun inside => outside (List.mem_cons_of_mem _ inside)
        simpa only [Function.update_of_ne different] using data.2 other absent
      · intro term inside
        have atUse : joint (NativePacketStep.useObject s (useTag index)) =
            wanted (NativePacketStep.useObject s (useTag index)) := by
          simpa only [Function.update_self] using data.2 index parts.1
        change ContextPackets.apply S joint (ContextPackets.apply S (TaggedAssignments.identity S) term) =
          ContextPackets.apply S wanted term
        rw [show ContextPackets.apply S (TaggedAssignments.identity S) term = term from
          (ContextPackets.action S (NativePacketStep.Rigid S O Γ sort)).apply_identity term]
        exact NativePacketStep.apply_at joint wanted _ atUse term
          (NativePacketStep.rule_location members[index] (useTag index) term inside)

/-- The actual indexed packet bag is jointly fresh at its one common source,
even when distinct positions carry equal native firing values. -/
theorem bag_fresh {s : NativeState S O Γ sort} (members : List (LiveFiring s)) :
    (RuleSyntax.JointFirings.bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)) (memberList members)).Fresh
      (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (source members) := by
  intro target incoming
  cases target
  have all := realized_indices members incoming (List.finRange members.length) (List.nodup_finRange _)
    (fun _ => TaggedAssignments.identity S)
  refine RuleSyntax.JointFirings.Realized.mono
    (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
    (memberList members) (fun joint data term mentioned => ?_) all
  change ContextPackets.apply S joint (ContextPackets.apply S (TaggedAssignments.identity S) term) =
    ContextPackets.apply S incoming term
  rw [show ContextPackets.apply S (TaggedAssignments.identity S) term = term from
    (ContextPackets.action S (NativePacketStep.Rigid S O Γ sort)).apply_identity term]
  exact NativePacketStep.apply_at joint incoming _ data.1 term (source_location members term mentioned)

/-- Equal native firing values retain separate positions and jointly fresh
use packets. This says nothing about whether their physical resources fit. -/
theorem equal_native_values_fresh {s : NativeState S O Γ sort} (firing : LiveFiring s) :
    (RuleSyntax.JointFirings.bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      (memberList [firing,firing])).Fresh
      (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort)))
        (source [firing,firing]) :=
  bag_fresh [firing,firing]

/-- Reusing the very same indexed packet twice cannot realize arbitrary
independent requests. The witness distinguishes internal packet target tags,
including when the captured name domain is empty. -/
theorem repeated_member_not_fresh {s : NativeState S O Γ sort} (members : List (LiveFiring s))
    (index : Fin members.length) :
    ¬ (RuleSyntax.JointFirings.bagOf (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))
      [member members index,member members index]).Fresh
      (RuleSyntax.OneFrame.frames (packetAction (S := S) (O := O) (Γ := Γ) (sort := sort))) (source members) := by
  intro fresh
  let point := NativePacketStep.useObject s (useTag index)
  let first := TaggedAssignments.single point (0,s.infoFrame) (generator s.infoFrame.arity)
  let second := TaggedAssignments.single point (1,s.infoFrame) (generator s.infoFrame.arity)
  obtain ⟨joint,⟨_,left⟩,right⟩ := fresh PUnit.unit (TaggedAssignments.identity S) first second
  let token : Terms S O Γ sort := NativePacketStep.captureRow s (useTag index)
  have present : token ∈ (member members index).rule.terms := by
    simp [token,member,NativePacketStep.rule,RuleSyntax.Rule.terms,NativePacketStep.body]
  have equal : ContextPackets.apply S first token = ContextPackets.apply S second token :=
    (left token present).symm.trans (right token present)
  have targets := congrArg (NativePacketStep.location (S := S) (O := O) (Γ := Γ) (sort := sort)) equal
  change some (first point).1 = some (second point).1 at targets
  rw [show first point = ⟨(0,s.infoFrame),generator s.infoFrame.arity⟩ from TaggedAssignments.single_at _ _ _,
    show second point = ⟨(1,s.infoFrame),generator s.infoFrame.arity⟩ from TaggedAssignments.single_at _ _ _] at targets
  have impossible : (0 : Nat) = 1 := congrArg Prod.fst (Option.some.inj targets)
  cases impossible

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.PacketJointFreshness
