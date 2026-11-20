import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricBagTransport

/-!
# Duplicate and renamed ambient presentations preserve symmetric CMR admission

Profile: one first-order occurrence-bag store, ambient rule sets, jointly fresh
finite bags, own-information guards after tells. Both directions transport
actual bags; equality of offered classes alone is not used as an existence
claim. Choosing a source presentation is noncomputable, not native code.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} {O : Type}
  {P P' : Program (Terms (Term signature))} {a : PUnit}
  {x : (ext (FirstOrder.action signature)).Ext a}

def reprogramMember (m : Member O (ext (FirstOrder.action signature)) P x) (member : m.rule ∈ P') :
    Member O (ext (FirstOrder.action signature)) P' x :=
  ⟨m.rule, member, m.opening, m.selection, m.seen⟩

def pullMember (names : Names signature.vars)
    (m : Member O (ext (FirstOrder.action signature)) P' x)
    (rule : Rule (Terms (Term signature))) (member : rule ∈ P) :
    Member O (ext (FirstOrder.action signature)) P x :=
  ⟨rule, member, fun v => m.opening (names.forward v), m.selection, m.seen⟩

def coordinates_reprogram (m : Member O (ext (FirstOrder.action signature)) P x)
    (member : m.rule ∈ P') :
    MemberCoordinates m (reprogramMember m member) :=
  ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, id, id,
    fun _ _ values => values, fun _ _ values => values⟩

def coordinates_pull (names : Names signature.vars)
    (m : Member O (ext (FirstOrder.action signature)) P' x)
    (rule : Rule (Terms (Term signature))) (member : rule ∈ P)
    (same : m.rule = renameRule names.forward rule) :
    MemberCoordinates m (pullMember names m rule member) := by
  apply MemberCoordinates.symm
  apply coordinates_of_renaming names (pullMember names m rule member) m same rfl rfl
  intro term _
  let forward : Subst signature := fun v => .var (names.forward v)
  change m.opening.applyTerm (forward.applyTerm term) = (m.opening.comp forward).applyTerm term
  exact (Subst.applyTerm_comp _ _ _).symm

theorem alias_member (names : Names signature.vars)
    (m : Member O (ext (FirstOrder.action signature)) (P ∪ renamedProgram names P) x) :
    ∃ n : Member O (ext (FirstOrder.action signature)) P x,
      Nonempty (MemberCoordinates m n) ∧ identity.key m.firing = identity.key n.firing := by
  rcases m.member with original | copy
  · exact ⟨reprogramMember m original, ⟨coordinates_reprogram m original⟩, rfl⟩
  · obtain ⟨rule, member, same⟩ := copy
    exact ⟨pullMember names m rule member,
      ⟨coordinates_pull names m rule member same.symm⟩,
      pullFiring_key names m.firing rule member same.symm⟩

noncomputable def forgetCopies (names : Names signature.vars)
    (bag : Bag O (ext (FirstOrder.action signature)) (P ∪ renamedProgram names P) a) :
    Bag O (ext (FirstOrder.action signature)) P a :=
  ⟨bag.ext, bag.members.map fun m => Classical.choose (alias_member names m)⟩

theorem forgetCopies_coordinates (names : Names signature.vars)
    (bag : Bag O (ext (FirstOrder.action signature)) (P ∪ renamedProgram names P) a) :
    List.Forall₂ (fun m n => Nonempty (MemberCoordinates m n)) bag.members
      (forgetCopies names bag).members := by
  apply List.forall₂_map_right_iff.mpr
  exact List.forall₂_same.mpr fun m _ => (Classical.choose_spec (alias_member names m)).1

theorem forgetCopies_keys (names : Names signature.vars)
    (bag : Bag O (ext (FirstOrder.action signature)) (P ∪ renamedProgram names P) a) :
    (forgetCopies names bag).keysBy identity = bag.keysBy identity := by
  change (bag.members.map _).map (fun m : Member O (ext (FirstOrder.action signature)) P bag.ext =>
    identity.key m.firing) = bag.members.map _
  rw [List.map_map]
  exact List.map_congr_left fun m _ => (Classical.choose_spec (alias_member names m)).2.symm

def embedBag (bag : Bag O (ext (FirstOrder.action signature)) P a)
    (inclusion : ∀ rule ∈ P, rule ∈ P') : Bag O (ext (FirstOrder.action signature)) P' a :=
  ⟨bag.ext, bag.members.map fun m => reprogramMember m (inclusion m.rule m.member)⟩

theorem embedBag_coordinates (bag : Bag O (ext (FirstOrder.action signature)) P a)
    (inclusion : ∀ rule ∈ P, rule ∈ P') :
    List.Forall₂ (fun m n => Nonempty (MemberCoordinates m n)) bag.members
      (embedBag bag inclusion).members := by
  apply List.forall₂_map_right_iff.mpr
  exact List.forall₂_same.mpr fun m _ => ⟨coordinates_reprogram m (inclusion m.rule m.member)⟩

theorem embedBag_keys (bag : Bag O (ext (FirstOrder.action signature)) P a)
    (inclusion : ∀ rule ∈ P, rule ∈ P') :
    (embedBag bag inclusion).keysBy identity = bag.keysBy identity := by
  dsimp only [embedBag, Bag.keysBy]
  rw [List.map_map]
  rfl

variable [DecidableEq O] {s : State (Terms (Term signature)) O}

theorem forgetCopies_every_unique (names : Names signature.vars)
    (bag : Bag O (ext (FirstOrder.action signature)) (P ∪ renamedProgram names P) s.frame)
    (region : Class signature O → Prop) :
    (bag.AdmitsEveryBy (frames (FirstOrder.action signature)) s identity region ↔
      (forgetCopies names bag).AdmitsEveryBy (frames (FirstOrder.action signature)) s identity region) ∧
    (bag.AdmitsUniqueBy (frames (FirstOrder.action signature)) s identity region ↔
      (forgetCopies names bag).AdmitsUniqueBy (frames (FirstOrder.action signature)) s identity region) :=
  coordinates_every_unique (forgetCopies_coordinates names bag) (forgetCopies_keys names bag).symm
    (offered_with_renamed_copies names s) region

theorem copies_exist_every_unique (names : Names signature.vars) (region : Class signature O → Prop) :
    ((∃ bag : Bag O (ext (FirstOrder.action signature)) P s.frame,
        bag.AdmitsEveryBy (frames (FirstOrder.action signature)) s identity region) ↔
      ∃ bag : Bag O (ext (FirstOrder.action signature)) (P ∪ renamedProgram names P) s.frame,
        bag.AdmitsEveryBy (frames (FirstOrder.action signature)) s identity region) ∧
    ((∃ bag : Bag O (ext (FirstOrder.action signature)) P s.frame,
        bag.AdmitsUniqueBy (frames (FirstOrder.action signature)) s identity region) ↔
      ∃ bag : Bag O (ext (FirstOrder.action signature)) (P ∪ renamedProgram names P) s.frame,
        bag.AdmitsUniqueBy (frames (FirstOrder.action signature)) s identity region) := by
  have inclusion : ∀ rule ∈ P, rule ∈ P ∪ renamedProgram names P := fun _ h => Or.inl h
  have embedded := fun bag => coordinates_every_unique (embedBag_coordinates bag inclusion)
    (embedBag_keys bag inclusion).symm (fun key => (offered_with_renamed_copies names s key).symm) region
  constructor
  · constructor
    · rintro ⟨bag, admitted⟩
      exact ⟨embedBag bag inclusion, (embedded bag).1.mp admitted⟩
    · rintro ⟨bag, admitted⟩
      exact ⟨forgetCopies names bag, (forgetCopies_every_unique names bag region).1.mp admitted⟩
  · constructor
    · rintro ⟨bag, admitted⟩
      exact ⟨embedBag bag inclusion, (embedded bag).2.mp admitted⟩
    · rintro ⟨bag, admitted⟩
      exact ⟨forgetCopies names bag, (forgetCopies_every_unique names bag region).2.mp admitted⟩

theorem duplicate_every_unique (bag : Bag O (ext (FirstOrder.action signature)) P s.frame)
    (region : Class signature O → Prop) :
    (bag.AdmitsEveryBy (frames (FirstOrder.action signature)) s identity region ↔
      (embedBag bag (P' := P ∪ P) (fun _ h => Or.inl h)).AdmitsEveryBy
        (frames (FirstOrder.action signature)) s identity region) ∧
    (bag.AdmitsUniqueBy (frames (FirstOrder.action signature)) s identity region ↔
      (embedBag bag (P' := P ∪ P) (fun _ h => Or.inl h)).AdmitsUniqueBy
        (frames (FirstOrder.action signature)) s identity region) :=
  coordinates_every_unique (P' := P ∪ P)
    (embedBag_coordinates (P' := P ∪ P) bag (fun _ h => Or.inl h))
    (embedBag_keys (P' := P ∪ P) bag (fun _ h => Or.inl h)).symm
    (fun key => (offered_duplicate (P := P) s key).symm) region

theorem renamed_exist_every_unique (names : Names signature.vars) (region : Class signature O → Prop) :
    ((∃ bag : Bag O (ext (FirstOrder.action signature)) P s.frame,
        bag.AdmitsEveryBy (frames (FirstOrder.action signature)) s identity region) ↔
      ∃ bag : Bag O (ext (FirstOrder.action signature)) (renamedProgram names P) s.frame,
        bag.AdmitsEveryBy (frames (FirstOrder.action signature)) s identity region) ∧
    ((∃ bag : Bag O (ext (FirstOrder.action signature)) P s.frame,
        bag.AdmitsUniqueBy (frames (FirstOrder.action signature)) s identity region) ↔
      ∃ bag : Bag O (ext (FirstOrder.action signature)) (renamedProgram names P) s.frame,
        bag.AdmitsUniqueBy (frames (FirstOrder.action signature)) s identity region) := by
  have inclusion : ∀ rule ∈ renamedProgram names P, rule ∈ P ∪ renamedProgram names P := fun _ h => Or.inr h
  have embedded := fun bag => coordinates_every_unique (embedBag_coordinates bag inclusion)
    (embedBag_keys bag inclusion).symm
    (fun key => (offered_renamed names s key).trans (offered_with_renamed_copies names s key).symm) region
  constructor
  · constructor
    · rintro ⟨bag, admitted⟩
      exact ⟨renameBag names bag, (renameBag_every_unique names bag region).1.mp admitted⟩
    · rintro ⟨bag, admitted⟩
      exact (copies_exist_every_unique names region).1.mpr
        ⟨embedBag bag inclusion, (embedded bag).1.mp admitted⟩
  · constructor
    · rintro ⟨bag, admitted⟩
      exact ⟨renameBag names bag, (renameBag_every_unique names bag region).2.mp admitted⟩
    · rintro ⟨bag, admitted⟩
      exact (copies_exist_every_unique names region).2.mpr
        ⟨embedBag bag inclusion, (embedded bag).2.mp admitted⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
