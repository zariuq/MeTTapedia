import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.BagCoordinates
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricOffers

/-!
# Symmetric CMR completeness and uniqueness under rule re-presentation

Profile: one first-order occurrence-bag store, ambient rule sets, jointly fresh
finite bags, guards after each member's own tells. Local renaming changes
neither admission nor completeness. Ordered and named-origin profiles remain
separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} {O : Type} [DecidableEq O]
  {P P' : Program (Terms (Term signature))} {s : State (Terms (Term signature)) O}

theorem completeBy_iff_offers (bag : Bag O (ext (FirstOrder.action signature)) P s.frame)
    (region : Class signature O → Prop) :
    bag.CompleteBy (frames (FirstOrder.action signature)) s identity region ↔
      ∀ key, offered P s key → region key → key ∈ bag.keysBy identity := by
  constructor
  · intro complete key ⟨f, admitted, same⟩ inRegion
    subst key
    exact complete f inRegion admitted
  · intro complete f inRegion admitted
    exact complete (identity.key f) ⟨f, admitted, rfl⟩ inRegion

theorem coordinates_every_unique
    {x : (ext (FirstOrder.action signature)).Ext s.frame}
    {first : List (Member O (ext (FirstOrder.action signature)) P x)}
    {second : List (Member O (ext (FirstOrder.action signature)) P' x)}
    (related : List.Forall₂ (fun m n => Nonempty (MemberCoordinates m n)) first second)
    (keys : first.map (fun m => identity.key m.firing) = second.map (fun m => identity.key m.firing))
    (offers : ∀ key, offered P s key ↔ offered P' s key) (region : Class signature O → Prop) :
    ((⟨x, first⟩ : Bag O (ext (FirstOrder.action signature)) P s.frame).AdmitsEveryBy
        (frames (FirstOrder.action signature)) s identity region ↔
      (⟨x, second⟩ : Bag O (ext (FirstOrder.action signature)) P' s.frame).AdmitsEveryBy
        (frames (FirstOrder.action signature)) s identity region) ∧
    ((⟨x, first⟩ : Bag O (ext (FirstOrder.action signature)) P s.frame).AdmitsUniqueBy
        (frames (FirstOrder.action signature)) s identity region ↔
      (⟨x, second⟩ : Bag O (ext (FirstOrder.action signature)) P' s.frame).AdmitsUniqueBy
        (frames (FirstOrder.action signature)) s identity region) := by
  have completeness :
      (⟨x, first⟩ : Bag O (ext (FirstOrder.action signature)) P s.frame).CompleteBy
        (frames (FirstOrder.action signature)) s identity region ↔
      (⟨x, second⟩ : Bag O (ext (FirstOrder.action signature)) P' s.frame).CompleteBy
        (frames (FirstOrder.action signature)) s identity region := by
    rw [completeBy_iff_offers, completeBy_iff_offers]
    simp only [Bag.keysBy, keys]
    exact forall_congr' fun key => imp_congr (offers key) Iff.rfl
  have every :
      (⟨x, first⟩ : Bag O (ext (FirstOrder.action signature)) P s.frame).AdmitsEveryBy
        (frames (FirstOrder.action signature)) s identity region ↔
      (⟨x, second⟩ : Bag O (ext (FirstOrder.action signature)) P' s.frame).AdmitsEveryBy
        (frames (FirstOrder.action signature)) s identity region := by
    unfold Bag.AdmitsEveryBy
    rw [(coordinates_admission_result related).1, completeness]
    simp only [Bag.keysBy, Bag.DistinctBy, keys]
    rfl
  exact ⟨every, and_congr every (by rw [related.length_eq])⟩

def renameMember (names : Names signature.vars) {a : PUnit}
    {x : (ext (FirstOrder.action signature)).Ext a}
    (m : Member O (ext (FirstOrder.action signature)) P x)
    (member : renameRule names.forward m.rule ∈ P') :
    Member O (ext (FirstOrder.action signature)) P' x :=
  ⟨renameRule names.forward m.rule, member, fun v => m.opening (names.backward v), m.selection, m.seen⟩

def renameBag (names : Names signature.vars)
    (bag : Bag O (ext (FirstOrder.action signature)) P s.frame) :
    Bag O (ext (FirstOrder.action signature)) (renamedProgram names P) s.frame :=
  ⟨bag.ext, bag.members.map fun m => renameMember (P' := renamedProgram names P)
    names m (renamedProgram_member names m.member)⟩

omit [DecidableEq O] in
theorem renameBag_coordinates (names : Names signature.vars)
    (bag : Bag O (ext (FirstOrder.action signature)) P s.frame) :
    List.Forall₂ (fun m n => Nonempty (MemberCoordinates m n)) bag.members
      (renameBag names bag).members := by
  change List.Forall₂ _ bag.members (bag.members.map _)
  apply List.forall₂_map_right_iff.mpr
  exact List.forall₂_same.mpr (fun m _ =>
    ⟨coordinates_rename (P' := renamedProgram names P) names m (renamedProgram_member names m.member)⟩)

omit [DecidableEq O] in
theorem renameBag_keys (names : Names signature.vars)
    (bag : Bag O (ext (FirstOrder.action signature)) P s.frame) :
    (renameBag names bag).keysBy identity = bag.keysBy identity := by
  dsimp only [renameBag, Bag.keysBy]
  rw [List.map_map]
  exact List.map_congr_left fun m _ => renameFiring_key (P' := renamedProgram names P)
    names m.firing (renamedProgram_member names m.member)

theorem renameBag_every_unique (names : Names signature.vars)
    (bag : Bag O (ext (FirstOrder.action signature)) P s.frame) (region : Class signature O → Prop) :
    (bag.AdmitsEveryBy (frames (FirstOrder.action signature)) s identity region ↔
      (renameBag names bag).AdmitsEveryBy (frames (FirstOrder.action signature)) s identity region) ∧
    (bag.AdmitsUniqueBy (frames (FirstOrder.action signature)) s identity region ↔
      (renameBag names bag).AdmitsUniqueBy (frames (FirstOrder.action signature)) s identity region) :=
  coordinates_every_unique (renameBag_coordinates names bag) (renameBag_keys names bag).symm
    (fun key => (offered_renamed names s key).symm) region

theorem renameBag_admission_result (names : Names signature.vars)
    (bag : Bag O (ext (FirstOrder.action signature)) P s.frame) :
    (bag.AdmitsOwn (frames (FirstOrder.action signature)) s ↔
      (renameBag names bag).AdmitsOwn (frames (FirstOrder.action signature)) s) ∧
    bag.result (frames (FirstOrder.action signature)) s =
      (renameBag names bag).result (frames (FirstOrder.action signature)) s :=
  coordinates_admission_result (renameBag_coordinates names bag)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
