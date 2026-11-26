import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Bags
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Renaming

/-!
# Occurrence equivariance of the joint step

Renaming transports an entire bag, including each member's claimed census.
The members use the same frame openings and the same rules. Freshness,
admission, and the atomic result commute with the renaming.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.OccurrenceRenaming

open Interface (Frames)

universe uO uT uH uOcc uE

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

def renameMember (π : Equiv.Perm O) {a : Obj} {extension : E.Ext a}
    (m : Member O E P extension) : Member O E P extension :=
  Member.ofFiring (Equivalence.renameFiring π m.firing)

def rename (π : Equiv.Perm O) {a : Obj} (bag : Bag O E P a) : Bag O E P a :=
  ⟨bag.ext, bag.members.map (renameMember π)⟩

private theorem realized_rename (X : Frames Tm Hom) (π : Equiv.Perm O) {a b : Obj}
    {extension : E.Ext a} (members : List (Member O E P extension))
    (property : Hom (E.target extension) b → Prop) :
    Realized X b (members.map (renameMember π)) property ↔ Realized X b members property := by
  induction members generalizing property with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.map_cons, Realized]
      exact forall_congr' fun _ => ih _

theorem fresh_rename (X : Frames Tm Hom) (π : Equiv.Perm O) (s : State Tm O)
    (bag : Bag O E P s.frame) :
    (rename π bag).Fresh X (Equivalence.renameState π s) ↔ bag.Fresh X s := by
  constructor
  · intro ready b g
    have original := (realized_rename X π bag.members _).mp (ready b g)
    exact Realized.mono X bag.members (fun u agreed t mentioned =>
      agreed t ((Equivalence.mentions_renameState π s t).mpr mentioned)) original
  · intro ready b g
    apply (realized_rename X π bag.members _).mpr
    exact Realized.mono X bag.members (fun u agreed t mentioned =>
      agreed t ((Equivalence.mentions_renameState π s t).mp mentioned)) (ready b g)

private theorem selection_rename (π : Equiv.Perm O) {a : Obj} (bag : Bag O E P a) :
    (rename π bag).selection =
      ⟨bag.selection.taken.map π, bag.selection.read.map π, bag.selection.made.map π⟩ := by
  simp only [rename, Bag.selection, List.flatMap_map, List.map_flatMap]
  rfl

private theorem own_rename (X : Frames Tm Hom) (π : Equiv.Perm O) [DecidableEq O]
    (s : State Tm O) {extension : E.Ext s.frame} (m : Member O E P extension) :
    (renameMember π m).own X (Equivalence.renameState π s) = m.own X s := by
  have equal := Equivalence.information_renameFiring X π m.firing
  have left := Member.information_eq X (Equivalence.renameState π s) (renameMember π m)
  have right := Member.information_eq X s m
  exact List.append_cancel_left (left.symm.trans (equal.trans right))

private theorem information_rename (X : Frames Tm Hom) (π : Equiv.Perm O) [DecidableEq O]
    (s : State Tm O) (bag : Bag O E P s.frame) :
    (rename π bag).information X (Equivalence.renameState π s) = bag.information X s := by
  simp only [Bag.information, rename, Equivalence.renameState, List.flatMap_map]
  exact congrArg (List.append (X.applyStore (E.weaken bag.ext) s.knowledge))
    (List.flatMap_congr fun m _ => own_rename X π s m)

private theorem fits_rename (X : Frames Tm Hom) (π : Equiv.Perm O)
    (s : State Tm O) (bag : Bag O E P s.frame) :
    (rename π bag).Fits X (Equivalence.renameState π s) ↔ bag.Fits X s := by
  unfold Bag.Fits
  rw [fresh_rename]
  erw [selection_rename π bag]
  simp only [List.nodup_map_iff π.injective]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro fits m inside
    have mapped := fits (renameMember π m) (List.mem_map.mpr ⟨m, inside, rfl⟩)
    simpa [renameMember, Member.ofFiring, Equivalence.renameFiring] using mapped
  · intro fits m inside
    have member : m ∈ bag.members.map (renameMember π) := inside
    obtain ⟨old, oldIn, rfl⟩ := List.mem_map.mp member
    simpa [renameMember, Member.ofFiring, Equivalence.renameFiring] using fits old oldIn

private theorem holds_rename (X : Frames Tm Hom) (π : Equiv.Perm O) [DecidableEq O]
    (s : State Tm O) (bag : Bag O E P s.frame) {b : Obj} (σ : Hom (E.target bag.ext) b) :
    (rename π bag).Holds X (Equivalence.renameState π s) σ ↔ bag.Holds X s σ := by
  constructor
  · intro holds m member
    apply (Equivalence.holds_renameFiring X π m.firing σ).mp
    exact holds (renameMember π m) (List.mem_map.mpr ⟨m, member, rfl⟩)
  · intro holds m member
    have chosen : m ∈ bag.members.map (renameMember π) := member
    obtain ⟨old, oldIn, rfl⟩ := List.mem_map.mp chosen
    exact (Equivalence.holds_renameFiring X π old.firing σ).mpr (holds old oldIn)

theorem admits_rename (X : Frames Tm Hom) (π : Equiv.Perm O) [DecidableEq O]
    (s : State Tm O) (bag : Bag O E P s.frame) :
    (rename π bag).Admits X (Equivalence.renameState π s) ↔ bag.Admits X s := by
  unfold Bag.Admits
  rw [fits_rename, information_rename]
  refine and_congr_right fun _ => and_congr ?_ (and_congr_right fun _ => ?_)
  · erw [selection_rename π bag]
    exact Equivalence.enabled_renameSelection π s.present bag.selection
  · exact forall₂_congr fun _ σ => imp_congr_right fun _ => holds_rename X π s bag σ

theorem result_rename (X : Frames Tm Hom) (π : Equiv.Perm O) [DecidableEq O]
    (s : State Tm O) (bag : Bag O E P s.frame) :
    (rename π bag).result X (Equivalence.renameState π s) =
      Equivalence.renameState π (bag.result X s) := by
  have produced : (rename π bag).produce X = bag.produce X := by
    simp only [Bag.produce, rename, List.flatMap_map]
    rfl
  unfold Bag.result
  rw [information_rename]
  erw [selection_rename π bag, produced]
  have rows := Equivalence.fire_rename π s.present bag.selection
  simp only [Equivalence.renameState, rows]
  congr 1
  funext o
  exact Equivalence.relabel_rename (Tm := Tm) π
    (fun o => X.act (E.weaken bag.ext) (s.label o)) bag.selection.made (Bag.produce X bag) o

#print axioms admits_rename
#print axioms result_rename

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.OccurrenceRenaming
