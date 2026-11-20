import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.MemberCoordinates

/-!
# Local-coordinate transport of actual jointly fresh CMR bags

Profile: one first-order occurrence-bag store, ambient programs, finite bags,
own-information guards after tells. Local valuation correspondence preserves
joint freshness. Equal opened syntax then gives actual admission and results,
not only equality of match keys.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} {O : Type}
  {P P' : Program (Terms (Term signature))}
  {s : State (Terms (Term signature)) O}
  {x : (ext (FirstOrder.action signature)).Ext s.frame}

theorem MemberCoordinates.own_eq
    {first : Member O (ext (FirstOrder.action signature)) P x}
    {second : Member O (ext (FirstOrder.action signature)) P' x}
    (c : MemberCoordinates first second) :
    first.own (frames (FirstOrder.action signature)) s =
      second.own (frames (FirstOrder.action signature)) s := by
  unfold Member.own
  rw [c.opened]
  simp only [Firing.matching, Member.firing, c.selection, Firing.row]

theorem MemberCoordinates.holds_iff
    {first : Member O (ext (FirstOrder.action signature)) P x}
    {second : Member O (ext (FirstOrder.action signature)) P' x}
    (c : MemberCoordinates first second) (assignment : Subst signature) :
    first.firing.Holds (frames (FirstOrder.action signature)) s (b := PUnit.unit) assignment ↔
      second.firing.Holds (frames (FirstOrder.action signature)) s (b := PUnit.unit) assignment := by
  unfold Firing.Holds
  have row : first.firing.row (frames (FirstOrder.action signature)) s =
      second.firing.row (frames (FirstOrder.action signature)) s := rfl
  rw [c.opened, c.collect, row]
  simp only [Member.firing, c.seen]

def MemberArity (m : Member O (ext (FirstOrder.action signature)) P x) : Prop :=
  m.rule.body.take.length = m.selection.taken.length ∧
    m.rule.body.read.length = m.selection.read.length ∧
    m.rule.body.produce.length = m.selection.made.length ∧
    m.rule.collect.length = m.seen.length

theorem MemberCoordinates.arity_iff
    {first : Member O (ext (FirstOrder.action signature)) P x}
    {second : Member O (ext (FirstOrder.action signature)) P' x}
    (c : MemberCoordinates first second) : MemberArity first ↔ MemberArity second := by
  unfold MemberArity
  rw [c.arities.1, c.arities.2.1, c.arities.2.2.1, c.arities.2.2.2, c.selection, c.seen]

theorem coordinates_all_iff
    {first : List (Member O (ext (FirstOrder.action signature)) P x)}
    {second : List (Member O (ext (FirstOrder.action signature)) P' x)}
    (related : List.Forall₂ (fun m n => Nonempty (MemberCoordinates m n)) first second)
    (A : Member O (ext (FirstOrder.action signature)) P x → Prop)
    (B : Member O (ext (FirstOrder.action signature)) P' x → Prop)
    (aligned : ∀ m n, MemberCoordinates m n → (A m ↔ B n)) :
    (∀ m ∈ first, A m) ↔ (∀ n ∈ second, B n) := by
  induction related with
  | nil => simp
  | @cons m n rest later head tail ih =>
    obtain ⟨c⟩ := head
    simpa only [List.forall_mem_cons] using and_congr (aligned m n c) ih

theorem coordinates_data
    {first : List (Member O (ext (FirstOrder.action signature)) P x)}
    {second : List (Member O (ext (FirstOrder.action signature)) P' x)}
    (related : List.Forall₂ (fun m n => Nonempty (MemberCoordinates m n)) first second) :
    (⟨x, first⟩ : Bag O (ext (FirstOrder.action signature)) P s.frame).selection =
        (⟨x, second⟩ : Bag O (ext (FirstOrder.action signature)) P' s.frame).selection ∧
      (⟨x, first⟩ : Bag O (ext (FirstOrder.action signature)) P s.frame).information
          (frames (FirstOrder.action signature)) s =
        (⟨x, second⟩ : Bag O (ext (FirstOrder.action signature)) P' s.frame).information
          (frames (FirstOrder.action signature)) s ∧
      (⟨x, first⟩ : Bag O (ext (FirstOrder.action signature)) P s.frame).produce
          (frames (FirstOrder.action signature)) =
        (⟨x, second⟩ : Bag O (ext (FirstOrder.action signature)) P' s.frame).produce
          (frames (FirstOrder.action signature)) := by
  have takes : first.flatMap (fun m => m.selection.taken) = second.flatMap (fun m => m.selection.taken) := by
    induction related with
    | nil => rfl
    | cons head _ ih => obtain ⟨c⟩ := head; simp only [List.flatMap_cons, c.selection, ih]
  have reads : first.flatMap (fun m => m.selection.read) = second.flatMap (fun m => m.selection.read) := by
    clear takes
    induction related with
    | nil => rfl
    | cons head _ ih => obtain ⟨c⟩ := head; simp only [List.flatMap_cons, c.selection, ih]
  have made : first.flatMap (fun m => m.selection.made) = second.flatMap (fun m => m.selection.made) := by
    clear takes reads
    induction related with
    | nil => rfl
    | cons head _ ih => obtain ⟨c⟩ := head; simp only [List.flatMap_cons, c.selection, ih]
  have own : first.flatMap (fun m => m.own (frames (FirstOrder.action signature)) s) =
      second.flatMap (fun m => m.own (frames (FirstOrder.action signature)) s) := by
    clear takes reads made
    induction related with
    | nil => rfl
    | cons head _ ih => obtain ⟨c⟩ := head; simp only [List.flatMap_cons, c.own_eq, ih]
  have produces : first.flatMap (fun m => (m.firing.opened (frames (FirstOrder.action signature))).produce) =
      second.flatMap (fun m => (m.firing.opened (frames (FirstOrder.action signature))).produce) := by
    clear takes reads made own
    induction related with
    | nil => rfl
    | cons head _ ih => obtain ⟨c⟩ := head; simp only [List.flatMap_cons, c.opened, ih]
  exact ⟨by simp only [Bag.selection, takes, reads, made],
    by simp only [Bag.information, own], produces⟩

variable [DecidableEq O]

theorem coordinates_admission_result
    {first : List (Member O (ext (FirstOrder.action signature)) P x)}
    {second : List (Member O (ext (FirstOrder.action signature)) P' x)}
    (related : List.Forall₂ (fun m n => Nonempty (MemberCoordinates m n)) first second) :
    ((⟨x, first⟩ : Bag O (ext (FirstOrder.action signature)) P s.frame).AdmitsOwn
        (frames (FirstOrder.action signature)) s ↔
      (⟨x, second⟩ : Bag O (ext (FirstOrder.action signature)) P' s.frame).AdmitsOwn
        (frames (FirstOrder.action signature)) s) ∧
    (⟨x, first⟩ : Bag O (ext (FirstOrder.action signature)) P s.frame).result
        (frames (FirstOrder.action signature)) s =
      (⟨x, second⟩ : Bag O (ext (FirstOrder.action signature)) P' s.frame).result
        (frames (FirstOrder.action signature)) s := by
  obtain ⟨selection, information, produce⟩ := coordinates_data (s := s) related
  have fresh : (⟨x, first⟩ : Bag O (ext (FirstOrder.action signature)) P s.frame).Fresh
      (frames (FirstOrder.action signature)) s ↔
      (⟨x, second⟩ : Bag O (ext (FirstOrder.action signature)) P' s.frame).Fresh
        (frames (FirstOrder.action signature)) s := by
    constructor <;> intro h b g <;> cases b
    · exact (realized_coordinates related _).mp (h PUnit.unit g)
    · exact (realized_coordinates related _).mpr (h PUnit.unit g)
  have arities := coordinates_all_iff related MemberArity MemberArity
    (fun _ _ c => c.arity_iff)
  have guards := coordinates_all_iff related
    (fun m => (frames (FirstOrder.action signature)).Entails
      (m.firing.information (frames (FirstOrder.action signature)) s)
      (fun b assignment => m.firing.Holds (frames (FirstOrder.action signature)) s (b := b) assignment))
    (fun m => (frames (FirstOrder.action signature)).Entails
      (m.firing.information (frames (FirstOrder.action signature)) s)
      (fun b assignment => m.firing.Holds (frames (FirstOrder.action signature)) s (b := b) assignment))
    (fun m n c => by
      have info : m.firing.information (frames (FirstOrder.action signature)) s =
          n.firing.information (frames (FirstOrder.action signature)) s := by
        rw [Member.information_eq, Member.information_eq, c.own_eq]
      constructor <;> intro h b assignment solved <;> cases b
      · exact (c.holds_iff assignment).mp (h PUnit.unit assignment (info ▸ solved))
      · exact (c.holds_iff assignment).mpr (h PUnit.unit assignment (info.symm ▸ solved)))
  refine ⟨?_, ?_⟩
  · unfold Bag.AdmitsOwn Bag.Fits
    rw [fresh, selection, information]
    exact and_congr (and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => arities) (and_congr_right fun _ => and_congr_right fun _ => guards)
  · unfold Bag.result
    rw [selection, information, produce]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
