import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricResources
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricBatchWords

/-!
# Resource alignment of symmetric first-order CMR bags

Profile: one occurrence-bag store, ambient programs, jointly fresh finite
bags, own-information guards after tells. Class alignment preserves all taken
occurrences and aligns fresh identities in output position order.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} {O : Type} [DecidableEq O]
  {P P' : Program (Terms (Term signature))}

theorem member_resource_totals (s : State (Terms (Term signature)) O)
    {x y : (ext (FirstOrder.action signature)).Ext s.frame}
    {first : List (Member O (ext (FirstOrder.action signature)) P x)}
    {second : List (Member O (ext (FirstOrder.action signature)) P' y)}
    (related : List.Forall₂ (fun m n => (presentation m.firing).key = (presentation n.firing).key) first second)
    (firstAdmitted : ∀ m ∈ first, m.firing.Admits (frames (FirstOrder.action signature)) s)
    (secondAdmitted : ∀ m ∈ second, m.firing.Admits (frames (FirstOrder.action signature)) s) :
    (↑(first.flatMap fun m => m.selection.taken) : Multiset O) =
        ↑(second.flatMap fun m => m.selection.taken) ∧
      (first.flatMap fun m => m.selection.made).length = (second.flatMap fun m => m.selection.made).length := by
  induction related with
  | nil => exact ⟨rfl, rfl⟩
  | @cons m n rest later same tail ih =>
    have remaining := ih (fun m inside => firstAdmitted m (List.mem_cons_of_mem _ inside))
      (fun n inside => secondAdmitted n (List.mem_cons_of_mem _ inside))
    have takes := same_class_taken s m.firing n.firing
      (firstAdmitted m List.mem_cons_self) (secondAdmitted n List.mem_cons_self) same
    have made := same_class_made_length s m.firing n.firing
      (firstAdmitted m List.mem_cons_self) (secondAdmitted n List.mem_cons_self) same
    constructor
    · simpa only [List.flatMap_cons, Multiset.coe_add] using congrArg₂ (· + ·) takes remaining.1
    · simp only [List.flatMap_cons, List.length_append, made, remaining.2]

omit [DecidableEq O] in
theorem bag_made_length (s : State (Terms (Term signature)) O)
    (bag : Bag O (ext (FirstOrder.action signature)) P s.frame)
    (fits : bag.Fits (frames (FirstOrder.action signature)) s) :
    bag.selection.made.length = (bag.produce (frames (FirstOrder.action signature))).length := by
  change (bag.members.flatMap fun m => m.selection.made).length =
    (bag.members.flatMap fun m => (m.firing.opened (frames (FirstOrder.action signature))).produce).length
  rw [List.length_flatMap, List.length_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro m member
  simp only [Firing.opened, RuleInstance.map, List.length_map]
  exact (fits.2.2.2 m member).2.2.1.symm

theorem same_keys_bag_resources (s : State (Terms (Term signature)) O)
    (first : Bag O (ext (FirstOrder.action signature)) P s.frame)
    (second : Bag O (ext (FirstOrder.action signature)) P' s.frame)
    (firstOwn : first.AdmitsOwn (frames (FirstOrder.action signature)) s)
    (secondOwn : second.AdmitsOwn (frames (FirstOrder.action signature)) s)
    (keys : first.keysBy identity = second.keysBy identity) :
    ∃ rename : Equiv.Perm O, (∀ o ∈ s.present, rename o = o) ∧
      first.selection.made.map rename = second.selection.made ∧
      (first.result (frames (FirstOrder.action signature)) s).present.map rename.toEmbedding =
        (second.result (frames (FirstOrder.action signature)) s).present := by
  have paired : List.Forall₂ Eq (first.keysBy identity) (second.keysBy identity) := by
    rw [keys]
    exact List.forall₂_same.mpr fun _ _ => rfl
  have related : List.Forall₂ (fun m n => (presentation m.firing).key = (presentation n.firing).key)
      first.members second.members :=
    List.forall₂_map_left_iff.mp (List.forall₂_map_right_iff.mp paired)
  obtain ⟨taken, length⟩ := member_resource_totals s related
    (fun m inside => Bag.admits_member _ (fun _ _ => ⟨Subst.id signature⟩) firstOwn inside)
    (fun m inside => Bag.admits_member _ (fun _ _ => ⟨Subst.id signature⟩) secondOwn inside)
  obtain ⟨rename, maps, fixes⟩ := FreshResultNames.align s.present first.selection.made second.selection.made
    firstOwn.1.2.2.1 secondOwn.1.2.2.1 length
    (fun o member => fun present => Finset.disjoint_left.mp firstOwn.2.1.fresh
      (List.mem_toFinset.mpr member) present)
    (fun o member => fun present => Finset.disjoint_left.mp secondOwn.2.1.fresh
      (List.mem_toFinset.mpr member) present)
  refine ⟨rename, fixes, maps, ?_⟩
  have takes : first.selection.taken.toFinset = second.selection.taken.toFinset :=
    congrArg Multiset.toFinset taken
  have old : (s.present \ first.selection.taken.toFinset).map rename.toEmbedding =
      s.present \ first.selection.taken.toFinset :=
    source_map_fixed _ rename (fun o member => fixes o (Finset.mem_sdiff.mp member).1)
  change ((s.present \ first.selection.taken.toFinset) ∪ first.selection.made.toFinset).map rename.toEmbedding =
    (s.present \ second.selection.taken.toFinset) ∪ second.selection.made.toFinset
  rw [Finset.map_union, old, made_toFinset_map maps, takes]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
