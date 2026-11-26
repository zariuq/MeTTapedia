import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Maximal
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SearchLicences

/-!
# One-key tests for maximal firings

Joint admission is closed under deleting members exactly when all admitted
members can justify their guards from their own information. In a
downward-closed region, testing every one-key extension decides maximality
relative to the available admission predicate. This test quantifies over
realizations of the keys, allowing the openings of a larger bag to be reused.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled)

section

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}
  {X : Frames Tm Hom}

private theorem realized_sublist {a b : Obj} {x : E.Ext a}
    (inhabited : ∀ (r : Rule Tm) (b : Obj), Nonempty (Hom r.locals b))
    {small large : List (Member O E P x)} (sub : small.Sublist large)
    {Q : Hom (E.target x) b → Prop} (largeRealized : Realized X b large Q) :
    Realized X b small Q := by
  induction sub generalizing Q with
  | slnil => exact largeRealized
  | cons m _ ih =>
      obtain ⟨h⟩ := inhabited m.rule b
      exact ih (Realized.mono X _ (fun _ both => both.1) (largeRealized h))
  | cons_cons m _ ih =>
      exact fun h => ih (largeRealized h)

namespace Bag

variable [DecidableEq O] {s : State Tm O}

/-- Keep the extension and use only the given member list. -/
def withMembers {a : Obj} (bag : Bag O E P a) (members : List (Member O E P bag.ext)) :
    Bag O E P a :=
  ⟨bag.ext, members⟩

/-- A sublist preserves fit, resource availability and solution consistency. -/
private theorem sublist_conditions
    (inhabited : ∀ (r : Rule Tm) (b : Obj), Nonempty (Hom r.locals b))
    {bag : Bag O E P s.frame} {members : List (Member O E P bag.ext)}
    (sub : members.Sublist bag.members)
    (fit : bag.Fits X s)
    (available : Enabled (fun _ : O => ()) s.present (bag.selection.commit (T := Unit)))
    (solvable : X.Solvable (bag.information X s)) :
    let small := bag.withMembers members
    small.Fits X s ∧
      Enabled (fun _ : O => ()) s.present (small.selection.commit (T := Unit)) ∧
      X.Solvable (small.information X s) := by
  dsimp only
  let small := bag.withMembers members
  change small.Fits X s ∧
    Enabled (fun _ : O => ()) s.present (small.selection.commit (T := Unit)) ∧
    X.Solvable (small.information X s)
  have taken : small.selection.taken.Sublist bag.selection.taken :=
    sub.flatMap fun m => m.selection.taken
  have read : small.selection.read.Sublist bag.selection.read :=
    sub.flatMap fun m => m.selection.read
  have made : small.selection.made.Sublist bag.selection.made :=
    sub.flatMap fun m => m.selection.made
  have takeSubset : small.selection.taken.toFinset ⊆ bag.selection.taken.toFinset :=
    fun _ h => List.mem_toFinset.mpr (taken.subset (List.mem_toFinset.mp h))
  have readSubset : small.selection.read.toFinset ⊆ bag.selection.read.toFinset :=
    fun _ h => List.mem_toFinset.mpr (read.subset (List.mem_toFinset.mp h))
  have makeSubset : small.selection.made.toFinset ⊆ bag.selection.made.toFinset :=
    fun _ h => List.mem_toFinset.mpr (made.subset (List.mem_toFinset.mp h))
  refine ⟨⟨fun b g => realized_sublist inhabited sub (fit.1 b g),
      taken.nodup fit.2.1, made.nodup fit.2.2.1, fun m hm => fit.2.2.2 m (sub.subset hm)⟩,
    ⟨takeSubset.trans available.taken_subset, readSubset.trans available.kept_subset,
      Disjoint.mono takeSubset readSubset available.apart,
      Disjoint.mono_left makeSubset available.fresh,
      fun _ h => (List.not_mem_nil h).elim⟩,
    ?_⟩
  obtain ⟨b, σ, model⟩ := solvable
  have info : (small.information X s).Sublist (bag.information X s) :=
    (List.Sublist.refl _).append (sub.flatMap fun m => m.own X s)
  exact ⟨b, σ, fun e present => model e (info.subset present)⟩

/-- Two admitted selections can be combined inside a compatible cap. Each
guard still sees its original entry cut and any added information refines
the models that established it. -/
theorem admits_of_union_cover
    (inhabited : ∀ (r : Rule Tm) (b : Obj), Nonempty (Hom r.locals b))
    {cap : Bag O E P s.frame}
    {left right combined : List (Member O E P cap.ext)}
    (fit : cap.Fits X s)
    (enabled : Enabled (fun _ : O => ()) s.present (cap.selection.commit (T := Unit)))
    (consistent : X.Solvable (cap.information X s))
    (sub : combined.Sublist cap.members)
    (leftIncluded : ∀ m ∈ left, m ∈ combined)
    (rightIncluded : ∀ m ∈ right, m ∈ combined)
    (covered : ∀ m ∈ combined, m ∈ left ∨ m ∈ right)
    (leftAdmits : (cap.withMembers left).Admits X s)
    (rightAdmits : (cap.withMembers right).Admits X s) :
    (cap.withMembers combined).Admits X s := by
  obtain ⟨combinedFit, combinedEnabled, combinedConsistent⟩ :=
    sublist_conditions inhabited sub fit enabled consistent
  refine ⟨combinedFit, combinedEnabled, combinedConsistent, ?_⟩
  intro b assignment solved m chosen
  rcases covered m chosen with fromLeft | fromRight
  · exact leftAdmits.2.2.2 b assignment
      (models_of_members_subset X leftIncluded solved) m fromLeft
  · exact rightAdmits.2.2.2 b assignment
      (models_of_members_subset X rightIncluded solved) m fromRight

/-- Member-local guard admission is closed under deleting members. -/
theorem admitsOwn_sublist
    (inhabited : ∀ (r : Rule Tm) (b : Obj), Nonempty (Hom r.locals b))
    {bag : Bag O E P s.frame} {members : List (Member O E P bag.ext)}
    (admitted : bag.AdmitsOwn X s) (sub : members.Sublist bag.members) :
    (bag.withMembers members).AdmitsOwn X s := by
  obtain ⟨fit, available, solved⟩ :=
    sublist_conditions inhabited sub admitted.1 admitted.2.1 admitted.2.2.1
  exact ⟨fit, available, solved, fun m hm => admitted.2.2.2 m (sub.subset hm)⟩

/-- Joint admission is hereditary precisely when every admitted bag already
admits its members at their own information. -/
theorem admits_sublist_iff_own
    (inhabited : ∀ (r : Rule Tm) (b : Obj), Nonempty (Hom r.locals b)) :
    (∀ (bag : Bag O E P s.frame) (members : List (Member O E P bag.ext)),
      bag.Admits X s → members.Sublist bag.members → (bag.withMembers members).Admits X s) ↔
    ∀ bag : Bag O E P s.frame, bag.Admits X s → bag.AdmitsOwn X s := by
  constructor
  · intro closed bag admitted
    refine ⟨admitted.1, admitted.2.1, admitted.2.2.1, fun member inside => ?_⟩
    have singleton := closed bag [member] admitted (List.singleton_sublist.mpr inside)
    exact ((admits_single X s member).mp singleton).2.2.2
  · intro localGuards bag members admitted sub
    exact admits_of_admitsOwn X (admitsOwn_sublist inhabited (localGuards bag admitted) sub)

/-- With neither checks nor collect queries, joint admission is closed under
deleting members as well. -/
theorem admits_sublist_of_no_checks
    (inhabited : ∀ (r : Rule Tm) (b : Obj), Nonempty (Hom r.locals b))
    (plain : ∀ r ∈ P, r.body.checks = [] ∧ r.collect = [])
    {bag : Bag O E P s.frame} {members : List (Member O E P bag.ext)}
    (admitted : bag.Admits X s) (sub : members.Sublist bag.members) :
    (bag.withMembers members).Admits X s := by
  obtain ⟨fit, available, solved⟩ :=
    sublist_conditions inhabited sub admitted.1 admitted.2.1 admitted.2.2.1
  refine ⟨fit, available, solved, fun b σ _ m hm => ?_⟩
  obtain ⟨checks, collect⟩ := plain m.rule m.member
  simp [Firing.Holds, Firing.opened, RuleInstance.map, Firing.collectOpened, checks, collect]

/-- The enlarged bag has exactly the keys of the base bag and one extra key. -/
def OneKeyExtension {a : Obj} (base enlarged : Bag O E P a) : Prop :=
  ∃ key ∉ base.members.map Member.key, ∀ k,
    k ∈ enlarged.members.map Member.key ↔ k ∈ base.members.map Member.key ∨ k = key

/-- In a hereditary region, every strict extension yields an admitted
one-key extension by retaining just the original keys and one new key. -/
theorem admitsMaximal_iff_no_oneKeyExtension_of_sublist
    (closed : ∀ (bag : Bag O E P s.frame) (members : List (Member O E P bag.ext)),
      bag.Admits X s → members.Sublist bag.members → (bag.withMembers members).Admits X s)
    (base : Bag O E P s.frame) :
    base.AdmitsMaximal X s ↔ base.Admits X s ∧ base.Distinct ∧
      ¬ ∃ enlarged : Bag O E P s.frame,
        enlarged.Admits X s ∧ enlarged.Distinct ∧ base.OneKeyExtension enlarged := by
  classical
  constructor
  · rintro ⟨admitted, distinct, maximal⟩
    refine ⟨admitted, distinct, ?_⟩
    rintro ⟨enlarged, enlargedAdmitted, enlargedDistinct, key, outside, keys⟩
    exact outside (maximal enlarged enlargedAdmitted enlargedDistinct
      (fun k inside => (keys k).mpr (.inl inside)) key ((keys key).mpr (.inr rfl)))
  · rintro ⟨admitted, distinct, noExtension⟩
    refine ⟨admitted, distinct, fun enlarged enlargedAdmitted enlargedDistinct included key present => ?_⟩
    by_contra outside
    let retained := enlarged.members.filter fun m =>
      decide (m.key ∈ base.members.map Member.key ∨ m.key = key)
    let smaller := enlarged.withMembers retained
    have sub : retained.Sublist enlarged.members := List.filter_sublist
    apply noExtension
    refine ⟨smaller, closed enlarged retained enlargedAdmitted sub,
      (sub.map Member.key).nodup enlargedDistinct, key, outside, fun k => ?_⟩
    change k ∈ retained.map Member.key ↔ _
    constructor
    · intro inside
      obtain ⟨m, matched, rfl⟩ := List.mem_map.mp inside
      exact of_decide_eq_true (List.mem_filter.mp matched).2
    · intro wanted
      have hits : k ∈ enlarged.members.map Member.key := by
        rcases wanted with old | rfl
        · exact included k old
        · exact present
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hits
      exact List.mem_map.mpr ⟨m, List.mem_filter.mpr ⟨hm, decide_eq_true wanted⟩, rfl⟩

/-- Rules without checks or census queries satisfy the one-key criterion. -/
theorem admitsMaximal_iff_no_oneKeyExtension
    (inhabited : ∀ (r : Rule Tm) (b : Obj), Nonempty (Hom r.locals b))
    (plain : ∀ r ∈ P, r.body.checks = [] ∧ r.collect = [])
    (base : Bag O E P s.frame) :
    base.AdmitsMaximal X s ↔ base.Admits X s ∧ base.Distinct ∧
      ¬ ∃ enlarged : Bag O E P s.frame,
        enlarged.Admits X s ∧ enlarged.Distinct ∧ base.OneKeyExtension enlarged :=
  admitsMaximal_iff_no_oneKeyExtension_of_sublist
    (fun _ _ admitted sub => admits_sublist_of_no_checks inhabited plain admitted sub) base

end Bag

end

#print axioms Bag.admits_of_union_cover
#print axioms Bag.admits_sublist_iff_own
#print axioms Bag.admitsMaximal_iff_no_oneKeyExtension_of_sublist
#print axioms Bag.admits_sublist_of_no_checks
#print axioms Bag.admitsMaximal_iff_no_oneKeyExtension

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
