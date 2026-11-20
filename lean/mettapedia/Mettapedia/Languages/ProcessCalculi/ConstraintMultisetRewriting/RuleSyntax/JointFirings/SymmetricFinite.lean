import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
import Mathlib.Data.Finset.Image

/-!
# Finite representatives of the admitted symmetric CMR matches

Profile: a finite ambient program, one finite occurrence-bag store, the
existing one-match after-tells judgment. The finite candidate presentation
enumerator is executable. Choosing admitted firing witnesses is a separate
noncomputable existence theorem; it supplies no joint-freshness or native
enumeration-cost claim.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} {O : Type} [DecidableEq O]
  {P : Program (Terms (Term signature))}

def selections {Occurrence : Type*} (rows : List Occurrence) : Nat → List (List Occurrence)
  | 0 => [[]]
  | count + 1 => rows.flatMap fun row => (selections rows count).map (row :: ·)

omit [DecidableEq O] in
theorem mem_selections {Occurrence : Type*} (rows : List Occurrence) : ∀ (count : Nat) (selected : List Occurrence),
    selected ∈ selections rows count ↔ selected.length = count ∧ ∀ o ∈ selected, o ∈ rows := by
  intro count
  induction count with
  | zero =>
    intro selected
    constructor
    · intro member
      have empty : selected = [] := by simpa only [selections, List.mem_singleton] using member
      subst selected
      simp
    · rintro ⟨length, _⟩
      have empty := List.length_eq_zero_iff.mp length
      subst selected
      exact List.mem_singleton_self _
  | succ count ih =>
    intro selected
    cases selected with
    | nil => simp [selections]
    | cons head rest =>
      constructor
      · intro member
        obtain ⟨o, inRows, restMember⟩ := List.mem_flatMap.mp member
        obtain ⟨old, oldMember, same⟩ := List.mem_map.mp restMember
        obtain ⟨rfl, rfl⟩ := List.cons.inj same
        obtain ⟨length, all⟩ := (ih old).mp oldMember
        exact ⟨congrArg Nat.succ length, fun o member =>
          (List.mem_cons.mp member).elim (fun same => same ▸ inRows) (all o)⟩
      · rintro ⟨length, all⟩
        exact List.mem_flatMap.mpr ⟨head, all head List.mem_cons_self,
          List.mem_map.mpr ⟨rest, (ih rest).mpr ⟨Nat.succ.inj length,
            fun o member => all o (List.mem_cons_of_mem _ member)⟩, rfl⟩⟩

def candidates (rules : List (Rule (Terms (Term signature)))) (rows : List O) :
    List (Presentation signature O) :=
  rules.flatMap fun rule =>
    (selections rows rule.body.take.length).flatMap fun taken =>
      (selections rows rule.body.read.length).map fun read =>
        ⟨rule, (rule.body.take.zip taken : List (Term signature × O)),
          (rule.body.read.zip read : List (Term signature × O))⟩

theorem admitted_presentation_is_candidate (s : State (Terms (Term signature)) O)
    (rules : List (Rule (Terms (Term signature))))
    (covers : ∀ rule ∈ P, rule ∈ rules)
    (f : Firing O (ext (FirstOrder.action signature)) P s.frame)
    (admitted : f.Admits (frames (FirstOrder.action signature)) s) :
    presentation f ∈ candidates rules s.present.toList := by
  apply List.mem_flatMap.mpr
  refine ⟨f.rule, covers f.rule f.member, List.mem_flatMap.mpr ?_⟩
  refine ⟨f.selection.taken, ?_, List.mem_map.mpr ⟨f.selection.read, ?_, rfl⟩⟩
  · apply (mem_selections _ _ _).mpr
    exact ⟨admitted.1.2.2.2.1.symm, fun o member =>
      Finset.mem_toList.mpr (admitted.2.1.taken_subset (List.mem_toFinset.mpr member))⟩
  · apply (mem_selections _ _ _).mpr
    exact ⟨admitted.1.2.2.2.2.1.symm, fun o member =>
      Finset.mem_toList.mpr (admitted.2.1.kept_subset (List.mem_toFinset.mpr member))⟩

noncomputable def admittedKeys (s : State (Terms (Term signature)) O)
    (rules : List (Rule (Terms (Term signature)))) : Finset (Class signature O) := by
  classical
  exact ((candidates rules s.present.toList).map Presentation.key).toFinset.filter fun key =>
    ∃ f : Firing O (ext (FirstOrder.action signature)) P s.frame,
      f.Admits (frames (FirstOrder.action signature)) s ∧ identity.key f = key

theorem mem_admittedKeys (s : State (Terms (Term signature)) O)
    (rules : List (Rule (Terms (Term signature))))
    (covers : ∀ rule ∈ P, rule ∈ rules) (key : Class signature O) :
    key ∈ admittedKeys (P := P) s rules ↔
      ∃ f : Firing O (ext (FirstOrder.action signature)) P s.frame,
        f.Admits (frames (FirstOrder.action signature)) s ∧ identity.key f = key := by
  classical
  constructor
  · intro member
    exact (Finset.mem_filter.mp member).2
  · rintro ⟨f, admitted, rfl⟩
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨presentation f, admitted_presentation_is_candidate s rules covers f admitted, rfl⟩),
      f, admitted, rfl⟩

/-- One actual admitted firing per class exists. The chosen witnesses can
subsequently be reopened in jointly fresh namespaces by a family builder. -/
theorem finite_admitted_representatives (s : State (Terms (Term signature)) O)
    (rules : List (Rule (Terms (Term signature))))
    (covers : ∀ rule ∈ P, rule ∈ rules) :
    ∃ representatives : List (Firing O (ext (FirstOrder.action signature)) P s.frame),
      (representatives.map identity.key).Nodup ∧
      (∀ f ∈ representatives, f.Admits (frames (FirstOrder.action signature)) s) ∧
      ∀ f : Firing O (ext (FirstOrder.action signature)) P s.frame,
        f.Admits (frames (FirstOrder.action signature)) s →
          identity.key f ∈ representatives.map identity.key := by
  classical
  let keys := admittedKeys (P := P) s rules
  have witness : ∀ key : {key // key ∈ keys},
      ∃ f : Firing O (ext (FirstOrder.action signature)) P s.frame,
        f.Admits (frames (FirstOrder.action signature)) s ∧ identity.key f = key.val :=
    fun key => (mem_admittedKeys s rules covers key.val).mp key.property
  let choose := fun key : {key // key ∈ keys} => Classical.choose (witness key)
  let representatives := keys.attach.toList.map choose
  have sameKeys : representatives.map identity.key = keys.attach.toList.map Subtype.val := by
    change representatives.map (fun f => (presentation f).key) = keys.attach.toList.map Subtype.val
    simp only [representatives, List.map_map]
    apply List.map_congr_left
    intro key _
    exact (Classical.choose_spec (witness key)).2
  refine ⟨representatives, ?_, ?_, ?_⟩
  · rw [sameKeys]
    exact (Finset.nodup_toList _).map Subtype.val_injective
  · intro f member
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp member
    exact (Classical.choose_spec (witness key)).1
  · intro f admitted
    rw [sameKeys]
    have member := (mem_admittedKeys s rules covers (identity.key f)).mpr ⟨f, admitted, rfl⟩
    exact List.mem_map.mpr ⟨⟨identity.key f, member⟩,
      Finset.mem_toList.mpr (Finset.mem_attach _ _), rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SymmetricMatches
